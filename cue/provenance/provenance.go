// Copyright 2026 CUE Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Package provenance reports what the fields of an evaluated value depend on.
//
// References are resolved through the environments the evaluator bound them
// in, so a reference inside a unified definition, an imported package, a
// comprehension or a let reports the field of this value that it reads, not
// where it was declared. That includes references evaluation consumed, such as
// the condition of an if clause, which leave no trace in the resulting value.
//
// The value must be built with structure sharing disabled, as sharing replaces
// an instantiated field with the one it was shared from:
//
//	cuecontext.New(cuecontext.CUE_DEBUG("sharing=false"))
package provenance

import (
	"errors"
	"fmt"
	"sort"

	"cuelang.org/go/cue"
	"cuelang.org/go/internal/core/adt"
	"cuelang.org/go/internal/core/eval"
	"cuelang.org/go/internal/value"
)

// A Use says how a field uses the target of a reference.
type Use int

const (
	// Value means the target flows into the field unchanged, possibly with
	// constraints: x: y and x: y & string.
	Value Use = iota

	// Computed means the target is an operand of an expression computing the
	// value of the field: arithmetic, interpolation, a builtin or a bound.
	Computed

	// Control means the target decides the structure of the field: a condition,
	// a label, an index or the arm of a disjunction.
	Control

	// Presence means only the existence of the target and the names of its
	// fields are used: a for source, len and a comparison with bottom.
	Presence
)

func (u Use) String() string {
	switch u {
	case Value:
		return "value"
	case Computed:
		return "computed"
	case Control:
		return "control"
	case Presence:
		return "presence"
	}
	return fmt.Sprintf("Use(%d)", int(u))
}

// A Dependency is a reference from an expression of Field to Target.
type Dependency struct {
	Field  cue.Path
	Target cue.Path
	Use    Use
}

// maxDepth bounds the expressions followed through lets and inline values.
const maxDepth = 512

// Analyze returns the dependencies of every field of v, which must be the root
// of an instance. A target outside of v, such as a field of an imported package
// that was not unified into v, is not reported: it cannot depend on v.
//
// An error means the analysis is incomplete and nothing may be concluded from it.
func Analyze(v cue.Value) (result []Dependency, err error) {
	defer func() {
		if recovered := recover(); recovered != nil {
			result, err = nil, fmt.Errorf("provenance: analysis failed: %v", recovered)
		}
	}()
	r, root := value.ToInternal(v)
	if root == nil {
		return nil, errors.New("provenance: value has no vertex")
	}
	w := &walker{
		ctx:    eval.NewContext(r, root),
		root:   root,
		empty:  &adt.Vertex{},
		found:  map[dependencyKey]Dependency{},
		fields: map[*adt.Vertex]bool{},
		inline: map[inlineKey]bool{},

		unifiedInto: map[unifiedKey]bool{},
	}
	w.empty.ForceDone()
	w.field(root)
	if w.err != nil {
		return nil, w.err
	}
	keys := make([]dependencyKey, 0, len(w.found))
	for key := range w.found {
		keys = append(keys, key)
	}
	sort.Slice(keys, func(i, j int) bool {
		left, right := keys[i], keys[j]
		if left.field != right.field {
			return left.field < right.field
		}
		if left.target != right.target {
			return left.target < right.target
		}
		return left.use < right.use
	})
	result = make([]Dependency, 0, len(keys))
	for _, key := range keys {
		result = append(result, w.found[key])
	}
	return result, nil
}

type dependencyKey struct {
	field, target string
	use           Use
}

type inlineKey struct {
	vertex, field *adt.Vertex
	use           Use
}

type unifiedKey struct {
	target, self, field *adt.Vertex
}

type walker struct {
	ctx         *adt.OpContext
	root        *adt.Vertex
	empty       *adt.Vertex
	found       map[dependencyKey]Dependency
	fields      map[*adt.Vertex]bool
	inline      map[inlineKey]bool
	unifiedInto map[unifiedKey]bool
	depth       int
	err         error
}

// A site is where a reference is found. Its field is the field of the value that
// the reference is reported for and self is the vertex whose struct holds the
// expression, which differs while reading through a let or an inline value.
type site struct {
	field, self *adt.Vertex
	use         Use
}

func (s site) with(use Use) site {
	s.use = use
	return s
}

// operand is the use of an operand of an expression with this use.
func (s site) operand() site {
	switch s.use {
	case Value:
		return s.with(Computed)
	case Presence:
		return s.with(Control)
	}
	return s
}

func (s site) control() site { return s.with(Control) }

func (w *walker) fail(err error) {
	if w.err == nil {
		w.err = err
	}
}

// field reports the dependencies of v and of everything below it.
func (w *walker) field(v *adt.Vertex) {
	if w.fields[v] {
		return
	}
	w.fields[v] = true
	v.Unify(w.ctx, adt.FinalizeWithoutTypoCheck)
	s := site{field: v, self: v, use: Value}
	for conjunct := range v.LeafConjuncts() {
		w.elem(s, conjunct.Env, conjunct.Elem())
	}
	for _, instance := range instances(v) {
		for _, arc := range instance.Arcs {
			if !arc.Label.IsLet() {
				w.field(arc)
			}
		}
	}
}

// instances returns the vertices holding the fields of v: every disjunct of a
// disjunction, as the one that is selected can depend on what is filled in later.
func instances(v *adt.Vertex) []*adt.Vertex {
	v = v.DerefValue()
	disjunction, ok := v.BaseValue.(*adt.Disjunction)
	if !ok {
		return []*adt.Vertex{v}
	}
	result := []*adt.Vertex{v}
	for _, disjunct := range disjunction.Values {
		if arm, ok := disjunct.(*adt.Vertex); ok {
			result = append(result, instances(arm)...)
		}
	}
	return result
}

// elem walks an expression which is unified into s.self.
func (w *walker) elem(s site, env *adt.Environment, e adt.Elem) {
	switch x := e.(type) {
	case nil:
	case *adt.StructLit:
		inner := &adt.Environment{Up: env, Vertex: s.self}
		for _, decl := range x.Decls {
			w.decl(s, inner, decl)
		}
	case *adt.ListLit:
		inner := &adt.Environment{Up: env, Vertex: s.self}
		for _, element := range x.Elems {
			switch element := element.(type) {
			case *adt.Comprehension:
				w.clauses(s, inner, element, 0, nil)
			case *adt.Ellipsis:
				w.expr(s.operand(), inner, element.Value)
			}
		}
	case *adt.Comprehension:
		w.comprehension(s, env, x)
	case *adt.BinaryExpr:
		if x.Op == adt.AndOp && s.use == Value {
			w.elem(s, env, x.X)
			w.elem(s, env, x.Y)
			return
		}
		w.expr(s, env, x)
	case *adt.CallExpr:
		if isClose(x) && s.use == Value {
			// close only affects which fields may be added.
			for _, argument := range x.Args {
				w.elem(s, env, argument)
			}
			return
		}
		w.expr(s, env, x)
	case adt.Resolver:
		w.resolver(s, env, x)
		if target := w.resolve(env, x); target != nil && s.use == Value {
			w.unified(s, target)
		}
	default:
		w.expr(s, env, e)
	}
}

func isClose(x *adt.CallExpr) bool {
	builtin, ok := x.Fun.(*adt.Builtin)
	return ok && builtin.Name == "close"
}

// unified walks the conjuncts of target as the evaluator does when a reference
// unifies target into s.self: bound to s.self instead of to the target. Its fields
// bind like that as arcs of s.self, but nothing else keeps what its struct embeds.
func (w *walker) unified(s site, target *adt.Vertex) {
	target = target.DerefValue()
	key := unifiedKey{target: target, self: s.self, field: s.field}
	if w.unifiedInto[key] {
		return
	}
	w.unifiedInto[key] = true
	for conjunct := range target.LeafConjuncts() {
		w.elem(s, conjunct.Env, conjunct.Elem())
	}
}

func (w *walker) decl(s site, env *adt.Environment, d adt.Decl) {
	switch x := d.(type) {
	case *adt.Field, *adt.LetField:
		// The value of a field is a conjunct of its arc.
	case *adt.DynamicField:
		w.expr(s.control(), env, x.Key)
	case *adt.BulkOptionalField:
		w.expr(s.control(), env, x.Filter)
	case *adt.Comprehension:
		w.comprehension(s, env, x)
	case *adt.Ellipsis:
		w.expr(s.operand(), env, x.Value)
	case adt.Expr:
		w.elem(s, env, x)
	default:
		w.fail(fmt.Errorf("provenance: unsupported declaration %T", d))
	}
}

// comprehension walks a comprehension unified into s.self. The evaluator pushes it
// down to the fixed fields of its value, so those depend on its clauses and s.self
// does not, unless the value holds something else or there is an else clause.
func (w *walker) comprehension(s site, env *adt.Environment, y *adt.Comprehension) {
	body, isStruct := adt.ToExpr(y.Value).(*adt.StructLit)
	if isStruct {
		for _, decl := range body.Decls {
			if field, isField := decl.(*adt.Field); isField {
				w.fixedField(s, env, y, field)
			}
		}
		if y.Fallback == nil && fixedFields(body) {
			return
		}
	}
	yielded, resolved := false, true
	w.clauses(s, env, y, 0, func(result *adt.Environment, known bool) {
		yielded = true
		resolved = resolved && known
		target := s
		if !known {
			target = s.control()
		}
		w.elem(target, y.ValueEnvironment(result), adt.ToExpr(y.Value))
	})
	if y.Fallback != nil {
		switch {
		case !resolved:
			w.literalDecl(s.control(), y.ValueEnvironment(env), y.Fallback)
		case !yielded:
			w.elem(s, y.ValueEnvironment(env), y.Fallback)
		}
	}
}

// fixedField reports what a field pushed down from a comprehension depends on. Its
// arc is gone unless the clauses resolved, so nothing else can report this: a field
// that exists depending on a condition is what makes the condition matter.
func (w *walker) fixedField(s site, env *adt.Environment, y *adt.Comprehension, field *adt.Field) {
	child := s
	if s.field == s.self {
		arc := s.self.LookupRaw(field.Label)
		if arc == nil {
			arc = &adt.Vertex{Parent: s.self, Label: field.Label}
		}
		child = site{field: arc, self: arc, use: s.use}
	}
	w.clauses(child, env, y, 0, func(result *adt.Environment, known bool) {
		if !known {
			inner := &adt.Environment{Up: y.ValueEnvironment(result), Vertex: w.empty}
			w.literalDecl(child.control(), inner, field.Value)
		}
	})
}

func fixedFields(body *adt.StructLit) bool {
	for _, decl := range body.Decls {
		switch decl.(type) {
		case *adt.Field, *adt.LetField:
		default:
			return false
		}
	}
	return true
}

// clauses reports what the clauses from index i on read, and calls yield with the
// Environment of each result. known is false for an Environment that stands in for
// results which depend on something that is not known yet. A nil yield only reports
// the clauses, for a list whose elements are arcs.
func (w *walker) clauses(s site, env *adt.Environment, y *adt.Comprehension, i int, yield func(*adt.Environment, bool)) {
	w.clausesKnown(s, env, y, i, yield, true)
}

func (w *walker) clausesKnown(s site, env *adt.Environment, y *adt.Comprehension, i int, yield func(*adt.Environment, bool), known bool) {
	if i == len(y.Clauses) {
		if yield != nil {
			yield(env, known)
		}
		return
	}
	next := func(result *adt.Environment, known bool) {
		w.clausesKnown(s, result, y, i+1, yield, known)
	}
	switch x := y.Clauses[i].(type) {
	case *adt.ForClause:
		w.forSource(s, env, x.Src)
		source := w.evaluate(env, x.Src)
		if source == nil {
			next(&adt.Environment{Up: env, Vertex: w.empty}, false)
			return
		}
		source.Unify(w.ctx, adt.FinalizeWithoutTypoCheck)
		for _, instance := range instances(source) {
			for _, arc := range instance.Arcs {
				arc.Unify(w.ctx, adt.FinalizeWithoutTypoCheck)
				if arc.Label.IsRegular() && (arc.ArcType == adt.ArcMember || arc.ArcType == adt.ArcPending) {
					next(w.forBinding(env, x, arc), known)
				}
			}
		}
	case *adt.IfClause:
		w.expr(s.control(), env, x.Condition)
		switch w.condition(env, x.Condition) {
		case conditionTrue:
			next(env, known)
		case conditionUnknown:
			next(env, false)
		}
	case *adt.LetClause:
		next(letBinding(env, x.Label, x.Expr), known)
	case *adt.TryClause:
		if x.Expr == nil {
			w.expr(s.control(), y.ValueEnvironment(env), adt.ToExpr(y.Value))
			next(env, known)
			return
		}
		w.expr(s.control(), env, x.Expr)
		next(letBinding(env, x.Label, x.Expr), known)
	default:
		w.fail(fmt.Errorf("provenance: unsupported clause %T", y.Clauses[i]))
	}
}

// forSource reports a for source. Which fields a reference has is only presence, and
// the fields of a literal are known: its values are read through the loop variables.
func (w *walker) forSource(s site, env *adt.Environment, source adt.Expr) {
	switch x := source.(type) {
	case adt.Resolver:
		w.resolver(s.with(Presence), env, x)
	case *adt.StructLit:
		inner := &adt.Environment{Up: env, Vertex: w.empty}
		for _, decl := range x.Decls {
			if _, isField := decl.(*adt.Field); !isField {
				w.literalDecl(s.control(), inner, decl)
			}
		}
	case *adt.ListLit:
		inner := &adt.Environment{Up: env, Vertex: w.empty}
		for _, element := range x.Elems {
			if comprehension, ok := element.(*adt.Comprehension); ok {
				w.literalDecl(s.control(), inner, comprehension)
			}
		}
	default:
		w.expr(s.control(), env, source)
	}
}

// forBinding builds the Environment ForClause.yield would for one element.
func (w *walker) forBinding(env *adt.Environment, x *adt.ForClause, element *adt.Vertex) *adt.Environment {
	n := &adt.Vertex{Parent: env.DerefVertex(w.ctx), IsDynamic: true, ArcType: adt.ArcMember}
	n.ForceDone()
	if x.Value != adt.InvalidLabel {
		n.Arcs = append(n.Arcs, &adt.Vertex{Label: x.Value, BaseValue: element, IsDynamic: true, ArcType: adt.ArcPending})
	}
	if x.Key != adt.InvalidLabel {
		key := element.Label.ToValue(w.ctx)
		arc := &adt.Vertex{Label: x.Key, IsDynamic: true}
		arc.AddConjunct(adt.MakeRootConjunct(env, key))
		arc.SetValue(w.ctx, key)
		n.Arcs = append(n.Arcs, arc)
	}
	return &adt.Environment{Up: env, Vertex: n}
}

// letBinding builds the Environment LetClause.yield would.
func letBinding(env *adt.Environment, label adt.Feature, expression adt.Expr) *adt.Environment {
	n := &adt.Vertex{Arcs: []*adt.Vertex{{
		Label:     label,
		IsDynamic: true,
		Conjuncts: []adt.Conjunct{adt.MakeRootConjunct(env, expression)},
	}}}
	return &adt.Environment{Up: env, Vertex: n}
}

type conditionResult int

const (
	conditionFalse conditionResult = iota
	conditionTrue
	conditionUnknown
)

func (w *walker) condition(env *adt.Environment, expression adt.Expr) conditionResult {
	result, _ := w.ctx.Evaluate(env, expression)
	_ = w.ctx.Err()
	if result == nil {
		return conditionUnknown
	}
	boolean, ok := adt.Unwrap(result).(*adt.Bool)
	switch {
	case !ok:
		return conditionUnknown
	case boolean.B:
		return conditionTrue
	}
	return conditionFalse
}

func (w *walker) evaluate(env *adt.Environment, expression adt.Expr) *adt.Vertex {
	vertex := w.ctx.ForSource(env, expression)
	_ = w.ctx.Err()
	return vertex
}

func (w *walker) resolve(env *adt.Environment, r adt.Resolver) *adt.Vertex {
	vertex, _ := w.ctx.Resolve(adt.MakeConjunct(env, r, adt.CloseInfo{}), r)
	_ = w.ctx.Err()
	return vertex
}

// expr walks an expression whose result s.field uses.
func (w *walker) expr(s site, env *adt.Environment, e adt.Elem) {
	if w.depth > maxDepth {
		w.fail(errors.New("provenance: expression nesting limit exceeded"))
		return
	}
	w.depth++
	defer func() { w.depth-- }()

	if r, ok := e.(adt.Resolver); ok {
		w.resolver(s, env, r)
		return
	}
	switch x := e.(type) {
	case nil:
	case *adt.BinaryExpr:
		w.binary(s, env, x)
	case *adt.UnaryExpr:
		w.expr(s.operand(), env, x.X)
	case *adt.OpenExpr:
		w.expr(s, env, x.X)
	case *adt.BoundExpr:
		w.expr(s.operand(), env, x.Expr)
	case *adt.Interpolation:
		for i := 1; i < len(x.Parts); i += 2 {
			w.expr(s.operand(), env, x.Parts[i])
		}
	case *adt.CallExpr:
		w.call(s, env, x)
	case *adt.DisjunctionExpr:
		for _, disjunct := range x.Values {
			w.expr(s.control(), env, disjunct.Val)
		}
	case *adt.SliceExpr:
		w.expr(s.operand(), env, x.X)
		w.expr(s.control(), env, x.Lo)
		w.expr(s.control(), env, x.Hi)
		w.expr(s.control(), env, x.Stride)
	case *adt.ListLit, *adt.StructLit:
		w.literal(s, env, x.(adt.Expr))
	case *adt.Comprehension:
		w.literalDecl(s, env, x)
	case *adt.LabelReference:
		// The label of a pattern match, which is known.
	case adt.Value:
		// A value holds no references.
	default:
		w.fail(fmt.Errorf("provenance: unsupported expression %T", e))
	}
}

func (w *walker) binary(s site, env *adt.Environment, x *adt.BinaryExpr) {
	if x.Op == adt.AndOp && s.use == Value {
		w.expr(s, env, x.X)
		w.expr(s, env, x.Y)
		return
	}
	if x.Op == adt.EqualOp || x.Op == adt.NotEqualOp {
		if operand, ok := comparedWithBottom(x); ok {
			if r, isReference := operand.(adt.Resolver); isReference {
				w.resolver(s.with(Presence), env, r)
			} else {
				w.expr(s.control(), env, operand)
			}
			return
		}
	}
	w.expr(s.operand(), env, x.X)
	w.expr(s.operand(), env, x.Y)
}

func comparedWithBottom(x *adt.BinaryExpr) (adt.Expr, bool) {
	if _, isBottom := x.Y.(*adt.Bottom); isBottom {
		return x.X, true
	}
	if _, isBottom := x.X.(*adt.Bottom); isBottom {
		return x.Y, true
	}
	return nil, false
}

func (w *walker) call(s site, env *adt.Environment, x *adt.CallExpr) {
	w.expr(s.operand(), env, x.Fun)
	builtin, _ := x.Fun.(*adt.Builtin)
	for _, argument := range x.Args {
		switch {
		case builtin != nil && builtin.Name == "len":
			if r, isReference := argument.(adt.Resolver); isReference {
				w.resolver(s.with(Presence), env, r)
			} else {
				w.expr(s.control(), env, argument)
			}
		case isClose(x):
			w.expr(s, env, argument)
		default:
			w.expr(s.operand(), env, argument)
		}
	}
}

// literal walks a composite literal which is an operand: evaluating it gives the
// fields of the literal its own vertex, which its references bind to.
func (w *walker) literal(s site, env *adt.Environment, x adt.Expr) {
	if vertex := w.evaluate(env, x); vertex != nil {
		w.inlined(s.operand(), vertex)
		return
	}
	w.literalDecl(s.operand(), env, x)
}

// literalDecl is the fallback for what cannot be evaluated: every reference counts,
// and those that bind to something only known once evaluated do not resolve.
func (w *walker) literalDecl(s site, env *adt.Environment, n adt.Node) {
	inner := &adt.Environment{Up: env, Vertex: w.empty}
	switch x := n.(type) {
	case *adt.StructLit:
		for _, decl := range x.Decls {
			w.literalDecl(s, inner, decl)
		}
	case *adt.ListLit:
		for _, element := range x.Elems {
			w.literalDecl(s, inner, element)
		}
	case *adt.Field:
		w.expr(s, env, x.Value)
	case *adt.LetField:
		w.expr(s, env, x.Value)
	case *adt.DynamicField:
		w.expr(s.control(), env, x.Key)
		w.expr(s, env, x.Value)
	case *adt.BulkOptionalField:
		w.expr(s.control(), env, x.Filter)
		w.expr(s, env, x.Value)
	case *adt.Ellipsis:
		w.expr(s, env, x.Value)
	case *adt.Comprehension:
		w.clausesKnown(s.control(), env, x, 0, func(result *adt.Environment, _ bool) {
			w.literalDecl(s.control(), x.ValueEnvironment(result), adt.ToExpr(x.Value))
		}, false)
		if x.Fallback != nil {
			w.literalDecl(s.control(), env, x.Fallback)
		}
	case adt.Expr:
		w.expr(s, env, x)
	}
}

func (w *walker) resolver(s site, env *adt.Environment, r adt.Resolver) {
	target := w.resolve(env, r)
	if target != nil {
		w.report(s, target)
	}
	switch x := r.(type) {
	case *adt.IndexExpr:
		w.expr(s.control(), env, x.Index)
		if target == nil {
			w.expr(base(s), env, x.X)
		}
	case *adt.SelectorExpr:
		if target == nil && !w.selectPending(s, env, x) {
			w.expr(base(s), env, x.X)
		}
	case *adt.DynamicReference:
		w.expr(s.control(), env, x.Label)
	}
}

// selectPending reports a selection from a struct that cannot be read yet, as what
// decides another of its fields is not known, if it has that field.
func (w *walker) selectPending(s site, env *adt.Environment, x *adt.SelectorExpr) bool {
	r, ok := x.X.(adt.Resolver)
	if !ok {
		return false
	}
	selected := w.resolve(env, r)
	if selected == nil {
		return false
	}
	arc := w.arc(selected, x.Sel)
	if arc == nil {
		return false
	}
	w.report(s, arc)
	return true
}

// arc returns the field of v with the given label. A copy without a path of its own
// is evaluated on demand, so it may not have its fields yet.
func (w *walker) arc(v *adt.Vertex, label adt.Feature) *adt.Vertex {
	v.Unify(w.ctx, adt.FinalizeWithoutTypoCheck)
	return v.DerefValue().LookupRaw(label)
}

// base is the use of the struct selected into by a reference that did not resolve.
// A selection that finds nothing yet only says something about its fields.
func base(s site) site {
	if s.use == Presence {
		return s
	}
	return s.operand()
}

type location int

const (
	rootless location = iota
	local
	foreign
)

func (w *walker) locate(v *adt.Vertex) location {
	for current := v; current != nil; current = current.Parent {
		if !current.Rooted() || !current.MayAttach() {
			return rootless
		}
		if current == w.root {
			return local
		}
	}
	return foreign
}

// report records that s uses target. A let, a comprehension variable and a field of
// an inline value have no path of their own, so what they read is read here.
func (w *walker) report(s site, target *adt.Vertex) {
	switch w.locate(target) {
	case foreign:
	case rootless:
		if indirect, ok := target.BaseValue.(*adt.Vertex); ok {
			w.report(s, indirect)
			return
		}
		w.inlined(s, target)
		w.projected(s, target)
	case local:
		if target == s.field {
			return
		}
		field, targetPath := w.path(s.field), w.path(target)
		key := dependencyKey{field: field.String(), target: targetPath.String(), use: s.use}
		w.found[key] = Dependency{Field: field, Target: targetPath, Use: s.use}
	}
}

// projected reports the field read through a copy without a path of its own: where
// an ancestor of v is unified with a reference, v is a copy of what that reference
// holds at the same labels, and its own conjuncts no longer say so.
func (w *walker) projected(s site, v *adt.Vertex) {
	var rest []adt.Feature
	for current := v; current != nil && w.locate(current) == rootless; current = current.Parent {
		if len(rest) > 0 {
			for conjunct := range current.LeafConjuncts() {
				w.projectedConjunct(s, conjunct.Env, conjunct.Elem(), rest)
			}
		}
		rest = append([]adt.Feature{current.Label}, rest...)
	}
}

func (w *walker) projectedConjunct(s site, env *adt.Environment, e adt.Elem, rest []adt.Feature) {
	switch x := e.(type) {
	case *adt.BinaryExpr:
		if x.Op == adt.AndOp {
			w.projectedConjunct(s, env, x.X, rest)
			w.projectedConjunct(s, env, x.Y, rest)
		}
	case adt.Resolver:
		selected := w.resolve(env, x)
		for _, label := range rest {
			if selected == nil {
				return
			}
			selected = w.arc(selected, label)
		}
		if selected != nil {
			w.report(s, selected)
		}
	}
}

// inlined walks what a vertex without a path of its own reads on behalf of s.field.
func (w *walker) inlined(s site, v *adt.Vertex) {
	key := inlineKey{vertex: v, field: s.field, use: s.use}
	if w.inline[key] {
		return
	}
	w.inline[key] = true
	if w.depth > maxDepth {
		w.fail(errors.New("provenance: expression nesting limit exceeded"))
		return
	}
	w.depth++
	defer func() { w.depth-- }()

	v.Unify(w.ctx, adt.FinalizeWithoutTypoCheck)
	inner := site{field: s.field, self: v, use: s.use}
	for conjunct := range v.LeafConjuncts() {
		w.elem(inner, conjunct.Env, conjunct.Elem())
	}
	switch s.use {
	case Value:
		// A struct unified into s.field brings along its fields as arcs of s.field.
	case Presence:
		// Which fields exist only depends on what decides the fields themselves.
		for _, instance := range instances(v) {
			for _, arc := range instance.Arcs {
				arc.Unify(w.ctx, adt.FinalizeWithoutTypoCheck)
				for conjunct := range arc.LeafConjuncts() {
					if comprehension, ok := conjunct.Elem().(*adt.Comprehension); ok {
						w.clauses(s.control(), conjunct.Env, comprehension, 0, nil)
					}
				}
			}
		}
	default:
		for _, instance := range instances(v) {
			for _, arc := range instance.Arcs {
				if !arc.Label.IsLet() {
					w.inlined(s, arc)
				}
			}
		}
	}
}

func (w *walker) path(v *adt.Vertex) cue.Path {
	features := v.Path()
	selectors := make([]cue.Selector, 0, len(features))
	for _, feature := range features {
		switch feature.Typ() {
		case adt.IntLabel:
			selectors = append(selectors, cue.Index(feature.Index()))
		case adt.DefinitionLabel:
			selectors = append(selectors, cue.Def(feature.SelectorString(w.ctx)))
		case adt.HiddenDefinitionLabel, adt.HiddenLabel:
			selectors = append(selectors, cue.Hid(feature.IdentString(w.ctx), feature.PkgID(w.ctx)))
		case adt.StringLabel:
			selectors = append(selectors, cue.Str(feature.StringValue(w.ctx)))
		default:
			w.fail(fmt.Errorf("provenance: unsupported label %s", feature.SelectorString(w.ctx)))
		}
	}
	return cue.MakePath(selectors...)
}
