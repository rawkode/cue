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

package adt

import "slices"

// Typed references
//
// A field such as
//
//	deps: [...(#A | #B)]
//	deps: [a]
//
// unifies a reference with a type. The disjunction disables structure sharing,
// so the referenced value is replayed into every disjunct, and each replayed
// copy unifies the typed references within it in turn. Evaluation is then
// exponential in the depth of a graph of such references.
//
// Suppose the referenced value a is final and was itself constrained by #A,
// with the closedness of #A enforced at a. Then a & #A is a: it repeats a
// conjunct. If #A & #B fails, so does a & #B, as a is an instance of #A. The
// disjunction then resolves to a, which can be shared. Whether two definitions
// can be unified does not depend on where a reference occurs, so it is
// computed once for each pair of definitions.
//
// The same holds for a field of an imported package, as in
//
//	deps: [pkg.a]
//
// The value of pkg.a is that of its package alone, so the conditions are those
// of a field of the same package; see importedField. One of them is checked
// differently. A package that embeds a definition may declare fields that the
// definition does not have, so that #A constrains a without being enforced
// on all of a. A typed reference within that package shares a nonetheless,
// which accepts such a field where a & #A would reject it. For a field of
// another package the unification is evaluated once instead; see closedBy.

// defPair identifies the unification of two definitions, or that of a value
// with a definition.
type defPair struct {
	a, b *Vertex
}

type disjointResult uint8

const (
	disjointPending disjointResult = iota + 1
	disjointYes
	disjointNo
)

// shareTypedReference shares a node consisting of a reference and type
// constraints with the referenced value if each constraint provably resolves
// to that value. It reports whether the conjuncts of the node were handled.
func (n *nodeContext) shareTypedReference() bool {
	v := n.node
	if !n.ctx.Sharing || len(v.Conjuncts) < 2 || len(v.Arcs) > 0 || n.isShared || n.noSharing {
		return false
	}

	// Find the single reference to a non-definition value. A field of an
	// imported package is looked up below, as that evaluates the package.
	refIndex := -1
	var target *Vertex
	for i, c := range v.Conjuncts {
		if !isTypedReferenceCandidate(c) {
			continue
		}
		w := n.ctx.refTarget(c.Env, c.Expr())
		if (w == nil || w.Label.IsDef()) && !isImportedField(c.Expr()) {
			continue
		}
		if refIndex >= 0 {
			return false
		}
		refIndex, target = i, w
	}
	if refIndex < 0 {
		return false
	}
	ref := v.Conjuncts[refIndex]
	if ref.CloseInfo.Opened || ref.CloseInfo.IsCyclic() {
		return false
	}

	// Every other conjunct must be a type made of definitions.
	types := make([][]*Vertex, 0, len(v.Conjuncts)-1)
	for i, typ := range v.Conjuncts {
		if i == refIndex {
			continue
		}
		if typ.CloseInfo.Opened || typ.CloseInfo.IsCyclic() {
			return false
		}
		var defs []*Vertex
		if !n.ctx.typeDefinitions(typ.Env, typ.Expr(), &defs, 0) {
			return false
		}
		types = append(types, defs)
	}

	// The other conjuncts are types: look up a field of an imported package.
	imported := target == nil
	if imported {
		if target = n.importedField(ref.Expr()); target == nil {
			return false
		}
	}
	if !n.completeTypedTarget(target) || !n.isTypedShareTarget(target) {
		return false
	}
	included := n.closedDefinitions(target, imported)
	if len(included) == 0 {
		return false
	}

	// Each type must resolve to the target.
	for _, defs := range types {
		matched := false
		for _, def := range defs {
			if slices.Contains(included, def) {
				// includesDefinition holds if no embedding relaxes def.
				if imported && !n.includesDefinition(target, def) && !n.ctx.closedBy(target, def) {
					return false
				}
				matched = true
				continue
			}
			if !n.ctx.excludedBy(def, included) {
				return false
			}
		}
		if !matched {
			return false
		}
	}

	// Mirror scheduleConjunct for all conjuncts before sharing.
	for _, c := range v.Conjuncts {
		if c.CloseInfo.FromDef {
			n.node.ClosedRecursive = true
		}
	}
	refID := n.ctx.combineCycleInfo(ref.CloseInfo)
	n.markNonCyclic(refID)

	n.scheduleVertexConjuncts(ref, target, refID)
	for i, typ := range v.Conjuncts {
		if i == refIndex {
			continue
		}
		typID := n.ctx.combineCycleInfo(typ.CloseInfo)
		if n.isShared {
			n.addShared(typ, nil, typID)
		} else {
			// The reference was expanded after all; apply the type as usual.
			n.scheduleConjunct(typ, typID)
		}
	}
	return true
}

func isTypedReferenceCandidate(c Conjunct) bool {
	switch c.Elem().(type) {
	case *FieldReference, *SelectorExpr:
		return c.Env != nil
	}
	return false
}

// isImportedField reports whether x selects a field of an imported package
// by a path of regular fields, as in pkg.a.b.
func isImportedField(x Expr) bool {
	for {
		sel, ok := x.(*SelectorExpr)
		if !ok || !sel.Sel.IsRegular() {
			return false
		}
		if r, ok := sel.X.(*ImportReference); ok {
			// A builtin package has no instance.
			return r.Instance != nil
		}
		x = sel.X
	}
}

// maxImportedPath bounds the fields selected from an imported package.
const maxImportedPath = 8

// importedField returns the arc that x, for which isImportedField holds,
// names, or nil if it is not known to be a regular field.
//
// The root of an imported package is a vertex of its own: the runtime holds
// one for each instance, its conjuncts are the files of the package, and it
// has no parent. A package cannot refer to a package that imports it, so the
// value of the field does not depend on the node that refers to it or on
// anything that is being evaluated. An arc reached from that root by regular
// fields is rooted in the same sense as an arc of the instance of n.
//
// refTarget does not evaluate, and the arcs of a package that has not been
// referred to do not exist yet. Process the conjuncts of the root and of each
// struct along the path, as a lookup of the reference does, without forcing
// anything that is blocked.
func (n *nodeContext) importedField(x Expr) *Vertex {
	c := n.ctx

	var buf [maxImportedPath]Feature
	path := buf[:0]
	var w *Vertex
	for w == nil {
		sel := x.(*SelectorExpr)
		if len(path) == cap(path) {
			return nil
		}
		path = append(path, sel.Sel)
		if r, ok := sel.X.(*ImportReference); ok {
			if w = c.Runtime.LoadInstance(r.Instance); w == nil {
				return nil
			}
		}
		x = sel.X
	}

	// earlier records that an earlier operation began to evaluate a struct
	// along the path. Such a struct is left as it is.
	earlier := false
	for i := len(path) - 1; i >= 0; i-- {
		w = w.DerefValue()
		if !w.isFinal() {
			s := w.getState(c)
			if s == nil {
				return nil
			}

			// Errors are those of the package. A lookup reports them for
			// the reference, so leave a struct that has any to the usual
			// path.
			saved := c.errs
			c.errs = nil
			if s.ctx != c {
				earlier = true
			} else {
				s.completeNodeTasks(attemptOnly)
				if len(s.disjuncts) > 0 {
					// The fields of a disjunction are those of its result.
					w.unify(c, Flags{condition: arcTypeKnown, mode: attemptOnly, checkTypos: false})
				}
			}
			failed := w.state != s || s.hasErr()
			c.errs = saved
			if failed {
				return nil
			}
			w = w.DerefValue()
		}
		if b := w.Bottom(); (b != nil && b != cycle) || w.ChildErrors != nil {
			return nil
		}
		if _, ok := w.BaseValue.(*Disjunction); ok {
			// A lookup selects the default, or fails.
			return nil
		}

		w = w.LookupRaw(path[i])
		if w == nil || w.ArcType != ArcMember {
			return nil
		}
	}
	if earlier && !w.isFinal() {
		// Only this operation completes a field on demand.
		return nil
	}
	return w
}

// closedBy reports whether the final value v, which def constrains, is
// closed by def: whether unifying v with def again gives v.
//
// A definition that constrains v need not be enforced on all of its fields.
// A struct that embeds a definition may declare fields that the definition,
// or a definition it refers to, does not have:
//
//	#P: {tasks?: [string]: #T}
//	#T: {cmd?: string}
//	{#P, tasks: a: {cmd: "x", extra: 1}}
//
// Here extra is allowed in tasks.a, but not in tasks.a & #T. Whether v has
// such a field is established once for each definition, by evaluating the
// unification on a detached vertex, as disjoint does for two definitions. As
// def already constrains v, the unification adds nothing to v unless it
// fails.
func (c *OpContext) closedBy(v, def *Vertex) bool {
	key := defPair{v, def}
	switch c.closedTargets[key] {
	case disjointYes:
		return true
	case disjointPending, disjointNo:
		return false
	}
	if c.closedTargets == nil {
		c.closedTargets = map[defPair]disjointResult{}
	}
	c.closedTargets[key] = disjointPending

	// As in disjoint, evaluate outside any disjunct.
	overlays := c.overlays
	c.overlays = nil
	saved := c.errs
	c.errs = nil

	w := &Vertex{Parent: v.Parent, Label: v.Label}
	w.Conjuncts = []Conjunct{
		MakeConjunct(nil, v, CloseInfo{}),
		MakeConjunct(nil, def, CloseInfo{FromDef: true}),
	}
	w.Finalize(c)

	failed := c.errs != nil
	c.errs = saved
	c.overlays = overlays

	result := disjointNo
	if x := w.DerefValue(); !failed && w.isFinal() && x.Bottom() == nil &&
		x.ChildErrors == nil && w.ChildErrors == nil {
		result = disjointYes
	}
	c.closedTargets[key] = result
	return result == disjointYes
}

// completeTypedTarget finalizes the target of a forward reference if it is
// idle, much like the evaluator does when it needs the value of a reference,
// and reports whether v is final. A target that is being evaluated, or that is
// an ancestor of n, is left alone.
func (n *nodeContext) completeTypedTarget(v *Vertex) bool {
	if equalDeref(v, n.node) {
		// A reference to the node itself.
		return false
	}
	if v.isFinal() {
		return true
	}
	if v.Parent == nil || v.Label.IsDef() || v.Label.IsLet() || v.IsDynamic || v.nonRooted ||
		v.status != unprocessed && v.status != partial {
		return false
	}
	if n.ctx.derefRoot(v) != v || n.hasAncestor(v) || !v.Parent.allChildConjunctsKnown(n.ctx) {
		return false
	}
	if s := v.state; s != nil {
		if s.ctx != n.ctx || s.refCount > 0 || s.isCompleting > 0 {
			return false
		}
		for _, t := range s.tasks {
			if t.state == taskRUNNING {
				return false
			}
		}
	}

	v.Finalize(n.ctx)

	// Completing a dependency can run tasks on this node as well.
	return v.isFinal() && n.node.state == n && !n.noSharing && !n.isShared &&
		len(n.node.Arcs) == 0 && n.ctx.errs == nil
}

// isTypedShareTarget reports whether v is a final, rooted value that can be
// shared from n without consulting the state of an ongoing evaluation.
func (n *nodeContext) isTypedShareTarget(v *Vertex) bool {
	if v == nil || v.Parent == nil || v.Label.IsDef() || v.Label.IsLet() || v.IsDynamic || v.nonRooted {
		return false
	}
	if n.ctx.derefRoot(v) != v || !v.isFinal() || v.cycleSensitive || v.DerefValue().cycleSensitive {
		return false
	}
	if n.hasAncestor(v) {
		return false
	}
	w := v.DerefValue()
	return w.Bottom() == nil && w.ChildErrors == nil && v.ChildErrors == nil
}

// closedDefinitions returns the definitions that constrain the final value v
// with their closedness enforced at v. These are direct references whose typo
// checking is enabled and that are not embedded within v itself; an embedding
// in an enclosing value does not relax the closedness of v.
//
// The state of a value that an earlier operation evaluated is evidence only
// if earlier is set. That is for a final field of an imported package: no
// operation can add a conjunct to it, and closedBy unifies it with the
// definition in this operation.
func (n *nodeContext) closedDefinitions(v *Vertex, earlier bool) []*Vertex {
	v = v.DerefDisjunct()
	s := v.state
	if s == nil || n.ctx.derefRoot(v) != v {
		return nil
	}
	if (s.ctx != n.ctx || s.opID != n.ctx.opID) && !(earlier && v.isFinal()) {
		return nil
	}
	var defs []*Vertex
	for _, r := range s.reqDefIDs {
		if r.kind != defReference || r.ignore || r.parent != 0 || r.v == nil || !r.v.Label.IsDef() {
			continue
		}
		if r.embed != 0 && slices.ContainsFunc(s.reqDefIDs, func(x refInfo) bool { return x.id == r.embed }) {
			continue
		}
		defs = append(defs, r.v)
	}
	return defs
}

// maxTypeDefinitions bounds the disjuncts considered for a single type.
const maxTypeDefinitions = 16

// typeDefinitions appends the definitions that make up a type expression: a
// reference to a definition, or a disjunction without defaults of such
// references. A definition whose only conjunct is such a disjunction is
// expanded in place.
func (c *OpContext) typeDefinitions(env *Environment, x Expr, defs *[]*Vertex, depth int) bool {
	if depth > 4 || env == nil {
		return false
	}
	switch x := x.(type) {
	case *DisjunctionExpr:
		if x.HasDefaults {
			return false
		}
		for _, d := range x.Values {
			if d.Default || !c.typeDefinitions(env, d.Val, defs, depth+1) {
				return false
			}
		}
		return true

	case *FieldReference, *SelectorExpr:
		def := c.refTarget(env, x)
		if def == nil || !def.Label.IsDef() || c.derefRoot(def) != def {
			return false
		}
		if len(def.Conjuncts) == 1 {
			dc := def.Conjuncts[0]
			if d, ok := dc.Expr().(*DisjunctionExpr); ok && !dc.CloseInfo.Opened {
				return c.typeDefinitions(dc.Env, d, defs, depth+1)
			}
		}
		if len(*defs) >= maxTypeDefinitions {
			return false
		}
		*defs = append(*defs, def)
		return true
	}
	return false
}

// excludedBy reports whether def cannot be unified with one of the
// definitions in included.
func (c *OpContext) excludedBy(def *Vertex, included []*Vertex) bool {
	for _, a := range included {
		if c.disjoint(a, def) {
			return true
		}
	}
	return false
}

// disjoint reports whether unifying the definitions a and b fails with a
// permanent error. The result is computed once for each pair, by completely
// evaluating the unification on a detached vertex. A pair that is being
// computed, or that fails only with incomplete errors, is not disjoint.
func (c *OpContext) disjoint(a, b *Vertex) bool {
	key := defPair{a, b}
	if a == b {
		return false
	}
	switch c.disjointDefs[key] {
	case disjointYes:
		return true
	case disjointPending, disjointNo:
		return false
	}
	if c.disjointDefs == nil {
		c.disjointDefs = map[defPair]disjointResult{}
	}
	c.disjointDefs[key] = disjointPending

	// Definitions do not depend on the evaluation that asks about them.
	// Evaluate them outside any disjunct, so that references within them are
	// not redirected to the vertices of the disjunct being evaluated.
	overlays := c.overlays
	c.overlays = nil
	saved := c.errs
	c.errs = nil

	id := CloseInfo{FromDef: true}
	w := &Vertex{Parent: a.Parent, Label: a.Label}
	w.Conjuncts = []Conjunct{
		MakeConjunct(nil, a, id),
		MakeConjunct(nil, b, id),
	}
	w.Finalize(c)

	c.errs = saved
	c.overlays = overlays

	result := disjointNo
	if hasPermanentError(w) {
		result = disjointYes
	}
	c.disjointDefs[key] = result
	return result == disjointYes
}

// hasPermanentError reports whether v or its arcs have an error that further
// evaluation cannot remove.
func hasPermanentError(v *Vertex) bool {
	for _, b := range []*Bottom{v.Bottom(), v.ChildErrors, v.DerefValue().ChildErrors} {
		if b != nil && !b.IsIncomplete() {
			return true
		}
	}
	return false
}
