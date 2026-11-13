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

package adt_test

import (
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"cuelang.org/go/cue"
	"cuelang.org/go/cue/build"
	"cuelang.org/go/cue/cuecontext"
	"cuelang.org/go/cue/errors"
	"cuelang.org/go/cue/load"
	"cuelang.org/go/cue/parser"
	"cuelang.org/go/cue/stats"
	"cuelang.org/go/cue/token"
	"cuelang.org/go/internal"
	"cuelang.org/go/internal/core/adt"
	"cuelang.org/go/internal/core/eval"
	"cuelang.org/go/internal/core/runtime"
	"cuelang.org/go/internal/cuedebug"
	"cuelang.org/go/internal/value"
)

// importedSchema is a schema package in the style of a task runner: tasks are
// declared through a pattern of a project definition, which each package
// embeds, and their dependencies are typed with a union of definitions.
const importedSchema = `package schema

#Task: {
	type?: _|_
	cmd!:  string
	out:   string | *"default"
	meta?: #Meta
	deps?: [...#Node]
}
#Meta: {label?: string}
#Group: {
	type: "group"
	deps?: [...#Node]
	[!~"^(type|deps)$"]: #Task | #Group
}
#Sequence: [...#Node]
#Node: #Task | #Group | #Sequence
#Project: {
	name!: string
	tasks?: [n=string]: ((#Task | #Group) & {_self: n}) | #Sequence
	...
}
`

const importedModule = "mod.test"

// projectChain returns the packages of a chain of projects. Each of the
// levels 0 to depth has width projects, p<level>x<index>, and every task of a
// project depends on the same task of each project one level down, through
// an import. direct writes each task as schema.#Task & {...}; otherwise only
// the pattern of #Project types it. The first project of the last level is
// returned as the one to evaluate.
func projectChain(depth, width int, direct bool) (packages map[string]string, top string) {
	packages = map[string]string{"schema": importedSchema}
	task := func(body string) string {
		if direct {
			return "schema.#Task & {" + body + "}"
		}
		return "{" + body + "}"
	}
	for level := 0; level <= depth; level++ {
		for index := range width {
			name := fmt.Sprintf("p%dx%d", level, index)
			var src, deps strings.Builder
			fmt.Fprintf(&src, "package cuenv\n\nimport (\n\t%q\n", importedModule+"/schema")
			for below := 0; level > 0 && below < width; below++ {
				fmt.Fprintf(&src, "\td%d \"%s/p%dx%d:cuenv\"\n", below, importedModule, level-1, below)
				if below > 0 {
					deps.WriteString(", ")
				}
				fmt.Fprintf(&deps, "d%d.tasks.TASK", below)
			}
			fmt.Fprintf(&src, ")\n\nschema.#Project\n\nname: %q\n\ntasks: {\n", name)
			for _, label := range []string{"build", "test"} {
				body := fmt.Sprintf("cmd: %q", label)
				if level > 0 {
					body += ", deps: [" + strings.ReplaceAll(deps.String(), "TASK", label) + "]"
				} else if label == "test" {
					body += ", deps: [build]"
				}
				fmt.Fprintf(&src, "\t%s: %s\n", label, task(body))
			}
			src.WriteString("}\n")
			packages[name] = src.String()
		}
	}
	return packages, fmt.Sprintf("p%dx0", depth)
}

// buildPackages builds the instance of the package main, resolving the
// imports of each package from packages, which maps a directory of the
// module to the source of its package.
func buildPackages(t *testing.T, packages map[string]string, main string) *build.Instance {
	t.Helper()
	ctx := build.NewContext()
	instances := map[string]*build.Instance{}
	var instance func(dir string) *build.Instance
	instance = func(dir string) *build.Instance {
		if inst := instances[dir]; inst != nil {
			return inst
		}
		src, ok := packages[dir]
		if !ok {
			t.Fatalf("no package %q", dir)
		}
		inst := ctx.NewInstance(dir, func(_ token.Pos, path string) *build.Instance {
			path, _, _ = strings.Cut(path, ":")
			return instance(strings.TrimPrefix(path, importedModule+"/"))
		})
		inst.ImportPath = importedModule + "/" + dir
		instances[dir] = inst
		file, err := parser.ParseFile(dir+"/in.cue", src, parser.Version("v0.14.1"))
		if err != nil {
			t.Fatal(err)
		}
		if err := inst.AddSyntax(file); err != nil {
			t.Fatal(err)
		}
		if err := inst.Complete(); err != nil {
			t.Fatal(err)
		}
		return inst
	}
	return instance(main)
}

// evalPackages evaluates the package main and returns the counts of that
// evaluation.
func evalPackages(t *testing.T, packages map[string]string, main string) (*runtime.Runtime, *adt.Vertex, stats.Counts) {
	t.Helper()
	r := runtime.NewWithSettings(internal.EvalV3, cuedebug.Config{Sharing: true})
	v, err := r.Build(nil, buildPackages(t, packages, main))
	if err != nil {
		t.Fatal(err)
	}
	ctx := adt.NewContext(r, v)
	v.Finalize(ctx)
	if b := adt.Validate(ctx, v, &adt.ValidateConfig{Concrete: true}); b != nil {
		t.Fatalf("unexpected evaluation error: %v", b.Err)
	}
	return r, v, *ctx.Stats()
}

// importedBudget bounds the evaluation of a chain of projects: the packages
// of one level cost a constant number of unifications. Without sharing, each
// level multiplies the cost: a chain of depth 4 and width 2 exceeds the
// budget of depth 32 a hundredfold.
func importedBudget(depth, width int) int64 {
	return int64(160 * width * (depth + 1))
}

// A typed reference to a field of an imported package should be shared like
// one to a field of the same package. A project that depends on the tasks of
// the projects it imports otherwise replays every dependency into each
// disjunct of the type, and evaluation is exponential in the depth of the
// chain of projects.
func TestImportedTypedReferenceSharingComplexity(t *testing.T) {
	for _, tc := range []struct {
		name   string
		width  int
		direct bool
	}{
		{"chain/direct", 1, true},
		{"chain/pattern", 1, false},
		{"fanout/direct", 2, true},
		{"fanout/pattern", 2, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			// Stop at the first excessive count, before trying larger depths
			// that would be expensive with broken sharing.
			for _, depth := range []int{1, 2, 4, 8, 16, 32} {
				packages, top := projectChain(depth, tc.width, tc.direct)
				_, _, counts := evalPackages(t, packages, top)
				t.Logf("depth %d: %d unifications, %d disjuncts", depth, counts.Unifications, counts.Disjuncts)
				budget := importedBudget(depth, tc.width)
				if counts.Unifications > budget || counts.Disjuncts > budget {
					t.Fatalf("depth %d: evaluation exceeds linear budget %d: %d unifications, %d disjuncts",
						depth, budget, counts.Unifications, counts.Disjuncts)
				}
			}
		})
	}
}

// A value that is unified or filled after it was evaluated is evaluated
// again by another operation, which finds the imported packages as the
// first one left them. Their final fields should still be shared.
func TestImportedTypedReferenceSharingAcrossOperations(t *testing.T) {
	for _, direct := range []bool{true, false} {
		t.Run(fmt.Sprintf("direct=%t", direct), func(t *testing.T) {
			for _, depth := range []int{2, 4, 8, 16} {
				packages, top := projectChain(depth, 2, direct)
				r, v, _ := evalPackages(t, packages, top)

				extra, inst := r.Compile(&runtime.Config{Filename: "extra.cue"}, `tasks: extra: {cmd: "extra"}`)
				if inst.Err != nil {
					t.Fatal(inst.Err)
				}
				w := &adt.Vertex{}
				w.AddConjunct(adt.MakeRootConjunct(nil, v))
				w.AddConjunct(adt.MakeRootConjunct(nil, extra))
				ctx := adt.NewContext(r, w)
				w.Finalize(ctx)
				if b := adt.Validate(ctx, w, &adt.ValidateConfig{Concrete: true}); b != nil {
					t.Fatalf("depth %d: unexpected evaluation error: %v", depth, b.Err)
				}
				counts := *ctx.Stats()
				t.Logf("depth %d: %d unifications, %d disjuncts", depth, counts.Unifications, counts.Disjuncts)
				budget := importedBudget(depth, 2)
				if counts.Unifications > budget || counts.Disjuncts > budget {
					t.Fatalf("depth %d: evaluation exceeds linear budget %d: %d unifications, %d disjuncts",
						depth, budget, counts.Unifications, counts.Disjuncts)
				}
			}
		})
	}
}

// importedDependency is a package with fields that may and fields that may
// not be shared.
const importedDependency = `package dep

import "mod.test/schema"

schema.#Project

name: "dep"

#local: schema.#Task & {out: "local"}

tasks: {
	a: {cmd: "a"}
	b: schema.#Task & {cmd: "b", deps: [a]}
	g: {type: "group", deps: [a], inner: {cmd: "inner"}}
	outer: {type: "group", sub: {type: "group", leaf: {cmd: "leaf", meta: label: "l"}}}
	viaLocal: #local & {cmd: "x"}
	abstract: {cmd: string}
	seq: [{cmd: "one"}, {cmd: "two", deps: [a]}]
	for k in ["t1", "t2"] {
		(k): {cmd: k}
	}

	// Allowed here, as this file embeds #Project.
	bad: {cmd: "x", bogus: 1}
	badNested: {cmd: "x", meta: {label: "l", bogus: 1}}
	badGroup: {type: "group", kid: {cmd: "x", bogus: 1}, fine: {cmd: "fine"}}
}

inner: {
	schema.#Project
	name: "inner"
	tasks: bad: {cmd: "x", bogus: 1}
}
ref: schema.#Project & {
	name: "ref"
	tasks: ok: {cmd: "ok"}
}

plain: {cmd: "plain"}
embedded: {schema.#Task, cmd: "e", extra: 1}
partial: schema.#Task
opt?: schema.#Task & {cmd: "o"}
#Def: schema.#Task & {cmd: "d"}
nested: deep: schema.#Task & {cmd: "deep"}
list: [schema.#Task & {cmd: "l0"}]
either: schema.#Task & {cmd: "x"} | schema.#Group & {type: "group"}
eitherStruct: {t: schema.#Task & {cmd: "one"}} | {t: schema.#Task & {cmd: "two"}}
defaulted: *(schema.#Task & {cmd: "x"}) | schema.#Group
defaultedStruct: *{t: schema.#Task & {cmd: "one"}} | {t: schema.#Task & {cmd: "two"}}
mixed: {t: schema.#Task & {cmd: "one"}} & ({k: 1} | {k: 2})
mixedDefault: {t: schema.#Task & {cmd: "one"}} & (*{k: 1} | {k: 2})
broken: schema.#Task & {cmd: 1}
conflict: schema.#Task & {cmd: "ok"}
conflict: schema.#Group
failed: {x: schema.#Task & {cmd: "x"}}
failed: [1]
`

// Sharing must not change a result. Each case refers to a field of an
// imported package from a typed list, and is evaluated with and without
// structure sharing: the value, or the fact that it is an error, must be the
// same. shared states whether the reference is expected to be shared, so
// that a case that must not be shared does not pass because nothing is.
func TestImportedTypedReferenceSharingSemantics(t *testing.T) {
	const dep = importedDependency
	for _, tc := range []struct {
		name   string
		ref    string
		shared bool
	}{
		// Shared: the field is final, rooted in the package, closed by a
		// definition of the type, and the other definitions exclude it.
		{"pattern", "dep.tasks.a", true},
		{"direct", "dep.tasks.b", true},
		{"group", "dep.tasks.g", true},
		{"group child", "dep.tasks.g.inner", true},
		{"nested group", "dep.tasks.outer", true},
		{"local definition", "dep.tasks.viaLocal", true},
		{"not concrete", "dep.tasks.abstract", true},
		{"comprehension", "dep.tasks.t1", true},
		{"sequence", "dep.tasks.seq", true},
		{"other struct", "dep.nested.deep", true},
		{"referenced project", "dep.ref.tasks.ok", true},
		{"sibling of a field with an error", "dep.tasks.badGroup.fine", true},

		// Not constrained by a definition of the type.
		{"plain struct", "dep.plain", false},
		// Embedding a definition does not close the value.
		{"embedded definition", "dep.embedded", false},
		// Allowed by the embedding of the package, not by the definition.
		{"field allowed by embedding", "dep.tasks.bad", false},
		{"nested field allowed by embedding", "dep.tasks.badNested", false},
		{"group with a field allowed by embedding", "dep.tasks.badGroup", false},
		{"group child allowed by embedding", "dep.tasks.badGroup.kid", false},
		{"embedded in a struct", "dep.inner.tasks.bad", false},
		// Not a final, regular field.
		{"required field missing", "dep.partial", false},
		{"optional field", "dep.opt", false},
		{"definition", "dep.#Def", false},
		{"list element", "dep.list[0]", false},
		{"missing field", "dep.tasks.nope", false},
		// Not a single value of the type.
		{"unresolved disjunction", "dep.either", false},
		{"default", "dep.defaulted", false},
		{"field of an unresolved disjunction", "dep.eitherStruct.t", false},
		{"field of a default", "dep.defaultedStruct.t", false},
		{"field beside an unresolved disjunction", "dep.mixed.t", false},
		{"field beside a default", "dep.mixedDefault.t", false},
		// Errors are reported at the reference.
		{"error", "dep.broken", false},
		{"conflicting definitions", "dep.conflict", false},
		{"field of an erroneous struct", "dep.failed.x", false},
		// Not only a reference.
		{"further constraint", `dep.tasks.a & {out: "changed"}`, false},
		{"two references", "dep.tasks.a & dep.tasks.b", false},
		{"alternatives", "*dep.tasks.a | dep.tasks.b", false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			packages := map[string]string{
				"schema": importedSchema,
				"dep":    dep,
				"main": fmt.Sprintf(`package main

import (
	"mod.test/schema"
	"mod.test/dep"
)

use: schema.#Task & {cmd: "use", deps: [%s]}
`, tc.ref),
			}
			result := func(option string) string {
				v := cuecontext.New(cuecontext.CUE_DEBUG(option)).BuildInstance(buildPackages(t, packages, "main"))
				if err := v.Validate(); err != nil {
					// Messages may name different positions.
					return "error"
				}
				data, err := v.MarshalJSON()
				if err != nil {
					return "error"
				}
				return string(data)
			}
			want := result("sharing=0")
			if got := result("sharing=1"); got != want {
				t.Errorf("sharing changes the result:\n got: %s\nwant: %s", got, want)
			}

			r := runtime.NewWithSettings(internal.EvalV3, cuedebug.Config{Sharing: true})
			v, err := r.Build(nil, buildPackages(t, packages, "main"))
			if err != nil {
				t.Fatal(err)
			}
			v.Finalize(adt.NewContext(r, v))
			elem := v
			for _, label := range []adt.Feature{r.StrLabel("use"), r.StrLabel("deps"), adt.MakeIntLabel(adt.IntLabel, 0)} {
				if elem = elem.DerefValue().LookupRaw(label); elem == nil {
					break
				}
			}
			if shared := elem != nil && elem.IsShared && elem.Bottom() == nil; shared != tc.shared {
				t.Errorf("shared = %t; want %t", shared, tc.shared)
			}
		})
	}
}

// References from within a definition, a comprehension, a group, a sequence,
// a disjunct and a let, evaluated in a fresh context, after the imported
// package was evaluated by itself, and again after the value was filled:
// the result must be that of evaluation without structure sharing.
func TestImportedTypedReferenceSharingContexts(t *testing.T) {
	// A package without errors: once a package with an error is evaluated
	// completely, every reference into it reports the error.
	const dep = `package dep

import "mod.test/schema"

schema.#Project

name: "dep"

#local: schema.#Task & {out: "local"}

tasks: {
	a: {cmd: "a"}
	b: schema.#Task & {cmd: "b", deps: [a]}
	g: {type: "group", deps: [a], inner: {cmd: "inner"}}
	outer: {type: "group", sub: {type: "group", leaf: {cmd: "leaf", meta: label: "l"}}}
	viaLocal: #local & {cmd: "x"}
	seq: [{cmd: "one"}, {cmd: "two", deps: [a]}]
}
ref: schema.#Project & {
	name: "ref"
	tasks: ok: {cmd: "ok"}
}
`
	packages := map[string]string{
		"schema": importedSchema,
		"dep":    dep,
		"main": `package main

import (
	"mod.test/schema"
	"mod.test/dep"
)

schema.#Project

name: "main"

#Template: schema.#Task & {cmd: "t", deps: [dep.tasks.a]}

let Local = dep.tasks.b

tasks: {
	fromTemplate: #Template & {out: "o"}
	for k in ["x", "y"] {
		(k): {cmd: k, deps: [dep.tasks.b, dep.tasks.g]}
	}
	group: {type: "group", deps: [dep.tasks.a], kid: {cmd: "k", deps: [dep.tasks.g.inner]}}
	seq: [{cmd: "one", deps: [dep.tasks.a]}, {cmd: "two", deps: [dep.tasks.seq, dep.tasks.outer]}]
	viaLet: {cmd: "l", deps: [Local]}
	both: {cmd: "b", deps: [fromTemplate, dep.tasks.viaLocal, dep.ref.tasks.ok]}
}
choice: schema.#Task & {cmd: "c", deps: [dep.tasks.a]} | schema.#Group & {cmd: "c", deps: [dep.tasks.b]}
`,
	}
	export := func(t *testing.T, option string, dependencyFirst, fill bool) string {
		ctx := cuecontext.New(cuecontext.CUE_DEBUG(option))
		inst := buildPackages(t, packages, "main")
		if dependencyFirst {
			for _, imported := range inst.Imports {
				if err := ctx.BuildInstance(imported).Validate(); err != nil {
					t.Fatal(errors.Details(err, nil))
				}
			}
		}
		v := ctx.BuildInstance(inst)
		if err := v.Validate(); err != nil {
			t.Fatal(errors.Details(err, nil))
		}
		if fill {
			v = v.FillPath(cue.ParsePath("tasks.filled"), ctx.CompileString(`{cmd: "filled"}`))
			v = v.FillPath(cue.ParsePath("tasks.seq[0].out"), "filled")
		}
		data, err := v.MarshalJSON()
		if err != nil {
			t.Fatal(errors.Details(err, nil))
		}
		return string(data)
	}
	for _, tc := range []struct {
		name                  string
		dependencyFirst, fill bool
	}{
		{"fresh", false, false},
		{"dependency first", true, false},
		{"filled", false, true},
		{"dependency first and filled", true, true},
	} {
		t.Run(tc.name, func(t *testing.T) {
			want := export(t, "sharing=0", tc.dependencyFirst, tc.fill)
			if got := export(t, "sharing=1", tc.dependencyFirst, tc.fill); got != want {
				t.Errorf("sharing changes the result:\n got: %s\nwant: %s", got, want)
			}
		})
	}
}

// writeModule writes packages as a module in a new directory.
func writeModule(t testing.TB, packages map[string]string) string {
	t.Helper()
	root := t.TempDir()
	write := func(name, data string) {
		path := filepath.Join(root, name)
		if err := os.MkdirAll(filepath.Dir(path), 0o777); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(data), 0o666); err != nil {
			t.Fatal(err)
		}
	}
	write("cue.mod/module.cue", fmt.Sprintf("module: %q\nlanguage: version: \"v0.14.1\"\n", importedModule))
	for dir, src := range packages {
		write(filepath.Join(dir, "env.cue"), src)
	}
	return root
}

// loadedChain evaluates and exports the project in dir of the module at
// root. It loads the directory of one package of the module and builds it in
// a context of its own.
func loadedChain(t testing.TB, root, dir string) (stats.Counts, time.Duration, int) {
	t.Helper()
	start := time.Now()
	instances := load.Instances([]string{"."}, &load.Config{
		Dir:        filepath.Join(root, dir),
		ModuleRoot: root,
		Package:    "cuenv",
	})
	if len(instances) != 1 {
		t.Fatalf("loaded %d instances", len(instances))
	}
	if err := instances[0].Err; err != nil {
		t.Fatal(errors.Details(err, nil))
	}
	r := runtime.NewWithSettings(internal.EvalV3, cuedebug.Config{Sharing: true})
	vertex, errs := r.Build(nil, instances[0])
	if errs != nil {
		t.Fatal(errors.Details(errs, nil))
	}
	ctx := eval.NewContext(r, vertex)
	vertex.Finalize(ctx)
	v := value.Make(ctx, vertex)
	if err := v.Validate(cue.Concrete(false)); err != nil {
		t.Fatal(errors.Details(err, nil))
	}
	data, err := v.MarshalJSON()
	if err != nil {
		t.Fatal(errors.Details(err, nil))
	}
	return *ctx.Stats(), time.Since(start), len(data)
}

// A chain of projects of depth 8, each depending on two projects one level
// down, should load, evaluate and export in well under a second.
func TestImportedProjectChain(t *testing.T) {
	const depth = 8
	for _, direct := range []bool{true, false} {
		t.Run(fmt.Sprintf("direct=%t", direct), func(t *testing.T) {
			packages, top := projectChain(depth, 2, direct)
			counts, elapsed, size := loadedChain(t, writeModule(t, packages), top)
			t.Logf("%d unifications, %d disjuncts, %d bytes of JSON in %v", counts.Unifications, counts.Disjuncts, size, elapsed)
			if budget := importedBudget(depth, 2); counts.Unifications > budget || counts.Disjuncts > budget {
				t.Fatalf("evaluation exceeds linear budget %d: %d unifications, %d disjuncts",
					budget, counts.Unifications, counts.Disjuncts)
			}
		})
	}
}

// TestCuenvProjectChain evaluates the chain of TestImportedProjectChain with
// the schema of cuenv, which the module vendors. It runs if CUENV_SCHEMA
// names the schema directory of a cuenv checkout.
func TestCuenvProjectChain(t *testing.T) {
	schema := os.Getenv("CUENV_SCHEMA")
	if schema == "" {
		t.Skip("CUENV_SCHEMA is not set")
	}
	const depth = 8
	for _, direct := range []bool{true, false} {
		t.Run(fmt.Sprintf("direct=%t", direct), func(t *testing.T) {
			root, top := cuenvChain(t, schema, depth, direct)
			best := time.Hour
			var counts stats.Counts
			for range 5 {
				var elapsed time.Duration
				counts, elapsed, _ = loadedChain(t, root, top)
				best = min(best, elapsed)
			}
			t.Logf("%d unifications, %d disjuncts, best of 5: %v", counts.Unifications, counts.Disjuncts, best)
			if counts.Unifications > 40_000 {
				t.Errorf("%d unifications; want at most 40000", counts.Unifications)
			}
			if best > time.Second {
				t.Errorf("evaluation took %v; want less than 1s", best)
			}
		})
	}
}

// cuenvChain writes a module that vendors the cuenv schema and holds a chain
// of cuenv projects: two for each of the levels 0 to depth, each in a
// directory of its own, with a build and a test task that depend on the
// same task of both projects one level down.
func cuenvChain(t testing.TB, schema string, depth int, direct bool) (root, top string) {
	t.Helper()
	const module = "github.com/cuenv/cuenv"
	root = t.TempDir()
	write := func(name string, data []byte) {
		path := filepath.Join(root, name)
		if err := os.MkdirAll(filepath.Dir(path), 0o777); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, data, 0o666); err != nil {
			t.Fatal(err)
		}
	}
	if err := filepath.WalkDir(schema, func(path string, entry os.DirEntry, err error) error {
		if err != nil || entry.IsDir() {
			return err
		}
		data, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		rel, err := filepath.Rel(schema, path)
		if err != nil {
			return err
		}
		write(filepath.Join("schema", rel), data)
		return nil
	}); err != nil {
		t.Fatal(err)
	}
	write("cue.mod/module.cue", fmt.Appendf(nil, "module: %q\nlanguage: version: \"v0.14.1\"\n", module))

	task := func(body string) string {
		if direct {
			return "schema.#Task & {" + body + "}"
		}
		return "{" + body + "}"
	}
	for level := 0; level <= depth; level++ {
		for _, side := range []string{"a", "b"} {
			name := fmt.Sprintf("l%d%s", level, side)
			var src strings.Builder
			fmt.Fprintf(&src, "package cuenv\n\nimport (\n\t%q\n", module+"/schema")
			if level > 0 {
				fmt.Fprintf(&src, "\tpa \"%s/l%da:cuenv\"\n\tpb \"%s/l%db:cuenv\"\n", module, level-1, module, level-1)
			}
			fmt.Fprintf(&src, ")\n\nschema.#Project\n\nname: %q\n\ntasks: {\n", name)
			for _, label := range []string{"build", "test"} {
				body := fmt.Sprintf("command: \"echo\", args: [%q]", label)
				if level > 0 {
					body += fmt.Sprintf(", dependsOn: [pa.tasks.%s, pb.tasks.%s]", label, label)
				} else if label == "test" {
					body += ", dependsOn: [build]"
				}
				fmt.Fprintf(&src, "\t%s: %s\n", label, task(body))
			}
			src.WriteString("}\n")
			write(filepath.Join(name, "env.cue"), []byte(src.String()))
		}
	}
	return root, fmt.Sprintf("l%da", depth)
}

func BenchmarkImportedProjectChain(b *testing.B) {
	packages, top := projectChain(8, 2, true)
	root := writeModule(b, packages)
	for b.Loop() {
		loadedChain(b, root, top)
	}
}
