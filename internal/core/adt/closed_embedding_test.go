// Copyright 2026 CUE Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package adt_test

import (
	"fmt"
	"strings"
	"testing"

	"cuelang.org/go/cue"
	"cuelang.org/go/cue/build"
	"cuelang.org/go/cue/cuecontext"
	"cuelang.org/go/cue/format"
	"cuelang.org/go/cue/parser"
	"cuelang.org/go/cue/token"
)

// A closed builtin result embedded at file scope must keep the union scope of
// its struct argument. The embedded definition cannot reject sibling fields
// declared by that same struct, and must not admit fields outside that scope.
func TestClosedEmbeddingAtFileScope(t *testing.T) {
	for _, tc := range []struct {
		name      string
		files     []string
		wantError string
		wantJSON  string
	}{
		{name: "root", files: []string{`
#Base: close({env?: [string]: string})
#Project: close({#Base, name!: string, tasks?: [string]: {command: string}})
#Project & {name: "bench", tasks: n: {command: "echo"}}
`}, wantJSON: `{"name":"bench","tasks":{"n":{"command":"echo"}}}`},
		{name: "root embedding sibling extension", files: []string{`
#Base: close({a?: int})
#Project: close({#Base, b!: int})
#Project
b: 2
extra: 3
`}, wantJSON: `{"b":2,"extra":3}`},
		{name: "nested embedding sibling extension", files: []string{`
#Base: close({a?: int})
#Project: close({#Base, b!: int})
x: {#Project, b: 2, extra: 3}
`}, wantJSON: `{"x":{"b":2,"extra":3}}`},
		{name: "root embedding", files: []string{`
#Base: close({a?: int})
#Project: close({#Base, b!: int})
#Project
b: 2
`}},
		{name: "nested", files: []string{`
#Base: close({a?: int})
#Project: close({#Base, b!: int})
x: #Project & {b: 2}
`}},
		{name: "anonymous embedding", files: []string{`
#Base: close({a?: int})
#Project: close({{#Base}, b!: int})
#Project & {b: 2}
`}},
		{name: "comprehension embedding", files: []string{`
#Base: close({a?: int})
#Project: close({if true {#Base}, b!: int})
#Project & {b: 2}
`}},
		{name: "optional and pattern fields", files: []string{`
#Base: close({a?: int})
#Project: close({#Base, b!: int, c?: string, [=~"^extra"]: int})
#Project & {b: 2, c: "ok", extraField: 3}
`}},
		{name: "multiple files", files: []string{`
#Base: close({a?: int})
#Project: close({#Base, b!: int})
#Project
`, `#Project & {b: 2}`}},
		{name: "default", files: []string{`
#Base: {a?: int}
#Project: close(*{#Base, b: 1} | {#Base, b: 2})
#Project
`}, wantJSON: `{"b":1}`},
		{name: "recursive nested extra field", files: []string{`
#Node: {value: int, deps?: [...#Node]}
#Base: {nodes?: [string]: #Node}
#Project: close({#Base, name!: string})
#Project & {name: "bench", nodes: n: {value: 1, deps: [{value: 2, extra: 3}]}}
`}, wantError: "extra: field not allowed"},
		{name: "unknown root field", files: []string{`
#Base: close({a?: int})
#Project: close({#Base, b!: int})
#Project & {b: 2, extra: 3}
`}, wantError: "extra: field not allowed"},
		{name: "conjunction root", files: []string{`
#Base: close({a?: int})
#Project: close(#Base & {b!: int})
#Project & {b: 2}
`}, wantError: "b: field not allowed"},
		{name: "conjunction nested", files: []string{`
#Base: close({a?: int})
#Project: close(#Base & {b!: int})
x: #Project & {b: 2}
`}, wantError: "b: field not allowed"},
		{name: "deferred conjunction", files: []string{`
#Base: close({a?: int})
#Project: close(#Base & {b?: int})
#Project & {b: 2}
`}, wantError: "b: field not allowed"},
		{name: "deferred conjunction reverse", files: []string{`
#Project & {b: 2}
#Project: close({b?: int} & #Base)
#Base: close({a?: int})
`}, wantError: "b: field not allowed"},
		{name: "deferred conjunction alias", files: []string{`
#Base: close({a?: int})
#Alias: #Base
#Project: close(#Alias & {b?: int})
#Project & {b: 2}
`}, wantError: "b: field not allowed"},
		{name: "independent closed constraints", files: []string{`
#Project: close({a?: int}) & close({b?: int})
#Project & {a: 1}
`}, wantError: "a: field not allowed"},
		{name: "independent closed constraints reverse", files: []string{`
#Project & {a: 1}
#Project: close({b?: int}) & close({a?: int})
`}, wantError: "a: field not allowed"},
		{name: "independent closed constraints alias", files: []string{`
#A: close({a?: int})
#B: close({b?: int})
#Project: #A & #B
#Project & {a: 1}
`}, wantError: "a: field not allowed"},
		{name: "disjunction remains closed", files: []string{`
#Project: close(*{} | 0)
#Project & {extra: 1}
`}, wantError: "extra: field not allowed"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			inst := build.NewContext().NewInstance(".", nil)
			for i, src := range tc.files {
				file, err := parser.ParseFile(fmt.Sprintf("file%d.cue", i), "package compat\n"+src, parser.Version("v0.14.1"))
				if err != nil {
					t.Fatal(err)
				}
				if err := inst.AddSyntax(file); err != nil {
					t.Fatal(err)
				}
			}
			v := cuecontext.New().BuildInstance(inst)
			err := v.Validate()
			if tc.wantError != "" {
				if err == nil || !strings.Contains(err.Error(), tc.wantError) {
					t.Fatalf("error = %v; want %q", err, tc.wantError)
				}
			} else if err != nil {
				t.Fatal(err)
			} else {
				data, err := v.MarshalJSON()
				if err != nil {
					t.Fatal(err)
				}
				if tc.wantJSON != "" && string(data) != tc.wantJSON {
					t.Fatalf("JSON = %s; want %s", data, tc.wantJSON)
				}
			}
		})
	}
}

// A close() elsewhere in the receiving node must not change the scope of a
// recursively closed source or force the default of a sibling disjunction.
func TestClosedEmbeddingPreservesRecursiveRoot(t *testing.T) {
	const source = `
root: input: foo: {
 metadata: name: *"foo" | string
 id: "id-\(metadata.name)"
 #deps: [string]: _
 #deps: root: {}
 spec: replicas: 1
}
{root.input.foo.#deps}
`
	for _, tc := range []struct{ name, source string }{
		{"recursive root", source},
		{"unrelated close before", "close({root: _})\n" + source},
		{"unrelated close after", source + "close({root: _})\n"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			file, err := parser.ParseFile("root.cue", tc.source, parser.Version("v0.14.1"))
			if err != nil {
				t.Fatal(err)
			}
			value := cuecontext.New().BuildFile(file)
			if err := value.Validate(); err != nil {
				t.Fatal(err)
			}
			name := value.LookupPath(cue.ParsePath("root.input.foo.metadata.name"))
			raw, err := format.Node(name.Syntax(cue.Raw()))
			if err != nil {
				t.Fatal(err)
			}
			if string(raw) != `*"foo" | string` {
				t.Fatalf("name syntax = %s; want unselected default disjunction", raw)
			}
			data, err := value.MarshalJSON()
			if err != nil {
				t.Fatal(err)
			}
			const expected = `{"root":{"input":{"foo":{"metadata":{"name":"foo"},"id":"id-foo","spec":{"replicas":1}}}}}`
			if string(data) != expected {
				t.Fatalf("JSON = %s; want %s", data, expected)
			}
		})
	}
}

func TestClosedEmbeddingAcrossPackages(t *testing.T) {
	const project = `
#Base: close({a?: int})
#Project: close({#Base, b!: int})
`
	for _, tc := range []struct{ name, dependency, source, wantJSON string }{
		{"root extension", project, "dep.#Project\nb:2\nextra:3", `{"b":2,"extra":3}`},
		{"nested extension", project, "x:{dep.#Project,b:2,extra:3}", `{"x":{"b":2,"extra":3}}`},
		{"conjunction extra rejected", project, "dep.#Project & {b:2,extra:3}", ""},
		{"conjunction nested extra rejected", project, "x:dep.#Project & {b:2,extra:3}", ""},
		{"direct closed intersection accepts common field", "#A: close({a?: int})\n#B: close({a?: int})", "out:dep.#A & dep.#B & {a:1}", `{"out":{"a":1}}`},
		{"direct closed intersection rejects extra", "#A: close({a?: int})\n#B: close({b?: int})", "out:dep.#A & dep.#B & {a:1}", ""},
		{"nested closed intersection rejects extra", "#A: close({a?: int})\n#B: close({b?: int})", "out:{dep.#A & dep.#B & {a:1}}", ""},
	} {
		t.Run(tc.name, func(t *testing.T) {
			context := build.NewContext()
			dependency := context.NewInstance("dep", nil)
			dependency.ImportPath = "example.com/dep"
			add := func(instance *build.Instance, source string) {
				file, err := parser.ParseFile("in.cue", source, parser.Version("v0.14.1"))
				if err != nil {
					t.Fatal(err)
				}
				if err := instance.AddSyntax(file); err != nil {
					t.Fatal(err)
				}
			}
			add(dependency, "package dep\n"+tc.dependency)
			instance := context.NewInstance("main", func(_ token.Pos, path string) *build.Instance {
				if path != dependency.ImportPath {
					t.Fatalf("unexpected import %q", path)
				}
				return dependency
			})
			add(instance, "package main\nimport \"example.com/dep\"\n"+tc.source)
			if err := instance.Complete(); err != nil {
				t.Fatal(err)
			}
			value := cuecontext.New().BuildInstance(instance)
			data, err := value.MarshalJSON()
			if tc.wantJSON == "" {
				if err == nil {
					t.Fatalf("unexpected accepted fields: %s", data)
				}
			} else if err != nil {
				t.Fatal(err)
			} else if string(data) != tc.wantJSON {
				t.Fatalf("JSON = %s; want %s", data, tc.wantJSON)
			}
		})
	}
}
