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

package provenance_test

import (
	"fmt"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"cuelang.org/go/cue/cuecontext"
	"cuelang.org/go/cue/load"
	"cuelang.org/go/cue/provenance"
)

const importSchema = `import "example.com/m/schema"` + "\n"

func analyze(t *testing.T, attributes, source, schema string) []string {
	t.Helper()
	dir := t.TempDir()
	overlay := map[string]load.Source{
		filepath.Join(dir, "cue.mod/module.cue"): load.FromString(`module: "example.com/m@v0", language: version: "v0.16.0"`),
		filepath.Join(dir, "a.cue"):              load.FromString(attributes + "package a\n" + source),
		filepath.Join(dir, "schema/s.cue"):       load.FromString("package schema\n" + schema),
	}
	instances := load.Instances([]string{"."}, &load.Config{Dir: dir, ModuleRoot: dir, Overlay: overlay})
	if err := instances[0].Err; err != nil {
		t.Fatal(err)
	}
	value := cuecontext.New(cuecontext.CUE_DEBUG("sharing=false")).BuildInstance(instances[0])
	if err := value.Err(); err != nil {
		t.Fatal(err)
	}
	dependencies, err := provenance.Analyze(value)
	if err != nil {
		t.Fatal(err)
	}
	var result []string
	for _, dependency := range dependencies {
		result = append(result, fmt.Sprintf("%v -> %v %v", dependency.Field, dependency.Target, dependency.Use))
	}
	return result
}

func TestAnalyze(t *testing.T) {
	testCases := []struct {
		name, attributes, source, schema string
		// want lists the dependencies of the fields it mentions, in any order.
		want []string
		// absent lists fields that have no dependency on o at all.
		absent []string
	}{{
		name:   "direct",
		source: `o: string, x: o`,
		want:   []string{"x -> o value"},
	}, {
		name:   "constrained",
		source: `o: string, x: o & =~"^a" & "abc"`,
		want:   []string{"x -> o value"},
	}, {
		name:   "chain",
		source: `o: string, a: o, x: a`,
		want:   []string{"a -> o value", "x -> a value"},
	}, {
		name:   "computed",
		source: `o: string, n: number, x: "a-\(o)", y: n + 1`,
		want:   []string{"x -> o computed", "y -> n computed"},
	}, {
		name:   "builtin",
		source: "import \"strings\"\no: string, x: strings.ToUpper(o)",
		want:   []string{"x -> o computed"},
	}, {
		name:   "if",
		source: `o: string, x: {if o == "a" {y: 1}}`,
		want:   []string{"x.y -> o control"},
		absent: []string{"x ->"},
	}, {
		name:   "if narrowed",
		source: `o: string, x: {if (o & "a") == "a" {y: 1}}`,
		want:   []string{"x.y -> o control"},
	}, {
		name:   "if with embedded value",
		source: `o: string, x: {if o == "a" {{y: 1}}}`,
		want:   []string{"x -> o control"},
	}, {
		name:   "value in if body",
		source: `o: string, f: true, x: {if f {y: o}}`,
		want:   []string{"x.y -> f control", "x.y -> o value"},
	}, {
		name:   "dynamic label",
		source: `o: string, x: {("\(o)"): 1}`,
		want:   []string{"x -> o control"},
	}, {
		name:   "pattern",
		source: `o: string, x: {[o]: 1, a: 1}`,
		want:   []string{"x -> o control"},
	}, {
		name:   "index",
		source: `o: string, m: {a: 1}, x: m[o]`,
		want:   []string{"x -> o control"},
	}, {
		name:   "default",
		source: `o: string, x: *"a" | o`,
		want:   []string{"x -> o control"},
	}, {
		name:   "presence of a field",
		source: `o: string, a: o, x: {if a != _|_ {y: 1}}`,
		want:   []string{"x.y -> a presence"},
		absent: []string{"x.y -> o"},
	}, {
		name:   "presence of a constrained expression",
		source: `o: string, x: {if (o & =~"^a") != _|_ {y: 1}}`,
		want:   []string{"x.y -> o control"},
	}, {
		name:   "missing optional field",
		source: `a: {b?: string}, x: {if a.b != _|_ {y: 1}}`,
		want:   []string{"x.y -> a.b presence"},
	}, {
		name:   "unrelated comprehensions",
		source: `o: string, _b: "x", _z: {if _b == "x" {v: 1}}, _xs: ["a"], _l: {for x in _xs {(x): 1}}`,
		absent: []string{"-> o"},
	}, {
		name:   "list comprehension index",
		source: `o: string, _b?: string, v: [if _b != _|_ {_b}, "0"][0]`,
		absent: []string{"-> o"},
	}, {
		name:   "let",
		source: "o: string\nlet L = o\nx: L",
		want:   []string{"x -> o value"},
	}, {
		name:   "let chain in condition",
		source: "o: string\nlet L = o\nlet M = L & \"a\"\nx: {if M == \"a\" {y: 1}}",
		want:   []string{"x.y -> o control"},
	}, {
		name:   "let selection",
		source: "o: string\nlet L = {a: o, b: \"lit\"}\nx: L.a, y: L.b",
		want:   []string{"x -> o value"},
		absent: []string{"y ->"},
	}, {
		name:   "let presence",
		source: "o: string\nlet M = o & \"a\"\nx: {if M != _|_ {y: 1}}",
		want:   []string{"x.y -> o control"},
	}, {
		name:   "field alias",
		source: `o: string, A=a: o, x: A`,
		want:   []string{"x -> a value"},
	}, {
		name:   "value alias",
		source: `o: string, s: W={z: o, y: W.z}`,
		want:   []string{"s.z -> o value", "s.y -> s.z value"},
	}, {
		name:   "shadowing",
		source: `o: string, s: {o: "lit", x: o}, y: s.x`,
		want:   []string{"s.x -> s.o value", "y -> s.x value"},
		absent: []string{"-> o"},
	}, {
		name:   "sibling condition",
		source: `o: string, s: {i: o, if i == "a" {y: 1}}`,
		want:   []string{"s.i -> o value", "s.y -> s.i control"},
	}, {
		name:   "for keys",
		source: `r: {a: {o: string}}, x: {for k, _ in r {(k): 1}}`,
		want:   []string{"x -> r presence"},
		absent: []string{"x.a ->"},
	}, {
		name:   "for value in value",
		source: `r: {a: {o: string}}, x: {for k, v in r {(k): v.o}}`,
		want:   []string{"x -> r presence", "x.a -> r.a.o value"},
	}, {
		name:   "for value in fixed field",
		source: `r: {a: {o: string}}, x: {for _, v in r {y: v.o}}`,
		want:   []string{"x.y -> r presence", "x.y -> r.a.o value"},
	}, {
		name:   "for value in condition",
		source: `r: {a: {o: string}}, x: {for k, v in r if v.o == "a" {(k): 1}}`,
		want:   []string{"x -> r presence", "x -> r.a.o control"},
	}, {
		name:   "for over a default",
		source: `r: {a: {o: string}}, x: {for k, v in *r | {} {(k): v.o}}`,
		want:   []string{"x -> r presence", "x.a -> r.a.o value"},
		absent: []string{"x -> r control"},
	}, {
		name:   "for over a default into a fixed field",
		source: `r: {a: {o: string}}, x: {for _, v in *r | {} {y: v.o}}`,
		want:   []string{"x.y -> r.a.o value"},
	}, {
		name:   "for over a default in a condition",
		source: `r: {a: {o: string}}, x: {for k, v in *r | {} if (v.o & "z") == "z" {c: 1}}`,
		want:   []string{"x.c -> r.a.o control"},
	}, {
		name:   "for over literal",
		source: `o: string, x: {for k, v in {a: o} {(k): v}}`,
		want:   []string{"x.a -> o value"},
		absent: []string{"x -> o"},
	}, {
		name:   "for over list with control",
		source: `o: string, x: {for v in [o & "a"] {(v): 1}}`,
		want:   []string{"x -> o control"},
	}, {
		name:   "let clause interpolating a loop variable",
		source: `o: string, x: {for k, _ in {a: o} let n = "\(k)-x" {(n): 1}}`,
		absent: []string{"-> o"},
	}, {
		name:   "let clause in condition",
		source: `r: {a: {o: string}}, x: {for k, v in r let i = v.o & "a" if i == "a" {(k): 1}}`,
		want:   []string{"x -> r.a.o control"},
	}, {
		name:       "try assignment",
		attributes: "@experiment(try)\n",
		source:     `o: string, a: {b?: string}, x: {try c = a.b? {y: c}}`,
		absent:     []string{"-> o"},
	}, {
		name:   "inline selection",
		source: `o: string, x: ({a: o, b: a}).b, y: ({a: o, b: "lit"}).b`,
		want:   []string{"x -> o value"},
		absent: []string{"y ->"},
	}, {
		name:   "function pattern",
		source: `o: string, #F: {in: string, v: in}, x: (#F & {in: o}).v`,
		want:   []string{"x -> o value"},
	}, {
		name:   "function pattern computing",
		source: `o: string, #F: {in: string, v: "\(in)"}, x: (#F & {in: o}).v`,
		want:   []string{"x -> o computed"},
	}, {
		name:   "function pattern embedded",
		source: `o: string, #F: {in: string, "\(in)"}, x: #F & {in: o}`,
		want:   []string{"x.in -> o value", "x -> x.in computed"},
	}, {
		name:       "self",
		attributes: "@experiment(aliasv2)\n",
		source:     `o: string, s: {a: o, b: self.a}`,
		want:       []string{"s.a -> o value", "s.b -> s.a value"},
	}, {
		name:   "unified definition binds to the instance",
		source: `s: #S, #S: {o: string, x: {if o == "a" {y: 1}}}`,
		want:   []string{"s.x.y -> s.o control", "#S.x.y -> #S.o control"},
	}, {
		name:   "imported definition binds to the instance",
		source: importSchema + `s: schema.#S`,
		schema: `#S: {o: string, _i: o, x: {if (_i & "a") == "a" {y: 1}}, z: _i}`,
		want:   []string{"s._i -> s.o value", "s.x.y -> s._i control", "s.z -> s._i value"},
	}, {
		name:   "same hidden name in another package",
		source: importSchema + "o: string, _b: o, x: schema.#D",
		schema: `#D: {_b: "a", z: {if _b == "a" {y: 1}}}`,
		absent: []string{"x.z.y -> o", "x.z.y -> _b"},
	}, {
		name:   "imported package value",
		source: importSchema + "o: string, x: schema.C",
		schema: `C: "a"`,
		absent: []string{"x ->"},
	}, {
		name:   "caller argument",
		source: importSchema + "o: string, x: schema.#G & {arg: o & \"a\"}",
		schema: `#G: {arg: string, z: {if arg == "a" {y: 1}}}`,
		want:   []string{"x.arg -> o value", "x.z.y -> x.arg control"},
	}, {
		name:   "disjunct control",
		source: `o: string, x: *{if o == "a" {y: 1}, z: 1} | {w: 1}`,
		want:   []string{"x -> o control"},
	}, {
		name:   "selected default field",
		source: `o: string, x: *{a: o} | {b: 1}`,
		want:   []string{"x.a -> o value"},
	}, {
		name:   "unselected disjunct",
		source: `o: string, x: *{c: 1} | {a: {("\(o)"): 1}}`,
		want:   []string{"x -> o control"},
	}, {
		name:   "close",
		source: `o: string, x: close({a: o})`,
		want:   []string{"x.a -> o value"},
		absent: []string{"x -> o control"},
	}, {
		name:   "len of a field",
		source: `o: string, r: {a: o}, x: {if len(r) > 0 {y: 1}}`,
		want:   []string{"x.y -> r presence"},
		absent: []string{"x.y -> o", "x.y -> r.a"},
	}, {
		name:   "len of an expression",
		source: `o: string, x: {if len(o & "a") > 0 {y: 1}}`,
		want:   []string{"x.y -> o control"},
	}, {
		name:   "list destination",
		source: `o: string, x: a: b: [{t: o}]`,
		want:   []string{"x.a.b[0].t -> o value"},
	}, {
		name:   "list comprehension element",
		source: `r: {a: {o: string}}, x: [for _, v in r {v.o}]`,
		want:   []string{"x[0] -> r.a.o value", "x -> r presence"},
	}, {
		name:   "struct copy",
		source: `s: {o: string}, x: s`,
		want:   []string{"x -> s value"},
	}, {
		name:   "embedded reference",
		source: `s: {o: string}, x: {s, y: 1}`,
		want:   []string{"x -> s value"},
	}, {
		name:   "false branch",
		source: `o: string, x: {if false {y: o}}`,
		absent: []string{"-> o"},
	}, {
		name:       "else clause",
		attributes: "@experiment(try)\n",
		source:     `o: string, x: {if false {y: 1} else {z: o}}`,
		want:       []string{"x.z -> o value"},
	}, {
		name:   "optional guard then condition",
		source: `o: string, _p?: string, x: {if _p != _|_ if (o & "a") == "a" {y: 1}}`,
		absent: []string{"x.y -> o"},
	}, {
		name:   "selecting through a let of a struct",
		source: "r: {a: {o: string}}\nlet C = r.a\nx: C.o",
		want:   []string{"x -> r.a.o value"},
	}, {
		name:   "selecting through an inline copy",
		source: `r: {a: {o: string}}, x: ({p: r.a}).p.o, y: (r.a & {z: 1}).o`,
		want:   []string{"x -> r.a.o value", "y -> r.a.o value"},
	}, {
		name:   "loop over a literal holding a struct",
		source: `r: {a: {o: string}}, x: {for k, v in {p: r.a} {(k): v.o}}`,
		want:   []string{"x.p -> r.a.o value"},
	}, {
		name:   "closed definition binds to the instance",
		source: `o: string, #C: close({arg: string, ("\(arg)"): "v"}), x: #C & {arg: o}`,
		want:   []string{"x -> x.arg control", "x.arg -> o value"},
	}, {
		name:   "loop over a list holding another loop variable",
		source: `r: {a: {b: {o: bool}}}, x: {for _, v in r {for _, w in [v] {for _, y in [w] {c: {if (y.b.o & false) {d: 1}}}}}}`,
		want:   []string{"x.c.d -> r.a.b.o control"},
	}, {
		name:   "arm selected by a field holding a value",
		source: `o: string, x: (*{_k: "a", v: 1} | {_k: "b", v: 2}) & {_k: o}`,
		want:   []string{"x -> x alternatives", "x._k -> o value"},
	}, {
		name:   "a single remaining arm has no alternatives",
		source: `o: string, x: null | {a: o}, y: x & {b: 1}`,
		absent: []string{"y -> y alternatives"},
	}, {
		name:   "selected list element with a condition beside it",
		source: `o: string, x: [if (o & "a") != _|_ {"y"}, "z"][0]`,
		want:   []string{"x -> o control"},
	}, {
		name:   "error in a let changes a comparison with bottom",
		source: "o: string\nlet S = {z: o & \"a\"}\nx: {if S != _|_ {y: 1}}",
		want:   []string{"x.y -> o control"},
	}, {
		name:   "error in an arm of a for source",
		source: `o: string, x: {for k, _ in *{a: o & "a"} | {b: 2} {(k): 1}}`,
		want:   []string{"x -> o control"},
	}, {
		name:       "explicitly opened reference",
		attributes: "@experiment(explicitopen)\n",
		source:     `o: string, _t: {if o == "a" {y: 1}}, x: _t...`,
		want:       []string{"x.y -> o control"},
	}, {
		name:   "selecting a field that is not there",
		source: `r: {o: string}, x: *r.missing | "none"`,
		want:   []string{"x -> r presence"},
		absent: []string{"x -> r control", "x -> r.o"},
	}, {
		name:   "selecting an optional field",
		source: `o: string, r: {a?: o}, x: *r.a | "none"`,
		want:   []string{"x -> r.a presence"},
		absent: []string{"x -> o", "x -> r.a control"},
	}, {
		name:   "len of a literal",
		source: `o: string, x: len({a: o}), y: len([o])`,
		absent: []string{"x -> o", "y -> o"},
	}, {
		name:   "hidden fields of different packages stay apart",
		source: importSchema + "o: string, x: schema.#S & {_x: o, y: \"\\(_x)\"}",
		schema: `#S: {_x: "lit", z: _x}`,
		want:   []string{"x._x -> o value", "x.y -> x._x computed"},
	}, {
		name:   "selection from an inline struct embedding a field",
		source: `r: {o: string}, x: ({r}).o`,
		want:   []string{"x -> r.o value"},
	}, {
		name:   "selection from an inline struct embedding a conditional",
		source: `o: string, _t: {p: *1 | int, if (o & "a") != _|_ {("p"): 2}}, x: ({_t}).p`,
		want:   []string{"x -> o control"},
	}, {
		name:   "scalar copy is read through",
		source: `o: string, a: "\(o)", x: a`,
		want:   []string{"x -> a value", "x -> o computed"},
	}, {
		name:   "value alias in a conditional",
		source: `o: string, s: W={z: o, if W.z == "a" {y: 1}}`,
		want:   []string{"s.y -> s.z control"},
	}, {
		name:   "field used in a condition of a definition",
		source: `o: string, #D: {i: string, if i == "a" {{y: 1}}}, x: #D & {i: o}`,
		want:   []string{"x -> x.i control", "x.i -> o value"},
	}, {
		name:   "two sources",
		source: `o: string, p: string, x: o & p`,
		want:   []string{"x -> o value", "x -> p value"},
	}, {
		name:   "conflicting hidden validator stays local",
		source: `o: string, _v: o & =~"^a", x: "lit"`,
		want:   []string{"_v -> o value"},
		absent: []string{"x ->"},
	}}
	for _, testCase := range testCases {
		t.Run(testCase.name, func(t *testing.T) {
			got := analyze(t, testCase.attributes, testCase.source, testCase.schema)
			for _, want := range testCase.want {
				if !slices.Contains(got, want) {
					t.Errorf("missing %q in:\n%s", want, strings.Join(got, "\n"))
				}
			}
			for _, absent := range testCase.absent {
				for _, line := range got {
					if strings.Contains(line, absent) {
						t.Errorf("unexpected %q in:\n%s", absent, strings.Join(got, "\n"))
					}
				}
			}
		})
	}
}
