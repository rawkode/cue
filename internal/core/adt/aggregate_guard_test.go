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
	"encoding/json"
	"fmt"
	"reflect"
	"testing"

	"cuelang.org/go/cue/cuecontext"
	"cuelang.org/go/cue/parser"
)

// Inspecting an optional aggregate before replaying a reference must preserve
// the aggregate's fields, even when both source and receiver have disjunctions.
func TestRecursiveSharingAggregateGuard(t *testing.T) {
	for _, version := range []string{"v0.14.1", "v0.16.0"} {
		for _, aggregate := range []struct{ name, constraint, value, json string }{
			{"struct", "{...}", "{b:1}", `{"b":1}`},
			{"list", "[... ]", "[{}]", `[{}]`},
			{"scalar", "int", "1", `1`},
		} {
			for _, guard := range []string{"", "if a != _|_ {_x:1}"} {
				for _, order := range []string{"source first", "reference first"} {
					for _, scope := range []string{"root", "nested"} {
						name := fmt.Sprintf("%s/%s/guard=%t/%s/%s", version, aggregate.name, guard != "", order, scope)
						t.Run(name, func(t *testing.T) {
							fields := "x:#T & {a:" + aggregate.value + "}, y:x"
							if order == "reference first" {
								fields = "y:x, x:#T & {a:" + aggregate.value + "}"
							}
							value := "#P & {" + fields + "}"
							expected := `{"x":{"a":` + aggregate.json + `},"y":{"a":` + aggregate.json + `}}`
							if scope == "nested" {
								value = "v:" + value
								expected = `{"v":` + expected + `}`
							}
							source := "#T:{a?:" + aggregate.constraint + "\n" + guard + "}\n#P:{x:#T|int,y:#T|int}\n" + value
							file, err := parser.ParseFile("aggregate.cue", source, parser.Version(version))
							if err != nil {
								t.Fatal(err)
							}
							got, err := cuecontext.New().BuildFile(file).MarshalJSON()
							if err != nil {
								t.Fatal(err)
							}
							var gotValue, wantValue any
							if err := json.Unmarshal(got, &gotValue); err != nil {
								t.Fatal(err)
							}
							if err := json.Unmarshal([]byte(expected), &wantValue); err != nil {
								t.Fatal(err)
							}
							if !reflect.DeepEqual(gotValue, wantValue) {
								t.Fatalf("JSON = %s; want %s", got, expected)
							}
						})
					}
				}
			}
		}
		for _, aggregate := range []struct{ name, constraint, value string }{
			{"closed struct", "{b?:int}", "{b:1,extra:2}"},
			{"closed list element", "[...{b?:int}]", "[{b:1,extra:2}]"},
		} {
			t.Run(version+"/"+aggregate.name+" rejects extra", func(t *testing.T) {
				source := "#T:{a?:" + aggregate.constraint + "\nif a != _|_ {_x:1}}\n#P:{x:#T|int,y:#T|int}\n#P & {x:#T & {a:" + aggregate.value + "},y:x}"
				file, err := parser.ParseFile("aggregate.cue", source, parser.Version(version))
				if err != nil {
					t.Fatal(err)
				}
				if data, err := cuecontext.New().BuildFile(file).MarshalJSON(); err == nil {
					t.Fatalf("accepted extra fields: %s", data)
				}
			})
		}
	}
}
