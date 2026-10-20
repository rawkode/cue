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
	"testing"

	"cuelang.org/go/cue/cuecontext"
	"cuelang.org/go/cue/parser"
)

// A disjunct's own pending comprehension is not an ancestor comprehension.
// Finalizing for it while expanding a nested union can lose the optional-bottom
// constraints that make the command and script alternatives exclusive.
func TestOwnComprehensionPreservesNestedDisjunction(t *testing.T) {
	for _, version := range []string{"v0.14.1", "v0.16.0"} {
		for _, condition := range []string{"false", "true"} {
			for _, order := range []string{"declaration first", "value first", "conjuncts reversed"} {
				for _, tc := range []struct{ name, data, wantJSON string }{
					{"command", `{command: "echo"}`, `{"x":{"command":"echo"}}`},
					{"script", `{script: "echo"}`, `{"x":{"script":"echo"}}`},
					{"both rejected", `{command: "echo", script: "both"}`, ""},
				} {
					t.Run(version+"/"+condition+"/"+order+"/"+tc.name, func(t *testing.T) {
						definition := fmt.Sprintf(`#T: {
 command?: string
 script?: string
 ({command!: string, script?: _|_} | {script!: string, command?: _|_})
 if %s {}
}
`, condition)
						value := fmt.Sprintf("x: (((#T | int) & {}) | []) & #T & %s\n", tc.data)
						source := definition + value
						switch order {
						case "value first":
							source = value + definition
						case "conjuncts reversed":
							source = definition + fmt.Sprintf("x: %s & #T & (((#T | int) & {}) | [])\n", tc.data)
						}
						file, err := parser.ParseFile("comp.cue", source, parser.Version(version))
						if err != nil {
							t.Fatal(err)
						}
						evaluated := cuecontext.New().BuildFile(file)
						data, err := evaluated.MarshalJSON()
						if tc.wantJSON == "" {
							if err == nil {
								t.Fatalf("mutually exclusive fields accepted: %s", data)
							}
						} else if err != nil {
							t.Fatal(err)
						} else if string(data) != tc.wantJSON {
							t.Fatalf("JSON = %s; want %s", data, tc.wantJSON)
						}
					})
				}
			}
		}
	}
}
