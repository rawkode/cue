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
	"strings"
	"testing"

	"cuelang.org/go/internal/core/adt"
)

// A conjunct of a finalized value that is evaluated again, as Value.Expr does
// with each operand, must be evaluated in the environment that evaluation
// settled on.
//
// pipeline[0].task has two disjunctions: #N from #M, and the pattern of tasks,
// which the reference through the let brings along. Its field out is added to
// the clone made for the first one, so the conjuncts of out refer to that
// clone, which evaluation left unfinished when it cloned it again for the
// second. Resuming the clone processes its disjunctions again, and those of
// every task its deps reach, without the sharing that evaluation used. The
// work grows by a factor of about 3.5 per task of the chain: depth 6 ran out
// of 4 GB. The clone also lacks _self from the pattern, so task was not "n0".
func TestSettledEnvironmentComplexity(t *testing.T) {
	for _, depth := range []int{2, 4, 8, 16, 32} {
		ctx, v := evalRecursiveSharing(t, settledEnvironmentSource(depth))

		out := v
		for _, f := range []adt.Feature{
			ctx.StringLabel("pipeline"),
			adt.MakeIntLabel(adt.IntLabel, 0),
			ctx.StringLabel("task"),
			ctx.StringLabel("out"),
		} {
			if out = out.Lookup(f); out == nil {
				t.Fatalf("depth %d: pipeline[0].task.out not found", depth)
			}
		}
		c, count := out.SingleConjunct()
		if count != 1 {
			t.Fatalf("depth %d: out has %d conjuncts, want 1", depth, count)
		}
		env, expr := c.EnvExpr()
		x, ok := expr.(*adt.BinaryExpr)
		if !ok {
			t.Fatalf("depth %d: out is %T, want *adt.BinaryExpr", depth, expr)
		}
		// Evaluation can already have settled this environment.
		settled := adt.SettledEnvironment(env)

		before := *ctx.Stats()
		n := &adt.Vertex{Label: out.Label}
		n.AddConjunct(adt.MakeRootConjunct(settled, x.Y))
		n.Finalize(ctx)
		after := *ctx.Stats()

		unifications := after.Unifications - before.Unifications
		disjuncts := after.Disjuncts - before.Disjuncts
		t.Logf("depth %d: %d unifications, %d disjuncts", depth, unifications, disjuncts)
		const budget = 16
		if unifications > budget || disjuncts > budget {
			t.Fatalf("depth %d: evaluating out again exceeds budget %d: %d unifications, %d disjuncts",
				depth, budget, unifications, disjuncts)
		}
		task := n.Lookup(ctx.StringLabel("task"))
		if task == nil {
			t.Fatalf("depth %d: task not found", depth)
		}
		if s, ok := task.Value().(*adt.String); !ok || s.Str != "n0" {
			t.Fatalf("depth %d: task is %v, want \"n0\"", depth, task.Value())
		}
	}
}

func settledEnvironmentSource(depth int) string {
	var src strings.Builder
	src.WriteString(`#Ref: {task: string}
#T: {
	_self: string | *""
	type?: _|_
	cmd?: string
	script?: string
	({cmd!: string, script?: _|_} | {script!: string, cmd?: _|_})
	out: #Ref & {task: _self}
	deps?: [...#N]
}
#G: {
	type: "group"
	deps?: [...#N]
	[!~"^(type|deps)$"]: #T | #G
}
#S: [...#N]
#N: #T | #G | #S
#M: {type: "matrix", task!: #N}
tasks: [string]~(n,_): ((#T | #G) & {_self: n}) | #S
let T = tasks
pipeline: [...(#N | #M)]
pipeline: [{type: "matrix", task: T.n0}]
tasks: {
`)
	for i := 0; i <= depth; i++ {
		fmt.Fprintf(&src, "\tn%d: {cmd: \"x\"", i)
		if i < depth {
			fmt.Fprintf(&src, ", deps: [n%d]", i+1)
		}
		src.WriteString("}\n")
	}
	src.WriteString("}\n")
	return src.String()
}
