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

package embed_test

import (
	iofs "io/fs"
	"os"
	"path/filepath"
	"testing"
	"testing/fstest"

	"cuelang.org/go/cue"
	"cuelang.org/go/cue/cuecontext"
	"cuelang.org/go/cue/load"
)

func TestInstanceEmbedFSReplacesTheDisk(t *testing.T) {
	dir := t.TempDir()
	for name, content := range map[string]string{
		"cue.mod/module.cue": `module: "example.com/m@v0", language: version: "v0.16.0"`,
		"a.cue":              "@extern(embed)\npackage a\nx: _ @embed(file=\"a.json\")\ny: _ @embed(glob=\"d/*.json\")\n",
		"a.json":             `{"from": "disk"}`,
	} {
		path := filepath.Join(dir, name)
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	instance := load.Instances([]string{"."}, &load.Config{Dir: dir, ModuleRoot: dir})[0]
	if err := instance.Err; err != nil {
		t.Fatal(err)
	}
	var asked []string
	instance.EmbedFS = func(requested string) iofs.StatFS {
		asked = append(asked, requested)
		return fstest.MapFS{
			"a.json":   {Data: []byte(`{"from": "memory"}`)},
			"d/b.json": {Data: []byte(`{"from": "glob"}`)},
		}
	}
	value := cuecontext.New().BuildInstance(instance)
	if err := value.Err(); err != nil {
		t.Fatal(err)
	}
	for path, want := range map[string]string{"x.from": "memory", `y."d/b.json".from`: "glob"} {
		got, err := value.LookupPath(cue.ParsePath(path)).String()
		if err != nil || got != want {
			t.Errorf("%s = %q, %v; want %q", path, got, err, want)
		}
	}
	if len(asked) == 0 || asked[0] != dir {
		t.Errorf("asked for %q, want %q", asked, dir)
	}
}
