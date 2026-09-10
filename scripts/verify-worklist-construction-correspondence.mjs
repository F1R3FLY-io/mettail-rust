import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { fileURLToPath, pathToFileURL } from "node:url";

const replacements = [
  ["", "use mettail_rholang_frontend::construction::{append_fold, ValueTarget};\n"],
  [`                let parts = self.stacks.pop_values(n);
                let par = parts.into_iter().fold(Target::empty(), Target::append);
                self.stacks.value(par);`,
    `                self.stacks
                    .inner
                    .reduce_values(n, |parts| append_fold(&mut Target, parts))
                    .expect("rholang lowering: valid parallel fold construction");`],
  [`                let right = self.stacks.pop_value();
                let left = self.stacks.pop_value();
                self.stacks.value(Target::append(left, right));`,
    `                self.stacks
                    .inner
                    .reduce_pair(|left, right| ValueTarget::append(&mut Target, left, right))
                    .expect("rholang lowering: valid parallel pair construction");`],
];
export function beforeWorklistConstruction(source) {
  for (const [before, after] of replacements) {
    assert.equal(source.split(after).length - 1, 1, "one exact shared transition delegation");
    source = source.replace(after, before);
  }
  return source;
}
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const root = fileURLToPath(new URL("../", import.meta.url));
  const path = "rholang-runtime/src/rholang_ast.rs";
  const baseline = "b914ea99ceff4cf2a848ee1fec2cb8ce49a4fdb4";
  const before = execFileSync("git", ["-c", "core.fsmonitor=false", "show", `${baseline}:${path}`],
    { cwd: root, encoding: "utf8", maxBuffer: 8 * 1024 * 1024 });
  const source = readFileSync(`${root}${path}`, "utf8");
  assert.equal(beforeWorklistConstruction(source), before);
  for (const [from, to] of [
    [".reduce_values(n,", ".reduce_values(n + 1,"],
    ["ValueTarget::append(&mut Target, left, right)", "ValueTarget::append(&mut Target, right, left)"],
    ["fn enter_proc(", "fn corrupted_enter_proc("],
  ]) assert.throws(() => assert.equal(beforeWorklistConstruction(source.replace(from, to)), before));
  console.log(`Shared construction correspondence passed against ${baseline}; arity, operand and producer mutations rejected.`);
}
