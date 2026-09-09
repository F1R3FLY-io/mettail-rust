import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

// Check the extraction boundary, not arbitrary Rust equivalence. The new
// storage is separately modeled/tested; this proves no producer, constructor,
// environment, oracle or staging code slipped into this particular refactor.
const root = fileURLToPath(new URL("../", import.meta.url));
const baseline = "a04cc83f27fdf106270de3faf71dfab3b4bc6c3d";
const before = path => execFileSync("git", ["-c", "core.fsmonitor=false", "show", `${baseline}:${path}`],
  { cwd: root, encoding: "utf8", maxBuffer: 8 * 1024 * 1024 });
const after = path => readFileSync(new URL(`../${path}`, import.meta.url), "utf8");
function outsideStorage(text) {
  const start = "/// The two stacks, plus the three incremental counters the deficit invariant needs.";
  const end = "/// Everything one drive owns.";
  const i = text.indexOf(start);
  const j = text.indexOf(end, i);
  assert(i >= 0 && j > i, "storage boundary exists");
  assert.equal(text.indexOf(start, i + 1), -1, "unique storage boundary");
  return (text.slice(0, i) + text.slice(j))
    .replaceAll("[`Stacks::work`]", "[`Stacks`]")
    .replaceAll("drive.stacks.values.len()", "drive.stacks.value_count()");
}
const path = "rholang-runtime/src/rholang_ast.rs";
assert.equal(outsideStorage(after(path)), outsideStorage(before(path)),
  "entire lowerer outside storage and exact accessor replacements must remain unchanged");
for (const oracle of [
  "rholang-runtime/tests/support/rholang_ast_recursive_oracle.rs",
  "rholang-runtime/src/rholang_formula.rs",
  "rholang-runtime/src/ddl_ast.rs",
  "languages/src/rholang.rs",
]) assert.equal(after(oracle), before(oracle), `unchanged source: ${oracle}`);
assert.throws(() => assert.equal(
  outsideStorage(after(path).replace("fn enter_proc(", "fn corrupted_enter_proc(")),
  outsideStorage(before(path))), "producer mutation must be detected");
console.log(`Storage-only extraction correspondence passed against ${baseline}; producer mutation rejected.`);
