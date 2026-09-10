import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { fileURLToPath, pathToFileURL } from "node:url";

// Edit-boundary evidence only. Pins identify the reviewed increment; model
// proofs and executable tests are the separate behavioral evidence. Recover
// all other source byte for byte, including the URI sort and metadata helper.
const root = fileURLToPath(new URL("../", import.meta.url));
const baseline = "73079ebcea44ffe19b357477a0743359d2d89a1a";
const driver = "rholang-runtime/src/rholang_ast.rs";
const target = "rholang-runtime/src/rholang_ast/target.rs";
const construction = "rholang-frontend/src/construction.rs";
const read = path => readFileSync(`${root}${path}`, "utf8");
const old = path => execFileSync("git", ["-c", "core.fsmonitor=false", "show", `${baseline}:${path}`],
  { cwd: root, encoding: "utf8", maxBuffer: 8 * 1024 * 1024 });
const digest = source => createHash("sha256").update(source).digest("hex");
function section(source, start, end) {
  const i = source.indexOf(start), j = source.indexOf(end, i + start.length);
  assert(i >= 0 && j > i, `source boundary exists: ${start}`);
  assert.equal(source.indexOf(start, i + 1), -1, `unique source boundary: ${start}`);
  return source.slice(i, j);
}
function replace(source, after, before) {
  assert.equal(source.split(after).length - 1, 1, `one exact extension: ${after}`);
  return source.replace(after, before);
}
function pinned(source, start, end, hash, before) {
  const current = section(source, start, end);
  assert.equal(digest(current), hash, `reviewed Fresh section: ${start}`);
  return replace(source, current, before);
}
export function beforeFreshSource(source) {
  const previous = old(driver);
  for (const [start, prior, end, hash] of [
    ["            Proc::PNew(scope) => {", "            Proc::PNew(scope) => {",
      "            // ── A-S4 cast purity", "20f9d32bf37316c19bd1e0dc33e871d30536d5ec0526a3fc5d51013381cac2b2"],
    ["            Kont::New { descriptor } => {", "            Kont::New { binder_count, uris } => {",
      "            Kont::SpecAll => {", "f7debd8b863a9ecbb2318fc70c8f50e8c11a51e8825e23a27cc624818683e7e3"],
  ]) source = pinned(source, start, end, hash, section(previous, prior, end));
  source = replace(source,
    "use mettail_rholang_frontend::construction::{\n    append_fold, CheckedFreshDescriptor, FreshShape, ValueTarget,\n};",
    "use mettail_rholang_frontend::construction::{append_fold, ValueTarget};");
  source = replace(source,
    "    FreshConstruction(mettail_rholang_frontend::construction::ConstructionError),\n", "");
  return replace(source,
    "    /// `PNew`'s `new`-scope wrapper over its lowered body. As with the DDL\n    /// plan, keep the owned descriptor out of the common work-item layout.\n    New { descriptor: Box<CheckedFreshDescriptor> },",
    "    /// `PNew`'s `new`-scope wrapper over its lowered body.\n    New { binder_count: usize, uris: Vec<String> },");
}
export function beforeFreshTarget(source) {
  source = pinned(source, "    /// Staged checked-descriptor path.", "    pub(super) fn append(",
    "98023a20ddbab8bac85022fc68e09eb03c894a44835b99cf3afab9ed132e7fdf", "");
  source = replace(source,
    "    CheckedBoundReference, CheckedFreshDescriptor, ConstructionError, StructuralObservation,\n    ValueOp, ValueTarget,",
    "    CheckedBoundReference, ConstructionError, StructuralObservation, ValueOp, ValueTarget,");
  return replace(source,
    "    new_boundvar_par, new_gbool_par, new_gint_par, new_gstring_par, new_new_par, new_wildcard_par,",
    "    new_boundvar_par, new_gbool_par, new_gint_par, new_gstring_par, new_wildcard_par,");
}
function beforeFreshConstruction(source) {
  source = pinned(source, "/// Projection of an already-opened binder roster.",
    "/// Structural information used by construction,",
    "393ba8226519ac7811af07ed572ec97c581d9c954a9ca2e4abe70508811d747e", "");
  source = replace(source, "    InvalidBinderLayout,\n    ArityOverflow,\n", "");
  return replace(source, "\n#[cfg(test)]\n#[path = \"construction_tests.rs\"]\nmod tests;\n", "");
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  assert.equal(beforeFreshSource(read(driver)), old(driver));
  assert.equal(beforeFreshTarget(read(target)), old(target));
  assert.equal(beforeFreshConstruction(read(construction)), old(construction));
  for (const path of ["rholang-runtime/src/rholang_ast/graph.rs", "rholang-frontend/src/arena.rs"])
    assert.equal(read(path), old(path), "no unfinished Fresh graph operation introduced");
  for (const [path, check, from, to] of [
    [driver, beforeFreshSource, "binder_count: binders.len()", "binder_count: 0"],
    [driver, beforeFreshSource, "Target::fresh(*descriptor, body, Vec::new())", "Target::fresh(*descriptor, Par::default(), Vec::new())"],
    [target, beforeFreshTarget, "descriptor.validate_injection_count(injections.len())?;", ""],
    [construction, beforeFreshConstruction, "pair[0] < pair[1]", "pair[0] <= pair[1]"],
    [construction, beforeFreshConstruction, ".checked_add(1)", ".wrapping_add(1)"],
  ]) {
    const source = read(path);
    assert(source.includes(from), "mutation source exists");
    assert.throws(() => assert.equal(check(source.replace(from, to)), old(path)));
  }
  console.log("Fresh descriptor boundary passed: exact source/target extension, unchanged graph domain and URI/metadata helpers, five rejected mutations. Behavioral evidence remains separate.");
}
