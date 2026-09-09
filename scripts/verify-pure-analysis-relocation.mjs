import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

// A source-correspondence check for this relocation, not a Rust semantics proof.
// Run in a git checkout containing the pinned pre-extraction commit. Only the
// explicit module-path changes below and rustfmt normalization are permitted.
const root = fileURLToPath(new URL("../", import.meta.url));
const baseline = "f2d554cd711a0300cddebab5acd2cb08669c2f57";
const read = (path) => readFileSync(new URL(path, new URL("../", import.meta.url)), "utf8");
const old = (path) => execFileSync("git", ["-c", "core.fsmonitor=false", "show", `${baseline}:${path}`], {
  cwd: root, encoding: "utf8", maxBuffer: 8 * 1024 * 1024,
});
function section(source, start, end) {
  const first = source.indexOf(start);
  assert(first >= 0 && source.indexOf(start, first + 1) < 0, `unique start: ${start}`);
  const last = source.indexOf(end, first + start.length);
  assert(last >= 0, `end: ${end}`);
  return source.slice(first, last).trim();
}
function format(source) {
  return execFileSync("rustfmt", ["--edition", "2021", "--config", "skip_children=true", "--emit", "stdout"], {
    cwd: root, input: source, encoding: "utf8", maxBuffer: 2 * 1024 * 1024,
  });
}
function check(label, expected, actual) {
  assert.equal(format(actual), format(expected), `${label}: exact formatted source`);
  const hash = createHash("sha256").update(format(actual)).digest("hex");
  console.log(`${label}: PASS sha256=${hash}`);
}

const guardBefore = old("rholang-codegen/src/backend.rs");
const guardAfter = read("ast/src/analysis/guard_obligations.rs");
const guardTypes = "/// Class of predicated-type / guard obligation";
const guardStart = "fn pred_has_structural_component(";
check("guard types and constructor",
  section(guardBefore, guardTypes, "/// Disposition kind for a guard"),
  section(guardAfter, guardTypes, guardStart));
check("complete guard-analysis implementation",
  section(guardBefore, guardStart, "/// The fail-closed guard-quality blockers")
    .replace("../tests/support/backend_recursive_oracle.rs", "../../tests/support/guard_obligations_recursive_oracle.rs"),
  section(guardAfter, guardStart, "#[cfg(test)]\nmod tests"));

const floatBefore = old("rholang-codegen/src/rho_net_lower.rs");
const floatAfter = read("ast/src/analysis/binder_float.rs");
const floatStart = "/// A-S5.4b: whether `def`'s declared equational theory";
check("complete binder-float-analysis implementation",
  section(floatBefore, floatStart, "/// One DEPTH-2 nested structural-AC-rewrite")
    .replaceAll("crate::backend::", "super::guard_obligations::")
    .replace("../tests/support/rho_net_metadata_recursive_oracle.rs", "../../tests/support/binder_float_recursive_oracle.rs"),
  section(floatAfter, floatStart, "#[cfg(test)]\nmod tests"));

for (const [before, after] of [
  ["backend_recursive_oracle.rs", "guard_obligations_recursive_oracle.rs"],
  ["rho_net_metadata_recursive_oracle.rs", "binder_float_recursive_oracle.rs"],
]) {
  check(`retained private oracle ${after}`,
    old(`rholang-codegen/tests/support/${before}`), read(`ast/tests/support/${after}`));
}

const backend = read("rholang-codegen/src/backend.rs");
const lower = read("rholang-codegen/src/rho_net_lower.rs");
assert(!backend.includes(guardStart), "no duplicate guard implementation");
assert(!lower.includes("pub fn float_satellite_table("), "no duplicate float implementation");
assert.match(backend, /pub use mettail_ast::analysis::guard_obligations::\{/);
assert.match(lower, /pub use mettail_ast::analysis::binder_float::\{/);
assert.match(floatAfter, /use crate::language::\{Equation, FreshnessCondition, FreshnessTarget, LanguageDef, Premise\};/);
assert.match(guardAfter, /use crate::grammar::\{GrammarRule, TermParam\};/);
assert.match(read("macros/src/gen/runtime/binder_congruence.rs"), /use mettail_ast::analysis::binder_float::float_satellite_table;/);
console.log(`Relocation correspondence passed against ${baseline}; compile/tests validate name resolution separately.`);
