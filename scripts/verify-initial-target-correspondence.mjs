import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { fileURLToPath, pathToFileURL } from "node:url";

// Exact source-boundary evidence, not a Rust equivalence prover. Each entry
// records one reviewed delegation to the direct target. Reconstructing the
// previous file must recover ALL other production code byte for byte.
const replacements = [
  ["mod recursive_oracle;\n", "mod recursive_oracle;\n\nmod target;\nuse target::DirectNodeTarget as Target;\n"],
  ["let par = parts\n                    .into_iter()\n                    .fold(Par::default(), |acc, part| acc.append(part));",
    "let par = parts.into_iter().fold(Target::empty(), Target::append);"],
  ["self.stacks.value(left.append(right));", "self.stacks.value(Target::append(left, right));"],
  ["let op = match is_single_gstring_value(&lhs) && is_single_gstring_value(&rhs) {",
    "let op = match Target::observation(&lhs).single_string\n                    && Target::observation(&rhs).single_string\n                {"],
  ["fn lower_arm_p_zero() -> Result<Par, RholangAstLowerError> {\n    Ok(Par::default())",
    "fn lower_arm_p_zero() -> Result<Par, RholangAstLowerError> {\n    Ok(Target::empty())"],
  ["Bool::BoolLit(literal) => Ok(new_gbool_par(*literal, Vec::new(), false)),",
    "Bool::BoolLit(literal) => Ok(Target::boolean(*literal)),"],
  ["Str::StringLit(literal) => Ok(new_gstring_par(literal.clone(), Vec::new(), false)),",
    "Str::StringLit(literal) => Ok(Target::text(literal.clone())),"],
  ["let mut par = new_gint_par(*literal, Vec::new(), false);",
    "let mut par = Target::integer(*literal);"],
];

export function beforeInitialTarget(source) {
  for (const [before, after] of replacements) {
    assert.equal(source.split(after).length - 1, 1, `one exact target delegation: ${after}`);
    source = source.replace(after, before);
  }
  return source;
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const root = fileURLToPath(new URL("../", import.meta.url));
  const baseline = "61089adf1dda2901421c14e19f1f8f0b30059008";
  const path = "rholang-runtime/src/rholang_ast.rs";
  const before = execFileSync("git", ["-c", "core.fsmonitor=false", "show", `${baseline}:${path}`],
    { cwd: root, encoding: "utf8", maxBuffer: 8 * 1024 * 1024 });
  const current = readFileSync(`${root}${path}`, "utf8");
  assert.equal(beforeInitialTarget(current), before, "all other lowerer code remains unchanged");
  assert.throws(() => beforeInitialTarget(current.replace(
    "Target::append(left, right)", "Target::append(right, left)")), "operand reversal rejected");
  assert.throws(() => assert.equal(beforeInitialTarget(current.replace(
    "fn enter_proc(", "fn corrupted_enter_proc(")), before), "producer mutation rejected");
  console.log(`Initial target delegation correspondence passed against ${baseline}; both mutations rejected.`);
}
