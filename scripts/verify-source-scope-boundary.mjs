import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { fileURLToPath, pathToFileURL } from "node:url";

// Exact edit-boundary evidence, NOT a Rust equivalence proof. The new sections
// are pinned to the reviewed source; model checks and executable tests assess
// their behavior separately. Everything outside them must recover the previous
// implementation byte for byte. Later edits require renewed evidence/pins.
const root = fileURLToPath(new URL("../", import.meta.url));
const baseline = "8208a95a99c12c1c882f6456fcf1e1bc479b84de";
const driver = "rholang-runtime/src/rholang_ast.rs";
const oracle = "rholang-runtime/tests/support/rholang_ast_recursive_oracle.rs";
const read = path => readFileSync(`${root}${path}`, "utf8");
const old = path => execFileSync("git",
  ["-c", "core.fsmonitor=false", "show", `${baseline}:${path}`],
  { cwd: root, encoding: "utf8", maxBuffer: 8 * 1024 * 1024 });
const digest = source => createHash("sha256").update(source).digest("hex");
function section(source, start, end) {
  const i = source.indexOf(start);
  const j = source.indexOf(end, i + start.length);
  assert(i >= 0 && j > i, `source boundary exists: ${start}`);
  assert.equal(source.indexOf(start, i + 1), -1, `unique source boundary: ${start}`);
  return source.slice(i, j);
}
function replace(source, before, after, count = 1) {
  assert.equal(source.split(after).length - 1, count, `exact edit count: ${after}`);
  return source.replaceAll(after, before);
}
export function beforeSourceScope(source) {
  const previous = old(driver);
  for (const [start, priorStart, end, hash] of [
    ["#[derive(Clone)]\npub struct BoundEnv", "#[derive(Clone)]\npub struct BoundEnv",
      "/// #14: one binder slot", "694929b8a2a72959356160292c776681d147aae7bbd7bf47f4b0ec29508debd5"],
    ["/// Fallible rholang-to-Rholang-AST lowering error.", "/// Fallible rholang-to-Rholang-AST lowering error.",
      "/// Rholang language adapter for the AST-first", "cb72242e83e69551d1fe340fa429700d8e23e61120fb9d223d66edf489d7ce4b"],
    ["impl<'a> EnvArena<'a>", "impl<'a> EnvArena<'a>",
      "/// The `ExprInstance` constructors", "0d7feb7a39e7a3e9374d2052d6d374199e02bc6165a534a7cb35623dc4b6419c"],
    ["    /// A fresh lexical environment,", "    /// `BoundEnv::new()`, materialised at most once.",
      "    /// Push `children`", "6e04e9b69528e309882dc68709bfa817256f1af1a87be4ee7172f08201ec2977"],
    ["fn lower_name_var(", "fn lower_name_var(",
      "/// L9-6b: the de-Bruijn level a free", "8aacc4bc4ef3cb0a892f7171059d5177f4eeeab388eb28d3e1e59669f235a49e"],
    ["fn extend_env(", "fn extend_env(", "fn send_par(",
      "bd9dcf42265e49276917313d9f86182662e2359769cc3dc3a6c43c9c3675d924"],
  ]) {
    const current = section(source, start, end);
    assert.equal(digest(current), hash, `reviewed scope section: ${start}`);
    source = source.replace(current, section(previous, priorStart, end));
  }
  source = replace(source, "", "mod scope;\npub use scope::SourceAdmissionMode;\n\n");
  for (const [before, after, count] of [
    ["self.envs.push(extend_env(self.env(env), &binders));",
      "self.envs.push(extend_env(self.env(env), &binders)?)?;", 1],
    ["self.envs.push(extend_env(self.env(env), &ordered_binders));",
      "self\n                    .envs\n                    .push(extend_env(self.env(env), &ordered_binders)?)?;", 1],
    [".push(extend_env(self.env(env), &[Binder(ret_var)]));",
      ".push(extend_env(self.env(env), &[Binder(ret_var)])?)?;", 3],
    [".push(extend_env(self.env(env_new), &[Binder(result_var)]));",
      ".push(extend_env(self.env(env_new), &[Binder(result_var)])?)?;", 1],
    [".push(extend_env(self.env(env_new), &[Binder(r_var)]));",
      ".push(extend_env(self.env(env_new), &[Binder(r_var)])?)?;", 1],
    [".push(extend_env(self.env(env_new), &[Binder(token_var.clone())]));",
      ".push(extend_env(self.env(env_new), &[Binder(token_var.clone())])?)?;", 1],
    ["let empty = self.empty_env();", "let empty = self.empty_env()?;", 1],
    ["self.envs.push(self.env(env).in_pattern_position());",
      "self.envs.push(self.env(env).in_pattern_position())?;", 1],
    [".push(self.env(state.env).extend_slots(&state.slots));",
      ".push(self.env(state.env).extend_slots(&state.slots)?)?;", 1],
  ]) source = replace(source, before, after, count);
  for (const [spaces, current] of [
    [16, "fills.insert(\n                    hole.name.clone(),\n                    scope::lower_bound_index(self.env(env_new).scope_width, level)?,\n                );"],
    [8, "fills.insert(hole.name.clone(), scope::lower_bound_index(env.scope_width, level)?);"],
  ]) {
    const indent = " ".repeat(spaces);
    source = replace(source,
      `${indent}fills.insert(\n${indent}    hole.name.clone(),\n${indent}    new_boundvar_par(level as i32, create_bit_vector(&[level]), false),\n${indent});`,
      `${indent}${current}`);
  }
  return source;
}

// Seven signature-only adjustments to the test oracle. Its recursive traversal
// and all other source remain pinned, rather than rewriting its expected values.
export function beforeScopeOracle(source) {
  for (const [before, count] of [
    ["let extended_env = extend_env(env, &binders)", 2],
    ["let env_new = extend_env(env, &[Binder(ret_var)])", 2],
    ["let env_for = extend_env(&env_new, &[Binder(result_var)])", 1],
    ["let env_for = extend_env(&env_new, &[Binder(r_var)])", 1],
    ["let extended_env = env.extend_slots(&slots)", 1],
  ]) source = replace(source, `${before};`, `${before}?;`, count);
  return source;
}

function checkResolver(source) {
  assert.equal(digest(source), "5fc3d84797f42aaa065c4656a88bd674102a3d4382847223383b840555788ba6",
    "exact reviewed lexical resolver; behavioral evidence is checked separately");
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const current = read(driver);
  assert.equal(beforeSourceScope(current), old(driver), "all other production code unchanged");
  assert.equal(beforeScopeOracle(read(oracle)), old(oracle), "only seven oracle signature changes");
  const resolver = read("rholang-runtime/src/rholang_ast/scope.rs");
  checkResolver(resolver);
  for (const [from, to] of [
    [".or_else(|| flt_hole_bound_level(free_var, env))", ".or(Some(0))"],
    ["CheckedBoundReference::new(scope, index)", "CheckedBoundReference::new(index, scope)"],
    [".checked_add(width)", ".wrapping_add(width)"],
    ["SourceAdmissionMode::Public => Err", "SourceAdmissionMode::Harness => Err"],
  ]) {
    assert(resolver.includes(from));
    assert.throws(() => checkResolver(resolver.replace(from, to)));
  }
  assert.throws(() => beforeSourceScope(current.replace("admission: self.admission", "admission: SourceAdmissionMode::Harness")));
  assert.throws(() => assert.equal(beforeSourceScope(current.replace("fn enter_proc(", "fn changed_enter_proc(")), old(driver)));
  console.log("Source-scope edit boundary passed; seven oracle signature changes; six rejected mutations. Behavioral correctness requires separate proofs/tests.");
}
