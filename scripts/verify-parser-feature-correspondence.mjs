import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

// Exact source checks complement the generated-output and compiled-package
// tests. They do not establish general Rust semantics or parser completeness.
const root = fileURLToPath(new URL("../", import.meta.url));
const baseline = "ad166157fd475545a9c5ef1597d4024f4e631f7b";
const before = path => execFileSync("git", ["-c", "core.fsmonitor=false", "show", `${baseline}:${path}`],
  { cwd: root, encoding: "utf8", maxBuffer: 8 * 1024 * 1024 });
const after = path => readFileSync(new URL(`../${path}`, import.meta.url), "utf8");
function section(source, start, end) {
  const first = source.indexOf(start);
  assert(first >= 0 && source.indexOf(start, first + 1) < 0, `unique start ${start}`);
  const last = source.indexOf(end, first + start.length);
  assert(last >= 0, `end ${end}`);
  return source.slice(first, last).trim();
}
function unchanged(path, transform = text => text) {
  assert.equal(transform(after(path)), before(path), `source changed: ${path}`);
  console.log(`${path}: exact enabled source retained`);
}
unchanged("macros/src/gen/runtime/dovetail_report.rs", text => text
  .replaceAll('#[cfg(feature = "runtime-codegen")]\n', "")
  .replaceAll('#[cfg(all(test, feature = "runtime-codegen"))]', "#[cfg(test)]"));
for (const path of [
  "macros/src/gen/runtime/rho_invocation.rs",
  "macros/src/gen/runtime/rho_dataflow.rs",
  "macros/src/gen/runtime/dovetail_report/typed_report.rs",
  "macros/src/gen/runtime/dovetail_report/semantic_adapter.rs",
  "macros/src/gen/runtime/dovetail_report/reconstruct.rs",
  "macros/src/gen/term_ops/normalize.rs",
  "macros/src/gen/runtime/metadata.rs",
]) unchanged(path);

unchanged("languages/src/rholang.rs", text => {
  for (const name of ["formula", "guard_substrate", "pathmap", "receive", "runtime", "type_inference", "zipper"]) {
    const declaration = `#[path = "rholang/${name}.rs"]\n`;
    assert.equal(text.split(declaration).length, 2, `one explicit helper path ${name}`);
    text = text.replace(declaration, "");
    unchanged(`languages/src/rholang/${name}.rs`);
  }
  return text;
});

const languagePath = "macros/src/gen/runtime/language.rs";
const original = before(languagePath);
const current = after(languagePath);
assert.equal(
  section(current, "    let rho_scalar_invocation_include", "    quote! {\n        // Gate the generated-source loader"),
  section(original, "    let rho_scalar_invocation_include", "    let numeric_cast_adapter_include"),
  "all enabled backend invocations and arguments retain their original source");
assert.equal(
  section(current, "fn generate_term_wrapper(", '#[cfg(all(test, feature = "runtime-codegen"))]'),
  section(original, "fn generate_term_wrapper(", "#[cfg(test)]\nmod backend_include_tests"),
  "shared language implementation source remains exact");
console.log(`Enabled invocation bodies, shared implementations, grammar, and helpers correspond to ${baseline}.`);
