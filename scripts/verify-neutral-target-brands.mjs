import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdirSync } from "node:fs";
import { fileURLToPath } from "node:url";

// Compile the actual dependency-free library, then a working client and eight
// ill-typed clients. A failure from an unresolved import is NOT brand evidence.
const root = fileURLToPath(new URL("../", import.meta.url));
const output = `${root}target/verification/neutral-brands`;
mkdirSync(output, { recursive: true });
function rustc(args) {
  const result = spawnSync("rustc", ["--edition=2021", ...args], {
    cwd: root, encoding: "utf8", maxBuffer: 4 * 1024 * 1024,
  });
  if (result.error) throw result.error;
  process.stdout.write(result.stdout);
  process.stdout.write(result.stderr);
  return result;
}
const library = `${output}/libmettail_rholang_frontend.rlib`;
assert.equal(rustc(["--crate-name", "mettail_rholang_frontend", "--crate-type=rlib",
  "rholang-frontend/src/lib.rs", "-o", library]).status, 0, "real library compiles");
for (const fixture of ["positive", "reference_escape", "target_escape", "outer_to_inner",
  "inner_to_outer", "outer_option", "closure_escape", "future_escape", "any_escape"]) {
  const result = rustc([`rholang-frontend/tests/ui/${fixture}.rs`,
    "--extern", `mettail_rholang_frontend=${library}`, "--error-format=json",
    ...(fixture === "positive" ? [] : ["--emit=metadata"]), "--out-dir", output]);
  if (fixture === "positive") {
    assert.equal(result.status, 0, "working nested-session client compiles");
    const run = spawnSync(`${output}/positive`, [], { encoding: "utf8" });
    if (run.error) throw run.error;
    assert.equal(run.status, 0, run.stderr);
  } else {
    assert.equal(result.status, 1, `${fixture} must be rejected by rustc`);
    const errors = result.stderr.split("\n").filter(Boolean).map(line => JSON.parse(line))
      .filter(diagnostic => diagnostic.level === "error" &&
        !diagnostic.message.startsWith("aborting due to"));
    assert(errors.length > 0, `${fixture} has a substantive compiler error`);
    for (const error of errors) assert(
      error.code?.code === "E0521" || error.message === "lifetime may not live long enough",
      `${fixture} failed for an unrelated reason: ${error.message}`);
  }
  console.log(`PASS: ${fixture}`);
}
console.log("Session brands: positive runtime control and eight compiler rejection checks passed.");
