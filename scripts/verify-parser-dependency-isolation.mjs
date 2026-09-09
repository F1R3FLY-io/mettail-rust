import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { realpathSync } from "node:fs";
import { fileURLToPath } from "node:url";

// Cargo metadata unifies the selected workspace's features. Inspect normal AND
// build/proc-macro edges, not merely target dependencies. This is conservative:
// an extra host/target-unified edge may reject a safe graph, never hide a leak.
const root = fileURLToPath(new URL("../", import.meta.url));
const metadata = JSON.parse(execFileSync("cargo", [
  "metadata", "--format-version", "1", "--locked", "--offline", "--all-features",
], { cwd: root, encoding: "utf8", maxBuffer: 64 * 1024 * 1024,
  stdio: ["ignore", "pipe", "inherit"] }));
const packages = new Map(metadata.packages.map(pkg => [pkg.id, pkg]));
const nodes = new Map(metadata.resolve.nodes.map(node => [node.id, node]));
const named = name => {
  const matches = metadata.packages.filter(pkg => pkg.name === name);
  assert.equal(matches.length, 1, `unique package ${name}`);
  return matches[0];
};
const normalBuildDeps = id => nodes.get(id).deps.filter(dep =>
  dep.dep_kinds.some(kind => kind.kind === null || kind.kind === "build")
).map(dep => dep.pkg);

function closureAndAcyclic(start, edges) {
  const seen = new Set();
  const active = new Set();
  const work = [[start, false]];
  while (work.length) {
    const [id, leaving] = work.pop();
    if (leaving) { active.delete(id); seen.add(id); continue; }
    assert(!active.has(id), `dependency cycle at ${id}`);
    if (seen.has(id)) continue;
    active.add(id);
    work.push([id, true]);
    for (const next of edges(id)) work.push([next, false]);
  }
  return seen;
}

// Negative control: a reachability check that ignores back-edges cannot prove
// the package boundary required by ParserBackendSelection.v.
assert.throws(() => closureAndAcyclic("a", id => id === "a" ? ["b"] : ["a"]),
  /dependency cycle/);

const parserMacro = named("parser-macros");
const backendMacro = named("macros");
const syntax = named("mettail-rholang-syntax");
assert(!Object.hasOwn(parserMacro.features, "runtime-codegen"));
assert(nodes.get(backendMacro.id).features.includes("runtime-codegen"),
  "the union test must enable the original backend macro");
assert(!nodes.get(parserMacro.id).features.includes("runtime-codegen"));
assert.equal(realpathSync(parserMacro.targets.find(t => t.kind.includes("proc-macro")).src_path),
  realpathSync(backendMacro.targets.find(t => t.kind.includes("proc-macro")).src_path),
  "both packages must compile the same macro source");

const forbidden = new Set([
  "macros", "languages", "rholang-codegen", "rholang-runtime", "rholang-adapter",
  "models", "rholang", "rho-pure-eval", "rspace_plus_plus",
  "rholang-parser", "rholang-tree-sitter", "tree-sitter-rholang", "tree-sitter",
]);
for (const start of [parserMacro, syntax]) {
  const reachable = closureAndAcyclic(start.id, normalBuildDeps);
  for (const id of reachable) {
    const pkg = packages.get(id);
    assert(!forbidden.has(pkg.name), `${start.name} reaches forbidden ${pkg.name}`);
    assert(!/\/f1r3node[^/]*\//.test(pkg.manifest_path),
      `${start.name} reaches node path ${pkg.manifest_path}`);
  }
  console.log(`${start.name}: ${reachable.size} normal/build packages, acyclic and node-independent under all-feature workspace unification`);
}
console.log("Shared macro source and absent backend feature verified; this is dependency evidence, not parser/semantic equivalence.");
