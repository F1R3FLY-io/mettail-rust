import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { fileURLToPath, pathToFileURL } from "node:url";
import { beforeSourceScope } from "./verify-source-scope-boundary.mjs";
import { beforeFreshTarget } from "./verify-fresh-descriptor-boundary.mjs";

const registration = "\nmod graph;\npub use graph::{interpret_construction_graph, GraphInterpretationError};\n";
export function beforeInitialGraph(source) {
  source = beforeSourceScope(source);
  assert.equal(source.split(registration).length - 1, 1, "one graph interpreter registration");
  return source.replace(registration, "");
}

// Exact source witnesses complement, not replace, Rocq/model and Rust tests.
// A change to any witness needs renewed review of the corresponding law.
function checkInterpreter(source) {
  for (const witness of [
    "Self::Visit(_) => None,\n            Self::Append(_) => Some(2)",
    "let jobs = depth\n        .checked_mul(2)\n        .and_then(|slots| slots.checked_add(1))",
    "let values = depth\n        .checked_add(1)",
    "Footprint { entries: slots, text_bytes: 0 }.charge(budget)?;\n    let mut work: Worklist<Job, Materialized> = Worklist::with_capacity(jobs, values);",
    "while let Some(job) = work.pop(Job::arity)? {\n        budget.charge(1, 0)?;",
    "if current.children.len() != current.operation.arity()",
    "for &child in [left, right] {\n                            if child >= index",
    "work.push(Job::Append(index), Job::arity)?;\n                        work.push(Job::Visit(*right), Job::arity)?;\n                        work.push(Job::Visit(*left), Job::arity)?;",
    "footprint.charge_with_metadata(budget, metadata)?;\n    build()",
    "let value = precharged(budget, footprint, metadata, || {\n                            // In particular the text clone is AFTER reservation.",
    "ValueOp::Text(value) => DirectNodeTarget::text(value.clone())",
    "work.reduce_pair(|left, right| {\n                    let footprint = left.footprint.plus(right.footprint)?;",
    "let copies = left.footprint.plus(footprint)?;\n                    let metadata = MetadataCharge::append(\n                        left.value.locally_free.len(),\n                        right.value.locally_free.len(),\n                    )?;\n                    precharged(budget, copies, metadata, || {",
    "ValueTarget::append(&mut DirectNodeTarget, left.value, right.value)?;",
    "if DirectNodeTarget::observation(&value) != node(graph, index)?.observation",
    "        work.check()?;\n    }\n    Ok(work.finish()?.value)",
    ".checked_mul(4)\n            .and_then(|units| units.checked_add(self.text_bytes))",
    "self.charge_with_metadata(budget, MetadataCharge::default())",
    "work: bytes\n                .checked_mul(3)",
    "units: bytes\n                .checked_mul(2)",
    "let result = left.max(right);",
    "work: result\n                .checked_mul(3)\n                .and_then(|passes| left.checked_add(passes))",
    "units: left\n                .checked_add(result)",
    ".and_then(|work| work.checked_add(metadata.work))",
    ".and_then(|units| units.checked_add(metadata.units))",
    "budget.charge(work, units)?;",
    "Some(CheckedBoundReference::new(*scope, *index)?)",
    "Some(reference) => MetadataCharge::bound(reference.metadata_bytes())?",
    "ValueOp::Bound { .. } => DirectNodeTarget::bound(\n                                    reference.expect(\"validated bound descriptor\"),",
    "DirectNodeTarget::wildcard(*connective)",
  ]) assert(source.includes(witness), `reviewed machine/resource witness missing: ${witness}`);
  assert(!/size_of|HashMap|BTreeMap|\.parse\(|Proc::/.test(source),
    "no native-layout debit, subtree memoization, or second source traversal");
}

// Remove only the checked bound/wildcard extension. Exact reconstruction below
// retains every pre-existing target operation; this is an edit-boundary check,
// not a replacement for constructor tests or the construction-protocol proof.
function beforeBoundTarget(source) {
  for (const [before, after] of [
    ["    ConstructionError, StructuralObservation, ValueOp, ValueTarget,",
      "    CheckedBoundReference, ConstructionError, StructuralObservation, ValueOp, ValueTarget,"],
    ["use models::rust::utils::{new_gbool_par, new_gint_par, new_gstring_par};",
      "use models::rust::utils::{\n    new_boundvar_par, new_gbool_par, new_gint_par, new_gstring_par, new_wildcard_par,\n};"],
    ["", "    /// Integer/scope validation is carried by the descriptor. Resource\n    /// reservation is the caller's separate obligation before invoking this.\n    pub(super) fn bound(reference: CheckedBoundReference) -> Par {\n        new_boundvar_par(reference.emitted_index(), Vec::new(), false)\n    }\n\n    pub(super) fn wildcard(connective: bool) -> Par {\n        new_wildcard_par(Vec::new(), connective)\n    }\n\n"],
    ["", "            ValueOp::Bound { scope, index } => {\n                Self::bound(CheckedBoundReference::new(scope, index)?)\n            },\n            ValueOp::Wildcard { connective } => Self::wildcard(connective),\n"],
  ]) {
    assert.equal(source.split(after).length - 1, 1, `one exact bound target extension: ${after}`);
    source = source.replace(after, before);
  }
  return source;
}

function between(source, start, end) {
  const first = source.indexOf(start);
  const last = source.indexOf(end, first + start.length);
  assert(first >= 0 && last > first, `unique source boundary ${start}`);
  assert.equal(source.indexOf(start, first + 1), -1);
  return source.slice(first, last);
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const root = fileURLToPath(new URL("../", import.meta.url));
  const read = path => readFileSync(`${root}${path}`, "utf8");
  const git = (cwd, revision, path) => execFileSync("git",
    ["-c", "core.fsmonitor=false", "show", `${revision}:${path}`],
    { cwd, encoding: "utf8", maxBuffer: 8 * 1024 * 1024 });
  const driver = "rholang-runtime/src/rholang_ast.rs";
  const baseline = "82e5b777d407edec3c8df3e48a3024ba6eed6b35";
  assert.equal(beforeInitialGraph(read(driver)), git(root, baseline, driver),
    "all pre-existing source lowering remains byte-identical");
  const target = "rholang-runtime/src/rholang_ast/target.rs";
  const boundTarget = beforeFreshTarget(read(target));
  assert.equal(beforeBoundTarget(boundTarget), git(root, baseline, target),
    "existing node target unchanged outside checked bound/wildcard extension");
  assert.throws(() => beforeBoundTarget(boundTarget.replace(
    "CheckedBoundReference::new(scope, index)", "CheckedBoundReference::new(index, scope)")));
  assert.throws(() => beforeBoundTarget(boundTarget.replace(
    "new_wildcard_par(Vec::new(), connective)", "new_wildcard_par(Vec::new(), false)")));
  const source = read("rholang-runtime/src/rholang_ast/graph.rs");
  checkInterpreter(source);
  for (const [from, to] of [
    ["work.push(Job::Visit(*right), Job::arity)?;", "work.push(Job::Visit(*left), Job::arity)?;"],
    ["work.push(Job::Visit(*left), Job::arity)?;", ""],
    ["let copies = left.footprint.plus(footprint)?;", "let copies = footprint;"],
    ["footprint.charge_with_metadata(budget, metadata)?;\n    build()", "let result = build();\n    footprint.charge_with_metadata(budget, metadata)?;\n    result"],
    [".checked_mul(4)", ".checked_mul(8)"],
    ["work: bytes\n                .checked_mul(3)", "work: bytes\n                .checked_mul(2)"],
    ["units: bytes\n                .checked_mul(2)", "units: bytes\n                .checked_mul(1)"],
    ["let result = left.max(right);", "let result = left + right;"],
    [".and_then(|work| work.checked_add(metadata.work))", ""],
    [".and_then(|units| units.checked_add(metadata.units))", ""],
    ["Some(CheckedBoundReference::new(*scope, *index)?)", "Some(CheckedBoundReference::new(*index, *scope)?)"],
  ]) {
    assert(source.includes(from), "mutation source exists");
    assert.throws(() => checkInterpreter(source.replace(from, to)));
  }

  const nodeRoot = fileURLToPath(new URL("../../../f1r3node-rust-f1r3lang/", import.meta.url));
  const nodeBaseline = "6781d1d671cc0b98b9de946b3871bdbb8e7f1280";
  for (const [path, start, end] of [
    ["models/src/rust/utils.rs", "    pub fn append(&self, mut other: Par)", "\n}\n"],
    ["models/src/rust/utils.rs", "pub fn new_gint_par(", "pub fn new_guri_par("],
    ["models/src/rust/utils.rs", "    pub fn with_exprs(", "    pub fn with_"],
    ["models/src/rust/rholang/implicits.rs", "pub fn vector_par(", "\npub fn "],
    ["models/src/lib.rs", "pub fn create_bit_vector(", "\n}\n"],
    ["models/src/lib.rs", "pub fn canonical_bit_vector(", "\n}\n"],
    ["models/src/rust/utils.rs", "pub fn new_boundvar_par(", "pub fn new_boundvar_expr("],
    ["models/src/rust/utils.rs", "pub fn new_boundvar_expr(", "pub fn new_freevar_par("],
    ["models/src/rust/utils.rs", "pub fn new_wildcard_par(", "pub fn new_wildcard_expr("],
    ["models/src/rust/utils.rs", "pub fn union(", "\n}\n"],
    ["models/src/rust/utils.rs", "pub fn new_new_par(", "pub fn new_eset_par("],
    ["models/src/rust/utils.rs", "    pub fn with_news(", "    pub fn with_exprs("],
  ]) {
    const current = readFileSync(`${nodeRoot}${path}`, "utf8");
    assert.equal(between(current, start, end), between(git(nodeRoot, nodeBaseline, path), start, end),
      `the exact constructor/copy policy remains pinned: ${start}`);
  }
  console.log("Graph correspondence passed: unchanged lowering outside declared scope edits, exact bound/wildcard target extension, pinned node helpers, thirteen rejected target/scheduling/charging mutations. Behavioral correctness requires separate proofs/tests.");
}
