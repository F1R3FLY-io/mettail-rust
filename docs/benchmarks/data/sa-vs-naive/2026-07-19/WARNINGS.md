# WARNINGS — sa-vs-naive full run 2026-07-19

- 2026-07-18T21:5x (protocol setup, before any measurement): the branch HEAD
  moved under the executor from the task-pinned `e56bb208` ("feat(bench):
  workload (vii) multi_rule_shared …") to `b87a9779` ("docs(rho-native): Track
  C Phase 0 — citation substrate, vendored KT paper, validator guards, H1
  normalization") — another agent is committing Track C work on
  `feature/rho-native-set-automata` concurrently. The commit is DOCS-ONLY: all
  24 changed files live under `docs/` (rho-native-integration docs +
  `docs/papers/knotted-topoi.{tex,pdf}`), and
  `git diff --name-only e56bb208..b87a9779 -- rholang-runtime/ docs/benchmarks/data/sa-vs-naive/`
  is EMPTY. The harness source compiled into the measurement binaries is
  therefore byte-identical between the two SHAs; measurement validity is
  unaffected.
- Provenance consequence: the driver embeds `git_sha` at RUNTIME per
  invocation (`git -C <manifest-dir> rev-parse HEAD` at cell start), so
  per-cell jsonl run headers record whatever HEAD is current when that cell
  starts (`b87a9779` or later if further Track C commits land mid-run). The
  stable provenance anchor for the measured code is `driver_binary_sha256` in
  `header.json` (binary built 2026-07-18T21:42-04:00 from the
  harness-identical tree). The criterion phase re-enters cargo (freshness
  check): the executor re-verifies at criterion launch that
  `rholang-runtime/` is still identical to `e56bb208` and records the result
  here.
- No action taken on the branch (the protocol executor does not manage git
  state); the orchestrator should reconcile SHAs when accepting the run.

- 2026-07-19T00:03:40-04:00 criterion run (encoding=pattern-guard filter='cold/lambda_chain') exited rc=101 — see docs/benchmarks/data/sa-vs-naive/2026-07-19/criterion-run.log
  ROOT CAUSE + RESPONSE (2026-07-19T00:1x): the rc=101 above was cargo
  attempting a REBUILD inside the criterion re-entry — the concurrent Track C
  agent had UNCOMMITTED in-progress edits to shared upstream crates (`macros/`,
  `rholang` lib) that did not compile (E0308 ×7). ZERO measurements were taken
  by the failed invocation (it died in the build, before criterion started);
  the cold/lambda_chain chunk was re-run afterwards. Response: all remaining
  criterion chunks invoke the ALREADY-BUILT bench binary DIRECTLY
  (`SA_VS_NAIVE_BENCH_BIN` mode in full.sh), pinned as a copy with sha256
  `e519ebc257142eeccca04ec050655ff67a2bfbecddc5c7d96d9a7e34ef3db697`
  (byte-identical to `target/release/deps/bench_sa_vs_naive-0f6cebd7be799eab`,
  built 2026-07-18T21:49-04:00, mtime-verified untouched through chunk 1 —
  chunk 1's lone cargo recompile was the EXTERNAL path-dep `rholang-parser`
  and did not relink the bench). Every criterion sample in this run therefore
  comes from that one binary; committed state `e56bb208..5c985622` differs
  only under `docs/`.
