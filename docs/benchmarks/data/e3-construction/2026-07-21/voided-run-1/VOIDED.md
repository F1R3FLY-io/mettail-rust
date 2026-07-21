# VOIDED run 1 — fragmented measurement window (kept for provenance, NOT for verdicts)

This directory preserves the FIRST 2026-07-21 E-3 measurement attempt (binary
`b1c143c13398e099…`, git `5382bd7a`), ruled **VOID** by the session coordinator because the
window died mid-cells and therefore was not one clean exclusive window:

* Segment 1 (`04:03:40Z – ~04:5xZ`): governor verified, 300 s settle, the H3v2 equivalence
  gate (16/16 PASS across r ∈ {100, 250, 500, 1000} — preserved in `e3_wb_gate_r*.jsonl`),
  then the W-B cells through `e3_wb_r500_full`. The session runner was externally killed
  (harness background-task cleanup) DURING the `e3_wb_r1000_incremental` cell.
* Segment 2 (`05:09Z – 06:29:51Z`): a detached (`setsid`) resume re-ran the interrupted
  r = 1000 W-B cells and completed the W-B spans + the full H1 grid, ending with
  `window end` (see `session.log`).

Every file here is internally complete (each cell ran once to completion within its
segment), but the WINDOW as a unit was fragmented by an uncontrolled interruption and an
inter-segment gap, so per the pre-registered run-once/exclusive-window discipline the whole
run is voided and the clean run in the parent directory supersedes it. Nothing was
overwritten: these are the original bytes plus the tee'd session log.
