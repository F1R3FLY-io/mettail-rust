#!/usr/bin/env bash
# Track B — the FULL pre-registered measurement protocol runner for the
# sa-vs-naive head-to-head (README.md §2–§7 in this directory, executed
# verbatim; smoke.sh is the plumbing/signal validation, THIS script is the
# measurement).
#
# ── What one execution produces ─────────────────────────────────────────────
#   docs/benchmarks/data/sa-vs-naive/<DATE>/
#   ├── header.json                 # machine-readable run header (env + protocol pins)
#   ├── env.txt                     # README §2 records (SHA, hostname, governor, affinity)
#   ├── WARNINGS.md                 # ONLY if warnings (non-performance governor,
#   │                               #   invocation failures) — absent on a clean run
#   ├── driver/<cell>.jsonl         # §5 counter driver: 1 header + TOTAL_REPS lines/cell
#   ├── driver-run.log              # per-cell progress (start/done/elapsed/dnf/rc)
#   ├── criterion/                  # §6 wall clock: copy of target/criterion (pattern-guard)
#   ├── criterion-run.log
#   ├── criterion-consume-test/     # §6 optional consume-test pass (phase criterion-ct)
#   ├── criterion-consume-test-run.log
#   ├── csv/driver_cells.csv        # §7 per-rep long table   (measured reps only)
#   ├── csv/driver_summary.csv      # §7 per-cell medians     (measured reps only)
#   ├── csv/dnf_audit.csv           # §7 DNF audit (dnf lines are DATA, incl. 60 s guard)
#   ├── csv/cell_accounting.csv     # per-cell line accounting (warmup/measured × ok/dnf)
#   ├── summary.csv                 # one row per rep line, ALL reps, warmup+dnf flags
#   ├── summary_medians.csv         # per-cell medians over the 30 MEASURED reps
#   └── sanity.txt                  # §sanity results (parse / ground-truth / determinism)
#
# ── Replicate discipline (pgmcp experiment 144) ─────────────────────────────
# ≥ 30 measured replicates after 3 warm-up replicates. Implementation: ONE
# driver invocation per cell at --reps 33 (reps are 0-based inside the driver;
# each rep gets a FRESH counting runtime), then the first WARMUP_REPS=3 rep
# lines (workload.rep < 3, dnf lines included) are marked with a POST-HOC
# wrapper field `"warmup":true` via jq — chosen over a separate warmup file so
# every cell stays ONE self-contained jsonl whose header `reps` field equals
# the total emitted rep count (33). Measured reps are workload.rep ∈ [3, 32]:
# exactly 30. All aggregate tables select `.warmup != true`; summary.csv keeps
# every rep with an explicit warmup flag.
#
# ── Cell matrix (README §5 + the executor-task lambda_chain n=2 extension) ──
# pattern-guard:  lambda_chain {2,4,8,16,32,64} × {sa,naive}          = 12
#                 swap_comb    {1,2,4,8,16,32,64} × {sa,naive}        = 14
#                 swap_small   {1..8} × {sa,naive}                    = 16
#                 wrap_swap_ctx {1} × {sa,naive}                      =  2
#                 nested_spine {2,4,8,16} × {naive,replay}            =  8
#                 multi_rule_shared {201,202,203,401,402,403,
#                                    801,802,803} × {sa,naive}        = 18
# consume-test (naive-only, single-candidate admitted cells — the r=1/m=1
# discipline):    lambda_chain {2,4,8,16,32,64} + swap_small {1..8}
#                 + wrap_swap_ctx {1} + swap_comb {1}                 = 16
# TOTAL: 86 invocations = the README-§5 accounting (83) + the 3 lambda_chain
# n=2 cells (sa, naive/pattern-guard, naive/consume-test) that the protocol
# executor's ladder adds (n=2 is registry-admitted; it is the smoke size).
#
# ── Environment discipline (README §2 — RECORD, never change) ───────────────
# Every measured invocation runs under
#   systemd-run --user --scope -q -p MemoryMax=28G   (never TasksMax)
#   env RUST_MIN_STACK=8388608                        (off-cargo: [env] does not apply)
#   taskset -c 0-7                                    (8 pinned cores)
# The governor/driver/boost state is RECORDED into header.json + env.txt; if
# any of cpus 0-7 is not `performance`, that is recorded prominently in both
# the header and WARNINGS.md and the run CONTINUES (the orchestrator decides).
#
# ── DNF discipline ──────────────────────────────────────────────────────────
# The driver's own 60 s per-rep timeout and 8 MiB emitted-program guard turn
# non-finishing reps into `"dnf":true` LINES (exit code 1) — DNFs are DATA:
# the runner records them and continues. Exit codes ≥ 2 (usage/compile/IO)
# are invocation FAILURES: recorded in WARNINGS.md, run continues to the next
# cell (the orchestrator triages).
#
# ── Criterion pins (README §6; bench-top default is 10 samples / 3 s) ───────
# The full protocol overrides via the criterion CLI, exactly as the bench-head
# rustdoc documents:  -- --sample-size 30 --warm-up-time 5
# The consume-test wall-clock pass is the separate `criterion-ct` phase (group
# names carry no encoding, so its target/criterion output would OVERWRITE the
# pattern-guard estimates — hence the separate copy dir and run order).
#
# ── Usage ───────────────────────────────────────────────────────────────────
#   full.sh <DATE> [phase] [FILTER]
#     DATE   the dated output directory name (e.g. 2026-07-19)
#     phase  driver | criterion | criterion-ct | criterion-chunk |
#            criterion-ct-chunk | criterion-copy | post | all   (default: all;
#            `all` = driver → criterion → post. criterion-ct is opt-in.)
#     FILTER criterion benchmark-name filter, required by the *-chunk phases
# Driver cells already complete (1 + TOTAL_REPS lines) are SKIPPED, so an
# interrupted driver phase resumes by re-invocation. The *-chunk phases run
# the SAME criterion command restricted by criterion's native FILTER argument
# (no target/criterion set-aside, no copy) — for execution environments that
# kill long-lived tasks; finish with `criterion-copy`. Chunking is
# measurement-identical: criterion groups are measured independently, and the
# chunk boundaries only change process lifetimes, never pinning or flags.

set -uo pipefail   # NOT -e: driver exit 1 (= dnf lines present) is data.

DATE="${1:?usage: full.sh <DATE> [driver|criterion|criterion-ct|post|all]}"
PHASE="${2:-all}"

FEATURES="bench-naive-baseline swap-demo-runtime lambda-demo-runtime ctx-demo-runtime"
TOTAL_REPS=33     # 3 warm-up + 30 measured (pgmcp experiment 144 discipline)
WARMUP_REPS=3
CRITERION_SAMPLE_SIZE=30
CRITERION_WARM_UP_TIME=5

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
cd "$REPO_ROOT"
export RUST_MIN_STACK=8388608

ROOT="docs/benchmarks/data/sa-vs-naive/$DATE"
DRIVER_DIR="$ROOT/driver"
CSV_DIR="$ROOT/csv"
DRIVER_BIN="$REPO_ROOT/target/release/bench_sa_vs_naive_driver"
WRAP=(systemd-run --user --scope -q -p MemoryMax=28G
      env "RUST_MIN_STACK=$RUST_MIN_STACK"
      taskset -c 0-7)

mkdir -p "$DRIVER_DIR" "$CSV_DIR"

log() { echo "[full] $(date -Is) $*" | tee -a "$ROOT/driver-run.log" >&2; }
warn() {  # append to WARNINGS.md (created on first warning only) + the log
    log "WARNING: $*"
    { [ -s "$ROOT/WARNINGS.md" ] || echo "# WARNINGS — sa-vs-naive full run $DATE"; \
      echo; echo "- $(date -Is) $*"; } >> "$ROOT/WARNINGS.md"
}

command -v jq >/dev/null 2>&1 || { echo "[full] FAIL: jq is required" >&2; exit 1; }

# ─────────────────────────────────────────────────────────────────────────────
# Environment record (README §2): env.txt + header.json — READ, never change.
# ─────────────────────────────────────────────────────────────────────────────
record_env() {
    local governor_warn=0 governors=""
    for cpu in 0 1 2 3 4 5 6 7; do
        local g
        g=$(cat "/sys/devices/system/cpu/cpu$cpu/cpufreq/scaling_governor" 2>/dev/null || echo unknown)
        governors+="cpu$cpu=$g "
        [ "$g" = performance ] || governor_warn=1
    done
    local scaling_driver boost pstate
    scaling_driver=$(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_driver 2>/dev/null || echo unknown)
    boost=$(cat /sys/devices/system/cpu/cpufreq/boost 2>/dev/null || echo unknown)
    pstate=$(cat /sys/devices/system/cpu/amd_pstate/status 2>/dev/null || echo n/a)

    {
        echo "git_sha: $(git rev-parse HEAD)"
        echo "git_branch: $(git rev-parse --abbrev-ref HEAD)"
        echo "hostname: $(hostname)"
        echo "uname: $(uname -a)"
        echo "rustc: $(rustc --version)"
        echo "scaling_governors: $governors"
        echo "scaling_driver: $scaling_driver"
        echo "cpufreq_boost: $boost"
        echo "amd_pstate_status: $pstate"
        echo "shell_cpus_allowed_list: $(grep Cpus_allowed_list /proc/self/status | awk '{print $2}')"
        echo "measured_invocation_wrapper: systemd-run --user --scope -q -p MemoryMax=28G env RUST_MIN_STACK=$RUST_MIN_STACK taskset -c 0-7"
        echo "driver_binary: $DRIVER_BIN"
        echo "driver_binary_sha256: $(sha256sum "$DRIVER_BIN" 2>/dev/null | awk '{print $1}')"
        echo "recorded_at: $(date -Is)"
    } > "$ROOT/env.txt"

    jq -n \
        --arg date "$DATE" \
        --arg git_sha "$(git rev-parse HEAD)" \
        --arg git_branch "$(git rev-parse --abbrev-ref HEAD)" \
        --arg hostname "$(hostname)" \
        --arg uname "$(uname -a)" \
        --arg rustc "$(rustc --version)" \
        --arg governors "$governors" \
        --arg scaling_driver "$scaling_driver" \
        --arg boost "$boost" \
        --arg pstate "$pstate" \
        --arg affinity "$(grep Cpus_allowed_list /proc/self/status | awk '{print $2}')" \
        --arg wrapper "systemd-run --user --scope -q -p MemoryMax=28G env RUST_MIN_STACK=$RUST_MIN_STACK taskset -c 0-7" \
        --arg driver_sha256 "$(sha256sum "$DRIVER_BIN" 2>/dev/null | awk '{print $1}')" \
        --argjson governor_warn "$governor_warn" \
        --argjson total_reps "$TOTAL_REPS" \
        --argjson warmup_reps "$WARMUP_REPS" \
        --argjson sample_size "$CRITERION_SAMPLE_SIZE" \
        --argjson warm_up_time "$CRITERION_WARM_UP_TIME" \
        '{date: $date, git_sha: $git_sha, git_branch: $git_branch,
          hostname: $hostname, uname: $uname, rustc: $rustc,
          cpu: {governors_cpu0_7: $governors, scaling_driver: $scaling_driver,
                boost: $boost, amd_pstate_status: $pstate,
                governor_all_performance: ($governor_warn == 0)},
          shell_cpus_allowed_list: $affinity,
          measured_invocation_wrapper: $wrapper,
          driver_binary_sha256: $driver_sha256,
          protocol: {
            total_reps_per_cell: $total_reps,
            warmup_reps: $warmup_reps,
            measured_reps: ($total_reps - $warmup_reps),
            warmup_marking: "post-hoc jq wrapper field \"warmup\":true on lines with workload.rep < 3 (dnf lines included); measured reps are workload.rep in [3,32]",
            rep_timeout_secs: 60,
            emitted_program_guard_bytes: 8388608,
            criterion_override: {sample_size: $sample_size, warm_up_time_secs: $warm_up_time,
                                 mechanism: "criterion CLI per the bench-head rustdoc: -- --sample-size 30 --warm-up-time 5"},
            cells: {pattern_guard: 70, consume_test: 16, total: 86,
                    readme_accounting: 83,
                    extension: "lambda_chain n=2 (sa, naive/pattern-guard, naive/consume-test) per the executor-task ladder; registry-admitted smoke size"}},
          recorded_at: now | todate}' > "$ROOT/header.json"

    if [ "$governor_warn" -ne 0 ]; then
        warn "scaling governor is NOT performance on all of cpus 0-7: $governors (protocol records, never changes — orchestrator decides whether to re-run)"
    fi
    log "environment recorded: $governors driver=$scaling_driver boost=$boost"
}

# ─────────────────────────────────────────────────────────────────────────────
# §5 driver phase
# ─────────────────────────────────────────────────────────────────────────────
run_cell() { # workload matcher n [encoding]
    local w=$1 m=$2 n=$3 enc=${4:-pattern-guard} suffix=""
    [ "$m" = naive ] && [ "$enc" != pattern-guard ] && suffix="_${enc}"
    local out="$DRIVER_DIR/${w}_${m}${suffix}_n${n}.jsonl"
    local raw="${out}.raw"
    local expect_lines=$((TOTAL_REPS + 1))   # 1 run header + TOTAL_REPS rep lines
    if [ -s "$out" ] && [ "$(wc -l < "$out")" -eq "$expect_lines" ]; then
        log "SKIP $w/$m${suffix} n=$n — already complete ($expect_lines lines)"
        return 0
    fi
    log "START $w/$m${suffix} n=$n reps=$TOTAL_REPS"
    local t0 rc=0
    t0=$(date +%s)
    "${WRAP[@]}" "$DRIVER_BIN" \
        --workload "$w" --matcher "$m" --encoding "$enc" \
        --n "$n" --reps "$TOTAL_REPS" --format json-lines --out "$raw" \
        2>>"$ROOT/driver-run.log" || rc=$?
    local elapsed=$(( $(date +%s) - t0 ))
    if [ "$rc" -ge 2 ]; then
        warn "driver invocation FAILED (rc=$rc) for $w/$m${suffix} n=$n after ${elapsed}s — raw output (if any) kept at $raw"
        return 0   # continue with the next cell; the orchestrator triages
    fi
    # rc 0 = clean; rc 1 = dnf lines present (DATA). Mark warm-up reps.
    if ! jq -c --argjson w "$WARMUP_REPS" \
        'if (.workload.rep != null) and (.workload.rep < $w) then . + {"warmup": true} else . end' \
        "$raw" > "$out"; then
        warn "jq warmup-marking FAILED for $w/$m${suffix} n=$n — raw output kept at $raw"
        return 0
    fi
    rm -f "$raw"
    local dnf
    dnf=$(grep -c '"dnf":true' "$out" || true)
    log "DONE  $w/$m${suffix} n=$n rc=$rc elapsed=${elapsed}s dnf=$dnf"
}

driver_phase() {
    [ -x "$DRIVER_BIN" ] || { echo "[full] FAIL: driver binary not found at $DRIVER_BIN — build it per README §3" >&2; exit 1; }
    log "driver phase start (TOTAL_REPS=$TOTAL_REPS = $WARMUP_REPS warmup + $((TOTAL_REPS - WARMUP_REPS)) measured)"

    # The full matrix, pattern-guard (README §5 order; lambda ladder per the
    # executor task includes the n=2 smoke size):
    local n
    for n in 2 4 8 16 32 64;    do run_cell lambda_chain sa "$n"; run_cell lambda_chain naive "$n"; done
    for n in 1 2 4 8 16 32 64;  do run_cell swap_comb    sa "$n"; run_cell swap_comb    naive "$n"; done
    for n in 1 2 3 4 5 6 7 8;   do run_cell swap_small   sa "$n"; run_cell swap_small   naive "$n"; done
    run_cell wrap_swap_ctx sa 1; run_cell wrap_swap_ctx naive 1
    for n in 2 4 8 16;          do run_cell nested_spine naive "$n"; run_cell nested_spine replay "$n"; done
    # multi_rule_shared: n = 100·r + s, r ∈ {2,4,8} × s ∈ {1,2,3} (amended W1).
    for n in 201 202 203 401 402 403 801 802 803; do
        run_cell multi_rule_shared sa "$n"; run_cell multi_rule_shared naive "$n"
    done

    # The consume-test encoding on its admitted single-candidate cells
    # (naive column only; r=1/m=1 discipline):
    for n in 2 4 8 16 32 64;    do run_cell lambda_chain naive "$n" consume-test; done
    for n in 1 2 3 4 5 6 7 8;   do run_cell swap_small   naive "$n" consume-test; done
    run_cell wrap_swap_ctx naive 1 consume-test
    run_cell swap_comb     naive 1 consume-test

    log "driver phase done: $(ls "$DRIVER_DIR"/*.jsonl 2>/dev/null | wc -l) cell files"
}

# ─────────────────────────────────────────────────────────────────────────────
# §6 criterion phase (pattern-guard; the consume-test pass is criterion-ct)
# ─────────────────────────────────────────────────────────────────────────────
set_aside_previous_criterion() {
    if [ -d target/criterion ]; then
        local aside="target/criterion.pre-trackb-$DATE-$(date +%s)"
        log "pre-existing target/criterion set aside (NOT deleted) -> $aside"
        mv target/criterion "$aside"
    fi
}

criterion_invoke() { # $1 = encoding, $2 = logf (append), $3 = optional FILTER
    # Two invocation modes:
    #  * default — `cargo bench` exactly as README §6 documents;
    #  * SA_VS_NAIVE_BENCH_BIN=<path> — invoke that ALREADY-BUILT criterion
    #    binary DIRECTLY, bypassing cargo's freshness check. Needed when the
    #    workspace sources are mutating under the protocol (e.g. a concurrent
    #    agent editing shared crates mid-run): cargo re-entry would REBUILD the
    #    bench from different (or broken) code than the driver phase measured,
    #    while the pinned binary keeps every criterion sample on byte-identical
    #    code — the same direct-invocation discipline §5 mandates for the
    #    driver. CARGO_TARGET_DIR is pinned so criterion resolves its output
    #    directory (target/criterion) without shelling out to cargo metadata.
    local enc="$1" logf="$2" filter="${3:-}" rc=0
    local envpair=() filterarg=()
    [ "$enc" = consume-test ] && envpair=("BENCH_SA_VS_NAIVE_ENCODING=consume-test")
    [ -n "$filter" ] && filterarg=("$filter")
    if [ -n "${SA_VS_NAIVE_BENCH_BIN:-}" ]; then
        [ -x "$SA_VS_NAIVE_BENCH_BIN" ] || { echo "[full] FAIL: SA_VS_NAIVE_BENCH_BIN=$SA_VS_NAIVE_BENCH_BIN is not executable" >&2; exit 1; }
        log "criterion invoke: DIRECT pinned binary $SA_VS_NAIVE_BENCH_BIN (sha256 $(sha256sum "$SA_VS_NAIVE_BENCH_BIN" | awk '{print $1}'))"
        systemd-run --user --scope -q -p MemoryMax=28G \
            env "RUST_MIN_STACK=$RUST_MIN_STACK" "CARGO_TARGET_DIR=$REPO_ROOT/target" "${envpair[@]}" \
            taskset -c 0-7 \
            "$SA_VS_NAIVE_BENCH_BIN" \
                --bench \
                "${filterarg[@]}" \
                --sample-size "$CRITERION_SAMPLE_SIZE" --warm-up-time "$CRITERION_WARM_UP_TIME" \
            2>&1 | tee -a "$logf"
        # ^ `--bench` is what cargo itself passes to a criterion binary under
        #   `cargo bench`; without it the harness runs in TEST mode (one
        #   unmeasured iteration per id, nothing written to target/criterion).
        rc=${PIPESTATUS[0]}
    else
        systemd-run --user --scope -q -p MemoryMax=28G \
            env "RUST_MIN_STACK=$RUST_MIN_STACK" "${envpair[@]}" \
            taskset -c 0-7 \
            cargo bench -p rholang-runtime \
                --features "$FEATURES" \
                --bench bench_sa_vs_naive -- \
                "${filterarg[@]}" \
                --sample-size "$CRITERION_SAMPLE_SIZE" --warm-up-time "$CRITERION_WARM_UP_TIME" \
            2>&1 | tee -a "$logf"
        rc=${PIPESTATUS[0]}
    fi
    if [ "$rc" -ne 0 ]; then
        warn "criterion run (encoding=$enc filter='${filter:-<none>}') exited rc=$rc — see $logf"
    fi
}

criterion_copy() { # $1 = encoding — copy target/criterion into the dated dir
    local enc="${1:-pattern-guard}" dest
    case "$enc" in
        pattern-guard) dest="$ROOT/criterion" ;;
        consume-test)  dest="$ROOT/criterion-consume-test" ;;
        *) echo "[full] FAIL: unknown criterion encoding $enc" >&2; exit 1 ;;
    esac
    rm -rf "$dest"
    cp -r target/criterion "$dest"
    log "criterion copy (encoding=$enc): target/criterion -> $dest"
}

criterion_phase() { # $1 = encoding (pattern-guard | consume-test)
    # The verbatim §6 protocol: ONE invocation over the whole matrix, then
    # copy. Where the execution environment enforces a wall-clock kill horizon
    # on long-lived tasks, use `criterion-chunk <filter>` invocations (same
    # command + pinning + flags, plus criterion's native FILTER argument —
    # measurement-identical, groups are independent) followed by
    # `criterion-copy`.
    local enc="${1:-pattern-guard}" logf
    case "$enc" in
        pattern-guard) logf="$ROOT/criterion-run.log" ;;
        consume-test)  logf="$ROOT/criterion-consume-test-run.log" ;;
        *) echo "[full] FAIL: unknown criterion encoding $enc" >&2; exit 1 ;;
    esac
    log "criterion phase start (encoding=$enc, --sample-size $CRITERION_SAMPLE_SIZE --warm-up-time $CRITERION_WARM_UP_TIME)"
    set_aside_previous_criterion
    criterion_invoke "$enc" "$logf"
    criterion_copy "$enc"
    log "criterion phase done (encoding=$enc)"
}

# ─────────────────────────────────────────────────────────────────────────────
# §7 post-processing + sanity checks (REPORT, never fix)
# ─────────────────────────────────────────────────────────────────────────────
post_phase() {
    log "post-processing start"
    local jsonls=("$DRIVER_DIR"/*.jsonl)
    [ -e "${jsonls[0]}" ] || { echo "[full] FAIL: no driver jsonl files under $DRIVER_DIR" >&2; exit 1; }

    # ── README §7 tables, measured reps only (warmup != true is the one
    #    amendment to the verbatim §7 jq — this run's files carry 33 reps of
    #    which the first 3 are warmup-marked; the §7 discipline of ≥30
    #    accepted reps refers to the MEASURED population). ──────────────────
    {
        echo 'workload,matcher,encoding,n,rep,build_ns,inj_ns,readback_ns,program_encoded_len,program_receiver_count,observed_count,consumed_cost_units,matching_tau,firing_visible,subst_tau,ac_carrier,contextual_plumbing,observation,other,join_arity_gt1,attempts,successes'
        jq -r 'select(.workload and (.dnf != true) and (.warmup != true)) |
            [.workload.name, .workload.matcher, .workload.encoding, .workload.n, .workload.rep,
             .build_ns, .inj_ns, .readback_ns, .program_encoded_len, .program_receiver_count,
             .observed_count, .consumed_cost_units,
             .comm.matching_tau, .comm.firing_visible, .comm.subst_tau, .comm.ac_carrier,
             .comm.contextual_plumbing, .comm.observation, .comm.other, .comm.join_arity_gt1,
             .matches.attempts, .matches.successes] | @csv' "${jsonls[@]}"
    } > "$CSV_DIR/driver_cells.csv"

    {
        echo 'workload,matcher,encoding,n,reps,median_inj_ns,median_matching_tau,median_attempts,median_consumed'
        jq -rs '
            def median: sort | if length == 0 then null
              elif length % 2 == 1 then .[length/2 | floor]
              else (.[length/2 - 1] + .[length/2]) / 2 end;
            [.[] | select(.workload and (.dnf != true) and (.warmup != true))]
            | group_by(.workload.name, .workload.matcher, .workload.encoding, .workload.n)[]
            | [.[0].workload.name, .[0].workload.matcher, .[0].workload.encoding, .[0].workload.n,
               length,
               ([.[].inj_ns] | median),
               ([.[].comm.matching_tau] | median),
               ([.[].matches.attempts] | median),
               ([.[].consumed_cost_units] | median)] | @csv' "${jsonls[@]}"
    } > "$CSV_DIR/driver_summary.csv"

    # DNF audit — dnf lines are DATA for this run (60 s guard DNFs included);
    # per README §7 an accepted CLEAN run has this empty.
    jq -r 'select(.dnf == true) | [.workload.name, .workload.matcher, .workload.encoding, .workload.n, .workload.rep, (if .warmup == true then 1 else 0 end), .reason] | @csv' \
        "${jsonls[@]}" > "$CSV_DIR/dnf_audit.csv"

    # Per-cell line accounting (feeds the completion report).
    {
        echo 'workload,matcher,encoding,n,total_rep_lines,warmup_ok,warmup_dnf,measured_ok,measured_dnf'
        jq -rs '
            [.[] | select(.workload)]
            | group_by(.workload.name, .workload.matcher, .workload.encoding, .workload.n)[]
            | [.[0].workload.name, .[0].workload.matcher, .[0].workload.encoding, .[0].workload.n,
               length,
               ([.[] | select(.warmup == true  and .dnf != true)] | length),
               ([.[] | select(.warmup == true  and .dnf == true)] | length),
               ([.[] | select(.warmup != true and .dnf != true)] | length),
               ([.[] | select(.warmup != true and .dnf == true)] | length)] | @csv' "${jsonls[@]}"
    } > "$CSV_DIR/cell_accounting.csv"

    # ── Task-shape tables ────────────────────────────────────────────────────
    # summary.csv: EVERY rep line (warmup + dnf included, flagged).
    {
        echo 'workload,matcher,encoding,n,rep,warmup,dnf,dnf_reason,build_ns,inj_ns,readback_ns,program_encoded_len,program_receiver_count,observed_count,consumed_cost_units,matching_tau,firing_visible,subst_tau,ac_carrier,contextual_plumbing,observation,other,join_arity_gt1,attempts,successes'
        jq -r 'select(.workload) |
            [.workload.name, .workload.matcher, .workload.encoding, .workload.n, .workload.rep,
             (if .warmup == true then 1 else 0 end),
             (if .dnf == true then 1 else 0 end),
             (.reason // ""),
             .build_ns, .inj_ns, .readback_ns, .program_encoded_len, .program_receiver_count,
             .observed_count, .consumed_cost_units,
             .comm.matching_tau, .comm.firing_visible, .comm.subst_tau, .comm.ac_carrier,
             .comm.contextual_plumbing, .comm.observation, .comm.other, .comm.join_arity_gt1,
             .matches.attempts, .matches.successes] | @csv' "${jsonls[@]}"
    } > "$ROOT/summary.csv"

    # summary_medians.csv: per-cell medians over the 30 measured (non-warmup,
    # non-dnf) reps, all counters + timings.
    {
        echo 'workload,matcher,encoding,n,measured_ok_reps,median_build_ns,median_inj_ns,median_readback_ns,median_program_encoded_len,median_program_receiver_count,median_observed_count,median_consumed_cost_units,median_matching_tau,median_firing_visible,median_subst_tau,median_attempts,median_successes'
        jq -rs '
            def median: sort | if length == 0 then null
              elif length % 2 == 1 then .[length/2 | floor]
              else (.[length/2 - 1] + .[length/2]) / 2 end;
            [.[] | select(.workload and (.dnf != true) and (.warmup != true))]
            | group_by(.workload.name, .workload.matcher, .workload.encoding, .workload.n)[]
            | [.[0].workload.name, .[0].workload.matcher, .[0].workload.encoding, .[0].workload.n,
               length,
               ([.[].build_ns] | median),
               ([.[].inj_ns] | median),
               ([.[].readback_ns] | median),
               ([.[].program_encoded_len] | median),
               ([.[].program_receiver_count] | median),
               ([.[].observed_count] | median),
               ([.[].consumed_cost_units] | median),
               ([.[].comm.matching_tau] | median),
               ([.[].comm.firing_visible] | median),
               ([.[].comm.subst_tau] | median),
               ([.[].matches.attempts] | median),
               ([.[].matches.successes] | median)] | @csv' "${jsonls[@]}"
    } > "$ROOT/summary_medians.csv"

    # ── Sanity checks (report-only; results land in sanity.txt) ─────────────
    {
        echo "sanity checks — sa-vs-naive full run $DATE ($(date -Is))"
        echo

        # 1. Every jsonl parses; every complete cell has 1 + TOTAL_REPS lines.
        local parse_fail=0
        for f in "${jsonls[@]}"; do
            if ! jq -e . "$f" >/dev/null 2>&1; then
                echo "PARSE FAIL: $f contains a non-JSON line"
                parse_fail=1
            fi
            local lines
            lines=$(wc -l < "$f")
            if [ "$lines" -ne $((TOTAL_REPS + 1)) ]; then
                echo "LINE-COUNT: $f has $lines lines (expected $((TOTAL_REPS + 1)))"
                parse_fail=1
            fi
        done
        [ "$parse_fail" -eq 0 ] && echo "PASS: every jsonl parses and has 1 header + $TOTAL_REPS rep lines"
        echo

        # 2. expected_firings == observed_count on every non-dnf rep (warmup
        #    included — ground truth is rep-independent).
        local truth_fail=0
        for f in "${jsonls[@]}"; do
            local bad
            bad=$(jq -rs '
                (.[0].header.expected_firings) as $want
                | [.[] | select(.workload and .dnf != true) | select(.observed_count != $want)
                   | "rep \(.workload.rep): observed \(.observed_count) != expected \($want)"]
                | .[]' "$f")
            if [ -n "$bad" ]; then
                echo "GROUND-TRUTH FAIL: $f"; echo "$bad" | sed 's/^/    /'
                truth_fail=1
            fi
        done
        [ "$truth_fail" -eq 0 ] && echo "PASS: observed_count == header.expected_firings on every non-dnf rep of every cell"
        echo

        # 3. Determinism: rep-to-rep COUNTER variance must be ZERO per cell
        #    (fixed seed). Checked over ALL non-dnf reps (warmup included —
        #    counters are wall-time-independent); wall timings excluded.
        local var_fail=0
        for f in "${jsonls[@]}"; do
            local varying
            varying=$(jq -rs '
                [.[] | select(.workload and .dnf != true)]
                | if length < 2 then empty else
                  [
                    {k: "program_encoded_len",    u: ([.[].program_encoded_len]    | unique | length)},
                    {k: "program_receiver_count", u: ([.[].program_receiver_count] | unique | length)},
                    {k: "observed_count",         u: ([.[].observed_count]         | unique | length)},
                    {k: "consumed_cost_units",    u: ([.[].consumed_cost_units]    | unique | length)},
                    {k: "matching_tau",           u: ([.[].comm.matching_tau]      | unique | length)},
                    {k: "firing_visible",         u: ([.[].comm.firing_visible]    | unique | length)},
                    {k: "subst_tau",              u: ([.[].comm.subst_tau]         | unique | length)},
                    {k: "ac_carrier",             u: ([.[].comm.ac_carrier]        | unique | length)},
                    {k: "contextual_plumbing",    u: ([.[].comm.contextual_plumbing] | unique | length)},
                    {k: "observation",            u: ([.[].comm.observation]       | unique | length)},
                    {k: "other",                  u: ([.[].comm.other]             | unique | length)},
                    {k: "join_arity_gt1",         u: ([.[].comm.join_arity_gt1]    | unique | length)},
                    {k: "attempts",               u: ([.[].matches.attempts]       | unique | length)},
                    {k: "successes",              u: ([.[].matches.successes]      | unique | length)}
                  ] | map(select(.u > 1) | .k) | if length == 0 then empty else join(",") end
                  end' "$f")
            if [ -n "$varying" ]; then
                echo "COUNTER-VARIANCE: $f — varying across reps: $varying"
                var_fail=1
            fi
        done
        [ "$var_fail" -eq 0 ] && echo "PASS: zero rep-to-rep counter variance in every cell (deterministic seed confirmed)"
        echo

        # DNF accounting (dnf lines are data; listed for the record).
        echo "dnf lines by cell (empty = none):"
        jq -r 'select(.dnf == true) | "\(.workload.name)/\(.workload.matcher)/\(.workload.encoding) n=\(.workload.n) rep=\(.workload.rep)\(if .warmup == true then " (warmup)" else "" end): \(.reason)"' \
            "${jsonls[@]}" | sort | uniq -c | sed 's/^/  /'
    } | tee "$ROOT/sanity.txt" >&2

    log "post-processing done: $CSV_DIR/{driver_cells,driver_summary,dnf_audit,cell_accounting}.csv, $ROOT/{summary,summary_medians}.csv, $ROOT/sanity.txt"
}

# ─────────────────────────────────────────────────────────────────────────────
record_env
case "$PHASE" in
    driver)           driver_phase ;;
    criterion)        criterion_phase pattern-guard ;;
    criterion-ct)     criterion_phase consume-test ;;
    criterion-chunk)  # $3 = FILTER (criterion substring filter); no set-aside, no copy
                      criterion_invoke pattern-guard "$ROOT/criterion-run.log" "${3:?criterion-chunk needs a FILTER}" ;;
    criterion-ct-chunk) criterion_invoke consume-test "$ROOT/criterion-consume-test-run.log" "${3:?criterion-ct-chunk needs a FILTER}" ;;
    criterion-copy)   criterion_copy "${3:-pattern-guard}" ;;
    post)             post_phase ;;
    all)              driver_phase; criterion_phase pattern-guard; post_phase ;;
    *) echo "[full] FAIL: unknown phase $PHASE (driver|criterion|criterion-ct|criterion-chunk|criterion-ct-chunk|criterion-copy|post|all)" >&2; exit 1 ;;
esac
log "phase(s) '$PHASE' complete for $ROOT"
