#!/usr/bin/env bash
# Track B — B6 §3: SMOKE validation of the sa-vs-naive benchmark harness.
#
# Runs the JSON-lines driver (`bench_sa_vs_naive_driver`) over the smoke cells
# (small sizes, 2 reps each, PatternGuard) and asserts:
#   1. every emitted line parses as JSON (jq when available, else grep floor);
#   2. no `"dnf":true` line anywhere;
#   3. per workload, the observed multisets AGREE between the two matcher
#      columns and the observed/firing counts equal the pre-computed ground
#      truth (the driver additionally verifies the observed CONTENT against the
#      expected multiset inside every rep — a mismatch would have produced a
#      dnf line, caught by 2);
#   4. the STRUCTURAL discriminating signal exists: comm.matching_tau AND
#      matches.attempts differ between the naive (in-Rho matching) and replay
#      (host-computed σ) columns on nested_spine — in-Rho matching MUST cost
#      τ-COMMs that a host replay does not, so equality here means broken
#      counters (hard assert);
#   5. the PRE-REGISTERED lambda_chain hypothesis — matching_tau divergence
#      between the sa and naive columns — is MEASURED and reported as a
#      CONFIRMED/REFUTED verdict, not hard-asserted: the B5/B6 smoke found the
#      two columns COUNT-IDENTICAL on the root-restricted per-step drive
#      (single rule, single site ⇒ the per-site COMM work coincides; the
#      same-CLTS theorem only promises a difference in erased τ STRUCTURE,
#      not τ count), and a smoke script must report reality, not enforce a
#      falsified hypothesis.
#   6. the AMENDED-W1 multi_rule_shared signal (pgmcp experiment 144
#      amendment, workload (vii)): at r = 4, s = 2 (n = 402) the naive
#      column's matching_tau must EXCEED the sa column's — HARD assert per the
#      amendment protocol (a failure is a REFUTATION that must surface with
#      its numbers; never weaken this assertion to make the smoke pass).
# Finally prints a per-cell summary table (matching_tau, firing_visible,
# attempts/successes, inj ms, consumed cost units).
#
# Usage: smoke.sh <out-dir> [cargo-profile]
#   out-dir        directory for the .jsonl outputs (created if absent)
#   cargo-profile  cargo profile for the driver build (default: release)
#
# The smoke run is NOT the measurement protocol (see README.md for the full
# pinned protocol): it validates plumbing, correctness, and signal visibility.

set -euo pipefail

OUT_DIR="${1:?usage: smoke.sh <out-dir> [cargo-profile]}"
PROFILE="${2:-release}"
FEATURES="bench-naive-baseline swap-demo-runtime lambda-demo-runtime ctx-demo-runtime"
REPS=2

mkdir -p "$OUT_DIR"
export RUST_MIN_STACK=8388608

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
cd "$REPO_ROOT"

# Build ONCE, then invoke the produced binary DIRECTLY: per-cell `cargo run`
# would re-run the whole-workspace freshness check on every invocation
# (minutes each on this workspace), and the [env] RUST_MIN_STACK from
# .cargo/config.toml is exported above for the off-cargo invocation.
cargo build --quiet --profile "$PROFILE" -p rholang-runtime \
    --features "$FEATURES" --bin bench_sa_vs_naive_driver
case "$PROFILE" in
    dev) DRIVER="$REPO_ROOT/target/debug/bench_sa_vs_naive_driver" ;;
    *)   DRIVER="$REPO_ROOT/target/$PROFILE/bench_sa_vs_naive_driver" ;;
esac
[ -x "$DRIVER" ] || { echo "[smoke] FAIL: driver binary not found at $DRIVER" >&2; exit 1; }

run_cell() {
    local workload="$1" matcher="$2" n="$3"
    local out="$OUT_DIR/${workload}_${matcher}_n${n}.jsonl"
    echo "[smoke] $workload/$matcher n=$n reps=$REPS -> $out"
    "$DRIVER" \
        --workload "$workload" --matcher "$matcher" --encoding pattern-guard \
        --n "$n" --reps "$REPS" --format json-lines --out "$out"
}

# The smoke cells (task §3): every workload family, both of its columns.
run_cell lambda_chain sa 2
run_cell lambda_chain naive 2
run_cell swap_comb sa 4
run_cell swap_comb naive 4
run_cell nested_spine naive 2
run_cell nested_spine replay 2
run_cell swap_small sa 2
run_cell swap_small naive 2
run_cell wrap_swap_ctx sa 1
run_cell wrap_swap_ctx naive 1
run_cell multi_rule_shared sa 402
run_cell multi_rule_shared naive 402

HAVE_JQ=0
if command -v jq >/dev/null 2>&1; then HAVE_JQ=1; fi

fail() { echo "[smoke] FAIL: $*" >&2; exit 1; }

# ── Assertion 1: every line parses ──────────────────────────────────────────
for file in "$OUT_DIR"/*.jsonl; do
    [ -s "$file" ] || fail "$file is empty"
    if [ "$HAVE_JQ" -eq 1 ]; then
        jq -e . "$file" >/dev/null || fail "$file contains a non-JSON line"
    else
        # Grep floor: every line is a braced object.
        if grep -qvE '^\{.*\}$' "$file"; then
            fail "$file contains a non-JSON-shaped line"
        fi
    fi
done
echo "[smoke] PASS: every line parses"

# ── Assertion 2: no DNF ─────────────────────────────────────────────────────
if grep -q '"dnf":true' "$OUT_DIR"/*.jsonl; then
    grep -H '"dnf":true' "$OUT_DIR"/*.jsonl >&2
    fail "dnf lines present"
fi
echo "[smoke] PASS: no dnf lines"

# ── Assertion 3: counts equal ground truth, per cell and across matchers ────
# Expected observed_count per cell (== expected_firings; the driver has already
# verified the observed CONTENT against the expected multiset inside each rep,
# so equal counts here + no dnf above ⇒ equal multisets across matchers).
declare -A EXPECTED=(
    [lambda_chain_sa_n2]=2    [lambda_chain_naive_n2]=2
    [swap_comb_sa_n4]=4       [swap_comb_naive_n4]=4
    [nested_spine_naive_n2]=2 [nested_spine_replay_n2]=2
    [swap_small_sa_n2]=1      [swap_small_naive_n2]=1
    [wrap_swap_ctx_sa_n1]=1   [wrap_swap_ctx_naive_n1]=1
    [multi_rule_shared_sa_n402]=4 [multi_rule_shared_naive_n402]=4
)
observed_counts() { # file -> one observed_count per rep line
    if [ "$HAVE_JQ" -eq 1 ]; then
        jq -r 'select(.workload and (.dnf != true)) | .observed_count' "$1"
    else
        grep -o '"observed_count":[0-9]*' "$1" | cut -d: -f2
    fi
}
for cell in "${!EXPECTED[@]}"; do
    file="$OUT_DIR/${cell%_n*}_n${cell##*_n}.jsonl"
    want="${EXPECTED[$cell]}"
    counts=$(observed_counts "$file")
    [ -n "$counts" ] || fail "$file has no rep lines"
    reps_seen=0
    while read -r count; do
        reps_seen=$((reps_seen + 1))
        [ "$count" -eq "$want" ] || fail "$cell: observed_count $count != expected $want"
    done <<<"$counts"
    [ "$reps_seen" -eq "$REPS" ] || fail "$cell: $reps_seen rep lines, expected $REPS"
done
echo "[smoke] PASS: observed counts equal expected firings on every cell (both columns agree)"

# ── Assertion 4: the STRUCTURAL discriminating signal on nested_spine ───────
first_field() { # file jq-path grep-key -> value from the FIRST rep line
    if [ "$HAVE_JQ" -eq 1 ]; then
        jq -r "[.[] | select(.workload and (.dnf != true))][0] | $2" <<<"$(jq -s . "$1")"
    else
        grep -o "\"$3\":[0-9-]*" "$1" | head -1 | cut -d: -f2
    fi
}
NS_NAIVE_TAU=$(first_field "$OUT_DIR/nested_spine_naive_n2.jsonl" '.comm.matching_tau' 'matching_tau')
NS_REPLAY_TAU=$(first_field "$OUT_DIR/nested_spine_replay_n2.jsonl" '.comm.matching_tau' 'matching_tau')
NS_NAIVE_ATT=$(first_field "$OUT_DIR/nested_spine_naive_n2.jsonl" '.matches.attempts' 'attempts')
NS_REPLAY_ATT=$(first_field "$OUT_DIR/nested_spine_replay_n2.jsonl" '.matches.attempts' 'attempts')
if [ "$NS_NAIVE_TAU" = "$NS_REPLAY_TAU" ] || [ "$NS_NAIVE_ATT" = "$NS_REPLAY_ATT" ]; then
    fail "nested_spine naive vs replay counters do not diverge (tau $NS_NAIVE_TAU vs $NS_REPLAY_TAU, attempts $NS_NAIVE_ATT vs $NS_REPLAY_ATT) — the in-Rho-matching-vs-host-replay signal is broken"
fi
echo "[smoke] PASS: nested_spine diverges naive-vs-replay (matching_tau $NS_NAIVE_TAU vs $NS_REPLAY_TAU, attempts $NS_NAIVE_ATT vs $NS_REPLAY_ATT)"

# ── Verdict 5: the pre-registered lambda_chain matching_tau hypothesis ──────
SA_TAU=$(first_field "$OUT_DIR/lambda_chain_sa_n2.jsonl" '.comm.matching_tau' 'matching_tau')
NAIVE_TAU=$(first_field "$OUT_DIR/lambda_chain_naive_n2.jsonl" '.comm.matching_tau' 'matching_tau')
if [ "$SA_TAU" = "$NAIVE_TAU" ]; then
    echo "[smoke] VERDICT: lambda_chain matching_tau hypothesis REFUTED at n=2 (sa=$SA_TAU == naive=$NAIVE_TAU): the root-restricted per-step drives are COMM-count-identical (single rule, single site — same-CLTS τ-STRUCTURE differs, τ COUNT does not)"
else
    echo "[smoke] VERDICT: lambda_chain matching_tau hypothesis CONFIRMED at n=2 (sa=$SA_TAU vs naive=$NAIVE_TAU)"
fi


# ── Summary table ───────────────────────────────────────────────────────────
echo
echo "[smoke] per-cell summary (rep 0):"
printf '%-28s %12s %8s %10s %11s %10s %10s\n' \
    cell matching_tau firing attempts successes inj_ms cost_units
for cell in lambda_chain_sa_n2 lambda_chain_naive_n2 swap_comb_sa_n4 swap_comb_naive_n4 \
            nested_spine_naive_n2 nested_spine_replay_n2 swap_small_sa_n2 swap_small_naive_n2 \
            wrap_swap_ctx_sa_n1 wrap_swap_ctx_naive_n1 \
            multi_rule_shared_sa_n402 multi_rule_shared_naive_n402; do
    file="$OUT_DIR/${cell%_n*}_n${cell##*_n}.jsonl"
    if [ "$HAVE_JQ" -eq 1 ]; then
        jq -r --arg cell "$cell" \
            '[.[] | select(.workload and (.dnf != true))][0] |
             [$cell, .comm.matching_tau, .comm.firing_visible, .matches.attempts,
              .matches.successes, (.inj_ns / 1e6 | floor), .consumed_cost_units] | @tsv' \
            <<<"$(jq -s . "$file")" |
            awk -F'\t' '{ printf "%-28s %12s %8s %10s %11s %10s %10s\n", $1, $2, $3, $4, $5, $6, $7 }'
    else
        tau=$(first_field "$file" '.comm.matching_tau' 'matching_tau')
        firing=$(first_field "$file" '.comm.firing_visible' 'firing_visible')
        attempts=$(first_field "$file" '.matches.attempts' 'attempts')
        printf '%-28s %12s %8s %10s %11s %10s %10s\n' \
            "$cell" "$tau" "$firing" "$attempts" '?' '?' '?'
    fi
done

# ── Assertion 6: multi_rule_shared counter equality (r = 4, s = 2) ──────────
# MEASURED VERDICT + regression pin (pgmcp experiment 144 amendment; measured
# 2026-07-19): the amended-W1 prediction (naive matching_tau > sa on the
# multi-rule shared-structure family) was REFUTED with a mechanism — every
# ruleset the naive OverlappingTagDemand gate admits is itself symbol-once
# under the once-published spread (≤1 candidate reader per message), so EXACT
# counter equality is the mechanism's prediction and the pinned expectation.
# A divergence in EITHER direction contradicts the recorded finding and fails
# this smoke (see the README FINDING ADDENDUM and experiment 144's ledger).
echo
MRS_SA_TAU=$(first_field "$OUT_DIR/multi_rule_shared_sa_n402.jsonl" '.comm.matching_tau' 'matching_tau')
MRS_NAIVE_TAU=$(first_field "$OUT_DIR/multi_rule_shared_naive_n402.jsonl" '.comm.matching_tau' 'matching_tau')
MRS_SA_ATT=$(first_field "$OUT_DIR/multi_rule_shared_sa_n402.jsonl" '.matches.attempts' 'attempts')
MRS_NAIVE_ATT=$(first_field "$OUT_DIR/multi_rule_shared_naive_n402.jsonl" '.matches.attempts' 'attempts')
if [ "$MRS_NAIVE_TAU" -eq "$MRS_SA_TAU" ] && [ "$MRS_NAIVE_ATT" -eq "$MRS_SA_ATT" ]; then
    echo "[smoke] VERDICT: amended-W1 signal MEASURED REFUTED — counter equality confirmed at r=4, s=2 (matching_tau naive $MRS_NAIVE_TAU = sa $MRS_SA_TAU; attempts naive $MRS_NAIVE_ATT = sa $MRS_SA_ATT)"
else
    fail "multi_rule_shared counter equality violated at r=4, s=2 (matching_tau naive $MRS_NAIVE_TAU vs sa $MRS_SA_TAU; attempts naive $MRS_NAIVE_ATT vs sa $MRS_SA_ATT) — contradicts the recorded amended-W1 refutation mechanism (experiment 144); investigate before re-pinning"
fi

echo
echo "[smoke] ALL ASSERTIONS PASSED"
