#!/usr/bin/env bash
# Pgmcp experiment 174: one-shot post-D-E5 production-SA versus persistent-R3
# counter and warm-wall run. The script refuses an existing output directory:
# a failed cell is evidence and must not be silently replaced by a rerun.

set -euo pipefail

RUN_ID="${1:?usage: post-d-e5-r3.sh <run-id>}"
FEATURES="bench-naive-baseline swap-demo-runtime lambda-demo-runtime ctx-demo-runtime"
WARMUP_REPS=3
MEASURED_REPS=51
TOTAL_REPS=$((WARMUP_REPS + MEASURED_REPS))
BUILD_MEMORY_MAX=12G
RUN_MEMORY_MAX=4G
PINNED_CPUS=0-7

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)"
cd "$REPO_ROOT"
unset RUST_MIN_STACK || true

ROOT="docs/benchmarks/data/sa-vs-naive/$RUN_ID"
DRIVER_DIR="$ROOT/driver"
DRIVER="$REPO_ROOT/target/release/bench_sa_vs_naive_driver"
if [ -e "$ROOT" ]; then
    echo "[post-d-e5-r3] FAIL: $ROOT already exists; never overwrite or cherry-pick a captured run" >&2
    exit 2
fi
mkdir -p "$DRIVER_DIR"

command -v jq >/dev/null 2>&1 || { echo "[post-d-e5-r3] FAIL: jq is required" >&2; exit 2; }

log() { echo "[post-d-e5-r3] $(date -Is) $*" | tee -a "$ROOT/run.log" >&2; }

log "build start: parallel release build, ordinary stacks, cap=$BUILD_MEMORY_MAX, swap=0"
systemd-run --user --scope -q -p "MemoryMax=$BUILD_MEMORY_MAX" -p MemorySwapMax=0 \
    env -u RUST_MIN_STACK \
    cargo build --release -p rholang-runtime --features "$FEATURES" \
        --bin bench_sa_vs_naive_driver 2>&1 | tee "$ROOT/build.log"
[ -x "$DRIVER" ] || { log "FAIL: release driver missing at $DRIVER"; exit 2; }

DRIVER_SHA=$(sha256sum "$DRIVER" | awk '{print $1}')
GIT_SHA=$(git rev-parse HEAD)
{
    echo "experiment_id: 174"
    echo "hypothesis_id: 174"
    echo "git_sha: $GIT_SHA"
    echo "git_branch: $(git rev-parse --abbrev-ref HEAD)"
    echo "driver_sha256: $DRIVER_SHA"
    echo "hostname: $(hostname)"
    echo "uname: $(uname -a)"
    echo "rustc: $(rustc --version)"
    echo "cpu: $(lscpu | awk -F: '/Model name/{sub(/^[[:space:]]+/,"",$2); print $2; exit}')"
    echo "governor: $(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor)"
    echo "scaling_driver: $(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_driver)"
    echo "boost: $(cat /sys/devices/system/cpu/cpufreq/boost)"
    echo "pinned_cpus: $PINNED_CPUS"
    echo "build_memory_max: $BUILD_MEMORY_MAX"
    echo "run_memory_max: $RUN_MEMORY_MAX"
    echo "memory_swap_max: 0"
    echo "rust_min_stack: unset"
    echo "warmup_reps: $WARMUP_REPS"
    echo "measured_reps: $MEASURED_REPS"
    echo "arm_order: even ladder index sa then naive-r3; odd index naive-r3 then sa"
    echo "recorded_at: $(date -Is)"
} > "$ROOT/env.txt"

jq -n \
    --arg run_id "$RUN_ID" --arg git_sha "$GIT_SHA" --arg driver_sha "$DRIVER_SHA" \
    --arg cpus "$PINNED_CPUS" --arg build_cap "$BUILD_MEMORY_MAX" --arg run_cap "$RUN_MEMORY_MAX" \
    --argjson warmups "$WARMUP_REPS" --argjson measured "$MEASURED_REPS" \
    '{experiment_id:174,hypothesis_id:174,run_id:$run_id,git_sha:$git_sha,
      driver_sha256:$driver_sha,workload:"lambda_chain",sizes:[2,4,8,16,32,64],
      arms:{control:"sa",treatment:"naive-r3"},encoding:"pattern-guard",
      affinity:$cpus,memory:{build_max:$build_cap,run_max:$run_cap,swap_max:0},
      stack_policy:"ordinary; RUST_MIN_STACK removed",warmup_reps:$warmups,
      measured_reps:$measured,recorded_at:(now|todate)}' > "$ROOT/header.json"

run_cell() {
    local matcher=$1 n=$2 out="$DRIVER_DIR/lambda_chain_${matcher}_n${n}.jsonl"
    local raw="${out}.raw" cell_log="$DRIVER_DIR/lambda_chain_${matcher}_n${n}.log"
    log "START lambda_chain/$matcher n=$n reps=$TOTAL_REPS"
    systemd-run --user --scope -q \
        -p "MemoryMax=$RUN_MEMORY_MAX" -p MemorySwapMax=0 \
        /usr/bin/time -v env -u RUST_MIN_STACK taskset -c "$PINNED_CPUS" \
        "$DRIVER" --workload lambda_chain --matcher "$matcher" \
            --encoding pattern-guard --n "$n" --reps "$TOTAL_REPS" \
            --format json-lines --out "$raw" > "$cell_log" 2>&1
    jq -c --argjson warmups "$WARMUP_REPS" \
        'if (.workload.rep != null) and (.workload.rep < $warmups)
         then . + {"warmup":true} else . end' "$raw" > "$out"
    rm -f "$raw"
    [ "$(wc -l < "$out")" -eq $((TOTAL_REPS + 1)) ] || {
        log "FAIL lambda_chain/$matcher n=$n: incomplete JSON-lines file"; exit 1;
    }
    log "DONE lambda_chain/$matcher n=$n"
}

sizes=(2 4 8 16 32 64)
for index in "${!sizes[@]}"; do
    n="${sizes[$index]}"
    if (( index % 2 == 0 )); then
        run_cell sa "$n"
        run_cell naive-r3 "$n"
    else
        run_cell naive-r3 "$n"
        run_cell sa "$n"
    fi
done

jsonls=("$DRIVER_DIR"/*.jsonl)
{
    echo -e 'workload\tmatcher\tn\trep\tinj_ns\tbuild_ns\treadback_ns\tprogram_encoded_len\tprogram_receiver_count\tobserved_count\tconsumed_cost_units\tmatching_tau\tfiring_visible\tsubst_tau\trespread_tau\tother\tjoin_arity_gt1\tattempts\tsuccesses'
    jq -r 'select(.workload and (.dnf != true) and (.warmup != true)) |
      [.workload.name,.workload.matcher,.workload.n,.workload.rep,.inj_ns,.build_ns,
       .readback_ns,.program_encoded_len,.program_receiver_count,.observed_count,
       .consumed_cost_units,.comm.matching_tau,.comm.firing_visible,.comm.subst_tau,
       .comm.respread_tau,.comm.other,.comm.join_arity_gt1,.matches.attempts,
       .matches.successes] | @tsv' "${jsonls[@]}"
} > "$ROOT/samples.tsv"

{
    echo -e 'matcher\tn\tmeasured_reps\tmedian_inj_ns\tprogram_encoded_len\tprogram_receiver_count\tobserved_count\tconsumed_cost_units\tmatching_tau\tfiring_visible\tsubst_tau\trespread_tau\tother\tjoin_arity_gt1\tattempts\tsuccesses'
    for file in "${jsonls[@]}"; do
        jq -rs '
          def median: sort | .[length/2|floor];
          [.[] | select(.workload and (.dnf != true) and (.warmup != true))] as $r |
          [$r[0].workload.matcher,$r[0].workload.n,($r|length),
           ([$r[].inj_ns]|median),$r[0].program_encoded_len,$r[0].program_receiver_count,
           $r[0].observed_count,$r[0].consumed_cost_units,$r[0].comm.matching_tau,
           $r[0].comm.firing_visible,$r[0].comm.subst_tau,$r[0].comm.respread_tau,
           $r[0].comm.other,$r[0].comm.join_arity_gt1,$r[0].matches.attempts,
           $r[0].matches.successes] | @tsv' "$file"
    done
} > "$ROOT/summary.tsv"

{
    echo "post-D-E5 R3 sanity — pgmcp experiment 174"
    fail=0
    for file in "${jsonls[@]}"; do
        warm=$(jq -s '[.[]|select(.warmup==true)]|length' "$file")
        measured=$(jq -s '[.[]|select(.workload and (.dnf!=true) and (.warmup!=true))]|length' "$file")
        dnf=$(jq -s '[.[]|select(.dnf==true)]|length' "$file")
        unique=$(jq -s '[.[]|select(.workload and (.dnf!=true)) |
          [.program_encoded_len,.program_receiver_count,.observed_count,.consumed_cost_units,
           .comm.matching_tau,.comm.firing_visible,.comm.subst_tau,.comm.respread_tau,
           .comm.other,.comm.join_arity_gt1,.matches.attempts,.matches.successes]]|unique|length' "$file")
        if [ "$warm" -ne "$WARMUP_REPS" ] || [ "$measured" -ne "$MEASURED_REPS" ] || \
           [ "$dnf" -ne 0 ] || [ "$unique" -ne 1 ]; then
            echo "FAIL $file warm=$warm measured=$measured dnf=$dnf deterministic_vectors=$unique"
            fail=1
        else
            echo "PASS $file warm=$warm measured=$measured dnf=0 deterministic_vectors=1"
        fi
    done
    while read -r n; do
        sa_fire=$(awk -F '\t' -v n="$n" '$1=="sa"&&$2==n{print $10}' "$ROOT/summary.tsv")
        r3=$(awk -F '\t' -v n="$n" '$1=="naive-r3"&&$2==n{print $0}' "$ROOT/summary.tsv")
        r3_match=$(awk -F '\t' '{print $9}' <<< "$r3")
        r3_fire=$(awk -F '\t' '{print $10}' <<< "$r3")
        r3_subst=$(awk -F '\t' '{print $11}' <<< "$r3")
        r3_respread=$(awk -F '\t' '{print $12}' <<< "$r3")
        r3_other=$(awk -F '\t' '{print $13}' <<< "$r3")
        r3_join=$(awk -F '\t' '{print $14}' <<< "$r3")
        if [ "$sa_fire" -ne "$n" ] || [ "$r3_match" -ne $((4*n)) ] || \
           [ "$r3_fire" -ne "$n" ] || [ "$r3_subst" -ne $((3*n)) ] || \
           [ "$r3_respread" -ne $((3*n)) ] || [ "$r3_other" -ne "$n" ] || \
           [ "$r3_join" -ne 0 ]; then
            echo "FAIL n=$n semantic/route law sa_fire=$sa_fire r3=$r3_match/$r3_fire/$r3_subst/$r3_respread/$r3_other/$r3_join"
            fail=1
        else
            echo "PASS n=$n equal visible firings=$n; R3 matching/subst/respread/other/join=$r3_match/$r3_subst/$r3_respread/$r3_other/0"
        fi
    done < <(printf '%s\n' "${sizes[@]}")
    [ "$fail" -eq 0 ] || exit 1
} | tee "$ROOT/sanity.txt"

python3 docs/benchmarks/data/sa-vs-naive/analyze-post-d-e5-r3.py "$ROOT" \
    | tee "$ROOT/analysis.log"

sha256sum "$DRIVER" "${jsonls[@]}" "$ROOT/samples.tsv" "$ROOT/summary.tsv" \
    "$ROOT/analysis.json" "$ROOT/comparison.md" > "$ROOT/sha256sums.txt"
log "COMPLETE experiment 174 capture at $ROOT"
