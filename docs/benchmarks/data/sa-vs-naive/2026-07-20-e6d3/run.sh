#!/usr/bin/env bash
# E-6d #3 re-measurement (pgmcp experiment 150) — identical protocol to
# ../2026-07-19-e6a/run.sh, ../2026-07-19-e6a-postfix/run.sh,
# ../2026-07-20-e6d1/run.sh and ../2026-07-20-e6d2/run.sh (33 reps/cell, first
# 3 warmups, deterministic seeds, pinned to CPUs 0-7), re-run against the
# f1r3node-rust-mettail `fix/epathmap-value-handling` stack @ 131aecee — the
# full E-6d #2 stack (P0 602144bd; P1 c3d5b3f2; P2 351e494d; P3 4e422b6b;
# P4.1 60aaa02e; P4.2 6c0a90cb; P4.3 ead2f152) PLUS the L2 shared-ps commit
# 131aecee (Arc-backed SharedPars; O(1) ps clone at the node; CoW mutation
# census), all stacked on the trie-cache fix 84a0fbe4. Only OUT differs from
# the e6d2 script. The primary COMM metric is counter-deterministic and MUST
# be identical to all four baseline runs. THIS RUN IS THE L2 FALSIFICATION
# TEST (attribution hypothesis): the frozen verdict instrument is the profile's
# boxed prost `Expr::to_vec` absolute ms/inj on swap_comb n=16 treatment —
# >=50% fall from the e6d2 ~44.8 ms/inj => the EPathMap-ps attribution is
# CONFIRMED; within +/-20% => REFUTED (the floor is general Par/Expr cloning
# elsewhere); between => partial (report the number). Confirmed-branch wall
# prediction: >=1.1x FURTHER treatment inj vs e6d2 on swap_comb n=16 AND
# nested_spine n=16. swap_comb 64's TREATMENT remains expected to
# DNF-by-machine-cap (the reducer trie-key arity cap — unrelated to, and
# untouched by, the fix stack).
#
# E-6d #1 LESSON (frozen since experiment 149): the machine MUST settle >=3
# minutes after the release build before the first measured cell (the e6d1
# swap_comb64-control +10.4% transient came from measuring 15-69 s
# post-build). The settle wait and run order are recorded in the run log.
set -u
cd "$(dirname "$0")/../../../../.."

DRIVER=target/release/bench_e6a_pathmap_driver
OUT=docs/benchmarks/data/sa-vs-naive/2026-07-20-e6d3/driver
mkdir -p "$OUT"

REPS=33
WARMUPS=3

run_cell() {
  local workload="$1" n="$2" arm="$3"
  local file="$OUT/${workload}-n${n}-${arm}.jsonl"
  echo "=== $(date -Is) cell ${workload} n=${n} arm=${arm} -> ${file}"
  RUST_MIN_STACK=8388608 taskset -c 0-7 "$DRIVER" \
    --workload "$workload" --arm "$arm" --n "$n" \
    --reps "$REPS" --warmups "$WARMUPS" --out "$file"
  echo "--- exit $? for ${workload} n=${n} arm=${arm}"
}

for n in 4 16 64; do
  for arm in control treatment; do run_cell swap_comb "$n" "$arm"; done
done
for n in 402 803; do
  for arm in control treatment; do run_cell multi_rule_shared "$n" "$arm"; done
done
for n in 2 8 16; do
  for arm in control treatment; do run_cell nested_spine "$n" "$arm"; done
done
for n in 4 8; do
  for arm in control treatment; do run_cell lambda_chain "$n" "$arm"; done
done

echo "=== $(date -Is) E-6d #3 run complete"
