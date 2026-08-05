#!/usr/bin/env bash
# HISTORICAL PROTOCOL ONLY: the cap/DNF expectation and RUST_MIN_STACK setting
# below reproduce the 2026-07-20 environment. The current native PathMap<Par>
# treatment is capless and does not require an enlarged Rust thread stack.
# E-6d #2 final re-measurement (pgmcp experiment 149) — identical protocol to
# ../2026-07-19-e6a/run.sh, ../2026-07-19-e6a-postfix/run.sh and
# ../2026-07-20-e6d1/run.sh (33 reps/cell, first 3 warmups, deterministic
# seeds, pinned to CPUs 0-7), re-run against the FULL f1r3node-rust-mettail
# `fix/epathmap-value-handling` stack @ ead2f152 (P0 parity 602144bd; P1
# intern store c3d5b3f2; P2 chain fusion 351e494d; P3 hand-maintained EPathMap
# wrapper 4e422b6b; P4.1 Arc-shaped hot-store payloads 60aaa02e; P4.2 borrowed
# Matcher signature 6c0a90cb; P4.3 spliced event hashing ead2f152), all
# stacked on the trie-cache fix 84a0fbe4. Only OUT differs from the e6d1
# script. The primary COMM metric is counter-deterministic and MUST be
# identical to all three baseline runs; the treatment inj wall is the quantity
# under test (frozen gate: >=1.2x FURTHER improvement vs e6d1 on swap_comb
# n=16 AND nested_spine n=16). swap_comb 64's TREATMENT remains expected to
# DNF-by-machine-cap (the reducer trie-key arity cap — unrelated to, and
# untouched by, the fix stack).
#
# E-6d #1 LESSON (frozen into experiment 149): the machine MUST settle >=3
# minutes after the release build before the first measured cell (the e6d1
# swap_comb64-control +10.4% transient came from measuring 15-69 s
# post-build). The settle wait and run order are recorded in the run log.
set -u
cd "$(dirname "$0")/../../../../.."

DRIVER=target/release/bench_e6a_pathmap_driver
OUT=docs/benchmarks/data/sa-vs-naive/2026-07-20-e6d2/driver
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

echo "=== $(date -Is) E-6d #2 run complete"
