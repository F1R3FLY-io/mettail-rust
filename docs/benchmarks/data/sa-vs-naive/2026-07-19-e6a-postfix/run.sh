#!/usr/bin/env bash
# HISTORICAL PROTOCOL ONLY: the cap/DNF expectation and RUST_MIN_STACK setting
# below reproduce the 2026-07-19 environment. The current native PathMap<Par>
# treatment is capless and does not require an enlarged Rust thread stack.
# E-6a POST-FIX re-measurement — identical protocol to ../2026-07-19-e6a/run.sh
# (33 reps/cell, first 3 warmups, deterministic seeds, pinned to CPUs 0-7),
# re-run after the f1r3node-rust-mettail `fix/epathmap-trie-cache` fix
# (EPathMap→trie conversion memoized + native prefix descent for the zipper
# query methods; commit 84a0fbe4 stacked on 31b354e6). Only OUT differs from
# the pre-fix script. The primary COMM metric is counter-deterministic and
# MUST be identical to the pre-fix run; the treatment inj wall is the quantity
# under test. swap_comb 64's TREATMENT remains expected to DNF-by-machine-cap
# (the reducer trie-key arity cap — unrelated to, and untouched by, the fix).
set -u
cd "$(dirname "$0")/../../../../.."

DRIVER=target/release/bench_e6a_pathmap_driver
OUT=docs/benchmarks/data/sa-vs-naive/2026-07-19-e6a-postfix/driver
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

echo "=== $(date -Is) E-6a post-fix run complete"
