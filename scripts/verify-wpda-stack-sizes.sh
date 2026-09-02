#!/usr/bin/env bash
set -euo pipefail

# Verify the native-stack budget of the generated Rholang WPDA dispatch.
#
# The parser's unbounded grammar stack lives in the heap-backed GSS.  A Rust
# transition call must therefore use a grammar-size-independent native frame.
# This gate reads rustc's ELF stack metadata and rejects any generated dispatch
# function above the budget.  The 256-KiB end-to-end tests remain the authority
# for the whole call chain; this script prevents a single generated frame from
# silently consuming most of that allowance.

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
budget_bytes="${WPDA_STACK_BUDGET_BYTES:-32768}"
stack_profile="${WPDA_STACK_PROFILE:-dev}"

case "$budget_bytes" in
  ''|*[!0-9]*)
    echo "WPDA_STACK_BUDGET_BYTES must be a positive integer" >&2
    exit 2
    ;;
esac
if (( budget_bytes == 0 )); then
  echo "WPDA_STACK_BUDGET_BYTES must be greater than zero" >&2
  exit 2
fi
case "$stack_profile" in
  dev|release) ;;
  *)
    echo "WPDA_STACK_PROFILE must be either dev or release" >&2
    exit 2
    ;;
esac

for tool in cargo jq llvm-readobj perl; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "required tool not found: $tool" >&2
    exit 2
  fi
done

artifact_log="$(mktemp)"
cargo_log="$(mktemp)"
stack_log="$(mktemp)"
all_sizes="$(mktemp)"
dispatch_sizes="$(mktemp)"
trap 'rm -f "$artifact_log" "$cargo_log" "$stack_log" "$all_sizes" "$dispatch_sizes"' EXIT

cd "$repo_root"
if ! RUSTFLAGS="${RUSTFLAGS:+${RUSTFLAGS} }-C target-cpu=native -Z emit-stack-sizes" \
  cargo test -p languages --no-default-features --features rholang \
    --test rholang_mettail_ddl --no-run \
    --profile "$stack_profile" --message-format=json-render-diagnostics \
    >"$artifact_log" 2>"$cargo_log"; then
  cat "$cargo_log" >&2
  exit 1
fi

binary="$({
  jq -r '
    select(.reason == "compiler-artifact")
    | select(.target.name == "rholang_mettail_ddl")
    | .executable // empty
  ' "$artifact_log"
} | tail -n 1)"

if [[ -z "$binary" || ! -x "$binary" ]]; then
  echo "could not locate the rholang_mettail_ddl test executable" >&2
  exit 1
fi

llvm-readobj --sections "$binary" | grep -q '\.stack_sizes' || {
  echo "rustc produced no .stack_sizes section for $binary" >&2
  exit 1
}
llvm-readobj --stack-sizes "$binary" >"$stack_log"

perl -ne '
  if (/Functions: \[([^\]]+)/) {
    $function = $1;
  } elsif (/Size: 0x([0-9A-Fa-f]+)/) {
    printf "%u\t%s\n", hex($1), $function if defined $function;
    undef $function;
  }
' "$stack_log" >"$all_sizes"

# The first term covers trait/inherent/local state handlers.  The remaining
# terms cover generated free-function grammar routers called by those handlers.
grep -E $'RholangWpdaEngine|lex_alt_rules_for_|__lex_alt_rules_for_|prefix_(arm|category|primary|crosscat|at_quoted)|binder_rule_|collection_(spec|loop)|mixfix_(part|parts|rep|nullary)|recovery_infra_for|infix_rules_for' \
  "$all_sizes" >"$dispatch_sizes" || true

matched_count="$(wc -l <"$dispatch_sizes")"
if (( matched_count < 10 )); then
  echo "stack metadata matched only $matched_count generated dispatch symbols" >&2
  exit 1
fi
for required in RholangWpdaEngine step_prefix_category binder_rule_dispatch __lex_alt_rules_for_prefix_chunk_; do
  grep -q "$required" "$dispatch_sizes" || {
    echo "required generated dispatch symbol missing from stack metadata: $required" >&2
    exit 1
  }
done

violations="$(awk -F '\t' -v budget="$budget_bytes" '$1 > budget { count += 1 } END { print count + 0 }' "$dispatch_sizes")"

echo "Largest generated Rholang WPDA dispatch frames (${stack_profile}, budget: ${budget_bytes} bytes):"
if command -v rustfilt >/dev/null 2>&1; then
  sort -nr "$dispatch_sizes" | sed -n '1,20p' | rustfilt
else
  sort -nr "$dispatch_sizes" | sed -n '1,20p'
fi

if (( violations > 0 )); then
  echo "$violations generated WPDA dispatch frame(s) exceed ${budget_bytes} bytes" >&2
  if command -v rustfilt >/dev/null 2>&1; then
    awk -F '\t' -v budget="$budget_bytes" '$1 > budget' "$dispatch_sizes" \
      | sort -nr | rustfilt >&2
  else
    awk -F '\t' -v budget="$budget_bytes" '$1 > budget' "$dispatch_sizes" \
      | sort -nr >&2
  fi
  exit 1
fi

echo "WPDA dispatch stack-size gate passed for $matched_count symbols."
