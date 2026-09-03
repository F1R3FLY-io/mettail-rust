#!/usr/bin/env bash
set -euo pipefail

demo_repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$demo_repo_root"

demo_evidence_dir="$demo_repo_root/target/campaign-evidence/registry-module-demo"
demo_formal_tmp="$demo_evidence_dir/formal-tmp"
demo_formal_cargo_target="$demo_evidence_dir/formal-cargo-target"
mkdir -p "$demo_evidence_dir" "$demo_formal_tmp" "$demo_formal_cargo_target"

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"
export CARGO_INCREMENTAL="${CARGO_INCREMENTAL:-0}"

run_and_capture() {
  local log_name="$1"
  shift
  "$@" 2>&1 | tee "$demo_evidence_dir/$log_name"
}

run_and_capture application.log \
  cargo test -p rholang-runtime --test inline_ddl_demo --features rholang-runtime \
    committed_registry_application_installs_one_exact_multi_export_snapshot -- --nocapture

run_and_capture canonical-graph.log \
  cargo test -p mettail-elab --lib resolve::tests

run_and_capture registry-installation.log \
  cargo test -p rholang-runtime language_install::tests --lib --features rholang-runtime

run_and_capture lexical-alias-capability.log \
  cargo test -p mettail-grammar-core aliases_are_lexical_capability_bindings_not_fingerprint_lookups

run_and_capture formal.log \
  make -C formal check-capped \
    FORMAL_CAPPED_TARGET=rocq-runtime-grammar \
    FORMAL_MEMORY_MAX_BYTES=536870912 \
    FORMAL_MEMORY_HIGH_BYTES=469762048 \
    FORMAL_TMPDIR="$demo_formal_tmp" \
    FORMAL_CARGO_TARGET_DIR="$demo_formal_cargo_target"

run_and_capture diff-check.log \
  git -c core.fsmonitor=false diff --check
