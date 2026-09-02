#!/usr/bin/env bash
set -euo pipefail

demo_repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$demo_repo_root"

demo_evidence_dir="$demo_repo_root/target/campaign-evidence/inline-ddl-demo"
mkdir -p "$demo_evidence_dir"

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"
export CARGO_INCREMENTAL="${CARGO_INCREMENTAL:-0}"

run_and_capture() {
  local log_name="$1"
  shift
  "$@" 2>&1 | tee "$demo_evidence_dir/$log_name"
}

run_and_capture application.log \
  cargo test -p rholang-runtime --test inline_ddl_demo -- --nocapture

run_and_capture runtime-security-resource.log \
  cargo test -p rholang-runtime language_install::tests --lib

run_and_capture reserved-band.log \
  cargo test -p rholang-codegen system_process_band --lib

run_and_capture formal.log \
  make -C formal check-capped \
    FORMAL_CAPPED_TARGET=rocq-runtime-grammar \
    FORMAL_MEMORY_MAX_BYTES=536870912 \
    FORMAL_MEMORY_HIGH_BYTES=469762048

run_and_capture diff-check.log \
  git -c core.fsmonitor=false diff --check
