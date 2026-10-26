#!/usr/bin/env bash
set -euo pipefail

project_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
output_dir=${1:-"$project_dir/../../../target/formal/rewrite-family"}
coqc_bin=${COQC:-coqc}
coqchk_bin=${COQCHK:-coqchk}
models=(RewriteFamilyNormalization RewriteFamilyExtraction RewriteFamilyPremises RewriteFamilyBoundary RewriteFamilyAuthored RewriteFamilyFocus RewriteFamilyNames RewriteFamilyAllocator RewriteFamilyAdapterRefinements RewriteFamilyContext RewriteContextSourceNames RewriteContextWireProjection RewriteContextTokenExtension RewriteFamilyDescriptors RootActivationProjection)
args=(-Q Dovetail Dovetail -Q RuntimeGrammar RuntimeGrammar)
mkdir -p -- "$output_dir/Dovetail/Requirements" "$output_dir/Dovetail/Lowering" "$output_dir/RuntimeGrammar"
cp -- "$project_dir/../../../dovetail/formal/rocq/theories/Requirements/MeTTaILRewriteCoverage.v" "$output_dir/Dovetail/Requirements/MeTTaILRewriteCoverage.v"
cp -- "$project_dir/../../../dovetail/formal/rocq/theories/Lowering/CollectionAcLowering.v" "$output_dir/Dovetail/Lowering/CollectionAcLowering.v"
cp -- "$project_dir/../runtime_grammar/theories/CollectionComprehension.v" "$output_dir/RuntimeGrammar/CollectionComprehension.v"
cp -- "$project_dir/../runtime_grammar/theories/SemanticTransitionKernel.v" "$output_dir/RuntimeGrammar/SemanticTransitionKernel.v"
cp -- "$project_dir/../prattail_wpda_runtime/theories/TermParamReaderProjection.v" "$output_dir/TermParamReaderProjection.v"
cp -- "$project_dir/../prattail_wpda_runtime/theories/LexForkKeywordReservation.v" "$output_dir/LexForkKeywordReservation.v"
for model in "${models[@]}"; do
  cp -- "$project_dir/theories/$model.v" "$output_dir/$model.v"
done
cd -- "$output_dir"
"$coqc_bin" "${args[@]}" Dovetail/Requirements/MeTTaILRewriteCoverage.v > requirements.compile.log 2>&1
"$coqc_bin" "${args[@]}" Dovetail/Lowering/CollectionAcLowering.v > collections.compile.log 2>&1
"$coqc_bin" "${args[@]}" RuntimeGrammar/CollectionComprehension.v > comprehension.compile.log 2>&1
"$coqc_bin" "${args[@]}" RuntimeGrammar/SemanticTransitionKernel.v > transition.compile.log 2>&1
"$coqc_bin" LexForkKeywordReservation.v > LexForkKeywordReservation.compile.log 2>&1
"$coqc_bin" TermParamReaderProjection.v > TermParamReaderProjection.compile.log 2>&1
for model in "${models[@]}"; do
  "$coqc_bin" "${args[@]}" "$model.v" > "$model.compile.log" 2>&1
  theorem_count=$(rg -c '^Theorem ' "$model.v")
  assumption_count=$(rg -c '^Closed under the global context$' "$model.compile.log")
  [[ "$theorem_count" -eq "$assumption_count" ]]
done
"$coqchk_bin" "${args[@]}" -silent "${models[@]}" > kernel.log 2>&1
bash "$project_dir/extract-properties.sh" "$PWD"
sha256sum -- TermParamReaderProjection.v LexForkKeywordReservation.v "${models[@]/%/.v}" RuntimeGrammar/*.v Dovetail/*/*.v > verified-sources.sha256
printf 'success\n' > result.txt
