#!/usr/bin/env bash
set -euo pipefail

# Documentation validation for the semantic-predicate symbolic-algebra suite.
# Mirrors the dovetail/ and rho-native-integration/ flagship validators:
# draft-marker ban, fenced-block balance, PlantUML figure rendering + asset
# integrity, math-in-backticks, relative-link resolution, bibliography local
# paths, optional online DOI/link checks, and whitespace.
#
# NOTE on the marker ban: this suite's `10-formal-verification-and-tests.md`
# must NAME the tokens the zero-admission gate scans for (`Axiom`, `Conjecture`,
# `Admitted.`) to explain that gate, so those proof keywords are deliberately
# NOT in the marker ban here. Every doc-incompleteness marker (TODO, FIXME,
# placeholder, stub, deferred, pending, …) IS banned, exactly as in the
# flagship suites.

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_docs_dir="$(cd -- "$script_dir/../.." && pwd)"
repo_root="$(cd -- "$repo_docs_dir/.." && pwd)"
figures_dir="$script_dir/figures"
online=0

case "${1:-}" in
  "") ;;
  "--online") online=1 ;;
  *) printf 'usage: %s [--online]\n' "$0" >&2; exit 2 ;;
esac

suite_files=("$script_dir"/*.md)
root_index="$repo_docs_dir/README.md"
architecture_overview="$repo_docs_dir/architecture.md"
all_files=("${suite_files[@]}" "$root_index" "$architecture_overview")

fail() { printf 'error: %s\n' "$*" >&2; exit 1; }
require_tool() { command -v "$1" >/dev/null 2>&1 || fail "required tool not found: $1"; }

require_tool rg
require_tool awk
require_tool basename
require_tool dirname
require_tool find
require_tool mktemp
require_tool rm
require_tool sort
require_tool wc
require_tool plantuml
require_tool git

anchor_exists() {
  local file="$1" fragment="$2"
  awk -v want="$fragment" '
    function slug(text) {
      text = tolower(text); gsub(/`/, "", text); gsub(/<[^>]*>/, "", text)
      gsub(/&[a-z]+;/, "", text); gsub(/[^[:alnum:] _-]/, "", text)
      gsub(/[[:space:]]+/, "-", text); gsub(/^-+/, "", text); gsub(/-+$/, "", text)
      return text
    }
    /^#{1,6}[[:space:]]+/ {
      h = $0; sub(/^#{1,6}[[:space:]]+/, "", h); sub(/[[:space:]]+#+[[:space:]]*$/, "", h)
      if (slug(h) == want) found = 1
    }
    END { exit found ? 0 : 1 }
  ' "$file"
}

printf 'checking draft/proof-hole markers...\n'
if rg -n '\b(TODO|FIXME|TBD|placeholder|stub|hack|temporary|deferred|future work|not implemented|not yet|pending|unimplemented|maybe|probably)\b|I think' "${suite_files[@]}"; then
  fail "draft/incompleteness marker found"
fi

printf 'checking index incompletion markers...\n'
if rg -n -i '\b(TODO|FIXME|TBD|placeholder|stub|hack|temporary|deferred|future work|not implemented|not yet|pending|unimplemented|pragmatic|technical debt)\b|I think' "$root_index" "$architecture_overview"; then
  fail "index incompletion marker found"
fi

printf 'checking fenced block balance...\n'
for file in "${all_files[@]}"; do
  fence_count="$(rg -c '^```' "$file" || true)"; fence_count="${fence_count:-0}"
  (( fence_count % 2 == 0 )) || fail "unbalanced fenced code block in $file"
done

printf 'checking standalone PlantUML figure assets...\n'
figure_puml_count="$(find "$figures_dir" -type f -name '*.puml' 2>/dev/null | wc -l)"
[[ "$figure_puml_count" == "0" ]] && fail "no PlantUML figures found"
while IFS= read -r puml; do
  stem="${puml%.puml}"; figure_svg="$stem.svg"
  JAVA_TOOL_OPTIONS=-Djava.awt.headless=true plantuml -checkonly -failfast2 "$puml" >/dev/null
  [[ -s "$figure_svg" ]] || fail "missing or empty rendered SVG asset: $figure_svg"
  rg -q '<svg([[:space:]>])' "$figure_svg" || fail "rendered asset is missing an SVG root: $figure_svg"
  rg -q '</svg>' "$figure_svg" || fail "rendered asset is missing an SVG close tag: $figure_svg"
  if rg -q '&lt;#|&lt;&lt;#|&lt;back:' "$figure_svg"; then
    fail "rendered asset contains escaped PlantUML color markup: $figure_svg"
  fi
done < <(find "$figures_dir" -type f -name '*.puml' | sort)

printf 'checking that every embedded figure reference has an asset...\n'
while IFS= read -r svg_ref; do
  [[ -f "$figures_dir/$(basename "$svg_ref")" ]] || fail "referenced figure asset missing: $svg_ref"
done < <(rg -o --no-filename 'figures/[A-Za-z0-9_-]+\.svg' "${suite_files[@]}" | sort -u)

printf 'checking math-symbol literal formatting...\n'
# Track fenced code blocks, including blockquoted fences (`> ```...`), since this
# suite presents literate pseudocode inside blockquotes.
awk '
  /^[[:space:]>]*```/ { in_fence = !in_fence; next }
  !in_fence && /[⊆⊇⊂⊃⇒⇐⟹⟸⟺∀∃≈→∧∨∪∩∖∈∉≡⊗⊕⊨⊤⊥∅≤≥≠]|0̄|₀|ᵢ/ && $0 !~ /`/ {
    print FILENAME ":" FNR ":" $0; bad = 1
  }
  END { exit bad ? 1 : 0 }
' "${suite_files[@]}" || fail "math symbol outside code literal"

printf 'checking relative Markdown links...\n'
link_errors=0
while IFS=: read -r file line match; do
  target="$(printf '%s' "$match" | sed -E 's/.*\]\(([^)#]+)(#[^)]+)?\).*/\1/')"
  fragment="$(printf '%s' "$match" | sed -nE 's/.*\]\([^)#]+#([^)]+)\).*/\1/p')"
  case "$target" in
    http*) continue ;;
    /*) path="$target" ;;
    *) path="$(dirname -- "$file")/$target" ;;
  esac
  if [[ ! -e "$path" ]]; then
    printf 'missing %s:%s -> %s (%s)\n' "$file" "$line" "$target" "$path" >&2; link_errors=1
  elif [[ -n "$fragment" && "$target" == *.md ]]; then
    if ! anchor_exists "$path" "$fragment"; then
      printf 'missing anchor %s:%s -> %s#%s\n' "$file" "$line" "$target" "$fragment" >&2; link_errors=1
    fi
  fi
done < <(rg -n -o '\[[^]]+\]\([^)]*\.(md|puml|svg)[^)]*\)' "${all_files[@]}")
(( link_errors == 0 )) || fail "relative Markdown link check failed"

printf 'checking bibliography local paths...\n'
path_errors=0
while IFS= read -r rel_path; do
  [[ -n "$rel_path" ]] || continue
  case "$rel_path" in /*) check_path="$rel_path" ;; *) check_path="$repo_root/$rel_path" ;; esac
  [[ -e "$check_path" ]] || { printf 'missing bibliography path: %s\n' "$rel_path" >&2; path_errors=1; }
done < <(awk '/^- `/ { l=$0; sub(/^- `/,"",l); sub(/`.*/,"",l); print l }' "$script_dir/references.md")
(( path_errors == 0 )) || fail "bibliography local path check failed"

if (( online != 0 )); then
  require_tool curl
  printf 'checking external bibliography links...\n'
  external_errors=0
  while IFS= read -r url; do
    case "$url" in
      https://doi.org/*)
        doi="${url#https://doi.org/}"
        code="$(curl -A 'mettail-doc-validation/1.0' -s -o /dev/null -w '%{http_code}' --max-time 25 "https://api.crossref.org/works/$doi" || true)"
        ;;
      *)
        code="$(curl -A 'mettail-doc-validation/1.0' -L -s -o /dev/null -w '%{http_code}' --max-time 25 "$url" || true)"
        ;;
    esac
    [[ "$code" =~ ^2[0-9][0-9]$ ]] || { printf 'external link failed: http=%s %s\n' "$code" "$url" >&2; external_errors=1; }
  done < <(rg -o 'https?://[^) ]+' "$script_dir/references.md" | sort -u)
  (( external_errors == 0 )) || fail "external bibliography link check failed"
fi

printf 'checking whitespace with git diff --check...\n'
git -C "$repo_root" diff --check -- docs/architecture/symbolic-predicates docs/README.md docs/architecture.md

printf 'symbolic-predicates documentation validation passed (%s PlantUML figure assets).\n' "$figure_puml_count"
