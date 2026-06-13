#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_docs_dir="$(cd -- "$script_dir/../.." && pwd)"
repo_root="$(cd -- "$repo_docs_dir/.." && pwd)"
figures_dir="$script_dir/figures"

fail() {
  printf 'error: %s\n' "$*" >&2
  exit 1
}

require_tool() {
  command -v "$1" >/dev/null 2>&1 || fail "required tool not found: $1"
}

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
require_tool dot
require_tool git

suite_files=("$script_dir"/*.md)
all_files=("${suite_files[@]}")

printf 'checking draft/proof-hole markers...\n'
if rg -n '\b(TODO|FIXME|TBD|placeholder|stub|hack|not implemented|unimplemented)\b|Axiom|Admitted\.' "${suite_files[@]}"; then
  fail "draft/proof-hole marker found"
fi

printf 'checking fenced block balance...\n'
for file in "${all_files[@]}"; do
  fence_count="$(rg -c '^```' "$file" || true)"
  fence_count="${fence_count:-0}"
  if (( fence_count % 2 != 0 )); then
    fail "unbalanced fenced code block in $file"
  fi
done

printf 'checking PlantUML figure assets...\n'
while IFS= read -r puml; do
  stem="${puml%.puml}"
  figure_svg="$stem.svg"
  JAVA_TOOL_OPTIONS=-Djava.awt.headless=true plantuml -checkonly -failfast2 "$puml" >/dev/null
  [[ -s "$figure_svg" ]] || fail "missing or empty rendered SVG asset: $figure_svg"
  rg -q '<svg([[:space:]>])' "$figure_svg" || fail "rendered asset is missing an SVG root: $figure_svg"
  rg -q '</svg>' "$figure_svg" || fail "rendered asset is missing an SVG close tag: $figure_svg"
done < <(find "$figures_dir" -type f -name '*.puml' | sort)

printf 'checking Graphviz figure assets...\n'
tmpdir="$(mktemp -d /tmp/dovetail-docs.XXXXXX)"
trap 'rm -rf "$tmpdir"' EXIT
while IFS= read -r dot_source; do
  name="$(basename -- "$dot_source")"
  stem="${name%.dot}"
  figure_svg="$figures_dir/$stem.svg"
  [[ -s "$figure_svg" ]] || fail "missing or empty rendered SVG asset: $figure_svg"
  rg -q '<svg([[:space:]>])' "$figure_svg" || fail "rendered asset is missing an SVG root: $figure_svg"
  rg -q '</svg>' "$figure_svg" || fail "rendered asset is missing an SVG close tag: $figure_svg"
  dot -Tsvg "$dot_source" -o "$tmpdir/$stem.svg"
done < <(find "$figures_dir" -type f -name '*.dot' | sort)

printf 'checking math-symbol literal formatting...\n'
awk '
  /^```/ { in_fence = !in_fence; next }
  !in_fence && /[⊆⇒∀∃≈→∧∨∪∖∈≡⊗⊕]|0̄|1̄|ᵢ|₀/ && $0 !~ /`/ {
    print FILENAME ":" FNR ":" $0
    bad = 1
  }
  END { exit bad ? 1 : 0 }
' "${suite_files[@]}" || fail "math symbol outside code literal"

printf 'checking relative Markdown links...\n'
link_errors=0
while IFS=: read -r file line match; do
  target="$(printf '%s' "$match" | sed -E 's/.*\]\(([^)#]+)(#[^)]+)?\).*/\1/')"
  case "$target" in
    http*) continue ;;
    /*) path="$target" ;;
    *) path="$(dirname -- "$file")/$target" ;;
  esac
  if [[ ! -e "$path" ]]; then
    printf 'missing %s:%s -> %s (%s)\n' "$file" "$line" "$target" "$path" >&2
    link_errors=1
  fi
done < <(rg -n -o '\[[^]]+\]\([^)]*\.(md|puml|dot|svg)[^)]*\)' "${all_files[@]}")
if (( link_errors != 0 )); then
  fail "relative Markdown link check failed"
fi

printf 'checking referenced local paths...\n'
path_errors=0
while IFS= read -r rel_path; do
  [[ -n "$rel_path" ]] || continue
  check_path="$repo_root/$rel_path"
  if [[ ! -e "$check_path" ]]; then
    printf 'missing referenced path: %s (%s)\n' "$rel_path" "$check_path" >&2
    path_errors=1
  fi
done < <(awk '
  /^- `/ {
    line = $0
    sub(/^- `/, "", line)
    sub(/`.*/, "", line)
    print line
  }
' "$script_dir/references.md")
if (( path_errors != 0 )); then
  fail "referenced local path check failed"
fi

printf 'checking whitespace with git diff --check...\n'
git -C "$repo_root" diff --check -- docs/architecture/dovetail docs/README.md docs/architecture.md

printf 'dovetail documentation validation passed.\n'
