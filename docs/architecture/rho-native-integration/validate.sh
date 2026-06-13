#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_docs_dir="$(cd -- "$script_dir/../.." && pwd)"
repo_root="$(cd -- "$repo_docs_dir/.." && pwd)"
figures_dir="$script_dir/figures"
online=0

case "${1:-}" in
  "") ;;
  "--online") online=1 ;;
  *)
    printf 'usage: %s [--online]\n' "$0" >&2
    exit 2
    ;;
esac

suite_files=("$script_dir"/*.md)
root_readme="$repo_root/README.md"
root_index="$repo_docs_dir/README.md"
architecture_overview="$repo_docs_dir/architecture.md"
all_files=("${suite_files[@]}" "$root_readme" "$root_index" "$architecture_overview")

fail() {
  printf 'error: %s\n' "$*" >&2
  exit 1
}

require_tool() {
  command -v "$1" >/dev/null 2>&1 || fail "required tool not found: $1"
}

require_tool rg
require_tool awk
require_tool sed
require_tool basename
require_tool cmp
require_tool dirname
require_tool find
require_tool mktemp
require_tool rm
require_tool sort
require_tool wc
require_tool plantuml
require_tool dot
require_tool git

anchor_exists() {
  local file="$1"
  local fragment="$2"
  awk -v want="$fragment" '
    function slug(text) {
      text = tolower(text)
      gsub(/`/, "", text)
      gsub(/<[^>]*>/, "", text)
      gsub(/&[a-z]+;/, "", text)
      gsub(/[^[:alnum:] _-]/, "", text)
      gsub(/[[:space:]]+/, "-", text)
      gsub(/^-+/, "", text)
      gsub(/-+$/, "", text)
      return text
    }
    /^#{1,6}[[:space:]]+/ {
      heading = $0
      sub(/^#{1,6}[[:space:]]+/, "", heading)
      sub(/[[:space:]]+#+[[:space:]]*$/, "", heading)
      if (slug(heading) == want) {
        found = 1
      }
    }
    END { exit found ? 0 : 1 }
  ' "$file"
}

printf 'checking draft/proof-hole markers...\n'
if rg -n '\b(TODO|FIXME|TBD|placeholder|stub|hack|temporary|deferred|future work|not implemented|not yet|pending|unimplemented|maybe|probably)\b|I think|Conjecture|Axiom|Admitted\.' "${suite_files[@]}"; then
  fail "draft/proof-hole marker found"
fi

printf 'checking index incompletion markers...\n'
if rg -n -i '\b(TODO|FIXME|TBD|placeholder|stub|hack|temporary|deferred|future work|not implemented|not yet|pending|unimplemented|maybe|probably|pragmatic|technical debt)\b|I think' "$root_readme" "$root_index" "$architecture_overview"; then
  fail "index incompletion marker found"
fi

printf 'checking fenced block balance...\n'
for file in "${all_files[@]}"; do
  fence_count="$(rg -c '^```' "$file" || true)"
  fence_count="${fence_count:-0}"
  if (( fence_count % 2 != 0 )); then
    fail "unbalanced fenced code block in $file"
  fi
done

printf 'checking PlantUML marker balance...\n'
for file in "${suite_files[@]}"; do
  starts="$(rg -c '@startuml' "$file" || true)"
  ends="$(rg -c '@enduml' "$file" || true)"
  starts="${starts:-0}"
  ends="${ends:-0}"
  if [[ "$starts" != "$ends" ]]; then
    fail "PlantUML marker mismatch in $file: start=$starts end=$ends"
  fi
done

printf 'checking PlantUML syntax...\n'
tmpdir="$(mktemp -d /tmp/rho-native-puml.XXXXXX)"
trap 'rm -rf "$tmpdir"' EXIT
for file in "${suite_files[@]}"; do
  base="$(basename -- "$file")"
  base="${base%.md}"
  awk -v dir="$tmpdir" -v base="$base" -v file="$file" '
    /^```plantuml$/ {
      inside = 1
      n++
      if (n > 1) {
        print "multiple PlantUML blocks in " file > "/dev/stderr"
        exit 3
      }
      out = dir "/" base ".puml"
      next
    }
    /^```$/ && inside { inside = 0; close(out); next }
    inside { print > out }
  ' "$file"
done
puml_count="$(find "$tmpdir" -type f -name '*.puml' | wc -l)"
figure_puml_count="$(find "$figures_dir" -type f -name '*.puml' | wc -l)"
if [[ "$figure_puml_count" == "0" ]]; then
  fail "no PlantUML diagrams found"
fi
while IFS= read -r puml; do
  JAVA_TOOL_OPTIONS=-Djava.awt.headless=true plantuml -checkonly -failfast2 "$puml" >/dev/null
done < <(find "$tmpdir" -type f -name '*.puml' | sort)

printf 'checking rendered PlantUML assets...\n'
while IFS= read -r puml; do
  name="$(basename -- "$puml")"
  stem="${name%.puml}"
  figure_puml="$figures_dir/$name"
  figure_svg="$figures_dir/$stem.svg"
  [[ -f "$figure_puml" ]] || fail "missing PlantUML source asset: $figure_puml"
  [[ -s "$figure_svg" ]] || fail "missing or empty rendered SVG asset: $figure_svg"
  rg -q '<svg([[:space:]>])' "$figure_svg" || fail "rendered asset is missing an SVG root: $figure_svg"
  rg -q '</svg>' "$figure_svg" || fail "rendered asset is missing an SVG close tag: $figure_svg"
  cmp -s "$puml" "$figure_puml" || fail "PlantUML fence differs from figure source: $figure_puml"
done < <(find "$tmpdir" -type f -name '*.puml' | sort)

printf 'checking standalone PlantUML figure assets...\n'
while IFS= read -r puml; do
  stem="${puml%.puml}"
  figure_svg="$stem.svg"
  JAVA_TOOL_OPTIONS=-Djava.awt.headless=true plantuml -checkonly -failfast2 "$puml" >/dev/null
  [[ -s "$figure_svg" ]] || fail "missing or empty rendered SVG asset: $figure_svg"
  rg -q '<svg([[:space:]>])' "$figure_svg" || fail "rendered asset is missing an SVG root: $figure_svg"
  rg -q '</svg>' "$figure_svg" || fail "rendered asset is missing an SVG close tag: $figure_svg"
done < <(find "$figures_dir" -type f -name '*.puml' | sort)

printf 'checking rendered Graphviz DOT assets...\n'
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
  !in_fence && /[μΔρσ⊆⇒∀∃≈→∧∨∪∖∈≡⊗⊕]|0̄|₀|ᵢ|ᴰ|ᴿ/ && $0 !~ /`/ {
    print FILENAME ":" FNR ":" $0
    bad = 1
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
    printf 'missing %s:%s -> %s (%s)\n' "$file" "$line" "$target" "$path" >&2
    link_errors=1
  elif [[ -n "$fragment" && "$target" == *.md ]]; then
    if ! anchor_exists "$path" "$fragment"; then
      printf 'missing anchor %s:%s -> %s#%s\n' "$file" "$line" "$target" "$fragment" >&2
      link_errors=1
    fi
  fi
done < <(rg -n -o '\[[^]]+\]\([^)]*\.(md|puml|dot|svg)[^)]*\)' "${all_files[@]}")
if (( link_errors != 0 )); then
  fail "relative Markdown link check failed"
fi

printf 'checking bibliography local paths...\n'
path_errors=0
while IFS= read -r rel_path; do
  [[ -n "$rel_path" ]] || continue
  case "$rel_path" in
    /*) check_path="$rel_path" ;;
    *) check_path="$repo_root/$rel_path" ;;
  esac
  if [[ ! -e "$check_path" ]]; then
    printf 'missing bibliography path: %s (%s)\n' "$rel_path" "$check_path" >&2
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
  fail "bibliography local path check failed"
fi

if (( online != 0 )); then
  require_tool curl
  require_tool sleep
  printf 'checking external bibliography links...\n'
  external_errors=0
  while IFS= read -r url; do
    case "$url" in
      https://doi.org/*)
        doi="${url#https://doi.org/}"
        code="$(curl -A 'mettail-rust-doc-validation/1.0' -s -o /dev/null -w '%{http_code}' --max-time 20 "https://api.crossref.org/works/$doi" || true)"
        if [[ "$code" == "429" ]]; then
          sleep 2
          code="$(curl -A 'mettail-rust-doc-validation/1.0' -s -o /dev/null -w '%{http_code}' --max-time 20 "https://api.crossref.org/works/$doi" || true)"
        fi
        ;;
      *)
        code="$(curl -A 'mettail-rust-doc-validation/1.0' -L -s -o /dev/null -w '%{http_code}' --max-time 20 "$url" || true)"
        ;;
    esac
    if [[ ! "$code" =~ ^2[0-9][0-9]$ ]]; then
      printf 'external link failed: http=%s %s\n' "$code" "$url" >&2
      external_errors=1
    fi
  done < <(rg -o 'https?://[^) ]+' "$script_dir/references.md" | sort -u)
  if (( external_errors != 0 )); then
    fail "external bibliography link check failed"
  fi
fi

printf 'checking whitespace with git diff --check...\n'
git -C "$repo_root" diff --check -- README.md docs/README.md docs/architecture.md docs/architecture/rho-native-integration

printf 'rho-native integration documentation validation passed (%s PlantUML figure assets, %s embedded blocks).\n' "$figure_puml_count" "$puml_count"
