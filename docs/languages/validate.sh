#!/usr/bin/env bash
# Reproducible local validation for the Language Specification References suite.
#
# Mirrors the checks the architecture suites run (docs/architecture/*/validate.sh),
# scoped to this directory: math-delimiter conformance for GitHub-flavored Markdown,
# PlantUML source/asset integrity, link and anchor integrity, and roster coverage.
#
# Usage: docs/languages/validate.sh
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$script_dir/../.." && pwd)"
figures_dir="$script_dir/figures"
readme="$script_dir/README.md"

fail() {
  printf 'error: %s\n' "$*" >&2
  exit 1
}

require_tool() {
  command -v "$1" >/dev/null 2>&1 || fail "required tool not found: $1"
}

for tool in rg awk basename find plantuml sort wc; do
  require_tool "$tool"
done

shopt -s nullglob
suite_files=("$script_dir"/*.md)
shopt -u nullglob
[[ ${#suite_files[@]} -gt 0 ]] || fail "no Markdown pages found in $script_dir"
[[ -f "$readme" ]] || fail "missing suite index: $readme"

# ── 1. Fenced-block balance ──────────────────────────────────────────────────
printf 'checking fenced-code-block balance...\n'
for file in "${suite_files[@]}"; do
  awk -v f="$file" '
    /^[[:space:]]*```/ { n++ }
    END { if (n % 2 != 0) { print "unbalanced code fences in " f > "/dev/stderr"; exit 1 } }
  ' "$file" || fail "unbalanced code fences: $file"
done

# ── 2. Math symbols must live inside a code literal or a math span ───────────
printf 'checking math-symbol literal formatting...\n'
awk '
  /^[[:space:]]*```/ { in_fence = !in_fence; next }
  !in_fence && /[μΔρσ⊆⇒∀∃≈→∧∨∪∖∈≡⊗⊕]|0̄|₀|ᵢ|ᴰ|ᴿ/ && $0 !~ /`/ {
    print FILENAME ":" FNR ":" $0
    bad = 1
  }
  END { exit bad ? 1 : 0 }
' "${suite_files[@]}" || fail "math symbol outside code literal"

# ── 3. Math delimiter conformance ────────────────────────────────────────────
# Inline math must be the code-span-protected form  $`X`$  (dollar, backtick span,
# dollar); display math must be a ```math fenced block. Bare $X$ / $$…$$ are
# forbidden: GitHub's CommonMark pass strips backslash escapes before MathJax sees
# them, and a backtick-FIRST `$X$` renders as an inert code span.
printf 'checking math delimiter conformance (inline dollar-backtick form; no bare/double dollar)...\n'
awk '
  /^[[:space:]]*```/ { in_fence = !in_fence; next }
  !in_fence {
    line = $0
    gsub(/\$`[^`]+`\$/, "", line)
    gsub(/`[^`]*`/, "", line)
    if (line ~ /\$/) {
      print FILENAME ":" FNR ":" $0
      bad = 1
    }
  }
  END { exit bad ? 1 : 0 }
' "${suite_files[@]}" || fail "bare or double dollar math delimiter found (use the inline dollar-backtick form or a math fence)"

# ── 4. GitHub-unrenderable MathJax commands ──────────────────────────────────
printf 'checking GitHub-unrenderable MathJax commands (llbracket / rrbracket / char)...\n'
if rg -n '\\llbracket|\\rrbracket|\\char' "${suite_files[@]}"; then
  fail "GitHub-unrenderable MathJax command found — use the [\\![ .. ]\\!] reflection form and textasciicircum"
fi

# ── 5. PlantUML sources parse, and every source has a rendered SVG ───────────
printf 'checking PlantUML figure assets...\n'
[[ -d "$figures_dir" ]] || fail "missing figures directory: $figures_dir"
puml_count="$(find "$figures_dir" -type f -name '*.puml' | wc -l)"
[[ "$puml_count" -gt 0 ]] || fail "no PlantUML diagrams found in $figures_dir"
while IFS= read -r puml; do
  JAVA_TOOL_OPTIONS=-Djava.awt.headless=true plantuml -checkonly -failfast2 "$puml" >/dev/null
  figure_svg="${puml%.puml}.svg"
  [[ -s "$figure_svg" ]] || fail "missing or empty rendered SVG asset: $figure_svg (run: plantuml -tsvg $puml)"
  rg -q '<svg([[:space:]>])' "$figure_svg" || fail "rendered asset is missing an SVG root: $figure_svg"
  rg -q '</svg>' "$figure_svg" || fail "rendered asset is missing an SVG close tag: $figure_svg"
  if rg -q '&lt;#|&lt;&lt;#|&lt;back:' "$figure_svg"; then
    fail "rendered asset contains escaped PlantUML color markup: $figure_svg"
  fi
  if rg -q -i 'syntax error|cannot be parsed' "$figure_svg"; then
    fail "rendered asset is a PlantUML error image: $figure_svg"
  fi
done < <(find "$figures_dir" -type f -name '*.puml' | sort)

# ── 6. Relative links resolve; in-document anchors resolve ───────────────────
printf 'checking relative Markdown links...\n'
for file in "${suite_files[@]}"; do
  while IFS= read -r target; do
    case "$target" in
      http*|mailto:*) continue ;;
    esac
    target="${target%%#*}"          # drop any '#fragment' — the path is what must exist
    [[ -n "$target" ]] || continue  # pure in-document anchor: checked by the next pass
    [[ -e "$script_dir/$target" ]] || fail "broken relative link in $(basename -- "$file"): $target"
  done < <(rg -o '\]\(([^)#][^)]*)\)' -r '$1' "$file" | sort -u)
done

printf 'checking in-document anchors (GitHub slug rules)...\n'
for file in "${suite_files[@]}"; do
  awk -v f="$file" '
    function slug(text,   t) {
      t = tolower(text)
      gsub(/`/, "", t)
      gsub(/[^[:alnum:] _-]/, "", t)   # github-slugger: drop punctuation, KEEP spaces
      gsub(/ /, "-", t)                # each space becomes one hyphen (no collapsing)
      return t
    }
    /^```/ { in_fence = !in_fence }
    in_fence { next }
    /^#{2,6} / {
      line = $0
      sub(/^#+ /, "", line)
      heads[slug(line)] = 1
      next
    }
    {
      rest = $0
      while (match(rest, /\]\(#[^)]+\)/)) {
        anchor = substr(rest, RSTART + 3, RLENGTH - 4)
        anchors[anchor] = FNR
        rest = substr(rest, RSTART + RLENGTH)
      }
    }
    END {
      for (a in anchors)
        if (!(a in heads)) {
          print "unresolved anchor #" a " (" f ":" anchors[a] ")" > "/dev/stderr"
          bad = 1
        }
      exit bad ? 1 : 0
    }
  ' "$file" || fail "unresolved in-document anchor: $file"
done

# ── 7. Roster coverage: every page is listed in the suite index ──────────────
printf 'checking roster coverage (every page listed in README.md)...\n'
for file in "${suite_files[@]}"; do
  name="$(basename -- "$file")"
  [[ "$name" == "README.md" ]] && continue
  rg -q -F "($name)" "$readme" || fail "page not listed in the README roster: $name"
done

# ── 8. Every documented language page names an existing specification ────────
printf 'checking that each page names a live specification source...\n'
for file in "${suite_files[@]}"; do
  name="$(basename -- "$file")"
  [[ "$name" == "README.md" ]] && continue
  src="languages/src/${name%.md}.rs"
  [[ -f "$repo_root/$src" ]] || fail "page $name documents a missing specification: $src"
done

printf 'ok: languages suite validated (%d page(s), %d figure(s))\n' "${#suite_files[@]}" "$puml_count"
