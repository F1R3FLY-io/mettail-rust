#!/usr/bin/env bash
# Reproducible local validation for the Language Specification References suite.
#
# This is the suite's acceptance gate against the pgmcp documentation guidelines
# (26 items in 7 categories; the canonical text is the `documentation_guidelines`
# MCP tool / `pgmcp:src/docguidelines/`). A guideline nobody checks is a guideline
# that silently rots, and this suite has already demonstrated that failure mode:
# all four of lambda.md's SVGs sat on disk at zero bytes while their .puml sources
# had real content. Check 6 below would have caught it. It had never been run.
#
# Every check reports its own name and one of PASS / FAIL / SKIP, and every
# verdict is taken from an EXIT CODE, never from grepped stdout. That rule is not
# decoration: `rustfmt` with a non-empty ignore list exits 101 while printing
# nothing at all, so a `| grep -c '^Diff in'` gate in this repo once scored a
# crash as CLEAN. Nothing here reads a tool's prose to decide anything.
#
# The run does not abort at the first failure — every check runs, and the script
# exits non-zero at the end if any of them failed. SKIP is not a failure; it
# means the check could not run here (no network, no word list, no rustfmt) and
# says so.
#
# Guideline coverage
# ─────────────────────────────────────────────────────────────────────────────
#   1  fences-balanced                 structural precondition for every fence check
#   2  math-symbol-literals            math-mathjax
#   3  math-delimiters                 math-delimiters
#   4  math-github-renderable          math-delimiters
#   5  math-backticks                  math-backticks           (inert code spans)
#   6  diagrams-plantuml-assets        diagrams-prefer-plantuml, diagrams-complete
#   7  diagrams-plenty                 diagrams-plenty
#   8  diagrams-fully-colored          diagrams-fully-colored
#   9  links-relative                  doc-placement, pedagogy-logical-flow
#  10  anchors-in-document             pedagogy-logical-flow
#  11  citations-exist + -doi-links    citations-exist, citations-doi-links
#  12  citations-doi-valid             citations-doi-valid      (network, OPTIONAL)
#  13  pedagogy-define-terms           pedagogy-define-terms
#  14  algorithms-literate-pseudocode  algorithms-literate-pseudocode
#  15  code-snippets-valid             code-snippets-valid
#  16  roster-coverage                 doc-naming-structure
#  17  live-spec-source                coverage-semantics
#
# The remaining guidelines are editorial judgements (coverage-doc-types,
# diagrams-best-types, diagrams-best-actors, pedagogy-intuition-rationale, …) and
# are reviewed by hand; they are not silently assumed to hold.
#
# Usage:
#   docs/languages/validate.sh [EXTRA.md ...]
#
# Positional arguments are Markdown files OUTSIDE this suite that should also be
# held to the document-level checks (2-5, 11-15). Suite-level checks (roster,
# specification source, figure inventory) never apply to them. Example:
#
#   docs/languages/validate.sh docs/design/exploring/lookahead-traces-as-a-pathmap.md
#
# Environment:
#   DOCLINT_DOI=auto|on|off   DOI resolution: attempt and skip if doi.org is
#                             unreachable (default) / require it / never attempt.
#   DOCLINT_WORDLIST=PATH     word list for the acronym check.
set -uo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "$script_dir/../.." && pwd)"
figures_dir="$script_dir/figures"
readme="$script_dir/README.md"
doclint="$script_dir/doclint.py"

failures=0
skips=0
tool_errors=0
checks_run=0
checks_passed=0

# Never leave a __pycache__ beside the pages being audited: a tool that drops
# bytecode into the directory it inspects is a tool whose droppings eventually
# get committed by someone else.
export PYTHONDONTWRITEBYTECODE=1

fail() {
  printf 'error: %s\n' "$*" >&2
  exit 1
}

require_tool() {
  command -v "$1" >/dev/null 2>&1 || fail "required tool not found: $1"
}

for tool in rg awk basename find plantuml python3 sort wc; do
  require_tool "$tool"
done

[[ -f "$doclint" ]] || fail "missing checker module: $doclint"

# run_check SLUG COMMAND...  — the ONLY place a verdict is decided, and it is
# decided on $?. Output is echoed for the operator; it is never parsed.
#
# Four states, mirroring scripts/check-fmt.sh in the sibling f1r3node-rust-mettail
# workspace rather than inventing a second convention:
#
#   0  PASS   the check ran and found nothing
#   1  FAIL   the check ran and found violations
#   2  ERROR  the check itself broke — the pages are UNCHECKED, not clean
#   3  SKIP   the check could not run here and said why
#
# ★ ERROR is counted as a failure and printed differently from FAIL, because the
# two demand different responses: FAIL means "fix the document", ERROR means
# "the answer is unknown". Any other exit code is also ERROR — an unrecognised
# status is by definition not a clean bill of health. This is the shape of the
# rustfmt-exits-101-with-no-stdout defect, refused here by construction.
run_check() {
  local slug="$1"
  shift
  local out rc=0
  checks_run=$((checks_run + 1))
  out="$("$@" 2>&1)" || rc=$?
  if [[ -n "$out" ]]; then
    printf '%s\n' "$out" | sed 's/^/       /'
  fi
  case "$rc" in
    0) printf '  PASS  %s\n' "$slug"; checks_passed=$((checks_passed + 1)) ;;
    1) printf '  FAIL  %s\n' "$slug"; failures=$((failures + 1)) ;;
    3) printf '  SKIP  %s  (not verified — a skip is not a pass)\n' "$slug"
       skips=$((skips + 1)) ;;
    *) printf '  ERROR %s  (checker exited %d; these pages are UNCHECKED)\n' "$slug" "$rc"
       tool_errors=$((tool_errors + 1)); failures=$((failures + 1)) ;;
  esac
}

shopt -s nullglob
suite_files=("$script_dir"/*.md)
shopt -u nullglob
[[ ${#suite_files[@]} -gt 0 ]] || fail "no Markdown pages found in $script_dir"
[[ -f "$readme" ]] || fail "missing suite index: $readme"

# Extra pages: document-level checks only.
extra_files=()
for argument in "$@"; do
  [[ -f "$argument" ]] || fail "extra page not found: $argument"
  extra_files+=("$argument")
done
document_files=("${suite_files[@]}" "${extra_files[@]}")

# ── 1. Fenced-block balance ──────────────────────────────────────────────────
check_fences() {
  local rc=0 file
  for file in "${document_files[@]}"; do
    awk -v f="$file" '
      /^[[:space:]]*```/ { n++ }
      END { if (n % 2 != 0) { print "unbalanced code fences in " f > "/dev/stderr"; exit 1 } }
    ' "$file" || rc=1
  done
  return $rc
}
run_check "fences-balanced" check_fences

# ── 2. Math symbols must live inside a code literal or a math span ───────────
check_math_symbols() {
  awk '
    /^[[:space:]]*```/ { in_fence = !in_fence; next }
    !in_fence && /[μΔρσ⊆⇒∀∃≈→∧∨∪∖∈≡⊗⊕]|0̄|₀|ᵢ|ᴰ|ᴿ/ && $0 !~ /`/ {
      print FILENAME ":" FNR ":" $0
      bad = 1
    }
    END { exit bad ? 1 : 0 }
  ' "${document_files[@]}"
}
run_check "math-symbol-literals" check_math_symbols

# ── 3. Math delimiter conformance ────────────────────────────────────────────
# Inline math must be the code-span-protected form  $`X`$  (dollar, backtick span,
# dollar); display math must be a ```math fenced block. Bare $X$ / $$…$$ are
# forbidden: GitHub's CommonMark pass strips backslash escapes before MathJax sees
# them, and a backtick-FIRST `$X$` renders as an inert code span.
check_math_delimiters() {
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
  ' "${document_files[@]}"
}
run_check "math-delimiters" check_math_delimiters

# ── 4. GitHub-unrenderable MathJax commands ──────────────────────────────────
check_mathjax_commands() {
  if rg -n '\\llbracket|\\rrbracket|\\char' "${document_files[@]}"; then
    printf 'use the [\\![ .. ]\\!] reflection form and \\textasciicircum instead\n' >&2
    return 1
  fi
  return 0
}
run_check "math-github-renderable" check_mathjax_commands

# ── 5. Mathematics must not hide in an inert code span or in bare prose ──────
run_check "math-backticks" python3 "$doclint" math-backticks "${document_files[@]}"

# ── 6. PlantUML sources parse, and every source has a rendered SVG ───────────
check_plantuml_assets() {
  local rc=0 puml figure_svg
  [[ -d "$figures_dir" ]] || { printf 'missing figures directory: %s\n' "$figures_dir" >&2; return 1; }
  while IFS= read -r puml; do
    if ! JAVA_TOOL_OPTIONS=-Djava.awt.headless=true plantuml -checkonly -failfast2 "$puml" >/dev/null 2>&1; then
      printf 'PlantUML source does not parse: %s\n' "$puml" >&2
      rc=1
      continue
    fi
    figure_svg="${puml%.puml}.svg"
    if [[ ! -s "$figure_svg" ]]; then
      printf 'missing or empty rendered SVG asset: %s (run: plantuml -tsvg %s)\n' "$figure_svg" "$puml" >&2
      rc=1
      continue
    fi
    rg -q '<svg([[:space:]>])' "$figure_svg" || { printf 'rendered asset is missing an SVG root: %s\n' "$figure_svg" >&2; rc=1; }
    rg -q '</svg>' "$figure_svg" || { printf 'rendered asset is missing an SVG close tag: %s\n' "$figure_svg" >&2; rc=1; }
    if rg -q '&lt;#|&lt;&lt;#|&lt;back:' "$figure_svg"; then
      printf 'rendered asset contains escaped PlantUML color markup: %s\n' "$figure_svg" >&2
      rc=1
    fi
    if rg -q -i 'syntax error|cannot be parsed' "$figure_svg"; then
      printf 'rendered asset is a PlantUML error image: %s\n' "$figure_svg" >&2
      rc=1
    fi
  done < <(find "$figures_dir" -type f -name '*.puml' | sort)
  return $rc
}
run_check "diagrams-plantuml-assets" check_plantuml_assets

puml_count="$(find "$figures_dir" -type f -name '*.puml' 2>/dev/null | wc -l)"
[[ "$puml_count" -gt 0 ]] || fail "no PlantUML diagrams found in $figures_dir"

# ── 7. Every expository page embeds at least one rendered figure ─────────────
# ASSUMPTION: the suite index is a roster, not an exposition, so it is exempt.
check_diagrams_present() {
  local rc=0 file name
  for file in "${suite_files[@]}"; do
    name="$(basename -- "$file")"
    [[ "$name" == "README.md" ]] && continue
    if ! rg -q '!\[[^]]*\]\(figures/[^)]+\.svg\)' "$file"; then
      printf '%s embeds no figure — every expository page needs at least one\n' "$name" >&2
      rc=1
    fi
  done
  return $rc
}
run_check "diagrams-plenty" check_diagrams_present

# ── 8. Every diagram is coloured ─────────────────────────────────────────────
# ASSUMPTION: "fully coloured with intuitive colorization per concept" cannot be
# judged mechanically, but its absence can: a .puml with no explicit colour at
# all is certainly not colourised. This is a floor, not a substitute for review.
check_diagrams_coloured() {
  local rc=0 puml
  while IFS= read -r puml; do
    if ! rg -q '#[0-9A-Fa-f]{6}\b' "$puml"; then
      printf 'diagram carries no explicit #RRGGBB colour: %s\n' "$puml" >&2
      rc=1
    fi
  done < <(find "$figures_dir" -type f -name '*.puml' | sort)
  return $rc
}
run_check "diagrams-fully-colored" check_diagrams_coloured

# ── 9. Relative links resolve ────────────────────────────────────────────────
# Span-aware: a page that DOCUMENTS link syntax inside a code span is not making
# a link. A raw-line scan cannot tell the difference and reads
# `![caption](figures/<name>.svg)` as a broken link to `<name>.svg`.
run_check "links-relative" python3 "$doclint" links "${document_files[@]}"

# ── 10. In-document anchors resolve (GitHub slug rules) ─────────────────────
check_anchors() {
  local rc=0 file
  for file in "${document_files[@]}"; do
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
    ' "$file" || rc=1
  done
  return $rc
}
run_check "anchors-in-document" check_anchors

# ── 11. Citations are navigable and carry DOIs ──────────────────────────────
run_check "citations-exist+doi-links" python3 "$doclint" citations "${document_files[@]}"

# ── 12. Every DOI actually resolves (network; OPTIONAL by design) ────────────
# A fabricated DOI is the worst failure this suite can ship, so it is checked —
# but a gate that fails on a plane is a gate people disable, so an unreachable
# doi.org SKIPs instead of failing. DOCLINT_DOI=on makes unreachability fatal.
run_check "citations-doi-valid" python3 "$doclint" doi-valid "${document_files[@]}"

# ── 13. Acronyms are defined before use ─────────────────────────────────────
run_check "pedagogy-define-terms" python3 "$doclint" define-terms "${document_files[@]}"

# ── 14. Algorithms are presented in literate form ───────────────────────────
run_check "algorithms-literate-pseudocode" \
  python3 "$doclint" algorithms --index README.md "${document_files[@]}"

# ── 15. Code snippets parse ─────────────────────────────────────────────────
run_check "code-snippets-valid" python3 "$doclint" code-snippets "${document_files[@]}"

# ── 16. Roster coverage: specs, pages, and completed index rows agree ───────
check_roster() {
  local rc=0 file name spec page row

  # Forward direction: every expository page is discoverable from the index.
  for file in "${suite_files[@]}"; do
    name="$(basename -- "$file")"
    [[ "$name" == "README.md" ]] && continue
    if ! rg -q -F "($name)" "$readme"; then
      printf 'page not listed in the README roster: %s\n' "$name" >&2
      rc=1
    fi
  done

  # Reverse direction: derive the production-language domain from the macro invocations rather
  # than maintaining another list. A checked roster row cannot substitute for the page itself.
  while IFS= read -r spec; do
    page="$(basename -- "${spec%.rs}.md")"
    if [[ ! -f "$script_dir/$page" ]]; then
      printf 'production language specification has no page: %s -> %s\n' \
        "${spec#"$repo_root/"}" "$page" >&2
      rc=1
      continue
    fi
    row="$(rg -F "($page)" "$readme" || true)"
    if [[ -z "$row" ]]; then
      printf 'production language page is absent from the README roster: %s\n' "$page" >&2
      rc=1
    elif [[ "$row" != *"✅"* ]]; then
      printf 'production language page is not marked complete in the README roster: %s\n' \
        "$page" >&2
      rc=1
    fi
  done < <(rg -l '^language![[:space:]]*\{' "$repo_root"/languages/src/*.rs | sort)

  return $rc
}
run_check "roster-coverage" check_roster

# ── 17. Every documented language page names an existing specification ──────
check_spec_source() {
  local rc=0 file name src
  for file in "${suite_files[@]}"; do
    name="$(basename -- "$file")"
    [[ "$name" == "README.md" ]] && continue
    src="languages/src/${name%.md}.rs"
    if [[ ! -f "$repo_root/$src" ]]; then
      printf 'page %s documents a missing specification: %s\n' "$name" "$src" >&2
      rc=1
    fi
  done
  return $rc
}
run_check "live-spec-source" check_spec_source

# ── summary ─────────────────────────────────────────────────────────────────
printf -- '---\n'
if [[ "$tool_errors" -gt 0 ]]; then
  printf 'ERROR: %d check(s) could not run to completion — the pages they cover are UNCHECKED.\n' \
    "$tool_errors" >&2
fi
if [[ "$failures" -gt 0 ]]; then
  printf 'FAILED: %d of %d check(s) failed (%d of them tool errors), %d skipped (%d suite page(s), %d extra page(s), %d figure(s))\n' \
    "$failures" "$checks_run" "$tool_errors" "$skips" "${#suite_files[@]}" \
    "${#extra_files[@]}" "$puml_count" >&2
  exit 1
fi
printf 'ok: languages suite validated — %d of %d check(s) passed, %d skipped (%d suite page(s), %d extra page(s), %d figure(s))\n' \
  "$checks_passed" "$checks_run" "$skips" "${#suite_files[@]}" "${#extra_files[@]}" \
  "$puml_count"
