#!/usr/bin/env python3
"""Mechanised pgmcp documentation-guideline checks for Markdown suites.

`validate.sh` is the entry point and the reporter; this module is where the
checks that need *positional* analysis live, because they must distinguish

    a code span             `Term::Lam`          <- code, correct as-is
    an inline math span     $`\\Theta(|S|)`$      <- mathematics, correct as-is
    an INERT code span      `Theta(|S|)`         <- mathematics wearing code's clothes
    bare prose              Theta(|S|)           <- mathematics with no delimiter at all

and line-oriented tools (grep/awk) cannot: a line containing any backtick
anywhere satisfies a line-level "is it quoted?" test even when the offending
expression sits outside every span on that line.

Every subcommand exits with

    0   PASS   -- no violation found
    1   FAIL   -- violations printed to stderr, one per line, as `path:line: …`
    2   SKIP   -- the check could not run; the reason is printed to stdout

and never asks its caller to interpret stdout. That is deliberate: this repo has
been bitten by gates that read a tool's *text* instead of its *status* (rustfmt
with a non-empty ignore list exits 101 while printing nothing, so a
`| grep -c '^Diff in'` pipeline scored a crash as CLEAN). Exit status is the
contract here.

Exit codes
──────────
Mirrors `scripts/check-fmt.sh` in the sibling `f1r3node-rust-mettail` workspace
rather than inventing a second convention, and extends it by one state:

    0  CLEAN       the check ran and found nothing
    1  VIOLATIONS  the check ran and found something; details on stderr
    2  TOOL ERROR  the check did NOT answer the question; the answer is UNKNOWN
    3  SKIP        the check could not run here (no network, no word list, no
                   rustfmt) and says which

★ 2 and 3 are different states and must never be collapsed. TOOL ERROR is a
failure -- something is broken and the documents are UNCHECKED. SKIP is a
deliberate non-answer. Both are distinct from CLEAN, and the fatal mistake in
either direction is letting "not checked" read as "passed": that is exactly the
rustfmt precedent above, reproduced in Python. Every unexpected exception is
therefore caught in `main` and reported as 2, so a crash can never be mistaken
for "no violations found" -- which is what an uncaught traceback would look like,
since CPython exits 1 on an unhandled exception, colliding with VIOLATIONS.

`doclint.py selftest` constructs all four states and asserts they are separable.

Where this file lives, and why
──────────────────────────────
`docs/languages/doclint.py`, beside `validate.sh` rather than in a repo-level
`scripts/` or `tools/` directory. The reasoning, since `doc-placement` and
`doc-naming-structure` are two of the 26 guidelines and bind the harness as much
as the pages:

  * `validate.sh` is the only entry point and the only reporter; this file is its
    implementation. A gate and its implementation should be found together and
    should move together, so a suite copied elsewhere stays runnable.
  * The other three suites (`docs/architecture/{dovetail,rho-native-integration,
    semantic-predicates}`) each carry their own `validate.sh`; none imports this
    module. Promoting it to a shared location would assert a generality that is
    not yet exercised, and shared code with one caller is a liability.
  * `doclint` says what it is -- a documentation linter -- without leaking how it
    works, so the name survives a rewrite.

If a second suite ever adopts it, that is the moment to lift it to a shared
`tools/` directory, not before.

Requirements
────────────
  * Python 3.9 or newer (checked at start-up).
  * `rustfmt` on PATH for the Rust half of `code-snippets`; absent, that check
    SKIPs and says so.
  * `bash` for the shell half of `code-snippets`.
  * A word list for `define-terms`; absent, that check SKIPs and says so.
  * Network access for `doi-valid`; absent, that check SKIPs and says so.

The supported invocation is **as a script** (`python3 doclint.py <subcommand>`),
which is why bytecode caching is disabled below: a tool that audits a directory
should not leave a `__pycache__` in it for someone else to commit by accident.

Guideline slugs mechanised, as returned by the pgmcp `documentation_guidelines`
tool (26 items / 7 categories):

    math-backticks                  -> subcommand `math-backticks`
    pedagogy-define-terms           -> subcommand `define-terms`
    citations-exist                 -> subcommand `citations` (cross-document anchors)
    citations-doi-links             -> subcommand `citations` (entry must carry a DOI)
    citations-doi-valid             -> subcommand `doi-valid`  (network, optional)
    algorithms-literate-pseudocode  -> subcommand `algorithms`
    code-snippets-valid             -> subcommand `code-snippets`

Usage: doclint.py <subcommand> [--index README.md] FILE [FILE...]
"""

from __future__ import annotations

import sys

# Set before anything else is imported, so no import this module performs can
# leave a __pycache__ beside the pages being audited. When doclint is run as a
# script -- the supported invocation -- CPython never caches the __main__ module
# itself either, so the audited directory stays clean.
sys.dont_write_bytecode = True

import http.client  # noqa: E402  (must follow the bytecode guard)
import os  # noqa: E402
import re  # noqa: E402
import subprocess  # noqa: E402
import tempfile  # noqa: E402
import urllib.parse  # noqa: E402

MINIMUM_PYTHON = (3, 9)
if sys.version_info < MINIMUM_PYTHON:
    sys.stderr.write(
        "doclint.py requires Python {}.{} or newer; this is {}.{}\n".format(
            *MINIMUM_PYTHON, *sys.version_info[:2]
        )
    )
    raise SystemExit(1)

PASS, FAIL, TOOL_ERROR, SKIP = 0, 1, 2, 3

STATE_NAMES = {PASS: "CLEAN", FAIL: "VIOLATIONS", TOOL_ERROR: "TOOL ERROR", SKIP: "SKIP"}

FENCE_RE = re.compile(r"^\s*```(\S*)")
HEADING_RE = re.compile(r"^(#{1,6})\s+(.*?)\s*$")

# ───────────────────────────── shared lexing ────────────────────────────────
#
# One pass produces, for every line, a `prose` projection in which every region
# that is NOT prose has been overwritten with a sentinel character of equal
# width. Widths are preserved so that a column reported against `prose` is a
# true column of the original line.

SENT_MATH = "\x01"  # $`...`$   inline math span
SENT_CODE = "\x02"  # `...`     code span
SENT_LINK = "\x03"  # ](...)    link target
SENT_HTML = "\x04"  # <...>     raw HTML / autolink
SENT_KEY = "\x05"  # SCREAMING-KEBAB-1998  citation key


def _blank(match: re.Match, sentinel: str) -> str:
    return sentinel * len(match.group(0))


# SCREAMING-KEBAB citation keys: OSLF-2017, DEBRUIJN-1972,
# SET-AUTOMATON-LOCATE-2021. The interior `(?:-…)*` is a STAR, not a plus: a
# single-segment key such as DEBRUIJN-1972 has no interior segment at all, and a
# plus here silently let `DEBRUIJN` through as an undefined acronym.
CITATION_KEY_RE = re.compile(r"\b[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*-\d{4}\b")


def read_lines(path: str) -> list[str]:
    with open(path, encoding="utf-8") as handle:
        return [line.rstrip("\n") for line in handle]


def project(lines: list[str]) -> list[str | None]:
    """Return one entry per line: the prose projection, or None inside a fence.

    The fence delimiter lines themselves project to None as well -- they are
    markup, not prose.
    """
    out: list[str | None] = []
    inside = False
    for raw in lines:
        if FENCE_RE.match(raw):
            inside = not inside
            out.append(None)
            continue
        if inside:
            out.append(None)
            continue
        text = re.sub(r"\$`[^`]*`\$", lambda m: _blank(m, SENT_MATH), raw)
        text = re.sub(r"`[^`]*`", lambda m: _blank(m, SENT_CODE), text)
        text = re.sub(r"\]\([^)]*\)", lambda m: _blank(m, SENT_LINK), text)
        text = re.sub(r"<[^>\s][^>]*>", lambda m: _blank(m, SENT_HTML), text)
        text = CITATION_KEY_RE.sub(lambda m: _blank(m, SENT_KEY), text)
        out.append(text)
    return out


def code_spans(lines: list[str]):
    """Yield (lineno, span_text) for every *plain* code span outside fences.

    A `$`...`$` inline math span is NOT a plain code span: it is blanked first
    so that the backticks belonging to it are never re-matched.
    """
    inside = False
    for number, raw in enumerate(lines, 1):
        if FENCE_RE.match(raw):
            inside = not inside
            continue
        if inside:
            continue
        masked = re.sub(r"\$`[^`]*`\$", lambda m: _blank(m, SENT_MATH), raw)
        for match in re.finditer(r"`([^`]+)`", masked):
            yield number, match.group(1)


def fences(lines: list[str]):
    """Yield (info_string, first_body_lineno, body_text) for every fenced block."""
    inside, info, start, body = False, "", 0, []
    for number, raw in enumerate(lines, 1):
        match = FENCE_RE.match(raw)
        if match:
            if not inside:
                inside, info, start, body = True, match.group(1), number + 1, []
            else:
                yield info, start, "\n".join(body)
                inside = False
        elif inside:
            body.append(raw)


def slug(text: str) -> str:
    """GitHub (github-slugger) heading anchor.

    Lower-case; drop backticks; drop every character that is neither
    alphanumeric nor space/underscore/hyphen; each remaining space becomes one
    hyphen (no run collapsing). Matches the awk implementation in validate.sh so
    the two passes cannot disagree.
    """
    text = text.lower().replace("`", "")
    text = "".join(ch for ch in text if ch.isalnum() or ch in " _-")
    return text.replace(" ", "-")


def headings(lines: list[str]) -> set[str]:
    found, inside = set(), False
    for raw in lines:
        if FENCE_RE.match(raw):
            inside = not inside
            continue
        if inside:
            continue
        match = HEADING_RE.match(raw)
        if match:
            found.add(slug(match.group(2)))
    return found


# ───────────────────────── math-backticks (guideline 18) ────────────────────
#
# Relations, quantifiers and set operators are mathematics wherever they appear.
# The character class extends validate.sh's incumbent math-symbol class so the
# two checks cannot classify the same glyph differently.
#
# Deliberately EXCLUDED, with reasons, because they are prose rather than
# formulae in this corpus:
#   *  Greek letters standing alone -- they NAME things here (the lambda
#      calculus, beta-reduction, the pi-calculus, the rho-calculus). Guideline
#      16 asks for MathJax for *formulae*, and a name is not a formula. A Greek
#      letter that heads a complexity class is caught by COMPLEXITY_RE below.
#   *  U+00B7 MIDDLE DOT -- guideline 16 explicitly keeps unicode for
#      separators, and this corpus uses it as one ("2026-07-27 · part of …").
#      As multiplication it only ever occurs inside a complexity class, which
#      COMPLEXITY_RE already rejects.
#   *  U+00D7 MULTIPLICATION SIGN -- "5.12×" is an idiomatic prose multiplier,
#      and `$`5.12\times`$` would be less readable, not more.

RELATION_CHARS = "⊆⊇⊂⊃⇒⟹⇔∀∃∈∉∌≡≈≠≤≥↦→⟶⇝∧∨∪∩∖⊕⊗⊢⊨∘−"
RELATION_RE = re.compile("[" + re.escape(RELATION_CHARS) + "]")
COMPLEXITY_RE = re.compile(r"(?<![0-9A-Za-z_])[OΘΩω]\s*\(")
SUBSUP_RE = re.compile(r"[₀₁₂₃₄₅₆₇₈₉⁰¹²³⁴⁵⁶⁷⁸⁹ᵢⱼₖₙ]")


def _math_hit(text: str) -> str | None:
    match = RELATION_RE.search(text)
    if match:
        return f"relation/quantifier {match.group(0)!r}"
    if COMPLEXITY_RE.search(text):
        return "complexity class"
    match = SUBSUP_RE.search(text)
    if match:
        return f"unicode sub/superscript {match.group(0)!r}"
    return None


def check_math_backticks(paths: list[str]) -> int:
    bad = []
    for path in paths:
        lines = read_lines(path)
        for number, span in code_spans(lines):
            reason = _math_hit(span)
            if reason:
                bad.append(
                    f"{path}:{number}: INERT code span -- {reason} in `{span}`; "
                    f"use an inline math span $`…`$ or a ```math fence"
                )
        for number, text in enumerate(project(lines), 1):
            if text is None:
                continue
            reason = _math_hit(text)
            if reason:
                bad.append(
                    f"{path}:{number}: BARE prose math -- {reason}; "
                    f"use an inline math span $`…`$ or a ```math fence"
                )
    for line in bad:
        print(line, file=sys.stderr)
    return FAIL if bad else PASS


# ─────────────────── pedagogy-define-terms (guideline 22) ───────────────────
#
# An acronym is an all-caps token that is NOT an English word. The dictionary is
# what makes this check usable instead of noisy: without it, every emphatic
# `**NEVER**` and `**PROPOSED**` in a design document reads as an undefined
# acronym. With it, PROPOSED/CORRECTED/UNCOMPRESSED/HEAD/SET/MATCHING fall away
# and DSL/GSLT/WPDA/BNFC/LHS/RHS/FIPS/BFS/DFS remain.
#
# ASSUMPTIONS, stated so they can be argued with:
#   * A token that is an English dictionary word is not an acronym. This trades
#     a few false negatives (COMM and AC are dictionary words) for the absence
#     of false positives, which is the right way round for a gate people must
#     keep enabled. Terms lost this way are still governed by the guideline --
#     the check is a floor, not a ceiling.
#   * Tokens with fewer than two letters (L2, C4, R) are rung/section labels,
#     not acronyms.
#   * SCREAMING-KEBAB-1998 citation keys are reference labels, not acronyms;
#     they are blanked before tokenising.
#   * The allow-list below is for acronyms whose expansion would be noise in
#     any technical document.

SYSTEM_DICTIONARIES = (
    "/usr/share/dict/words",
    "/usr/share/dict/american-english",
    "/usr/share/dict/british-english",
)

UNIVERSAL_ACRONYMS = {
    "ASCII", "API", "CI", "CPU", "CSV", "DOI", "GPU", "HTML", "HTTP", "HTTPS",
    "ID", "IO", "ISBN", "JSON", "PDF", "RAM", "RFC", "SVG", "TOC", "TODO", "UI",
    "URL", "UTF", "XML", "YAML",
}

ACRONYM_RE = re.compile(r"\b[A-Z][A-Z0-9]*\b")


def load_dictionary() -> set[str] | None:
    """The word list, or None if there is not one.

    `DOCLINT_WORDLIST` is AUTHORITATIVE when set: if it names a file that is not
    there, the check skips rather than quietly falling back to a system list.
    Silently ignoring explicit configuration is how a check ends up measuring
    something other than what its operator asked for.
    """
    override = os.environ.get("DOCLINT_WORDLIST", "")
    candidates = (override,) if override else SYSTEM_DICTIONARIES
    for candidate in candidates:
        if candidate and os.path.isfile(candidate):
            with open(candidate, encoding="utf-8", errors="ignore") as handle:
                return {word.strip().lower() for word in handle if word.strip()}
    return None


# A parenthetical that OPENS with one of these is a cross-reference, not an
# expansion: "the XYZ (see below)" tells the reader where to look, not what the
# letters stand for. No real expansion begins with any of them.
CROSS_REFERENCE_OPENERS = (
    "see", "cf", "eg", "ie", "above", "below", "and", "or", "but", "not",
    "page", "pages", "section", "chapter", "ibid", "op", "loc", "as", "which",
    "note", "compare", "per",
)


def definition_lines(lines: list[str], acronym: str) -> list[int]:
    """Line numbers at which `acronym` is defined, by any accepted form."""
    escaped = re.escape(acronym)
    openers = "|".join(CROSS_REFERENCE_OPENERS)
    forms = (
        # ACRONYM (expansion). The parenthetical must LOOK like an expansion:
        # no code span inside it, at least two words of two-or-more letters, and
        # at least one lower-case letter. Without those conditions an incidental
        # parenthetical citation -- `FIPS (2026-01-08-Lookahead.md)` -- reads as
        # a definition and silently exempts a genuinely undefined acronym.
        re.compile(
            rf"\b{escaped}\b\s*\((?=[^)`]*\))(?=[^)]*[a-z])"
            rf"(?!\s*(?:{openers})\b)"
            rf"(?:[^)]*?[A-Za-z]{{2,}}[^)]*?[A-Za-z]{{2,}}[^)]*)\)"
        ),
        # expansion (ACRONYM) — and the bibliographic variants that carry a year
        # or edition inside the same parenthesis: (ICTAC 2021), (POPL '73).
        re.compile(rf"\(\s*{escaped}\b[^)]{{0,24}}\)"),
        # notation/glossary table row whose FIRST cell is the acronym
        re.compile(rf"^\s*\|\s*[`*_]*{escaped}[`*_]*\s*(?:/[^|]*)?\|"),
        # bold gloss:  **ACRONYM** — expansion
        re.compile(rf"\*\*{escaped}\*\*\s*[—–-]{{1,2}}\s"),
    )
    found = []
    for number, raw in enumerate(lines, 1):
        if any(form.search(raw) for form in forms):
            found.append(number)
    return found


def check_define_terms(paths: list[str]) -> int:
    words = load_dictionary()
    if words is None:
        override = os.environ.get("DOCLINT_WORDLIST", "")
        where = f"$DOCLINT_WORDLIST ({override})" if override else \
            "/usr/share/dict/{words,american-english,british-english}"
        print(f"no word list found at {where}; install a `words` package or point "
              f"DOCLINT_WORDLIST at one to enable the acronym check")
        return SKIP
    bad = []
    for path in paths:
        lines = read_lines(path)
        first_use: dict[str, int] = {}
        for number, text in enumerate(project(lines), 1):
            if text is None:
                continue
            for match in ACRONYM_RE.finditer(text):
                token = match.group(0)
                letters = [ch for ch in token if ch.isalpha()]
                if len(letters) < 2:
                    continue
                if token in UNIVERSAL_ACRONYMS or token.lower() in words:
                    continue
                first_use.setdefault(token, number)
        for token, use_line in sorted(first_use.items(), key=lambda kv: kv[1]):
            defs = definition_lines(lines, token)
            if not defs:
                bad.append(
                    f"{path}:{use_line}: acronym {token!r} is never expanded -- "
                    f"give it a notation-table row, a bold gloss, or write "
                    f"'{token} (expansion)' at first use"
                )
            elif min(defs) > use_line:
                bad.append(
                    f"{path}:{use_line}: acronym {token!r} is used before its "
                    f"definition on line {min(defs)}"
                )
    for line in bad:
        print(line, file=sys.stderr)
    return FAIL if bad else PASS


# ────────────── citations-exist / citations-doi-links (19, 20) ──────────────

REFERENCES_HEADING_RE = re.compile(
    r"^#{1,6}\s+(?:\d+[.)]\s*)?(references|bibliography|works\s+cited|sources)\b",
    re.IGNORECASE,
)
ENTRY_START_RE = re.compile(r"^\s*(?:[-*+]|\d+[.)])\s+\S")
DOI_LINK_RE = re.compile(r"https?://(?:dx\.)?doi\.org/10\.\S+")
REPO_LINK_RE = re.compile(r"\]\(([^)\s]+)\)")
NO_DOI_MARKER = "(no DOI registered)"


def reference_entries(lines: list[str]):
    """Yield (start_lineno, joined_entry_text) for each entry of each References section."""
    inside_fence = False
    in_refs = False
    current: list[str] = []
    start = 0
    for number, raw in enumerate(lines, 1):
        if FENCE_RE.match(raw):
            inside_fence = not inside_fence
            continue
        if inside_fence:
            if current:
                current.append(raw)
            continue
        if HEADING_RE.match(raw):
            if current:
                yield start, "\n".join(current)
                current = []
            in_refs = bool(REFERENCES_HEADING_RE.match(raw))
            continue
        if not in_refs:
            continue
        if ENTRY_START_RE.match(raw):
            if current:
                yield start, "\n".join(current)
            current, start = [raw], number
        elif current and raw.strip():
            current.append(raw)
        elif current:
            yield start, "\n".join(current)
            current = []
    if current:
        yield start, "\n".join(current)


def check_citations(paths: list[str]) -> int:
    bad = []
    for path in paths:
        lines = read_lines(path)
        base = os.path.dirname(os.path.abspath(path))

        # citations-doi-links: every external reference entry carries a DOI, or
        # is an in-repo cross reference (a navigable relative Markdown link), or
        # says outright that no DOI is registered.
        for start, entry in reference_entries(lines):
            if DOI_LINK_RE.search(entry) or NO_DOI_MARKER in entry:
                continue
            internal = False
            for match in REPO_LINK_RE.finditer(entry):
                target = match.group(1).split("#", 1)[0]
                if target and not target.startswith(("http://", "https://", "mailto:")):
                    if os.path.exists(os.path.join(base, target)):
                        internal = True
                        break
            if not internal:
                head = entry.splitlines()[0].strip()[:96]
                bad.append(
                    f"{path}:{start}: reference entry has no DOI link, no navigable "
                    f"in-repo link, and no '{NO_DOI_MARKER}' marker -- {head}"
                )

        # citations-exist: a cross-document anchor must resolve in its target.
        inside_fence = False
        for number, raw in enumerate(lines, 1):
            if FENCE_RE.match(raw):
                inside_fence = not inside_fence
                continue
            if inside_fence:
                continue
            for match in REPO_LINK_RE.finditer(raw):
                target = match.group(1)
                if target.startswith(("http://", "https://", "mailto:", "#")):
                    continue
                if "#" not in target:
                    continue
                relative, anchor = target.split("#", 1)
                if not relative.endswith(".md"):
                    continue
                resolved = os.path.join(base, relative)
                if not os.path.exists(resolved):
                    bad.append(
                        f"{path}:{number}: citation points at a missing file: {relative}"
                    )
                    continue
                if anchor not in headings(read_lines(resolved)):
                    bad.append(
                        f"{path}:{number}: citation anchor #{anchor} does not exist "
                        f"in {relative}"
                    )
    for line in bad:
        print(line, file=sys.stderr)
    return FAIL if bad else PASS


# ──────────────────────── relative links (guideline 1) ──────────────────────
#
# Span-aware, and that is the whole point of doing it here rather than with a
# line-oriented `rg`. A page that DOCUMENTS link syntax writes it inside a code
# span -- "referenced as `![caption](figures/<name>.svg)`" -- and a raw-line
# scan reads that as a live link to a file named `<name>.svg`, which of course
# does not exist. The fix is not to stop documenting the convention; it is to
# stop treating code spans as prose.


def check_links(paths: list[str]) -> int:
    bad = []
    for path in paths:
        base = os.path.dirname(os.path.abspath(path))
        lines = read_lines(path)
        inside = False
        for number, raw in enumerate(lines, 1):
            if FENCE_RE.match(raw):
                inside = not inside
                continue
            if inside:
                continue
            # Blank inline math and code spans, then look for what remains.
            text = re.sub(r"\$`[^`]*`\$", lambda m: _blank(m, SENT_MATH), raw)
            text = re.sub(r"`[^`]*`", lambda m: _blank(m, SENT_CODE), text)
            for match in re.finditer(r"\]\(([^)]+)\)", text):
                target = match.group(1)
                if target.startswith(("http://", "https://", "mailto:", "#")):
                    continue
                target = target.split("#", 1)[0]
                if not target:
                    continue  # pure in-document anchor: the anchor pass owns it
                if not os.path.exists(os.path.join(base, target)):
                    bad.append(
                        f"{path}:{number}: broken relative link: {target}"
                    )
    for line in bad:
        print(line, file=sys.stderr)
    return FAIL if bad else PASS


# ───────────────────── citations-doi-valid (guideline 21) ───────────────────
#
# "Does this DOI exist?" is a question for the DOI resolver, not for the
# publisher. Following the redirect asks the publisher instead, and publishers
# answer HEAD requests badly: 10.1145/512927.512931 (Pratt 1973) is a perfectly
# real DOI whose ACM landing page answers 403. So this check stops at
# https://doi.org and reads the resolver's own status:
#
#     3xx  registered      -> PASS
#     404  not registered  -> FAIL   (a fabricated DOI, the worst failure here)
#     else indeterminate   -> SKIP that DOI, and say so
#
# The network is OPTIONAL. If doi.org is unreachable the whole check SKIPs, so
# the gate still runs on a plane. Set DOCLINT_DOI=off to skip it deliberately,
# or DOCLINT_DOI=on to make unreachability a hard failure in CI.

DOI_TRIM = ".,;:)]}>’\"'"


def collect_dois(paths: list[str]) -> dict[str, tuple[str, int]]:
    found: dict[str, tuple[str, int]] = {}
    for path in paths:
        for number, raw in enumerate(read_lines(path), 1):
            for match in DOI_LINK_RE.finditer(raw):
                url = match.group(0)
                while url and url[-1] in DOI_TRIM:
                    url = url[:-1]
                doi = url.split("doi.org/", 1)[1]
                found.setdefault(doi, (path, number))
    return found


def resolver_status(doi: str, timeout: float) -> int:
    """HTTP status returned by doi.org itself for this DOI, without redirecting.

    `http.client` is used rather than `urllib.request` precisely because it does
    not follow redirects: there is no handler to subclass and no redirect
    behaviour to suppress. 0 means "no answer" (DNS failure, timeout, reset).
    """
    path = "/" + urllib.parse.quote(doi, safe="/%:()<>_.-")
    connection = http.client.HTTPSConnection("doi.org", timeout=timeout)
    try:
        connection.request("HEAD", path, headers={"User-Agent": "doclint/1.0"})
        return connection.getresponse().status
    except Exception:
        return 0
    finally:
        connection.close()


def check_doi_valid(paths: list[str]) -> int:
    mode = os.environ.get("DOCLINT_DOI", "auto").lower()
    if mode == "off":
        print("DOCLINT_DOI=off -- DOI resolution not attempted")
        return SKIP
    dois = collect_dois(paths)
    if not dois:
        print("no DOI links found in the checked pages -- nothing to resolve")
        return SKIP
    if resolver_status("10.1016/j.entcs.2005.05.016", timeout=6.0) == 0:
        message = "https://doi.org is unreachable -- DOI resolution not attempted"
        if mode == "on":
            print(message + " (DOCLINT_DOI=on makes this fatal)", file=sys.stderr)
            return FAIL
        print(message + " (set DOCLINT_DOI=on to make this fatal)")
        return SKIP
    bad, skipped, ok = [], [], 0
    for doi, (path, number) in sorted(dois.items()):
        status = resolver_status(doi, timeout=20.0)
        if 300 <= status < 400:
            ok += 1
        elif status == 404:
            bad.append(f"{path}:{number}: DOI is not registered at doi.org: {doi}")
        else:
            skipped.append(f"{path}:{number}: DOI {doi} indeterminate (HTTP {status})")
    for line in bad:
        print(line, file=sys.stderr)
    if bad:
        return FAIL
    if skipped:
        # PARTIAL verification is not verification. Reporting PASS here would
        # convert "we could not check these" into "these are fine" in the
        # reader's mind, which is the precise failure this check exists to
        # prevent -- so an indeterminate DOI downgrades the whole check to SKIP.
        print(f"  resolved {ok}/{len(dois)} DOI(s) at doi.org; "
              f"{len(skipped)} could NOT be verified:")
        for line in skipped:
            print("    " + line)
        return SKIP
    print(f"  resolved {ok}/{len(dois)} DOI(s) at doi.org (all verified)")
    return PASS


# ────────── algorithms-literate-pseudocode (guideline 25) ───────────────────
#
# Knuth's literate form is prose and code interleaved, each chunk named and
# explained. Mechanised as a three-part convention, announced in README.md:
#
#   1. an algorithm is a fenced block with the info-string `pseudocode`;
#   2. it carries a caption `**Algorithm N (Name).**` in the six lines above it;
#   3. it is EXPOSITED -- prose follows within twelve lines, so the block is
#      explained rather than dumped;
#
# and every expository page carries at least one. Index pages (named with
# --index) are exempt: a roster enumerates pages, it does not present an
# algorithm, so there is nothing for the guideline to bite on.

CAPTION_RE = re.compile(r"\*\*Algorithm\s+[0-9A-Za-z.]+\s*\([^)]+\)\.?\*\*")


def check_algorithms(paths: list[str], index: set[str]) -> int:
    bad = []
    for path in paths:
        lines = read_lines(path)
        blocks = [(start, body) for info, start, body in fences(lines)
                  if info.lower() == "pseudocode"]
        if not blocks:
            if os.path.basename(path) not in index:
                bad.append(
                    f"{path}:1: no ```pseudocode block -- an expository page must "
                    f"present its algorithms in literate form (caption "
                    f"'**Algorithm N (Name).**', a ```pseudocode fence, then prose)"
                )
            continue
        for start, body in blocks:
            # `start` is the first body line; the opening fence is `start - 1`.
            # Six lines above that fence: 1-based start-7 .. start-2.
            above = lines[max(0, start - 8):max(0, start - 2)]
            if not any(CAPTION_RE.search(line) for line in above):
                bad.append(
                    f"{path}:{start}: ```pseudocode block has no "
                    f"'**Algorithm N (Name).**' caption within the six lines above it"
                )
            end = start + len(body.splitlines())
            following = lines[end:end + 13]
            exposition = False
            for line in following:
                if FENCE_RE.match(line):
                    break
                if line.strip() and not line.startswith("#"):
                    exposition = True
                    break
            if not exposition:
                bad.append(
                    f"{path}:{start}: ```pseudocode block is not exposited -- literate "
                    f"form requires prose explaining the steps within twelve lines below"
                )
    for line in bad:
        print(line, file=sys.stderr)
    return FAIL if bad else PASS


# ───────────────── code-snippets-valid (guideline 26) ───────────────────────
#
# Machine-checked info-strings and how:
#   rust        must parse. `rustfmt --emit stdout` is a parse-only gate that
#               needs no cargo build; it exits non-zero on a syntax error and
#               zero when the input merely wants reformatting. A snippet is
#               accepted if it parses EITHER as a whole file OR wrapped in a
#               function body, so genuine statement-level fragments are legal
#               while DSL text mislabelled as Rust is not.
#   sh / bash   must pass `bash -n` (parse only, nothing is executed).
#
# Every other info-string (text, math, pseudocode, …) is out of scope here and
# is covered by the math and algorithm checks instead. A fence tagged `rust`
# that is really specification syntax should be tagged `text`: that is the fix,
# not an exemption.

RUST_EDITION = "2021"


def rust_parses(snippet: str) -> bool:
    with tempfile.TemporaryDirectory() as workdir:
        for candidate in (snippet, "fn __doclint_probe() {\n" + snippet + "\n}\n"):
            probe = os.path.join(workdir, "probe.rs")
            with open(probe, "w", encoding="utf-8") as handle:
                handle.write(candidate + "\n")
            result = subprocess.run(
                ["rustfmt", "--edition", RUST_EDITION, "--emit", "stdout", probe],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                check=False,
            )
            if result.returncode == 0:
                return True
    return False


def shell_parses(snippet: str) -> bool:
    result = subprocess.run(
        ["bash", "-n"],
        input=snippet,
        text=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    )
    return result.returncode == 0


def check_code_snippets(paths: list[str]) -> int:
    have_rustfmt = subprocess.run(
        ["rustfmt", "--version"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=False,
    ).returncode == 0
    bad, rust_seen = [], 0
    for path in paths:
        for info, start, body in fences(read_lines(path)):
            tag = info.lower()
            if tag in ("rust", "rs"):
                rust_seen += 1
                if have_rustfmt and not rust_parses(body):
                    bad.append(
                        f"{path}:{start}: ```{info} block does not parse as Rust "
                        f"(neither as a file nor as a function body) -- fix it, or "
                        f"tag it ```text if it is specification syntax rather than Rust"
                    )
            elif tag in ("sh", "bash", "shell"):
                if not shell_parses(body):
                    bad.append(
                        f"{path}:{start}: ```{info} block is not valid shell "
                        f"(`bash -n` rejects it)"
                    )
    for line in bad:
        print(line, file=sys.stderr)
    if bad:
        return FAIL
    if rust_seen and not have_rustfmt:
        print("rustfmt not found -- Rust snippets were not parsed (shell snippets were)")
        return SKIP
    return PASS


# ──────────────────────────────── self-test ─────────────────────────────────
#
# A check that has never been observed to reject anything is not evidence that
# the thing it guards is absent -- it is only evidence that the check ran. So
# every check above ships with a NEGATIVE fixture that it must reject and a
# POSITIVE fixture that it must accept. The positive fixtures matter just as
# much: a check wired to fail unconditionally would satisfy the negative half
# on its own and guard nothing.
#
# Run with:  docs/languages/doclint.py selftest

NEGATIVE_FIXTURES: dict[str, tuple[str, str]] = {
    "math-backticks/inert-code-span": ("math-backticks", """\
# Fixture

The visited key costs `Θ(|S|)` per edge.
"""),
    "math-backticks/bare-prose": ("math-backticks", """\
# Fixture

For every trace t we have t ⊆ u, hence the claim.
"""),
    "define-terms/never-expanded": ("define-terms", """\
# Fixture

The WPDA parser consumes the token frontier.
"""),
    "define-terms/defined-too-late": ("define-terms", """\
# Fixture

The WPDA parser consumes the token frontier.

| Term | Meaning |
|---|---|
| **WPDA** | weighted pushdown automaton |
"""),
    "citations/entry-without-doi": ("citations", """\
# Fixture

## References

- Barendregt, H. P., *The Lambda Calculus*, North-Holland, 1984.
"""),
    "citations/dangling-cross-document-anchor": ("citations", """\
# Fixture

See [the roster](sibling.md#a-heading-that-does-not-exist).

## References

- In-repo: [sibling](sibling.md)
"""),
    "algorithms/no-pseudocode-block": ("algorithms", """\
# Fixture

We first descend child 0, then bind child 1, then fire the substitution.
"""),
    "algorithms/uncaptioned-block": ("algorithms", """\
# Fixture

Here is how it works.

```pseudocode
descend(child 0)
```

And that is the whole story.
"""),
    "algorithms/unexposited-block": ("algorithms", """\
# Fixture

**Algorithm 1 (Descent).**

```pseudocode
descend(child 0)
```
"""),
    "code-snippets/rust-that-is-not-rust": ("code-snippets", """\
# Fixture

```rust
Beta . |- (App (Lam fun) arg) ~> (eval fun arg);
```
"""),
    "code-snippets/broken-shell": ("code-snippets", """\
# Fixture

```sh
if [ -f x ; then echo hi
```
"""),
    "doi-valid/fabricated-doi": ("doi-valid", """\
# Fixture

## References

- A work that does not exist.
  DOI: [10.9999/definitely.not.a.real.doi](https://doi.org/10.9999/definitely.not.a.real.doi)
"""),
    "links/broken-relative-link": ("links", """\
# Fixture

See [the figure](figures/there-is-no-such-file.svg).
"""),
}

# The link checker must NOT fire on link syntax that a page merely documents
# inside a code span. This is a negative control for a false positive rather
# than for a false negative, so it lives apart from NEGATIVE_FIXTURES.
FALSE_POSITIVE_FIXTURES: dict[str, tuple[str, str]] = {
    "links/documented-syntax-in-a-code-span": ("links", """\
# Fixture

Every expository page embeds a figure, referenced as `![caption](figures/<name>.svg)`.
"""),
}

POSITIVE_FIXTURE = """\
# Fixture

The weighted pushdown automaton (WPDA) parser costs $`\\Theta(|S|)`$ per edge,
and every trace satisfies $`t \\subseteq u`$.

**Algorithm 1 (Descent).**

```pseudocode
descend(child 0)
bind(child 1)
```

Step 1 walks to the function position; step 2 captures the argument.

```rust
pub enum Term {
    App(Arc<Term>, Arc<Term>),
}
```

```sh
plantuml -tsvg figures/*.puml
```

## References

- Peyton Jones, S., and Graf, S., *Triemaps that match*, arXiv:2302.08775, 2024.
  DOI: [10.48550/arXiv.2302.08775](https://doi.org/10.48550/arXiv.2302.08775)
"""

SIBLING_FIXTURE = "# Sibling\n\n## A real heading\n\nBody.\n"


def _run_check(command: str, files: list[str]) -> int:
    if command == "math-backticks":
        return check_math_backticks(files)
    if command == "define-terms":
        return check_define_terms(files)
    if command == "citations":
        return check_citations(files)
    if command == "doi-valid":
        return check_doi_valid(files)
    if command == "algorithms":
        return check_algorithms(files, set())
    if command == "code-snippets":
        return check_code_snippets(files)
    if command == "links":
        return check_links(files)
    raise AssertionError(f"unknown check {command!r}")


def selftest() -> int:
    import contextlib
    import io

    failures = []
    with tempfile.TemporaryDirectory() as workdir:
        sibling = os.path.join(workdir, "sibling.md")
        with open(sibling, "w", encoding="utf-8") as handle:
            handle.write(SIBLING_FIXTURE)

        for name, (command, body) in NEGATIVE_FIXTURES.items():
            path = os.path.join(workdir, "fixture.md")
            with open(path, "w", encoding="utf-8") as handle:
                handle.write(body)
            captured = io.StringIO()
            with contextlib.redirect_stderr(captured), contextlib.redirect_stdout(io.StringIO()):
                status = _run_check(command, [path])
            verdict = STATE_NAMES[status]
            detail = captured.getvalue().strip().splitlines()
            first = detail[0].split(": ", 1)[-1] if detail else ""
            if status == FAIL:
                print(f"  RED  ok   {name:<44} -> FAIL   {first[:76]}")
            elif status == SKIP:
                print(f"  RED  skip {name:<44} -> SKIP   (check unavailable here)")
            else:
                print(f"  RED  BAD  {name:<44} -> {verdict}   check did NOT fire")
                failures.append(name)

        for name, (command, body) in FALSE_POSITIVE_FIXTURES.items():
            path = os.path.join(workdir, "fixture.md")
            with open(path, "w", encoding="utf-8") as handle:
                handle.write(body)
            captured = io.StringIO()
            with contextlib.redirect_stderr(captured), contextlib.redirect_stdout(io.StringIO()):
                status = _run_check(command, [path])
            if status == PASS:
                print(f"  GREEN ok  {name:<44} -> PASS   (no false positive)")
            else:
                print(f"  GREEN BAD {name:<44} -> FALSE POSITIVE "
                      f"{captured.getvalue().strip()[:60]}")
                failures.append(name)

        clean = os.path.join(workdir, "clean.md")
        with open(clean, "w", encoding="utf-8") as handle:
            handle.write(POSITIVE_FIXTURE)
        for command in ("math-backticks", "define-terms", "citations",
                        "algorithms", "code-snippets", "doi-valid", "links"):
            captured = io.StringIO()
            with contextlib.redirect_stderr(captured), contextlib.redirect_stdout(io.StringIO()):
                status = _run_check(command, [clean])
            if status in (PASS, SKIP):
                print(f"  GREEN ok  {command:<44} -> {STATE_NAMES[status]}")
            else:
                print(f"  GREEN BAD {command:<44} -> {STATE_NAMES[status]}   "
                      f"{captured.getvalue().strip()[:66]}")
                failures.append("positive/" + command)

        failures.extend(_selftest_driver_states(workdir, clean))

    if failures:
        print("selftest FAILED for: " + ", ".join(failures), file=sys.stderr)
        return FAIL
    return PASS


def _selftest_driver_states(workdir: str, clean_doc: str) -> list[str]:
    """Prove the DRIVER separates CLEAN / VIOLATIONS / TOOL ERROR / SKIP.

    Run as real subprocesses, because the thing under test is the process exit
    code a caller sees -- not a return value inside this interpreter. A checker
    whose failure mode has never been exercised is not evidence of anything.
    """
    violating = os.path.join(workdir, "violating.md")
    with open(violating, "w", encoding="utf-8") as handle:
        handle.write("# Fixture\n\nThe visited key costs `Θ(|S|)` per edge.\n")

    scenarios = [
        ("CLEAN      (a conforming document)",
         ["math-backticks", clean_doc], {}, PASS),
        ("VIOLATIONS (an inert math code span)",
         ["math-backticks", violating], {}, FAIL),
        ("TOOL ERROR (a file that does not exist)",
         ["math-backticks", os.path.join(workdir, "no-such-file.md")], {}, TOOL_ERROR),
        ("TOOL ERROR (an unknown subcommand)",
         ["no-such-check", clean_doc], {}, TOOL_ERROR),
        ("SKIP       (DOI resolution switched off)",
         ["doi-valid", clean_doc], {"DOCLINT_DOI": "off"}, SKIP),
        ("SKIP       (no word list available)",
         ["define-terms", clean_doc], {"DOCLINT_WORDLIST": os.path.join(workdir, "nope")}, SKIP),
    ]

    print()
    print("  driver states — is a CRASH distinguishable from a CLEAN run?")
    print(f"    {'scenario':<40} {'exit':>4}  {'classified':<12} verdict")
    failures = []
    seen: dict[int, str] = {}
    for label, args, env_overrides, expected in scenarios:
        env = dict(os.environ)
        # Neutralise ambient settings so each scenario tests what it says it does.
        env.pop("DOCLINT_DOI", None)
        env.pop("DOCLINT_WORDLIST", None)
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        env.update(env_overrides)
        result = subprocess.run(
            [sys.executable, os.path.abspath(__file__), *args],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            env=env, check=False,
        )
        ok = result.returncode == expected
        classified = STATE_NAMES.get(result.returncode, f"?{result.returncode}")
        print(f"    {label:<40} {result.returncode:>4}  {classified:<12} "
              f"{'ok' if ok else 'BAD, expected ' + STATE_NAMES[expected]}")
        if not ok:
            failures.append("driver/" + label.split()[0].lower())
        seen.setdefault(result.returncode, label)

    if len(seen) < 4:
        print(f"    ⚠ only {len(seen)} distinct exit code(s) observed; the four "
              f"states are NOT separable", file=sys.stderr)
        failures.append("driver/states-not-separable")
    else:
        print(f"    → {len(seen)} distinct exit codes observed: "
              f"{', '.join(str(code) for code in sorted(seen))} — separable")
    return failures


# ──────────────────────────────── dispatch ──────────────────────────────────


def main(argv: list[str]) -> int:
    """Dispatch, converting ANY unexpected failure into TOOL ERROR (2).

    Without this, an unhandled exception would exit 1 -- indistinguishable from
    "violations found" -- and a caller would record a crashed checker as a
    document that merely needs fixing, or worse, as one that was checked.
    """
    try:
        return _dispatch(argv)
    except SystemExit:
        raise
    except BaseException:  # noqa: BLE001 -- deliberately total; see the docstring
        import traceback
        print("doclint.py: the checker itself failed; the documents are "
              "UNCHECKED (exit 2 = TOOL ERROR, not 'clean')", file=sys.stderr)
        traceback.print_exc()
        return TOOL_ERROR


def _dispatch(argv: list[str]) -> int:
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return TOOL_ERROR
    command, rest = argv[1], argv[2:]
    if command == "selftest":
        return selftest()
    index: set[str] = set()
    files: list[str] = []
    iterator = iter(rest)
    for argument in iterator:
        if argument == "--index":
            index.add(os.path.basename(next(iterator)))
        else:
            files.append(argument)
    if not files:
        print("doclint.py: no files given", file=sys.stderr)
        return TOOL_ERROR
    missing = [path for path in files if not os.path.isfile(path)]
    if missing:
        print("doclint.py: no such file(s): " + ", ".join(missing), file=sys.stderr)
        return TOOL_ERROR
    if command == "math-backticks":
        return check_math_backticks(files)
    if command == "define-terms":
        return check_define_terms(files)
    if command == "citations":
        return check_citations(files)
    if command == "doi-valid":
        return check_doi_valid(files)
    if command == "algorithms":
        return check_algorithms(files, index)
    if command == "code-snippets":
        return check_code_snippets(files)
    if command == "links":
        return check_links(files)
    print(f"doclint.py: unknown subcommand {command!r}", file=sys.stderr)
    return TOOL_ERROR


if __name__ == "__main__":
    sys.exit(main(sys.argv))
