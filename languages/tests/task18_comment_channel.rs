//! Task #18 gate — comments are LEXED to the retained `COMMENTS` channel, not stripped.
//!
//! Comments used to be removed by a PRE-PARSE STRING STRIP in the `rhocalc` interpreter binary
//! (`strip_comments`, now retired in place with a rationale). That was lossy: source positions
//! shifted, the text was unrecoverable, and no consumer could ever see a comment. They are now
//! ordinary tokens declared in the RhoCalc grammar's `tokens {}` block and routed to the
//! alternative channel `COMMENTS` (`languages/src/rhocalc.rs`).
//!
//! The mechanism under test is GENERAL — `-> CHANNEL` on any token of any grammar — and rests on
//! ONE rule, applied where the lexer already skipped whitespace:
//!
//! > A channel-routed token is TRIVIA. The scanner resolves it by the same MAXIMAL MUNCH rule as
//! > every other token; when it wins, its span is consumed but never delivered to the parse
//! > stream. It is retained, with its source `Range`, in `LexResult.streams[CHANNEL]`.
//!
//! Four obligations are gated here.
//!
//! 1. **Retention** — the comment text and its source position survive on the channel
//!    (`retention_*`), readable through the ANTLR4-parity reader (`reader_api_*`).
//! 2. **Non-perturbation** — a commented program and its comment-free twin elect the SAME AST,
//!    lex to the SAME `DEFAULT` token sequence, and — the load-bearing fence — yield the SAME
//!    PARSE COUNT. This grammar has a documented 14 ms → 109 s frontier-explosion incident, so an
//!    ambiguity regression is the hazard: `//` competes with the `Div` terminal `"/"` at the same
//!    position, and maximal munch (not a new disambiguation) is what settles it (`unperturbed_*`).
//! 3. **The FLT / modal interaction** — the guest modes are RAW and declare their own tokens; the
//!    comment tokens exist ONLY in the default mode, so a comment marker inside a `` ` ``, ```` ```
//!    ```` or `box{…}` guest body is verbatim GUEST TEXT and must never be eaten as a host
//!    comment (`flt_*`). This is the sharpest failure mode of the change.
//! 4. **The accepted comment language is exactly what the strip removed** — flat (non-nested)
//!    C-style block comments, `//` to end of line, markers inert inside strings (`language_*`).

use mettail_languages::rhocalc::{self, Proc};
use mettail_runtime::FltNode;

/// The conventional channel name the RhoCalc grammar routes its comment tokens to.
const COMMENTS: &str = "COMMENTS";

/// The `DEFAULT` (parse-stream) token sequence, positions dropped — what the parser consumes.
fn default_tokens(source: &str) -> Vec<String> {
    rhocalc::lex(source)
        .unwrap_or_else(|e| panic!("lex {source:?}: {e}"))
        .into_iter()
        .map(|(token, _range)| format!("{token:?}"))
        .collect()
}

/// Every comment retained on `COMMENTS`, as `(verbatim text, 1-based line, 1-based column)`.
fn retained_comments(source: &str) -> Vec<(String, usize, usize)> {
    let lexed = rhocalc::lex_with_streams(source)
        .unwrap_or_else(|e| panic!("lex_with_streams {source:?}: {e}"));
    lexed
        .tokens_on_channel(COMMENTS)
        .iter()
        .map(|(_token, range)| {
            (
                source[range.start.byte_offset..range.end.byte_offset].to_string(),
                range.start.line + 1,
                range.start.column + 1,
            )
        })
        .collect()
}

/// The elected term's structure, UP TO FRESH-BINDER RENAMING.
///
/// `Debug` prints each free binder's `UniqueId(n)`, and `n` comes from a monotonically increasing
/// process-global counter that `clear_var_cache` does NOT rewind (clearing the name→id cache means
/// the next parse MINTS a new id rather than reusing the cached one). So two parses of the very
/// same source print different ids purely by ordinal position in the process — nothing to do with
/// comments. Erasing the ordinal compares the terms up to fresh-binder renaming, which is exactly
/// what "the same AST" means for a binder-carrying term; every other structural detail — the
/// constructor tree, and each bound occurrence's de-Bruijn `ScopeOffset`/`BinderIndex`, which is
/// the part that actually witnesses correct binding — is preserved verbatim.
fn parse_debug(source: &str) -> String {
    mettail_runtime::clear_var_cache();
    let term = Proc::parse(source).unwrap_or_else(|e| panic!("parse {source:?}: {e}"));
    let rendered = format!("{term:?}");
    let mut normalized = String::with_capacity(rendered.len());
    let mut rest = rendered.as_str();
    while let Some(at) = rest.find("UniqueId(") {
        normalized.push_str(&rest[..at]);
        normalized.push_str("UniqueId(_");
        rest = &rest[at + "UniqueId(".len()..];
        let digits = rest
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(rest.len());
        rest = &rest[digits..];
    }
    normalized.push_str(rest);
    normalized
}

/// The elected term's SURFACE rendering — independent evidence of AST equality that never mentions
/// a binder ordinal at all.
fn parse_display(source: &str) -> String {
    mettail_runtime::clear_var_cache();
    let term = Proc::parse(source).unwrap_or_else(|e| panic!("parse {source:?}: {e}"));
    format!("{term}")
}

fn parse_count(source: &str) -> usize {
    mettail_runtime::clear_var_cache();
    Proc::parse_via_wpda_all(source)
        .unwrap_or_else(|e| panic!("parse_via_wpda_all {source:?}: {e:?}"))
        .len()
}

fn flt_node(term: &Proc) -> &FltNode {
    match term {
        Proc::PFlt(n) | Proc::PFltFence(n) | Proc::PFltBrace(n) => n,
        other => panic!("expected a PFlt* variant, got {other:?}"),
    }
}

// ── 1. RETENTION — the comment survives, with its source position ────────────────────────────────

#[test]
fn retention_line_comment_is_retained_with_its_source_position() {
    // Byte layout: line 1 is `{0 | 1} // trailing`, so the comment starts at column 9 (1-based).
    let source = "{0 | 1} // trailing\n";
    assert_eq!(
        retained_comments(source),
        vec![("// trailing".to_string(), 1, 9)],
        "the line comment must be RETAINED verbatim on the COMMENTS channel, at its true position \
         — this is precisely what the pre-parse strip destroyed"
    );
}

#[test]
fn retention_position_is_the_true_source_position_on_a_later_line() {
    let source = "// header\n{0 |\n  1} // tail\n";
    assert_eq!(
        retained_comments(source),
        vec![("// header".to_string(), 1, 1), ("// tail".to_string(), 3, 6)],
        "positions must index the ORIGINAL source; the strip shifted them by deleting bytes"
    );
}

#[test]
fn retention_block_comment_spanning_lines_is_retained_whole() {
    let source = "{0 /* spans\n   two lines */ | 1}";
    assert_eq!(
        retained_comments(source),
        vec![("/* spans\n   two lines */".to_string(), 1, 4)],
        "a multi-line block comment is ONE token spanning the newline"
    );
}

#[test]
fn retention_multiple_comments_arrive_in_source_order() {
    let source = "// a\n{0 /* b */ | 1} // c\n";
    let texts: Vec<String> = retained_comments(source)
        .into_iter()
        .map(|(t, _, _)| t)
        .collect();
    assert_eq!(texts, vec!["// a", "/* b */", "// c"]);
}

#[test]
fn retention_an_uncommented_program_retains_nothing() {
    assert!(
        retained_comments("{0 | 1}").is_empty(),
        "no comments ⇒ an empty channel, not an error"
    );
}

// ── 2. NON-PERTURBATION — the parse is byte-for-byte the parse of the comment-free twin ──────────

/// Commented / comment-free program pairs. Each pair must be indistinguishable to the parser.
const TWINS: &[(&str, &str)] = &[
    ("{0 | 1} // trailing", "{0 | 1}"),
    ("// leading\n{0 | 1}", "{0 | 1}"),
    ("{0 /* inline */ | 1}", "{0 | 1}"),
    ("{0 |/* tight */1}", "{0 |1}"),
    ("new x in { x!(0) } // done", "new x in { x!(0) }"),
    ("/* a */ new x in { /* b */ x!(0) /* c */ } /* d */", "new x in { x!(0) }"),
    ("@a!(0,1) // ambiguous send", "@a!(0,1)"),
];

#[test]
fn unperturbed_commented_and_uncommented_elect_the_same_ast() {
    for (commented, plain) in TWINS {
        assert_eq!(
            parse_debug(commented),
            parse_debug(plain),
            "the elected AST must be IDENTICAL for {commented:?} and {plain:?}"
        );
        assert_eq!(
            parse_display(commented),
            parse_display(plain),
            "…and so must its surface rendering, for {commented:?} and {plain:?}"
        );
    }
}

#[test]
fn unperturbed_parse_count_is_unchanged() {
    // ★ The ambiguity fence. Routing comments through the lexer must not add a single reading:
    // trivia only ever REMOVES a span from the scan, it never contributes an alternative. This
    // grammar has a documented 14 ms → 109 s frontier-explosion incident, so a parse-count drift
    // here is the regression to catch — including for `@a!(0,1)`, which is genuinely 2-ways
    // ambiguous and must stay exactly 2-ways ambiguous.
    for (commented, plain) in TWINS {
        assert_eq!(
            parse_count(commented),
            parse_count(plain),
            "the PARSE COUNT must be identical for {commented:?} and {plain:?}"
        );
    }
}

#[test]
fn unperturbed_default_token_stream_is_identical() {
    for (commented, plain) in TWINS {
        assert_eq!(
            default_tokens(commented),
            default_tokens(plain),
            "the DEFAULT token stream must be identical for {commented:?} and {plain:?}"
        );
    }
}

#[test]
fn unperturbed_no_comment_token_ever_reaches_the_default_stream() {
    let source = "// header\n{0 /* inline */ | 1} // tail";
    let lexed = rhocalc::lex_with_streams(source).expect("lex_with_streams");
    for (token, _range) in &lexed.tokens {
        let rendered = format!("{token:?}");
        assert!(
            !rendered.contains("LineComment") && !rendered.contains("BlockComment"),
            "a COMMENTS-channel token leaked onto DEFAULT: {rendered}"
        );
    }
    assert_eq!(
        lexed.tokens_on_channel(COMMENTS).len(),
        3,
        "…while all three comments ARE retained off-stream"
    );
}

#[test]
fn unperturbed_division_still_lexes_as_division() {
    // `//` beats `/` by MAXIMAL MUNCH — the same rule that separates every other token pair, not a
    // new disambiguation. A single `/` must therefore still be the `Div` terminal.
    let with_division = "@Nil!(@Nil!() / @Nil!())";
    assert!(
        retained_comments(with_division).is_empty(),
        "a lone `/` is division, never the start of a comment"
    );
    assert_eq!(
        parse_debug(with_division),
        parse_debug("@Nil!(@Nil!() / @Nil!()) // and a comment"),
        "adding a comment to a program containing division must not perturb it"
    );
}

#[test]
fn unperturbed_display_does_not_reemit_comments() {
    // ★ The honest answer to "does it round-trip through Display?": NO, and it CANNOT. A comment is
    // routed OFF `DEFAULT`, so no AST node carries it and `Display` has nothing to re-emit. The
    // round trip that the channel provides is `source → COMMENTS channel` (asserted by the
    // retention tests above), NOT `source → AST → source`. Re-emitting a comment is a FORMATTER's
    // job, and the primitive it needs is `hidden_tokens_to_left/right`, gated below.
    mettail_runtime::clear_var_cache();
    let term = Proc::parse("{0 | 1} // trailing").expect("parse");
    let rendered = format!("{term}");
    assert!(
        !rendered.contains("//") && !rendered.contains("trailing"),
        "Display must NOT re-emit a comment (it has no AST node to render): {rendered}"
    );
}

// ── 3. THE FLT / MODAL INTERACTION — a marker in a RAW guest body is GUEST TEXT ──────────────────

#[test]
fn flt_line_comment_marker_inside_a_backtick_guest_body_is_guest_text() {
    // The guest modes are RAW and declare their own tokens (`GuestChunk`, `Hole`, the closer); the
    // host comment tokens live ONLY in the default mode. So `//` inside a guest body can never be
    // lexed as a host comment — it is the guest's own bytes.
    mettail_runtime::clear_var_cache();
    let term = Proc::parse("lam`App(a // b, c)`").expect("backtick FLT with a `//` in the body");
    assert_eq!(
        flt_node(&term).body_src,
        "App(a // b, c)",
        "the guest body must survive VERBATIM, `//` included"
    );
    assert!(
        retained_comments("lam`App(a // b, c)`").is_empty(),
        "nothing inside a guest body may be routed to the host COMMENTS channel"
    );
}

#[test]
fn flt_block_comment_marker_inside_a_backtick_guest_body_is_guest_text() {
    mettail_runtime::clear_var_cache();
    let term = Proc::parse("lam`App(/* not a comment */ x, y)`").expect("backtick FLT");
    assert_eq!(flt_node(&term).body_src, "App(/* not a comment */ x, y)");
    assert!(retained_comments("lam`App(/* not a comment */ x, y)`").is_empty());
}

#[test]
fn flt_comment_marker_inside_a_fence_guest_body_is_guest_text() {
    mettail_runtime::clear_var_cache();
    let source = "lam```App(a // b, c)```";
    let term = Proc::parse(source).expect("fence FLT with a `//` in the body");
    assert_eq!(flt_node(&term).body_src, "App(a // b, c)");
    assert!(retained_comments(source).is_empty());
}

#[test]
fn flt_comment_marker_inside_a_brace_guest_body_is_guest_text() {
    mettail_runtime::clear_var_cache();
    let source = "box{App(a // b, c)}";
    let term = Proc::parse(source).expect("brace FLT with a `//` in the body");
    assert_eq!(flt_node(&term).body_src, "App(a // b, c)");
    assert!(retained_comments(source).is_empty());
}

#[test]
fn flt_guest_body_with_a_marker_holds_its_typed_holes() {
    // The guest body's `${…}` holes must still be recognized when a comment marker sits beside
    // them — routing must not disturb the RAW mode's own tokenization at all.
    mettail_runtime::clear_var_cache();
    let term = Proc::parse("lam`App(${f} // pick, K)`").expect("backtick FLT with hole + marker");
    let node = flt_node(&term);
    assert_eq!(node.body_src, "App(${f} // pick, K)");
    assert_eq!(node.holes.len(), 1, "the typed hole must still bind");
    assert_eq!(node.holes[0].name, "f");
}

#[test]
fn flt_a_host_comment_may_CONTAIN_an_flt_opener_without_opening_a_guest_mode() {
    // The mirror direction: a comment is the maximal munch at `//`, so the mode map never sees the
    // backtick inside it and no guest mode is pushed. Without this, an unbalanced backtick in a
    // comment (the demo files are FULL of them) would report an unterminated guest region.
    let source = "// mentions lam`App(x, y)` in prose\n{0 | 1}";
    assert_eq!(
        retained_comments(source),
        vec![("// mentions lam`App(x, y)` in prose".to_string(), 1, 1)],
        "the whole line is ONE comment token — the backticks inside it are comment bytes"
    );
    assert_eq!(parse_debug(source), parse_debug("{0 | 1}"));
}

#[test]
fn flt_a_host_comment_may_contain_an_unbalanced_backtick() {
    let source = "// one unbalanced ` backtick\n{0 | 1}";
    assert_eq!(parse_debug(source), parse_debug("{0 | 1}"));
}

// ── 4. THE ACCEPTED COMMENT LANGUAGE — exactly what the strip removed ────────────────────────────

#[test]
fn language_marker_inside_a_string_literal_is_string_content() {
    // `StringLit` is a single maximal-munch span from `"` to `"`, so a marker inside it is never at
    // a token-start position and can never be trivia. This is the strip's `State::Str` guard,
    // obtained for free from the DFA.
    let source = "@\"a // b\"!(0)";
    assert!(
        retained_comments(source).is_empty(),
        "a `//` inside a string literal is string bytes, not a comment"
    );
    assert_eq!(
        default_tokens(source),
        default_tokens("@\"a // b\"!(0)"),
        "the string literal must lex identically"
    );
}

#[test]
fn language_block_comment_markers_inside_a_string_literal_are_string_content() {
    assert!(retained_comments("@\"a /* b */ c\"!(0)").is_empty());
}

#[test]
fn language_line_comment_runs_to_end_of_line_only() {
    let source = "// first\n{0 | 1}\n";
    assert_eq!(
        retained_comments(source),
        vec![("// first".to_string(), 1, 1)],
        "the comment stops at the newline — it must not swallow the program"
    );
    assert_eq!(parse_debug(source), parse_debug("{0 | 1}"));
}

#[test]
fn language_line_comment_may_end_at_end_of_input() {
    let source = "{0 | 1} // no trailing newline";
    assert_eq!(retained_comments(source).len(), 1);
    assert_eq!(parse_debug(source), parse_debug("{0 | 1}"));
}

#[test]
fn language_block_comment_is_FLAT_closing_at_the_first_close_marker() {
    // The convention is Rholang/C flat, NOT nested — and it is deliberately IDENTICAL to what the
    // retired strip did (it too closed at the first `*/`). `/* /* */` therefore closes at the
    // inner `*/`, leaving the trailing ` */` as code, which does not parse.
    let source = "{0 /* /* */ */ | 1}";
    assert_eq!(
        retained_comments(source),
        vec![("/* /* */".to_string(), 1, 4)],
        "the FIRST `*/` closes the block comment"
    );
    mettail_runtime::clear_var_cache();
    assert!(
        Proc::parse(source).is_err(),
        "the leftover `*/` is code and must not parse — pinning the FLAT (non-nested) convention"
    );
}

#[test]
fn language_unterminated_block_comment_fails_closed() {
    // ★ The ONE deliberate behaviour change vs. the retired strip, which swallowed an unterminated
    // `/*` SILENTLY to EOF — so `{0 | 1} /* never closed` used to evaluate as though the tail were
    // not there at all. Now it fails closed.
    //
    // Note precisely WHERE it fails: not in the lexer. `BlockComment` needs its closing `*/`, so
    // with no close marker the maximal munch at `/` falls back to the `Div` terminal and the tail
    // lexes as ordinary tokens; the failure surfaces at the PARSE, reported through the
    // interpreter's existing exit code 65. What matters is that the program no longer runs with a
    // silently-truncated tail, and that the unterminated text is NOT reported as a comment.
    let source = "{0 | 1} /* never closed";
    mettail_runtime::clear_var_cache();
    assert!(
        Proc::parse(source).is_err(),
        "an unterminated block comment must FAIL rather than silently swallow the rest of the file"
    );
    assert!(
        retained_comments(source).is_empty(),
        "an unterminated block comment is not a comment — nothing may be retained for it"
    );
}

#[test]
fn language_an_empty_block_comment_lexes() {
    let source = "{0 /**/ | 1}";
    assert_eq!(retained_comments(source), vec![("/**/".to_string(), 1, 4)]);
    assert_eq!(parse_debug(source), parse_debug("{0 | 1}"));
}

#[test]
fn language_a_comment_may_contain_non_ascii_text() {
    // The negated classes complement over the FULL 0..=255 byte range, so UTF-8 lead/continuation
    // bytes are members and a comment is never truncated at the first multi-byte character. The
    // committed demo files' box-drawing rules and `λ`/`⟦…⟧` glyphs depend on this.
    let source = "// ═══ λ ⟦x⟧ ─── ═══\n{0 | 1}";
    assert_eq!(
        retained_comments(source),
        vec![("// ═══ λ ⟦x⟧ ─── ═══".to_string(), 1, 1)],
        "a comment must carry arbitrary UTF-8 text to its end of line"
    );
    assert_eq!(parse_debug(source), parse_debug("{0 | 1}"));
}

// ── The ANTLR4-parity reader — the primitive a formatter/LSP re-attaches comments with ───────────

#[test]
fn reader_api_tokens_on_channel_is_generic_over_the_channel_name() {
    let lexed = rhocalc::lex_with_streams("// a\n{0 | 1}").expect("lex_with_streams");
    assert_eq!(lexed.tokens_on_channel(COMMENTS).len(), 1);
    assert!(
        lexed.tokens_on_channel("PRAGMAS").is_empty(),
        "an undeclared channel yields an empty slice, never an error — there is no registry and \
         no privileged channel name"
    );
    assert_eq!(lexed.channels().collect::<Vec<_>>(), vec![COMMENTS]);
}

#[test]
fn reader_api_hidden_tokens_attach_a_comment_to_its_neighbouring_token() {
    //   `// header` precedes DEFAULT token 0; `// tail` follows the last DEFAULT token.
    let source = "// header\n{0 | 1}\n// tail\n";
    let lexed = rhocalc::lex_with_streams(source).expect("lex_with_streams");

    let leading = lexed.hidden_tokens_to_left(0, COMMENTS);
    assert_eq!(leading.len(), 1, "the file header attaches to the FIRST default token");
    assert_eq!(
        &source[leading[0].1.start.byte_offset..leading[0].1.end.byte_offset],
        "// header"
    );

    // The last DEFAULT entry is `Eof`; the token before it is the closing `}`.
    let last_real = lexed.tokens.len() - 2;
    let trailing = lexed.hidden_tokens_to_right(last_real, COMMENTS);
    assert_eq!(trailing.len(), 1, "the trailing comment attaches to the LAST real token");
    assert_eq!(
        &source[trailing[0].1.start.byte_offset..trailing[0].1.end.byte_offset],
        "// tail"
    );
}

// ── Cross-path agreement — the retention scan and the parse scan must never drift ───────────────

/// Sources exercising every interaction: comments, division, strings, guest bodies, holes.
const CORPUS: &[&str] = &[
    "{0 | 1}",
    "{0 | 1} // trailing",
    "// leading\n{0 | 1}",
    "{0 /* inline */ | 1}",
    "// a\n{0 /* b */ | 1} // c\n",
    "@Nil!(@Nil!() / @Nil!())",
    "@Nil!(@Nil!() / @Nil!()) // division plus a comment",
    "@\"a // b\"!(0)",
    "lam`App(a // b, c)`",
    "lam`App(${f} // pick, K)`",
    "box{App(a // b, c)}",
    "lam```App(a // b, c)```",
    "new x in { x!(0) } /* multi\n   line */",
    "// ═══ λ ⟦x⟧ ═══\n{0 | 1}",
];

#[test]
fn cross_path_retention_scan_and_plain_lex_agree_on_the_default_stream() {
    // ★ `lex()` (which the DEFAULT path shares its tables with) and `lex_with_streams()` (the
    // retention entry) are two generated scan loops reading the SAME `stream_id_*` tables under the
    // SAME maximal-munch rule. This gate pins that they cannot drift: for every source, the
    // `DEFAULT` stream they produce must be identical DOWN TO THE SOURCE RANGES. If retention ever
    // disagreed with the parse about where a comment lies, a tool would re-attach comments to the
    // wrong tokens — silently.
    for source in CORPUS {
        let plain = rhocalc::lex(source).unwrap_or_else(|e| panic!("lex {source:?}: {e}"));
        let streamed = rhocalc::lex_with_streams(source)
            .unwrap_or_else(|e| panic!("lex_with_streams {source:?}: {e}"));
        assert_eq!(
            plain.len(),
            streamed.tokens.len(),
            "DEFAULT token COUNT diverges between lex() and lex_with_streams() for {source:?}"
        );
        for (index, ((left, left_range), (right, right_range))) in
            plain.iter().zip(streamed.tokens.iter()).enumerate()
        {
            assert_eq!(
                format!("{left:?}"),
                format!("{right:?}"),
                "DEFAULT token {index} diverges for {source:?}"
            );
            assert_eq!(
                (left_range.start.byte_offset, left_range.end.byte_offset),
                (right_range.start.byte_offset, right_range.end.byte_offset),
                "DEFAULT token {index}'s source range diverges for {source:?}"
            );
        }
    }
}

#[test]
fn cross_path_every_source_byte_is_a_default_token_a_comment_or_whitespace() {
    // A coverage argument for the whole corpus: partition each source by the spans the two streams
    // claim. Anything left over must be pure whitespace. This is what "nothing was silently
    // dropped" means — the strip's failure mode was exactly a class of bytes vanishing with no
    // record, and this test would catch its return.
    for source in CORPUS {
        let lexed = rhocalc::lex_with_streams(source)
            .unwrap_or_else(|e| panic!("lex_with_streams {source:?}: {e}"));
        let mut claimed = vec![false; source.len()];
        let mut claim = |range: &mettail_prattail::runtime_types::Range| {
            for byte in range.start.byte_offset..range.end.byte_offset.min(source.len()) {
                claimed[byte] = true;
            }
        };
        for (_token, range) in &lexed.tokens {
            claim(range);
        }
        for (_token, range) in lexed.tokens_on_channel(COMMENTS) {
            claim(range);
        }
        let unclaimed: String = source
            .char_indices()
            .filter(|(byte, _)| !claimed[*byte])
            .map(|(_, character)| character)
            .collect();
        assert!(
            unclaimed.chars().all(char::is_whitespace),
            "these bytes of {source:?} are neither a DEFAULT token nor a retained comment nor \
             whitespace — they were silently dropped: {unclaimed:?}"
        );
    }
}

#[test]
fn reader_api_hidden_tokens_are_empty_where_no_trivia_sits() {
    let lexed = rhocalc::lex_with_streams("{0 | 1}").expect("lex_with_streams");
    assert!(lexed.hidden_tokens_to_left(0, COMMENTS).is_empty());
    assert!(lexed.hidden_tokens_to_right(0, COMMENTS).is_empty());
    assert!(
        lexed.hidden_tokens_to_left(9_999, COMMENTS).is_empty(),
        "an out-of-range index yields an empty slice, not a panic"
    );
}
