//! Display-side FENCE-CAPTURE grouping.
//!
//! # The invariant
//!
//! Write a rule's surface template as a sequence of positions
//! `s_0, s_1, …, s_{m-1}`, each a LITERAL token or a CHILD slot. When the
//! parser reaches a child slot it must decide where that child's text ENDS.
//! For every slot that is not an outermost operand of a Pratt operator, it
//! decides lexically: it scans for the literal token that follows the slot in
//! the template. Call that token the slot's **right fence**.
//!
//! > **Fence-capture invariant.** A child's rendered text must not contain any
//! > of its right fences at bracket depth 0. If it does, the parser stops at the
//! > child's OWN fence occurrence instead of the rule's, and every token after
//! > that point is mis-assigned. `Display` must then wrap the child in
//! > PraTTaIL's transparent grouping `( … )`, which puts every occurrence at
//! > depth ≥ 1 and restores the boundary.
//!
//! The set of right fences by slot kind:
//!
//! | slot kind | right fences |
//! |---|---|
//! | interior plain child `… L₀ c L₁ …` | `{ L₁ }` |
//! | element of `c.*sep(S)` followed by `L` | `{ S, L }` — the list loop either CONTINUES on `S` or TERMINATES on `L` |
//! | leading / trailing operand of an infix, prefix or postfix rule | `∅` — see *Why operands are excluded* |
//!
//! This is the separator/keyword analogue of precedence-based
//! parenthesization. Where `min_bp` stops a looser infix operator from
//! capturing a tighter child, this stops a rule's own delimiter from capturing
//! part of a child.
//!
//! # Why it became reachable
//!
//! Until 2026-07-24 no RhoCalc `Proc` rendered a depth-0 comma: every comma in
//! the surface sat inside `(…)`, `[…]`, `{…}` or `#{…}#`. Aligning `new` with
//! official Rholang (`new x, y in { P }`, `grammar.js:89` /
//! `rholang_mercury.cf:72`) introduced the first one.
//!
//! The first casualty was a two-binder `new` used as an ELEMENT of a
//! comma-separated send, which rendered
//!
//! ```text
//! @Nil!(0 , new a , b in{Nil})
//! ```
//!
//! and re-parsed as four operands. That was fixed on 2026-07-24 by grouping
//! `.*sep(S)` elements.
//!
//! The SECOND casualty — this module's 2026-07-25 generalization — is the same
//! `new` in the slot that a `2Plus` send names EXPLICITLY rather than through
//! its repetition. `POutput2Plus`'s surface is
//!
//! ```text
//! "@" n "!" "(" a "," bs.*sep(",") ")"
//! ```
//!
//! and the hazardous slot is `a`, a plain child whose right fence is the
//! LITERAL `","` — not an element of the `.*sep` list at all. So
//! `POutputNil2Plus(PNew([a0,a1], PZero), [])` rendered
//!
//! ```text
//! @@Nil!(new a0 , a1 in{Nil},)
//! ```
//!
//! which does not parse (`gen_rhocalc_prop::name_display_parse_roundtrip`,
//! minimal input
//! `NQuote(POutput2Plus(NParen(NQuoteNil), PNew([a0,a1], PZero), []))`).
//! Grouping the slot fixes it:
//!
//! ```text
//! @@Nil!((new a0 , a1 in{Nil}),)
//! ```
//!
//! Official Rholang has the same hazard by construction (its `_proc_list` is
//! `commaSep($._proc)` and `new`'s decl list is `commaSep1($.name_decl)`), so
//! this is a property of the target syntax, not of our encoding of it.
//!
//! # Why operands are excluded
//!
//! For the leading operand of `a "|" b` the parser does NOT scan for `|`: it
//! runs the Pratt loop, and the boundary falls out of the binding-power
//! comparison. `Display` mirrors that with `own_left_bp < min_bp`
//! parenthesization. Applying fence capture there as well would emit
//! precedence-REDUNDANT parentheses, which the next parse discards — so the
//! canonical form would oscillate between `x | y | b` and `(x | y) | b` and
//! one-cycle Display idempotence would break (the exact failure analyzed in
//! `macros/src/gen/syntax/display.rs`, where the earlier
//! `shadowed_by_syntaxless_projection` disjunct was removed for this reason).
//! A slot is recognized as precedence-governed structurally: it is the FIRST
//! element of the template (no literal to its left) or the LAST (no literal to
//! its right).
//!
//! # Why bracket fences are vacuous
//!
//! [`has_bare_any`] consumes `(`, `[`, `{` as depth increments and `)`, `]`,
//! `}` as depth decrements; a bracket character is therefore never TESTED
//! against a fence. Since `Display` always emits balanced brackets, a fence
//! whose first character is a bracket can never match at depth 0, so the guard
//! is a constant `false`. The codegen skips emitting it for such fences — a
//! static optimization, not a semantic exception.
//!
//! # Why `(…)` is the right wrapper
//!
//! PraTTaIL gives every category a TRANSPARENT parenthesized grouping: `( P )`
//! parses to `P` itself with no wrapper AST node (verified for RhoCalc `Proc`:
//! `parse("(Nil)")` yields `PZero`, and
//! `parse("@Nil!(0, (new a, b in {Nil}))")` yields exactly the term whose
//! Display produced it). So grouping preserves the term, unlike a
//! language-specific block such as RhoCalc's `{ P }`, which would introduce a
//! singleton `PPar`.
//!
//! # Token boundaries
//!
//! A fence may be a WORD keyword (`in`, `where`, `then`, `else`). A raw
//! substring test would then fire on `internal`, `elsewhere`, … and group text
//! that the lexer never splits. [`has_bare_any`] therefore requires a token
//! boundary on any word-shaped edge of the fence, using the lexer's own
//! identifier-character rule (`is_alphanumeric() || '_'`,
//! `prattail/src/lexer.rs`). Every separator in the repo's grammars today
//! (`,` `|` `;` `&`) is non-word-shaped on both edges, so this guard is a no-op
//! for them and the pre-2026-07-25 behaviour is preserved byte for byte.
//!
//! # Safety
//!
//! [`group_if_bare_delims`] is a no-op unless the child genuinely carries a
//! fence at depth 0 — a situation in which the ungrouped text was already
//! mis-parsed. It can therefore only turn a broken roundtrip into a working
//! one; it can never break a roundtrip that worked. It is also idempotent as a
//! canonical form: the wrapped text's fences all sit at depth ≥ 1, so a second
//! Display of the re-parsed term produces the identical string.

/// Bracket pairs whose interior is "protected": a fence inside any of them is
/// already delimited and cannot be captured by an enclosing rule.
///
/// Both `{` `}` (blocks / maps / bags via `#{`…`}#`) and `{|` `|}` (pathmaps)
/// are covered by the plain brace entry, since their extra sigil characters
/// (`#`, `|`) are not themselves depth-carrying.
const BRACKETS: [(char, char); 3] = [('(', ')'), ('[', ']'), ('{', '}')];

/// The lexer's identifier-character class (`prattail/src/lexer.rs`): a keyword
/// literal glued to one of these re-lexes as a single `Ident`, so a word-shaped
/// fence only counts as a fence at a token boundary.
#[inline]
fn is_word_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// True iff `text` contains ANY of `delims` at bracket depth 0, outside string
/// literals, at a token boundary.
///
/// Depth is tracked over `()`, `[]` and `{}`. Double-quoted spans are skipped
/// wholesale (with `\` escapes honoured) so a delimiter inside a string literal
/// — `x!("a,b" , y)` — never forces a spurious grouping. A delimiter whose
/// first (resp. last) character is an identifier character only matches when
/// the character immediately before (resp. after) the occurrence is not an
/// identifier character, so the fence `in` does not match inside `internal`.
pub fn has_bare_any(text: &str, delims: &[&str]) -> bool {
    // Cheap pre-filter: if no delimiter occurs even as a raw substring, the
    // depth scan cannot find one.
    if !delims.iter().any(|d| !d.is_empty() && text.contains(d)) {
        return false;
    }
    let mut depth: i32 = 0;
    let mut in_string = false;
    let mut escaped = false;
    let mut prev: Option<char> = None;
    for (i, c) in text.char_indices() {
        if in_string {
            match (escaped, c) {
                (true, _) => escaped = false,
                (false, '\\') => escaped = true,
                (false, '"') => in_string = false,
                _ => {},
            }
            prev = Some(c);
            continue;
        }
        match c {
            '"' => in_string = true,
            _ if BRACKETS.iter().any(|(open, _)| *open == c) => depth += 1,
            _ if BRACKETS.iter().any(|(_, close)| *close == c) => depth -= 1,
            _ if depth == 0 => {
                let rest = &text[i..];
                for delim in delims {
                    if delim.is_empty() || !rest.starts_with(*delim) {
                        continue;
                    }
                    let left_ok = !delim.starts_with(is_word_char)
                        || !matches!(prev, Some(p) if is_word_char(p));
                    let right_ok = !delim.ends_with(is_word_char)
                        || !matches!(
                            text[i + delim.len()..].chars().next(),
                            Some(n) if is_word_char(n)
                        );
                    if left_ok && right_ok {
                        return true;
                    }
                }
            },
            _ => {},
        }
        prev = Some(c);
    }
    false
}

/// True iff `text` contains `sep` at bracket depth 0 — the single-fence form of
/// [`has_bare_any`], kept as the name the 2026-07-24 `.*sep(S)` call sites use.
pub fn has_bare_sep(text: &str, sep: &str) -> bool {
    has_bare_any(text, &[sep])
}

/// Wrap `text` in `(` … `)` iff any of its right fences would otherwise capture
/// part of it. Returns `text` unchanged in every other case.
///
/// See the module docs for why `(…)` is term-preserving and why the result is a
/// canonical fixed point.
pub fn group_if_bare_delims(text: &str, delims: &[&str]) -> String {
    match has_bare_any(text, delims) {
        true => {
            let mut out = String::with_capacity(text.len() + 2);
            out.push('(');
            out.push_str(text);
            out.push(')');
            out
        },
        false => text.to_string(),
    }
}

/// Single-fence form of [`group_if_bare_delims`].
pub fn group_if_bare_sep(text: &str, sep: &str) -> String {
    group_if_bare_delims(text, &[sep])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plain_text_is_untouched() {
        assert_eq!(group_if_bare_sep("Nil", ","), "Nil");
        assert_eq!(group_if_bare_sep("x!(0)", ","), "x!(0)");
    }

    #[test]
    fn separators_inside_brackets_do_not_count() {
        // The exact shapes that made every pre-2026-07-24 RhoCalc element safe.
        for s in ["x!(a,b)", "[1, 2]", "{k : v , j : w}", "f(g(a,b))", "#{a|b}#"] {
            assert!(!has_bare_sep(s, ","), "{s} has no DEPTH-0 comma");
            assert_eq!(group_if_bare_sep(s, ","), s);
        }
    }

    #[test]
    fn a_depth_zero_separator_forces_grouping() {
        // The `new` decl list — the case this exists for.
        assert!(has_bare_sep("new a , b in{Nil}", ","));
        assert_eq!(group_if_bare_sep("new a , b in{Nil}", ","), "(new a , b in{Nil})");
    }

    #[test]
    fn a_single_binder_new_needs_no_grouping() {
        assert_eq!(group_if_bare_sep("new a in{Nil}", ","), "new a in{Nil}");
    }

    #[test]
    fn separators_inside_string_literals_do_not_count() {
        assert!(!has_bare_sep(r#"x!("a,b")"#, ","));
        assert!(!has_bare_sep(r#""a,b""#, ","));
        // an escaped quote must not end the string span early
        assert!(!has_bare_sep(r#""a\",b""#, ","));
    }

    #[test]
    fn works_for_non_comma_separators() {
        assert!(has_bare_sep("a | b", "|"));
        assert!(!has_bare_sep("{a | b}", "|"));
        assert_eq!(group_if_bare_sep("a & b", "&"), "(a & b)");
    }

    #[test]
    fn multi_char_separators_are_matched_whole() {
        assert!(has_bare_sep("a <- b", "<-"));
        assert!(!has_bare_sep("f(a <- b)", "<-"));
    }

    #[test]
    fn unbalanced_close_brackets_do_not_panic() {
        // Defensive: Display never emits these, but the scan must stay total.
        let _ = has_bare_sep(")))", ",");
        let _ = has_bare_sep("a),b", ",");
    }

    // ── 2026-07-25 generalization: multi-fence + word-shaped fences ─────────

    #[test]
    fn any_of_several_fences_triggers_grouping() {
        // A `.*sep(",")` element followed by the literal `in` has BOTH as fences.
        assert!(has_bare_any("a , b", &[",", "in"]));
        assert!(has_bare_any("x in y", &[",", "in"]));
        assert!(!has_bare_any("f(a , b in c)", &[",", "in"]));
        assert_eq!(group_if_bare_delims("x in y", &[",", "in"]), "(x in y)");
        assert_eq!(group_if_bare_delims("Nil", &[",", "in"]), "Nil");
    }

    #[test]
    fn word_fences_only_match_at_token_boundaries() {
        // The whole point: a keyword fence must not fire inside an identifier.
        assert!(!has_bare_sep("internal", "in"));
        assert!(!has_bare_sep("win", "in"));
        assert!(!has_bare_sep("a_in_b", "in"));
        assert!(!has_bare_sep("elsewhere", "else"));
        // …but it must still fire on the real token.
        assert!(has_bare_sep("new a in{Nil}", "in"));
        assert!(has_bare_sep("in x", "in"));
        assert!(has_bare_sep("x in", "in"));
        assert!(has_bare_sep("a then b", "then"));
    }

    #[test]
    fn non_word_fences_are_unaffected_by_the_boundary_rule() {
        // Every separator in the repo's grammars is non-word on both edges, so
        // the 2026-07-25 boundary guard must be byte-for-byte inert for them.
        assert!(has_bare_sep("a,b", ","));
        assert!(has_bare_sep("a|b", "|"));
        assert!(has_bare_sep("a;b", ";"));
        assert!(has_bare_sep("a&b", "&"));
        assert!(has_bare_sep("a<-b", "<-"));
    }

    #[test]
    fn bracket_fences_are_vacuous() {
        // Why the codegen may skip emitting the guard for a bracket fence.
        for balanced in ["f(a)", "[1, 2]", "{x}", "new a in{Nil}", "@Nil!(0)"] {
            for fence in ["(", ")", "[", "]", "{", "}"] {
                assert!(
                    !has_bare_sep(balanced, fence),
                    "{fence:?} must be vacuous on balanced text {balanced:?}"
                );
            }
        }
    }

    #[test]
    fn grouping_is_a_canonical_fixed_point() {
        // Wrapping puts every fence at depth >= 1, so a second pass is a no-op.
        let once = group_if_bare_sep("new a , b in{Nil}", ",");
        assert_eq!(group_if_bare_sep(&once, ","), once);
    }

    #[test]
    fn utf8_text_is_scanned_by_character_not_byte() {
        // Multi-byte identifiers must not be split mid-character, and a
        // word-shaped fence must respect non-ASCII identifier characters.
        assert!(!has_bare_sep("λin", "in"));
        assert!(has_bare_sep("λ , x", ","));
        assert!(!has_bare_sep("(λ , x)", ","));
    }
}
