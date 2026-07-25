//! Display-side SEPARATOR-CAPTURE grouping.
//!
//! # The invariant
//!
//! A `Display` implementation that renders a `.*sep(S)` repetition joins its
//! elements with `S`. That text only re-parses if no ELEMENT contains `S` at
//! bracket depth 0 — otherwise the parser splits the list at the element's own
//! separator and both halves become garbage.
//!
//! This is the separator analogue of precedence-based parenthesization. Where
//! `min_bp` stops a looser infix operator from capturing a tighter child, this
//! stops a list separator from capturing part of an element.
//!
//! # Why it became reachable
//!
//! Until 2026-07-24 no RhoCalc `Proc` rendered a depth-0 comma: every comma in
//! the surface sat inside `(…)`, `[…]`, `{…}` or `#{…}#`. Aligning `new` with
//! official Rholang (`new x, y in { P }`, `grammar.js:89` / `rholang_mercury.cf:72`)
//! introduced the first one. A two-binder `new` nested in a comma-separated send
//! then rendered
//!
//! ```text
//! @Nil!(0 , new a , b in{Nil})
//! ```
//!
//! which re-parses as the four operands `0`, `new a`, `b in{Nil}` — a broken
//! Display→parse roundtrip. Grouping the element fixes it:
//!
//! ```text
//! @Nil!(0 , (new a , b in{Nil}))
//! ```
//!
//! Official Rholang has the same hazard by construction (its `_proc_list` is
//! `commaSep($._proc)` and `new`'s decl list is `commaSep1($.name_decl)`), so
//! this is a property of the target syntax, not of our encoding of it.
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
//! # Safety
//!
//! [`group_if_bare_sep`] is a no-op unless the element genuinely contains the
//! separator at depth 0 — a situation in which the ungrouped text was already
//! unparseable. It can therefore only turn a broken roundtrip into a working
//! one; it can never break a roundtrip that worked.

/// Bracket pairs whose interior is "protected": a separator inside any of them
/// is already delimited and cannot be captured by an enclosing list.
///
/// Both `{` `}` (blocks / maps / bags via `#{`…`}#`) and `{|` `|}` (pathmaps)
/// are covered by the plain brace entry, since their extra sigil characters
/// (`#`, `|`) are not themselves depth-carrying.
const BRACKETS: [(char, char); 3] = [('(', ')'), ('[', ']'), ('{', '}')];

/// True iff `text` contains `sep` at bracket depth 0, outside string literals.
///
/// Depth is tracked over `()`, `[]` and `{}`. Double-quoted spans are skipped
/// wholesale (with `\` escapes honoured) so a separator inside a string literal
/// — `x!("a,b" , y)` — never forces a spurious grouping.
pub fn has_bare_sep(text: &str, sep: &str) -> bool {
    if sep.is_empty() || !text.contains(sep) {
        return false;
    }
    let bytes = text.as_bytes();
    let sep_bytes = sep.as_bytes();
    let mut depth: i32 = 0;
    let mut in_string = false;
    let mut i = 0usize;
    while i < bytes.len() {
        let c = bytes[i] as char;
        if in_string {
            match c {
                '\\' => i += 1, // skip the escaped byte
                '"' => in_string = false,
                _ => {},
            }
            i += 1;
            continue;
        }
        match c {
            '"' => in_string = true,
            _ => {
                if let Some((_, _)) = BRACKETS.iter().find(|(o, _)| *o == c) {
                    depth += 1;
                } else if BRACKETS.iter().any(|(_, cl)| *cl == c) {
                    depth -= 1;
                } else if depth == 0 && bytes[i..].starts_with(sep_bytes) {
                    return true;
                }
            },
        }
        i += 1;
    }
    false
}

/// Wrap `text` in `(` … `)` iff it would otherwise be split by an enclosing
/// `sep`-joined list. Returns `text` unchanged in every other case.
///
/// See the module docs for why `(…)` is term-preserving.
pub fn group_if_bare_sep(text: &str, sep: &str) -> String {
    match has_bare_sep(text, sep) {
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
}
