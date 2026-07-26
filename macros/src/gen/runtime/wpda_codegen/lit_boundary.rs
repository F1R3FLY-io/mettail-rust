//! THE TOKEN-BOUNDARY ALPHABET — *a fixed literal must not match INSIDE a longer token.*
//!
//! # The rule, and the half of it that was missing
//!
//! The `@`-projection isolation helper ([`super::facade`]) matches a grammar-derived
//! skeleton (`@ ⟨n⟩ ! ( ⟨q⟩ )`, `- ⟨a⟩`, …) against the RAW input string, before any
//! lexing. Every fixed literal in that skeleton is a TOKEN, so it may only match where
//! the lexer would actually produce that token — never in the middle of a longer one.
//!
//! The helper already stated that rule and implemented **one half** of it: an
//! IDENT-SHAPED literal was required to sit in its own word run,
//!
//! ```text
//!     before_ok = p == 0     || !is_word(bytes[p - 1])
//!     after_ok  = p + |l| == n || !is_word(bytes[p + |l|])
//! ```
//!
//! — *"Word-boundary for identifier-shaped terminals (`or`, `and`, `bitor`) so `or` does
//! not match inside `error`/`for`"* (the infix facade's own comment; the projection
//! matcher carries the same test). A PUNCTUATION sigil got no test at all, on the
//! unstated assumption that punctuation is never inside a longer token.
//!
//! That assumption is false exactly when a literal token pattern carries the sigil. In
//! RhoCalc — and in consensus Rholang, whose tree-sitter grammar it mirrors — the sign
//! is part of the numeral:
//!
//! ```text
//!     Int   = -?(…digits…)(i32|i64)?  |  (…digits…)u32
//!     BigInt/BigRat/Float/Fixed        …all leading `-?`
//! ```
//!
//! so in `-7n` the maximal munch at byte 0 is the three-byte `BigInt("-7n")`, and the
//! one-byte `Minus` the skeleton `NegProc . a:Proc |- "-" a` wants is a PROPER PREFIX of
//! it. Matching it frames `-7n` as `- ⟨7n⟩` and destroys the adjacency the lexer
//! preserved — the whole-input half of the sign-abutted numeral divergence from f1r3node.
//!
//! # What this module computes
//!
//! For each literal `l` the projection skeletons use, two byte sets derived from the
//! language's OWN token alphabet — no hardcoded sigil, no per-language special case:
//!
//! | set      | membership of byte `b`                              | meaning |
//! |----------|-----------------------------------------------------|---------|
//! | `ext(l)` | `l · b` is a viable prefix of some token             | `b` after `l` EXTENDS `l` into a longer token starting at the same place |
//! | `pre(l)` | some fixed terminal `t` spells `… b l₀ …` at index ≥1 | `b` before `l` means the known, finite token `t` can carry INTO `l` |
//!
//! The emitted matcher then refuses a literal match at `p` unless
//! `bytes[p-1] ∉ pre(l)` and `bytes[p+|l|] ∉ ext(l)`. For `@`, `(`, `*` both sets are
//! EMPTY in every bundled grammar (nothing extends them, nothing runs into them), so no
//! code is emitted for those literals and the generated helper is byte-identical — which
//! is the mechanical reason the two goldens `43ef99aa` named (`Name::parse("(@Nil)")`,
//! `@Nil!(0)` electing `POutputNil`) cannot move.
//!
//! # ★ The rule has a LOCAL half and a NON-LOCAL half, and only one of them is decidable
//! # at the string level. That asymmetry is the whole design, so it is stated up front.
//!
//! * **`ext` — LOCAL, and therefore exact.** *"Does a token longer than `l` START at
//!   `p`?"* depends only on `bytes[p..]`. If `l · b` is a viable token prefix then the
//!   lexer at `p` has a candidate strictly longer than `l`, whatever precedes `p`. One
//!   byte of lookahead is all this question has: it is `l`'s own maximal munch.
//! * **`pre` — NON-LOCAL.** *"Does a token that started BEFORE `p` cover `p`?"* depends
//!   on where the lexer chose to start tokens, i.e. on the tokenization of the entire
//!   prefix — exactly the computation this string-level facade exists to avoid. It is
//!   therefore answered only for tokens whose text is KNOWN AND FINITE (the grammar's
//!   fixed terminals), which is the same character of approximation the pre-existing
//!   ident-run test already makes.
//!
//! ⚠ **MEASURED REFUTATION, recorded so it is not re-attempted.** The first cut of this
//! module computed `pre` from the regex families too, by the symmetric question *"is
//! `b · l₀` a viable token prefix?"*. That is unsound to the point of uselessness,
//! because an unbounded family swallows the whole alphabet after its opener: the string
//! family `"([^"\\]|\\.)*"` makes `b = '"'` viable before EVERY literal, so `pre(l) ∋ '"'`
//! for all `l`. Emitted and measured on RhoCalc, that made `@"OUT"!(0)` — the single most
//! common Rholang send — decline, because its `!` is preceded by a CLOSING quote and one
//! byte of lookbehind cannot tell a closing quote from an opening one. (The same happened
//! to `*` via the comment families: `pre("*") ∋ '/'` from `/*`.) The declines were sound
//! — they fall through to the walker — but they defeat the facade on its main idiom for
//! no correctness gain. Terminal-only `pre` gives the finite, intended answer:
//! `pre("-") = {'<'}` (from `<-`), `pre("!") = {'!'}` (from `!!`), and ∅ for the brackets.
//!
//! # Viable prefix
//!
//! "`s` is a viable prefix" means the union DFA over the language's token alphabet, run
//! from its start state on `s`, is in a live (non-`DEAD_STATE`) state — i.e. some token
//! of the language begins with `s`. The regex fragments Thompson-compiled by
//! [`compile_regex`] are trimmed by construction (every state lies on a start→accept
//! path), so live ⇒ *some* accept is still reachable.
//!
//! Even for `ext`, viability is a CONSERVATIVE decision procedure rather than an exact
//! one: `l · b` being viable does not prove the rest of the input completes that longer
//! token. The asymmetry is deliberate and is what makes this safe to add:
//!
//! > **A false "not a boundary" makes the helper DECLINE, and a decline falls through to
//! > the monolithic walker, which is the authoritative, ambiguity-preserving path.**
//!
//! So the error direction can only ever cost the facade's fast path, never a reading.
//! (`ProjectionIsolation.v` T7: `combine_run = None` ⇒ the unmodified monolithic body.)
//! The opposite direction — a literal matching where it should not — is the one that
//! loses readings, and that is the direction this module removes.
//!
//! # Sources of the alphabet
//!
//! 1. `language.token_defs` — the DEFAULT-mode token patterns. `literals { … }` entries
//!    desugar into this list (`TokenDef::from_literals`), so every numeric carrier's
//!    regex is here. Named lexer MODES (`mode_defs`) are excluded: their tokens are only
//!    active inside a guest region the host skeleton never frames, so including them
//!    could only manufacture declines on host text. **`ext` ONLY** (see the asymmetry
//!    above).
//! 2. [`LiteralPatterns::default()`]'s `ident` / `integer` / `float` / `string` — the
//!    built-in families a grammar that declares no `literals { … }` block still lexes.
//!    Including them unconditionally is a UNION with (1), never a replacement: a
//!    language that overrides a family keeps its own pattern and gains at most the
//!    default's bytes, which is the safe (decline) direction. **`ext` ONLY.**
//! 3. Every fixed terminal of the grammar (`SyntaxExpr::Literal` anywhere in any rule,
//!    plus `.*sep` separators). These are handled as plain strings rather than through
//!    the regex engine — no escaping question can arise. They contribute to BOTH sets,
//!    and they are the sole source of `pre`: `ext("!") ∋ '!'` (`!!`), `pre("-") ∋ '<'`
//!    (`<-`).
//!
//! # Subsumption: what is NOT emitted
//!
//! For an ident-shaped literal the retained word-run test already rejects every
//! word-character neighbour. When `pre(l)` and `ext(l)` are both ⊆ the word characters,
//! this module's test can therefore never fire, and the entry is dropped so no table row
//! and no runtime scan are emitted for it. The word-run test is KEPT rather than replaced
//! because it is strictly STRONGER at one neighbour class — a DIGIT before an ident-shaped
//! literal (`1Nil`) is a word character but is not in `pre("Nil")` — and replacing it
//! would make the helper match where it declines today, the unsafe direction. That
//! difference is a deliberate, recorded asymmetry, not an oversight.

use std::collections::{BTreeMap, BTreeSet};

use mettail_ast::{
    grammar::{PatternOp, SyntaxExpr},
    language::LanguageDef,
};
use mettail_prattail::automata::partition::compute_equivalence_classes;
use mettail_prattail::automata::regex::compile_regex;
use mettail_prattail::automata::subset::subset_construction;
use mettail_prattail::automata::{Dfa, Nfa, StateId, TokenKind, DEAD_STATE};
use mettail_prattail::LiteralPatterns;

/// THE SINGLE-VARIABLE A/B LEVER for this rule, in the house style of
/// `forks::S1_FACTORING` — a COMPILE-TIME constant, deliberately not an environment
/// switch. Setting it to `false` makes [`literal_boundary_sets`] return an empty map, so
/// every `Lit` slot is emitted with empty `pre`/`ext` slices and `__lit_boundary_ok`
/// becomes vacuously true at every site: the matcher then makes exactly the decisions it
/// made before this module existed. That is the control leg of every measurement in this
/// change's ledger.
///
/// It is a `const` and not a `std::env` read precisely because a shipped binary must not
/// be able to reopen a consensus divergence: flipping the leg requires recompiling.
pub(crate) const TOKEN_BOUNDARY_ALPHABET: bool = true;

/// The two token-boundary byte sets for one literal. Both are sorted and deduped so the
/// emitted table is deterministic (byte-reproducible codegen).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct LitBoundary {
    /// Bytes that, immediately BEFORE the literal, mean a token starting there can carry
    /// into the literal's first byte — the `error`/`or` direction, generalized.
    pub(crate) pre: Vec<u8>,
    /// Bytes that, immediately AFTER the literal, extend it into a strictly longer token
    /// starting at the same position — the `-`/`-7n` direction.
    pub(crate) ext: Vec<u8>,
}

impl LitBoundary {
    /// A literal with no boundary bytes at all imposes no condition, so nothing is
    /// emitted for it and the generated matcher is byte-identical to the pre-fix one.
    pub(crate) fn is_vacuous(&self) -> bool {
        self.pre.is_empty() && self.ext.is_empty()
    }
}

/// The word-character class the RETAINED ident-run test uses (`__is_word` in the emitted
/// helper). Kept in sync by being the only definition on this side of the fence.
fn is_word(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

/// Is `l` ident-shaped, i.e. does the retained word-run test apply to it?
fn is_word_shaped(l: &str) -> bool {
    !l.is_empty() && l.as_bytes().iter().all(|&c| is_word(c))
}

/// Every fixed terminal the grammar spells: literals in any rule's syntax pattern, plus
/// `.*sep` separators (a separator is lexed as a terminal like any other).
fn grammar_terminals(language: &LanguageDef) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for rule in &language.terms {
        let mut normalized = rule.clone();
        mettail_ast::grammar::convert_items_to_term_context(&mut normalized);
        let Some(sp) = &normalized.syntax_pattern else { continue };
        for expr in sp {
            match expr {
                SyntaxExpr::Literal(l) => {
                    if !l.is_empty() {
                        out.insert(l.clone());
                    }
                },
                SyntaxExpr::Op(PatternOp::Sep { separator, .. }) => {
                    if !separator.is_empty() {
                        out.insert(separator.clone());
                    }
                },
                _ => {},
            }
        }
    }
    out
}

/// The union DFA over the language's DEFAULT-mode token alphabet (regex families only —
/// fixed terminals are handled as strings by the caller). `None` when no pattern
/// compiles, in which case only the string-level terminal analysis contributes.
fn token_alphabet_dfa(language: &LanguageDef) -> Option<(Dfa, mettail_prattail::automata::partition::AlphabetPartition)> {
    let mut nfa = Nfa::new();
    let mut any = false;
    let defaults = LiteralPatterns::default();
    // Source (1): the language's own default-mode token patterns — this is where the
    // `literals { … }` entries live after desugaring.
    let mut patterns: Vec<String> =
        language.token_defs.iter().map(|td| td.pattern.clone()).collect();
    // Source (2): the built-in families, unioned in unconditionally (see the module docs
    // — a union can only widen the sets, i.e. decline more, which is the safe direction).
    patterns.push(defaults.integer.clone());
    patterns.push(defaults.float.clone());
    patterns.push(defaults.string.clone());
    patterns.push(defaults.ident.clone());
    if let Some(b) = defaults.boolean.clone() {
        patterns.push(b);
    }
    for pattern in patterns {
        if pattern.is_empty() {
            continue;
        }
        // The `TokenKind` is only an accept LABEL; boundary analysis asks whether a state
        // is live, never which token it accepts, so one arbitrary kind for all fragments
        // is correct (the same simplification `classify::compile_to_minimized_dfa` makes).
        if let Ok(frag) = compile_regex(&pattern, &mut nfa, TokenKind::Integer) {
            let start = nfa.start;
            nfa.add_epsilon(start, frag.start);
            any = true;
        }
    }
    if !any {
        return None;
    }
    let partition = compute_equivalence_classes(&nfa);
    let dfa = subset_construction(&nfa, &partition);
    Some((dfa, partition))
}

/// Run `bytes` from `state`; `DEAD_STATE` as soon as the DFA has no transition.
fn run(
    dfa: &Dfa,
    partition: &mettail_prattail::automata::partition::AlphabetPartition,
    mut state: StateId,
    bytes: &[u8],
) -> StateId {
    for &b in bytes {
        if state == DEAD_STATE {
            return DEAD_STATE;
        }
        state = dfa.transition(state, partition.classify(b));
    }
    state
}

/// Derive [`LitBoundary`] for every literal in `literals`, dropping the ones that impose
/// no condition the retained word-run test does not already impose.
///
/// The returned map is what the projection helper's `Lit` matcher consults; a literal
/// absent from it keeps EXACTLY today's behaviour.
pub(crate) fn literal_boundary_sets(
    language: &LanguageDef,
    literals: &BTreeSet<String>,
) -> BTreeMap<String, LitBoundary> {
    if !TOKEN_BOUNDARY_ALPHABET {
        // CONTROL LEG: no literal gets a boundary alphabet ⇒ every emitted conjunct is
        // vacuous ⇒ the matcher's decisions are the pre-fix ones.
        return BTreeMap::new();
    }
    let terminals = grammar_terminals(language);
    let alphabet = token_alphabet_dfa(language);

    let mut out = BTreeMap::new();
    for l in literals {
        if l.is_empty() {
            continue;
        }
        let lb = l.as_bytes();
        let mut ext: BTreeSet<u8> = BTreeSet::new();
        let mut pre: BTreeSet<u8> = BTreeSet::new();

        // ── Source (3): fixed terminals, EXACTLY (no regex, no escaping question). ──
        for t in &terminals {
            let tb = t.as_bytes();
            // `ext`: a terminal that strictly EXTENDS `l` contributes its next byte.
            if tb.len() > lb.len() && tb.starts_with(lb) {
                ext.insert(tb[lb.len()]);
            }
            // `pre`: a terminal in which `l`'s first byte occurs at position ≥ 1
            // contributes the byte before it (`<-` contributes `<` for the literal `-`).
            for i in 1..tb.len() {
                if tb[i] == lb[0] {
                    pre.insert(tb[i - 1]);
                }
            }
        }

        // ── Sources (1)+(2): the regex token families, via the union DFA. `ext` ONLY —
        // the LOCAL half. The symmetric `pre` question is NOT asked of these families:
        // an unbounded family swallows the alphabet after its opener, so it would answer
        // "yes" for `'"'` before every literal and decline `@"OUT"!(0)`. Measured; see
        // the module header's REFUTATION note.
        if let Some((dfa, partition)) = alphabet.as_ref() {
            let after_l = run(dfa, partition, dfa.start, lb);
            if after_l != DEAD_STATE {
                for b in 0u8..=255 {
                    if dfa.transition(after_l, partition.classify(b)) != DEAD_STATE {
                        ext.insert(b);
                    }
                }
            }
        }

        // ── Subsumption: an ident-shaped literal whose boundary bytes are all word
        // characters is already fully covered by the RETAINED word-run test. Emitting a
        // row for it would cost a runtime scan and change nothing.
        if is_word_shaped(l)
            && ext.iter().all(|&b| is_word(b))
            && pre.iter().all(|&b| is_word(b))
        {
            continue;
        }

        let boundary =
            LitBoundary { pre: pre.into_iter().collect(), ext: ext.into_iter().collect() };
        if boundary.is_vacuous() {
            continue;
        }
        out.insert(l.clone(), boundary);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A DFA over a signed-integer family: `-` must be extensible by every digit, and by
    /// nothing else. This is the exact shape of the RhoCalc defect.
    #[test]
    fn a_sign_is_extended_by_digits_only() {
        let mut nfa = Nfa::new();
        let frag = compile_regex("-?[0-9]+", &mut nfa, TokenKind::Integer)
            .expect("the signed-integer family compiles");
        let start = nfa.start;
        nfa.add_epsilon(start, frag.start);
        let partition = compute_equivalence_classes(&nfa);
        let dfa = subset_construction(&nfa, &partition);

        let after_dash = run(&dfa, &partition, dfa.start, b"-");
        assert_ne!(after_dash, DEAD_STATE, "`-` must be a viable prefix of `-?[0-9]+`");
        for b in b'0'..=b'9' {
            assert_ne!(
                dfa.transition(after_dash, partition.classify(b)),
                DEAD_STATE,
                "a digit must extend `-` into the signed literal"
            );
        }
        for b in [b'@', b'(', b' ', b'x'] {
            assert_eq!(
                dfa.transition(after_dash, partition.classify(b)),
                DEAD_STATE,
                "`-{}` is not a viable numeral prefix, so the sign stays a token there",
                b as char
            );
        }
    }

    /// The subsumption predicate: word-shaped literals bounded by word characters are
    /// dropped (the retained word-run test covers them), punctuation is not.
    #[test]
    fn word_shaped_and_word_bounded_is_dropped() {
        assert!(is_word_shaped("Nil"));
        assert!(!is_word_shaped("-"));
        assert!(!is_word_shaped("!!"));
        assert!(!is_word_shaped(""));
    }
}
