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
//! Rholang — and in consensus Rholang, whose tree-sitter grammar it mirrors — the sign
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
//! for all `l`. Emitted and measured on Rholang, that made `@"OUT"!(0)` — the single most
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

/// Every fixed terminal the grammar spells: literals in any rule's syntax pattern,
/// `.*sep` separators (a separator is lexed as a terminal like any other), **and the
/// declared COLLECTION DELIMITERS**.
///
/// ⚠ **THE COLLECTION DELIMITERS WERE THE MISSING PART OF THIS FUNCTION'S OWN RULE, and
/// they were found by the Stage-C enumerating gate, not by inspection.** The gate reported:
///
/// ```text
///   SCAN SITE `proj.lit` accepts literal "{" at byte 0 of "{|", but the language's own
///   lexer does NOT produce it as a DEFAULT-channel token there.
/// ```
///
/// Rholang declares `![PathMapLit<Proc,Proc>] as Pathmap { open_parts: ["{|"],
/// close_parts: ["|}"], sep: "," }` and `as Bag { open_parts: ["#{"], close_parts: ["}#"] }`
/// in its `types { … }` block — **not** as `SyntaxExpr::Literal` in any rule's syntax
/// pattern. So `{|` was never in the terminal set, `ext("{")` was missing `'|'`, and the
/// projection matcher would match the one-byte `{` at position 0 of a `{| … |}` literal
/// where the lexer's maximal munch is the two-byte `{|`.
///
/// That is the SAME defect shape as `-` inside `-7n`: a literal matching as a PROPER
/// PREFIX of a longer token at `p == 0`, where no left span exists and `ext` is therefore
/// the sole possible refuter. This function claimed *"every fixed terminal the grammar
/// spells"* and implemented it over a proper subset — the exact family this whole change
/// is about, found in the module that was supposed to be the family's cure.
fn grammar_terminals(language: &LanguageDef) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for rule in &language.terms {
        let mut normalized = rule.clone();
        mettail_ast::grammar::convert_items_to_term_context(&mut normalized);
        let Some(sp) = &normalized.syntax_pattern else {
            continue;
        };
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
    // ── The declared collection delimiters. A `{| … |}` opener is lexed as one token
    // exactly like any rule literal, so it belongs in the same set. Read through the
    // variant-agnostic `CollectionCategory::delimiters()` accessor, so a new collection
    // container shape is covered without a new match arm here.
    for ty in &language.types {
        let Some(kind) = &ty.collection_kind else {
            continue;
        };
        let d = kind.delimiters();
        for part in [Some(&d.open), Some(&d.close), Some(&d.sep), d.key_val_sep.as_ref()]
            .into_iter()
            .flatten()
        {
            if !part.is_empty() {
                out.insert(part.clone());
            }
        }
    }
    out
}

/// The union DFA over the language's DEFAULT-mode token alphabet (regex families only —
/// fixed terminals are handled as strings by the caller). `None` when no pattern
/// compiles, in which case only the string-level terminal analysis contributes.
fn token_alphabet_dfa(
    language: &LanguageDef,
) -> Option<(Dfa, mettail_prattail::automata::partition::AlphabetPartition)> {
    let mut nfa = Nfa::new();
    let mut any = false;
    let defaults = LiteralPatterns::default();
    // Source (1): the language's own default-mode token patterns — this is where the
    // `literals { … }` entries live after desugaring.
    let mut patterns: Vec<String> = language
        .token_defs
        .iter()
        .map(|td| td.pattern.clone())
        .collect();
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
        if is_word_shaped(l) && ext.iter().all(|&b| is_word(b)) && pre.iter().all(|&b| is_word(b)) {
            continue;
        }

        let boundary = LitBoundary {
            pre: pre.into_iter().collect(),
            ext: ext.into_iter().collect(),
        };
        if boundary.is_vacuous() {
            continue;
        }
        out.insert(l.clone(), boundary);
    }
    out
}

// ════════════════════════════════════════════════════════════════════════════════════
// ★ THE SIBLING COMPUTATION: RULE-inert's INERT SPANS, derived from the same
// `language.token_defs`.
//
// `ext`/`pre` above answer *"can a longer token cover this position?"*. RULE-inert
// answers a question that is ORTHOGONAL to both and was, until this module, implemented
// at exactly one site in the whole emitter (`__in_str`, the infix facade's string state):
//
//     A scan over RAW SOURCE may only inspect bytes the lexer would place on the
//     DEFAULT channel. Bytes inside a string literal, or inside `-> COMMENTS` trivia,
//     are NOT CODE.
//
// The measured consequence of the missing half, on the shipped `rholang` binary:
//
// ```text
//     @"OUT"!(1) // z|@"OUT"!(2)          ⇒  @"OUT" observations (2): Int(1), Int(2)
//     | Nil                                   ← the COMMENTED-OUT send RAN
//
//     @"OUT"!(1) // z@"OUT"!(2)           ⇒  @"OUT" observations (1): Int(1)
//     | Nil                                   ← same comment, no depth-0 `|` in it
// ```
//
// The single controlled variable is the `|` inside the comment: the infix `__OPS` scan
// sees it at depth 0, elects it as the `Par` root, and splits the source there — so the
// text to its right, which the lexer had already routed to the COMMENTS channel, is
// handed to a sub-parser as code.
//
// Rholang's comments are LEXED, NOT STRIPPED (`languages/src/rholang.rs`
// `LineComment = "//[^\n]*" -> COMMENTS`), which is what puts raw comment bytes in front
// of every string facade in the first place.
//
// SAFETY DIRECTION. Skipping inert spans can only make a scan see FEWER candidate
// positions ⇒ more declines ⇒ fall-through to the monolithic walker, which lexes
// correctly. Same argument as `ProjectionIsolation.v` `T7_fallthrough_is_monolithic`.
// ════════════════════════════════════════════════════════════════════════════════════

/// The token patterns whose spans are INERT for a raw-source scan.
///
/// Two sources, both derived — no hardcoded `//`, no hardcoded `"`:
///
/// 1. **Off-DEFAULT-channel tokens.** Every `TokenDef` routed to a named stream other
///    than `main` (`-> COMMENTS`). The predicate mirrors the lexer's own, verbatim from
///    `prattail/src/lexer.rs`: `spec.stream.as_deref().filter(|s| *s != "main")`.
/// 2. **The string family.** A string literal is on the DEFAULT channel, but its
///    INTERIOR is not code — which is precisely what the hand-written `__in_str` state
///    has always encoded. Taken from [`LiteralPatterns::default()`], unioned in
///    unconditionally for the same reason source (2) of `ext` is: a union can only widen
///    the inert set, i.e. decline more, which is the safe direction.
///
/// A language with no comments and no string family yields an EMPTY vector, for which
/// [`emit_inert_skipper`] emits nothing at all and the generated code is byte-identical.
pub(crate) fn inert_token_patterns(language: &LanguageDef) -> Vec<String> {
    let mut out: Vec<String> = Vec::with_capacity(language.token_defs.len() + 1);
    for td in &language.token_defs {
        // The lexer's own off-DEFAULT predicate (`prattail/src/lexer.rs`).
        let off_default = td
            .stream
            .as_ref()
            .map(|s| s.to_string())
            .filter(|s| s != "main")
            .is_some();
        if off_default && !td.pattern.is_empty() {
            out.push(td.pattern.clone());
        }
    }
    let string_family = LiteralPatterns::default().string;
    if !string_family.is_empty() {
        out.push(string_family);
    }
    out.sort();
    out.dedup();
    out
}

/// Does this language emit a `lex_with_streams` entry point?
///
/// MIRRORS `prattail/src/lexer.rs`'s own `has_streams` predicate EXACTLY, including its
/// use of bare `stream.is_some()` rather than `!= "main"`, so the two cannot disagree
/// about whether the function exists. The Stage-C gate calls `lex_with_streams` as its
/// oracle, so it may only be emitted for a language that has one — a JSON grammar with no
/// stream-annotated token does not, and emitting the gate there is a build error. (That
/// was a real regression in this change, caught by `--all-features`.)
pub(crate) fn language_emits_lex_with_streams(language: &LanguageDef) -> bool {
    let is_auxiliary = |stream: &Option<syn::Ident>| {
        stream
            .as_ref()
            .map(|name| name.to_string())
            .is_some_and(|name| name != "main")
    };
    language
        .token_defs
        .iter()
        .any(|td| is_auxiliary(&td.stream))
        || language
            .mode_defs
            .iter()
            .any(|m| m.token_defs.iter().any(|td| is_auxiliary(&td.stream)))
}

/// Emit the shared source-layout oracle used by raw-source isolation facades.
///
/// Ordinary Unicode whitespace and lexer-certified auxiliary-channel ranges are
/// layout.  DEFAULT-channel strings and modal guest text are deliberately absent
/// from those ranges, so this helper cannot erase them.  A malformed or failed
/// authoritative lex makes the facade decline through `None`.
pub(crate) fn emit_layout_oracle(language: &LanguageDef) -> proc_macro2::TokenStream {
    use quote::quote;

    let collect_auxiliary = if language_emits_lex_with_streams(language) {
        quote! {
            let __lexed = lex_with_streams(input).ok()?;
            let mut __auxiliary: Vec<(usize, usize)> = __lexed
                .streams
                .values()
                .flat_map(|__tokens| __tokens.iter().map(|(_, __range)| {
                    (__range.start.byte_offset, __range.end.byte_offset)
                }))
                .collect();
            __auxiliary.sort_unstable();
            let mut __previous_end = 0usize;
            for &(__start, __end) in &__auxiliary {
                if __start >= __end
                    || __end > input.len()
                    || !input.is_char_boundary(__start)
                    || !input.is_char_boundary(__end)
                    || __start < __previous_end
                {
                    return None;
                }
                __previous_end = __end;
            }
            __auxiliary
        }
    } else {
        quote! { Vec::new() }
    };

    quote! {
        struct __MettailSourceLayout {
            auxiliary: Vec<(usize, usize)>,
            opaque: Vec<(usize, usize)>,
        }

        /// Ranges hidden from the parser by the generated lexer's own channel
        /// routing, plus lexically atomic non-Fixed token ranges. The lexer DAG
        /// is the authority for modes and all tokenization alternatives.
        fn __mettail_layout_ranges(input: &str) -> Option<__MettailSourceLayout> {
            let __auxiliary = { #collect_auxiliary };
            let __dag = lex_dag(input).ok()?;
            let mut __opaque: Vec<(usize, usize)> = __dag
                .nodes
                .iter()
                .filter_map(|__node| {
                    let __first = __node.edges.first()?;
                    let __end = __first.end_byte;
                    let __same_non_fixed_span = __end > __node.byte_start
                        && __node.edges.iter().all(|__edge| {
                            __edge.end_byte == __end
                                && !matches!(
                                    __edge.kind,
                                    mettail_prattail::automata::TokenKind::Fixed(_)
                                )
                        });
                    __same_non_fixed_span.then_some((__node.byte_start, __end))
                })
                .collect();
            __opaque.sort_unstable();
            __opaque.dedup();
            for &(__start, __end) in &__opaque {
                if __start >= __end
                    || __end > input.len()
                    || !input.is_char_boundary(__start)
                    || !input.is_char_boundary(__end)
                {
                    return None;
                }
            }
            Some(__MettailSourceLayout {
                auxiliary: __auxiliary,
                opaque: __opaque,
            })
        }

        /// Advance across layout at `at`, never beyond `end`.  Every successful
        /// loop consumes at least one UTF-8 byte or one non-empty auxiliary range.
        fn __mettail_skip_layout(
            input: &str,
            layout: &__MettailSourceLayout,
            mut at: usize,
            end: usize,
        ) -> usize {
            while at < end {
                let before = at;
                while at < end {
                    let Some(rest) = input.get(at..end) else { return at };
                    let Some(ch) = rest.chars().next() else { return at };
                    if !ch.is_whitespace() {
                        break;
                    }
                    at += ch.len_utf8();
                }

                let index = layout
                    .auxiliary
                    .partition_point(|&(_, range_end)| range_end <= at);
                if let Some(&(range_start, range_end)) = layout.auxiliary.get(index) {
                    if range_start <= at && at < range_end && range_end <= end {
                        at = range_end;
                    }
                }
                if at == before {
                    break;
                }
            }
            at
        }

        /// Skip one token only when every lexer-DAG alternative at this exact
        /// boundary is non-Fixed and has the same non-empty range. Such a token
        /// cannot expose host punctuation; ambiguity makes the oracle decline
        /// to skip, preserving every possible fixed-token reading.
        fn __mettail_skip_opaque(
            layout: &__MettailSourceLayout,
            at: usize,
            end: usize,
        ) -> usize {
            let index = layout.opaque.partition_point(|&(start, _)| start < at);
            match layout.opaque.get(index) {
                Some(&(start, finish)) if start == at && finish <= end => finish,
                _ => at,
            }
        }

        /// Remove layout from both ends of a source range without copying or
        /// rewriting its interior.  Returns byte indices into the original input.
        fn __mettail_trim_layout(
            input: &str,
            layout: &__MettailSourceLayout,
            start: usize,
            end: usize,
        ) -> Option<(usize, usize)> {
            if start > end || end > input.len() {
                return None;
            }
            let start = __mettail_skip_layout(input, layout, start, end);
            let mut finish = end;
            while start < finish {
                let before = finish;
                let index = layout
                    .auxiliary
                    .partition_point(|&(range_start, _)| range_start < finish);
                if let Some(&(range_start, range_end)) =
                    index.checked_sub(1).and_then(|i| layout.auxiliary.get(i))
                {
                    if start <= range_start && range_start < finish && finish <= range_end {
                        finish = range_start;
                    }
                }
                if finish == before {
                    let Some(prefix) = input.get(start..finish) else { return None };
                    let Some(ch) = prefix.chars().next_back() else { break };
                    if !ch.is_whitespace() {
                        break;
                    }
                    finish -= ch.len_utf8();
                }
            }
            Some((start, finish))
        }
    }
}

/// Emit the per-language `__inert_skip` helper: given `bytes` and an index `i`, return
/// the index just past the inert span starting at `i`, or `i` when no inert span starts
/// there.
///
/// # The algorithm, and why it is maximal munch
///
/// The helper runs the union DFA of [`inert_token_patterns`] from `i` and returns the
/// LAST accepting position — the same maximal munch the lexer performs, so
/// `// a // b` is one comment (as the lexer says) rather than two.
///
/// ```text
///     __inert_skip(bytes, i):
///       s ← start;  last ← i;  j ← i
///       while j < |bytes| and δ(s, bytes[j]) ≠ ⊥:
///           s ← δ(s, bytes[j]);  j ← j + 1
///           if s ∈ F then last ← j
///       if last = i and j > i and s ≠ ⊥ then return |bytes|      ⟵ unterminated
///       return last
/// ```
///
/// # The unterminated-span clause
///
/// If the run consumed at least one byte and ran out of input while still LIVE, the span
/// is an *unterminated* comment or string. The helper then reports the whole remainder as
/// inert. That is deliberate and it is the conservative choice on two counts: it
/// reproduces exactly what the hand-written `__in_str` toggle did (an unmatched `"`
/// makes the rest of the span content), and it errs toward MORE inert bytes, i.e. fewer
/// split candidates, i.e. a decline — the direction that falls through to the walker.
///
/// Returning `i` instead would treat the opener as code and let the scan split inside an
/// unterminated literal, which is the direction that loses readings.
pub(crate) fn emit_inert_skipper(language: &LanguageDef) -> proc_macro2::TokenStream {
    use quote::quote;

    if !super::scan_site::INERT_SPAN_SKIP {
        // CONTROL LEG: nothing emitted ⇒ byte-identical to the pre-Stage-B artifact.
        return quote! {};
    }
    let patterns = inert_token_patterns(language);
    if patterns.is_empty() {
        // A language with no comments and no string family: the identity skipper is
        // never called because no site can skip anything. Emit nothing.
        return quote! {};
    }

    let mut nfa = Nfa::new();
    let mut any = false;
    for pattern in &patterns {
        if let Ok(frag) = compile_regex(pattern, &mut nfa, TokenKind::StringLit) {
            let start = nfa.start;
            nfa.add_epsilon(start, frag.start);
            any = true;
        }
    }
    if !any {
        return quote! {};
    }
    let partition = compute_equivalence_classes(&nfa);
    let dfa = subset_construction(&nfa, &partition);

    let num_classes = dfa.num_classes;
    // Byte → equivalence class, so the emitted transition table is class-compressed
    // (`num_states × num_classes`) rather than `num_states × 256`.
    let class_of: Vec<u8> = (0u16..=255).map(|b| partition.classify(b as u8)).collect();
    // `DEAD_STATE` is `u32::MAX`; the emitted table uses `u32::MAX` as its own sentinel so
    // no state index can collide with it.
    let mut trans: Vec<u32> = Vec::with_capacity(dfa.states.len() * num_classes);
    for s in 0..dfa.states.len() {
        for c in 0..num_classes {
            trans.push(dfa.transition(s as StateId, c as u8));
        }
    }
    let accept: Vec<bool> = dfa.states.iter().map(|s| s.accept.is_some()).collect();
    let start = dfa.start;
    let n_classes_lit = num_classes;
    let pattern_doc = format!(
        " Derived from {} inert token pattern(s): {}",
        patterns.len(),
        patterns.join(" · ")
    );

    quote! {
        /// ★ RULE-inert — the INERT-SPAN SKIPPER.
        ///
        /// Byte → alphabet-equivalence-class map for the inert-token DFA.
        #[allow(dead_code)]
        const __INERT_CLASS: [u8; 256] = [ #(#class_of),* ];
        /// Class-compressed transition table, `state * __INERT_CLASSES + class`.
        /// `u32::MAX` is the dead state.
        #[allow(dead_code)]
        const __INERT_TRANS: &[u32] = &[ #(#trans),* ];
        /// Accepting states of the inert-token DFA.
        #[allow(dead_code)]
        const __INERT_ACCEPT: &[bool] = &[ #(#accept),* ];
        #[allow(dead_code)]
        const __INERT_CLASSES: usize = #n_classes_lit;
        #[allow(dead_code)]
        const __INERT_START: u32 = #start;

        #[doc = #pattern_doc]
        ///
        /// Return the index just past the inert span (string literal or `-> COMMENTS`
        /// trivia) beginning at `i`, or `i` when no inert span begins there.
        ///
        /// Maximal munch, exactly as the lexer performs it. An UNTERMINATED span (the run
        /// stays live to end-of-input without accepting) reports the whole remainder as
        /// inert — the conservative direction, and the behaviour the hand-written
        /// `__in_str` toggle it replaces already had.
        #[allow(dead_code)]
        fn __inert_skip(bytes: &[u8], i: usize) -> usize {
            let n = bytes.len();
            if i >= n {
                return i;
            }
            let mut state: u32 = __INERT_START;
            let mut last = i;
            let mut j = i;
            while j < n {
                let class = __INERT_CLASS[bytes[j] as usize] as usize;
                let next = __INERT_TRANS[state as usize * __INERT_CLASSES + class];
                if next == u32::MAX {
                    break;
                }
                state = next;
                j += 1;
                if __INERT_ACCEPT[state as usize] {
                    last = j;
                }
            }
            if last == i && j > i && j == n {
                // Unterminated comment / string: the remainder is not code.
                return n;
            }
            last
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::language::{LanguageDef, ModeDef, TokenDef};
    use proc_macro2::Span;
    use syn::Ident;

    fn empty_language() -> LanguageDef {
        LanguageDef {
            name: Ident::new("LayoutOracleTest", Span::call_site()),
            options: Default::default(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: Vec::new(),
            refinement_types: Vec::new(),
            token_defs: Vec::new(),
            mode_defs: Vec::new(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms: Vec::new(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        }
    }

    fn token(stream: Option<&str>) -> TokenDef {
        TokenDef {
            name: Ident::new("Trivia", Span::call_site()),
            pattern: "//[^\\n]*".to_string(),
            category: None,
            rust_code: None,
            priority: None,
            push_mode: None,
            is_pop: false,
            stream: stream.map(|name| Ident::new(name, Span::call_site())),
            from_literals: false,
        }
    }

    /// A DFA over a signed-integer family: `-` must be extensible by every digit, and by
    /// nothing else. This is the exact shape of the Rholang defect.
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

    #[test]
    fn layout_oracle_uses_lexer_ranges_only_for_auxiliary_channels() {
        let mut auxiliary = empty_language();
        auxiliary.token_defs.push(token(Some("COMMENTS")));
        assert!(language_emits_lex_with_streams(&auxiliary));
        let emitted = emit_layout_oracle(&auxiliary).to_string();
        assert!(emitted.contains("lex_with_streams"));
        assert!(emitted.contains("range . start . byte_offset"));

        let mut main = empty_language();
        main.token_defs.push(token(Some("main")));
        assert!(!language_emits_lex_with_streams(&main));
        let emitted = emit_layout_oracle(&main).to_string();
        assert!(!emitted.contains("lex_with_streams"));
    }

    #[test]
    fn layout_oracle_detects_auxiliary_tokens_in_named_modes() {
        let mut language = empty_language();
        language.mode_defs.push(ModeDef {
            name: Ident::new("guest", Span::call_site()),
            token_defs: vec![token(Some("COMMENTS"))],
            raw: true,
        });
        assert!(language_emits_lex_with_streams(&language));
        assert!(emit_layout_oracle(&language)
            .to_string()
            .contains("lex_with_streams"));
    }
}
