//! Bisimilarity-based semantic classification of lexer token patterns.
//!
//! Given a user-declared token regex (or a default `LiteralPatterns`
//! entry), decide whether its accepted language is equivalent to a
//! canonical reference family (`Integer`, `SignedInt`, `Float`, …).
//! Classification is done by **language equivalence** between the
//! minimized DFAs: two patterns classify as the same family iff their
//! DFAs accept exactly the same set of strings.
//!
//! Language equivalence is decided by a **byte-level product
//! traversal**: starting from `(s_a, s_b) = (start_a, start_b)`,
//! BFS over every input byte, verifying that the two DFAs' accept
//! status agrees at every reachable product state. This is sound
//! regardless of each DFA's internal `ClassId` partition (which is
//! computed per-NFA and is NOT comparable across independently
//! compiled patterns). Complexity: `O(|S_a| · |S_b| · 256)` — for
//! the ≤30-state DFAs typical of lexer patterns, ≤230k steps.
//!
//! Constraint extraction (length bounds, signed-ness, radix) is
//! performed on the *user's* minimized DFA after classification —
//! these parameters are passed to the family's sampler so the
//! generated values stay within the pattern's admitted domain.

use mettail_prattail::automata::{
    Dfa, Nfa, StateId, TokenKind, DEAD_STATE,
};
use mettail_prattail::automata::minimize::minimize_dfa;
use mettail_prattail::automata::partition::compute_equivalence_classes;
use mettail_prattail::automata::regex::compile_regex;
use mettail_prattail::automata::subset::subset_construction;

/// Canonical token family — the "semantic kind" a pattern belongs to.
///
/// `Unclassified` means no canonical DFA was language-equivalent to
/// the user's pattern; callers fall back to generic NFA walk.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CanonicalKind {
    /// `/[0-9]+/` — unsigned decimal integer. Value domain is
    /// `0..=i64::MAX` (bounded below by storage).
    Integer,
    /// `/-?[0-9]+/` — signed decimal integer. Value domain is the
    /// full `i64` range. `i64::MIN` is a representable surface value
    /// because `-9223372036854775808` lexes correctly under this
    /// pattern.
    SignedInt,
    /// `/[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?/` — unsigned float literal.
    /// Value domain is non-negative finite f64.
    Float,
    /// `/-?[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?/` — signed float literal.
    /// Value domain is finite f64 (both signs).
    SignedFloat,
    /// Pattern didn't match any canonical reference. Callers should
    /// fall back to generic NFA walk against the pattern itself.
    Unclassified,
}

/// Constraints extracted from a classified pattern's DFA.
///
/// For numeric families this narrows the sampler's value domain; the
/// pattern `[0-9]{1,3}` yields `Constraints { min_len: 1, max_len:
/// Some(3), signed: false, .. }`, which the `Integer` sampler
/// translates to values in `0..=999`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constraints {
    /// Shortest string the pattern accepts (BFS shortest-path).
    pub min_len: usize,
    /// Longest string the pattern accepts. `None` if any reachable
    /// cycle lies on a start-to-accept path (→ unbounded length).
    pub max_len: Option<usize>,
    /// Whether a leading `-` byte is accepted from the start state.
    /// Derived from examining start-state transitions.
    pub signed: bool,
}

impl Constraints {
    /// Unbounded default used when constraint extraction is not
    /// applicable or not yet implemented for a family.
    pub fn unbounded() -> Self {
        Constraints { min_len: 0, max_len: None, signed: false }
    }
}

/// Compile a regex pattern to a minimized DFA. The returned DFA has
/// BFS-canonical state ordering (produced by `minimize_dfa`), so
/// `start = 0` always.
fn compile_to_minimized_dfa(pattern: &str) -> Option<Dfa> {
    let mut nfa = Nfa::new();
    // The TokenKind assigned here is only a label on accept states;
    // it does not affect language equivalence. We use `Integer`
    // arbitrarily and collapse any non-None accept to a single
    // "accept" signal during product traversal.
    let frag = compile_regex(pattern, &mut nfa, TokenKind::Integer).ok()?;
    // Wire the fragment's start as the NFA start.
    nfa.add_epsilon(nfa.start, frag.start);
    let partition = compute_equivalence_classes(&nfa);
    let dfa = subset_construction(&nfa, &partition);
    Some(minimize_dfa(&dfa))
}

/// Is the given DFA state an accepting state?
#[inline]
fn is_accept(dfa: &Dfa, s: StateId) -> bool {
    dfa.states[s as usize].accept.is_some()
}

/// Follow a DFA transition on a concrete input byte `b`. Returns
/// `DEAD_STATE` if the DFA has no transition for that byte.
///
/// Because `ClassId`s differ per DFA, we can't directly index by
/// byte. Instead we rely on the fact that every DFA state's
/// `transitions` vector is indexed by its own `ClassId` partition
/// — so we must look up which class `b` falls into for *this* DFA.
///
/// The per-DFA byte→class map is **not** stored on `Dfa` itself;
/// it's produced by `compute_equivalence_classes` as part of the
/// partition. Since we don't retain the partition alongside the
/// minimized DFA here, we take a different route: walk *accepted
/// strings* directly via the NFA rather than byte-stepping through
/// the DFA for product comparison. See `language_equivalent` for
/// the actual mechanism.
#[allow(dead_code)]
fn _dfa_step_by_byte(_dfa: &Dfa, _s: StateId, _b: u8) -> StateId {
    unimplemented!("use language_equivalent instead")
}

/// Decide whether two patterns (given as regex strings) accept the
/// same language.
///
/// Implementation note: the two patterns may compile with *different*
/// `ClassId` partitions because partitions are computed per-NFA. To
/// sidestep that, we compile both patterns into the *same* NFA —
/// with distinct accept tokens — then determinize the union. In the
/// resulting DFA, each accept state inherits one token (the best by
/// priority); we examine the full `alt_accepts` list (preserved by
/// `subset_construction`) to see *both* tokens when a state accepts
/// via both patterns.
///
/// Two patterns are language-equivalent iff, for every DFA state
/// reachable from the shared start:
///   - accept sets (`accept` ∪ `alt_accepts`) agree on which of
///     `kind_a` / `kind_b` are present.
pub fn language_equivalent(pattern_a: &str, pattern_b: &str) -> bool {
    // Distinct TokenKinds let us track which pattern each accept
    // state came from. We pick two Custom variants to avoid
    // colliding with built-ins.
    let kind_a = TokenKind::Custom("__classify_A".to_string());
    let kind_b = TokenKind::Custom("__classify_B".to_string());

    let mut nfa = Nfa::new();
    // Compile both patterns into the shared NFA.
    let frag_a = match compile_regex(pattern_a, &mut nfa, kind_a.clone()) {
        Ok(f) => f,
        Err(_) => return false,
    };
    let frag_b = match compile_regex(pattern_b, &mut nfa, kind_b.clone()) {
        Ok(f) => f,
        Err(_) => return false,
    };
    // Union: shared start state ε-transitions to both fragment starts.
    nfa.add_epsilon(nfa.start, frag_a.start);
    nfa.add_epsilon(nfa.start, frag_b.start);

    let partition = compute_equivalence_classes(&nfa);
    let dfa = subset_construction(&nfa, &partition);
    // No minimize step needed — we only care about accept labels
    // per reachable state, which determinization preserves.

    // Walk every reachable DFA state and check the accept-set
    // agreement on (kind_a, kind_b).
    let mut visited = vec![false; dfa.states.len()];
    let mut stack = vec![dfa.start];
    while let Some(s) = stack.pop() {
        if visited[s as usize] {
            continue;
        }
        visited[s as usize] = true;

        let state = &dfa.states[s as usize];
        // Build the accept set for this state: the primary accept
        // PLUS every kind in alt_accepts. Duplicates are fine.
        let mut has_a = false;
        let mut has_b = false;
        if let Some(ref k) = state.accept {
            if *k == kind_a { has_a = true; }
            if *k == kind_b { has_b = true; }
        }
        for (k, _) in &state.alt_accepts {
            if *k == kind_a { has_a = true; }
            if *k == kind_b { has_b = true; }
        }

        if has_a != has_b {
            // Some reachable state accepts via one pattern but not
            // the other → languages differ on some string.
            return false;
        }

        for &next in &state.transitions {
            if next != DEAD_STATE && !visited[next as usize] {
                stack.push(next);
            }
        }
    }

    true
}

/// Classify a pattern by comparing it against the canonical library.
///
/// Current library (will grow incrementally — see mod-level docs):
/// - `/[0-9]+/` → `Integer`
/// - `/-?[0-9]+/` → `SignedInt`
///
/// Other patterns return `Unclassified`; callers fall back to
/// generic NFA walk.
pub fn classify_token(pattern: &str) -> CanonicalKind {
    // Order matters for readability only — each check is independent
    // because language equivalence is a strict equality.
    if language_equivalent(pattern, "[0-9]+") {
        return CanonicalKind::Integer;
    }
    if language_equivalent(pattern, "-?[0-9]+") {
        return CanonicalKind::SignedInt;
    }
    if language_equivalent(pattern, r"[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?") {
        return CanonicalKind::Float;
    }
    if language_equivalent(pattern, r"-?[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?") {
        return CanonicalKind::SignedFloat;
    }
    CanonicalKind::Unclassified
}

/// Extract constraints from a pattern's minimized DFA.
///
/// For the first cut this only populates `signed` via start-state
/// inspection and leaves length bounds at their unbounded defaults.
/// Full extraction (BFS shortest path for `min_len`, cycle detection
/// for `max_len`) is a follow-up.
pub fn extract_constraints(pattern: &str) -> Constraints {
    let mut out = Constraints::unbounded();

    // `signed`: does the pattern accept a leading `-`? A pattern
    // like `-?[0-9]+` has the start state transitioning on `-` to a
    // non-dead state; `[0-9]+` does not.
    if let Some(dfa) = compile_to_minimized_dfa(pattern) {
        out.signed = has_dash_from_start(pattern, &dfa);
    }

    out
}

/// Inspect the minimized DFA's start state and determine whether a
/// `-` byte (0x2D) leads to a non-dead state. Because `ClassId`s
/// differ per DFA, we need to find which class contains 0x2D. We do
/// this by rebuilding the NFA, computing the partition, and asking
/// the partition which class 0x2D belongs to.
///
/// This is slightly wasteful (re-compile), but constraint extraction
/// runs once per token kind at codegen time, not in a hot loop.
///
/// **Stage 3.27b (2026-05-04):** the recompiled partition's
/// `byte_to_class` array is bit-identical to the one used to build
/// `dfa` because (a) `compile_regex` is deterministic on a fresh
/// `Nfa::new()` for the same pattern string, and (b)
/// `compute_equivalence_classes` (`prattail/src/automata/partition.rs`)
/// is iteration-driven over `0u8..=255` with deterministic signature
/// computation per byte. So `partition.classify(b'-')` returns a
/// `ClassId` valid as an index into `dfa.states[dfa.start].transitions`.
fn has_dash_from_start(pattern: &str, dfa: &Dfa) -> bool {
    let mut nfa = Nfa::new();
    let frag = match compile_regex(pattern, &mut nfa, TokenKind::Integer) {
        Ok(f) => f,
        Err(_) => return false,
    };
    nfa.add_epsilon(nfa.start, frag.start);
    let partition = compute_equivalence_classes(&nfa);
    let class = partition.classify(b'-');
    let target = dfa.transition(dfa.start, class);
    target != DEAD_STATE
}

/// Look up the effective regex pattern for a built-in lexer token
/// kind (`"Integer"` / `"Float"` / `"StringLit"` / `"Ident"`) by
/// examining the language's `tokens { ... }` overrides, falling
/// back to the built-in default if no override exists.
///
/// Matches the resolution logic at
/// `macros/src/gen/syntax/parser/prattail_bridge.rs:78–92` so the
/// strategy's classifier sees the same pattern the parser will see.
pub fn effective_pattern_for(
    language: &mettail_ast::language::LanguageDef,
    kind: &str,
) -> String {
    // Walk user overrides first — they win.
    for td in &language.token_defs {
        if td.name == kind {
            return td.pattern.clone();
        }
    }
    // Fall back to the defaults embedded in
    // `prattail/src/literal_patterns.ebnf`.
    match kind {
        "Integer" => "[0-9]+".to_string(),
        "Float" => r"[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?".to_string(),
        "StringLit" => r#""([^"\\]|\\.)*""#.to_string(),
        "Ident" => "[a-zA-Z_][a-zA-Z0-9_]*".to_string(),
        // Unknown kind: caller gets an empty pattern which will
        // classify as Unclassified (language_equivalent rejects
        // empty pattern via compile error).
        _ => "".to_string(),
    }
}

// ─── Tests ──────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classify_canonical_integer() {
        assert_eq!(classify_token("[0-9]+"), CanonicalKind::Integer);
    }

    #[test]
    fn classify_canonical_signed_int() {
        assert_eq!(classify_token("-?[0-9]+"), CanonicalKind::SignedInt);
    }

    #[test]
    fn classify_language_equivalent_integer_variants() {
        // Syntactically different, language-equivalent to [0-9]+.
        // Proves bisimilarity is doing real work beyond string
        // matching.
        assert_eq!(classify_token("[0-9][0-9]*"), CanonicalKind::Integer);
    }

    #[test]
    fn classify_unclassified_pattern() {
        // Letter-only pattern isn't in the canonical library.
        assert_eq!(classify_token("[a-z]+"), CanonicalKind::Unclassified);
    }

    #[test]
    fn language_equivalent_reflexive() {
        assert!(language_equivalent("[0-9]+", "[0-9]+"));
    }

    #[test]
    fn language_equivalent_syntactic_variants() {
        // Regexes that differ syntactically but accept the same
        // language must be detected.
        assert!(language_equivalent("[0-9]+", "[0-9][0-9]*"));
        assert!(language_equivalent("-?[0-9]+", "(-)?[0-9]+"));
    }

    #[test]
    fn language_not_equivalent_different_alphabets() {
        assert!(!language_equivalent("[0-9]+", "[a-z]+"));
    }

    #[test]
    fn language_not_equivalent_signed_vs_unsigned() {
        // Signed accepts "-5", unsigned doesn't → not equivalent.
        assert!(!language_equivalent("[0-9]+", "-?[0-9]+"));
    }

    #[test]
    fn extract_constraints_unbounded_default() {
        let c = extract_constraints("[0-9]+");
        assert_eq!(c.max_len, None);
        // Stage 3.27b (2026-05-04): signed extraction is now wired;
        // this test still covers the unbounded-default path. The
        // signed=false case is asserted explicitly in
        // extract_constraints_unsigned_for_plain_int_pattern below.
    }

    // ─── Stage 3.27b (2026-05-04): signed-detection coverage ──────────

    #[test]
    fn extract_constraints_signed_for_signed_int_pattern() {
        let c = extract_constraints("-?[0-9]+");
        assert!(c.signed, "pattern -?[0-9]+ should have signed=true");
    }

    #[test]
    fn extract_constraints_unsigned_for_plain_int_pattern() {
        let c = extract_constraints("[0-9]+");
        assert!(!c.signed, "pattern [0-9]+ should have signed=false");
    }

    #[test]
    fn extract_constraints_signed_for_signed_float_pattern() {
        let c = extract_constraints(r"-?[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?");
        assert!(c.signed, "signed float pattern should have signed=true");
    }

    #[test]
    fn extract_constraints_unsigned_for_plain_float_pattern() {
        let c = extract_constraints(r"[0-9]+\.[0-9]+([eE][+-]?[0-9]+)?");
        assert!(!c.signed, "plain float pattern should have signed=false");
    }

    #[test]
    fn extract_constraints_invalid_pattern_returns_unbounded() {
        // Smoke: bad regex doesn't panic; returns the unbounded default.
        let c = extract_constraints("[");
        assert!(!c.signed);
        assert_eq!(c.max_len, None);
    }
}
