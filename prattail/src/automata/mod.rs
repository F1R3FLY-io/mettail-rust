//! Automata infrastructure for lexer generation.
//!
//! Provides NFA/DFA types, traits, and the lexer generation pipeline:
//! `Terminals -> NFA -> DFA -> Minimize -> Equiv Classes -> Codegen`

pub mod codegen;
pub mod minimize;
pub mod mph;
pub mod nfa;
pub mod partition;
pub mod regex;
pub mod semiring;
pub mod subset;
pub mod utf8;

use semiring::{Semiring, TropicalWeight};

/// Identifier for an automaton state.
pub type StateId = u32;

/// Identifier for an equivalence class of characters.
pub type ClassId = u8;

/// A sentinel value representing a non-existent / dead state.
pub const DEAD_STATE: StateId = u32::MAX;

/// Source position span in input text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

/// Token kind produced by the lexer. Each variant corresponds to a distinct
/// terminal symbol in the grammar.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TokenKind {
    /// End of file
    Eof,
    /// Identifier (variable name)
    Ident,
    /// Integer literal
    Integer,
    /// Float literal
    Float,
    /// Boolean literal `true`
    True,
    /// Boolean literal `false`
    False,
    /// String literal
    StringLit,
    /// A fixed terminal symbol (operator, keyword, delimiter).
    /// The string is the exact terminal text (e.g. "+", "error", "(").
    Fixed(String),
    /// Dollar-prefixed identifier: `$proc`, `$name`, etc.
    Dollar,
    /// Double-dollar-prefixed application: `$$proc(`, `$$name(`, etc.
    DoubleDollar,
    /// Custom user-defined token kind from the `tokens { ... }` block.
    Custom(String),
}

impl TokenKind {
    /// Priority for disambiguation. Higher value = higher priority.
    /// Keywords beat identifiers; fixed terminals beat character-class tokens.
    pub fn priority(&self) -> u8 {
        match self {
            TokenKind::Eof => 0,
            TokenKind::Ident => 1,
            TokenKind::Integer => 2,
            TokenKind::Float => 3,
            TokenKind::True | TokenKind::False => 10,
            TokenKind::StringLit => 2,
            TokenKind::Fixed(_) => 10,
            TokenKind::Dollar => 5,
            TokenKind::DoubleDollar => 6,
            // Default priority for custom tokens; actual priority is set from
            // CustomTokenSpec.priority at the NFA accept-state level.
            TokenKind::Custom(_) => 2,
        }
    }
}

/// A character class for NFA transitions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CharClass {
    /// Single character.
    Single(u8),
    /// Inclusive range of characters.
    Range(u8, u8),
    /// Equivalence class identifier (assigned by partition phase).
    Class(ClassId),
}

impl CharClass {
    /// Check whether a byte falls within this class.
    pub fn contains(&self, byte: u8) -> bool {
        match self {
            CharClass::Single(b) => *b == byte,
            CharClass::Range(lo, hi) => byte >= *lo && byte <= *hi,
            CharClass::Class(_) => false, // resolved during subset construction
        }
    }

    /// Enumerate all bytes in this class (for partition computation).
    pub fn bytes(&self) -> Vec<u8> {
        match self {
            CharClass::Single(b) => vec![*b],
            CharClass::Range(lo, hi) => (*lo..=*hi).collect(),
            CharClass::Class(_) => vec![],
        }
    }
}

/// NFA state with labeled and epsilon transitions.
#[derive(Debug, Clone)]
pub struct NfaState {
    /// Labeled transitions: (character class, target state).
    pub transitions: Vec<(CharClass, StateId)>,
    /// Epsilon transitions: target states reachable without consuming input.
    pub epsilon: Vec<StateId>,
    /// If this is an accepting state, which token kind it produces.
    pub accept: Option<TokenKind>,
    /// Tropical weight for this accepting state.
    ///
    /// Derived from `TokenKind::priority()` via `TropicalWeight::from_priority()`.
    /// Lower weight = higher priority. Non-accepting states have `TropicalWeight::zero()`
    /// (infinity / unreachable).
    pub weight: TropicalWeight,
}

impl NfaState {
    /// Create a new non-accepting NFA state with no transitions.
    pub fn new() -> Self {
        NfaState {
            transitions: Vec::new(),
            epsilon: Vec::new(),
            accept: None,
            weight: TropicalWeight::zero(),
        }
    }

    /// Create a new accepting NFA state with weight derived from the token kind's priority.
    pub fn accepting(kind: TokenKind) -> Self {
        let weight = TropicalWeight::from_priority(kind.priority());
        NfaState {
            transitions: Vec::new(),
            epsilon: Vec::new(),
            accept: Some(kind),
            weight,
        }
    }
}

impl Default for NfaState {
    fn default() -> Self {
        Self::new()
    }
}

/// A complete NFA (collection of states with a designated start state).
#[derive(Debug, Clone)]
pub struct Nfa {
    pub states: Vec<NfaState>,
    pub start: StateId,
}

impl Nfa {
    /// Create a new NFA with a single non-accepting start state.
    pub fn new() -> Self {
        Nfa { states: vec![NfaState::new()], start: 0 }
    }

    /// Add a new state and return its ID.
    pub fn add_state(&mut self, state: NfaState) -> StateId {
        let id = self.states.len() as StateId;
        self.states.push(state);
        id
    }

    /// Add an epsilon transition from `from` to `to`.
    pub fn add_epsilon(&mut self, from: StateId, to: StateId) {
        self.states[from as usize].epsilon.push(to);
    }

    /// Add a labeled transition from `from` to `to` on `class`.
    pub fn add_transition(&mut self, from: StateId, to: StateId, class: CharClass) {
        self.states[from as usize].transitions.push((class, to));
    }
}

impl Default for Nfa {
    fn default() -> Self {
        Self::new()
    }
}

/// DFA state with deterministic transitions.
///
/// Transitions are stored as a dense array indexed by equivalence class ID.
/// `transitions[class_id]` gives the target state, or `DEAD_STATE` if no
/// transition exists for that class.
#[derive(Debug, Clone)]
pub struct DfaState {
    /// Dense transition table: `transitions[class_id] = target_state`.
    /// Length is always `num_classes` (stored in parent `Dfa`).
    /// `DEAD_STATE` means no transition for that equivalence class.
    pub transitions: Vec<StateId>,
    /// If this is an accepting state, which token kind it produces (primary winner).
    pub accept: Option<TokenKind>,
    /// Tropical weight for this accepting state.
    ///
    /// Inherits from the highest-priority NFA accept state during subset
    /// construction. Lower weight = higher priority.
    /// Non-accepting states have `TropicalWeight::zero()` (infinity).
    pub weight: TropicalWeight,
    /// Alternative accept tokens for this DFA state, sorted by weight (ascending).
    ///
    /// Non-empty only for **ambiguous** states where 2+ distinct `TokenKind`s
    /// are valid (e.g., a keyword like `error` that also matches the identifier
    /// pattern). The primary winner is in `accept`/`weight`; this vec contains
    /// ALL alternatives including the primary, for use by composed dispatch tables.
    ///
    /// Empty for unambiguous states (zero overhead).
    pub alt_accepts: Vec<(TokenKind, TropicalWeight)>,
}

impl DfaState {
    /// Create a new non-accepting DFA state with `num_classes` dead transitions.
    pub fn with_classes(num_classes: usize) -> Self {
        DfaState {
            transitions: vec![DEAD_STATE; num_classes],
            accept: None,
            weight: TropicalWeight::zero(),
            alt_accepts: Vec::new(),
        }
    }

    /// Whether this state has ambiguous accepts (2+ distinct token kinds).
    #[inline]
    pub fn is_ambiguous(&self) -> bool {
        !self.alt_accepts.is_empty()
    }
}

/// A complete DFA (collection of states with a designated start state).
#[derive(Debug, Clone)]
pub struct Dfa {
    pub states: Vec<DfaState>,
    pub start: StateId,
    /// Number of equivalence classes (alphabet size after partitioning).
    pub num_classes: usize,
}

impl Dfa {
    /// Create a new DFA with a single non-accepting start state.
    pub fn new(num_classes: usize) -> Self {
        Dfa {
            states: vec![DfaState::with_classes(num_classes)],
            start: 0,
            num_classes,
        }
    }

    /// Add a new state and return its ID.
    pub fn add_state(&mut self, state: DfaState) -> StateId {
        let id = self.states.len() as StateId;
        self.states.push(state);
        id
    }

    /// O(1) transition lookup: returns target state or `DEAD_STATE`.
    #[inline]
    pub fn transition(&self, state: StateId, class: ClassId) -> StateId {
        self.states[state as usize].transitions[class as usize]
    }

    /// Set a transition: `state --class--> target`.
    #[inline]
    pub fn set_transition(&mut self, state: StateId, class: ClassId, target: StateId) {
        self.states[state as usize].transitions[class as usize] = target;
    }

    /// Whether any DFA state has ambiguous accepts (2+ distinct token kinds).
    pub fn has_ambiguous_accepts(&self) -> bool {
        self.states.iter().any(|s| s.is_ambiguous())
    }

    /// Collect all ambiguous DFA states: `(state_id, alt_accepts_slice)`.
    ///
    /// Returns only states with 2+ distinct token kinds in their accept set.
    /// The returned slices are sorted by weight (ascending = best first).
    pub fn ambiguous_states(&self) -> Vec<(StateId, &[(TokenKind, TropicalWeight)])> {
        self.states
            .iter()
            .enumerate()
            .filter(|(_, s)| s.is_ambiguous())
            .map(|(i, s)| (i as StateId, s.alt_accepts.as_slice()))
            .collect()
    }
}

/// An NFA fragment (sub-automaton) with a designated start and accept state.
/// Used during Thompson's construction to build up the NFA incrementally.
#[derive(Debug, Clone)]
pub struct NfaFragment {
    pub start: StateId,
    pub accept: StateId,
}

/// Terminal pattern extracted from a grammar, ready for NFA construction.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TerminalPattern {
    /// The exact text of the terminal (e.g. "+", "error", "$$proc(").
    pub text: String,
    /// The token kind this terminal produces.
    pub kind: TokenKind,
    /// Whether this is a keyword (identifier-like text that should take
    /// priority over the generic identifier pattern).
    pub is_keyword: bool,
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::minimize::minimize_dfa;
    use super::nfa::{build_nfa, BuiltinNeeds};
    use super::partition::compute_equivalence_classes;
    use super::subset::subset_construction;
    use crate::LiteralPatterns;
    use proptest::prelude::*;

    // ── Helpers ──────────────────────────────────────────────────────────

    /// Simulate running `input` through a DFA, returning the accept token of
    /// the final state if the entire input is consumed without hitting a dead
    /// state.
    fn dfa_accepts(
        dfa: &Dfa,
        partition: &partition::AlphabetPartition,
        input: &[u8],
    ) -> Option<TokenKind> {
        let mut state = dfa.start;
        for &byte in input {
            let class = partition.classify(byte);
            state = dfa.transition(state, class);
            if state == DEAD_STATE {
                return None;
            }
        }
        dfa.states[state as usize].accept.clone()
    }

    /// Build a simple NFA that accepts a single literal byte string.
    /// The accept state is tagged with `kind`.
    fn nfa_for_literal(text: &[u8], kind: TokenKind) -> Nfa {
        let mut nfa = Nfa::new();
        let mut current = nfa.start;
        for &byte in text {
            let next = nfa.add_state(NfaState::new());
            nfa.add_transition(current, next, CharClass::Single(byte));
            current = next;
        }
        nfa.states[current as usize].accept = Some(kind.clone());
        nfa.states[current as usize].weight = TropicalWeight::from_priority(kind.priority());
        nfa
    }

    /// Build an NFA that accepts either of two literal byte strings (alternation).
    /// Each branch gets its own accept token.
    fn nfa_for_alternation(
        a: &[u8],
        kind_a: TokenKind,
        b: &[u8],
        kind_b: TokenKind,
    ) -> Nfa {
        let mut nfa = Nfa::new();
        let start = nfa.start;

        // Branch A
        let a_start = nfa.add_state(NfaState::new());
        nfa.add_epsilon(start, a_start);
        let mut current = a_start;
        for &byte in a {
            let next = nfa.add_state(NfaState::new());
            nfa.add_transition(current, next, CharClass::Single(byte));
            current = next;
        }
        nfa.states[current as usize].accept = Some(kind_a.clone());
        nfa.states[current as usize].weight = TropicalWeight::from_priority(kind_a.priority());

        // Branch B
        let b_start = nfa.add_state(NfaState::new());
        nfa.add_epsilon(start, b_start);
        current = b_start;
        for &byte in b {
            let next = nfa.add_state(NfaState::new());
            nfa.add_transition(current, next, CharClass::Single(byte));
            current = next;
        }
        nfa.states[current as usize].accept = Some(kind_b.clone());
        nfa.states[current as usize].weight = TropicalWeight::from_priority(kind_b.priority());

        nfa
    }

    /// Build an NFA for a Kleene star over a single byte: `b*`.
    /// Accepts zero or more repetitions of `byte`, tagged with `kind`.
    fn nfa_for_star(byte: u8, kind: TokenKind) -> Nfa {
        let mut nfa = Nfa::new();
        let start = nfa.start;
        let loop_state = nfa.add_state(NfaState::new());
        let accept = nfa.add_state(NfaState::accepting(kind));

        // start -> accept (zero repetitions)
        nfa.add_epsilon(start, accept);
        // start -> loop_state
        nfa.add_epsilon(start, loop_state);
        // loop_state --byte--> loop_state (repeat)
        nfa.add_transition(loop_state, loop_state, CharClass::Single(byte));
        // loop_state -> accept
        nfa.add_epsilon(loop_state, accept);

        nfa
    }

    /// Run the full pipeline on a hand-built NFA: partition -> DFA -> minimize.
    /// Returns (dfa, minimized_dfa, partition).
    fn full_pipeline(nfa: &Nfa) -> (Dfa, Dfa, partition::AlphabetPartition) {
        let part = compute_equivalence_classes(nfa);
        let dfa = subset_construction(nfa, &part);
        let min_dfa = minimize_dfa(&dfa);
        (dfa, min_dfa, part)
    }

    // ── Unit tests: single-character NFA ─────────────────────────────────

    #[test]
    fn test_single_char_nfa_to_dfa() {
        let nfa = nfa_for_literal(b"a", TokenKind::Fixed("a".into()));
        let (dfa, _min_dfa, part) = full_pipeline(&nfa);

        assert_eq!(dfa_accepts(&dfa, &part, b"a"), Some(TokenKind::Fixed("a".into())));
        assert_eq!(dfa_accepts(&dfa, &part, b"b"), None);
        assert_eq!(dfa_accepts(&dfa, &part, b""), None);
        assert_eq!(dfa_accepts(&dfa, &part, b"aa"), None);
    }

    // ── Unit tests: alternation NFA ──────────────────────────────────────

    #[test]
    fn test_alternation_nfa_to_dfa() {
        let nfa = nfa_for_alternation(
            b"a",
            TokenKind::Fixed("a".into()),
            b"b",
            TokenKind::Fixed("b".into()),
        );
        let (dfa, _min_dfa, part) = full_pipeline(&nfa);

        assert_eq!(dfa_accepts(&dfa, &part, b"a"), Some(TokenKind::Fixed("a".into())));
        assert_eq!(dfa_accepts(&dfa, &part, b"b"), Some(TokenKind::Fixed("b".into())));
        assert_eq!(dfa_accepts(&dfa, &part, b"c"), None);
        assert_eq!(dfa_accepts(&dfa, &part, b""), None);
        assert_eq!(dfa_accepts(&dfa, &part, b"ab"), None);
    }

    // ── Unit tests: concatenation NFA ────────────────────────────────────

    #[test]
    fn test_concatenation_nfa_to_dfa() {
        let nfa = nfa_for_literal(b"ab", TokenKind::Fixed("ab".into()));
        let (dfa, _min_dfa, part) = full_pipeline(&nfa);

        assert_eq!(dfa_accepts(&dfa, &part, b"ab"), Some(TokenKind::Fixed("ab".into())));
        assert_eq!(dfa_accepts(&dfa, &part, b"a"), None);
        assert_eq!(dfa_accepts(&dfa, &part, b"b"), None);
        assert_eq!(dfa_accepts(&dfa, &part, b"ba"), None);
        assert_eq!(dfa_accepts(&dfa, &part, b"abc"), None);
        assert_eq!(dfa_accepts(&dfa, &part, b""), None);
    }

    // ── Unit tests: minimize preserves language ──────────────────────────

    #[test]
    fn test_minimize_preserves_language_single_char() {
        let nfa = nfa_for_literal(b"x", TokenKind::Fixed("x".into()));
        let (dfa, min_dfa, part) = full_pipeline(&nfa);

        // Minimized DFA must accept exactly the same inputs
        for input in &[b"x" as &[u8], b"", b"y", b"xx", b"xy"] {
            assert_eq!(
                dfa_accepts(&dfa, &part, input),
                dfa_accepts(&min_dfa, &part, input),
                "minimize changed acceptance for input {:?}",
                String::from_utf8_lossy(input)
            );
        }
        // Minimized should have no more states
        assert!(min_dfa.states.len() <= dfa.states.len());
    }

    #[test]
    fn test_minimize_preserves_language_alternation() {
        let nfa = nfa_for_alternation(
            b"foo",
            TokenKind::Fixed("foo".into()),
            b"bar",
            TokenKind::Fixed("bar".into()),
        );
        let (dfa, min_dfa, part) = full_pipeline(&nfa);

        let test_inputs: &[&[u8]] = &[
            b"foo", b"bar", b"fo", b"ba", b"foobar", b"baz", b"f", b"", b"x",
        ];
        for input in test_inputs {
            assert_eq!(
                dfa_accepts(&dfa, &part, input),
                dfa_accepts(&min_dfa, &part, input),
                "minimize changed acceptance for input {:?}",
                String::from_utf8_lossy(input)
            );
        }
    }

    #[test]
    fn test_minimize_preserves_language_prefix_sharing() {
        // "==" and "=" share a common prefix — minimization must not merge
        // the intermediate and final states.
        let nfa = nfa_for_alternation(
            b"=",
            TokenKind::Fixed("=".into()),
            b"==",
            TokenKind::Fixed("==".into()),
        );
        let (dfa, min_dfa, part) = full_pipeline(&nfa);

        let test_inputs: &[&[u8]] = &[b"=", b"==", b"===", b"", b"!"];
        for input in test_inputs {
            assert_eq!(
                dfa_accepts(&dfa, &part, input),
                dfa_accepts(&min_dfa, &part, input),
                "minimize changed acceptance for prefix-sharing input {:?}",
                String::from_utf8_lossy(input)
            );
        }
    }

    // ── Unit tests: Kleene star ──────────────────────────────────────────

    #[test]
    fn test_kleene_star_nfa_to_dfa() {
        let kind = TokenKind::Fixed("a*".into());
        let nfa = nfa_for_star(b'a', kind.clone());
        let (dfa, min_dfa, part) = full_pipeline(&nfa);

        // a* accepts "", "a", "aa", "aaa", ...
        assert_eq!(dfa_accepts(&dfa, &part, b""), Some(kind.clone()));
        assert_eq!(dfa_accepts(&dfa, &part, b"a"), Some(kind.clone()));
        assert_eq!(dfa_accepts(&dfa, &part, b"aaa"), Some(kind.clone()));
        // rejects anything with non-'a' bytes
        assert_eq!(dfa_accepts(&dfa, &part, b"b"), None);
        assert_eq!(dfa_accepts(&dfa, &part, b"ab"), None);

        // minimized DFA preserves the language
        for input in &[b"" as &[u8], b"a", b"aa", b"aaa", b"b", b"ab", b"ba"] {
            assert_eq!(
                dfa_accepts(&dfa, &part, input),
                dfa_accepts(&min_dfa, &part, input),
                "minimize changed acceptance for star input {:?}",
                String::from_utf8_lossy(input)
            );
        }
    }

    // ── Unit tests: build_nfa pipeline ───────────────────────────────────

    #[test]
    fn test_build_nfa_pipeline_operators() {
        let terminals = vec![
            TerminalPattern {
                text: "+".into(),
                kind: TokenKind::Fixed("+".into()),
                is_keyword: false,
            },
            TerminalPattern {
                text: "->".into(),
                kind: TokenKind::Fixed("->".into()),
                is_keyword: false,
            },
        ];
        let needs = BuiltinNeeds::default();
        let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
        let (dfa, min_dfa, part) = full_pipeline(&nfa);

        assert_eq!(dfa_accepts(&dfa, &part, b"+"), Some(TokenKind::Fixed("+".into())));
        assert_eq!(dfa_accepts(&dfa, &part, b"->"), Some(TokenKind::Fixed("->".into())));
        assert_eq!(dfa_accepts(&dfa, &part, b"-"), None);

        // Minimized DFA agrees
        for input in &[b"+" as &[u8], b"->", b"-", b"", b">"] {
            assert_eq!(
                dfa_accepts(&dfa, &part, input),
                dfa_accepts(&min_dfa, &part, input),
                "minimize changed acceptance for operator input {:?}",
                String::from_utf8_lossy(input)
            );
        }
    }

    #[test]
    fn test_build_nfa_pipeline_ident_integer() {
        let terminals = vec![];
        let needs = BuiltinNeeds {
            ident: true,
            integer: true,
            float: false,
            string_lit: false,
            boolean: false,
        };
        let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
        let (dfa, min_dfa, part) = full_pipeline(&nfa);

        // Identifiers
        assert_eq!(dfa_accepts(&dfa, &part, b"x"), Some(TokenKind::Ident));
        assert_eq!(dfa_accepts(&dfa, &part, b"foo"), Some(TokenKind::Ident));
        // Integers
        assert_eq!(dfa_accepts(&dfa, &part, b"42"), Some(TokenKind::Integer));
        assert_eq!(dfa_accepts(&dfa, &part, b"0"), Some(TokenKind::Integer));
        // Neither
        assert_eq!(dfa_accepts(&dfa, &part, b""), None);

        // Minimized DFA agrees on all test inputs
        for input in &[b"x" as &[u8], b"foo", b"42", b"0", b""] {
            assert_eq!(
                dfa_accepts(&dfa, &part, input),
                dfa_accepts(&min_dfa, &part, input),
                "minimize changed acceptance for ident/int input {:?}",
                String::from_utf8_lossy(input)
            );
        }
    }

    // ── Unit tests: DFA with redundant states ────────────────────────────

    #[test]
    fn test_minimize_reduces_redundant_states() {
        // Construct a DFA by hand with two equivalent states that should be
        // merged by minimization.
        //
        // State 0 (start, non-accepting):
        //   class 0 -> state 1
        //   class 1 -> state 2
        // State 1 (accepting Fixed("x")):
        //   (dead)
        // State 2 (accepting Fixed("x")):
        //   (dead)
        //
        // States 1 and 2 are equivalent (same accept, same transitions).
        let num_classes = 2;
        let mut dfa = Dfa::new(num_classes);
        let s1 = dfa.add_state(DfaState {
            transitions: vec![DEAD_STATE; num_classes],
            accept: Some(TokenKind::Fixed("x".into())),
            weight: TropicalWeight::from_priority(10),
            alt_accepts: Vec::new(),
        });
        let s2 = dfa.add_state(DfaState {
            transitions: vec![DEAD_STATE; num_classes],
            accept: Some(TokenKind::Fixed("x".into())),
            weight: TropicalWeight::from_priority(10),
            alt_accepts: Vec::new(),
        });
        dfa.set_transition(0, 0, s1);
        dfa.set_transition(0, 1, s2);

        assert_eq!(dfa.states.len(), 3);
        let min_dfa = minimize_dfa(&dfa);
        // States 1 and 2 should be merged into one
        assert_eq!(
            min_dfa.states.len(),
            2,
            "minimization should merge 2 equivalent accepting states into 1"
        );
    }

    // ── Proptest: minimize preserves language on random inputs ────────────

    /// Strategy that generates printable ASCII byte strings of length 0..20.
    fn ascii_input() -> impl Strategy<Value = Vec<u8>> {
        proptest::collection::vec(32u8..=126, 0..20)
    }

    proptest! {
        /// For a grammar with operators "+", "++", "-", "->", the minimized DFA
        /// must accept exactly the same language as the pre-minimization DFA on
        /// arbitrary ASCII inputs.
        #[test]
        fn proptest_minimize_preserves_operators(input in ascii_input()) {
            let terminals = vec![
                TerminalPattern {
                    text: "+".into(),
                    kind: TokenKind::Fixed("+".into()),
                    is_keyword: false,
                },
                TerminalPattern {
                    text: "++".into(),
                    kind: TokenKind::Fixed("++".into()),
                    is_keyword: false,
                },
                TerminalPattern {
                    text: "-".into(),
                    kind: TokenKind::Fixed("-".into()),
                    is_keyword: false,
                },
                TerminalPattern {
                    text: "->".into(),
                    kind: TokenKind::Fixed("->".into()),
                    is_keyword: false,
                },
            ];
            let needs = BuiltinNeeds {
                ident: true,
                integer: true,
                float: false,
                string_lit: false,
                boolean: false,
            };
            let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
            let (dfa, min_dfa, part) = full_pipeline(&nfa);
            prop_assert_eq!(
                dfa_accepts(&dfa, &part, &input),
                dfa_accepts(&min_dfa, &part, &input),
                "minimize changed acceptance for random input {:?}",
                String::from_utf8_lossy(&input)
            );
        }

        /// For a grammar with keyword "error" + ident, the minimized DFA must
        /// preserve both primary accept and ambiguity status for arbitrary inputs.
        #[test]
        fn proptest_minimize_preserves_keyword_ident(input in ascii_input()) {
            let terminals = vec![
                TerminalPattern {
                    text: "error".into(),
                    kind: TokenKind::Fixed("error".into()),
                    is_keyword: true,
                },
                TerminalPattern {
                    text: "if".into(),
                    kind: TokenKind::Fixed("if".into()),
                    is_keyword: true,
                },
            ];
            let needs = BuiltinNeeds {
                ident: true,
                integer: true,
                float: false,
                string_lit: false,
                boolean: false,
            };
            let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
            let (dfa, min_dfa, part) = full_pipeline(&nfa);

            // Primary accept must match
            prop_assert_eq!(
                dfa_accepts(&dfa, &part, &input),
                dfa_accepts(&min_dfa, &part, &input),
                "minimize changed primary accept for keyword input {:?}",
                String::from_utf8_lossy(&input)
            );

            // Ambiguity status must also be preserved: walk both DFAs and compare
            // is_ambiguous at the final state.
            let final_state_orig = {
                let mut s = dfa.start;
                for &byte in &input {
                    let c = part.classify(byte);
                    s = dfa.transition(s, c);
                    if s == DEAD_STATE { break; }
                }
                s
            };
            let final_state_min = {
                let mut s = min_dfa.start;
                for &byte in &input {
                    let c = part.classify(byte);
                    s = min_dfa.transition(s, c);
                    if s == DEAD_STATE { break; }
                }
                s
            };

            // Both dead or both live
            prop_assert_eq!(
                final_state_orig == DEAD_STATE,
                final_state_min == DEAD_STATE,
            );

            // If both live, ambiguity must match
            if final_state_orig != DEAD_STATE && final_state_min != DEAD_STATE {
                prop_assert_eq!(
                    dfa.states[final_state_orig as usize].is_ambiguous(),
                    min_dfa.states[final_state_min as usize].is_ambiguous(),
                    "minimize changed ambiguity for keyword input {:?}",
                    String::from_utf8_lossy(&input)
                );
            }
        }

        /// For a hand-built NFA (alternation of two literals), the minimized DFA
        /// must accept exactly the same language on random inputs.
        #[test]
        fn proptest_minimize_preserves_hand_built_alternation(input in ascii_input()) {
            let nfa = nfa_for_alternation(
                b"hello",
                TokenKind::Fixed("hello".into()),
                b"world",
                TokenKind::Fixed("world".into()),
            );
            let (dfa, min_dfa, part) = full_pipeline(&nfa);
            prop_assert_eq!(
                dfa_accepts(&dfa, &part, &input),
                dfa_accepts(&min_dfa, &part, &input),
                "minimize changed acceptance for hand-built alternation on {:?}",
                String::from_utf8_lossy(&input)
            );
        }

        /// For a hand-built Kleene-star NFA (a*), the minimized DFA must accept
        /// exactly the same language on random inputs.
        #[test]
        fn proptest_minimize_preserves_kleene_star(input in ascii_input()) {
            let kind = TokenKind::Fixed("a*".into());
            let nfa = nfa_for_star(b'a', kind);
            let (dfa, min_dfa, part) = full_pipeline(&nfa);
            prop_assert_eq!(
                dfa_accepts(&dfa, &part, &input),
                dfa_accepts(&min_dfa, &part, &input),
                "minimize changed acceptance for Kleene star on {:?}",
                String::from_utf8_lossy(&input)
            );
        }

        /// Subset construction produces a DFA with no more states than the
        /// powerset bound (2^n for n NFA states), though in practice far fewer.
        /// This property-tests that the DFA state count is within reason.
        #[test]
        fn proptest_dfa_state_count_bounded(
            a in "[a-z]{1,4}",
            b in "[a-z]{1,4}",
        ) {
            let nfa = nfa_for_alternation(
                a.as_bytes(),
                TokenKind::Fixed(a.clone()),
                b.as_bytes(),
                TokenKind::Fixed(b.clone()),
            );
            let part = compute_equivalence_classes(&nfa);
            let dfa = subset_construction(&nfa, &part);
            let min_dfa = minimize_dfa(&dfa);

            // Sanity: DFA should have at least 2 states (start + at least 1 accept)
            prop_assert!(dfa.states.len() >= 2);
            // Minimized should not exceed original
            prop_assert!(min_dfa.states.len() <= dfa.states.len());
            // Neither should be absurdly large for small NFAs
            prop_assert!(
                dfa.states.len() < 100,
                "DFA too large: {} states for alternation of {:?} | {:?}",
                dfa.states.len(),
                a,
                b
            );
        }
    }

    // ── Proptest: equivalence class partition consistency ─────────────────

    proptest! {
        /// Every byte must be assigned to a valid equivalence class, and
        /// bytes within the same class must be interchangeable in all DFA
        /// transitions.
        #[test]
        fn proptest_partition_class_ids_valid(
            term_text in "[+\\-*/=<>!]{1,3}",
        ) {
            let terminals = vec![TerminalPattern {
                text: term_text.clone(),
                kind: TokenKind::Fixed(term_text),
                is_keyword: false,
            }];
            let needs = BuiltinNeeds {
                ident: true,
                integer: true,
                float: false,
                string_lit: false,
                boolean: false,
            };
            let nfa = build_nfa(&terminals, &needs, &LiteralPatterns::default());
            let part = compute_equivalence_classes(&nfa);

            // Every byte's class ID must be < num_classes
            for byte in 0u8..=255 {
                let class = part.classify(byte);
                prop_assert!(
                    (class as usize) < part.num_classes,
                    "byte {} classified as {} but num_classes is {}",
                    byte,
                    class,
                    part.num_classes
                );
            }

            // num_classes must have exactly that many representatives
            prop_assert_eq!(part.class_representatives.len(), part.num_classes);
        }
    }
}
