//! Automata infrastructure for lexer generation.
//!
//! Provides NFA/DFA types, traits, and the lexer generation pipeline:
//! `Terminals -> NFA -> DFA -> Minimize -> Equiv Classes -> Codegen`

pub mod codegen;
pub mod minimize;
pub mod nfa;
pub mod partition;
pub mod semiring;
pub mod subset;

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
    /// If this is an accepting state, which token kind it produces.
    pub accept: Option<TokenKind>,
    /// Tropical weight for this accepting state.
    ///
    /// Inherits from the highest-priority NFA accept state during subset
    /// construction. Lower weight = higher priority.
    /// Non-accepting states have `TropicalWeight::zero()` (infinity).
    pub weight: TropicalWeight,
}

impl DfaState {
    /// Create a new non-accepting DFA state with `num_classes` dead transitions.
    pub fn with_classes(num_classes: usize) -> Self {
        DfaState {
            transitions: vec![DEAD_STATE; num_classes],
            accept: None,
            weight: TropicalWeight::zero(),
        }
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
