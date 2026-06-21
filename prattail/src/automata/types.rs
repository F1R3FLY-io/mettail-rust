use super::*;

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
#[non_exhaustive]
pub enum TokenKind {
    /// End of file
    Eof,
    /// Identifier (variable name)
    Ident,
    /// Integer literal
    Integer,
    /// Integer literal for a specific category (e.g. Int, UInt32).
    IntegerLit(String),
    /// Rational literal for a specific category (e.g. BigRat).
    RationalLit(String),
    /// Fixed-point literal for a specific category (e.g. Fixed).
    FixedPointLit(String),
    /// Float literal
    Float,
    /// Boolean literal `true`
    True,
    /// Boolean literal `false`
    False,
    /// Custom boolean literal (regex match, eval converts text to bool). Used when literal_patterns.boolean is Some.
    BooleanLit,
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
    /// L3 (2026-04-28): lex failure at this position — no DFA accept matched
    /// the current bytes. Carries an error category for diagnostics and
    /// recovery decisions. Treated as a real token in the parse so error
    /// recovery (#64 / L12 WPDS-edge recovery) can compose lex failures
    /// with parser failures uniformly.
    LexError(LexErrorKind),
}

/// L3 (2026-04-28): kind of lex failure. Used by `TokenKind::LexError` to
/// distinguish "no match" (DFA dead-end) from semantic eval failures
/// (e.g., `parse_int_lit` returning `Err` for an out-of-range literal).
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
pub enum LexErrorKind {
    /// The DFA had no accepting transition at this byte position. The
    /// nearest match-or-recovery target is determined by the lex-Fork
    /// machinery (#64 / L12).
    NoMatch,
    /// A token DFA accepted but its eval block returned `Err`. The lexer
    /// reports this so parser-side recovery can react to a malformed
    /// literal differently from a structural mismatch.
    EvalFailed,
    /// An unexpected end-of-input was reached mid-token (e.g., unterminated
    /// string literal).
    UnexpectedEof,
}

impl TokenKind {
    /// Priority for disambiguation. Higher value = higher priority.
    /// Keywords beat identifiers; fixed terminals beat character-class tokens.
    pub fn priority(&self) -> u8 {
        match self {
            TokenKind::Eof => 0,
            TokenKind::Ident => 1,
            TokenKind::Integer | TokenKind::IntegerLit(_) | TokenKind::RationalLit(_) => 2,
            // Fixed-point literals share a prefix with floats (e.g. `3.5` vs `3.5p0`); priority must
            // be >= float so ties at the same DFA position prefer fixed (maximal munch still picks
            // the longer match when the DFA can extend with `p…`).
            TokenKind::FixedPointLit(_) => 4,
            TokenKind::Float => 3,
            TokenKind::True | TokenKind::False | TokenKind::BooleanLit => 10,
            TokenKind::StringLit => 2,
            TokenKind::Fixed(_) => 10,
            TokenKind::Dollar => 5,
            TokenKind::DoubleDollar => 6,
            // Default priority for custom tokens; actual priority is set from
            // CustomTokenSpec.priority at the NFA accept-state level.
            TokenKind::Custom(_) => 2,
            // LexError tokens are surfaced for recovery; lowest priority so
            // any successful match preempts the error variant.
            TokenKind::LexError(_) => 0,
        }
    }
}

// ─── Token family classification ────────────────────────────────────────────
//
// `TokenFamily` provides typed dispatch for token variant names, eliminating
// string comparisons throughout codegen. Every token variant belongs to exactly
// one family; families with payloads (Integer, Float, Rational, …) require
// wildcard patterns (`Token::Name(_)`) in generated match arms.

/// Classification of a Token enum variant into a known family.
///
/// Used by codegen sites to determine:
/// - Whether a variant carries a payload (→ wildcard match pattern)
/// - The canonical match-arm pattern string for code emission
/// - Whether it's a built-in lexer family or a user-defined custom token
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum TokenFamily {
    Eof,
    Ident,
    Integer,
    Float,
    Boolean,
    StringLit,
    Rational,
    FixedPoint,
    Dollar,
    DoubleDollar,
    /// A fixed keyword/punctuation token or a user-defined custom token.
    /// Custom tokens may carry payloads — checked via `CustomTokenSpec`.
    Other,
}

impl TokenFamily {
    /// Classify a token variant name into its family.
    ///
    /// This is the **single** string→enum gateway. All downstream dispatch
    /// uses the returned `TokenFamily` via pattern matching — no further
    /// string comparisons.
    pub fn from_name(name: &str) -> Self {
        match name {
            "Eof" => Self::Eof,
            "Ident" => Self::Ident,
            "Integer" => Self::Integer,
            "Float" => Self::Float,
            "Boolean" => Self::Boolean,
            "StringLit" => Self::StringLit,
            "Rational" => Self::Rational,
            "FixedPoint" => Self::FixedPoint,
            "Dollar" => Self::Dollar,
            "DoubleDollar" => Self::DoubleDollar,
            _ => Self::Other,
        }
    }

    /// Whether this family's Token variant carries a payload and therefore
    /// requires a wildcard pattern (`Token::Name(_)`) in match arms.
    #[inline]
    pub const fn has_payload(self) -> bool {
        matches!(
            self,
            Self::Ident
                | Self::Integer
                | Self::Float
                | Self::Boolean
                | Self::StringLit
                | Self::Rational
                | Self::FixedPoint
                | Self::Dollar
                | Self::DoubleDollar
        )
    }

    /// Whether this is a built-in lexer family (driven by `BuiltinNeeds`
    /// and `LiteralPatterns`) as opposed to a user-defined custom token.
    #[inline]
    pub const fn is_builtin(self) -> bool {
        !matches!(self, Self::Other)
    }

    /// The canonical match-arm pattern for this family in generated code.
    ///
    /// Returns `Some("Token::Name(_)")` for payload families,
    /// `Some("Token::Eof")` for Eof, `None` for `Other` (caller must
    /// format `Token::{name}` or `Token::{name}(_)` based on
    /// `CustomTokenSpec::payload_type`).
    pub const fn match_pattern(self) -> Option<&'static str> {
        match self {
            Self::Eof => Some("Token::Eof"),
            Self::Ident => Some("Token::Ident(_)"),
            Self::Integer => Some("Token::Integer(_, _)"),
            Self::Float => Some("Token::Float(_)"),
            Self::Boolean => Some("Token::Boolean(_)"),
            Self::StringLit => Some("Token::StringLit(_)"),
            Self::Rational => Some("Token::Rational(_)"),
            Self::FixedPoint => Some("Token::FixedPoint(_)"),
            Self::Dollar => Some("Token::Dollar(_)"),
            Self::DoubleDollar => Some("Token::DoubleDollar(_)"),
            Self::Other => None,
        }
    }
}

/// A character class for NFA transitions.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
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
    ///
    /// This is the highest-priority candidate (lowest tropical weight) among
    /// all accepting NFA states in the subset. Additional candidates are
    /// tracked via `accept_alternatives` (feature branch) for ambiguity
    /// detection and disambiguation.
    pub accept: Option<TokenKind>,
    /// Tropical weight for the default accepting token kind.
    ///
    /// Inherits from the highest-priority NFA accept state during subset
    /// construction. Lower weight = higher priority. Non-accepting states
    /// have `TropicalWeight::zero()` (infinity).
    pub weight: TropicalWeight,
    /// All accepting token kinds reachable in this DFA state, sorted by
    /// weight (ascending = highest priority first).
    ///
    /// Populated when 2+ distinct `TokenKind`s accept at this state — either
    /// because the patterns overlap semantically (e.g., a keyword like
    /// `error` that also matches the identifier pattern) or because the
    /// lexer wants to try multiple candidates in priority order with
    /// per-candidate `eval` fallback when evaluation fails.
    ///
    /// The primary winner is also in `accept`/`weight`; this vec contains
    /// ALL alternatives including the primary for use by composed dispatch
    /// tables and fallback-based literal evaluation.
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
