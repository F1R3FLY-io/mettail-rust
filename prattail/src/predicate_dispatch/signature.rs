use super::*;

// ═══════════════════════════════════════════════════════════════════════════════
// §1  PredicateSignature — bitfield of automata varieties
// ═══════════════════════════════════════════════════════════════════════════════

/// Bitfield encoding which automata varieties are relevant to a predicate formula.
///
/// Each bit corresponds to one of the 15 advanced automata modules (M1–M15).
/// The base signature (M1 | M10) is always set: M1 provides the predicate algebra
/// foundation and M10 provides the MSO specification language.
///
/// ```text
/// Bit 0:  M1  Symbolic        (REG — regular, Boolean closure)
/// Bit 1:  M2  Büchi           (ω-REG — omega-regular)
/// Bit 2:  M3  AWA             (ALT — alternating, universal branching)
/// Bit 3:  M4  VPA             (VPL — visibly pushdown)
/// Bit 4:  M5  Parity Tree     (μCLR — mu-calculus)
/// Bit 5:  M6  Register        (DATA — data languages)
/// Bit 6:  M7  Probabilistic   (PROB — stochastic)
/// Bit 7:  M8  Multi-Tape      (k-TAPE — multi-stream)
/// Bit 8:  M9  Multiset        (MSET — commutative)
/// Bit 9:  M10 W. MSO          (MSO — full definability)
/// Bit 10: M11 Two-Way         (2-WAY — bidirectional)
/// Bit 11: M12 Linear Arith    (PRESB — Presburger arithmetic)
/// Bit 12: M13 Unification     (UNIF — structural unification)
/// Bit 13: M14 Subtype Lattice (LAT — subtype hierarchy)
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PredicateSignature(u16);

impl PredicateSignature {
    pub const M1_SYMBOLIC: u16 = 1 << 0;
    pub const M2_BUCHI: u16 = 1 << 1;
    pub const M3_AWA: u16 = 1 << 2;
    pub const M4_VPA: u16 = 1 << 3;
    pub const M5_PARITY_TREE: u16 = 1 << 4;
    pub const M6_REGISTER: u16 = 1 << 5;
    pub const M7_PROBABILISTIC: u16 = 1 << 6;
    pub const M8_MULTI_TAPE: u16 = 1 << 7;
    pub const M9_MULTISET: u16 = 1 << 8;
    pub const M10_MSO: u16 = 1 << 9;
    pub const M11_TWO_WAY: u16 = 1 << 10;
    pub const M12_LINEAR_ARITHMETIC: u16 = 1 << 11;
    pub const M13_UNIFICATION: u16 = 1 << 12;
    pub const M14_SUBTYPE_LATTICE: u16 = 1 << 13;
    pub const M15_SFT: u16 = 1 << 14;

    /// Number of module bits defined.
    pub const NUM_MODULES: u32 = 15;

    /// All bits set: 0x7FFF.
    pub const ALL: u16 = (1 << Self::NUM_MODULES) - 1;

    /// Default: M1 + M10 always active.
    pub const BASE: u16 = Self::M1_SYMBOLIC | Self::M10_MSO;

    /// Create a new signature with the base modules (M1 + M10) active.
    pub fn new() -> Self {
        Self(Self::BASE)
    }

    /// Create a signature from a raw u16 value.
    pub fn from_raw(bits: u16) -> Self {
        Self(bits)
    }

    /// Get the raw u16 value.
    pub fn raw(self) -> u16 {
        self.0
    }

    /// Check if a specific module bit is set.
    pub fn contains(self, module_bit: u16) -> bool {
        self.0 & module_bit != 0
    }

    /// Set a specific module bit.
    pub fn set(&mut self, module_bit: u16) {
        self.0 |= module_bit;
    }

    /// Union of two signatures (bitwise OR).
    pub fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Intersection of two signatures (bitwise AND).
    pub fn intersection(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    /// Count of active module bits.
    pub fn count(self) -> u32 {
        self.0.count_ones()
    }

    /// Whether this is the base signature (only M1 + M10).
    pub fn is_base_only(self) -> bool {
        self.0 == Self::BASE
    }

    /// Whether all 11 module bits are set.
    pub fn is_full(self) -> bool {
        self.0 & Self::ALL == Self::ALL
    }

    /// Whether no bits are set (degenerate — should not occur from extract_features).
    pub fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Module bit constant by index (0–10).
    pub fn module_bit(index: u32) -> u16 {
        debug_assert!(index < Self::NUM_MODULES, "module index out of range");
        1u16 << index
    }
}

impl Default for PredicateSignature {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Display for PredicateSignature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "0x{:04X} [", self.0)?;
        let names = [
            "M1:Sym",
            "M2:Büchi",
            "M3:AWA",
            "M4:VPA",
            "M5:PTree",
            "M6:Reg",
            "M7:Prob",
            "M8:MTape",
            "M9:MSet",
            "M10:MSO",
            "M11:2Way",
            "M12:Presb",
            "M13:Unif",
            "M14:Lat",
            "M15:Sft",
        ];
        let mut first = true;
        for (i, name) in names.iter().enumerate() {
            if self.0 & (1 << i) != 0 {
                if !first {
                    write!(f, ", ")?;
                }
                write!(f, "{name}")?;
                first = false;
            }
        }
        write!(f, "]")
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// §2  ModuleId — enumeration of the 11 advanced automata modules
// ═══════════════════════════════════════════════════════════════════════════════

/// Identifies one of the 15 advanced automata modules.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ModuleId {
    /// M1: Symbolic automata (predicate algebra foundation).
    Symbolic = 0,
    /// M2: Büchi automata (omega-regular properties).
    Buchi = 1,
    /// M3: Alternating Weighted Automata (universal branching).
    Awa = 2,
    /// M4: Visibly Pushdown Automata (balanced structures).
    Vpa = 3,
    /// M5: Parity Tree Automata (mu-calculus model checking).
    ParityTree = 4,
    /// M6: Register Automata (data equality/freshness).
    Register = 5,
    /// M7: Probabilistic Automata (statistical disambiguation).
    Probabilistic = 6,
    /// M8: Multi-Tape Automata (multi-channel operations).
    MultiTape = 7,
    /// M9: Multiset Automata (cardinality predicates).
    Multiset = 8,
    /// M10: Weighted MSO (specification language foundation).
    Mso = 9,
    /// M11: Two-Way Transducer (cross-channel constraints).
    TwoWay = 10,
    /// M12: Linear Arithmetic (Presburger automata for numeric guards).
    LinearArithmetic = 11,
    /// M13: Unification (structural pattern matching via Martelli-Montanari).
    Unification = 12,
    /// M14: Subtype Lattice (type hierarchy with join/meet).
    SubtypeLattice = 13,
    /// M15: Symbolic Finite Transducer (output-producing transductions).
    Sft = 14,
}

impl ModuleId {
    /// All 15 module IDs in order.
    pub const ALL: [ModuleId; 15] = [
        Self::Symbolic,
        Self::Buchi,
        Self::Awa,
        Self::Vpa,
        Self::ParityTree,
        Self::Register,
        Self::Probabilistic,
        Self::MultiTape,
        Self::Multiset,
        Self::Mso,
        Self::TwoWay,
        Self::LinearArithmetic,
        Self::Unification,
        Self::SubtypeLattice,
        Self::Sft,
    ];

    /// The signature bit for this module.
    pub fn bit(self) -> u16 {
        1u16 << (self as u32)
    }

    /// Human-readable name.
    pub fn name(self) -> &'static str {
        match self {
            Self::Symbolic => "Symbolic",
            Self::Buchi => "Büchi",
            Self::Awa => "AWA",
            Self::Vpa => "VPA",
            Self::ParityTree => "Parity Tree",
            Self::Register => "Register",
            Self::Probabilistic => "Probabilistic",
            Self::MultiTape => "Multi-Tape",
            Self::Multiset => "Multiset",
            Self::Mso => "Weighted MSO",
            Self::TwoWay => "Two-Way",
            Self::LinearArithmetic => "Linear Arithmetic",
            Self::Unification => "Unification",
            Self::SubtypeLattice => "Subtype Lattice",
            Self::Sft => "SFT",
        }
    }

    /// Feature gate name for this module.
    pub fn feature_gate(self) -> &'static str {
        match self {
            Self::Symbolic => "symbolic-automata",
            Self::Buchi => "omega",
            Self::Awa => "alternating",
            Self::Vpa => "vpa",
            Self::ParityTree => "parity-tree-automata",
            Self::Register => "register-automata",
            Self::Probabilistic => "probabilistic",
            Self::MultiTape => "multi-tape",
            Self::Multiset => "multiset-automata",
            Self::Mso => "weighted-mso",
            Self::TwoWay => "two-way-transducer",
            Self::LinearArithmetic => "presburger",
            Self::Unification => "unification",
            Self::SubtypeLattice => "lattice-theory",
            Self::Sft => "sft",
        }
    }

    /// Estimated relative cost (lower = cheaper). Used for scheduling.
    pub fn estimated_cost(self) -> u32 {
        match self {
            Self::Symbolic | Self::Mso => 1,      // always-on foundations
            Self::Multiset | Self::Register => 2, // lightweight analysis
            Self::SubtypeLattice => 2,            // decidable, finite universe
            Self::Buchi | Self::Awa => 3,         // omega-regular
            Self::LinearArithmetic | Self::Unification => 3, // constraint theories
            Self::Vpa | Self::ParityTree => 4,    // pushdown / tree
            Self::Probabilistic | Self::MultiTape => 5, // WFST-dependent
            Self::TwoWay => 6,                    // most complex
            Self::Sft => 5,                       // depends on symbolic-automata + weighted-mso
        }
    }
}

impl fmt::Display for ModuleId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "M{}:{}", *self as u32 + 1, self.name())
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// §3  ChannelContext — variable-to-channel mapping for cross-channel detection
// ═══════════════════════════════════════════════════════════════════════════════

/// Maps variable names to the channel they are bound on.
///
/// Used by `extract_features()` to detect cross-channel references:
/// if a `Relation` argument refers to a variable bound on a different channel
/// than the current context, this triggers M8 (Multi-Tape) and M11 (Two-Way).
#[derive(Debug, Clone, Default)]
pub struct ChannelContext {
    /// `variable_name → channel_name`.
    bindings: HashMap<String, String>,
    /// The channel currently being analyzed (if any).
    current_channel: Option<String>,
}

impl ChannelContext {
    /// Create an empty context.
    pub fn new() -> Self {
        Self::default()
    }

    /// Bind a variable to a channel.
    pub fn bind(&mut self, var: String, channel: String) {
        self.bindings.insert(var, channel);
    }

    /// Set the current channel being analyzed.
    pub fn set_current_channel(&mut self, channel: String) {
        self.current_channel = Some(channel);
    }

    /// Get the channel a variable is bound on.
    pub fn channel_of(&self, var: &str) -> Option<&str> {
        self.bindings.get(var).map(|s| s.as_str())
    }

    /// Check if a variable reference crosses channels (bound on a different
    /// channel than `current_channel`).
    pub fn is_cross_channel(&self, var: &str) -> bool {
        if let (Some(bound_ch), Some(current_ch)) =
            (self.channel_of(var), self.current_channel.as_deref())
        {
            bound_ch != current_ch
        } else {
            false
        }
    }

    /// The set of distinct channels referenced.
    pub fn distinct_channels(&self) -> HashSet<&str> {
        self.bindings.values().map(|s| s.as_str()).collect()
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// §4  PredicateProfile — quantitative analysis of a single predicate
// ═══════════════════════════════════════════════════════════════════════════════

/// Quantitative profile of a single predicate formula, produced by
/// `extract_features()` or `extract_features_mso()`.
#[derive(Debug, Clone)]
pub struct PredicateProfile {
    /// Which automata varieties are relevant (bitfield).
    pub signature: PredicateSignature,
    /// Maximum quantifier nesting depth.
    pub quantifier_depth: u32,
    /// Number of distinct channels referenced.
    pub channel_count: u32,
    /// Number of register-relevant variables (equality/freshness comparisons).
    pub register_count: u32,
    /// Whether a backward (cross-channel) constraint was detected.
    pub has_backward_constraint: bool,
    /// Whether cardinality atoms (count, >=, <=) were found.
    pub has_cardinality: bool,
    /// Whether recursive predicate definitions (letprop / fixpoints) were found.
    pub has_recursive_predicate: bool,
    /// Whether arithmetic comparisons (linear arithmetic) were found.
    pub has_arithmetic: bool,
    /// Whether structural unification / pattern matching was detected.
    pub has_unification: bool,
    /// Whether subtype / type hierarchy constraints were detected.
    pub has_subtype: bool,
    /// Decidability tier from `classify_decidability()`.
    pub decidability_tier: DecidabilityTier,
}

impl PredicateProfile {
    /// Create a base profile (M1 + M10 only, all metrics zero).
    pub fn base() -> Self {
        Self {
            signature: PredicateSignature::new(),
            quantifier_depth: 0,
            channel_count: 0,
            register_count: 0,
            has_backward_constraint: false,
            has_cardinality: false,
            has_recursive_predicate: false,
            has_arithmetic: false,
            has_unification: false,
            has_subtype: false,
            decidability_tier: DecidabilityTier::CompileTimeDecidable,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// §5  Feature Extraction — PredicateExpr → PredicateProfile
// ═══════════════════════════════════════════════════════════════════════════════

// ── Relation Name Fallbacks ──────────────────────────────────────────────
//
// The following `is_*_relation()` functions classify `PredicateExpr::Relation`
// names into constraint theory modules when no explicit `guards { theories {} }`
// registration owns the corresponding theory kind. Explicit registrations are
// checked by `theory_registered()` below and bypass these fallbacks.
//
// Design notes:
//
// 1. **Backward-compatible approximation**: The fallbacks preserve the original
//    M1–M11 keyword-based behavior for grammars that do not opt into
//    data-driven theory registration.
//
// 2. **Explicit registration wins**: User-defined languages that introduce novel
//    relation names should register their theory in `guards { theories {} }`.
//    Once a known theory kind is registered, its fallback classifier is not used
//    for that grammar.
//
// 3. **Overlap**: Some relation names appear in multiple classifiers (e.g.,
//    ">=" appears in both `is_cardinality_relation` and `is_arithmetic_relation`).
//    This is intentional — a relation may activate multiple modules, and
//    `walk_predicate()` calls all classifiers independently.

// ─────────────────────────────────────────────────────────────────────────────
// Theory-kind classification for `guards { theories { } }` integration
// ─────────────────────────────────────────────────────────────────────────────
//
// `TheoryKind` is the closed set of theory categories the dispatch pipeline
// recognizes. When a `theories { }` sub-block in a `guards { }` block
// registers a theory whose Rust type matches one of these kinds, the
// corresponding heuristic activation path (terminal scan, relation-name
// match) is bypassed and the explicit registration becomes the sole
// authority for the affected automaton modules.
//
// New theory kinds are added by extending this enum and the `known_theory_kind`
// matcher. The kind is intentionally distinct from the user-visible registration
// `name` (e.g., `arithmetic`) — the kind classifies *which decision procedure*
// is in use, while the name is a local label.
//
// See: docs/design/dispatch/predicate-dispatch-integration.md

/// A closed enumeration of constraint-theory kinds the pipeline recognizes.
///
/// Each variant corresponds to a class of theory-type names that the bridge
/// from `language!` produces (the bridge stringifies `syn::Type` via
/// `quote!(#ty).to_string()`). The `known_theory_kind` matcher accepts
/// equivalent spellings — e.g., both `"PresburgerAlgebra"` and
/// `"PresburgerTheory"` map to `TheoryKind::Presburger`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TheoryKind {
    /// Linear integer arithmetic (Presburger). Activates M12.
    Presburger,
    /// First-order syntactic unification. Activates M13.
    Unification,
    /// Subtype lattice (`join`/`meet`/`<:`). Activates M14.
    Lattice,
    /// Equality and freshness over data values. Activates M6.
    Register,
    /// Cardinality and AC-matching over collections. Activates M9.
    Multiset,
    /// Recursive predicate definitions (`letprop`, μ/ν fixpoints).
    /// Activates M4 + M5.
    Fixpoint,
}

/// Map a stringified theory type (from `GuardConfigSpec::theories[i].theory_type`)
/// to its corresponding `TheoryKind`. Returns `None` for unknown types so
/// new theory implementations can be registered without immediately
/// disabling any heuristics.
pub fn known_theory_kind(theory_type: &str) -> Option<TheoryKind> {
    match theory_type {
        "PresburgerAlgebra" | "Presburger" | "PresburgerTheory" => Some(TheoryKind::Presburger),
        "UnificationTheory" | "Unification" => Some(TheoryKind::Unification),
        "LatticeTheory" | "Lattice" => Some(TheoryKind::Lattice),
        "RegisterTheory" | "EqualityTheory" => Some(TheoryKind::Register),
        "MultisetTheory" | "CardinalityTheory" => Some(TheoryKind::Multiset),
        "FixpointTheory" => Some(TheoryKind::Fixpoint),
        _ => None,
    }
}

/// Whether the given guard config explicitly registers a theory of the given kind.
///
/// Used by `classify_grammar_with_config` and `walk_predicate_with_config` to
/// gate heuristic fallbacks: when an explicit theory of the matching kind is
/// registered, the heuristic for that kind is bypassed and the explicit
/// registration becomes the sole authority for the corresponding module bits.
///
/// Backward compatible: when `gc` is `None`, this returns `false` for every
/// kind, so all heuristics run as before.
pub fn theory_registered(gc: Option<&crate::GuardConfigSpec>, kind: TheoryKind) -> bool {
    let Some(gc) = gc else {
        return false;
    };
    gc.theories
        .iter()
        .any(|t| known_theory_kind(&t.theory_type) == Some(kind))
}
