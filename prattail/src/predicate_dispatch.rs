//! # Predicate Dispatch Automaton — Module Selection via Algebraic Variety Classification
//!
//! Decomposes predicate formulas into algebraic "morphemes" (structural features),
//! classifies them into automata varieties (Eilenberg's variety theorem), and directs
//! only the applicable advanced automata modules (M1–M11) to run in Phase 7.
//!
//! **Eilenberg connection**: Rather than computing syntactic monoids at runtime
//! (exponential), we detect variety membership directly from formula AST structure
//! in O(|AST|) time. Feature extraction is a conservative approximation — it may
//! activate extra modules but never misses a needed one.
//!
//! ## Self-Referential Verification
//!
//! The dispatch algebra (`DispatchAlgebra`) implements M1's `BooleanAlgebra` trait,
//! enabling construction of a `SymbolicAutomaton<DispatchAlgebra>` that formally
//! verifies completeness (every valid predicate activates ≥ M1 + M10) and
//! consistency (no contradictory module combinations).

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::symbolic::{BooleanAlgebra, DecidabilityTier, PredicateExpr, SymbolicAutomaton};
use crate::weighted_mso::WeightedMsoFormula;
use crate::pipeline::CategoryInfo;
use crate::SyntaxItemSpec;

// ═══════════════════════════════════════════════════════════════════════════════
// §1  PredicateSignature — bitfield of automata varieties
// ═══════════════════════════════════════════════════════════════════════════════

/// Bitfield encoding which automata varieties are relevant to a predicate formula.
///
/// Each bit corresponds to one of the 11 advanced automata modules (M1–M11).
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

    /// Number of module bits defined.
    pub const NUM_MODULES: u32 = 11;

    /// All bits set: 0x07FF.
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
            "M1:Sym", "M2:Büchi", "M3:AWA", "M4:VPA", "M5:PTree",
            "M6:Reg", "M7:Prob", "M8:MTape", "M9:MSet", "M10:MSO", "M11:2Way",
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

/// Identifies one of the 11 advanced automata modules.
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
}

impl ModuleId {
    /// All 11 module IDs in order.
    pub const ALL: [ModuleId; 11] = [
        Self::Symbolic, Self::Buchi, Self::Awa, Self::Vpa, Self::ParityTree,
        Self::Register, Self::Probabilistic, Self::MultiTape, Self::Multiset,
        Self::Mso, Self::TwoWay,
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
        }
    }

    /// Estimated relative cost (lower = cheaper). Used for scheduling.
    pub fn estimated_cost(self) -> u32 {
        match self {
            Self::Symbolic | Self::Mso => 1,           // always-on foundations
            Self::Multiset | Self::Register => 2,      // lightweight analysis
            Self::Buchi | Self::Awa => 3,              // omega-regular
            Self::Vpa | Self::ParityTree => 4,         // pushdown / tree
            Self::Probabilistic | Self::MultiTape => 5, // WFST-dependent
            Self::TwoWay => 6,                         // most complex
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
        if let (Some(bound_ch), Some(current_ch)) = (self.channel_of(var), self.current_channel.as_deref()) {
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
            decidability_tier: DecidabilityTier::CompileTimeDecidable,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// §5  Feature Extraction — PredicateExpr → PredicateProfile
// ═══════════════════════════════════════════════════════════════════════════════

/// Equality-like relation names that trigger M6 (Register).
fn is_equality_relation(name: &str) -> bool {
    matches!(
        name,
        "eq" | "neq" | "equal" | "not_equal" | "fresh"
            | "==" | "!=" | "equals" | "related"
    )
}

/// Cardinality-like relation names that trigger M9 (Multiset).
fn is_cardinality_relation(name: &str) -> bool {
    matches!(
        name,
        "count" | "size" | "cardinality" | "length"
            | ">=" | "<=" | ">" | "<" | "at_least" | "at_most"
    )
}

/// Fixpoint/recursive relation names that trigger M4 (VPA) + M5 (Parity Tree).
fn is_fixpoint_relation(name: &str) -> bool {
    matches!(name, "letprop" | "fixpoint" | "mu" | "nu" | "letrec" | "recursive")
}

/// Extract variety features from a `PredicateExpr` in O(|AST|) time.
///
/// Single post-order traversal accumulating:
/// - Module bits (signature)
/// - Quantifier depth
/// - Channel/register counts
/// - Boolean flags for backward constraints, cardinality, recursion
///
/// The signature is a conservative approximation: it may activate extra modules
/// but never misses a needed one (Lemma 1.1 in variety-classification.md).
pub fn extract_features(expr: &PredicateExpr, ctx: &ChannelContext) -> PredicateProfile {
    let mut profile = PredicateProfile::base();
    let mut channels_seen: HashSet<String> = HashSet::new();
    let mut register_vars: HashSet<String> = HashSet::new();
    let mut depth: u32 = 0;
    let mut max_depth: u32 = 0;

    walk_predicate(
        expr,
        ctx,
        &mut profile.signature,
        &mut depth,
        &mut max_depth,
        &mut channels_seen,
        &mut register_vars,
        &mut profile.has_backward_constraint,
        &mut profile.has_cardinality,
        &mut profile.has_recursive_predicate,
    );

    profile.quantifier_depth = max_depth;
    profile.channel_count = channels_seen.len() as u32;
    profile.register_count = register_vars.len() as u32;
    profile.decidability_tier = crate::symbolic::classify_decidability(expr);

    // Multi-guard heuristic: ≥2 channels suggests selectivity ordering need.
    if channels_seen.len() >= 2 {
        profile.signature.set(PredicateSignature::M7_PROBABILISTIC);
        profile.signature.set(PredicateSignature::M8_MULTI_TAPE);
    }

    profile
}

/// Recursive AST walker for `PredicateExpr` feature extraction.
#[allow(clippy::too_many_arguments)]
fn walk_predicate(
    expr: &PredicateExpr,
    ctx: &ChannelContext,
    sig: &mut PredicateSignature,
    depth: &mut u32,
    max_depth: &mut u32,
    channels: &mut HashSet<String>,
    registers: &mut HashSet<String>,
    has_backward: &mut bool,
    has_cardinality: &mut bool,
    has_recursive: &mut bool,
) {
    match expr {
        PredicateExpr::True | PredicateExpr::False | PredicateExpr::Atom(_) => {
            // Base cases: only M1 + M10 (already in base signature)
        }

        PredicateExpr::Not(inner) => {
            walk_predicate(inner, ctx, sig, depth, max_depth, channels, registers, has_backward, has_cardinality, has_recursive);
        }

        PredicateExpr::And(a, b) | PredicateExpr::Or(a, b) => {
            walk_predicate(a, ctx, sig, depth, max_depth, channels, registers, has_backward, has_cardinality, has_recursive);
            walk_predicate(b, ctx, sig, depth, max_depth, channels, registers, has_backward, has_cardinality, has_recursive);
        }

        PredicateExpr::ForallFinite { body, .. } => {
            sig.set(PredicateSignature::M3_AWA); // universal branching
            *depth += 1;
            *max_depth = (*max_depth).max(*depth);
            walk_predicate(body, ctx, sig, depth, max_depth, channels, registers, has_backward, has_cardinality, has_recursive);
            *depth -= 1;
        }

        PredicateExpr::ExistsFinite { body, .. } => {
            *depth += 1;
            *max_depth = (*max_depth).max(*depth);
            walk_predicate(body, ctx, sig, depth, max_depth, channels, registers, has_backward, has_cardinality, has_recursive);
            *depth -= 1;
        }

        PredicateExpr::ForallInfinite { body, .. } => {
            sig.set(PredicateSignature::M2_BUCHI); // omega-regular
            sig.set(PredicateSignature::M3_AWA);   // universal branching
            *depth += 1;
            *max_depth = (*max_depth).max(*depth);
            walk_predicate(body, ctx, sig, depth, max_depth, channels, registers, has_backward, has_cardinality, has_recursive);
            *depth -= 1;
        }

        PredicateExpr::ExistsInfinite { body, .. } => {
            sig.set(PredicateSignature::M2_BUCHI); // omega-regular
            *depth += 1;
            *max_depth = (*max_depth).max(*depth);
            walk_predicate(body, ctx, sig, depth, max_depth, channels, registers, has_backward, has_cardinality, has_recursive);
            *depth -= 1;
        }

        PredicateExpr::Relation { name, args } => {
            if is_equality_relation(name) {
                sig.set(PredicateSignature::M6_REGISTER);
                for arg in args {
                    registers.insert(arg.clone());
                }
            }
            if is_cardinality_relation(name) {
                sig.set(PredicateSignature::M9_MULTISET);
                *has_cardinality = true;
            }
            // Fixpoint/recursive relation → VPA + Parity Tree
            if is_fixpoint_relation(name) {
                sig.set(PredicateSignature::M4_VPA);
                sig.set(PredicateSignature::M5_PARITY_TREE);
                *has_recursive = true;
            }
            // Cross-channel detection
            for arg in args {
                if ctx.is_cross_channel(arg) {
                    sig.set(PredicateSignature::M8_MULTI_TAPE);
                    sig.set(PredicateSignature::M11_TWO_WAY);
                    *has_backward = true;
                }
                if let Some(ch) = ctx.channel_of(arg) {
                    channels.insert(ch.to_string());
                }
            }
            // Default: if not equality or cardinality, still a data comparison
            if !is_equality_relation(name) && !is_cardinality_relation(name) {
                sig.set(PredicateSignature::M6_REGISTER);
                for arg in args {
                    registers.insert(arg.clone());
                }
            }
        }

        PredicateExpr::Bounded { body, .. } => {
            walk_predicate(body, ctx, sig, depth, max_depth, channels, registers, has_backward, has_cardinality, has_recursive);
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// §6  Feature Extraction — WeightedMsoFormula → PredicateProfile
// ═══════════════════════════════════════════════════════════════════════════════

/// Extract variety features from a `WeightedMsoFormula` in O(|AST|) time.
///
/// Analogous to `extract_features()` for `PredicateExpr`, with MSO-specific rules:
/// - `ForallSecond` → M3_AWA (universal second-order quantification)
/// - `AtomicPos { label: "letprop" }` → M4_VPA + M5_PARITY_TREE
pub fn extract_features_mso(formula: &WeightedMsoFormula, ctx: &ChannelContext) -> PredicateProfile {
    let mut profile = PredicateProfile::base();
    let mut channels_seen: HashSet<String> = HashSet::new();
    let mut register_vars: HashSet<String> = HashSet::new();
    let mut depth: u32 = 0;
    let mut max_depth: u32 = 0;

    walk_mso_formula(
        formula,
        ctx,
        &mut profile.signature,
        &mut depth,
        &mut max_depth,
        &mut channels_seen,
        &mut register_vars,
        &mut profile.has_backward_constraint,
        &mut profile.has_cardinality,
        &mut profile.has_recursive_predicate,
    );

    profile.quantifier_depth = max_depth;
    profile.channel_count = channels_seen.len() as u32;
    profile.register_count = register_vars.len() as u32;
    profile.decidability_tier = crate::weighted_mso::check_decidability(formula);

    // Multi-guard heuristic
    if channels_seen.len() >= 2 {
        profile.signature.set(PredicateSignature::M7_PROBABILISTIC);
        profile.signature.set(PredicateSignature::M8_MULTI_TAPE);
    }

    profile
}

/// Recursive AST walker for `WeightedMsoFormula` feature extraction.
#[allow(clippy::too_many_arguments)]
fn walk_mso_formula(
    formula: &WeightedMsoFormula,
    ctx: &ChannelContext,
    sig: &mut PredicateSignature,
    depth: &mut u32,
    max_depth: &mut u32,
    channels: &mut HashSet<String>,
    registers: &mut HashSet<String>,
    has_backward: &mut bool,
    has_cardinality: &mut bool,
    has_recursive: &mut bool,
) {
    match formula {
        WeightedMsoFormula::Constant(_) => {
            // Base: only M1 + M10
        }

        WeightedMsoFormula::AtomicPos { label, var } => {
            // "letprop" triggers VPA + Parity Tree (recursive predicate definition)
            if label == "letprop" || label == "fixpoint" || label == "mu" || label == "nu" {
                sig.set(PredicateSignature::M4_VPA);
                sig.set(PredicateSignature::M5_PARITY_TREE);
                *has_recursive = true;
            }
            // Check cross-channel
            if ctx.is_cross_channel(var) {
                sig.set(PredicateSignature::M8_MULTI_TAPE);
                sig.set(PredicateSignature::M11_TWO_WAY);
                *has_backward = true;
            }
            if let Some(ch) = ctx.channel_of(var) {
                channels.insert(ch.to_string());
            }
        }

        WeightedMsoFormula::NegAtomicPos { label, var } => {
            if label == "letprop" || label == "fixpoint" || label == "mu" || label == "nu" {
                sig.set(PredicateSignature::M4_VPA);
                sig.set(PredicateSignature::M5_PARITY_TREE);
                *has_recursive = true;
            }
            if ctx.is_cross_channel(var) {
                sig.set(PredicateSignature::M8_MULTI_TAPE);
                sig.set(PredicateSignature::M11_TWO_WAY);
                *has_backward = true;
            }
            if let Some(ch) = ctx.channel_of(var) {
                channels.insert(ch.to_string());
            }
        }

        WeightedMsoFormula::Order { x, y } | WeightedMsoFormula::NegOrder { x, y } => {
            // Order relations are register-relevant
            sig.set(PredicateSignature::M6_REGISTER);
            registers.insert(x.clone());
            registers.insert(y.clone());
            for v in [x, y] {
                if ctx.is_cross_channel(v) {
                    sig.set(PredicateSignature::M8_MULTI_TAPE);
                    sig.set(PredicateSignature::M11_TWO_WAY);
                    *has_backward = true;
                }
                if let Some(ch) = ctx.channel_of(v) {
                    channels.insert(ch.to_string());
                }
            }
        }

        WeightedMsoFormula::InSet { var, set_var } | WeightedMsoFormula::NotInSet { var, set_var } => {
            // Set membership is MSO-native (already base)
            for v in [var, set_var] {
                if ctx.is_cross_channel(v) {
                    sig.set(PredicateSignature::M8_MULTI_TAPE);
                    sig.set(PredicateSignature::M11_TWO_WAY);
                    *has_backward = true;
                }
                if let Some(ch) = ctx.channel_of(v) {
                    channels.insert(ch.to_string());
                }
            }
        }

        WeightedMsoFormula::And(a, b) | WeightedMsoFormula::Or(a, b) => {
            walk_mso_formula(a, ctx, sig, depth, max_depth, channels, registers, has_backward, has_cardinality, has_recursive);
            walk_mso_formula(b, ctx, sig, depth, max_depth, channels, registers, has_backward, has_cardinality, has_recursive);
        }

        WeightedMsoFormula::ExistsFirst { body, .. } => {
            *depth += 1;
            *max_depth = (*max_depth).max(*depth);
            walk_mso_formula(body, ctx, sig, depth, max_depth, channels, registers, has_backward, has_cardinality, has_recursive);
            *depth -= 1;
        }

        WeightedMsoFormula::ForallFirst { body, .. } => {
            sig.set(PredicateSignature::M3_AWA); // universal first-order
            *depth += 1;
            *max_depth = (*max_depth).max(*depth);
            walk_mso_formula(body, ctx, sig, depth, max_depth, channels, registers, has_backward, has_cardinality, has_recursive);
            *depth -= 1;
        }

        WeightedMsoFormula::ExistsSecond { body, .. } => {
            // Second-order existential: MSO-native (already base)
            *depth += 1;
            *max_depth = (*max_depth).max(*depth);
            walk_mso_formula(body, ctx, sig, depth, max_depth, channels, registers, has_backward, has_cardinality, has_recursive);
            *depth -= 1;
        }

        WeightedMsoFormula::ForallSecond { body, .. } => {
            sig.set(PredicateSignature::M3_AWA); // universal second-order
            *depth += 1;
            *max_depth = (*max_depth).max(*depth);
            walk_mso_formula(body, ctx, sig, depth, max_depth, channels, registers, has_backward, has_cardinality, has_recursive);
            *depth -= 1;
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// §7  GrammarDispatchPlan — per-grammar classification and module schedule
// ═══════════════════════════════════════════════════════════════════════════════

/// Dispatch plan for a grammar: aggregate signature, per-predicate profiles,
/// and an ordered module schedule.
#[derive(Debug, Clone)]
pub struct GrammarDispatchPlan {
    /// Union of all predicate signatures in the grammar.
    pub aggregate_signature: PredicateSignature,
    /// Profile for each predicate found in the grammar.
    pub predicate_profiles: Vec<PredicateProfile>,
    /// Modules to invoke, ordered by estimated cost (cheapest first).
    pub module_schedule: Vec<ModuleId>,
    /// Number of modules that would have run unconditionally but are now skipped.
    pub modules_skipped: u32,
}

impl GrammarDispatchPlan {
    /// Check if a module is needed by this grammar.
    pub fn requires(&self, module: ModuleId) -> bool {
        self.aggregate_signature.contains(module.bit())
    }

    /// Modules that are NOT needed (for diagnostic reporting).
    pub fn skipped_modules(&self) -> Vec<ModuleId> {
        ModuleId::ALL
            .iter()
            .copied()
            .filter(|m| !self.requires(*m))
            .collect()
    }
}

/// Classify a grammar to build a `GrammarDispatchPlan`.
///
/// Scans `all_syntax` for predicate-bearing rules, extracts channel context
/// from multi-category references, computes per-predicate profiles, and unions
/// into an aggregate signature that controls Phase 7 module spawning.
///
/// Currently, since predicates are not yet parsed from grammar rules (they come
/// from the forthcoming predicated-types codegen pipeline), this function
/// constructs a base plan from grammar structure heuristics:
/// - Cross-category rules → multi-tape / two-way potential
/// - Multiple categories → channel context richness
/// - Collection patterns → multiset potential
pub fn classify_grammar(
    all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
    _categories: &[CategoryInfo],
) -> GrammarDispatchPlan {
    let mut aggregate = PredicateSignature::new();
    let profiles = Vec::new();

    // ── Build category reference graph for recursion/cycle detection ──────
    let mut category_refs: HashMap<&str, HashSet<&str>> = HashMap::new();
    let mut rules_per_category: HashMap<&str, usize> = HashMap::new();
    let mut has_binders = false;
    let mut has_branching = false;

    // Terminal symbol sets for bracket detection
    let mut terminals: HashSet<&str> = HashSet::new();

    // Build channel context: each category acts as a "channel"
    let mut ctx = ChannelContext::new();
    for (_label, category, syntax) in all_syntax {
        *rules_per_category.entry(category.as_str()).or_default() += 1;

        // Collect non-terminal references from this rule
        let mut nt_count = 0usize;
        for item in syntax {
            match item {
                SyntaxItemSpec::NonTerminal { category: ref cat, param_name } => {
                    ctx.bind(param_name.clone(), cat.clone());
                    category_refs.entry(category.as_str()).or_default().insert(cat.as_str());
                    nt_count += 1;
                }
                SyntaxItemSpec::Binder { param_name, category: ref cat, .. } => {
                    ctx.bind(param_name.clone(), cat.clone());
                    category_refs.entry(category.as_str()).or_default().insert(cat.as_str());
                    has_binders = true;
                    nt_count += 1;
                }
                SyntaxItemSpec::Collection { param_name, element_category, .. } => {
                    ctx.bind(param_name.clone(), element_category.clone());
                    category_refs.entry(category.as_str()).or_default().insert(element_category.as_str());
                }
                SyntaxItemSpec::Terminal(value) => {
                    terminals.insert(value.as_str());
                }
                _ => {}
            }
        }

        // Track branching: ≥3 non-terminal children in a single rule
        if nt_count >= 3 {
            has_branching = true;
        }

        // Heuristic: cross-category rules suggest multi-tape / two-way patterns
        let referenced_categories: HashSet<&str> = syntax
            .iter()
            .filter_map(|item| match item {
                SyntaxItemSpec::NonTerminal { category: cat, .. } => Some(cat.as_str()),
                SyntaxItemSpec::Binder { category: cat, .. } => Some(cat.as_str()),
                SyntaxItemSpec::Collection { element_category, .. } => Some(element_category.as_str()),
                _ => None,
            })
            .collect();

        if referenced_categories.len() >= 2 {
            aggregate.set(PredicateSignature::M8_MULTI_TAPE);
            // Only set two-way if there's a cross-category reference that differs from rule's category
            let has_cross = referenced_categories.iter().any(|cat| *cat != category.as_str());
            if has_cross {
                aggregate.set(PredicateSignature::M11_TWO_WAY);
            }
        }

        // Collection patterns → multiset potential
        let has_collection = syntax.iter().any(|item| matches!(
            item,
            SyntaxItemSpec::Collection { .. } | SyntaxItemSpec::Sep { .. }
        ));
        if has_collection {
            aggregate.set(PredicateSignature::M9_MULTISET);
        }
    }

    // ── M2 Büchi: Recursive category detection ───────────────────────────
    // A category C is recursive if C ∈ refs(C) (direct self-reference).
    let has_recursion = category_refs.iter().any(|(cat, refs)| refs.contains(cat));
    if has_recursion {
        aggregate.set(PredicateSignature::M2_BUCHI);
    }

    // ── M3 AWA: Multi-branch universal rules ─────────────────────────────
    // Rules with ≥3 non-terminal children suggest universal branching.
    if has_branching {
        aggregate.set(PredicateSignature::M3_AWA);
    }

    // ── M4 VPA: Bracket/delimiter detection ──────────────────────────────
    // Paired call/return terminals indicate visible pushdown structure.
    let call_symbols = ["(", "{", "[", "begin", "do"];
    let return_symbols = [")", "}", "]", "end", "done"];
    let has_call = call_symbols.iter().any(|s| terminals.contains(s));
    let has_return = return_symbols.iter().any(|s| terminals.contains(s));
    if has_call && has_return {
        aggregate.set(PredicateSignature::M4_VPA);
    }

    // ── M5 Parity Tree: Recursive AST with ranked branching ──────────────
    // Recursive category + branching children = tree structure needing
    // mu-calculus fixpoint analysis. Neither alone suffices.
    if has_recursion && has_branching {
        aggregate.set(PredicateSignature::M5_PARITY_TREE);
    }

    // ── M6 Register: Binder/name patterns ────────────────────────────────
    // Binder items introduce variable scopes requiring register automata
    // for scope-correctness and freshness tracking.
    if has_binders {
        aggregate.set(PredicateSignature::M6_REGISTER);
    }

    // ── M7 Probabilistic: Ambiguous rules ────────────────────────────────
    // ≥3 rules in the same category suggest parse ambiguity needing
    // statistical disambiguation. Binary choice is deterministic.
    let has_ambiguity = rules_per_category.values().any(|&count| count >= 3);
    if has_ambiguity {
        aggregate.set(PredicateSignature::M7_PROBABILISTIC);
    }

    // Build module schedule from aggregate signature
    let mut schedule: Vec<ModuleId> = ModuleId::ALL
        .iter()
        .copied()
        .filter(|m| aggregate.contains(m.bit()))
        .collect();
    schedule.sort_by_key(|m| m.estimated_cost());

    let skipped = PredicateSignature::NUM_MODULES - aggregate.count();

    GrammarDispatchPlan {
        aggregate_signature: aggregate,
        predicate_profiles: profiles,
        module_schedule: schedule,
        modules_skipped: skipped,
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// §8  Dispatch Algebra — BooleanAlgebra impl for SFA verification
// ═══════════════════════════════════════════════════════════════════════════════

/// Predicates over `PredicateSignature` values (bit-membership tests).
///
/// Used as the `Predicate` type in `DispatchAlgebra : BooleanAlgebra`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SignaturePred {
    /// Satisfied by all signatures.
    True,
    /// Satisfied by no signatures.
    False,
    /// Satisfied iff bit `i` is set (module M_{i+1} is active).
    HasBit(u16),
    /// Conjunction.
    And(Box<SignaturePred>, Box<SignaturePred>),
    /// Disjunction.
    Or(Box<SignaturePred>, Box<SignaturePred>),
    /// Negation.
    Not(Box<SignaturePred>),
}

impl SignaturePred {
    /// Evaluate this predicate against a concrete signature.
    pub fn eval(&self, sig: PredicateSignature) -> bool {
        match self {
            Self::True => true,
            Self::False => false,
            Self::HasBit(bit) => sig.contains(*bit),
            Self::And(a, b) => a.eval(sig) && b.eval(sig),
            Self::Or(a, b) => a.eval(sig) || b.eval(sig),
            Self::Not(a) => !a.eval(sig),
        }
    }
}

/// Boolean algebra over signature-membership predicates.
///
/// Domain: `PredicateSignature` (u16 bitfields).
/// Predicates: `SignaturePred` (bit-membership tests + Boolean connectives).
///
/// This implements the same `BooleanAlgebra` trait that `IntervalAlgebra` and
/// `CharClassAlgebra` implement in `symbolic.rs`, making the dispatch layer
/// self-referential: M1's trait verifies M1–M11 dispatch.
#[derive(Clone, Debug)]
pub struct DispatchAlgebra;

impl BooleanAlgebra for DispatchAlgebra {
    type Predicate = SignaturePred;
    type Domain = PredicateSignature;

    fn true_pred(&self) -> SignaturePred {
        SignaturePred::True
    }

    fn false_pred(&self) -> SignaturePred {
        SignaturePred::False
    }

    fn and(&self, a: &SignaturePred, b: &SignaturePred) -> SignaturePred {
        match (a, b) {
            (SignaturePred::True, _) => b.clone(),
            (_, SignaturePred::True) => a.clone(),
            (SignaturePred::False, _) | (_, SignaturePred::False) => SignaturePred::False,
            _ => SignaturePred::And(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn or(&self, a: &SignaturePred, b: &SignaturePred) -> SignaturePred {
        match (a, b) {
            (SignaturePred::False, _) => b.clone(),
            (_, SignaturePred::False) => a.clone(),
            (SignaturePred::True, _) | (_, SignaturePred::True) => SignaturePred::True,
            _ => SignaturePred::Or(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn not(&self, a: &SignaturePred) -> SignaturePred {
        match a {
            SignaturePred::True => SignaturePred::False,
            SignaturePred::False => SignaturePred::True,
            SignaturePred::Not(inner) => (**inner).clone(),
            _ => SignaturePred::Not(Box::new(a.clone())),
        }
    }

    fn is_satisfiable(&self, a: &SignaturePred) -> bool {
        // Brute-force over all 2^11 = 2048 signatures (fast enough for 11 bits)
        (0..=PredicateSignature::ALL)
            .any(|bits| a.eval(PredicateSignature::from_raw(bits)))
    }

    fn witness(&self, a: &SignaturePred) -> Option<PredicateSignature> {
        // Fast paths aligned with Rocq witness_satisfies_has_bit theorem:
        // For HasBit(bit), the bit itself is the witness (Nat.land_diag).
        match a {
            SignaturePred::True => Some(PredicateSignature::new()),
            SignaturePred::False => None,
            SignaturePred::HasBit(bit) => {
                if *bit != 0 {
                    Some(PredicateSignature::from_raw(*bit))
                } else {
                    None
                }
            }
            // Compound predicates: brute-force over all 2^11 signatures
            _ => (0..=PredicateSignature::ALL)
                .map(PredicateSignature::from_raw)
                .find(|sig| a.eval(*sig)),
        }
    }

    fn evaluate(&self, pred: &SignaturePred, elem: &PredicateSignature) -> bool {
        pred.eval(*elem)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// §9  Dispatch SFA — verification automaton
// ═══════════════════════════════════════════════════════════════════════════════

/// Build the dispatch SFA: a 13-state automaton (q₀ + 11 module states + q_⊥)
/// that verifies dispatch completeness and consistency.
///
/// State diagram:
/// ```text
///     q₀ ──HasBit(0)──→ ◉ q_M1  (Symbolic)
///        ──HasBit(1)──→ ◉ q_M2  (Büchi)
///        ──HasBit(2)──→ ◉ q_M3  (AWA)
///        ...
///        ──HasBit(10)─→ ◉ q_M11 (Two-Way)
///        ──¬(any bit)─→ ○ q_⊥   (reject)
/// ```
pub fn build_dispatch_sfa() -> SymbolicAutomaton<DispatchAlgebra> {
    let mut sfa = SymbolicAutomaton::new(DispatchAlgebra);

    // q₀ (state 0): initial, non-accepting
    let q0 = sfa.add_state(false, Some("q₀".to_string()));
    sfa.set_initial(q0);

    // 11 module states (states 1–11): all accepting
    for module in &ModuleId::ALL {
        let q = sfa.add_state(true, Some(format!("q_{}", module)));
        sfa.add_transition(q0, q, SignaturePred::HasBit(module.bit()));
    }

    // q_⊥ (state 12): reject state — reached when no bit is set
    let q_reject = sfa.add_state(false, Some("q_⊥".to_string()));
    // Guard: ¬(HasBit(0) ∨ HasBit(1) ∨ ... ∨ HasBit(10))
    let any_bit = (0..PredicateSignature::NUM_MODULES)
        .map(|i| SignaturePred::HasBit(PredicateSignature::module_bit(i)))
        .reduce(|acc, p| SignaturePred::Or(Box::new(acc), Box::new(p)))
        .expect("at least one module");
    let no_bits = SignaturePred::Not(Box::new(any_bit));
    sfa.add_transition(q0, q_reject, no_bits);

    sfa
}

/// Verify that the dispatch SFA accepts every non-zero signature.
///
/// **Theorem 3.1** (Completeness): For every σ ∈ D with σ ≠ 0, A_D accepts σ.
pub fn verify_completeness(sfa: &SymbolicAutomaton<DispatchAlgebra>) -> bool {
    // Check all non-zero signatures in [1, 0x07FF]
    (1..=PredicateSignature::ALL).all(|bits| {
        let sig = PredicateSignature::from_raw(bits);
        sfa.accepts(&[sig])
    })
}

/// Verify that zero signature is rejected (PD01 condition).
pub fn verify_zero_rejected(sfa: &SymbolicAutomaton<DispatchAlgebra>) -> bool {
    !sfa.accepts(&[PredicateSignature::from_raw(0)])
}

/// Find module pairs that are always co-activated.
///
/// Returns pairs (M_i, M_j) such that for every signature produced by
/// `extract_features()`, if M_i is active then M_j is always also active.
pub fn dispatch_overlap_pairs() -> Vec<(ModuleId, ModuleId)> {
    // M1 and M10 are always co-activated (both in BASE)
    // M8 and M11 are typically co-activated (cross-channel triggers both)
    vec![
        (ModuleId::Symbolic, ModuleId::Mso),
        (ModuleId::Mso, ModuleId::Symbolic),
    ]
}

// ═══════════════════════════════════════════════════════════════════════════════
// §10 Dispatch Diagnostics — collected diagnostic data
// ═══════════════════════════════════════════════════════════════════════════════

/// Diagnostic data from predicate dispatch, consumed by lint functions.
#[derive(Debug, Clone)]
pub struct DispatchDiagnostics {
    /// Per-predicate profiles.
    pub profiles: Vec<PredicateProfile>,
    /// Predicates that activate only base modules (PD01 candidates).
    pub degenerate_predicates: Vec<usize>,
    /// Predicates that activate all 11 modules (PD02 candidates).
    pub full_activation_predicates: Vec<usize>,
    /// Total modules skipped across all predicates.
    pub total_modules_skipped: u32,
    /// Cross-channel predicates found when two-way-transducer feature is disabled.
    pub cross_channel_without_two_way: Vec<usize>,
}

impl DispatchDiagnostics {
    /// Compute diagnostics from a `GrammarDispatchPlan`.
    pub fn from_plan(plan: &GrammarDispatchPlan) -> Self {
        let mut degenerate = Vec::new();
        let mut full_activation = Vec::new();
        let mut cross_channel_no_tw = Vec::new();

        for (i, profile) in plan.predicate_profiles.iter().enumerate() {
            if profile.signature.is_base_only() {
                degenerate.push(i);
            }
            if profile.signature.is_full() {
                full_activation.push(i);
            }
            if profile.has_backward_constraint {
                #[cfg(not(feature = "two-way-transducer"))]
                {
                    cross_channel_no_tw.push(i);
                }
            }
        }

        Self {
            profiles: plan.predicate_profiles.clone(),
            degenerate_predicates: degenerate,
            full_activation_predicates: full_activation,
            total_modules_skipped: plan.modules_skipped,
            cross_channel_without_two_way: cross_channel_no_tw,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// §11 PredicateCompiler trait — per-predicate compilation interface
// ═══════════════════════════════════════════════════════════════════════════════

/// Trait for modules that can compile individual predicates.
///
/// Each advanced automata module (M1–M11) implements this trait to provide
/// targeted per-predicate compilation, as opposed to the existing
/// `analyze_from_bundle()` which processes entire grammars.
///
/// Default implementation delegates to the existing `analyze_from_bundle()`
/// for backward compatibility.
pub trait PredicateCompiler {
    /// The analysis output type.
    type Output;

    /// Compile a single predicate formula into this module's analysis.
    ///
    /// The `profile` provides pre-computed variety features to guide compilation.
    fn compile_predicate(
        &self,
        pred: &PredicateExpr,
        profile: &PredicateProfile,
        all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
        categories: &[CategoryInfo],
    ) -> Self::Output;
}

/// Run the per-predicate compilation pipeline.
///
/// For each predicate in the dispatch plan, invokes only the modules whose
/// bits are set in the predicate's signature. Collects results per-module.
pub fn compile_predicate_pipeline(
    plan: &GrammarDispatchPlan,
    _all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
    _categories: &[CategoryInfo],
) -> DispatchDiagnostics {
    // For now, return diagnostics only (compilation delegates to existing
    // analyze_from_bundle() in Phase 7). Per-predicate compilation will be
    // wired in when modules implement PredicateCompiler.
    DispatchDiagnostics::from_plan(plan)
}

// ═══════════════════════════════════════════════════════════════════════════════
// §11b  Sprint C4 — Symbolic Subsumption → Predicate Dispatch Ordering
// ═══════════════════════════════════════════════════════════════════════════════

/// Reorder predicates by guard specificity using subsumption data.
///
/// When `subsumed_guards` data is available from symbolic analysis, more specific
/// guards (those subsumed by more general ones) are tried first. This implements
/// most-specific-first dispatch semantics (Ernst et al. 1998).
///
/// Each entry `(a, b)` in `subsumed_guards` means guard `a` is subsumed by
/// (more specific than) guard `b` — i.e. the language of `a` is a subset of the
/// language of `b`. A predicate's *specificity score* equals the number of
/// subsumption pairs where it appears as the subsumed element: higher score
/// means more guards are strictly more general, so the predicate is more specific.
///
/// Returns the input predicates sorted by specificity (most specific first).
/// Ties are broken by grammar order (index in the original list).
pub fn order_by_specificity(
    predicate_labels: &[String],
    subsumed_guards: &[(String, String)],
) -> Vec<String> {
    if subsumed_guards.is_empty() {
        return predicate_labels.to_vec();
    }

    // Build specificity scores: count how many other predicates subsume each one.
    // Higher count = more specific (more guards are more general than this one).
    let mut specificity: HashMap<&str, usize> =
        HashMap::with_capacity(predicate_labels.len());
    for label in predicate_labels {
        specificity.insert(label.as_str(), 0);
    }

    for (subsumed, _subsumer) in subsumed_guards {
        // subsumed is MORE specific (its guard is contained in subsumer's)
        if let Some(count) = specificity.get_mut(subsumed.as_str()) {
            *count += 1;
        }
    }

    // Sort: higher specificity first, then by original order for ties
    let mut indexed: Vec<(usize, &String)> = predicate_labels.iter().enumerate().collect();
    indexed.sort_by(|(idx_a, label_a), (idx_b, label_b)| {
        let spec_a = specificity.get(label_a.as_str()).copied().unwrap_or(0);
        let spec_b = specificity.get(label_b.as_str()).copied().unwrap_or(0);
        spec_b
            .cmp(&spec_a) // descending specificity
            .then(idx_a.cmp(idx_b)) // ascending grammar order for ties
    });

    indexed
        .into_iter()
        .map(|(_, label)| label.clone())
        .collect()
}

// ═══════════════════════════════════════════════════════════════════════════════
// §12 Tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    // ── PredicateSignature tests ──────────────────────────────────────────

    #[test]
    fn test_signature_base_contains_m1_and_m10() {
        let sig = PredicateSignature::new();
        assert!(sig.contains(PredicateSignature::M1_SYMBOLIC));
        assert!(sig.contains(PredicateSignature::M10_MSO));
        assert!(!sig.contains(PredicateSignature::M2_BUCHI));
        assert_eq!(sig.count(), 2);
    }

    #[test]
    fn test_signature_union() {
        let a = PredicateSignature::from_raw(PredicateSignature::M1_SYMBOLIC);
        let b = PredicateSignature::from_raw(PredicateSignature::M6_REGISTER);
        let c = a.union(b);
        assert!(c.contains(PredicateSignature::M1_SYMBOLIC));
        assert!(c.contains(PredicateSignature::M6_REGISTER));
        assert_eq!(c.count(), 2);
    }

    #[test]
    fn test_signature_is_base_only() {
        assert!(PredicateSignature::new().is_base_only());
        let mut sig = PredicateSignature::new();
        sig.set(PredicateSignature::M3_AWA);
        assert!(!sig.is_base_only());
    }

    #[test]
    fn test_signature_is_full() {
        let sig = PredicateSignature::from_raw(PredicateSignature::ALL);
        assert!(sig.is_full());
        assert!(!PredicateSignature::new().is_full());
    }

    #[test]
    fn test_signature_display() {
        let sig = PredicateSignature::new();
        let s = format!("{sig}");
        assert!(s.contains("M1:Sym"));
        assert!(s.contains("M10:MSO"));
    }

    // ── ModuleId tests ────────────────────────────────────────────────────

    #[test]
    fn test_module_id_bits_are_distinct() {
        let bits: Vec<u16> = ModuleId::ALL.iter().map(|m| m.bit()).collect();
        let unique: HashSet<u16> = bits.iter().copied().collect();
        assert_eq!(bits.len(), unique.len(), "all module bits should be distinct");
    }

    #[test]
    fn test_module_id_count() {
        assert_eq!(ModuleId::ALL.len(), 11);
    }

    // ── extract_features: PredicateExpr tests ─────────────────────────────

    #[test]
    fn test_extract_atom_base_only() {
        let expr = PredicateExpr::Atom("p".to_string());
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.is_base_only(), "Atom should activate only M1+M10");
        assert_eq!(profile.quantifier_depth, 0);
    }

    #[test]
    fn test_extract_true_base_only() {
        let expr = PredicateExpr::True;
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.is_base_only());
    }

    #[test]
    fn test_extract_false_base_only() {
        let expr = PredicateExpr::False;
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.is_base_only());
    }

    #[test]
    fn test_extract_forall_infinite_triggers_m2_m3() {
        let expr = PredicateExpr::ForallInfinite {
            var: "x".to_string(),
            body: Box::new(PredicateExpr::Atom("p".to_string())),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M2_BUCHI), "ForallInfinite → M2");
        assert!(profile.signature.contains(PredicateSignature::M3_AWA), "ForallInfinite → M3");
        assert_eq!(profile.quantifier_depth, 1);
    }

    #[test]
    fn test_extract_exists_infinite_triggers_m2() {
        let expr = PredicateExpr::ExistsInfinite {
            var: "x".to_string(),
            body: Box::new(PredicateExpr::True),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M2_BUCHI), "ExistsInfinite → M2");
        assert!(!profile.signature.contains(PredicateSignature::M3_AWA), "ExistsInfinite should NOT set M3");
    }

    #[test]
    fn test_extract_forall_finite_triggers_m3() {
        let expr = PredicateExpr::ForallFinite {
            var: "x".to_string(),
            domain: vec!["a".to_string(), "b".to_string()],
            body: Box::new(PredicateExpr::True),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M3_AWA), "ForallFinite → M3");
        assert!(!profile.signature.contains(PredicateSignature::M2_BUCHI), "ForallFinite should NOT set M2");
    }

    #[test]
    fn test_extract_exists_finite_no_extra_modules() {
        let expr = PredicateExpr::ExistsFinite {
            var: "x".to_string(),
            domain: vec!["a".to_string()],
            body: Box::new(PredicateExpr::True),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.is_base_only(), "ExistsFinite should only be base");
        assert_eq!(profile.quantifier_depth, 1);
    }

    #[test]
    fn test_extract_equality_relation_triggers_m6() {
        let expr = PredicateExpr::Relation {
            name: "eq".to_string(),
            args: vec!["x".to_string(), "y".to_string()],
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M6_REGISTER), "eq relation → M6");
        assert_eq!(profile.register_count, 2);
    }

    #[test]
    fn test_extract_cardinality_relation_triggers_m9() {
        let expr = PredicateExpr::Relation {
            name: "count".to_string(),
            args: vec!["x".to_string()],
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M9_MULTISET), "count → M9");
        assert!(profile.has_cardinality);
    }

    #[test]
    fn test_extract_cross_channel_triggers_m8_m11() {
        let expr = PredicateExpr::Relation {
            name: "related".to_string(),
            args: vec!["x".to_string()],
        };
        let mut ctx = ChannelContext::new();
        ctx.bind("x".to_string(), "ch1".to_string());
        ctx.set_current_channel("ch2".to_string());
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M8_MULTI_TAPE), "cross-channel → M8");
        assert!(profile.signature.contains(PredicateSignature::M11_TWO_WAY), "cross-channel → M11");
        assert!(profile.has_backward_constraint);
    }

    #[test]
    fn test_extract_multi_channel_triggers_m7() {
        // Create a conjunction referencing vars from two channels
        let expr = PredicateExpr::And(
            Box::new(PredicateExpr::Relation {
                name: "eq".to_string(),
                args: vec!["x".to_string()],
            }),
            Box::new(PredicateExpr::Relation {
                name: "eq".to_string(),
                args: vec!["y".to_string()],
            }),
        );
        let mut ctx = ChannelContext::new();
        ctx.bind("x".to_string(), "ch1".to_string());
        ctx.bind("y".to_string(), "ch2".to_string());
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M7_PROBABILISTIC),
            "≥2 channels → M7");
        assert_eq!(profile.channel_count, 2);
    }

    #[test]
    fn test_extract_deeply_nested() {
        // ∀x. ∃y. ∀∞z. p(x, y, z)
        let expr = PredicateExpr::ForallFinite {
            var: "x".to_string(),
            domain: vec!["a".to_string()],
            body: Box::new(PredicateExpr::ExistsFinite {
                var: "y".to_string(),
                domain: vec!["b".to_string()],
                body: Box::new(PredicateExpr::ForallInfinite {
                    var: "z".to_string(),
                    body: Box::new(PredicateExpr::Atom("p".to_string())),
                }),
            }),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert_eq!(profile.quantifier_depth, 3);
        assert!(profile.signature.contains(PredicateSignature::M2_BUCHI));
        assert!(profile.signature.contains(PredicateSignature::M3_AWA));
    }

    #[test]
    fn test_extract_all_morphemes() {
        // A predicate combining all morpheme types
        let expr = PredicateExpr::ForallInfinite {
            var: "z".to_string(),
            body: Box::new(PredicateExpr::And(
                Box::new(PredicateExpr::Relation {
                    name: "eq".to_string(),
                    args: vec!["x".to_string()],
                }),
                Box::new(PredicateExpr::Relation {
                    name: "count".to_string(),
                    args: vec!["y".to_string()],
                }),
            )),
        };
        let mut ctx = ChannelContext::new();
        ctx.bind("x".to_string(), "ch1".to_string());
        ctx.bind("y".to_string(), "ch2".to_string());
        ctx.set_current_channel("ch3".to_string());
        let profile = extract_features(&expr, &ctx);

        assert!(profile.signature.contains(PredicateSignature::M1_SYMBOLIC));
        assert!(profile.signature.contains(PredicateSignature::M2_BUCHI));
        assert!(profile.signature.contains(PredicateSignature::M3_AWA));
        assert!(profile.signature.contains(PredicateSignature::M6_REGISTER));
        assert!(profile.signature.contains(PredicateSignature::M7_PROBABILISTIC));
        assert!(profile.signature.contains(PredicateSignature::M8_MULTI_TAPE));
        assert!(profile.signature.contains(PredicateSignature::M9_MULTISET));
        assert!(profile.signature.contains(PredicateSignature::M10_MSO));
        assert!(profile.signature.contains(PredicateSignature::M11_TWO_WAY));
    }

    #[test]
    fn test_extract_bounded_body() {
        let expr = PredicateExpr::Bounded {
            body: Box::new(PredicateExpr::ForallInfinite {
                var: "x".to_string(),
                body: Box::new(PredicateExpr::Atom("p".to_string())),
            }),
            bound: 100,
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M2_BUCHI));
        assert!(profile.signature.contains(PredicateSignature::M3_AWA));
    }

    #[test]
    fn test_extract_not_propagates() {
        let expr = PredicateExpr::Not(Box::new(PredicateExpr::ForallInfinite {
            var: "x".to_string(),
            body: Box::new(PredicateExpr::True),
        }));
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M2_BUCHI));
    }

    // ── extract_features_mso: WeightedMsoFormula tests ────────────────────

    #[test]
    fn test_mso_constant_base_only() {
        let formula = WeightedMsoFormula::Constant("c".to_string());
        let ctx = ChannelContext::new();
        let profile = extract_features_mso(&formula, &ctx);
        assert!(profile.signature.is_base_only());
    }

    #[test]
    fn test_mso_forall_first_triggers_m3() {
        let formula = WeightedMsoFormula::ForallFirst {
            var: "x".to_string(),
            body: Box::new(WeightedMsoFormula::Constant("c".to_string())),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features_mso(&formula, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M3_AWA));
        assert_eq!(profile.quantifier_depth, 1);
    }

    #[test]
    fn test_mso_forall_second_triggers_m3() {
        let formula = WeightedMsoFormula::ForallSecond {
            var: "X".to_string(),
            body: Box::new(WeightedMsoFormula::Constant("c".to_string())),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features_mso(&formula, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M3_AWA));
    }

    #[test]
    fn test_mso_exists_first_no_extra() {
        let formula = WeightedMsoFormula::ExistsFirst {
            var: "x".to_string(),
            body: Box::new(WeightedMsoFormula::Constant("c".to_string())),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features_mso(&formula, &ctx);
        assert!(profile.signature.is_base_only());
        assert_eq!(profile.quantifier_depth, 1);
    }

    #[test]
    fn test_mso_exists_second_no_extra() {
        let formula = WeightedMsoFormula::ExistsSecond {
            var: "X".to_string(),
            body: Box::new(WeightedMsoFormula::Constant("c".to_string())),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features_mso(&formula, &ctx);
        assert!(profile.signature.is_base_only());
    }

    #[test]
    fn test_mso_letprop_triggers_m4_m5() {
        let formula = WeightedMsoFormula::AtomicPos {
            label: "letprop".to_string(),
            var: "x".to_string(),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features_mso(&formula, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M4_VPA));
        assert!(profile.signature.contains(PredicateSignature::M5_PARITY_TREE));
        assert!(profile.has_recursive_predicate);
    }

    #[test]
    fn test_mso_fixpoint_triggers_m4_m5() {
        let formula = WeightedMsoFormula::AtomicPos {
            label: "fixpoint".to_string(),
            var: "x".to_string(),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features_mso(&formula, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M4_VPA));
        assert!(profile.signature.contains(PredicateSignature::M5_PARITY_TREE));
    }

    #[test]
    fn test_mso_order_triggers_m6() {
        let formula = WeightedMsoFormula::Order {
            x: "a".to_string(),
            y: "b".to_string(),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features_mso(&formula, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M6_REGISTER));
        assert_eq!(profile.register_count, 2);
    }

    #[test]
    fn test_mso_cross_channel() {
        let formula = WeightedMsoFormula::AtomicPos {
            label: "action".to_string(),
            var: "x".to_string(),
        };
        let mut ctx = ChannelContext::new();
        ctx.bind("x".to_string(), "ch1".to_string());
        ctx.set_current_channel("ch2".to_string());
        let profile = extract_features_mso(&formula, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M8_MULTI_TAPE));
        assert!(profile.signature.contains(PredicateSignature::M11_TWO_WAY));
    }

    #[test]
    fn test_mso_in_set_cross_channel() {
        let formula = WeightedMsoFormula::InSet {
            var: "x".to_string(),
            set_var: "S".to_string(),
        };
        let mut ctx = ChannelContext::new();
        ctx.bind("x".to_string(), "ch1".to_string());
        ctx.set_current_channel("ch2".to_string());
        let profile = extract_features_mso(&formula, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M8_MULTI_TAPE));
        assert!(profile.signature.contains(PredicateSignature::M11_TWO_WAY));
    }

    #[test]
    fn test_mso_and_or_propagate() {
        let formula = WeightedMsoFormula::And(
            Box::new(WeightedMsoFormula::ForallFirst {
                var: "x".to_string(),
                body: Box::new(WeightedMsoFormula::Constant("c".to_string())),
            }),
            Box::new(WeightedMsoFormula::Order {
                x: "a".to_string(),
                y: "b".to_string(),
            }),
        );
        let ctx = ChannelContext::new();
        let profile = extract_features_mso(&formula, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M3_AWA));
        assert!(profile.signature.contains(PredicateSignature::M6_REGISTER));
    }

    // ── GrammarDispatchPlan tests ─────────────────────────────────────────

    #[test]
    fn test_classify_empty_grammar() {
        let plan = classify_grammar(&[], &[]);
        assert!(plan.aggregate_signature.contains(PredicateSignature::M1_SYMBOLIC));
        assert!(plan.aggregate_signature.contains(PredicateSignature::M10_MSO));
    }

    #[test]
    fn test_plan_requires_base_modules() {
        let plan = classify_grammar(&[], &[]);
        assert!(plan.requires(ModuleId::Symbolic));
        assert!(plan.requires(ModuleId::Mso));
    }

    #[test]
    fn test_plan_skipped_modules() {
        let plan = classify_grammar(&[], &[]);
        let skipped = plan.skipped_modules();
        assert!(skipped.contains(&ModuleId::Buchi));
        assert!(skipped.contains(&ModuleId::Register));
        assert!(!skipped.contains(&ModuleId::Symbolic));
    }

    // ── Dispatch Algebra / SFA tests ──────────────────────────────────────

    #[test]
    fn test_dispatch_algebra_true_false() {
        let alg = DispatchAlgebra;
        assert!(alg.is_satisfiable(&SignaturePred::True));
        assert!(!alg.is_satisfiable(&SignaturePred::False));
    }

    #[test]
    fn test_dispatch_algebra_has_bit() {
        let alg = DispatchAlgebra;
        let pred = SignaturePred::HasBit(PredicateSignature::M6_REGISTER);
        assert!(alg.is_satisfiable(&pred));
        let w = alg.witness(&pred).expect("should have witness");
        assert!(w.contains(PredicateSignature::M6_REGISTER));
    }

    #[test]
    fn test_dispatch_algebra_and() {
        let alg = DispatchAlgebra;
        let p = SignaturePred::HasBit(PredicateSignature::M2_BUCHI);
        let q = SignaturePred::HasBit(PredicateSignature::M3_AWA);
        let conj = alg.and(&p, &q);
        assert!(alg.is_satisfiable(&conj));
        let w = alg.witness(&conj).expect("should have witness");
        assert!(w.contains(PredicateSignature::M2_BUCHI));
        assert!(w.contains(PredicateSignature::M3_AWA));
    }

    #[test]
    fn test_dispatch_algebra_not() {
        let alg = DispatchAlgebra;
        let p = SignaturePred::True;
        let np = alg.not(&p);
        assert!(!alg.is_satisfiable(&np));
    }

    #[test]
    fn test_dispatch_algebra_evaluate() {
        let alg = DispatchAlgebra;
        let pred = SignaturePred::HasBit(PredicateSignature::M6_REGISTER);
        let sig_yes = PredicateSignature::from_raw(PredicateSignature::M6_REGISTER);
        let sig_no = PredicateSignature::from_raw(PredicateSignature::M2_BUCHI);
        assert!(alg.evaluate(&pred, &sig_yes));
        assert!(!alg.evaluate(&pred, &sig_no));
    }

    #[test]
    fn test_dispatch_sfa_state_count() {
        let sfa = build_dispatch_sfa();
        // 1 initial + 11 module + 1 reject = 13 states
        assert_eq!(sfa.num_states(), 13);
        // 11 module transitions + 1 reject transition = 12
        assert_eq!(sfa.num_transitions(), 12);
    }

    #[test]
    fn test_dispatch_sfa_completeness() {
        let sfa = build_dispatch_sfa();
        assert!(verify_completeness(&sfa), "all non-zero signatures should be accepted");
    }

    #[test]
    fn test_dispatch_sfa_zero_rejected() {
        let sfa = build_dispatch_sfa();
        assert!(verify_zero_rejected(&sfa), "zero signature should be rejected");
    }

    #[test]
    fn test_dispatch_sfa_base_accepted() {
        let sfa = build_dispatch_sfa();
        assert!(sfa.accepts(&[PredicateSignature::new()]), "base signature should be accepted");
    }

    #[test]
    fn test_dispatch_sfa_full_accepted() {
        let sfa = build_dispatch_sfa();
        assert!(sfa.accepts(&[PredicateSignature::from_raw(PredicateSignature::ALL)]));
    }

    #[test]
    fn test_dispatch_sfa_single_module_accepted() {
        let sfa = build_dispatch_sfa();
        for module in &ModuleId::ALL {
            let sig = PredicateSignature::from_raw(module.bit());
            assert!(sfa.accepts(&[sig]), "single-module signature for {} should be accepted", module);
        }
    }

    #[test]
    fn test_dispatch_sfa_witness_generation() {
        let alg = DispatchAlgebra;
        for module in &ModuleId::ALL {
            let pred = SignaturePred::HasBit(module.bit());
            let w = alg.witness(&pred).expect(&format!("should have witness for {}", module));
            assert!(w.contains(module.bit()));
        }
    }

    // ── ChannelContext tests ──────────────────────────────────────────────

    #[test]
    fn test_channel_context_cross_channel() {
        let mut ctx = ChannelContext::new();
        ctx.bind("x".to_string(), "ch1".to_string());
        ctx.set_current_channel("ch2".to_string());
        assert!(ctx.is_cross_channel("x"));
        assert!(!ctx.is_cross_channel("y")); // unbound
    }

    #[test]
    fn test_channel_context_same_channel() {
        let mut ctx = ChannelContext::new();
        ctx.bind("x".to_string(), "ch1".to_string());
        ctx.set_current_channel("ch1".to_string());
        assert!(!ctx.is_cross_channel("x"));
    }

    // ── DispatchDiagnostics tests ─────────────────────────────────────────

    #[test]
    fn test_diagnostics_from_empty_plan() {
        let plan = classify_grammar(&[], &[]);
        let diag = DispatchDiagnostics::from_plan(&plan);
        assert!(diag.profiles.is_empty());
        assert!(diag.degenerate_predicates.is_empty());
    }

    // ── Dispatch overlap pairs ────────────────────────────────────────────

    #[test]
    fn test_overlap_pairs_m1_m10() {
        let pairs = dispatch_overlap_pairs();
        assert!(pairs.contains(&(ModuleId::Symbolic, ModuleId::Mso)));
        assert!(pairs.contains(&(ModuleId::Mso, ModuleId::Symbolic)));
    }

    // ── PredicateCompiler and pipeline orchestration ──────────────────────

    #[test]
    fn test_compile_predicate_pipeline_returns_diagnostics() {
        let plan = classify_grammar(&[], &[]);
        let diag = compile_predicate_pipeline(&plan, &[], &[]);
        assert!(diag.profiles.is_empty());
    }

    // ── PredicateCompiler trait integration tests ────────────────────────
    //
    // Each test is gated on its module's feature since `predicate-dispatch`
    // only implies `symbolic-automata` and `weighted-mso`.

    #[test]
    fn test_symbolic_compiler_produces_analysis() {
        use crate::symbolic::SymbolicCompiler;
        let compiler = SymbolicCompiler;
        let pred = PredicateExpr::True;
        let profile = extract_features(&pred, &ChannelContext::new());
        let result: crate::symbolic::SymbolicAnalysis =
            compiler.compile_predicate(&pred, &profile, &[], &[]);
        // Empty categories → max(0, 1) = 1 state, 0 transitions
        assert_eq!(result.num_states, 1);
        assert_eq!(result.num_transitions, 0);
    }

    #[cfg(feature = "buchi")]
    #[test]
    fn test_buchi_compiler_produces_analysis() {
        use crate::buchi::BuchiCompiler;
        let compiler = BuchiCompiler;
        let pred = PredicateExpr::ExistsInfinite {
            var: "x".into(),
            body: Box::new(PredicateExpr::True),
        };
        let profile = extract_features(&pred, &ChannelContext::new());
        assert!(profile.signature.contains(PredicateSignature::M2_BUCHI));
        let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
        // Trait call succeeds and returns valid analysis
        assert!(!result.has_accepting_cycle);
    }

    #[cfg(feature = "alternating")]
    #[test]
    fn test_alternating_compiler_produces_analysis() {
        use crate::alternating::AlternatingCompiler;
        let compiler = AlternatingCompiler;
        let pred = PredicateExpr::ForallFinite {
            var: "x".into(),
            domain: vec!["a".into(), "b".into()],
            body: Box::new(PredicateExpr::True),
        };
        let profile = extract_features(&pred, &ChannelContext::new());
        assert!(profile.signature.contains(PredicateSignature::M3_AWA));
        let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
        assert!(result.non_bisimilar_pairs.is_empty());
    }

    #[cfg(feature = "vpa")]
    #[test]
    fn test_vpa_compiler_produces_analysis() {
        use crate::vpa::VpaCompiler;
        let compiler = VpaCompiler;
        let pred = PredicateExpr::True;
        let profile = extract_features(&pred, &ChannelContext::new());
        let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
        // VPA returns Option<VpaAnalysis> — empty grammar yields None
        assert!(result.is_none());
    }

    #[cfg(feature = "parity-tree-automata")]
    #[test]
    fn test_parity_tree_compiler_produces_analysis() {
        use crate::parity_tree::ParityTreeCompiler;
        let compiler = ParityTreeCompiler;
        let pred = PredicateExpr::True;
        let profile = extract_features(&pred, &ChannelContext::new());
        let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
        // Parity tree on empty grammar: language is empty with 0 max priority
        assert!(result.is_empty);
    }

    #[cfg(feature = "register-automata")]
    #[test]
    fn test_register_compiler_produces_analysis() {
        use crate::register_automata::RegisterCompiler;
        let compiler = RegisterCompiler;
        let pred = PredicateExpr::Relation {
            name: "eq".into(),
            args: vec!["x".into(), "y".into()],
        };
        let profile = extract_features(&pred, &ChannelContext::new());
        assert!(profile.signature.contains(PredicateSignature::M6_REGISTER));
        let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
        assert!(result.dead_registers.is_empty());
    }

    #[cfg(feature = "probabilistic")]
    #[test]
    fn test_probabilistic_compiler_produces_analysis() {
        use crate::probabilistic::ProbabilisticCompiler;
        let compiler = ProbabilisticCompiler;
        let pred = PredicateExpr::True;
        let profile = extract_features(&pred, &ChannelContext::new());
        let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
        assert!(result.low_selectivity_rules.is_empty());
    }

    #[cfg(feature = "multi-tape")]
    #[test]
    fn test_multi_tape_compiler_produces_analysis() {
        use crate::multi_tape::MultiTapeCompiler;
        let compiler = MultiTapeCompiler;
        let pred = PredicateExpr::True;
        let profile = extract_features(&pred, &ChannelContext::new());
        let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
        assert!(result.disconnected_tapes.is_empty());
    }

    #[cfg(feature = "multiset-automata")]
    #[test]
    fn test_multiset_compiler_produces_analysis() {
        use crate::multiset_automata::MultisetCompiler;
        let compiler = MultisetCompiler;
        let pred = PredicateExpr::Relation {
            name: "count".into(),
            args: vec!["x".into()],
        };
        let profile = extract_features(&pred, &ChannelContext::new());
        assert!(profile.signature.contains(PredicateSignature::M9_MULTISET));
        let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
        assert!(result.unsatisfiable_constraints.is_empty());
    }

    #[test]
    fn test_mso_compiler_produces_analysis() {
        use crate::weighted_mso::MsoCompiler;
        let compiler = MsoCompiler;
        let pred = PredicateExpr::True;
        let profile = extract_features(&pred, &ChannelContext::new());
        let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
        // MSO on empty syntax classifies into one of the basic formula classes
        assert!(matches!(
            result.formula_class,
            crate::weighted_mso::MsoFormulaClass::Restricted
                | crate::weighted_mso::MsoFormulaClass::RestrictedExistential
                | crate::weighted_mso::MsoFormulaClass::FirstOrder
                | crate::weighted_mso::MsoFormulaClass::Full
        ));
    }

    #[cfg(feature = "two-way-transducer")]
    #[test]
    fn test_two_way_compiler_produces_analysis() {
        use crate::two_way_transducer::TwoWayCompiler;
        let compiler = TwoWayCompiler;
        let pred = PredicateExpr::True;
        let profile = extract_features(&pred, &ChannelContext::new());
        let result = compiler.compile_predicate(&pred, &profile, &[], &[]);
        assert!(result.deadlock_cycles.is_empty());
    }

    #[cfg(all(
        feature = "buchi",
        feature = "alternating",
        feature = "vpa",
        feature = "parity-tree-automata",
        feature = "register-automata",
        feature = "probabilistic",
        feature = "multi-tape",
        feature = "multiset-automata",
        feature = "two-way-transducer",
    ))]
    #[test]
    fn test_all_compilers_implement_predicate_compiler() {
        fn assert_compiler<C: PredicateCompiler>(_c: &C) {}

        assert_compiler(&crate::symbolic::SymbolicCompiler);
        assert_compiler(&crate::buchi::BuchiCompiler);
        assert_compiler(&crate::alternating::AlternatingCompiler);
        assert_compiler(&crate::vpa::VpaCompiler);
        assert_compiler(&crate::parity_tree::ParityTreeCompiler);
        assert_compiler(&crate::register_automata::RegisterCompiler);
        assert_compiler(&crate::probabilistic::ProbabilisticCompiler);
        assert_compiler(&crate::multi_tape::MultiTapeCompiler);
        assert_compiler(&crate::multiset_automata::MultisetCompiler);
        assert_compiler(&crate::weighted_mso::MsoCompiler);
        assert_compiler(&crate::two_way_transducer::TwoWayCompiler);
    }

    // ── GrammarDispatchPlan with real grammar structure ───────────────────

    #[test]
    fn test_classify_grammar_cross_category_activates_m8() {
        let syntax = vec![
            ("PInput".to_string(), "Proc".to_string(), vec![
                SyntaxItemSpec::Terminal("for".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Name".to_string(), param_name: "ch".to_string() },
                SyntaxItemSpec::NonTerminal { category: "Proc".to_string(), param_name: "body".to_string() },
            ]),
        ];
        let categories = vec![
            CategoryInfo { name: "Proc".to_string(), native_type: None, is_primary: true },
            CategoryInfo { name: "Name".to_string(), native_type: None, is_primary: false },
        ];
        let plan = classify_grammar(&syntax, &categories);
        assert!(plan.requires(ModuleId::MultiTape), "cross-category should activate M8");
    }

    #[test]
    fn test_classify_grammar_collection_activates_m9() {
        let syntax = vec![
            ("PList".to_string(), "Proc".to_string(), vec![
                SyntaxItemSpec::Collection {
                    param_name: "elems".to_string(),
                    element_category: "Proc".to_string(),
                    separator: ",".to_string(),
                    kind: crate::recursive::CollectionKind::Vec,
                },
            ]),
        ];
        let plan = classify_grammar(&syntax, &[]);
        assert!(plan.requires(ModuleId::Multiset), "collection should activate M9");
    }

    #[test]
    fn test_module_schedule_is_sorted_by_cost() {
        let plan = classify_grammar(&[], &[]);
        for window in plan.module_schedule.windows(2) {
            assert!(
                window[0].estimated_cost() <= window[1].estimated_cost(),
                "schedule should be sorted by cost: {} vs {}",
                window[0], window[1]
            );
        }
    }

    // ── DispatchDiagnostics tests ─────────────────────────────────────────

    #[test]
    fn test_diagnostics_detects_base_only_predicate() {
        let plan = GrammarDispatchPlan {
            aggregate_signature: PredicateSignature::new(),
            predicate_profiles: vec![PredicateProfile::base()],
            module_schedule: vec![ModuleId::Symbolic, ModuleId::Mso],
            modules_skipped: 9,
        };
        let diag = DispatchDiagnostics::from_plan(&plan);
        assert_eq!(diag.degenerate_predicates, vec![0], "base-only should be degenerate");
    }

    #[test]
    fn test_diagnostics_detects_full_activation() {
        let mut profile = PredicateProfile::base();
        profile.signature = PredicateSignature::from_raw(PredicateSignature::ALL);
        let plan = GrammarDispatchPlan {
            aggregate_signature: PredicateSignature::from_raw(PredicateSignature::ALL),
            predicate_profiles: vec![profile],
            module_schedule: ModuleId::ALL.to_vec(),
            modules_skipped: 0,
        };
        let diag = DispatchDiagnostics::from_plan(&plan);
        assert_eq!(diag.full_activation_predicates, vec![0]);
    }

    // ── Signature arithmetic properties ───────────────────────────────────

    #[test]
    fn test_signature_union_is_commutative() {
        let a = PredicateSignature::from_raw(0b101);
        let b = PredicateSignature::from_raw(0b110);
        assert_eq!(a.union(b), b.union(a));
    }

    #[test]
    fn test_signature_union_is_associative() {
        let a = PredicateSignature::from_raw(0b001);
        let b = PredicateSignature::from_raw(0b010);
        let c = PredicateSignature::from_raw(0b100);
        assert_eq!(a.union(b).union(c), a.union(b.union(c)));
    }

    #[test]
    fn test_signature_intersection_complement() {
        let full = PredicateSignature::from_raw(PredicateSignature::ALL);
        let base = PredicateSignature::new();
        assert_eq!(full.intersection(base), base);
    }

    // ── ChannelContext edge cases ─────────────────────────────────────────

    #[test]
    fn test_channel_context_unbound_var_not_cross() {
        let mut ctx = ChannelContext::new();
        ctx.set_current_channel("ch1".to_string());
        assert!(!ctx.is_cross_channel("unbound"));
    }

    #[test]
    fn test_channel_context_no_current_not_cross() {
        let mut ctx = ChannelContext::new();
        ctx.bind("x".to_string(), "ch1".to_string());
        // No current channel set
        assert!(!ctx.is_cross_channel("x"));
    }

    #[test]
    fn test_channel_context_distinct_channels() {
        let mut ctx = ChannelContext::new();
        ctx.bind("x".to_string(), "ch1".to_string());
        ctx.bind("y".to_string(), "ch2".to_string());
        ctx.bind("z".to_string(), "ch1".to_string());
        let channels = ctx.distinct_channels();
        assert_eq!(channels.len(), 2);
        assert!(channels.contains("ch1"));
        assert!(channels.contains("ch2"));
    }

    // ── extract_features: OR/AND propagation and composition ──────────────

    #[test]
    fn test_extract_or_combines_signatures() {
        let expr = PredicateExpr::Or(
            Box::new(PredicateExpr::ForallInfinite {
                var: "x".to_string(),
                body: Box::new(PredicateExpr::True),
            }),
            Box::new(PredicateExpr::Relation {
                name: "eq".to_string(),
                args: vec!["y".to_string()],
            }),
        );
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M2_BUCHI));
        assert!(profile.signature.contains(PredicateSignature::M3_AWA));
        assert!(profile.signature.contains(PredicateSignature::M6_REGISTER));
    }

    #[test]
    fn test_extract_unknown_relation_defaults_to_m6() {
        let expr = PredicateExpr::Relation {
            name: "custom_check".to_string(),
            args: vec!["x".to_string()],
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M6_REGISTER),
            "unknown relation should default to M6 (register)");
    }

    #[test]
    fn test_extract_fresh_relation_triggers_m6() {
        let expr = PredicateExpr::Relation {
            name: "fresh".to_string(),
            args: vec!["x".to_string()],
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M6_REGISTER));
    }

    // ── MSO formula edge cases ────────────────────────────────────────────

    #[test]
    fn test_mso_neg_atomic_letprop() {
        let formula = WeightedMsoFormula::NegAtomicPos {
            label: "letprop".to_string(),
            var: "x".to_string(),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features_mso(&formula, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M4_VPA));
        assert!(profile.signature.contains(PredicateSignature::M5_PARITY_TREE));
    }

    #[test]
    fn test_mso_neg_order_triggers_m6() {
        let formula = WeightedMsoFormula::NegOrder {
            x: "a".to_string(),
            y: "b".to_string(),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features_mso(&formula, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M6_REGISTER));
    }

    #[test]
    fn test_mso_not_in_set() {
        let formula = WeightedMsoFormula::NotInSet {
            var: "x".to_string(),
            set_var: "S".to_string(),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features_mso(&formula, &ctx);
        // Should be base only (set membership is MSO-native)
        assert!(profile.signature.contains(PredicateSignature::M1_SYMBOLIC));
        assert!(profile.signature.contains(PredicateSignature::M10_MSO));
    }

    #[test]
    fn test_mso_deeply_nested_quantifiers() {
        // ∀x. ∃X. ∀²y. c
        let formula = WeightedMsoFormula::ForallFirst {
            var: "x".to_string(),
            body: Box::new(WeightedMsoFormula::ExistsSecond {
                var: "X".to_string(),
                body: Box::new(WeightedMsoFormula::ForallSecond {
                    var: "Y".to_string(),
                    body: Box::new(WeightedMsoFormula::Constant("c".to_string())),
                }),
            }),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features_mso(&formula, &ctx);
        assert_eq!(profile.quantifier_depth, 3);
        assert!(profile.signature.contains(PredicateSignature::M3_AWA)); // ForallFirst + ForallSecond
    }

    #[test]
    fn test_mso_mu_triggers_parity_tree() {
        let formula = WeightedMsoFormula::AtomicPos {
            label: "mu".to_string(),
            var: "x".to_string(),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features_mso(&formula, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M5_PARITY_TREE));
    }

    #[test]
    fn test_mso_nu_triggers_parity_tree() {
        let formula = WeightedMsoFormula::AtomicPos {
            label: "nu".to_string(),
            var: "x".to_string(),
        };
        let ctx = ChannelContext::new();
        let profile = extract_features_mso(&formula, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M5_PARITY_TREE));
    }

    // ── Dispatch SFA additional verification ──────────────────────────────

    #[test]
    fn test_dispatch_sfa_is_not_empty() {
        let sfa = build_dispatch_sfa();
        assert!(!sfa.is_empty(), "dispatch SFA should not be empty");
    }

    #[test]
    fn test_dispatch_algebra_equivalence() {
        let alg = DispatchAlgebra;
        let p = SignaturePred::HasBit(PredicateSignature::M1_SYMBOLIC);
        let q = SignaturePred::HasBit(PredicateSignature::M1_SYMBOLIC);
        assert!(alg.equivalent(&p, &q));
    }

    #[test]
    fn test_dispatch_algebra_implies() {
        let alg = DispatchAlgebra;
        let specific = SignaturePred::And(
            Box::new(SignaturePred::HasBit(PredicateSignature::M1_SYMBOLIC)),
            Box::new(SignaturePred::HasBit(PredicateSignature::M2_BUCHI)),
        );
        let general = SignaturePred::HasBit(PredicateSignature::M1_SYMBOLIC);
        assert!(alg.implies(&specific, &general));
    }

    #[test]
    fn test_dispatch_algebra_or_satisfiability() {
        let alg = DispatchAlgebra;
        let p = SignaturePred::HasBit(PredicateSignature::M2_BUCHI);
        let q = SignaturePred::HasBit(PredicateSignature::M3_AWA);
        let disj = alg.or(&p, &q);
        assert!(alg.is_satisfiable(&disj));
        // Witness should satisfy at least one
        let w = alg.witness(&disj).expect("should have witness");
        assert!(w.contains(PredicateSignature::M2_BUCHI) || w.contains(PredicateSignature::M3_AWA));
    }

    #[test]
    fn test_signature_pred_eval_and() {
        let pred = SignaturePred::And(
            Box::new(SignaturePred::HasBit(PredicateSignature::M1_SYMBOLIC)),
            Box::new(SignaturePred::HasBit(PredicateSignature::M6_REGISTER)),
        );
        let sig_both = PredicateSignature::from_raw(
            PredicateSignature::M1_SYMBOLIC | PredicateSignature::M6_REGISTER,
        );
        let sig_one = PredicateSignature::from_raw(PredicateSignature::M1_SYMBOLIC);
        assert!(pred.eval(sig_both));
        assert!(!pred.eval(sig_one));
    }

    #[test]
    fn test_signature_pred_eval_or() {
        let pred = SignaturePred::Or(
            Box::new(SignaturePred::HasBit(PredicateSignature::M2_BUCHI)),
            Box::new(SignaturePred::HasBit(PredicateSignature::M3_AWA)),
        );
        let sig_m2 = PredicateSignature::from_raw(PredicateSignature::M2_BUCHI);
        let sig_m3 = PredicateSignature::from_raw(PredicateSignature::M3_AWA);
        let sig_neither = PredicateSignature::from_raw(PredicateSignature::M1_SYMBOLIC);
        assert!(pred.eval(sig_m2));
        assert!(pred.eval(sig_m3));
        assert!(!pred.eval(sig_neither));
    }

    #[test]
    fn test_signature_pred_eval_not() {
        let pred = SignaturePred::Not(Box::new(SignaturePred::HasBit(PredicateSignature::M2_BUCHI)));
        let sig_m2 = PredicateSignature::from_raw(PredicateSignature::M2_BUCHI);
        let sig_m1 = PredicateSignature::from_raw(PredicateSignature::M1_SYMBOLIC);
        assert!(!pred.eval(sig_m2));
        assert!(pred.eval(sig_m1));
    }

    // ── Base module invariant (Theorem 3.2) ──────────────────────────────

    #[test]
    fn test_extract_features_always_includes_base() {
        // Various predicate shapes should all include M1 and M10
        let exprs = vec![
            PredicateExpr::True,
            PredicateExpr::False,
            PredicateExpr::Atom("p".to_string()),
            PredicateExpr::Not(Box::new(PredicateExpr::True)),
            PredicateExpr::And(
                Box::new(PredicateExpr::True),
                Box::new(PredicateExpr::False),
            ),
            PredicateExpr::ForallInfinite {
                var: "x".to_string(),
                body: Box::new(PredicateExpr::True),
            },
            PredicateExpr::ExistsInfinite {
                var: "x".to_string(),
                body: Box::new(PredicateExpr::True),
            },
            PredicateExpr::Relation {
                name: "eq".to_string(),
                args: vec!["x".to_string()],
            },
        ];
        let ctx = ChannelContext::new();
        for (i, expr) in exprs.iter().enumerate() {
            let profile = extract_features(expr, &ctx);
            assert!(
                profile.signature.contains(PredicateSignature::M1_SYMBOLIC),
                "expr #{} should contain M1", i
            );
            assert!(
                profile.signature.contains(PredicateSignature::M10_MSO),
                "expr #{} should contain M10", i
            );
        }
    }

    // ── ModuleId coverage ─────────────────────────────────────────────────

    #[test]
    fn test_module_id_feature_gates_are_nonempty() {
        for module in &ModuleId::ALL {
            assert!(!module.feature_gate().is_empty(), "{} has empty feature gate", module);
        }
    }

    #[test]
    fn test_module_id_names_are_nonempty() {
        for module in &ModuleId::ALL {
            assert!(!module.name().is_empty(), "{} has empty name", module);
        }
    }

    #[test]
    fn test_module_id_estimated_costs_are_positive() {
        for module in &ModuleId::ALL {
            assert!(module.estimated_cost() > 0, "{} has zero cost", module);
        }
    }

    // ── Sprint 4a: Grammar-structure heuristic unit tests ───────────────

    #[test]
    fn test_classify_grammar_recursive_activates_buchi() {
        // Category "Expr" has a rule referencing itself → M2
        let syntax = vec![
            ("ExprAdd".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "left".to_string() },
                SyntaxItemSpec::Terminal("+".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "right".to_string() },
            ]),
        ];
        let plan = classify_grammar(&syntax, &[]);
        assert!(plan.requires(ModuleId::Buchi), "recursive category should activate M2 Büchi");
    }

    #[test]
    fn test_classify_grammar_branching_activates_awa() {
        // Rule with ≥3 NonTerminal items → M3
        let syntax = vec![
            ("Ternary".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "cond".to_string() },
                SyntaxItemSpec::Terminal("?".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "then".to_string() },
                SyntaxItemSpec::Terminal(":".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "else_".to_string() },
            ]),
        ];
        let plan = classify_grammar(&syntax, &[]);
        assert!(plan.requires(ModuleId::Awa), "≥3 non-terminals should activate M3 AWA");
    }

    #[test]
    fn test_classify_grammar_brackets_activates_vpa() {
        // Terminals "(" and ")" → M4
        let syntax = vec![
            ("Paren".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Terminal("(".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "inner".to_string() },
                SyntaxItemSpec::Terminal(")".to_string()),
            ]),
        ];
        let plan = classify_grammar(&syntax, &[]);
        assert!(plan.requires(ModuleId::Vpa), "paired brackets should activate M4 VPA");
    }

    #[test]
    fn test_classify_grammar_recursive_branching_activates_parity_tree() {
        // Recursive + ≥3 NTs → M5
        let syntax = vec![
            ("TreeNode".to_string(), "Tree".to_string(), vec![
                SyntaxItemSpec::NonTerminal { category: "Tree".to_string(), param_name: "left".to_string() },
                SyntaxItemSpec::NonTerminal { category: "Tree".to_string(), param_name: "middle".to_string() },
                SyntaxItemSpec::NonTerminal { category: "Tree".to_string(), param_name: "right".to_string() },
            ]),
        ];
        let plan = classify_grammar(&syntax, &[]);
        assert!(plan.requires(ModuleId::ParityTree),
            "recursive + branching should activate M5 Parity Tree");
        // Also check M2 and M3 are set
        assert!(plan.requires(ModuleId::Buchi));
        assert!(plan.requires(ModuleId::Awa));
    }

    #[test]
    fn test_classify_grammar_binders_activates_register() {
        // Binder item → M6
        let syntax = vec![
            ("Lambda".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Terminal("\\".to_string()),
                SyntaxItemSpec::Binder {
                    param_name: "x".to_string(),
                    category: "Expr".to_string(),
                    is_multi: false,
                },
                SyntaxItemSpec::Terminal(".".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "body".to_string() },
            ]),
        ];
        let plan = classify_grammar(&syntax, &[]);
        assert!(plan.requires(ModuleId::Register), "binder items should activate M6 Register");
    }

    #[test]
    fn test_classify_grammar_ambiguous_activates_probabilistic() {
        // ≥3 rules in same category → M7
        let syntax = vec![
            ("Add".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Terminal("+".to_string()),
            ]),
            ("Sub".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Terminal("-".to_string()),
            ]),
            ("Mul".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Terminal("*".to_string()),
            ]),
        ];
        let plan = classify_grammar(&syntax, &[]);
        assert!(plan.requires(ModuleId::Probabilistic),
            "≥3 rules in same category should activate M7 Probabilistic");
    }

    #[test]
    fn test_classify_grammar_base_only() {
        // Single terminal rule → only M1+M10
        let syntax = vec![
            ("Lit".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Terminal("42".to_string()),
            ]),
        ];
        let plan = classify_grammar(&syntax, &[]);
        assert!(plan.requires(ModuleId::Symbolic));
        assert!(plan.requires(ModuleId::Mso));
        assert!(!plan.requires(ModuleId::Buchi), "single terminal should not activate M2");
        assert!(!plan.requires(ModuleId::Awa), "single terminal should not activate M3");
        assert!(!plan.requires(ModuleId::Vpa), "single terminal should not activate M4");
    }

    #[test]
    fn test_classify_grammar_no_brackets_no_vpa() {
        // Has "(" but no ")" → M4 NOT set
        let syntax = vec![
            ("Open".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Terminal("(".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "inner".to_string() },
            ]),
        ];
        let plan = classify_grammar(&syntax, &[]);
        assert!(!plan.requires(ModuleId::Vpa), "unpaired bracket should not activate M4");
    }

    #[test]
    fn test_classify_grammar_non_recursive_no_buchi() {
        // Non-recursive categories → M2 NOT set
        let syntax = vec![
            ("Lit".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::NonTerminal { category: "Num".to_string(), param_name: "val".to_string() },
            ]),
            ("Digit".to_string(), "Num".to_string(), vec![
                SyntaxItemSpec::Terminal("0".to_string()),
            ]),
        ];
        let plan = classify_grammar(&syntax, &[]);
        assert!(!plan.requires(ModuleId::Buchi), "non-recursive categories should not activate M2");
    }

    #[test]
    fn test_classify_grammar_two_rules_no_probabilistic() {
        // Exactly 2 rules in same category → M7 NOT set
        let syntax = vec![
            ("Add".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Terminal("+".to_string()),
            ]),
            ("Sub".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Terminal("-".to_string()),
            ]),
        ];
        let plan = classify_grammar(&syntax, &[]);
        assert!(!plan.requires(ModuleId::Probabilistic),
            "2 rules in same category should not activate M7");
    }

    // ── Sprint 4b: Predicate-level fixpoint detection tests ──────────────

    #[test]
    fn test_extract_features_fixpoint_activates_vpa_parity() {
        let expr = PredicateExpr::Relation {
            name: "fixpoint".to_string(),
            args: vec!["x".to_string()],
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M4_VPA),
            "fixpoint relation → M4");
        assert!(profile.signature.contains(PredicateSignature::M5_PARITY_TREE),
            "fixpoint relation → M5");
        assert!(profile.has_recursive_predicate);
    }

    #[test]
    fn test_extract_features_letrec_activates_vpa_parity() {
        let expr = PredicateExpr::Relation {
            name: "letrec".to_string(),
            args: vec!["x".to_string()],
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M4_VPA));
        assert!(profile.signature.contains(PredicateSignature::M5_PARITY_TREE));
        assert!(profile.has_recursive_predicate);
    }

    #[test]
    fn test_extract_features_mu_activates_vpa_parity() {
        let expr = PredicateExpr::Relation {
            name: "mu".to_string(),
            args: vec!["x".to_string()],
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(profile.signature.contains(PredicateSignature::M4_VPA));
        assert!(profile.signature.contains(PredicateSignature::M5_PARITY_TREE));
    }

    #[test]
    fn test_extract_features_regular_relation_no_vpa() {
        let expr = PredicateExpr::Relation {
            name: "custom".to_string(),
            args: vec!["x".to_string()],
        };
        let ctx = ChannelContext::new();
        let profile = extract_features(&expr, &ctx);
        assert!(!profile.signature.contains(PredicateSignature::M4_VPA),
            "custom relation should not trigger M4");
        assert!(!profile.signature.contains(PredicateSignature::M5_PARITY_TREE),
            "custom relation should not trigger M5");
    }

    // ── Sprint 4c: Dispatch gate consistency tests ───────────────────────

    #[test]
    fn test_dispatch_plan_requires_all_base_modules() {
        let plan = classify_grammar(&[], &[]);
        assert!(plan.requires(ModuleId::Symbolic), "any plan must require M1");
        assert!(plan.requires(ModuleId::Mso), "any plan must require M10");
    }

    #[test]
    fn test_dispatch_plan_skipped_modules_complement() {
        let plan = classify_grammar(&[], &[]);
        let skipped: HashSet<ModuleId> = plan.skipped_modules().into_iter().collect();
        for module in &ModuleId::ALL {
            assert_eq!(
                plan.requires(*module),
                !skipped.contains(module),
                "skipped_modules() and requires() must be complementary for {}",
                module
            );
        }
    }

    #[test]
    fn test_dispatch_plan_empty_grammar_base_only() {
        let plan = classify_grammar(&[], &[]);
        assert!(plan.aggregate_signature.is_base_only(),
            "empty grammar should have only base modules");
    }

    #[test]
    fn test_dispatch_plan_full_grammar_all_modules() {
        // Grammar triggering all heuristics: recursive + branching + brackets +
        // binders + collection + cross-category + ambiguity (≥3 same-cat rules)
        let syntax = vec![
            // Recursive + branching (3 NTs, self-ref) → M2+M3+M5
            ("TreeNode".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "a".to_string() },
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "b".to_string() },
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "c".to_string() },
            ]),
            // Brackets → M4
            ("Paren".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Terminal("(".to_string()),
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "inner".to_string() },
                SyntaxItemSpec::Terminal(")".to_string()),
            ]),
            // Binder → M6
            ("Lambda".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Binder {
                    param_name: "x".to_string(),
                    category: "Expr".to_string(),
                    is_multi: false,
                },
            ]),
            // 3rd rule in "Expr" already exists above, this is the 4th → M7
            ("Lit".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Terminal("42".to_string()),
            ]),
            // Cross-category (≥2 distinct categories in one rule) → M8+M11
            ("Apply".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "fn_".to_string() },
                SyntaxItemSpec::NonTerminal { category: "Type".to_string(), param_name: "ty".to_string() },
            ]),
            // Collection → M9
            ("List".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Collection {
                    param_name: "elems".to_string(),
                    element_category: "Expr".to_string(),
                    separator: ",".to_string(),
                    kind: crate::recursive::CollectionKind::Vec,
                },
            ]),
        ];
        let plan = classify_grammar(&syntax, &[]);
        for module in &ModuleId::ALL {
            assert!(plan.requires(*module),
                "full grammar should activate {}", module);
        }
    }

    // ── Sprint 4d: Combined grammar + predicate interaction tests ────────

    #[test]
    fn test_classify_grammar_collection_and_binder() {
        let syntax = vec![
            ("CollBind".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Collection {
                    param_name: "items".to_string(),
                    element_category: "Expr".to_string(),
                    separator: ",".to_string(),
                    kind: crate::recursive::CollectionKind::Vec,
                },
                SyntaxItemSpec::Binder {
                    param_name: "x".to_string(),
                    category: "Expr".to_string(),
                    is_multi: false,
                },
            ]),
        ];
        let plan = classify_grammar(&syntax, &[]);
        assert!(plan.requires(ModuleId::Register), "binder → M6");
        assert!(plan.requires(ModuleId::Multiset), "collection → M9");
    }

    #[test]
    fn test_classify_grammar_all_heuristics_fire() {
        // Construct a grammar triggering all 6 new heuristics plus existing ones
        let syntax = vec![
            // Self-recursive + branching → M2+M3+M5
            ("Branch".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "a".to_string() },
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "b".to_string() },
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "c".to_string() },
            ]),
            // Brackets → M4
            ("Parens".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Terminal("(".to_string()),
                SyntaxItemSpec::Terminal(")".to_string()),
            ]),
            // Binder → M6
            ("Bind".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Binder {
                    param_name: "v".to_string(),
                    category: "Expr".to_string(),
                    is_multi: false,
                },
            ]),
            // Collection → M9
            ("Coll".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::Collection {
                    param_name: "xs".to_string(),
                    element_category: "Expr".to_string(),
                    separator: ",".to_string(),
                    kind: crate::recursive::CollectionKind::Vec,
                },
            ]),
            // Cross-category → M8+M11
            ("Cross".to_string(), "Expr".to_string(), vec![
                SyntaxItemSpec::NonTerminal { category: "Expr".to_string(), param_name: "e".to_string() },
                SyntaxItemSpec::NonTerminal { category: "Type".to_string(), param_name: "t".to_string() },
            ]),
            // 6th rule: already ≥3 rules in "Expr" → M7 (actually ≥6, threshold is 3)
        ];
        let plan = classify_grammar(&syntax, &[]);
        assert!(plan.requires(ModuleId::Buchi), "M2");
        assert!(plan.requires(ModuleId::Awa), "M3");
        assert!(plan.requires(ModuleId::Vpa), "M4");
        assert!(plan.requires(ModuleId::ParityTree), "M5");
        assert!(plan.requires(ModuleId::Register), "M6");
        assert!(plan.requires(ModuleId::Probabilistic), "M7");
        assert!(plan.requires(ModuleId::MultiTape), "M8");
        assert!(plan.requires(ModuleId::Multiset), "M9");
        assert!(plan.requires(ModuleId::TwoWay), "M11");
    }

    // ── Sprint C4: order_by_specificity tests ────────────────────────────

    #[test]
    fn order_by_specificity_linear_chain() {
        // A ⊂ B ⊂ C — A is most specific
        let labels = vec![
            "Expr::C".to_string(),
            "Expr::B".to_string(),
            "Expr::A".to_string(),
        ];
        let subsumed = vec![
            ("Expr::A".to_string(), "Expr::B".to_string()), // A ⊂ B
            ("Expr::B".to_string(), "Expr::C".to_string()), // B ⊂ C
            ("Expr::A".to_string(), "Expr::C".to_string()), // A ⊂ C (transitive)
        ];

        let ordered = order_by_specificity(&labels, &subsumed);
        assert_eq!(ordered[0], "Expr::A", "most specific should be first");
        assert_eq!(ordered[1], "Expr::B");
        assert_eq!(ordered[2], "Expr::C", "most general should be last");
    }

    #[test]
    fn order_by_specificity_no_subsumption() {
        let labels = vec![
            "Expr::X".to_string(),
            "Expr::Y".to_string(),
            "Expr::Z".to_string(),
        ];
        let subsumed: Vec<(String, String)> = vec![];

        let ordered = order_by_specificity(&labels, &subsumed);
        // Original order preserved
        assert_eq!(ordered[0], "Expr::X");
        assert_eq!(ordered[1], "Expr::Y");
        assert_eq!(ordered[2], "Expr::Z");
    }

    #[test]
    fn order_by_specificity_tiebreak_grammar_order() {
        // A and B are both subsumed by C equally — break tie by grammar order
        let labels = vec![
            "Expr::A".to_string(),
            "Expr::B".to_string(),
            "Expr::C".to_string(),
        ];
        let subsumed = vec![
            ("Expr::A".to_string(), "Expr::C".to_string()),
            ("Expr::B".to_string(), "Expr::C".to_string()),
        ];

        let ordered = order_by_specificity(&labels, &subsumed);
        // A and B have same specificity (1), should be in grammar order
        assert_eq!(ordered[0], "Expr::A");
        assert_eq!(ordered[1], "Expr::B");
        // C has specificity 0 (most general)
        assert_eq!(ordered[2], "Expr::C");
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// §13 Proptest — property-based tests
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod proptest_tests {
    use super::*;
    use proptest::prelude::*;

    // ── Arbitrary PredicateExpr generator ──────────────────────────────────

    fn arb_var() -> impl Strategy<Value = String> {
        prop::sample::select(vec![
            "x".to_string(), "y".to_string(), "z".to_string(),
            "w".to_string(), "v".to_string(),
        ])
    }

    fn arb_channel() -> impl Strategy<Value = String> {
        prop::sample::select(vec![
            "ch1".to_string(), "ch2".to_string(), "ch3".to_string(),
        ])
    }

    fn arb_relation_name() -> impl Strategy<Value = String> {
        prop::sample::select(vec![
            "eq".to_string(), "neq".to_string(), "fresh".to_string(),
            "count".to_string(), "size".to_string(), "custom".to_string(),
            "related".to_string(), ">=".to_string(),
        ])
    }

    fn arb_predicate_expr(depth: u32) -> impl Strategy<Value = PredicateExpr> {
        let leaf = prop_oneof![
            Just(PredicateExpr::True),
            Just(PredicateExpr::False),
            arb_var().prop_map(PredicateExpr::Atom),
            (arb_relation_name(), prop::collection::vec(arb_var(), 1..=3))
                .prop_map(|(name, args)| PredicateExpr::Relation { name, args }),
        ];
        if depth == 0 {
            leaf.boxed()
        } else {
            prop_oneof![
                leaf,
                arb_predicate_expr(depth - 1)
                    .prop_map(|e| PredicateExpr::Not(Box::new(e))),
                (arb_predicate_expr(depth - 1), arb_predicate_expr(depth - 1))
                    .prop_map(|(a, b)| PredicateExpr::And(Box::new(a), Box::new(b))),
                (arb_predicate_expr(depth - 1), arb_predicate_expr(depth - 1))
                    .prop_map(|(a, b)| PredicateExpr::Or(Box::new(a), Box::new(b))),
                (arb_var(), arb_predicate_expr(depth - 1))
                    .prop_map(|(var, body)| PredicateExpr::ForallFinite {
                        var, domain: vec!["a".to_string()], body: Box::new(body),
                    }),
                (arb_var(), arb_predicate_expr(depth - 1))
                    .prop_map(|(var, body)| PredicateExpr::ExistsFinite {
                        var, domain: vec!["a".to_string()], body: Box::new(body),
                    }),
                (arb_var(), arb_predicate_expr(depth - 1))
                    .prop_map(|(var, body)| PredicateExpr::ForallInfinite {
                        var, body: Box::new(body),
                    }),
                (arb_var(), arb_predicate_expr(depth - 1))
                    .prop_map(|(var, body)| PredicateExpr::ExistsInfinite {
                        var, body: Box::new(body),
                    }),
                arb_predicate_expr(depth - 1)
                    .prop_map(|body| PredicateExpr::Bounded {
                        body: Box::new(body), bound: 100,
                    }),
            ]
            .boxed()
        }
    }

    fn arb_channel_context() -> impl Strategy<Value = ChannelContext> {
        prop::collection::vec((arb_var(), arb_channel()), 0..=5)
            .prop_flat_map(|bindings| {
                let ctx_bindings = bindings.clone();
                prop::option::of(arb_channel()).prop_map(move |current| {
                    let mut ctx = ChannelContext::new();
                    for (var, ch) in &ctx_bindings {
                        ctx.bind(var.clone(), ch.clone());
                    }
                    if let Some(ch) = current {
                        ctx.set_current_channel(ch);
                    }
                    ctx
                })
            })
    }

    // ── Arbitrary WeightedMsoFormula generator ────────────────────────────

    fn arb_mso_formula(depth: u32) -> impl Strategy<Value = WeightedMsoFormula> {
        let leaf = prop_oneof![
            arb_var().prop_map(|v| WeightedMsoFormula::Constant(v)),
            (arb_var(), arb_var())
                .prop_map(|(label, var)| WeightedMsoFormula::AtomicPos { label, var }),
            (arb_var(), arb_var())
                .prop_map(|(x, y)| WeightedMsoFormula::Order { x, y }),
            (arb_var(), arb_var())
                .prop_map(|(var, set_var)| WeightedMsoFormula::InSet { var, set_var }),
            (arb_var(), arb_var())
                .prop_map(|(var, set_var)| WeightedMsoFormula::NotInSet { var, set_var }),
        ];
        if depth == 0 {
            leaf.boxed()
        } else {
            prop_oneof![
                leaf,
                (arb_mso_formula(depth - 1), arb_mso_formula(depth - 1))
                    .prop_map(|(a, b)| WeightedMsoFormula::And(Box::new(a), Box::new(b))),
                (arb_mso_formula(depth - 1), arb_mso_formula(depth - 1))
                    .prop_map(|(a, b)| WeightedMsoFormula::Or(Box::new(a), Box::new(b))),
                (arb_var(), arb_mso_formula(depth - 1))
                    .prop_map(|(var, body)| WeightedMsoFormula::ExistsFirst {
                        var, body: Box::new(body),
                    }),
                (arb_var(), arb_mso_formula(depth - 1))
                    .prop_map(|(var, body)| WeightedMsoFormula::ForallFirst {
                        var, body: Box::new(body),
                    }),
                (arb_var(), arb_mso_formula(depth - 1))
                    .prop_map(|(var, body)| WeightedMsoFormula::ExistsSecond {
                        var, body: Box::new(body),
                    }),
                (arb_var(), arb_mso_formula(depth - 1))
                    .prop_map(|(var, body)| WeightedMsoFormula::ForallSecond {
                        var, body: Box::new(body),
                    }),
            ]
            .boxed()
        }
    }

    // ── Arbitrary signature generator ─────────────────────────────────────

    fn arb_signature() -> impl Strategy<Value = PredicateSignature> {
        (0u16..=PredicateSignature::ALL).prop_map(PredicateSignature::from_raw)
    }

    // ── Properties ────────────────────────────────────────────────────────

    proptest! {
        /// P1: extract_features always includes base modules (Theorem 3.2).
        #[test]
        fn prop_extract_always_includes_base(
            expr in arb_predicate_expr(3),
            ctx in arb_channel_context(),
        ) {
            let profile = extract_features(&expr, &ctx);
            prop_assert!(profile.signature.contains(PredicateSignature::M1_SYMBOLIC),
                "M1 (Symbolic) must always be present");
            prop_assert!(profile.signature.contains(PredicateSignature::M10_MSO),
                "M10 (MSO) must always be present");
        }

        /// P2: extract_features_mso always includes base modules.
        #[test]
        fn prop_extract_mso_always_includes_base(
            formula in arb_mso_formula(3),
            ctx in arb_channel_context(),
        ) {
            let profile = extract_features_mso(&formula, &ctx);
            prop_assert!(profile.signature.contains(PredicateSignature::M1_SYMBOLIC));
            prop_assert!(profile.signature.contains(PredicateSignature::M10_MSO));
        }

        /// P3: Signature union is idempotent (a ∪ a = a).
        #[test]
        fn prop_signature_union_idempotent(sig in arb_signature()) {
            prop_assert_eq!(sig.union(sig), sig);
        }

        /// P4: Signature union is commutative (a ∪ b = b ∪ a).
        #[test]
        fn prop_signature_union_commutative(a in arb_signature(), b in arb_signature()) {
            prop_assert_eq!(a.union(b), b.union(a));
        }

        /// P5: Signature union is associative ((a ∪ b) ∪ c = a ∪ (b ∪ c)).
        #[test]
        fn prop_signature_union_associative(
            a in arb_signature(),
            b in arb_signature(),
            c in arb_signature(),
        ) {
            prop_assert_eq!(a.union(b).union(c), a.union(b.union(c)));
        }

        /// P6: count() = popcount of raw bits.
        #[test]
        fn prop_signature_count_is_popcount(sig in arb_signature()) {
            prop_assert_eq!(sig.count(), sig.raw().count_ones());
        }

        /// P7: contains() is consistent with raw bit test.
        #[test]
        fn prop_signature_contains_consistent(
            sig in arb_signature(),
            bit_idx in 0u32..PredicateSignature::NUM_MODULES,
        ) {
            let module_bit = PredicateSignature::module_bit(bit_idx);
            prop_assert_eq!(sig.contains(module_bit), sig.raw() & module_bit != 0);
        }

        /// P8: set() is monotonic — only adds bits, never removes.
        #[test]
        fn prop_signature_set_monotonic(
            initial in arb_signature(),
            bit_idx in 0u32..PredicateSignature::NUM_MODULES,
        ) {
            let mut sig = initial;
            sig.set(PredicateSignature::module_bit(bit_idx));
            // All bits from initial should still be set
            for i in 0..PredicateSignature::NUM_MODULES {
                if initial.contains(PredicateSignature::module_bit(i)) {
                    prop_assert!(sig.contains(PredicateSignature::module_bit(i)),
                        "set() should not clear bit {}", i);
                }
            }
            // The new bit should be set
            prop_assert!(sig.contains(PredicateSignature::module_bit(bit_idx)));
        }

        /// P9: SFA accepts all non-zero signatures (completeness).
        #[test]
        fn prop_sfa_accepts_nonzero(bits in 1u16..=PredicateSignature::ALL) {
            let sfa = build_dispatch_sfa();
            let sig = PredicateSignature::from_raw(bits);
            prop_assert!(sfa.accepts(&[sig]),
                "SFA should accept non-zero signature 0x{:04X}", bits);
        }

        /// P10: SFA rejects zero signature.
        #[test]
        fn prop_sfa_rejects_zero(_dummy in 0u8..1u8) {
            let sfa = build_dispatch_sfa();
            prop_assert!(!sfa.accepts(&[PredicateSignature::from_raw(0)]));
        }

        /// P11: DispatchAlgebra evaluates HasBit correctly.
        #[test]
        fn prop_algebra_has_bit_eval(
            sig in arb_signature(),
            bit_idx in 0u32..PredicateSignature::NUM_MODULES,
        ) {
            let alg = DispatchAlgebra;
            let module_bit = PredicateSignature::module_bit(bit_idx);
            let pred = SignaturePred::HasBit(module_bit);
            prop_assert_eq!(
                alg.evaluate(&pred, &sig),
                sig.contains(module_bit)
            );
        }

        /// P12: DispatchAlgebra witness satisfies its predicate.
        #[test]
        fn prop_algebra_witness_satisfies(bit_idx in 0u32..PredicateSignature::NUM_MODULES) {
            let alg = DispatchAlgebra;
            let pred = SignaturePred::HasBit(PredicateSignature::module_bit(bit_idx));
            if let Some(w) = alg.witness(&pred) {
                prop_assert!(alg.evaluate(&pred, &w),
                    "witness should satisfy the predicate");
            }
        }

        /// P13: GrammarDispatchPlan.requires() is consistent with aggregate signature.
        #[test]
        fn prop_plan_requires_consistent(bits in 0u16..=PredicateSignature::ALL) {
            let plan = GrammarDispatchPlan {
                aggregate_signature: PredicateSignature::from_raw(bits),
                predicate_profiles: Vec::new(),
                module_schedule: Vec::new(),
                modules_skipped: 0,
            };
            for module in &ModuleId::ALL {
                prop_assert_eq!(
                    plan.requires(*module),
                    PredicateSignature::from_raw(bits).contains(module.bit()),
                    "requires() mismatch for {}", module
                );
            }
        }

        /// P14: Feature extraction is monotonic under formula growth.
        /// Adding a sub-formula can only add module bits, never remove them.
        #[test]
        fn prop_extract_monotonic_and(
            a in arb_predicate_expr(2),
            b in arb_predicate_expr(2),
            ctx in arb_channel_context(),
        ) {
            let profile_a = extract_features(&a, &ctx);
            let combined = PredicateExpr::And(Box::new(a), Box::new(b.clone()));
            let profile_combined = extract_features(&combined, &ctx);
            // Combined should have at least all bits of a
            let a_bits = profile_a.signature.raw();
            let combined_bits = profile_combined.signature.raw();
            prop_assert_eq!(
                combined_bits & a_bits, a_bits,
                "And should preserve all bits from left operand"
            );
        }

        /// P15: intersection(a, a) = a (idempotent).
        #[test]
        fn prop_signature_intersection_idempotent(sig in arb_signature()) {
            prop_assert_eq!(sig.intersection(sig), sig);
        }

        /// P16: union with BASE is superset of BASE.
        #[test]
        fn prop_union_with_base_includes_base(sig in arb_signature()) {
            let base = PredicateSignature::new();
            let result = sig.union(base);
            prop_assert!(result.contains(PredicateSignature::M1_SYMBOLIC));
            prop_assert!(result.contains(PredicateSignature::M10_MSO));
        }

        // ── Sprint 4e: Grammar heuristic proptest properties ────────────

        /// P17: Grammar dispatch always includes BASE (M1+M10).
        #[test]
        fn prop_classify_grammar_always_includes_base(
            grammar in arb_grammar(),
        ) {
            let plan = classify_grammar(&grammar, &[]);
            prop_assert!(plan.aggregate_signature.contains(PredicateSignature::M1_SYMBOLIC),
                "grammar dispatch must always include M1");
            prop_assert!(plan.aggregate_signature.contains(PredicateSignature::M10_MSO),
                "grammar dispatch must always include M10");
        }

        /// P18: Grammar dispatch is monotonic under rule addition.
        #[test]
        fn prop_classify_grammar_monotonic(
            base_grammar in arb_grammar(),
            extra_rule in arb_grammar_rule(),
        ) {
            let plan_base = classify_grammar(&base_grammar, &[]);
            let mut extended = base_grammar.clone();
            extended.push(extra_rule);
            let plan_extended = classify_grammar(&extended, &[]);
            let base_bits = plan_base.aggregate_signature.raw();
            let ext_bits = plan_extended.aggregate_signature.raw();
            prop_assert_eq!(ext_bits & base_bits, base_bits,
                "adding a rule must not remove module bits");
        }

        /// P19: Recursive grammar always activates M2 (Büchi).
        #[test]
        fn prop_recursive_implies_buchi(category in arb_category()) {
            let rule = (
                "r".to_string(),
                category.clone(),
                vec![SyntaxItemSpec::NonTerminal {
                    category, param_name: "x".to_string(),
                }],
            );
            let plan = classify_grammar(&[rule], &[]);
            prop_assert!(plan.requires(ModuleId::Buchi),
                "recursive category must activate Büchi");
        }

        /// P20: Paired brackets always activate M4 (VPA).
        #[test]
        fn prop_brackets_implies_vpa(
            open_idx in 0usize..3,
            close_idx in 0usize..3,
        ) {
            let opens = ["(", "{", "["];
            let closes = [")", "}", "]"];
            let grammar = vec![
                ("R".to_string(), "Expr".to_string(), vec![
                    SyntaxItemSpec::Terminal(opens[open_idx].to_string()),
                    SyntaxItemSpec::Terminal(closes[close_idx].to_string()),
                ]),
            ];
            let plan = classify_grammar(&grammar, &[]);
            prop_assert!(plan.requires(ModuleId::Vpa),
                "paired brackets must activate VPA");
        }

        /// P21: Binder items always activate M6 (Register).
        #[test]
        fn prop_binder_implies_register(cat in arb_category()) {
            let grammar = vec![
                ("R".to_string(), cat.clone(), vec![
                    SyntaxItemSpec::Binder {
                        param_name: "x".to_string(),
                        category: cat,
                        is_multi: false,
                    },
                ]),
            ];
            let plan = classify_grammar(&grammar, &[]);
            prop_assert!(plan.requires(ModuleId::Register),
                "binder must activate Register");
        }

        /// P22: ≥3 same-category rules always activate M7 (Probabilistic).
        #[test]
        fn prop_ambiguity_implies_probabilistic(cat in arb_category()) {
            let grammar = vec![
                ("R1".to_string(), cat.clone(), vec![SyntaxItemSpec::Terminal("a".to_string())]),
                ("R2".to_string(), cat.clone(), vec![SyntaxItemSpec::Terminal("b".to_string())]),
                ("R3".to_string(), cat, vec![SyntaxItemSpec::Terminal("c".to_string())]),
            ];
            let plan = classify_grammar(&grammar, &[]);
            prop_assert!(plan.requires(ModuleId::Probabilistic),
                "≥3 same-category rules must activate Probabilistic");
        }

        /// P23: Module schedule is sorted by cost.
        #[test]
        fn prop_schedule_ordered_by_cost(grammar in arb_grammar()) {
            let plan = classify_grammar(&grammar, &[]);
            for window in plan.module_schedule.windows(2) {
                prop_assert!(window[0].estimated_cost() <= window[1].estimated_cost(),
                    "schedule must be sorted: {} vs {}", window[0], window[1]);
            }
        }

        /// P24: classify_grammar is deterministic.
        #[test]
        fn prop_classify_grammar_deterministic(grammar in arb_grammar()) {
            let plan1 = classify_grammar(&grammar, &[]);
            let plan2 = classify_grammar(&grammar, &[]);
            prop_assert_eq!(plan1.aggregate_signature, plan2.aggregate_signature,
                "same grammar must produce same signature");
        }

        /// P25: Conservative approximation — grammar dispatch activates a
        /// superset of predicate-level dispatch for base predicates.
        #[test]
        fn prop_grammar_superset_of_predicate(grammar in arb_grammar()) {
            let plan = classify_grammar(&grammar, &[]);
            let ctx = ChannelContext::new();
            let base_profile = extract_features(&PredicateExpr::True, &ctx);
            let grammar_bits = plan.aggregate_signature.raw();
            let predicate_bits = base_profile.signature.raw();
            prop_assert_eq!(grammar_bits & predicate_bits, predicate_bits,
                "grammar dispatch must be superset of predicate dispatch");
        }

        // ── Sprint 4f: Fixpoint detection proptest properties ───────────

        /// P26: Fixpoint relations always activate M4+M5.
        #[test]
        fn prop_fixpoint_activates_vpa_parity(
            name_idx in 0usize..6,
        ) {
            let names = ["letprop", "fixpoint", "mu", "nu", "letrec", "recursive"];
            let expr = PredicateExpr::Relation {
                name: names[name_idx].to_string(),
                args: vec!["x".to_string()],
            };
            let profile = extract_features(&expr, &ChannelContext::new());
            prop_assert!(profile.signature.contains(PredicateSignature::M4_VPA),
                "{} must activate M4", names[name_idx]);
            prop_assert!(profile.signature.contains(PredicateSignature::M5_PARITY_TREE),
                "{} must activate M5", names[name_idx]);
            prop_assert!(profile.has_recursive_predicate,
                "{} must set has_recursive_predicate", names[name_idx]);
        }

        /// P27: Non-fixpoint relations never activate M4/M5.
        #[test]
        fn prop_non_fixpoint_no_vpa(
            name_idx in 0usize..5,
        ) {
            let names = ["eq", "neq", "count", "size", "custom_check"];
            let expr = PredicateExpr::Relation {
                name: names[name_idx].to_string(),
                args: vec!["x".to_string()],
            };
            let profile = extract_features(&expr, &ChannelContext::new());
            prop_assert!(!profile.signature.contains(PredicateSignature::M4_VPA),
                "{} must not activate M4", names[name_idx]);
            prop_assert!(!profile.signature.contains(PredicateSignature::M5_PARITY_TREE),
                "{} must not activate M5", names[name_idx]);
        }

        // ── order_by_specificity properties ──────────────────────────────

        /// P28: order_by_specificity output is a permutation of the input
        /// (same elements, same count).
        #[test]
        fn prop_specificity_preserves_all_labels(
            n in 2usize..=6,
            pair_indices in prop::collection::vec((0usize..6, 0usize..6), 0..=10),
        ) {
            let labels: Vec<String> = (0..n).map(|i| format!("P{}", i)).collect();
            let subsumed_guards: Vec<(String, String)> = pair_indices
                .into_iter()
                .filter(|(a, b)| *a < n && *b < n && a != b)
                .map(|(a, b)| (format!("P{}", a), format!("P{}", b)))
                .collect();

            let result = order_by_specificity(&labels, &subsumed_guards);

            // Same length
            prop_assert_eq!(result.len(), labels.len(),
                "output length must match input length");

            // Same multiset of elements
            let mut sorted_input = labels.clone();
            sorted_input.sort();
            let mut sorted_output = result.clone();
            sorted_output.sort();
            prop_assert_eq!(sorted_output, sorted_input,
                "output must be a permutation of input");
        }

        /// P29: When subsumed_guards is empty, the output order is identical
        /// to the input order.
        #[test]
        fn prop_no_subsumption_preserves_order(n in 2usize..=6) {
            let labels: Vec<String> = (0..n).map(|i| format!("P{}", i)).collect();
            let result = order_by_specificity(&labels, &[]);
            prop_assert_eq!(result, labels,
                "empty subsumption must preserve original order");
        }

        /// P30: If (a,b) is in subsumed_guards and both a and b are in the
        /// input labels, then a appears before b in the output.
        #[test]
        fn prop_subsumed_before_subsumer(
            n in 2usize..=6,
            a_idx in 0usize..6,
            b_idx in 0usize..6,
        ) {
            prop_assume!(a_idx < n && b_idx < n && a_idx != b_idx);
            let labels: Vec<String> = (0..n).map(|i| format!("P{}", i)).collect();
            let a = format!("P{}", a_idx);
            let b = format!("P{}", b_idx);
            let subsumed_guards = vec![(a.clone(), b.clone())];

            let result = order_by_specificity(&labels, &subsumed_guards);
            let pos_a = result.iter().position(|l| *l == a)
                .expect("a must be in output");
            let pos_b = result.iter().position(|l| *l == b)
                .expect("b must be in output");
            prop_assert!(pos_a < pos_b,
                "subsumed label {} (pos {}) must appear before subsumer {} (pos {})",
                a, pos_a, b, pos_b);
        }

        /// P31: If (a,b), (b,c), and (a,c) are in subsumed_guards, then the
        /// output order is a, b, c (from most to least specific). The extra
        /// pair (a,c) ensures a has score 2 > b's score 1 > c's score 0,
        /// giving a strict specificity chain.
        #[test]
        fn prop_transitivity_ordering(
            n in 3usize..=6,
            a_idx in 0usize..6,
            b_idx in 0usize..6,
            c_idx in 0usize..6,
        ) {
            prop_assume!(a_idx < n && b_idx < n && c_idx < n);
            prop_assume!(a_idx != b_idx && b_idx != c_idx && a_idx != c_idx);
            let labels: Vec<String> = (0..n).map(|i| format!("P{}", i)).collect();
            let a = format!("P{}", a_idx);
            let b = format!("P{}", b_idx);
            let c = format!("P{}", c_idx);
            // (a,b) + (b,c) + (a,c): a has score 2, b has score 1, c has score 0
            let subsumed_guards = vec![
                (a.clone(), b.clone()),
                (b.clone(), c.clone()),
                (a.clone(), c.clone()),
            ];

            let result = order_by_specificity(&labels, &subsumed_guards);
            let pos_a = result.iter().position(|l| *l == a)
                .expect("a must be in output");
            let pos_b = result.iter().position(|l| *l == b)
                .expect("b must be in output");
            let pos_c = result.iter().position(|l| *l == c)
                .expect("c must be in output");
            prop_assert!(pos_a < pos_b,
                "a ({}) at {} must precede b ({}) at {}", a, pos_a, b, pos_b);
            prop_assert!(pos_b < pos_c,
                "b ({}) at {} must precede c ({}) at {}", b, pos_b, c, pos_c);
        }

        /// P32: Labels with higher specificity score (more subsumption pairs
        /// where they are the subsumed element) appear earlier in the output.
        #[test]
        fn prop_specificity_score_monotone(
            n in 2usize..=6,
            pair_indices in prop::collection::vec((0usize..6, 0usize..6), 0..=10),
        ) {
            let labels: Vec<String> = (0..n).map(|i| format!("P{}", i)).collect();
            let subsumed_guards: Vec<(String, String)> = pair_indices
                .into_iter()
                .filter(|(a, b)| *a < n && *b < n && a != b)
                .map(|(a, b)| (format!("P{}", a), format!("P{}", b)))
                .collect();

            // Compute specificity scores (same algorithm as the function)
            let mut scores: HashMap<String, usize> = HashMap::new();
            for label in &labels {
                scores.insert(label.clone(), 0);
            }
            for (subsumed, _) in &subsumed_guards {
                if let Some(count) = scores.get_mut(subsumed) {
                    *count += 1;
                }
            }

            let result = order_by_specificity(&labels, &subsumed_guards);

            // For every pair of labels in the result, if one has a strictly
            // higher specificity score, it must appear earlier.
            for i in 0..result.len() {
                for j in (i + 1)..result.len() {
                    let score_i = scores[&result[i]];
                    let score_j = scores[&result[j]];
                    prop_assert!(score_i >= score_j,
                        "label {} (score {}) at position {} must not follow \
                         label {} (score {}) at position {}",
                        result[i], score_i, i, result[j], score_j, j);
                }
            }
        }
    }

    // ── Grammar generators for proptest ──────────────────────────────────

    fn arb_category() -> impl Strategy<Value = String> {
        prop::sample::select(vec![
            "Expr".to_string(), "Term".to_string(),
            "Stmt".to_string(), "Type".to_string(),
        ])
    }

    fn arb_syntax_item() -> impl Strategy<Value = SyntaxItemSpec> {
        prop_oneof![
            prop::sample::select(vec![
                "(", ")", "{", "}", "[", "]", "+", "-", ";", "let", "in",
            ]).prop_map(|s| SyntaxItemSpec::Terminal(s.to_string())),
            (arb_category(), arb_var())
                .prop_map(|(cat, param)| SyntaxItemSpec::NonTerminal {
                    category: cat, param_name: param,
                }),
            (arb_var(), arb_category())
                .prop_map(|(param, cat)| SyntaxItemSpec::Binder {
                    param_name: param, category: cat, is_multi: false,
                }),
            (arb_var(), arb_category())
                .prop_map(|(param, cat)| SyntaxItemSpec::Collection {
                    param_name: param, element_category: cat,
                    separator: ",".to_string(),
                    kind: crate::recursive::CollectionKind::Vec,
                }),
        ]
    }

    fn arb_grammar_rule() -> impl Strategy<Value = (String, String, Vec<SyntaxItemSpec>)> {
        (arb_var(), arb_category(), prop::collection::vec(arb_syntax_item(), 1..=6))
            .prop_map(|(label, cat, items)| (label, cat, items))
    }

    fn arb_grammar() -> impl Strategy<Value = Vec<(String, String, Vec<SyntaxItemSpec>)>> {
        prop::collection::vec(arb_grammar_rule(), 1..=8)
    }
}
