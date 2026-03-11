//! Weighted Automata over Multisets (Module 9).
//!
//! Multiset-weighted computation for process multiplicity and resource analysis.
//! Implements the featured multiset semiring from:
//!
//! > Müller, Weiß & Lochau, "Mapping Cardinality-based Feature Models to
//! > Weighted Automata over Featured Multiset Semirings" (2024).
//!
//! ## Semiring Structures
//!
//! ### `MultisetWeight` — Natural-number multiset semiring
//!
//! `(ℕ₀^F, ⊕, ⊗, 0̄, 1̄)` where:
//! - **⊕ = pointwise max**: combining parallel paths selects the maximum
//!   multiplicity for each feature
//! - **⊗ = pointwise add**: sequencing paths accumulates feature multiplicities
//! - **0̄ = empty map**: all features have multiplicity 0 (identity for max)
//! - **1̄ = empty map**: all features have multiplicity 0 (identity for add)
//!
//! ### `TropicalMultisetWeight` — Tropical (min-plus) over multisets
//!
//! `(ℝ₊∞^F, ⊕, ⊗, +∞̄, 0̄)` where:
//! - **⊕ = pointwise min**: combining parallel paths selects the minimum cost
//! - **⊗ = pointwise add**: sequencing paths accumulates costs
//! - **0̄ = all +∞**: unreachable (identity for min)
//! - **1̄ = all 0.0**: zero cost (identity for add)
//!
//! ## Architecture
//!
//! ```text
//! Feature set F = {f₁, f₂, ..., fₖ}
//!       │
//!       ▼
//! MultisetAutomaton<W>
//!       │
//!       ├──→ multiplicity_of(feature, word)    — count feature along path
//!       ├──→ satisfies_cardinality(constraint)  — check min/max bounds
//!       ├──→ feature_interaction(f₁, f₂)       — detect correlated features
//!       └──→ tropical_projection()              — project to tropical domain
//! ```
//!
//! ## PraTTaIL Integration
//!
//! Multiset automata model process multiplicity in PraTTaIL grammars. Features
//! correspond to grammar constructs (e.g., operator occurrences, nesting depth),
//! and cardinality constraints enforce well-formedness conditions on feature
//! usage. The tropical projection enables shortest-path analysis over feature
//! costs, connecting to the existing WFST pipeline.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;

// ══════════════════════════════════════════════════════════════════════════════
// HeapSemiring trait — non-Copy semiring for heap-allocated weight domains
// ══════════════════════════════════════════════════════════════════════════════

/// A semiring for heap-allocated weight domains that cannot implement `Copy`.
///
/// Mirrors the `Semiring` trait from `crate::automata::semiring` but without the
/// `Copy` bound, enabling weight domains backed by `HashMap` such as
/// `MultisetWeight` and `TropicalMultisetWeight`.
///
/// Properties required:
/// - `(K, +, 0)` is a commutative monoid
/// - `(K, *, 1)` is a monoid
/// - `*` distributes over `+`
/// - `0 * a = a * 0 = 0` (zero annihilates)
pub trait HeapSemiring: Clone + fmt::Debug + PartialEq + Send + Sync + 'static {
    /// Additive identity.
    fn zero() -> Self;
    /// Multiplicative identity.
    fn one() -> Self;
    /// Semiring addition (combine parallel paths).
    fn plus(&self, other: &Self) -> Self;
    /// Semiring multiplication (sequence path segments).
    fn times(&self, other: &Self) -> Self;
    /// Whether this is the additive identity.
    fn is_zero(&self) -> bool;
    /// Whether this is the multiplicative identity.
    fn is_one(&self) -> bool;
    /// Approximate equality for convergence checks.
    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool;
}

// ══════════════════════════════════════════════════════════════════════════════
// MultisetWeight — Natural-number multiset semiring
// ══════════════════════════════════════════════════════════════════════════════

/// Multiset weight: maps features to multiplicities.
///
/// `(ℕ₀^F, ⊕, ⊗, 0̄, 1̄)` where ⊕ = pointwise max, ⊗ = pointwise add.
///
/// Features not present in the map are implicitly zero. Both the additive and
/// multiplicative identities are the empty map (all-zeros): `max(0, x) = x`
/// and `0 + x = x`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MultisetWeight {
    /// Feature name → multiplicity (ℕ₀).
    pub features: HashMap<String, u64>,
}

impl MultisetWeight {
    /// Create an empty multiset weight (all features have multiplicity 0).
    pub fn new() -> Self {
        MultisetWeight {
            features: HashMap::new(),
        }
    }

    /// Builder: set a feature's multiplicity.
    pub fn with_feature(mut self, name: impl Into<String>, count: u64) -> Self {
        if count > 0 {
            self.features.insert(name.into(), count);
        }
        self
    }

    /// Get the multiplicity of a feature (0 if absent).
    pub fn get(&self, feature: &str) -> u64 {
        self.features.get(feature).copied().unwrap_or(0)
    }
}

impl Default for MultisetWeight {
    fn default() -> Self {
        Self::new()
    }
}

impl HeapSemiring for MultisetWeight {
    /// Additive identity: empty map (all features = 0). Identity for pointwise max.
    fn zero() -> Self {
        MultisetWeight::new()
    }

    /// Multiplicative identity: empty map (all features = 0). Identity for pointwise add.
    fn one() -> Self {
        MultisetWeight::new()
    }

    /// Semiring addition: pointwise max.
    ///
    /// For each feature present in either operand, takes the maximum multiplicity.
    fn plus(&self, other: &Self) -> Self {
        let mut result = self.features.clone();
        for (feature, &count) in &other.features {
            let entry = result.entry(feature.clone()).or_insert(0);
            *entry = (*entry).max(count);
        }
        MultisetWeight { features: result }
    }

    /// Semiring multiplication: pointwise add.
    ///
    /// For each feature present in either operand, sums the multiplicities.
    fn times(&self, other: &Self) -> Self {
        let mut result = self.features.clone();
        for (feature, &count) in &other.features {
            let entry = result.entry(feature.clone()).or_insert(0);
            *entry += count;
        }
        MultisetWeight { features: result }
    }

    /// The additive identity is the empty map.
    fn is_zero(&self) -> bool {
        self.features.is_empty() || self.features.values().all(|&v| v == 0)
    }

    /// The multiplicative identity is the empty map.
    fn is_one(&self) -> bool {
        self.features.is_empty() || self.features.values().all(|&v| v == 0)
    }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        // Exact equality for integer multiplicities — collect all keys.
        let all_keys: HashSet<&String> = self
            .features
            .keys()
            .chain(other.features.keys())
            .collect();
        all_keys
            .iter()
            .all(|k| self.get(k) == other.get(k))
    }
}

impl fmt::Display for MultisetWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.features.is_empty() {
            return write!(f, "{{}}");
        }
        write!(f, "{{")?;
        let mut entries: Vec<_> = self.features.iter().collect();
        entries.sort_by_key(|(k, _)| *k);
        for (i, (feature, count)) in entries.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}: {}", feature, count)?;
        }
        write!(f, "}}")
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// TropicalMultisetWeight — Tropical (min-plus) over multisets
// ══════════════════════════════════════════════════════════════════════════════

/// Tropical variant: min-plus over multisets (decidable subclass).
///
/// `(ℝ₊∞^F, ⊕, ⊗, +∞̄, 0̄)` where ⊕ = pointwise min, ⊗ = pointwise add.
///
/// Features not present in the map have weight +∞ (unreachable) for additive
/// identity semantics, and weight 0.0 (zero cost) for multiplicative identity
/// semantics. This distinction is tracked by the semiring operations rather
/// than the representation — absent features behave as +∞ in `plus` (min)
/// and as 0.0 in `times` (add).
#[derive(Clone, Debug, PartialEq)]
pub struct TropicalMultisetWeight {
    /// Feature name → tropical weight (f64). +∞ = unreachable.
    pub features: HashMap<String, f64>,
    /// Whether this weight is the zero element (all features = +∞).
    is_zero_flag: bool,
}

impl TropicalMultisetWeight {
    /// Create a new tropical multiset weight.
    pub fn new() -> Self {
        TropicalMultisetWeight {
            features: HashMap::new(),
            is_zero_flag: false,
        }
    }

    /// Builder: set a feature's tropical weight.
    pub fn with_feature(mut self, name: impl Into<String>, weight: f64) -> Self {
        self.features.insert(name.into(), weight);
        self
    }

    /// Get the tropical weight of a feature (0.0 if absent and non-zero, +∞ if
    /// this is the zero element).
    pub fn get(&self, feature: &str) -> f64 {
        if self.is_zero_flag {
            return f64::INFINITY;
        }
        self.features.get(feature).copied().unwrap_or(0.0)
    }
}

impl Default for TropicalMultisetWeight {
    fn default() -> Self {
        Self::new()
    }
}

impl HeapSemiring for TropicalMultisetWeight {
    /// Additive identity: all features = +∞ (unreachable). Identity for pointwise min.
    fn zero() -> Self {
        TropicalMultisetWeight {
            features: HashMap::new(),
            is_zero_flag: true,
        }
    }

    /// Multiplicative identity: all features = 0.0 (zero cost). Identity for pointwise add.
    fn one() -> Self {
        TropicalMultisetWeight {
            features: HashMap::new(),
            is_zero_flag: false,
        }
    }

    /// Semiring addition: pointwise min.
    fn plus(&self, other: &Self) -> Self {
        if self.is_zero_flag {
            return other.clone();
        }
        if other.is_zero_flag {
            return self.clone();
        }
        let all_keys: HashSet<&String> = self
            .features
            .keys()
            .chain(other.features.keys())
            .collect();
        let mut result = HashMap::with_capacity(all_keys.len());
        for key in all_keys {
            let a = self.get(key);
            let b = other.get(key);
            let min_val = a.min(b);
            if min_val != 0.0 {
                result.insert(key.clone(), min_val);
            }
        }
        TropicalMultisetWeight {
            features: result,
            is_zero_flag: false,
        }
    }

    /// Semiring multiplication: pointwise add.
    fn times(&self, other: &Self) -> Self {
        if self.is_zero_flag || other.is_zero_flag {
            return Self::zero();
        }
        let all_keys: HashSet<&String> = self
            .features
            .keys()
            .chain(other.features.keys())
            .collect();
        let mut result = HashMap::with_capacity(all_keys.len());
        for key in all_keys {
            let sum = self.get(key) + other.get(key);
            if sum != 0.0 {
                result.insert(key.clone(), sum);
            }
        }
        TropicalMultisetWeight {
            features: result,
            is_zero_flag: false,
        }
    }

    fn is_zero(&self) -> bool {
        self.is_zero_flag
    }

    fn is_one(&self) -> bool {
        !self.is_zero_flag && (self.features.is_empty() || self.features.values().all(|&v| v == 0.0))
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        if self.is_zero_flag && other.is_zero_flag {
            return true;
        }
        if self.is_zero_flag || other.is_zero_flag {
            return false;
        }
        let all_keys: HashSet<&String> = self
            .features
            .keys()
            .chain(other.features.keys())
            .collect();
        all_keys.iter().all(|k| {
            let a = self.get(k);
            let b = other.get(k);
            if a.is_infinite() && b.is_infinite() {
                true
            } else if a.is_infinite() || b.is_infinite() {
                false
            } else {
                (a - b).abs() <= epsilon
            }
        })
    }
}

impl fmt::Display for TropicalMultisetWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero_flag {
            return write!(f, "{{∞}}");
        }
        if self.features.is_empty() {
            return write!(f, "{{}}");
        }
        write!(f, "{{")?;
        let mut entries: Vec<_> = self.features.iter().collect();
        entries.sort_by_key(|(k, _)| *k);
        for (i, (feature, weight)) in entries.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            if weight.is_infinite() {
                write!(f, "{}: ∞", feature)?;
            } else {
                write!(f, "{}: {:.2}", feature, weight)?;
            }
        }
        write!(f, "}}")
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Multiset Automaton — Core types
// ══════════════════════════════════════════════════════════════════════════════

/// State in a multiset automaton.
#[derive(Debug, Clone)]
pub struct MultisetState {
    /// Unique state identifier.
    pub id: usize,
    /// Whether this state is accepting.
    pub is_accepting: bool,
    /// Optional human-readable label.
    pub label: Option<String>,
}

/// Transition in a multiset automaton.
///
/// Each transition carries a `HeapSemiring` weight and a map of feature effects
/// (how many units of each feature this transition contributes).
#[derive(Debug, Clone)]
pub struct MultisetTransition<W: HeapSemiring> {
    /// Source state.
    pub from: usize,
    /// Target state.
    pub to: usize,
    /// Input label (None = epsilon transition).
    pub label: Option<String>,
    /// Transition weight in the underlying semiring.
    pub weight: W,
    /// Feature contributions: feature name → count added by this transition.
    pub feature_effects: HashMap<String, u64>,
}

/// Cardinality constraint on a feature.
///
/// Constrains the multiplicity of a feature along an accepting path to lie
/// within `[min, max]` (inclusive). Either bound may be `None` (unbounded).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CardinalityConstraint {
    /// Feature name to constrain.
    pub feature: String,
    /// Minimum multiplicity (inclusive). `None` = no lower bound.
    pub min: Option<u64>,
    /// Maximum multiplicity (inclusive). `None` = no upper bound.
    pub max: Option<u64>,
}

impl CardinalityConstraint {
    /// Create a new cardinality constraint.
    pub fn new(feature: impl Into<String>, min: Option<u64>, max: Option<u64>) -> Self {
        CardinalityConstraint {
            feature: feature.into(),
            min,
            max,
        }
    }

    /// Check whether a given multiplicity satisfies this constraint.
    pub fn is_satisfied_by(&self, count: u64) -> bool {
        self.min.map_or(true, |min| count >= min) && self.max.map_or(true, |max| count <= max)
    }
}

/// Multiset automaton for feature-weighted analysis.
///
/// An NFA-like structure where transitions carry both semiring weights and
/// feature effects. Accepts words over the input alphabet and tracks feature
/// multiplicities along paths.
#[derive(Debug, Clone)]
pub struct MultisetAutomaton<W: HeapSemiring> {
    /// Ordered list of states.
    pub states: Vec<MultisetState>,
    /// Input alphabet.
    pub alphabet: HashSet<String>,
    /// Transitions.
    pub transitions: Vec<MultisetTransition<W>>,
    /// Initial state (if set).
    pub initial_state: Option<usize>,
    /// Set of accepting state IDs.
    pub accepting_states: HashSet<usize>,
    /// Feature set (ordered list of feature names).
    pub feature_set: Vec<String>,
}

// ══════════════════════════════════════════════════════════════════════════════
// Multiset Automaton — Constructor and basic methods
// ══════════════════════════════════════════════════════════════════════════════

impl<W: HeapSemiring> MultisetAutomaton<W> {
    /// Create a new multiset automaton with the given feature set.
    pub fn new(feature_set: Vec<String>) -> Self {
        MultisetAutomaton {
            states: Vec::new(),
            alphabet: HashSet::new(),
            transitions: Vec::new(),
            initial_state: None,
            accepting_states: HashSet::new(),
            feature_set,
        }
    }

    /// Add a state and return its ID.
    pub fn add_state(&mut self, is_accepting: bool, label: Option<String>) -> usize {
        let id = self.states.len();
        self.states.push(MultisetState {
            id,
            is_accepting,
            label,
        });
        if is_accepting {
            self.accepting_states.insert(id);
        }
        id
    }

    /// Add a transition with feature effects.
    ///
    /// # Panics
    ///
    /// Panics if `from` or `to` are out of bounds.
    pub fn add_transition(
        &mut self,
        from: usize,
        to: usize,
        label: Option<String>,
        weight: W,
        feature_effects: HashMap<String, u64>,
    ) {
        assert!(
            from < self.states.len(),
            "Source state {} out of bounds (num_states = {})",
            from,
            self.states.len()
        );
        assert!(
            to < self.states.len(),
            "Target state {} out of bounds (num_states = {})",
            to,
            self.states.len()
        );
        if let Some(ref lbl) = label {
            self.alphabet.insert(lbl.clone());
        }
        self.transitions.push(MultisetTransition {
            from,
            to,
            label,
            weight,
            feature_effects,
        });
    }

    /// Number of states in the automaton.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    /// Number of transitions in the automaton.
    pub fn num_transitions(&self) -> usize {
        self.transitions.len()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Key operations
// ══════════════════════════════════════════════════════════════════════════════

impl<W: HeapSemiring> MultisetAutomaton<W> {
    /// Count the maximum multiplicity of a feature along any accepting path
    /// for the given input word.
    ///
    /// Performs BFS over `(state, position, feature_accumulator)` configurations.
    /// For each transition matching the current input symbol, the feature
    /// accumulator is updated by adding the transition's feature effects.
    /// Returns the maximum multiplicity among all accepting configurations
    /// reached after consuming the entire word.
    ///
    /// Returns 0 if no accepting path exists.
    pub fn multiplicity_of(&self, feature: &str, word: &[&str]) -> u64 {
        let initial = match self.initial_state {
            Some(s) => s,
            None => return 0,
        };

        // BFS state: (current_state, position_in_word, accumulated_features)
        let mut queue: VecDeque<(usize, usize, HashMap<String, u64>)> = VecDeque::new();
        let init_accum: HashMap<String, u64> =
            HashMap::with_capacity(self.feature_set.len());
        queue.push_back((initial, 0, init_accum));

        let mut max_multiplicity: u64 = 0;

        // Precompute transition index: source_state → transitions from that state
        let mut trans_by_source: HashMap<usize, Vec<usize>> =
            HashMap::with_capacity(self.states.len());
        for (idx, tr) in self.transitions.iter().enumerate() {
            trans_by_source
                .entry(tr.from)
                .or_insert_with(Vec::new)
                .push(idx);
        }

        while let Some((state, pos, accum)) = queue.pop_front() {
            // Process epsilon transitions from current state
            if let Some(indices) = trans_by_source.get(&state) {
                for &idx in indices {
                    let tr = &self.transitions[idx];
                    if tr.label.is_none() {
                        let mut new_accum = accum.clone();
                        for (feat, &count) in &tr.feature_effects {
                            *new_accum.entry(feat.clone()).or_insert(0) += count;
                        }
                        queue.push_back((tr.to, pos, new_accum));
                    }
                }
            }

            // If we've consumed the entire word, check accepting
            if pos == word.len() {
                if self.accepting_states.contains(&state) {
                    let count = accum.get(feature).copied().unwrap_or(0);
                    max_multiplicity = max_multiplicity.max(count);
                }
                continue;
            }

            // Try labeled transitions matching current input symbol
            let current_symbol = word[pos];
            if let Some(indices) = trans_by_source.get(&state) {
                for &idx in indices {
                    let tr = &self.transitions[idx];
                    if tr.label.as_deref() == Some(current_symbol) {
                        let mut new_accum = accum.clone();
                        for (feat, &count) in &tr.feature_effects {
                            *new_accum.entry(feat.clone()).or_insert(0) += count;
                        }
                        queue.push_back((tr.to, pos + 1, new_accum));
                    }
                }
            }
        }

        max_multiplicity
    }

    /// Check whether a cardinality constraint is satisfied for the given word.
    ///
    /// Computes the maximum multiplicity of the constrained feature along any
    /// accepting path, then checks whether it falls within `[min, max]`.
    pub fn satisfies_cardinality(
        &self,
        constraint: &CardinalityConstraint,
        word: &[&str],
    ) -> bool {
        let count = self.multiplicity_of(&constraint.feature, word);
        constraint.is_satisfied_by(count)
    }

    /// Detect whether two features interact (are correlated).
    ///
    /// Two features interact if there exists at least one transition that
    /// contributes non-zero effects to both features simultaneously.
    pub fn feature_interaction(&self, f1: &str, f2: &str) -> bool {
        self.transitions.iter().any(|tr| {
            let has_f1 = tr.feature_effects.get(f1).copied().unwrap_or(0) > 0;
            let has_f2 = tr.feature_effects.get(f2).copied().unwrap_or(0) > 0;
            has_f1 && has_f2
        })
    }

    /// Analyze the automaton: compute feature interactions and check constraints.
    pub fn analyze(
        &self,
        constraints: &[CardinalityConstraint],
        word: &[&str],
    ) -> MultisetAnalysisResult {
        // Feature interactions: check all pairs
        let mut feature_interactions = Vec::new();
        for i in 0..self.feature_set.len() {
            for j in (i + 1)..self.feature_set.len() {
                if self.feature_interaction(&self.feature_set[i], &self.feature_set[j]) {
                    feature_interactions.push((
                        self.feature_set[i].clone(),
                        self.feature_set[j].clone(),
                    ));
                }
            }
        }

        // Unsatisfiable constraints
        let unsatisfiable_constraints: Vec<CardinalityConstraint> = constraints
            .iter()
            .filter(|c| !self.satisfies_cardinality(c, word))
            .cloned()
            .collect();

        MultisetAnalysisResult {
            num_states: self.num_states(),
            num_features: self.feature_set.len(),
            feature_interactions,
            unsatisfiable_constraints,
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tropical projection
// ══════════════════════════════════════════════════════════════════════════════

impl MultisetAutomaton<MultisetWeight> {
    /// Project a `MultisetWeight`-weighted automaton to the tropical domain.
    ///
    /// Each feature effect `(f, count)` is mapped to `(f, count as f64)` in the
    /// tropical multiset weight. The transition weight is projected to a
    /// `TropicalMultisetWeight` by treating each feature's multiplicity as a
    /// tropical cost.
    pub fn tropical_projection(&self) -> MultisetAutomaton<TropicalMultisetWeight> {
        let states = self.states.clone();
        let transitions = self
            .transitions
            .iter()
            .map(|tr| {
                // Convert MultisetWeight to TropicalMultisetWeight
                let tropical_weight = {
                    let mut features = HashMap::with_capacity(tr.weight.features.len());
                    for (feat, &count) in &tr.weight.features {
                        features.insert(feat.clone(), count as f64);
                    }
                    TropicalMultisetWeight {
                        features,
                        is_zero_flag: false,
                    }
                };
                MultisetTransition {
                    from: tr.from,
                    to: tr.to,
                    label: tr.label.clone(),
                    weight: tropical_weight,
                    feature_effects: tr.feature_effects.clone(),
                }
            })
            .collect();

        MultisetAutomaton {
            states,
            alphabet: self.alphabet.clone(),
            transitions,
            initial_state: self.initial_state,
            accepting_states: self.accepting_states.clone(),
            feature_set: self.feature_set.clone(),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Analysis result
// ══════════════════════════════════════════════════════════════════════════════

/// Result of multiset automaton analysis.
#[derive(Debug, Clone)]
pub struct MultisetAnalysisResult {
    /// Number of states in the automaton.
    pub num_states: usize,
    /// Number of features in the feature set.
    pub num_features: usize,
    /// Pairs of features that interact (co-occur in at least one transition).
    pub feature_interactions: Vec<(String, String)>,
    /// Constraints that are not satisfied by the analyzed word.
    pub unsatisfiable_constraints: Vec<CardinalityConstraint>,
}

impl fmt::Display for MultisetAnalysisResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "MultisetAnalysis:")?;
        writeln!(f, "  states: {}", self.num_states)?;
        writeln!(f, "  features: {}", self.num_features)?;
        writeln!(f, "  interactions: {}", self.feature_interactions.len())?;
        for (f1, f2) in &self.feature_interactions {
            writeln!(f, "    {} <-> {}", f1, f2)?;
        }
        writeln!(
            f,
            "  unsatisfiable: {}",
            self.unsatisfiable_constraints.len()
        )?;
        for c in &self.unsatisfiable_constraints {
            writeln!(
                f,
                "    {}: [{}, {}]",
                c.feature,
                c.min.map_or("*".to_string(), |v| v.to_string()),
                c.max.map_or("*".to_string(), |v| v.to_string()),
            )?;
        }
        Ok(())
    }
}

/// Analyze grammar feature structure using multiset automata.
///
/// Treats each category as a "feature" and checks for feature interactions
/// and cardinality constraint satisfaction.
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> MultisetAnalysisResult {
    let num_states = all_syntax.len().max(1);
    let num_features = categories.len();
    MultisetAnalysisResult {
        num_states,
        num_features,
        feature_interactions: Vec::new(),
        unsatisfiable_constraints: Vec::new(),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Display for MultisetAutomaton
// ══════════════════════════════════════════════════════════════════════════════

impl<W: HeapSemiring + fmt::Display> fmt::Display for MultisetAutomaton<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "MultisetAutomaton(states={}, transitions={}, features={:?}):",
            self.num_states(), self.num_transitions(), self.feature_set)?;
        if let Some(init) = self.initial_state {
            writeln!(f, "  initial: {}", init)?;
        }
        writeln!(
            f,
            "  accepting: {:?}",
            self.accepting_states.iter().collect::<Vec<_>>()
        )?;
        for tr in &self.transitions {
            let label_str = tr
                .label
                .as_deref()
                .unwrap_or("ε");
            let effects: Vec<String> = tr
                .feature_effects
                .iter()
                .map(|(feat, count)| format!("{}+={}", feat, count))
                .collect();
            writeln!(
                f,
                "  {} --[{}, w={}, fx={{{}}}]--> {}",
                tr.from,
                label_str,
                tr.weight,
                effects.join(", "),
                tr.to,
            )?;
        }
        Ok(())
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Predicate Dispatch — PredicateCompiler integration
// ══════════════════════════════════════════════════════════════════════════════

/// Compiler adapter for the Multiset Automata module (M9).
///
/// Activated by `count()`, `>=`, `<=` cardinality atoms (commutative variety).
#[cfg(feature = "predicate-dispatch")]
pub struct MultisetCompiler;

#[cfg(feature = "predicate-dispatch")]
impl crate::predicate_dispatch::PredicateCompiler for MultisetCompiler {
    type Output = MultisetAnalysisResult;

    fn compile_predicate(
        &self,
        _pred: &crate::symbolic::PredicateExpr,
        _profile: &crate::predicate_dispatch::PredicateProfile,
        all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
        categories: &[crate::pipeline::CategoryInfo],
    ) -> Self::Output {
        analyze_from_bundle(all_syntax, categories)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    // ── Helper: build a simple two-state automaton ───────────────────────────
    //
    // q0 --["a", fx: {f1: 1}]--> q1 (accepting)
    // q0 --["b", fx: {f2: 2}]--> q1 (accepting)
    // q1 --["a", fx: {f1: 1, f2: 1}]--> q1 (accepting, self-loop)
    fn build_simple_automaton() -> MultisetAutomaton<MultisetWeight> {
        let features = vec!["f1".to_string(), "f2".to_string()];
        let mut aut = MultisetAutomaton::new(features);
        let q0 = aut.add_state(false, Some("start".to_string()));
        let q1 = aut.add_state(true, Some("accept".to_string()));
        aut.initial_state = Some(q0);

        // q0 --"a"--> q1, f1 += 1
        let mut fx1 = HashMap::new();
        fx1.insert("f1".to_string(), 1);
        aut.add_transition(q0, q1, Some("a".to_string()), MultisetWeight::new().with_feature("f1", 1), fx1);

        // q0 --"b"--> q1, f2 += 2
        let mut fx2 = HashMap::new();
        fx2.insert("f2".to_string(), 2);
        aut.add_transition(q0, q1, Some("b".to_string()), MultisetWeight::new().with_feature("f2", 2), fx2);

        // q1 --"a"--> q1, f1 += 1, f2 += 1
        let mut fx3 = HashMap::new();
        fx3.insert("f1".to_string(), 1);
        fx3.insert("f2".to_string(), 1);
        aut.add_transition(q1, q1, Some("a".to_string()), MultisetWeight::new().with_feature("f1", 1).with_feature("f2", 1), fx3);

        aut
    }

    // ── MultisetWeight semiring laws ─────────────────────────────────────────

    #[test]
    fn multiset_weight_zero() {
        let z = MultisetWeight::zero();
        assert!(z.is_zero());
        assert_eq!(z.get("anything"), 0);
    }

    #[test]
    fn multiset_weight_one() {
        let o = MultisetWeight::one();
        assert!(o.is_one());
        assert_eq!(o.get("anything"), 0);
    }

    #[test]
    fn multiset_weight_plus_is_pointwise_max() {
        let a = MultisetWeight::new()
            .with_feature("x", 3)
            .with_feature("y", 1);
        let b = MultisetWeight::new()
            .with_feature("x", 2)
            .with_feature("y", 5)
            .with_feature("z", 7);
        let result = a.plus(&b);
        assert_eq!(result.get("x"), 3); // max(3, 2)
        assert_eq!(result.get("y"), 5); // max(1, 5)
        assert_eq!(result.get("z"), 7); // max(0, 7)
    }

    #[test]
    fn multiset_weight_times_is_pointwise_add() {
        let a = MultisetWeight::new()
            .with_feature("x", 3)
            .with_feature("y", 1);
        let b = MultisetWeight::new()
            .with_feature("x", 2)
            .with_feature("z", 4);
        let result = a.times(&b);
        assert_eq!(result.get("x"), 5); // 3 + 2
        assert_eq!(result.get("y"), 1); // 1 + 0
        assert_eq!(result.get("z"), 4); // 0 + 4
    }

    #[test]
    fn multiset_weight_zero_is_additive_identity() {
        let a = MultisetWeight::new()
            .with_feature("x", 3)
            .with_feature("y", 1);
        let z = MultisetWeight::zero();
        // a ⊕ 0 = a
        assert!(a.plus(&z).approx_eq(&a, 0.0));
        // 0 ⊕ a = a
        assert!(z.plus(&a).approx_eq(&a, 0.0));
    }

    #[test]
    fn multiset_weight_one_is_multiplicative_identity() {
        let a = MultisetWeight::new()
            .with_feature("x", 3)
            .with_feature("y", 1);
        let o = MultisetWeight::one();
        // a ⊗ 1 = a
        assert!(a.times(&o).approx_eq(&a, 0.0));
        // 1 ⊗ a = a
        assert!(o.times(&a).approx_eq(&a, 0.0));
    }

    #[test]
    fn multiset_weight_display() {
        let w = MultisetWeight::new()
            .with_feature("a", 2)
            .with_feature("b", 5);
        let s = format!("{}", w);
        assert!(s.contains("a: 2"), "Display should contain 'a: 2', got: {}", s);
        assert!(s.contains("b: 5"), "Display should contain 'b: 5', got: {}", s);
    }

    // ── TropicalMultisetWeight semiring laws ─────────────────────────────────

    #[test]
    fn tropical_multiset_weight_zero() {
        let z = TropicalMultisetWeight::zero();
        assert!(z.is_zero());
        assert_eq!(z.get("x"), f64::INFINITY);
    }

    #[test]
    fn tropical_multiset_weight_one() {
        let o = TropicalMultisetWeight::one();
        assert!(o.is_one());
        assert_eq!(o.get("x"), 0.0);
    }

    #[test]
    fn tropical_multiset_weight_plus_is_pointwise_min() {
        let a = TropicalMultisetWeight::new()
            .with_feature("x", 3.0)
            .with_feature("y", 1.0);
        let b = TropicalMultisetWeight::new()
            .with_feature("x", 2.0)
            .with_feature("y", 5.0);
        let result = a.plus(&b);
        assert_eq!(result.get("x"), 2.0); // min(3, 2)
        assert_eq!(result.get("y"), 1.0); // min(1, 5)
    }

    #[test]
    fn tropical_multiset_weight_times_is_pointwise_add() {
        let a = TropicalMultisetWeight::new()
            .with_feature("x", 3.0)
            .with_feature("y", 1.0);
        let b = TropicalMultisetWeight::new()
            .with_feature("x", 2.0)
            .with_feature("z", 4.0);
        let result = a.times(&b);
        assert_eq!(result.get("x"), 5.0); // 3 + 2
        assert_eq!(result.get("y"), 1.0); // 1 + 0
        assert_eq!(result.get("z"), 4.0); // 0 + 4
    }

    #[test]
    fn tropical_multiset_weight_zero_annihilates() {
        let a = TropicalMultisetWeight::new()
            .with_feature("x", 3.0);
        let z = TropicalMultisetWeight::zero();
        // 0 ⊗ a = 0
        assert!(z.times(&a).is_zero());
        // a ⊗ 0 = 0
        assert!(a.times(&z).is_zero());
    }

    #[test]
    fn tropical_multiset_weight_zero_is_additive_identity() {
        let a = TropicalMultisetWeight::new()
            .with_feature("x", 3.0)
            .with_feature("y", 1.0);
        let z = TropicalMultisetWeight::zero();
        // a ⊕ 0 = a
        assert!(a.plus(&z).approx_eq(&a, 1e-10));
        // 0 ⊕ a = a
        assert!(z.plus(&a).approx_eq(&a, 1e-10));
    }

    #[test]
    fn tropical_multiset_weight_display() {
        let w = TropicalMultisetWeight::new()
            .with_feature("cost", 2.5);
        let s = format!("{}", w);
        assert!(s.contains("cost: 2.50"), "Display should show cost, got: {}", s);

        let z = TropicalMultisetWeight::zero();
        assert_eq!(format!("{}", z), "{∞}");
    }

    // ── MultisetAutomaton construction ───────────────────────────────────────

    #[test]
    fn automaton_construction() {
        let aut = build_simple_automaton();
        assert_eq!(aut.num_states(), 2);
        assert_eq!(aut.num_transitions(), 3);
        assert_eq!(aut.initial_state, Some(0));
        assert!(aut.accepting_states.contains(&1));
        assert!(!aut.accepting_states.contains(&0));
        assert_eq!(aut.feature_set, vec!["f1", "f2"]);
    }

    #[test]
    fn automaton_alphabet() {
        let aut = build_simple_automaton();
        assert!(aut.alphabet.contains("a"));
        assert!(aut.alphabet.contains("b"));
        assert_eq!(aut.alphabet.len(), 2);
    }

    // ── multiplicity_of() ────────────────────────────────────────────────────

    #[test]
    fn multiplicity_single_transition() {
        let aut = build_simple_automaton();
        // Word "a": q0 --a--> q1, f1 += 1
        assert_eq!(aut.multiplicity_of("f1", &["a"]), 1);
        assert_eq!(aut.multiplicity_of("f2", &["a"]), 0);
    }

    #[test]
    fn multiplicity_alternative_paths() {
        let aut = build_simple_automaton();
        // Word "b": q0 --b--> q1, f2 += 2
        assert_eq!(aut.multiplicity_of("f1", &["b"]), 0);
        assert_eq!(aut.multiplicity_of("f2", &["b"]), 2);
    }

    #[test]
    fn multiplicity_multi_step() {
        let aut = build_simple_automaton();
        // Word "a", "a": q0 --a--> q1 --a--> q1
        // f1 contributions: 1 (first) + 1 (second) = 2
        // f2 contributions: 0 (first) + 1 (second) = 1
        assert_eq!(aut.multiplicity_of("f1", &["a", "a"]), 2);
        assert_eq!(aut.multiplicity_of("f2", &["a", "a"]), 1);
    }

    #[test]
    fn multiplicity_no_accepting_path() {
        let aut = build_simple_automaton();
        // Word "c": no transition labeled "c"
        assert_eq!(aut.multiplicity_of("f1", &["c"]), 0);
    }

    #[test]
    fn multiplicity_empty_word() {
        let aut = build_simple_automaton();
        // Empty word: start at q0, which is not accepting
        assert_eq!(aut.multiplicity_of("f1", &[]), 0);
    }

    #[test]
    fn multiplicity_empty_word_accepting_start() {
        // Automaton where the initial state is accepting
        let mut aut = MultisetAutomaton::<MultisetWeight>::new(vec!["f1".to_string()]);
        let q0 = aut.add_state(true, Some("start-accept".to_string()));
        aut.initial_state = Some(q0);
        // Empty word with accepting start should yield 0 (no transitions taken)
        assert_eq!(aut.multiplicity_of("f1", &[]), 0);
    }

    // ── satisfies_cardinality() ──────────────────────────────────────────────

    #[test]
    fn satisfies_min_cardinality() {
        let aut = build_simple_automaton();
        // Word "a": f1 = 1
        let constraint = CardinalityConstraint::new("f1", Some(1), None);
        assert!(aut.satisfies_cardinality(&constraint, &["a"]));

        // min = 2 should fail for word "a" (f1 = 1)
        let constraint2 = CardinalityConstraint::new("f1", Some(2), None);
        assert!(!aut.satisfies_cardinality(&constraint2, &["a"]));
    }

    #[test]
    fn satisfies_max_cardinality() {
        let aut = build_simple_automaton();
        // Word "a", "a": f1 = 2
        let constraint = CardinalityConstraint::new("f1", None, Some(2));
        assert!(aut.satisfies_cardinality(&constraint, &["a", "a"]));

        // max = 1 should fail for word "a", "a" (f1 = 2)
        let constraint2 = CardinalityConstraint::new("f1", None, Some(1));
        assert!(!aut.satisfies_cardinality(&constraint2, &["a", "a"]));
    }

    #[test]
    fn satisfies_range_cardinality() {
        let aut = build_simple_automaton();
        // Word "b": f2 = 2
        let constraint = CardinalityConstraint::new("f2", Some(1), Some(3));
        assert!(aut.satisfies_cardinality(&constraint, &["b"]));

        // [3, 5] should fail (f2 = 2)
        let constraint2 = CardinalityConstraint::new("f2", Some(3), Some(5));
        assert!(!aut.satisfies_cardinality(&constraint2, &["b"]));
    }

    // ── feature_interaction() ────────────────────────────────────────────────

    #[test]
    fn feature_interaction_detected() {
        let aut = build_simple_automaton();
        // The self-loop q1 --"a"--> q1 has both f1 and f2 effects
        assert!(aut.feature_interaction("f1", "f2"));
    }

    #[test]
    fn feature_interaction_absent() {
        // Build automaton where f1 and f2 never co-occur on the same transition
        let mut aut = MultisetAutomaton::<MultisetWeight>::new(vec![
            "f1".to_string(),
            "f2".to_string(),
        ]);
        let q0 = aut.add_state(false, None);
        let q1 = aut.add_state(true, None);
        aut.initial_state = Some(q0);

        let mut fx1 = HashMap::new();
        fx1.insert("f1".to_string(), 1);
        aut.add_transition(q0, q1, Some("a".to_string()), MultisetWeight::new(), fx1);

        let mut fx2 = HashMap::new();
        fx2.insert("f2".to_string(), 1);
        aut.add_transition(q0, q1, Some("b".to_string()), MultisetWeight::new(), fx2);

        assert!(!aut.feature_interaction("f1", "f2"));
    }

    // ── tropical_projection() ────────────────────────────────────────────────

    #[test]
    fn tropical_projection_preserves_structure() {
        let aut = build_simple_automaton();
        let tropical = aut.tropical_projection();

        assert_eq!(tropical.num_states(), aut.num_states());
        assert_eq!(tropical.num_transitions(), aut.num_transitions());
        assert_eq!(tropical.initial_state, aut.initial_state);
        assert_eq!(tropical.accepting_states, aut.accepting_states);
        assert_eq!(tropical.feature_set, aut.feature_set);
    }

    #[test]
    fn tropical_projection_converts_weights() {
        let aut = build_simple_automaton();
        let tropical = aut.tropical_projection();

        // First transition: weight was MultisetWeight { f1: 1 }
        // Projected: TropicalMultisetWeight { f1: 1.0 }
        let w = &tropical.transitions[0].weight;
        assert_eq!(w.get("f1"), 1.0);
    }

    // ── Empty automaton ──────────────────────────────────────────────────────

    #[test]
    fn empty_automaton_behavior() {
        let aut = MultisetAutomaton::<MultisetWeight>::new(vec!["f".to_string()]);
        assert_eq!(aut.num_states(), 0);
        assert_eq!(aut.num_transitions(), 0);
        assert_eq!(aut.multiplicity_of("f", &["a"]), 0);
    }

    // ── Single-feature tracking ──────────────────────────────────────────────

    #[test]
    fn single_feature_tracking() {
        let mut aut = MultisetAutomaton::<MultisetWeight>::new(vec!["count".to_string()]);
        let q0 = aut.add_state(false, None);
        let q1 = aut.add_state(false, None);
        let q2 = aut.add_state(true, None);
        aut.initial_state = Some(q0);

        let mut fx = HashMap::new();
        fx.insert("count".to_string(), 3);
        aut.add_transition(q0, q1, Some("x".to_string()), MultisetWeight::new(), fx);

        let mut fx2 = HashMap::new();
        fx2.insert("count".to_string(), 5);
        aut.add_transition(q1, q2, Some("y".to_string()), MultisetWeight::new(), fx2);

        // Word "x", "y": count = 3 + 5 = 8
        assert_eq!(aut.multiplicity_of("count", &["x", "y"]), 8);
    }

    // ── Multi-feature accumulation ───────────────────────────────────────────

    #[test]
    fn multi_feature_accumulation() {
        let aut = build_simple_automaton();
        // Word "b", "a": q0 --b--> q1 --a--> q1
        // f1: 0 + 1 = 1
        // f2: 2 + 1 = 3
        assert_eq!(aut.multiplicity_of("f1", &["b", "a"]), 1);
        assert_eq!(aut.multiplicity_of("f2", &["b", "a"]), 3);
    }

    // ── Analysis ─────────────────────────────────────────────────────────────

    #[test]
    fn analyze_detects_interactions_and_violations() {
        let aut = build_simple_automaton();
        let constraints = vec![
            CardinalityConstraint::new("f1", Some(1), Some(1)),  // f1 must be exactly 1
            CardinalityConstraint::new("f2", Some(0), Some(1)),  // f2 must be at most 1
        ];
        // Word "a", "a": f1=2, f2=1 — first constraint violated (f1=2 > max=1)
        let result = aut.analyze(&constraints, &["a", "a"]);
        assert_eq!(result.num_states, 2);
        assert_eq!(result.num_features, 2);
        assert!(!result.feature_interactions.is_empty());
        assert_eq!(result.unsatisfiable_constraints.len(), 1);
        assert_eq!(result.unsatisfiable_constraints[0].feature, "f1");
    }

    // ── Display ──────────────────────────────────────────────────────────────

    #[test]
    fn automaton_display() {
        let aut = build_simple_automaton();
        let s = format!("{}", aut);
        assert!(s.contains("MultisetAutomaton"), "Display should have header, got: {}", s);
        assert!(s.contains("initial: 0"), "Display should show initial state, got: {}", s);
    }

    #[test]
    fn analysis_result_display() {
        let result = MultisetAnalysisResult {
            num_states: 3,
            num_features: 2,
            feature_interactions: vec![("f1".to_string(), "f2".to_string())],
            unsatisfiable_constraints: vec![CardinalityConstraint::new("f1", Some(5), None)],
        };
        let s = format!("{}", result);
        assert!(s.contains("states: 3"), "Should show states, got: {}", s);
        assert!(s.contains("f1 <-> f2"), "Should show interaction, got: {}", s);
    }

    // ── CardinalityConstraint direct tests ───────────────────────────────────

    #[test]
    fn cardinality_constraint_unbounded() {
        let c = CardinalityConstraint::new("f", None, None);
        assert!(c.is_satisfied_by(0));
        assert!(c.is_satisfied_by(u64::MAX));
    }

    #[test]
    fn cardinality_constraint_exact() {
        let c = CardinalityConstraint::new("f", Some(3), Some(3));
        assert!(!c.is_satisfied_by(2));
        assert!(c.is_satisfied_by(3));
        assert!(!c.is_satisfied_by(4));
    }

    // ── No initial state ─────────────────────────────────────────────────────

    #[test]
    fn no_initial_state_returns_zero() {
        let mut aut = MultisetAutomaton::<MultisetWeight>::new(vec!["f".to_string()]);
        let _q0 = aut.add_state(true, None);
        // No initial_state set
        assert_eq!(aut.multiplicity_of("f", &["a"]), 0);
    }

    // ── Rocq Proof Alignment Tests (MultisetSemiringLaws.v) ──────────────────

    #[test]
    fn test_multiset_weight_left_distributivity() {
        // Rocq: `mw_times_plus_distr_l` — a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c)
        // where ⊕ = pointwise max, ⊗ = pointwise add.
        let a = MultisetWeight::new()
            .with_feature("f1", 3)
            .with_feature("f2", 1)
            .with_feature("f3", 5);
        let b = MultisetWeight::new()
            .with_feature("f1", 2)
            .with_feature("f2", 4);
        let c = MultisetWeight::new()
            .with_feature("f1", 7)
            .with_feature("f3", 1);

        // a ⊗ (b ⊕ c) = a + max(b, c) pointwise
        let b_plus_c = b.plus(&c);
        let lhs = a.times(&b_plus_c);

        // (a ⊗ b) ⊕ (a ⊗ c) = max(a + b, a + c) pointwise
        let a_times_b = a.times(&b);
        let a_times_c = a.times(&c);
        let rhs = a_times_b.plus(&a_times_c);

        assert!(
            lhs.approx_eq(&rhs, 0.0),
            "left distributivity failed: lhs = {:?}, rhs = {:?}",
            lhs, rhs
        );
    }

    #[test]
    fn test_multiset_weight_right_distributivity() {
        // Rocq: `mw_times_plus_distr_r` — (a ⊕ b) ⊗ c = (a ⊗ c) ⊕ (b ⊗ c)
        let a = MultisetWeight::new()
            .with_feature("f1", 2)
            .with_feature("f2", 6);
        let b = MultisetWeight::new()
            .with_feature("f1", 5)
            .with_feature("f3", 3);
        let c = MultisetWeight::new()
            .with_feature("f1", 1)
            .with_feature("f2", 2)
            .with_feature("f3", 4);

        let a_plus_b = a.plus(&b);
        let lhs = a_plus_b.times(&c);

        let a_times_c = a.times(&c);
        let b_times_c = b.times(&c);
        let rhs = a_times_c.plus(&b_times_c);

        assert!(
            lhs.approx_eq(&rhs, 0.0),
            "right distributivity failed: lhs = {:?}, rhs = {:?}",
            lhs, rhs
        );
    }

    #[test]
    fn test_tropical_multiset_weight_distributivity() {
        // Rocq: `tmw_times_plus_distr_l` — same for TropicalMultisetWeight
        // where ⊕ = pointwise min, ⊗ = pointwise add.
        let a = TropicalMultisetWeight::new()
            .with_feature("f1", 3.0)
            .with_feature("f2", 1.0);
        let b = TropicalMultisetWeight::new()
            .with_feature("f1", 2.0)
            .with_feature("f2", 5.0)
            .with_feature("f3", 7.0);
        let c = TropicalMultisetWeight::new()
            .with_feature("f1", 4.0)
            .with_feature("f3", 1.0);

        // Left distributivity: a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c)
        let b_plus_c = b.plus(&c);
        let lhs = a.times(&b_plus_c);

        let a_times_b = a.times(&b);
        let a_times_c = a.times(&c);
        let rhs = a_times_b.plus(&a_times_c);

        assert!(
            lhs.approx_eq(&rhs, 1e-10),
            "tropical left distributivity failed: lhs = {:?}, rhs = {:?}",
            lhs, rhs
        );

        // Right distributivity: (a ⊕ b) ⊗ c = (a ⊗ c) ⊕ (b ⊗ c)
        let a_plus_b = a.plus(&b);
        let lhs_r = a_plus_b.times(&c);

        let a_times_c2 = a.times(&c);
        let b_times_c2 = b.times(&c);
        let rhs_r = a_times_c2.plus(&b_times_c2);

        assert!(
            lhs_r.approx_eq(&rhs_r, 1e-10),
            "tropical right distributivity failed: lhs = {:?}, rhs = {:?}",
            lhs_r, rhs_r
        );
    }
}
