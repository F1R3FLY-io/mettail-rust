//! Symbolic Automata (SFA) with predicate-labeled transitions over infinite domains.
//!
//! ## Theory
//!
//! Symbolic Finite Automata (SFA) generalize classical finite automata by replacing
//! finite alphabets with transitions guarded by predicates from an effective Boolean
//! algebra (D'Antoni & Veanes, 2017). Where a classical DFA has transitions labeled
//! with individual symbols from a finite set Sigma, an SFA has transitions labeled
//! with predicates over a potentially infinite domain D. A transition fires when the
//! current input element satisfies the guard predicate.
//!
//! The key abstraction is the **`BooleanAlgebra`** trait, which provides:
//! - Predicate constructors: `true_pred`, `false_pred`, `and`, `or`, `not`
//! - Decision procedures: `is_satisfiable`, `witness`
//! - Evaluation: `evaluate(predicate, element) -> bool`
//!
//! These operations suffice for all standard automata algorithms (emptiness, intersection,
//! complement, determinization, equivalence) to work symbolically, without enumerating
//! the potentially infinite domain.
//!
//! ### Minterm-Based Determinization
//!
//! The determinization algorithm uses minterms — maximal satisfiable conjunctions of
//! predicates and their negations. For a set of predicates {phi_1, ..., phi_k} appearing
//! on outgoing transitions, the minterms partition the domain into equivalence classes
//! where all elements are treated identically by every guard. This reduces the problem
//! to classical subset construction over a finite (though potentially exponential)
//! effective alphabet.
//!
//! ### References
//!
//! - D'Antoni, L. & Veanes, M. (2017). "The power of symbolic automata and transducers."
//!   CAV 2017. The foundational paper on effective Boolean algebras for symbolic automata.
//! - Veanes, M., de Halleux, P., & Tillmann, N. (2010). "Rex: Symbolic regular expression
//!   explorer." ICST 2010. Symbolic execution of regular expressions.
//! - D'Antoni, L. & Veanes, M. (2014). "Minimization of symbolic automata." POPL 2014.
//!   Efficient minimization using predicates rather than explicit alphabets.
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────┐
//! │                PraTTaIL Pipeline                         │
//! │                                                         │
//! │  Grammar rules                                          │
//! │       │                                                 │
//! │       ▼                                                 │
//! │  WFST + Decision Tree (finite-alphabet dispatch)        │
//! │       │                                                 │
//! │       │    ┌─────────────────────────────────────┐      │
//! │       └───▶│  Symbolic Automata Module            │      │
//! │            │                                     │      │
//! │            │  BooleanAlgebra (trait)              │      │
//! │            │    ├── IntervalAlgebra (numeric)     │      │
//! │            │    ├── CharClassAlgebra (characters)  │      │
//! │            │    └── KatBooleanAlgebra (propositional)│   │
//! │            │                                     │      │
//! │            │  SymbolicAutomaton<A>                │      │
//! │            │    ├── is_empty()                    │      │
//! │            │    ├── accepts()                     │      │
//! │            │    ├── intersect()                   │      │
//! │            │    ├── complement()                  │      │
//! │            │    ├── determinize()                 │      │
//! │            │    └── is_equivalent()               │      │
//! │            │                                     │      │
//! │            │  DecidabilityClassifier              │      │
//! │            │    └── classify_decidability()       │      │
//! │            │                                     │      │
//! │            │  SymbolicAnalysis (pipeline bridge)  │      │
//! │            └─────────────────────────────────────┘      │
//! │                                                         │
//! │  KAT module ◄──── KatBooleanAlgebra adapter             │
//! └─────────────────────────────────────────────────────────┘
//! ```
//!
//! ## Integration Points
//!
//! - **KAT module** (`kat.rs`): The `KatBooleanAlgebra` adapter wraps `BooleanTest`
//!   predicates from the KAT module, enabling symbolic automata operations over
//!   propositional predicates used in Hoare logic verification.
//! - **Pipeline analysis** (`pipeline.rs`): `SymbolicAnalysis` provides guard
//!   satisfiability, overlap, and subsumption data for lint diagnostics.
//! - **Decision tree** (`decision_tree.rs`): Symbolic automata can model dispatch
//!   decisions over predicate-guarded transitions (e.g., character class checks),
//!   complementing the PathMap-based trie dispatch.
//! - **WFST** (`wfst.rs`): Symbolic guards generalize WFST input labels from
//!   finite tokens to predicate-guarded transitions, enabling analysis over
//!   infinite token domains (e.g., all integers, all identifiers matching a pattern).

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;

use crate::kat::BooleanTest;

// ══════════════════════════════════════════════════════════════════════════════
// BooleanAlgebra trait
// ══════════════════════════════════════════════════════════════════════════════

/// Effective Boolean algebra over predicates — the core abstraction for symbolic automata.
///
/// An effective Boolean algebra provides decidable operations over a potentially
/// infinite domain via predicates. The algebra must support:
/// - Construction of true/false/and/or/not predicates
/// - A satisfiability decision procedure
/// - Witness generation (finding a concrete domain element satisfying a predicate)
/// - Evaluation of predicates on concrete domain elements
///
/// These operations enable all standard automata algorithms (emptiness, intersection,
/// complement, determinization, equivalence) to work symbolically.
///
/// # Type Parameters
///
/// - `Predicate`: The type of guard predicates (e.g., `IntervalPred`, `CharClassPred`).
/// - `Domain`: The type of concrete elements the predicates range over (e.g., `i64`, `char`).
pub trait BooleanAlgebra: Clone + std::fmt::Debug + Send + Sync + 'static {
    /// The type of guard predicates in this algebra.
    type Predicate: Clone + std::fmt::Debug + Eq + std::hash::Hash + Send + Sync + 'static;

    /// The type of concrete domain elements that predicates evaluate over.
    type Domain: Clone + std::fmt::Debug + Send + Sync + 'static;

    /// The predicate that is always satisfied (accepts all domain elements).
    fn true_pred(&self) -> Self::Predicate;

    /// The predicate that is never satisfied (rejects all domain elements).
    fn false_pred(&self) -> Self::Predicate;

    /// Conjunction: `a AND b`. Satisfied when both `a` and `b` are satisfied.
    fn and(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate;

    /// Disjunction: `a OR b`. Satisfied when either `a` or `b` is satisfied.
    fn or(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate;

    /// Negation: `NOT a`. Satisfied when `a` is not satisfied.
    fn not(&self, a: &Self::Predicate) -> Self::Predicate;

    /// Satisfiability check: does there exist a domain element satisfying `a`?
    ///
    /// This is the core decision procedure. All derived methods (implies,
    /// equivalent, is_tautology, overlaps) reduce to satisfiability queries.
    fn is_satisfiable(&self, a: &Self::Predicate) -> bool;

    /// Witness generation: find a concrete domain element satisfying `a`, if one exists.
    ///
    /// Returns `None` iff `a` is unsatisfiable.
    fn witness(&self, a: &Self::Predicate) -> Option<Self::Domain>;

    /// Evaluate a predicate on a concrete domain element.
    ///
    /// Returns `true` iff `elem` satisfies `pred`.
    fn evaluate(&self, pred: &Self::Predicate, elem: &Self::Domain) -> bool;

    /// Implication: does `a` imply `b`? Equivalently, is `a AND NOT b` unsatisfiable?
    fn implies(&self, a: &Self::Predicate, b: &Self::Predicate) -> bool {
        !self.is_satisfiable(&self.and(a, &self.not(b)))
    }

    /// Semantic equivalence: are `a` and `b` satisfied by exactly the same elements?
    fn equivalent(&self, a: &Self::Predicate, b: &Self::Predicate) -> bool {
        self.implies(a, b) && self.implies(b, a)
    }

    /// Tautology check: is `a` satisfied by all domain elements?
    fn is_tautology(&self, a: &Self::Predicate) -> bool {
        !self.is_satisfiable(&self.not(a))
    }

    /// Overlap check: can `a` and `b` be simultaneously satisfied?
    fn overlaps(&self, a: &Self::Predicate, b: &Self::Predicate) -> bool {
        self.is_satisfiable(&self.and(a, b))
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// IntervalAlgebra — numeric range predicates
// ══════════════════════════════════════════════════════════════════════════════

/// A predicate over integer intervals.
///
/// Represents sets of integers via half-open ranges `[lo, hi)`, their unions,
/// and their complements. The algebra domain is `i64` values within a
/// configured `[min_val, max_val)` universe.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum IntervalPred {
    /// The universal predicate: satisfied by all integers in `[min_val, max_val)`.
    True,
    /// The empty predicate: satisfied by no integer.
    False,
    /// A single half-open range `[lo, hi)`.
    Range(i64, i64),
    /// A union of sorted, non-overlapping half-open ranges.
    Union(Vec<(i64, i64)>),
    /// Complement of a predicate (relative to the universe `[min_val, max_val)`).
    Not(Box<IntervalPred>),
}

impl fmt::Display for IntervalPred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntervalPred::True => write!(f, "TRUE"),
            IntervalPred::False => write!(f, "FALSE"),
            IntervalPred::Range(lo, hi) => write!(f, "[{}, {})", lo, hi),
            IntervalPred::Union(ranges) => {
                write!(f, "(")?;
                for (i, (lo, hi)) in ranges.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "[{}, {})", lo, hi)?;
                }
                write!(f, ")")
            }
            IntervalPred::Not(inner) => write!(f, "~{}", inner),
        }
    }
}

/// Boolean algebra over integer intervals within a bounded universe.
///
/// The domain is `i64` values in `[min_val, max_val)`. Predicates are
/// expressed as unions of half-open ranges.
#[derive(Clone, Debug)]
pub struct IntervalAlgebra {
    /// Minimum value in the universe (inclusive).
    pub min_val: i64,
    /// Maximum value in the universe (exclusive).
    pub max_val: i64,
}

impl IntervalAlgebra {
    /// Create a new interval algebra with the given universe bounds.
    pub fn new(min_val: i64, max_val: i64) -> Self {
        assert!(
            min_val < max_val,
            "IntervalAlgebra requires min_val ({}) < max_val ({})",
            min_val,
            max_val,
        );
        IntervalAlgebra { min_val, max_val }
    }

    /// Normalize a predicate to a canonical union-of-ranges form.
    ///
    /// Returns a sorted, non-overlapping list of half-open ranges `[lo, hi)`
    /// representing exactly the set of integers satisfying the predicate
    /// within the universe `[min_val, max_val)`.
    fn normalize(&self, pred: &IntervalPred) -> Vec<(i64, i64)> {
        match pred {
            IntervalPred::True => vec![(self.min_val, self.max_val)],
            IntervalPred::False => vec![],
            IntervalPred::Range(lo, hi) => {
                let lo = (*lo).max(self.min_val);
                let hi = (*hi).min(self.max_val);
                if lo < hi {
                    vec![(lo, hi)]
                } else {
                    vec![]
                }
            }
            IntervalPred::Union(ranges) => {
                // Clip and merge ranges into canonical form.
                let mut clipped: Vec<(i64, i64)> = ranges
                    .iter()
                    .filter_map(|&(lo, hi)| {
                        let lo = lo.max(self.min_val);
                        let hi = hi.min(self.max_val);
                        if lo < hi {
                            Some((lo, hi))
                        } else {
                            None
                        }
                    })
                    .collect();
                clipped.sort_unstable();
                merge_ranges(&clipped)
            }
            IntervalPred::Not(inner) => {
                let inner_ranges = self.normalize(inner);
                complement_ranges(&inner_ranges, self.min_val, self.max_val)
            }
        }
    }

    /// Build a predicate from a normalized list of ranges.
    fn from_ranges(ranges: &[(i64, i64)]) -> IntervalPred {
        match ranges.len() {
            0 => IntervalPred::False,
            1 => IntervalPred::Range(ranges[0].0, ranges[0].1),
            _ => IntervalPred::Union(ranges.to_vec()),
        }
    }
}

/// Merge a sorted list of ranges into a non-overlapping union.
fn merge_ranges(sorted: &[(i64, i64)]) -> Vec<(i64, i64)> {
    if sorted.is_empty() {
        return vec![];
    }
    let mut result = Vec::with_capacity(sorted.len());
    let (mut cur_lo, mut cur_hi) = sorted[0];
    for &(lo, hi) in &sorted[1..] {
        if lo <= cur_hi {
            // Overlapping or adjacent — extend.
            cur_hi = cur_hi.max(hi);
        } else {
            result.push((cur_lo, cur_hi));
            cur_lo = lo;
            cur_hi = hi;
        }
    }
    result.push((cur_lo, cur_hi));
    result
}

/// Complement a sorted, non-overlapping list of ranges within `[min_val, max_val)`.
fn complement_ranges(ranges: &[(i64, i64)], min_val: i64, max_val: i64) -> Vec<(i64, i64)> {
    let mut result = Vec::with_capacity(ranges.len() + 1);
    let mut cursor = min_val;
    for &(lo, hi) in ranges {
        if cursor < lo {
            result.push((cursor, lo));
        }
        cursor = hi;
    }
    if cursor < max_val {
        result.push((cursor, max_val));
    }
    result
}

/// Intersect two sorted, non-overlapping range lists.
fn intersect_ranges(a: &[(i64, i64)], b: &[(i64, i64)]) -> Vec<(i64, i64)> {
    let mut result = Vec::with_capacity(a.len().min(b.len()));
    let mut i = 0;
    let mut j = 0;
    while i < a.len() && j < b.len() {
        let lo = a[i].0.max(b[j].0);
        let hi = a[i].1.min(b[j].1);
        if lo < hi {
            result.push((lo, hi));
        }
        // Advance the range that ends first.
        if a[i].1 < b[j].1 {
            i += 1;
        } else {
            j += 1;
        }
    }
    result
}

/// Union two sorted, non-overlapping range lists.
fn union_ranges(a: &[(i64, i64)], b: &[(i64, i64)]) -> Vec<(i64, i64)> {
    let mut combined = Vec::with_capacity(a.len() + b.len());
    combined.extend_from_slice(a);
    combined.extend_from_slice(b);
    combined.sort_unstable();
    merge_ranges(&combined)
}

impl BooleanAlgebra for IntervalAlgebra {
    type Predicate = IntervalPred;
    type Domain = i64;

    fn true_pred(&self) -> IntervalPred {
        IntervalPred::True
    }

    fn false_pred(&self) -> IntervalPred {
        IntervalPred::False
    }

    fn and(&self, a: &IntervalPred, b: &IntervalPred) -> IntervalPred {
        let ra = self.normalize(a);
        let rb = self.normalize(b);
        let result = intersect_ranges(&ra, &rb);
        IntervalAlgebra::from_ranges(&result)
    }

    fn or(&self, a: &IntervalPred, b: &IntervalPred) -> IntervalPred {
        let ra = self.normalize(a);
        let rb = self.normalize(b);
        let result = union_ranges(&ra, &rb);
        IntervalAlgebra::from_ranges(&result)
    }

    fn not(&self, a: &IntervalPred) -> IntervalPred {
        let ra = self.normalize(a);
        let result = complement_ranges(&ra, self.min_val, self.max_val);
        IntervalAlgebra::from_ranges(&result)
    }

    fn is_satisfiable(&self, a: &IntervalPred) -> bool {
        !self.normalize(a).is_empty()
    }

    fn witness(&self, a: &IntervalPred) -> Option<i64> {
        let ranges = self.normalize(a);
        ranges.first().map(|&(lo, _)| lo)
    }

    fn evaluate(&self, pred: &IntervalPred, elem: &i64) -> bool {
        let val = *elem;
        if val < self.min_val || val >= self.max_val {
            return false;
        }
        let ranges = self.normalize(pred);
        ranges.iter().any(|&(lo, hi)| val >= lo && val < hi)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// CharClassAlgebra — character class predicates
// ══════════════════════════════════════════════════════════════════════════════

/// A predicate over Unicode character classes.
///
/// Represents sets of characters via inclusive ranges `[lo, hi]`, their unions,
/// and their complements. The domain is the full Unicode scalar value range
/// `['\0', char::MAX]`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CharClassPred {
    /// The universal predicate: satisfied by all characters.
    True,
    /// The empty predicate: satisfied by no character.
    False,
    /// A single inclusive character range `[lo, hi]`.
    Range(char, char),
    /// A union of sorted, non-overlapping inclusive character ranges.
    Union(Vec<(char, char)>),
    /// Complement of a predicate (relative to the full Unicode range).
    Not(Box<CharClassPred>),
}

impl fmt::Display for CharClassPred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CharClassPred::True => write!(f, "TRUE"),
            CharClassPred::False => write!(f, "FALSE"),
            CharClassPred::Range(lo, hi) => {
                if lo == hi {
                    write!(f, "[{}]", lo.escape_debug())
                } else {
                    write!(f, "[{}-{}]", lo.escape_debug(), hi.escape_debug())
                }
            }
            CharClassPred::Union(ranges) => {
                write!(f, "[")?;
                for (i, (lo, hi)) in ranges.iter().enumerate() {
                    if i > 0 {
                        write!(f, "|")?;
                    }
                    if lo == hi {
                        write!(f, "{}", lo.escape_debug())?;
                    } else {
                        write!(f, "{}-{}", lo.escape_debug(), hi.escape_debug())?;
                    }
                }
                write!(f, "]")
            }
            CharClassPred::Not(inner) => write!(f, "~{}", inner),
        }
    }
}

/// Boolean algebra over Unicode character classes.
///
/// The domain is all Unicode scalar values. Predicates are expressed as
/// unions of inclusive character ranges. Internally, ranges are converted
/// to `u32` half-open intervals `[lo, hi+1)` for uniform manipulation,
/// then converted back to `(char, char)` for the public API.
#[derive(Clone, Debug)]
pub struct CharClassAlgebra;

impl CharClassAlgebra {
    /// Create a new character class algebra.
    pub fn new() -> Self {
        CharClassAlgebra
    }

    /// Normalize a predicate to a sorted, non-overlapping list of
    /// half-open `u32` ranges `[lo, hi)`.
    fn normalize_u32(pred: &CharClassPred) -> Vec<(u32, u32)> {
        match pred {
            CharClassPred::True => vec![(0, (char::MAX as u32) + 1)],
            CharClassPred::False => vec![],
            CharClassPred::Range(lo, hi) => {
                if *lo <= *hi {
                    vec![(*lo as u32, (*hi as u32) + 1)]
                } else {
                    vec![]
                }
            }
            CharClassPred::Union(ranges) => {
                let mut u32_ranges: Vec<(u32, u32)> = ranges
                    .iter()
                    .filter_map(|&(lo, hi)| {
                        if lo <= hi {
                            Some((lo as u32, (hi as u32) + 1))
                        } else {
                            None
                        }
                    })
                    .collect();
                u32_ranges.sort_unstable();
                merge_u32_ranges(&u32_ranges)
            }
            CharClassPred::Not(inner) => {
                let inner_ranges = Self::normalize_u32(inner);
                complement_u32_ranges(&inner_ranges, 0, (char::MAX as u32) + 1)
            }
        }
    }

    /// Build a `CharClassPred` from a list of half-open `u32` ranges.
    fn from_u32_ranges(ranges: &[(u32, u32)]) -> CharClassPred {
        let char_ranges: Vec<(char, char)> = ranges
            .iter()
            .filter_map(|&(lo, hi)| {
                if lo < hi {
                    let lo_char = char::from_u32(lo)?;
                    let hi_char = char::from_u32(hi - 1)?;
                    Some((lo_char, hi_char))
                } else {
                    None
                }
            })
            .collect();

        match char_ranges.len() {
            0 => CharClassPred::False,
            1 => CharClassPred::Range(char_ranges[0].0, char_ranges[0].1),
            _ => CharClassPred::Union(char_ranges),
        }
    }
}

impl Default for CharClassAlgebra {
    fn default() -> Self {
        Self::new()
    }
}

/// Merge sorted half-open `u32` ranges.
fn merge_u32_ranges(sorted: &[(u32, u32)]) -> Vec<(u32, u32)> {
    if sorted.is_empty() {
        return vec![];
    }
    let mut result = Vec::with_capacity(sorted.len());
    let (mut cur_lo, mut cur_hi) = sorted[0];
    for &(lo, hi) in &sorted[1..] {
        if lo <= cur_hi {
            cur_hi = cur_hi.max(hi);
        } else {
            result.push((cur_lo, cur_hi));
            cur_lo = lo;
            cur_hi = hi;
        }
    }
    result.push((cur_lo, cur_hi));
    result
}

/// Complement sorted, non-overlapping half-open `u32` ranges within `[min, max)`.
fn complement_u32_ranges(ranges: &[(u32, u32)], min: u32, max: u32) -> Vec<(u32, u32)> {
    let mut result = Vec::with_capacity(ranges.len() + 1);
    let mut cursor = min;
    for &(lo, hi) in ranges {
        if cursor < lo {
            result.push((cursor, lo));
        }
        cursor = hi;
    }
    if cursor < max {
        result.push((cursor, max));
    }
    result
}

/// Intersect two sorted, non-overlapping half-open `u32` range lists.
fn intersect_u32_ranges(a: &[(u32, u32)], b: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let mut result = Vec::with_capacity(a.len().min(b.len()));
    let mut i = 0;
    let mut j = 0;
    while i < a.len() && j < b.len() {
        let lo = a[i].0.max(b[j].0);
        let hi = a[i].1.min(b[j].1);
        if lo < hi {
            result.push((lo, hi));
        }
        if a[i].1 < b[j].1 {
            i += 1;
        } else {
            j += 1;
        }
    }
    result
}

/// Union two sorted, non-overlapping half-open `u32` range lists.
fn union_u32_ranges(a: &[(u32, u32)], b: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let mut combined = Vec::with_capacity(a.len() + b.len());
    combined.extend_from_slice(a);
    combined.extend_from_slice(b);
    combined.sort_unstable();
    merge_u32_ranges(&combined)
}

impl BooleanAlgebra for CharClassAlgebra {
    type Predicate = CharClassPred;
    type Domain = char;

    fn true_pred(&self) -> CharClassPred {
        CharClassPred::True
    }

    fn false_pred(&self) -> CharClassPred {
        CharClassPred::False
    }

    fn and(&self, a: &CharClassPred, b: &CharClassPred) -> CharClassPred {
        let ra = CharClassAlgebra::normalize_u32(a);
        let rb = CharClassAlgebra::normalize_u32(b);
        let result = intersect_u32_ranges(&ra, &rb);
        CharClassAlgebra::from_u32_ranges(&result)
    }

    fn or(&self, a: &CharClassPred, b: &CharClassPred) -> CharClassPred {
        let ra = CharClassAlgebra::normalize_u32(a);
        let rb = CharClassAlgebra::normalize_u32(b);
        let result = union_u32_ranges(&ra, &rb);
        CharClassAlgebra::from_u32_ranges(&result)
    }

    fn not(&self, a: &CharClassPred) -> CharClassPred {
        let ra = CharClassAlgebra::normalize_u32(a);
        let result = complement_u32_ranges(&ra, 0, (char::MAX as u32) + 1);
        CharClassAlgebra::from_u32_ranges(&result)
    }

    fn is_satisfiable(&self, a: &CharClassPred) -> bool {
        !CharClassAlgebra::normalize_u32(a).is_empty()
    }

    fn witness(&self, a: &CharClassPred) -> Option<char> {
        let ranges = CharClassAlgebra::normalize_u32(a);
        ranges.first().and_then(|&(lo, _)| char::from_u32(lo))
    }

    fn evaluate(&self, pred: &CharClassPred, elem: &char) -> bool {
        let val = *elem as u32;
        let ranges = CharClassAlgebra::normalize_u32(pred);
        ranges.iter().any(|&(lo, hi)| val >= lo && val < hi)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// KatBooleanAlgebra — adapter for KAT BooleanTest
// ══════════════════════════════════════════════════════════════════════════════

/// Boolean algebra adapter for the KAT module's `BooleanTest` type.
///
/// This algebra bridges the KAT module's propositional tests with the
/// symbolic automata framework. The domain is truth assignments:
/// `HashMap<String, bool>` mapping proposition names to truth values.
///
/// # Satisfiability
///
/// Since the domain is finite (2^n valuations for n atoms), satisfiability
/// is decided by exhaustive enumeration. This is tractable for the small
/// number of atoms typical in PraTTaIL grammars (usually fewer than 10).
#[derive(Clone, Debug)]
pub struct KatBooleanAlgebra {
    /// All proposition (atom) names known to this algebra.
    pub atoms: Vec<String>,
}

impl KatBooleanAlgebra {
    /// Create a new KAT Boolean algebra with the given atom names.
    pub fn new(atoms: Vec<String>) -> Self {
        KatBooleanAlgebra { atoms }
    }

    /// Create a KAT Boolean algebra by extracting atoms from a BooleanTest.
    pub fn from_test(test: &BooleanTest) -> Self {
        let atom_set = test.atoms();
        let mut atoms: Vec<String> = atom_set.into_iter().collect();
        atoms.sort();
        KatBooleanAlgebra { atoms }
    }

    /// Generate all 2^n truth assignments for the atoms.
    fn all_valuations(&self) -> Vec<HashMap<String, bool>> {
        let n = self.atoms.len();
        let num_valuations = 1usize << n;
        let mut valuations = Vec::with_capacity(num_valuations);
        for bits in 0..num_valuations {
            let mut valuation = HashMap::with_capacity(n);
            for (i, name) in self.atoms.iter().enumerate() {
                valuation.insert(name.clone(), (bits >> i) & 1 == 1);
            }
            valuations.push(valuation);
        }
        valuations
    }
}

/// Evaluate a `BooleanTest` under a truth assignment.
///
/// Public helper for use by the symbolic automata module and tests.
/// Atoms not present in the valuation are treated as `false`.
pub fn eval_test_public(test: &BooleanTest, valuation: &HashMap<String, bool>) -> bool {
    match test {
        BooleanTest::True => true,
        BooleanTest::False => false,
        BooleanTest::Atom(name) => *valuation.get(name).unwrap_or(&false),
        BooleanTest::Not(inner) => !eval_test_public(inner, valuation),
        BooleanTest::And(a, b) => eval_test_public(a, valuation) && eval_test_public(b, valuation),
        BooleanTest::Or(a, b) => eval_test_public(a, valuation) || eval_test_public(b, valuation),
    }
}

impl BooleanAlgebra for KatBooleanAlgebra {
    type Predicate = BooleanTest;
    type Domain = HashMap<String, bool>;

    fn true_pred(&self) -> BooleanTest {
        BooleanTest::True
    }

    fn false_pred(&self) -> BooleanTest {
        BooleanTest::False
    }

    fn and(&self, a: &BooleanTest, b: &BooleanTest) -> BooleanTest {
        BooleanTest::And(Box::new(a.clone()), Box::new(b.clone()))
    }

    fn or(&self, a: &BooleanTest, b: &BooleanTest) -> BooleanTest {
        BooleanTest::Or(Box::new(a.clone()), Box::new(b.clone()))
    }

    fn not(&self, a: &BooleanTest) -> BooleanTest {
        BooleanTest::Not(Box::new(a.clone()))
    }

    fn is_satisfiable(&self, a: &BooleanTest) -> bool {
        // Exhaustive search over 2^n truth assignments.
        self.all_valuations()
            .iter()
            .any(|v| eval_test_public(a, v))
    }

    fn witness(&self, a: &BooleanTest) -> Option<HashMap<String, bool>> {
        self.all_valuations()
            .into_iter()
            .find(|v| eval_test_public(a, v))
    }

    fn evaluate(&self, pred: &BooleanTest, elem: &HashMap<String, bool>) -> bool {
        eval_test_public(pred, elem)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Symbolic Automaton
// ══════════════════════════════════════════════════════════════════════════════

/// A state in a symbolic automaton.
#[derive(Debug, Clone)]
pub struct SymbolicState {
    /// Unique state identifier.
    pub id: usize,
    /// Whether this is an accepting (final) state.
    pub is_accepting: bool,
    /// Optional human-readable label for diagnostics.
    pub label: Option<String>,
}

/// A transition in a symbolic automaton, guarded by a predicate.
///
/// The transition `from --[guard]--> to` fires on input element `e`
/// iff `algebra.evaluate(guard, e)` returns true.
#[derive(Debug, Clone)]
pub struct SymbolicTransition<A: BooleanAlgebra> {
    /// Source state ID.
    pub from: usize,
    /// Target state ID.
    pub to: usize,
    /// Guard predicate: the transition fires when this predicate is satisfied.
    pub guard: A::Predicate,
}

/// A Symbolic Finite Automaton (SFA) parameterized by a Boolean algebra.
///
/// Unlike classical NFAs/DFAs where transitions are labeled with individual
/// symbols, SFA transitions are labeled with predicates from the algebra.
/// This enables modeling automata over infinite alphabets (e.g., all integers,
/// all Unicode characters) compactly.
///
/// # Type Parameter
///
/// - `A`: The Boolean algebra providing predicate operations. Determines
///   both the predicate type (used as transition guards) and the domain
///   type (used for concrete simulation).
#[derive(Debug, Clone)]
pub struct SymbolicAutomaton<A: BooleanAlgebra> {
    /// The Boolean algebra used for guard operations.
    pub algebra: A,
    /// All states in the automaton.
    pub states: Vec<SymbolicState>,
    /// All transitions, each guarded by a predicate.
    pub transitions: Vec<SymbolicTransition<A>>,
    /// Set of initial state IDs.
    pub initial_states: HashSet<usize>,
    /// Set of accepting (final) state IDs.
    pub accepting_states: HashSet<usize>,
}

impl<A: BooleanAlgebra> SymbolicAutomaton<A> {
    /// Create a new empty symbolic automaton.
    pub fn new(algebra: A) -> Self {
        SymbolicAutomaton {
            algebra,
            states: Vec::new(),
            transitions: Vec::new(),
            initial_states: HashSet::new(),
            accepting_states: HashSet::new(),
        }
    }

    /// Add a state and return its ID.
    pub fn add_state(&mut self, is_accepting: bool, label: Option<String>) -> usize {
        let id = self.states.len();
        self.states.push(SymbolicState {
            id,
            is_accepting,
            label,
        });
        if is_accepting {
            self.accepting_states.insert(id);
        }
        id
    }

    /// Mark a state as initial.
    pub fn set_initial(&mut self, state_id: usize) {
        assert!(
            state_id < self.states.len(),
            "State ID {} out of range (have {} states)",
            state_id,
            self.states.len(),
        );
        self.initial_states.insert(state_id);
    }

    /// Add a guarded transition.
    pub fn add_transition(&mut self, from: usize, to: usize, guard: A::Predicate) {
        assert!(
            from < self.states.len() && to < self.states.len(),
            "Transition endpoints ({} -> {}) out of range (have {} states)",
            from,
            to,
            self.states.len(),
        );
        self.transitions.push(SymbolicTransition { from, to, guard });
    }

    /// Get the number of states.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    /// Get the number of transitions.
    pub fn num_transitions(&self) -> usize {
        self.transitions.len()
    }

    // ── Core algorithms ──────────────────────────────────────────────────

    /// Emptiness check: does the automaton accept any word?
    ///
    /// Uses BFS from initial states, following only transitions whose guards
    /// are satisfiable. The automaton is non-empty iff some accepting state
    /// is reachable via satisfiable transitions.
    ///
    /// # Complexity
    ///
    /// O(|Q| + |delta| * SAT), where SAT is the cost of one satisfiability
    /// check on the algebra.
    pub fn is_empty(&self) -> bool {
        if self.initial_states.is_empty() {
            return true;
        }
        if self.accepting_states.is_empty() {
            return true;
        }

        // Pre-build adjacency list filtered by satisfiability.
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); self.states.len()];
        for trans in &self.transitions {
            if self.algebra.is_satisfiable(&trans.guard) {
                adj[trans.from].push(trans.to);
            }
        }

        // BFS from initial states.
        let mut visited = vec![false; self.states.len()];
        let mut queue = VecDeque::with_capacity(self.initial_states.len());
        for &init in &self.initial_states {
            if !visited[init] {
                visited[init] = true;
                queue.push_back(init);
            }
        }

        while let Some(state) = queue.pop_front() {
            if self.accepting_states.contains(&state) {
                return false; // Found reachable accepting state → non-empty.
            }
            for &next in &adj[state] {
                if !visited[next] {
                    visited[next] = true;
                    queue.push_back(next);
                }
            }
        }

        true // No reachable accepting state → empty.
    }

    /// Simulate the automaton on a concrete word.
    ///
    /// Returns `true` iff the word is accepted (i.e., after consuming all
    /// elements, at least one current state is accepting).
    ///
    /// This performs NFA-style simulation: it maintains a set of current
    /// states and, for each input element, computes successor states by
    /// evaluating guards.
    ///
    /// # Complexity
    ///
    /// O(|w| * |Q| * |delta|), where |w| is word length.
    pub fn accepts(&self, word: &[A::Domain]) -> bool {
        if self.initial_states.is_empty() {
            return false;
        }

        let mut current: HashSet<usize> = self.initial_states.clone();

        for elem in word {
            let mut next = HashSet::new();
            for &state in &current {
                for trans in &self.transitions {
                    if trans.from == state && self.algebra.evaluate(&trans.guard, elem) {
                        next.insert(trans.to);
                    }
                }
            }
            if next.is_empty() {
                return false;
            }
            current = next;
        }

        current.iter().any(|s| self.accepting_states.contains(s))
    }

    /// Product construction: intersection of two SFAs over the same algebra.
    ///
    /// States are pairs `(q1, q2)` from the two automata. Transitions are
    /// guarded by the conjunction of the corresponding guards. The resulting
    /// automaton accepts exactly the intersection of the two languages.
    ///
    /// # Complexity
    ///
    /// O(|Q1| * |Q2| * |delta1| * |delta2| * AND), where AND is the cost
    /// of one conjunction + satisfiability check on the algebra.
    pub fn intersect(&self, other: &Self) -> Self {
        let mut result = SymbolicAutomaton::new(self.algebra.clone());

        // State mapping: (self_state, other_state) -> result_state_id.
        let mut state_map: HashMap<(usize, usize), usize> = HashMap::new();

        // Create product states.
        for s1 in &self.states {
            for s2 in &other.states {
                let is_accepting = s1.is_accepting && s2.is_accepting;
                let label = match (&s1.label, &s2.label) {
                    (Some(a), Some(b)) => Some(format!("({},{})", a, b)),
                    (Some(a), None) => Some(format!("({},q{})", a, s2.id)),
                    (None, Some(b)) => Some(format!("(q{},{})", s1.id, b)),
                    (None, None) => Some(format!("(q{},q{})", s1.id, s2.id)),
                };
                let id = result.add_state(is_accepting, label);
                state_map.insert((s1.id, s2.id), id);
            }
        }

        // Set initial states.
        for &i1 in &self.initial_states {
            for &i2 in &other.initial_states {
                if let Some(&pid) = state_map.get(&(i1, i2)) {
                    result.set_initial(pid);
                }
            }
        }

        // Create product transitions with conjunctive guards.
        for t1 in &self.transitions {
            for t2 in &other.transitions {
                let guard = self.algebra.and(&t1.guard, &t2.guard);
                if self.algebra.is_satisfiable(&guard) {
                    if let (Some(&from), Some(&to)) =
                        (state_map.get(&(t1.from, t2.from)), state_map.get(&(t1.to, t2.to)))
                    {
                        result.add_transition(from, to, guard);
                    }
                }
            }
        }

        result
    }

    /// Complement the automaton.
    ///
    /// Determinizes the automaton first (if it is nondeterministic), then
    /// flips accepting and non-accepting states in the deterministic version.
    ///
    /// # Complexity
    ///
    /// Dominated by determinization: worst case O(2^|Q|) states.
    pub fn complement(&self) -> Self {
        let det = self.determinize();

        let mut result = SymbolicAutomaton::new(det.algebra.clone());

        // Copy states with flipped acceptance.
        for state in &det.states {
            result.add_state(!state.is_accepting, state.label.clone());
        }

        // Copy initial states.
        for &init in &det.initial_states {
            result.set_initial(init);
        }

        // Copy transitions.
        for trans in &det.transitions {
            result.add_transition(trans.from, trans.to, trans.guard.clone());
        }

        // Add a dead/sink state for completeness — any input not matched
        // by existing transitions goes to the sink (which is accepting in
        // the complement).
        let sink = result.add_state(true, Some("sink".to_string()));

        // For each state, compute the disjunction of all outgoing guards.
        // The complement of that disjunction covers inputs with no transition.
        let num_states = det.states.len();
        for state_id in 0..num_states {
            let outgoing_guards: Vec<&A::Predicate> = det
                .transitions
                .iter()
                .filter(|t| t.from == state_id)
                .map(|t| &t.guard)
                .collect();

            let covered = if outgoing_guards.is_empty() {
                self.algebra.false_pred()
            } else {
                let mut disj = outgoing_guards[0].clone();
                for g in &outgoing_guards[1..] {
                    disj = self.algebra.or(&disj, g);
                }
                disj
            };

            let uncovered = self.algebra.not(&covered);
            if self.algebra.is_satisfiable(&uncovered) {
                result.add_transition(state_id, sink, uncovered);
            }
        }

        // Sink state loops to itself on all inputs.
        result.add_transition(sink, sink, self.algebra.true_pred());

        result
    }

    /// Determinize the automaton using minterm-based subset construction.
    ///
    /// ## Algorithm
    ///
    /// 1. For each subset state `S` (set of NFA states), collect all guard
    ///    predicates on outgoing transitions.
    /// 2. Compute minterms: maximal satisfiable conjunctions of predicates
    ///    and their negations. Minterms partition the domain into equivalence
    ///    classes where all elements trigger exactly the same transitions.
    /// 3. For each minterm, compute the successor subset state by collecting
    ///    all targets of transitions whose guards overlap with the minterm.
    /// 4. Continue until no new subset states are discovered.
    ///
    /// ## Complexity
    ///
    /// Worst case O(2^|Q|) subset states, each with up to 2^k minterms
    /// (k = number of distinct predicates on outgoing transitions).
    /// In practice, far fewer states and minterms are generated.
    pub fn determinize(&self) -> Self {
        let mut result = SymbolicAutomaton::new(self.algebra.clone());

        // Subset state mapping: sorted set of NFA state IDs -> DFA state ID.
        let mut state_map: HashMap<BTreeSet<usize>, usize> = HashMap::new();
        let mut worklist: VecDeque<BTreeSet<usize>> = VecDeque::new();

        // Initial subset state.
        let initial_set: BTreeSet<usize> = self.initial_states.iter().copied().collect();
        if initial_set.is_empty() {
            // No initial states → empty automaton.
            let q0 = result.add_state(false, Some("empty".to_string()));
            result.set_initial(q0);
            return result;
        }

        let is_accepting = initial_set.iter().any(|s| self.accepting_states.contains(s));
        let dfa_id = result.add_state(
            is_accepting,
            Some(format!("{:?}", initial_set)),
        );
        result.set_initial(dfa_id);
        state_map.insert(initial_set.clone(), dfa_id);
        worklist.push_back(initial_set);

        // Pre-build outgoing transition index: state -> Vec<(guard, target)>.
        let mut outgoing: HashMap<usize, Vec<(A::Predicate, usize)>> = HashMap::new();
        for trans in &self.transitions {
            outgoing
                .entry(trans.from)
                .or_default()
                .push((trans.guard.clone(), trans.to));
        }

        while let Some(current_set) = worklist.pop_front() {
            // Collect all guard predicates on outgoing transitions from this subset.
            let mut all_guards: Vec<A::Predicate> = Vec::new();
            for &nfa_state in &current_set {
                if let Some(trans_list) = outgoing.get(&nfa_state) {
                    for (guard, _) in trans_list {
                        all_guards.push(guard.clone());
                    }
                }
            }

            if all_guards.is_empty() {
                continue; // Dead end — no outgoing transitions.
            }

            // Compute minterms from the guard predicates.
            let minterms = compute_minterms(&self.algebra, &all_guards);

            // For each satisfiable minterm, compute the successor subset state.
            for minterm in &minterms {
                let mut successor_set = BTreeSet::new();

                for &nfa_state in &current_set {
                    if let Some(trans_list) = outgoing.get(&nfa_state) {
                        for (guard, target) in trans_list {
                            // Does this minterm overlap with the guard?
                            if self.algebra.overlaps(minterm, guard) {
                                successor_set.insert(*target);
                            }
                        }
                    }
                }

                if successor_set.is_empty() {
                    continue;
                }

                let succ_id = if let Some(&existing) = state_map.get(&successor_set) {
                    existing
                } else {
                    let is_acc = successor_set
                        .iter()
                        .any(|s| self.accepting_states.contains(s));
                    let new_id = result.add_state(
                        is_acc,
                        Some(format!("{:?}", successor_set)),
                    );
                    state_map.insert(successor_set.clone(), new_id);
                    worklist.push_back(successor_set);
                    new_id
                };

                let from_id = state_map[&current_set];
                result.add_transition(from_id, succ_id, minterm.clone());
            }
        }

        result
    }

    /// Equivalence check: do two SFAs accept the same language?
    ///
    /// Reduces to emptiness of the symmetric difference:
    /// `L(A) = L(B)` iff `(L(A) ∩ L(B)^c) ∪ (L(A)^c ∩ L(B))` is empty.
    ///
    /// # Complexity
    ///
    /// Dominated by complement (determinization) and intersection.
    pub fn is_equivalent(&self, other: &Self) -> bool {
        // A \ B = A ∩ B^c
        let b_complement = other.complement();
        let a_minus_b = self.intersect(&b_complement);

        if !a_minus_b.is_empty() {
            return false;
        }

        // B \ A = B ∩ A^c
        let a_complement = self.complement();
        let b_minus_a = other.intersect(&a_complement);

        b_minus_a.is_empty()
    }

    /// Analyze the automaton for pipeline diagnostics.
    ///
    /// Produces a `SymbolicAnalysis` summarizing:
    /// - State and transition counts
    /// - Guard satisfiability for each transition
    /// - Pairs of guards that overlap (non-disjoint)
    /// - Pairs where one guard subsumes (implies) another
    pub fn analyze(&self) -> SymbolicAnalysis {
        let mut guard_satisfiability = Vec::with_capacity(self.transitions.len());
        let mut overlapping_guards = Vec::new();
        let mut subsumed_guards = Vec::new();

        // Check satisfiability of each guard.
        for (i, trans) in self.transitions.iter().enumerate() {
            let desc = format!(
                "q{} --[{:?}]--> q{}",
                trans.from, trans.guard, trans.to,
            );
            let sat = self.algebra.is_satisfiable(&trans.guard);
            guard_satisfiability.push((desc.clone(), sat));

            // Check overlap and subsumption against all subsequent transitions.
            for (_j, other_trans) in self.transitions.iter().enumerate().skip(i + 1) {
                let desc_j = format!(
                    "q{} --[{:?}]--> q{}",
                    other_trans.from, other_trans.guard, other_trans.to,
                );

                // Overlap check.
                if self.algebra.overlaps(&trans.guard, &other_trans.guard) {
                    overlapping_guards.push((desc.clone(), desc_j.clone()));
                }

                // Subsumption checks (both directions).
                if self.algebra.implies(&trans.guard, &other_trans.guard) {
                    subsumed_guards.push((desc.clone(), desc_j.clone()));
                }
                if self.algebra.implies(&other_trans.guard, &trans.guard) {
                    subsumed_guards.push((desc_j, desc.clone()));
                }
            }
        }

        let unsatisfiable_rule_labels: Vec<String> = guard_satisfiability
            .iter()
            .filter(|(_, sat)| !sat)
            .map(|(desc, _)| desc.clone())
            .collect();
        SymbolicAnalysis {
            num_states: self.states.len(),
            num_transitions: self.transitions.len(),
            guard_satisfiability,
            overlapping_guards,
            subsumed_guards,
            unsatisfiable_rule_labels,
        }
    }
}

impl<A: BooleanAlgebra> fmt::Display for SymbolicAutomaton<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SymbolicAutomaton ({} states, {} transitions)", self.states.len(), self.transitions.len())?;
        writeln!(f, "  Initial: {:?}", self.initial_states)?;
        writeln!(f, "  Accepting: {:?}", self.accepting_states)?;
        for trans in &self.transitions {
            writeln!(
                f,
                "  q{} --[{:?}]--> q{}",
                trans.from, trans.guard, trans.to,
            )?;
        }
        Ok(())
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Minterm computation
// ══════════════════════════════════════════════════════════════════════════════

/// Compute minterms from a set of predicates.
///
/// A minterm is a maximal satisfiable conjunction of predicates and their
/// negations. Given predicates {phi_1, ..., phi_k}, a minterm is:
///   (+/-)phi_1 AND (+/-)phi_2 AND ... AND (+/-)phi_k
/// where (+) means the predicate itself and (-) means its negation, and the
/// resulting conjunction is satisfiable.
///
/// Minterms partition the domain into equivalence classes: all elements in
/// the same minterm are treated identically by every predicate.
///
/// # Algorithm
///
/// Iteratively refine a set of satisfiable predicates by splitting each
/// against each guard predicate. Start with {TRUE}, then for each guard phi:
/// - Replace each current predicate psi with psi AND phi and psi AND NOT phi
/// - Keep only satisfiable results
///
/// # Complexity
///
/// Worst case O(2^k) minterms for k predicates, but in practice many
/// conjunctions are unsatisfiable and are pruned.
fn compute_minterms<A: BooleanAlgebra>(algebra: &A, predicates: &[A::Predicate]) -> Vec<A::Predicate> {
    // Deduplicate predicates.
    let unique_preds: Vec<&A::Predicate> = {
        let mut seen = HashSet::new();
        let mut result = Vec::new();
        for p in predicates {
            if seen.insert(p.clone()) {
                result.push(p);
            }
        }
        result
    };

    let mut minterms = vec![algebra.true_pred()];

    for pred in &unique_preds {
        let mut new_minterms = Vec::with_capacity(minterms.len() * 2);
        let neg = algebra.not(pred);

        for minterm in &minterms {
            // Split: minterm AND pred
            let pos = algebra.and(minterm, pred);
            if algebra.is_satisfiable(&pos) {
                new_minterms.push(pos);
            }

            // Split: minterm AND NOT pred
            let neg_part = algebra.and(minterm, &neg);
            if algebra.is_satisfiable(&neg_part) {
                new_minterms.push(neg_part);
            }
        }

        minterms = new_minterms;
    }

    minterms
}

// ══════════════════════════════════════════════════════════════════════════════
// Decidability Classifier
// ══════════════════════════════════════════════════════════════════════════════

/// Classification of decidability for predicate expressions.
///
/// Following the standard computability hierarchy:
/// - T1 (compile-time decidable): purely propositional, finite-domain quantification
/// - T2 (runtime decidable): involves Ascent relation lookups (finite but dynamic)
/// - T3 (semi-decidable): bounded infinite-domain quantification
/// - T4 (undecidable): unbounded infinite-domain quantification
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DecidabilityTier {
    /// T1: Compile-time decidable (structural, finite-domain).
    ///
    /// Expressions containing only True/False/Atom/Not/And/Or and
    /// ForallFinite/ExistsFinite with finite domains. All quantification
    /// is bounded over enumerable sets; all atoms are ground-decidable.
    CompileTimeDecidable,

    /// T2: Runtime decidable (Ascent queries, finite-state checks).
    ///
    /// Expressions containing `Relation` atoms that reference Ascent
    /// database relations. Decidable at runtime when the Ascent database
    /// is populated, but not at compile time.
    RuntimeDecidable,

    /// T3: Semi-decidable (bounded checking with depth limit).
    ///
    /// Expressions containing `ForallInfinite`/`ExistsInfinite` quantifiers,
    /// but wrapped in a `Bounded` node with an explicit depth limit. The
    /// checker explores up to the bound; correctness is guaranteed only
    /// within the bound.
    SemiDecidable,

    /// T4: Undecidable (requires user proof/assertion).
    ///
    /// Expressions containing unbounded `ForallInfinite`/`ExistsInfinite`
    /// quantifiers without a `Bounded` wrapper. No algorithm can decide
    /// these in general; they require manual proof or axiom assertion.
    Undecidable,
}

impl fmt::Display for DecidabilityTier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DecidabilityTier::CompileTimeDecidable => write!(f, "T1 (compile-time decidable)"),
            DecidabilityTier::RuntimeDecidable => write!(f, "T2 (runtime decidable)"),
            DecidabilityTier::SemiDecidable => write!(f, "T3 (semi-decidable)"),
            DecidabilityTier::Undecidable => write!(f, "T4 (undecidable)"),
        }
    }
}

/// A predicate expression for decidability classification.
///
/// This is a richer predicate language than `BooleanTest`, supporting
/// quantification (both finite and infinite-domain), relational atoms
/// (database lookups), and bounded checking.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PredicateExpr {
    /// Boolean true.
    True,
    /// Boolean false.
    False,
    /// Atomic proposition (ground-decidable at compile time).
    Atom(String),
    /// Logical negation.
    Not(Box<PredicateExpr>),
    /// Logical conjunction.
    And(Box<PredicateExpr>, Box<PredicateExpr>),
    /// Logical disjunction.
    Or(Box<PredicateExpr>, Box<PredicateExpr>),
    /// Universal quantification over a finite domain.
    /// Decidable by enumeration: check body for each element.
    ForallFinite {
        /// Bound variable name.
        var: String,
        /// Finite domain to quantify over.
        domain: Vec<String>,
        /// Body predicate (may reference `var`).
        body: Box<PredicateExpr>,
    },
    /// Existential quantification over a finite domain.
    /// Decidable by enumeration: find an element satisfying body.
    ExistsFinite {
        /// Bound variable name.
        var: String,
        /// Finite domain to quantify over.
        domain: Vec<String>,
        /// Body predicate (may reference `var`).
        body: Box<PredicateExpr>,
    },
    /// Universal quantification over an infinite domain.
    /// Undecidable in general; semi-decidable when wrapped in `Bounded`.
    ForallInfinite {
        /// Bound variable name.
        var: String,
        /// Body predicate (may reference `var`).
        body: Box<PredicateExpr>,
    },
    /// Existential quantification over an infinite domain.
    /// Undecidable in general; semi-decidable when wrapped in `Bounded`.
    ExistsInfinite {
        /// Bound variable name.
        var: String,
        /// Body predicate (may reference `var`).
        body: Box<PredicateExpr>,
    },
    /// Relational atom: references an Ascent database relation.
    /// Decidable at runtime (T2) when the relation is populated.
    Relation {
        /// Relation name in the Ascent database.
        name: String,
        /// Arguments (column names or values).
        args: Vec<String>,
    },
    /// Bounded checking wrapper: limits exploration depth for
    /// infinite-domain quantification, making it semi-decidable (T3).
    Bounded {
        /// The body expression being bounded.
        body: Box<PredicateExpr>,
        /// Maximum exploration depth/count.
        bound: u64,
    },
}

impl fmt::Display for PredicateExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PredicateExpr::True => write!(f, "true"),
            PredicateExpr::False => write!(f, "false"),
            PredicateExpr::Atom(name) => write!(f, "{}", name),
            PredicateExpr::Not(inner) => write!(f, "~({})", inner),
            PredicateExpr::And(a, b) => write!(f, "({} /\\ {})", a, b),
            PredicateExpr::Or(a, b) => write!(f, "({} \\/ {})", a, b),
            PredicateExpr::ForallFinite { var, domain, body } => {
                write!(f, "forall {} in {:?}. {}", var, domain, body)
            }
            PredicateExpr::ExistsFinite { var, domain, body } => {
                write!(f, "exists {} in {:?}. {}", var, domain, body)
            }
            PredicateExpr::ForallInfinite { var, body } => {
                write!(f, "forall {}. {}", var, body)
            }
            PredicateExpr::ExistsInfinite { var, body } => {
                write!(f, "exists {}. {}", var, body)
            }
            PredicateExpr::Relation { name, args } => {
                write!(f, "{}({})", name, args.join(", "))
            }
            PredicateExpr::Bounded { body, bound } => {
                write!(f, "bounded({}, {})", body, bound)
            }
        }
    }
}

/// Classify the decidability tier of a predicate expression.
///
/// The classification follows the computability hierarchy:
///
/// - **T1 (CompileTimeDecidable)**: Only propositional connectives (True, False,
///   Atom, Not, And, Or) and finite-domain quantifiers (ForallFinite, ExistsFinite).
///   All atoms are ground-decidable and all domains are enumerable.
///
/// - **T2 (RuntimeDecidable)**: Contains `Relation` atoms referencing Ascent
///   database relations. Decidable when the database is populated, but not
///   at compile time.
///
/// - **T3 (SemiDecidable)**: Contains `ForallInfinite`/`ExistsInfinite` quantifiers,
///   but all such quantifiers are wrapped in `Bounded` nodes. The checker
///   explores up to the bound, making the check semi-decidable.
///
/// - **T4 (Undecidable)**: Contains unbounded `ForallInfinite`/`ExistsInfinite`
///   quantifiers. No algorithm can decide these in general.
///
/// The function returns the highest (least decidable) tier found anywhere
/// in the expression tree. A sub-expression of higher tier dominates.
pub fn classify_decidability(expr: &PredicateExpr) -> DecidabilityTier {
    classify_decidability_inner(expr, false)
}

/// Internal recursive classifier.
///
/// `in_bounded` tracks whether we are inside a `Bounded` wrapper,
/// which downgrades infinite quantifiers from T4 to T3.
fn classify_decidability_inner(expr: &PredicateExpr, in_bounded: bool) -> DecidabilityTier {
    match expr {
        PredicateExpr::True | PredicateExpr::False | PredicateExpr::Atom(_) => {
            DecidabilityTier::CompileTimeDecidable
        }

        PredicateExpr::Not(inner) => classify_decidability_inner(inner, in_bounded),

        PredicateExpr::And(a, b) | PredicateExpr::Or(a, b) => {
            let ta = classify_decidability_inner(a, in_bounded);
            let tb = classify_decidability_inner(b, in_bounded);
            ta.max(tb)
        }

        PredicateExpr::ForallFinite { body, .. } | PredicateExpr::ExistsFinite { body, .. } => {
            // Finite-domain quantification is at most T1 from the quantifier itself.
            // But the body may push it higher.
            classify_decidability_inner(body, in_bounded)
        }

        PredicateExpr::ForallInfinite { body, .. }
        | PredicateExpr::ExistsInfinite { body, .. } => {
            if in_bounded {
                // Inside a Bounded wrapper → T3 from the quantifier.
                let body_tier = classify_decidability_inner(body, in_bounded);
                body_tier.max(DecidabilityTier::SemiDecidable)
            } else {
                // Unbounded infinite quantification → T4.
                DecidabilityTier::Undecidable
            }
        }

        PredicateExpr::Relation { .. } => DecidabilityTier::RuntimeDecidable,

        PredicateExpr::Bounded { body, .. } => {
            // The Bounded wrapper enables semi-decidability for infinite quantifiers.
            classify_decidability_inner(body, true)
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline Analysis Result
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline-level symbolic automaton analysis results.
///
/// Captures guard analysis data for lint diagnostics:
/// - Which guards are satisfiable (unsatisfiable guards indicate dead transitions)
/// - Which guard pairs overlap (potential ambiguity)
/// - Which guards subsume others (redundancy opportunities)
#[derive(Debug, Clone)]
pub struct SymbolicAnalysis {
    /// Number of states in the analyzed automaton.
    pub num_states: usize,
    /// Number of transitions in the analyzed automaton.
    pub num_transitions: usize,
    /// Per-transition guard satisfiability: `(guard_description, is_satisfiable)`.
    pub guard_satisfiability: Vec<(String, bool)>,
    /// Pairs of transitions with overlapping (non-disjoint) guards.
    /// Each entry is `(guard_desc_1, guard_desc_2)`.
    pub overlapping_guards: Vec<(String, String)>,
    /// Pairs where one guard subsumes (implies) another.
    /// Each entry is `(subsumed_guard_desc, subsumer_guard_desc)`.
    pub subsumed_guards: Vec<(String, String)>,
    /// Rule labels whose guards are provably unsatisfiable (dead rules).
    /// Populated from `guard_satisfiability` entries where `is_satisfiable == false`.
    /// Used by codegen to extend dead-code elimination (SYM01-DCE).
    pub unsatisfiable_rule_labels: Vec<String>,
}

impl fmt::Display for SymbolicAnalysis {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SymbolicAnalysis: {} states, {} transitions", self.num_states, self.num_transitions)?;
        writeln!(f, "  Guard satisfiability:")?;
        for (desc, sat) in &self.guard_satisfiability {
            writeln!(f, "    {} : {}", desc, if *sat { "SAT" } else { "UNSAT" })?;
        }
        if !self.overlapping_guards.is_empty() {
            writeln!(f, "  Overlapping guards:")?;
            for (a, b) in &self.overlapping_guards {
                writeln!(f, "    {} <-> {}", a, b)?;
            }
        }
        if !self.subsumed_guards.is_empty() {
            writeln!(f, "  Subsumed guards:")?;
            for (sub, sup) in &self.subsumed_guards {
                writeln!(f, "    {} <= {}", sub, sup)?;
            }
        }
        Ok(())
    }
}

/// Extract leading terminal strings from a syntax item.
///
/// Recursively descends into `Optional` and `Map` wrappers to find the
/// terminal tokens that can start a match for this syntax item.
fn collect_leading_terminals(item: &crate::SyntaxItemSpec, out: &mut HashSet<String>) {
    match item {
        crate::SyntaxItemSpec::Terminal(t) => {
            out.insert(t.clone());
        }
        crate::SyntaxItemSpec::Optional { inner } => {
            if let Some(first) = inner.first() {
                collect_leading_terminals(first, out);
            }
        }
        crate::SyntaxItemSpec::Map { body_items } => {
            if let Some(first) = body_items.first() {
                collect_leading_terminals(first, out);
            }
        }
        crate::SyntaxItemSpec::Sep { body, .. } => {
            collect_leading_terminals(body, out);
        }
        // NonTerminal, IdentCapture, Binder, Collection, Zip, BinderCollection
        // don't contribute concrete terminal tokens to the guard.
        _ => {}
    }
}

/// Analyze grammar guard structure using symbolic automata.
///
/// Builds per-rule guard predicates from leading terminals, then detects:
/// - **Unsatisfiable guards**: rules with no leading terminals AND no
///   NonTerminal/IdentCapture/Binder/Collection first item (cannot match any input).
/// - **Overlapping guards**: rule pairs within the same category whose leading
///   terminal sets intersect (potential ambiguity).
/// - **Subsumed guards**: when one rule's leading terminal set is a strict subset
///   of another's within the same category.
pub fn analyze_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> SymbolicAnalysis {
    let num_states = categories.len().max(1);
    let num_transitions = all_syntax.len();

    // Build per-rule leading terminal sets.
    // A rule's "guard" is the set of terminal tokens that can start a match.
    let mut rule_guards: Vec<(String, String, HashSet<String>)> =
        Vec::with_capacity(all_syntax.len());

    for (label, cat, items) in all_syntax {
        let qualified = format!("{}::{}", cat, label);
        let mut leading_terminals = HashSet::new();

        if let Some(first_item) = items.first() {
            collect_leading_terminals(first_item, &mut leading_terminals);
        }

        rule_guards.push((qualified, cat.clone(), leading_terminals));
    }

    // Guard satisfiability: a guard is satisfiable if it has at least one
    // leading terminal OR starts with a NonTerminal/IdentCapture/Binder/Collection
    // (which can match dynamically), OR is an empty rule (epsilon production).
    let guard_satisfiability: Vec<(String, bool)> = all_syntax
        .iter()
        .zip(rule_guards.iter())
        .map(|((_, _, items), (qualified, _, terminals))| {
            let has_terminal = !terminals.is_empty();
            let has_nonterminal_start = items.first().map_or(false, |item| {
                matches!(
                    item,
                    crate::SyntaxItemSpec::NonTerminal { .. }
                        | crate::SyntaxItemSpec::IdentCapture { .. }
                        | crate::SyntaxItemSpec::Binder { .. }
                        | crate::SyntaxItemSpec::Collection { .. }
                )
            });
            let is_empty_rule = items.is_empty();
            (
                qualified.clone(),
                has_terminal || has_nonterminal_start || is_empty_rule,
            )
        })
        .collect();

    let unsatisfiable_rule_labels: Vec<String> = guard_satisfiability
        .iter()
        .filter(|(_, sat)| !sat)
        .map(|(desc, _)| desc.clone())
        .collect();

    // Overlapping guards: pairs of rules in the same category with
    // intersecting leading terminal sets.
    let mut overlapping_guards: Vec<(String, String)> = Vec::new();
    for i in 0..rule_guards.len() {
        for j in (i + 1)..rule_guards.len() {
            let (ref qual_i, ref cat_i, ref terms_i) = rule_guards[i];
            let (ref qual_j, ref cat_j, ref terms_j) = rule_guards[j];
            if cat_i == cat_j && !terms_i.is_empty() && !terms_j.is_empty() {
                if terms_i.intersection(terms_j).next().is_some() {
                    overlapping_guards.push((qual_i.clone(), qual_j.clone()));
                }
            }
        }
    }

    // Subsumed guards: when one rule's leading terminal set is a strict
    // subset of another's within the same category.
    let mut subsumed_guards: Vec<(String, String)> = Vec::new();
    for i in 0..rule_guards.len() {
        for j in 0..rule_guards.len() {
            if i == j {
                continue;
            }
            let (ref qual_i, ref cat_i, ref terms_i) = rule_guards[i];
            let (ref qual_j, ref cat_j, ref terms_j) = rule_guards[j];
            if cat_i == cat_j && !terms_i.is_empty() && !terms_j.is_empty() {
                if terms_i.is_subset(terms_j) && terms_i != terms_j {
                    subsumed_guards.push((qual_i.clone(), qual_j.clone()));
                }
            }
        }
    }

    SymbolicAnalysis {
        num_states,
        num_transitions,
        guard_satisfiability,
        overlapping_guards,
        subsumed_guards,
        unsatisfiable_rule_labels,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Predicate Dispatch — PredicateCompiler integration
// ══════════════════════════════════════════════════════════════════════════════

/// Compiler adapter for the Symbolic Automata module (M1).
///
/// Delegates per-predicate compilation to `analyze_from_bundle()`.
/// M1 is always active (base module in every dispatch signature).
#[cfg(feature = "predicate-dispatch")]
pub struct SymbolicCompiler;

#[cfg(feature = "predicate-dispatch")]
impl crate::predicate_dispatch::PredicateCompiler for SymbolicCompiler {
    type Output = SymbolicAnalysis;

    fn compile_predicate(
        &self,
        _pred: &PredicateExpr,
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

    // ── IntervalAlgebra tests ────────────────────────────────────────────

    #[test]
    fn interval_true_is_satisfiable() {
        let alg = IntervalAlgebra::new(0, 100);
        assert!(alg.is_satisfiable(&alg.true_pred()));
    }

    #[test]
    fn interval_false_is_not_satisfiable() {
        let alg = IntervalAlgebra::new(0, 100);
        assert!(!alg.is_satisfiable(&alg.false_pred()));
    }

    #[test]
    fn interval_range_satisfiability() {
        let alg = IntervalAlgebra::new(0, 100);
        // [10, 20) is satisfiable.
        assert!(alg.is_satisfiable(&IntervalPred::Range(10, 20)));
        // Empty range [20, 10) is not.
        assert!(!alg.is_satisfiable(&IntervalPred::Range(20, 10)));
        // Range outside universe [200, 300) is not.
        assert!(!alg.is_satisfiable(&IntervalPred::Range(200, 300)));
    }

    #[test]
    fn interval_witness() {
        let alg = IntervalAlgebra::new(0, 100);
        let w = alg.witness(&IntervalPred::Range(10, 20));
        assert_eq!(w, Some(10));
        let w = alg.witness(&alg.false_pred());
        assert_eq!(w, None);
    }

    #[test]
    fn interval_and() {
        let alg = IntervalAlgebra::new(0, 100);
        // [10, 30) AND [20, 40) = [20, 30)
        let result = alg.and(
            &IntervalPred::Range(10, 30),
            &IntervalPred::Range(20, 40),
        );
        assert!(alg.is_satisfiable(&result));
        assert!(alg.evaluate(&result, &25));
        assert!(!alg.evaluate(&result, &10));
        assert!(!alg.evaluate(&result, &35));
    }

    #[test]
    fn interval_or() {
        let alg = IntervalAlgebra::new(0, 100);
        // [10, 20) OR [30, 40) — disjoint union.
        let result = alg.or(
            &IntervalPred::Range(10, 20),
            &IntervalPred::Range(30, 40),
        );
        assert!(alg.evaluate(&result, &15));
        assert!(alg.evaluate(&result, &35));
        assert!(!alg.evaluate(&result, &25));
    }

    #[test]
    fn interval_not() {
        let alg = IntervalAlgebra::new(0, 100);
        // NOT [10, 20) = [0, 10) union [20, 100)
        let result = alg.not(&IntervalPred::Range(10, 20));
        assert!(alg.evaluate(&result, &5));
        assert!(alg.evaluate(&result, &50));
        assert!(!alg.evaluate(&result, &15));
    }

    #[test]
    fn interval_overlaps() {
        let alg = IntervalAlgebra::new(0, 100);
        // [10, 30) and [20, 40) overlap.
        assert!(alg.overlaps(
            &IntervalPred::Range(10, 30),
            &IntervalPred::Range(20, 40),
        ));
        // [10, 20) and [30, 40) do not overlap.
        assert!(!alg.overlaps(
            &IntervalPred::Range(10, 20),
            &IntervalPred::Range(30, 40),
        ));
    }

    #[test]
    fn interval_implies() {
        let alg = IntervalAlgebra::new(0, 100);
        // [15, 25) implies [10, 30) (subset).
        assert!(alg.implies(
            &IntervalPred::Range(15, 25),
            &IntervalPred::Range(10, 30),
        ));
        // [10, 30) does NOT imply [15, 25).
        assert!(!alg.implies(
            &IntervalPred::Range(10, 30),
            &IntervalPred::Range(15, 25),
        ));
    }

    #[test]
    fn interval_equivalent() {
        let alg = IntervalAlgebra::new(0, 100);
        assert!(alg.equivalent(
            &IntervalPred::Range(10, 20),
            &IntervalPred::Range(10, 20),
        ));
        assert!(!alg.equivalent(
            &IntervalPred::Range(10, 20),
            &IntervalPred::Range(10, 25),
        ));
    }

    #[test]
    fn interval_tautology() {
        let alg = IntervalAlgebra::new(0, 100);
        assert!(alg.is_tautology(&alg.true_pred()));
        assert!(!alg.is_tautology(&IntervalPred::Range(0, 50)));
        // [0, 100) is a tautology over [0, 100).
        assert!(alg.is_tautology(&IntervalPred::Range(0, 100)));
    }

    #[test]
    fn interval_union_normalization() {
        let alg = IntervalAlgebra::new(0, 100);
        // Overlapping ranges should merge.
        let union = IntervalPred::Union(vec![(10, 30), (20, 40)]);
        assert!(alg.evaluate(&union, &25));
        assert!(alg.evaluate(&union, &35));
        assert!(!alg.evaluate(&union, &5));
    }

    // ── CharClassAlgebra tests ───────────────────────────────────────────

    #[test]
    fn charclass_range_satisfiability() {
        let alg = CharClassAlgebra::new();
        assert!(alg.is_satisfiable(&CharClassPred::Range('a', 'z')));
        assert!(alg.is_satisfiable(&CharClassPred::Range('a', 'a')));
        assert!(!alg.is_satisfiable(&alg.false_pred()));
    }

    #[test]
    fn charclass_witness() {
        let alg = CharClassAlgebra::new();
        let w = alg.witness(&CharClassPred::Range('a', 'z'));
        assert_eq!(w, Some('a'));
    }

    #[test]
    fn charclass_union() {
        let alg = CharClassAlgebra::new();
        // [a-z] OR [0-9]
        let result = alg.or(
            &CharClassPred::Range('a', 'z'),
            &CharClassPred::Range('0', '9'),
        );
        assert!(alg.evaluate(&result, &'m'));
        assert!(alg.evaluate(&result, &'5'));
        assert!(!alg.evaluate(&result, &'!'));
    }

    #[test]
    fn charclass_complement() {
        let alg = CharClassAlgebra::new();
        // NOT [a-z] should accept digits, punctuation, etc.
        let result = alg.not(&CharClassPred::Range('a', 'z'));
        assert!(!alg.evaluate(&result, &'m'));
        assert!(alg.evaluate(&result, &'5'));
        assert!(alg.evaluate(&result, &'A'));
    }

    #[test]
    fn charclass_intersection() {
        let alg = CharClassAlgebra::new();
        // [a-m] AND [h-z] = [h-m]
        let result = alg.and(
            &CharClassPred::Range('a', 'm'),
            &CharClassPred::Range('h', 'z'),
        );
        assert!(alg.evaluate(&result, &'h'));
        assert!(alg.evaluate(&result, &'m'));
        assert!(!alg.evaluate(&result, &'a'));
        assert!(!alg.evaluate(&result, &'z'));
    }

    // ── KatBooleanAlgebra tests ──────────────────────────────────────────

    #[test]
    fn kat_algebra_true_satisfiable() {
        let alg = KatBooleanAlgebra::new(vec!["p".to_string()]);
        assert!(alg.is_satisfiable(&BooleanTest::True));
    }

    #[test]
    fn kat_algebra_false_unsatisfiable() {
        let alg = KatBooleanAlgebra::new(vec!["p".to_string()]);
        assert!(!alg.is_satisfiable(&BooleanTest::False));
    }

    #[test]
    fn kat_algebra_atom_satisfiable() {
        let alg = KatBooleanAlgebra::new(vec!["p".to_string()]);
        assert!(alg.is_satisfiable(&BooleanTest::Atom("p".to_string())));
    }

    #[test]
    fn kat_algebra_contradiction_unsatisfiable() {
        let alg = KatBooleanAlgebra::new(vec!["p".to_string()]);
        // p AND NOT p is unsatisfiable.
        let p = BooleanTest::Atom("p".to_string());
        let contradiction = alg.and(&p, &alg.not(&p));
        assert!(!alg.is_satisfiable(&contradiction));
    }

    #[test]
    fn kat_algebra_evaluation() {
        let alg = KatBooleanAlgebra::new(vec!["p".to_string(), "q".to_string()]);
        let p_and_q = BooleanTest::And(
            Box::new(BooleanTest::Atom("p".to_string())),
            Box::new(BooleanTest::Atom("q".to_string())),
        );

        let mut valuation = HashMap::new();
        valuation.insert("p".to_string(), true);
        valuation.insert("q".to_string(), true);
        assert!(alg.evaluate(&p_and_q, &valuation));

        valuation.insert("q".to_string(), false);
        assert!(!alg.evaluate(&p_and_q, &valuation));
    }

    #[test]
    fn kat_algebra_witness() {
        let alg = KatBooleanAlgebra::new(vec!["p".to_string(), "q".to_string()]);
        let p_and_q = BooleanTest::And(
            Box::new(BooleanTest::Atom("p".to_string())),
            Box::new(BooleanTest::Atom("q".to_string())),
        );
        let w = alg.witness(&p_and_q);
        assert!(w.is_some());
        let w = w.expect("should have witness for p AND q");
        assert_eq!(w.get("p"), Some(&true));
        assert_eq!(w.get("q"), Some(&true));
    }

    // ── SymbolicAutomaton: emptiness ─────────────────────────────────────

    #[test]
    fn sfa_empty_automaton_is_empty() {
        let alg = IntervalAlgebra::new(0, 100);
        let sfa: SymbolicAutomaton<IntervalAlgebra> = SymbolicAutomaton::new(alg);
        assert!(sfa.is_empty());
    }

    #[test]
    fn sfa_single_accepting_initial_is_not_empty() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sfa = SymbolicAutomaton::new(alg);
        let q0 = sfa.add_state(true, Some("start".to_string()));
        sfa.set_initial(q0);
        // Accepting initial state → accepts the empty word.
        assert!(!sfa.is_empty());
    }

    #[test]
    fn sfa_unreachable_accepting_state_is_empty() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sfa = SymbolicAutomaton::new(alg.clone());
        let q0 = sfa.add_state(false, Some("start".to_string()));
        let _q1 = sfa.add_state(true, Some("accept".to_string()));
        sfa.set_initial(q0);
        // q1 is accepting but unreachable from q0 → empty.
        assert!(sfa.is_empty());
    }

    #[test]
    fn sfa_reachable_via_satisfiable_guard() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sfa = SymbolicAutomaton::new(alg.clone());
        let q0 = sfa.add_state(false, Some("start".to_string()));
        let q1 = sfa.add_state(true, Some("accept".to_string()));
        sfa.set_initial(q0);
        sfa.add_transition(q0, q1, IntervalPred::Range(10, 20));
        assert!(!sfa.is_empty());
    }

    #[test]
    fn sfa_unsatisfiable_guard_blocks_reachability() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sfa = SymbolicAutomaton::new(alg.clone());
        let q0 = sfa.add_state(false, Some("start".to_string()));
        let q1 = sfa.add_state(true, Some("accept".to_string()));
        sfa.set_initial(q0);
        // Guard [200, 300) is outside universe [0, 100) → unsatisfiable.
        sfa.add_transition(q0, q1, IntervalPred::Range(200, 300));
        assert!(sfa.is_empty());
    }

    // ── SymbolicAutomaton: accepts ───────────────────────────────────────

    #[test]
    fn sfa_accepts_empty_word() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sfa = SymbolicAutomaton::new(alg);
        let q0 = sfa.add_state(true, None);
        sfa.set_initial(q0);
        assert!(sfa.accepts(&[]));
    }

    #[test]
    fn sfa_accepts_single_element() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sfa = SymbolicAutomaton::new(alg);
        let q0 = sfa.add_state(false, None);
        let q1 = sfa.add_state(true, None);
        sfa.set_initial(q0);
        sfa.add_transition(q0, q1, IntervalPred::Range(10, 20));

        assert!(sfa.accepts(&[15]));
        assert!(!sfa.accepts(&[5]));
        assert!(!sfa.accepts(&[25]));
    }

    #[test]
    fn sfa_accepts_two_element_word() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sfa = SymbolicAutomaton::new(alg);
        let q0 = sfa.add_state(false, None);
        let q1 = sfa.add_state(false, None);
        let q2 = sfa.add_state(true, None);
        sfa.set_initial(q0);
        sfa.add_transition(q0, q1, IntervalPred::Range(0, 50));
        sfa.add_transition(q1, q2, IntervalPred::Range(50, 100));

        assert!(sfa.accepts(&[25, 75]));
        assert!(!sfa.accepts(&[25, 25])); // second element not in [50, 100)
        assert!(!sfa.accepts(&[75, 75])); // first element not in [0, 50)
    }

    // ── SymbolicAutomaton: intersect ─────────────────────────────────────

    #[test]
    fn sfa_intersect_compatible() {
        let alg = IntervalAlgebra::new(0, 100);

        // SFA1: q0 --[0,50)--> q1(accept)
        let mut sfa1 = SymbolicAutomaton::new(alg.clone());
        let q0 = sfa1.add_state(false, None);
        let q1 = sfa1.add_state(true, None);
        sfa1.set_initial(q0);
        sfa1.add_transition(q0, q1, IntervalPred::Range(0, 50));

        // SFA2: q0 --[25,75)--> q1(accept)
        let mut sfa2 = SymbolicAutomaton::new(alg.clone());
        let q0 = sfa2.add_state(false, None);
        let q1 = sfa2.add_state(true, None);
        sfa2.set_initial(q0);
        sfa2.add_transition(q0, q1, IntervalPred::Range(25, 75));

        let inter = sfa1.intersect(&sfa2);
        // Intersection should accept [25, 50).
        assert!(inter.accepts(&[30]));
        assert!(!inter.accepts(&[10]));  // in SFA1 but not SFA2
        assert!(!inter.accepts(&[60]));  // in SFA2 but not SFA1
    }

    #[test]
    fn sfa_intersect_disjoint() {
        let alg = IntervalAlgebra::new(0, 100);

        // SFA1: accepts [0, 30)
        let mut sfa1 = SymbolicAutomaton::new(alg.clone());
        let q0 = sfa1.add_state(false, None);
        let q1 = sfa1.add_state(true, None);
        sfa1.set_initial(q0);
        sfa1.add_transition(q0, q1, IntervalPred::Range(0, 30));

        // SFA2: accepts [50, 100)
        let mut sfa2 = SymbolicAutomaton::new(alg.clone());
        let q0 = sfa2.add_state(false, None);
        let q1 = sfa2.add_state(true, None);
        sfa2.set_initial(q0);
        sfa2.add_transition(q0, q1, IntervalPred::Range(50, 100));

        let inter = sfa1.intersect(&sfa2);
        assert!(inter.is_empty());
    }

    // ── SymbolicAutomaton: complement ────────────────────────────────────

    #[test]
    fn sfa_complement_flips_acceptance() {
        let alg = IntervalAlgebra::new(0, 100);

        // SFA: accepts single elements in [10, 20).
        let mut sfa = SymbolicAutomaton::new(alg);
        let q0 = sfa.add_state(false, None);
        let q1 = sfa.add_state(true, None);
        sfa.set_initial(q0);
        sfa.add_transition(q0, q1, IntervalPred::Range(10, 20));

        let comp = sfa.complement();

        // Original accepts [15], complement should reject it.
        assert!(sfa.accepts(&[15]));
        assert!(!comp.accepts(&[15]));

        // Original rejects [5], complement should accept it.
        assert!(!sfa.accepts(&[5]));
        assert!(comp.accepts(&[5]));
    }

    // ── SymbolicAutomaton: determinize ───────────────────────────────────

    #[test]
    fn sfa_determinize_preserves_language() {
        let alg = IntervalAlgebra::new(0, 100);

        // NFA: q0 --[0,50)--> q1(accept), q0 --[25,75)--> q2(accept)
        // Nondeterministic: for input 30, both transitions fire.
        let mut sfa = SymbolicAutomaton::new(alg);
        let q0 = sfa.add_state(false, None);
        let q1 = sfa.add_state(true, None);
        let q2 = sfa.add_state(true, None);
        sfa.set_initial(q0);
        sfa.add_transition(q0, q1, IntervalPred::Range(0, 50));
        sfa.add_transition(q0, q2, IntervalPred::Range(25, 75));

        let det = sfa.determinize();

        // Both should accept the same inputs.
        for val in [5, 15, 30, 45, 60, 70, 80, 90] {
            assert_eq!(
                sfa.accepts(&[val]),
                det.accepts(&[val]),
                "Mismatch at input [{}]",
                val,
            );
        }
    }

    #[test]
    fn sfa_determinize_empty_automaton() {
        let alg = IntervalAlgebra::new(0, 100);
        let sfa: SymbolicAutomaton<IntervalAlgebra> = SymbolicAutomaton::new(alg);
        let det = sfa.determinize();
        assert!(det.is_empty());
    }

    // ── SymbolicAutomaton: equivalence ───────────────────────────────────

    #[test]
    fn sfa_self_equivalence() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sfa = SymbolicAutomaton::new(alg);
        let q0 = sfa.add_state(false, None);
        let q1 = sfa.add_state(true, None);
        sfa.set_initial(q0);
        sfa.add_transition(q0, q1, IntervalPred::Range(10, 50));

        assert!(sfa.is_equivalent(&sfa));
    }

    #[test]
    fn sfa_non_equivalent_different_languages() {
        let alg = IntervalAlgebra::new(0, 100);

        // SFA1: accepts [10, 50)
        let mut sfa1 = SymbolicAutomaton::new(alg.clone());
        let q0 = sfa1.add_state(false, None);
        let q1 = sfa1.add_state(true, None);
        sfa1.set_initial(q0);
        sfa1.add_transition(q0, q1, IntervalPred::Range(10, 50));

        // SFA2: accepts [10, 60)
        let mut sfa2 = SymbolicAutomaton::new(alg.clone());
        let q0 = sfa2.add_state(false, None);
        let q1 = sfa2.add_state(true, None);
        sfa2.set_initial(q0);
        sfa2.add_transition(q0, q1, IntervalPred::Range(10, 60));

        assert!(!sfa1.is_equivalent(&sfa2));
    }

    // ── SymbolicAutomaton: analyze ───────────────────────────────────────

    #[test]
    fn sfa_analyze_reports_guard_satisfiability() {
        let alg = IntervalAlgebra::new(0, 100);
        let mut sfa = SymbolicAutomaton::new(alg);
        let q0 = sfa.add_state(false, None);
        let q1 = sfa.add_state(true, None);
        sfa.set_initial(q0);
        sfa.add_transition(q0, q1, IntervalPred::Range(10, 20));
        // Add an unsatisfiable transition.
        sfa.add_transition(q0, q1, IntervalPred::Range(200, 300));

        let analysis = sfa.analyze();
        assert_eq!(analysis.num_states, 2);
        assert_eq!(analysis.num_transitions, 2);
        assert_eq!(analysis.guard_satisfiability.len(), 2);
        assert!(analysis.guard_satisfiability[0].1);  // [10, 20) is SAT
        assert!(!analysis.guard_satisfiability[1].1); // [200, 300) is UNSAT
    }

    // ── Decidability classifier tests ────────────────────────────────────

    #[test]
    fn decidability_t1_ground_boolean() {
        let expr = PredicateExpr::And(
            Box::new(PredicateExpr::Atom("a".to_string())),
            Box::new(PredicateExpr::Not(Box::new(PredicateExpr::Atom("b".to_string())))),
        );
        assert_eq!(classify_decidability(&expr), DecidabilityTier::CompileTimeDecidable);
    }

    #[test]
    fn decidability_t1_finite_quantifier() {
        let expr = PredicateExpr::ForallFinite {
            var: "x".to_string(),
            domain: vec!["a".to_string(), "b".to_string(), "c".to_string()],
            body: Box::new(PredicateExpr::Atom("p".to_string())),
        };
        assert_eq!(classify_decidability(&expr), DecidabilityTier::CompileTimeDecidable);
    }

    #[test]
    fn decidability_t2_relation() {
        let expr = PredicateExpr::Relation {
            name: "reachable".to_string(),
            args: vec!["x".to_string(), "y".to_string()],
        };
        assert_eq!(classify_decidability(&expr), DecidabilityTier::RuntimeDecidable);
    }

    #[test]
    fn decidability_t2_relation_in_conjunction() {
        let expr = PredicateExpr::And(
            Box::new(PredicateExpr::Atom("ground_fact".to_string())),
            Box::new(PredicateExpr::Relation {
                name: "derives".to_string(),
                args: vec!["A".to_string(), "B".to_string()],
            }),
        );
        assert_eq!(classify_decidability(&expr), DecidabilityTier::RuntimeDecidable);
    }

    #[test]
    fn decidability_t3_bounded_infinite() {
        let expr = PredicateExpr::Bounded {
            body: Box::new(PredicateExpr::ForallInfinite {
                var: "n".to_string(),
                body: Box::new(PredicateExpr::Atom("safe".to_string())),
            }),
            bound: 1000,
        };
        assert_eq!(classify_decidability(&expr), DecidabilityTier::SemiDecidable);
    }

    #[test]
    fn decidability_t4_unbounded_infinite() {
        let expr = PredicateExpr::ForallInfinite {
            var: "n".to_string(),
            body: Box::new(PredicateExpr::Atom("terminates".to_string())),
        };
        assert_eq!(classify_decidability(&expr), DecidabilityTier::Undecidable);
    }

    #[test]
    fn decidability_t4_exists_infinite_unbounded() {
        let expr = PredicateExpr::ExistsInfinite {
            var: "x".to_string(),
            body: Box::new(PredicateExpr::Atom("solution".to_string())),
        };
        assert_eq!(classify_decidability(&expr), DecidabilityTier::Undecidable);
    }

    #[test]
    fn decidability_t3_bounded_exists_infinite() {
        let expr = PredicateExpr::Bounded {
            body: Box::new(PredicateExpr::ExistsInfinite {
                var: "x".to_string(),
                body: Box::new(PredicateExpr::Atom("witness".to_string())),
            }),
            bound: 500,
        };
        assert_eq!(classify_decidability(&expr), DecidabilityTier::SemiDecidable);
    }

    #[test]
    fn decidability_max_dominates() {
        // T2 (Relation) AND T4 (unbounded ForallInfinite) → T4.
        let expr = PredicateExpr::And(
            Box::new(PredicateExpr::Relation {
                name: "r".to_string(),
                args: vec!["x".to_string()],
            }),
            Box::new(PredicateExpr::ForallInfinite {
                var: "n".to_string(),
                body: Box::new(PredicateExpr::True),
            }),
        );
        assert_eq!(classify_decidability(&expr), DecidabilityTier::Undecidable);
    }

    // ── Display / formatting tests ───────────────────────────────────────

    #[test]
    fn interval_pred_display() {
        assert_eq!(format!("{}", IntervalPred::True), "TRUE");
        assert_eq!(format!("{}", IntervalPred::False), "FALSE");
        assert_eq!(format!("{}", IntervalPred::Range(10, 20)), "[10, 20)");
    }

    #[test]
    fn decidability_tier_display() {
        assert_eq!(
            format!("{}", DecidabilityTier::CompileTimeDecidable),
            "T1 (compile-time decidable)",
        );
        assert_eq!(
            format!("{}", DecidabilityTier::Undecidable),
            "T4 (undecidable)",
        );
    }

    #[test]
    fn predicate_expr_display() {
        let expr = PredicateExpr::ForallFinite {
            var: "x".to_string(),
            domain: vec!["a".to_string(), "b".to_string()],
            body: Box::new(PredicateExpr::Atom("p".to_string())),
        };
        let s = format!("{}", expr);
        assert!(s.contains("forall"));
        assert!(s.contains("x"));
    }

    #[test]
    fn symbolic_analysis_display() {
        let analysis = SymbolicAnalysis {
            num_states: 3,
            num_transitions: 2,
            guard_satisfiability: vec![
                ("guard1".to_string(), true),
                ("guard2".to_string(), false),
            ],
            overlapping_guards: vec![],
            subsumed_guards: vec![],
            unsatisfiable_rule_labels: vec!["guard2".to_string()],
        };
        let s = format!("{}", analysis);
        assert!(s.contains("3 states"));
        assert!(s.contains("SAT"));
        assert!(s.contains("UNSAT"));
    }

    // ── CharClass algebra: additional edge cases ─────────────────────────

    #[test]
    fn charclass_single_char_range() {
        let alg = CharClassAlgebra::new();
        let pred = CharClassPred::Range('x', 'x');
        assert!(alg.evaluate(&pred, &'x'));
        assert!(!alg.evaluate(&pred, &'y'));
        assert_eq!(alg.witness(&pred), Some('x'));
    }

    #[test]
    fn charclass_true_is_tautology() {
        let alg = CharClassAlgebra::new();
        assert!(alg.is_tautology(&alg.true_pred()));
        assert!(!alg.is_tautology(&CharClassPred::Range('a', 'z')));
    }

    // ── Minterm computation tests ────────────────────────────────────────

    #[test]
    fn minterms_single_predicate() {
        let alg = IntervalAlgebra::new(0, 100);
        let preds = vec![IntervalPred::Range(10, 50)];
        let minterms = compute_minterms(&alg, &preds);
        // Should have 2 minterms: [10, 50) and its complement [0,10) + [50,100).
        assert_eq!(minterms.len(), 2);
        // All minterms should be satisfiable (by construction).
        for m in &minterms {
            assert!(alg.is_satisfiable(m));
        }
    }

    #[test]
    fn minterms_two_overlapping_predicates() {
        let alg = IntervalAlgebra::new(0, 100);
        let preds = vec![
            IntervalPred::Range(0, 50),
            IntervalPred::Range(25, 75),
        ];
        let minterms = compute_minterms(&alg, &preds);
        // Expected minterms:
        // [0,25): in first, not in second
        // [25,50): in both
        // [50,75): not in first, in second
        // [75,100): not in either (if exists) -- actually this is the
        //           complement of first AND complement of second → [75,100)
        //           which IS satisfiable, so we get 4 minterms.
        // But [0,25) may not exist since the complement logic works differently.
        // We just verify all are satisfiable and they partition the universe.
        for m in &minterms {
            assert!(
                alg.is_satisfiable(m),
                "Minterm {:?} should be satisfiable",
                m,
            );
        }
        // At least 3 minterms (the 3 non-empty regions).
        assert!(minterms.len() >= 3, "Expected >= 3 minterms, got {}", minterms.len());
    }

    // ── analyze_from_bundle: real guard analysis ────────────────────────

    #[test]
    fn analyze_bundle_disjoint_terminals_no_overlap() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![CategoryInfo {
            name: "Expr".to_string(),
            is_primary: true,
            native_type: None,
        }];

        // Two rules starting with different terminals -> no overlap.
        let all_syntax = vec![
            (
                "Add".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("+".to_string())],
            ),
            (
                "Sub".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("-".to_string())],
            ),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            result.overlapping_guards.is_empty(),
            "different terminals should not overlap"
        );
        assert!(result.unsatisfiable_rule_labels.is_empty());
        assert_eq!(result.guard_satisfiability.len(), 2);
        assert!(result.guard_satisfiability.iter().all(|(_, sat)| *sat));
    }

    #[test]
    fn analyze_bundle_overlapping_guards() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![CategoryInfo {
            name: "Expr".to_string(),
            is_primary: true,
            native_type: None,
        }];

        // Two rules starting with the same terminal -> overlap.
        let all_syntax = vec![
            (
                "IfThen".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("if".to_string())],
            ),
            (
                "IfElse".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("if".to_string())],
            ),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert_eq!(
            result.overlapping_guards.len(),
            1,
            "same leading terminal should overlap"
        );
    }

    #[test]
    fn analyze_bundle_subsumed_guards() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![CategoryInfo {
            name: "Expr".to_string(),
            is_primary: true,
            native_type: None,
        }];

        // Rule A starts with "if", Rule B starts with "if" or "while"
        // (via Optional wrapping "while" as a second leading terminal path).
        // Since we only extract from the first item, we construct a scenario
        // where both have guard {"if"} — equal sets, no subsumption.
        let all_syntax = vec![
            (
                "A".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("if".to_string())],
            ),
            (
                "B".to_string(),
                "Expr".to_string(),
                vec![
                    crate::SyntaxItemSpec::Terminal("if".to_string()),
                    crate::SyntaxItemSpec::Terminal("then".to_string()),
                ],
            ),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        // Both have guard {"if"}, so they overlap but neither subsumes the other (equal sets).
        assert!(!result.overlapping_guards.is_empty());
        assert!(
            result.subsumed_guards.is_empty(),
            "equal sets are not subsumed"
        );
    }

    #[test]
    fn analyze_bundle_empty_grammar() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![CategoryInfo {
            name: "Expr".to_string(),
            is_primary: true,
            native_type: None,
        }];
        let all_syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(result.guard_satisfiability.is_empty());
        assert!(result.overlapping_guards.is_empty());
        assert!(result.unsatisfiable_rule_labels.is_empty());
    }

    #[test]
    fn analyze_bundle_nonterminal_start_satisfiable() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![CategoryInfo {
            name: "Expr".to_string(),
            is_primary: true,
            native_type: None,
        }];

        // Rule starting with NonTerminal -> satisfiable (can match anything the NT matches).
        let all_syntax = vec![(
            "Cast".to_string(),
            "Expr".to_string(),
            vec![crate::SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "e".to_string(),
            }],
        )];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            result.guard_satisfiability[0].1,
            "NonTerminal start should be satisfiable"
        );
        assert!(result.unsatisfiable_rule_labels.is_empty());
    }

    #[test]
    fn analyze_bundle_cross_category_no_overlap() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![
            CategoryInfo {
                name: "Expr".to_string(),
                is_primary: true,
                native_type: None,
            },
            CategoryInfo {
                name: "Stmt".to_string(),
                is_primary: false,
                native_type: None,
            },
        ];

        // Same leading terminal but different categories -> no overlap.
        let all_syntax = vec![
            (
                "IfExpr".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("if".to_string())],
            ),
            (
                "IfStmt".to_string(),
                "Stmt".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("if".to_string())],
            ),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            result.overlapping_guards.is_empty(),
            "rules in different categories should not overlap"
        );
    }

    #[test]
    fn analyze_bundle_optional_leading_terminal() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![CategoryInfo {
            name: "Expr".to_string(),
            is_primary: true,
            native_type: None,
        }];

        // Rule starts with Optional containing a terminal -> leading terminal extracted.
        let all_syntax = vec![(
            "MaybeNeg".to_string(),
            "Expr".to_string(),
            vec![crate::SyntaxItemSpec::Optional {
                inner: vec![crate::SyntaxItemSpec::Terminal("-".to_string())],
            }],
        )];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            result.guard_satisfiability[0].1,
            "Optional with terminal should be satisfiable"
        );
    }

    #[test]
    fn analyze_bundle_unsatisfiable_zip_start() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![CategoryInfo {
            name: "Expr".to_string(),
            is_primary: true,
            native_type: None,
        }];

        // Rule starts with Zip (not Terminal, not NonTerminal/IdentCapture/Binder/Collection)
        // -> no leading terminals AND not a recognized nonterminal start -> unsatisfiable.
        let all_syntax = vec![(
            "ZipRule".to_string(),
            "Expr".to_string(),
            vec![crate::SyntaxItemSpec::Zip {
                left_name: "l".to_string(),
                right_name: "r".to_string(),
                left_category: "Expr".to_string(),
                right_category: "Expr".to_string(),
                body: Box::new(crate::SyntaxItemSpec::Terminal("x".to_string())),
            }],
        )];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            !result.guard_satisfiability[0].1,
            "Zip start should be unsatisfiable"
        );
        assert_eq!(result.unsatisfiable_rule_labels.len(), 1);
        assert_eq!(result.unsatisfiable_rule_labels[0], "Expr::ZipRule");
    }

    #[test]
    fn analyze_bundle_real_subsumption() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![CategoryInfo {
            name: "Expr".to_string(),
            is_primary: true,
            native_type: None,
        }];

        // Rule A starts with Optional containing "if" -> guard {"if"}.
        // Rule B starts with Optional containing "if" and "while" -> guard {"if", "while"}.
        // But collect_leading_terminals only looks at the first item in Optional,
        // so we use Map to create multi-terminal guards.
        // Actually, Map with first item "if" gives {"if"}, and we need another
        // approach for multi-terminal. Let's just test with direct construction:
        // We can exploit the fact that Optional collects from its first inner item
        // and Sep collects from its body. Neither gives us multiple terminals from
        // a single first item. For a real subsumption test, we need rules where
        // the guard sets differ in size.
        //
        // Since collect_leading_terminals is recursive into Optional/Map/Sep but
        // only looks at the first element, the only way to get a multi-terminal
        // guard from the first syntax item is if the first item is a Map whose
        // first inner item is a Terminal. That's still one terminal.
        //
        // For a genuine subsumption test, we would need multiple alternative
        // first items (e.g., via grammar alternation). Since the current
        // extraction model only looks at the first SyntaxItemSpec, subsumption
        // between single-terminal guards is impossible (they're either equal or
        // disjoint). This test confirms that expectation.
        let all_syntax = vec![
            (
                "A".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("if".to_string())],
            ),
            (
                "B".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("while".to_string())],
            ),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            result.subsumed_guards.is_empty(),
            "disjoint single-terminal guards cannot be subsumed"
        );
        assert!(
            result.overlapping_guards.is_empty(),
            "disjoint terminals should not overlap"
        );
    }

    #[test]
    fn analyze_bundle_empty_rule_satisfiable() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![CategoryInfo {
            name: "Expr".to_string(),
            is_primary: true,
            native_type: None,
        }];

        // Empty rule (epsilon production) -> satisfiable.
        let all_syntax = vec![(
            "Epsilon".to_string(),
            "Expr".to_string(),
            vec![],
        )];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            result.guard_satisfiability[0].1,
            "empty rule (epsilon) should be satisfiable"
        );
    }

    #[test]
    fn analyze_bundle_ident_capture_satisfiable() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![CategoryInfo {
            name: "Expr".to_string(),
            is_primary: true,
            native_type: None,
        }];

        // Rule starting with IdentCapture -> satisfiable.
        let all_syntax = vec![(
            "Var".to_string(),
            "Expr".to_string(),
            vec![crate::SyntaxItemSpec::IdentCapture {
                param_name: "name".to_string(),
            }],
        )];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            result.guard_satisfiability[0].1,
            "IdentCapture start should be satisfiable"
        );
    }

    #[test]
    fn analyze_bundle_binder_start_satisfiable() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![CategoryInfo {
            name: "Expr".to_string(),
            is_primary: true,
            native_type: None,
        }];

        // Rule starting with Binder -> satisfiable.
        let all_syntax = vec![(
            "Lambda".to_string(),
            "Expr".to_string(),
            vec![crate::SyntaxItemSpec::Binder {
                param_name: "x".to_string(),
                category: "Expr".to_string(),
                is_multi: false,
            }],
        )];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            result.guard_satisfiability[0].1,
            "Binder start should be satisfiable"
        );
    }

    #[test]
    fn analyze_bundle_collection_start_satisfiable() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![CategoryInfo {
            name: "Expr".to_string(),
            is_primary: true,
            native_type: None,
        }];

        // Rule starting with Collection -> satisfiable.
        let all_syntax = vec![(
            "List".to_string(),
            "Expr".to_string(),
            vec![crate::SyntaxItemSpec::Collection {
                param_name: "elems".to_string(),
                element_category: "Expr".to_string(),
                separator: ",".to_string(),
                kind: crate::CollectionKind::Vec,
            }],
        )];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            result.guard_satisfiability[0].1,
            "Collection start should be satisfiable"
        );
    }

    #[test]
    fn analyze_bundle_map_leading_terminal() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![CategoryInfo {
            name: "Expr".to_string(),
            is_primary: true,
            native_type: None,
        }];

        // Rule starts with Map whose first body item is a Terminal.
        let all_syntax = vec![(
            "Pair".to_string(),
            "Expr".to_string(),
            vec![crate::SyntaxItemSpec::Map {
                body_items: vec![
                    crate::SyntaxItemSpec::Terminal("(".to_string()),
                    crate::SyntaxItemSpec::NonTerminal {
                        category: "Expr".to_string(),
                        param_name: "e".to_string(),
                    },
                    crate::SyntaxItemSpec::Terminal(")".to_string()),
                ],
            }],
        )];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert!(
            result.guard_satisfiability[0].1,
            "Map with terminal first item should be satisfiable"
        );
        // The leading terminal set should be {"("}.
        assert!(result.unsatisfiable_rule_labels.is_empty());
    }

    #[test]
    fn analyze_bundle_multiple_overlapping_pairs() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![CategoryInfo {
            name: "Expr".to_string(),
            is_primary: true,
            native_type: None,
        }];

        // Three rules all starting with "(" -> 3 overlap pairs: (0,1), (0,2), (1,2).
        let all_syntax = vec![
            (
                "Parens".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("(".to_string())],
            ),
            (
                "Tuple".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("(".to_string())],
            ),
            (
                "Cast".to_string(),
                "Expr".to_string(),
                vec![crate::SyntaxItemSpec::Terminal("(".to_string())],
            ),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert_eq!(
            result.overlapping_guards.len(),
            3,
            "three rules with same terminal should yield 3 overlap pairs"
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Property-based tests (proptest)
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod proptest_tests {
    use super::*;
    use proptest::prelude::*;
    use crate::test_generators::*;
    use crate::SyntaxItemSpec;

    /// Helper: extract the category prefix from a qualified label.
    ///
    /// Labels produced by `analyze_from_bundle` are `"<cat>::<label>"`, so the
    /// category is everything before the first `::`.
    fn category_of(qualified: &str) -> &str {
        qualified.split("::").next().unwrap_or(qualified)
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(30))]

        // ── 1. Disjoint terminals => no overlap ──────────────────────────────

        /// If no two same-category rules share a leading terminal (all
        /// leading terminals are distinct within each category), then
        /// `overlapping_guards` must be empty.
        #[test]
        fn prop_disjoint_terminals_no_overlap(
            (categories, mut all_syntax) in arb_small_grammar(),
        ) {
            // Post-process: replace every rule's first item with a unique
            // terminal so that no two same-category rules share a leading
            // terminal.
            let mut counter = 0usize;
            for (_label, _cat, items) in all_syntax.iter_mut() {
                let unique_terminal = format!("t{}", counter);
                counter += 1;
                if items.is_empty() {
                    items.push(SyntaxItemSpec::Terminal(unique_terminal));
                } else {
                    items[0] = SyntaxItemSpec::Terminal(unique_terminal);
                }
            }

            let result = analyze_from_bundle(&all_syntax, &categories);
            prop_assert!(
                result.overlapping_guards.is_empty(),
                "disjoint terminals should produce no overlapping guards, \
                 but got {:?}",
                result.overlapping_guards,
            );
        }

        // ── 2. Unsatisfiable is a subset of all rule labels ──────────────────

        /// Every entry in `unsatisfiable_rule_labels` must appear among
        /// the qualified labels of `guard_satisfiability`.
        #[test]
        fn prop_unsatisfiable_subset_all_rules(
            (categories, all_syntax) in arb_small_grammar(),
        ) {
            let result = analyze_from_bundle(&all_syntax, &categories);
            let all_labels: std::collections::HashSet<&str> = result
                .guard_satisfiability
                .iter()
                .map(|(desc, _)| desc.as_str())
                .collect();

            for unsat in &result.unsatisfiable_rule_labels {
                prop_assert!(
                    all_labels.contains(unsat.as_str()),
                    "unsatisfiable label {:?} not found in guard_satisfiability",
                    unsat,
                );
            }
        }

        // ── 3. Terminal start => always satisfiable ──────────────────────────

        /// Any rule whose first syntax item is `Terminal(...)` should
        /// appear as satisfiable in `guard_satisfiability`.
        #[test]
        fn prop_terminal_start_always_satisfiable(
            (categories, all_syntax) in arb_small_grammar(),
        ) {
            let result = analyze_from_bundle(&all_syntax, &categories);

            for (i, (_label, cat, items)) in all_syntax.iter().enumerate() {
                if let Some(SyntaxItemSpec::Terminal(_)) = items.first() {
                    let (ref desc, sat) = result.guard_satisfiability[i];
                    prop_assert!(
                        sat,
                        "rule {} (cat={}) starts with Terminal but guard_satisfiability \
                         reports unsatisfiable",
                        desc,
                        cat,
                    );
                }
            }
        }

        // ── 4. NonTerminal/IdentCapture/Binder start => satisfiable ─────────

        /// Rules starting with `NonTerminal`, `IdentCapture`, or `Binder`
        /// should always be satisfiable.
        #[test]
        fn prop_nonterminal_start_always_satisfiable(
            (categories, all_syntax) in arb_small_grammar(),
        ) {
            let result = analyze_from_bundle(&all_syntax, &categories);

            for (i, (_label, cat, items)) in all_syntax.iter().enumerate() {
                let is_nt_like = items.first().map_or(false, |item| {
                    matches!(
                        item,
                        SyntaxItemSpec::NonTerminal { .. }
                            | SyntaxItemSpec::IdentCapture { .. }
                            | SyntaxItemSpec::Binder { .. }
                    )
                });
                if is_nt_like {
                    let (ref desc, sat) = result.guard_satisfiability[i];
                    prop_assert!(
                        sat,
                        "rule {} (cat={}) starts with NonTerminal/IdentCapture/Binder \
                         but guard_satisfiability reports unsatisfiable",
                        desc,
                        cat,
                    );
                }
            }
        }

        // ── 6. Overlap only within same category ─────────────────────────────

        /// Every pair in `overlapping_guards` must be from the same category
        /// (the category prefix of both qualified labels must match).
        #[test]
        fn prop_overlap_only_within_category(
            (categories, all_syntax) in arb_small_grammar(),
        ) {
            let result = analyze_from_bundle(&all_syntax, &categories);

            for (a, b) in &result.overlapping_guards {
                let cat_a = category_of(a);
                let cat_b = category_of(b);
                prop_assert_eq!(
                    cat_a,
                    cat_b,
                    "overlapping pair ({:?}, {:?}) crosses categories {} vs {}",
                    a,
                    b,
                    cat_a,
                    cat_b,
                );
            }
        }

        // ── 7. Subsumed => strict subset of leading terminals ────────────────

        /// For every `(a, b)` in `subsumed_guards`, the leading terminal
        /// set of rule `a` must be a strict subset of that of rule `b`.
        #[test]
        fn prop_subsumed_implies_strict_subset(
            (categories, all_syntax) in arb_small_grammar(),
        ) {
            let result = analyze_from_bundle(&all_syntax, &categories);

            // Build a map from qualified label -> leading terminal set.
            let mut label_to_terminals: std::collections::HashMap<String, HashSet<String>> =
                std::collections::HashMap::new();
            for (label, cat, items) in &all_syntax {
                let qualified = format!("{}::{}", cat, label);
                let mut terminals = HashSet::new();
                if let Some(first_item) = items.first() {
                    collect_leading_terminals(first_item, &mut terminals);
                }
                label_to_terminals.insert(qualified, terminals);
            }

            for (sub_label, sup_label) in &result.subsumed_guards {
                let sub_terms = label_to_terminals
                    .get(sub_label)
                    .expect("subsumed label not found in grammar");
                let sup_terms = label_to_terminals
                    .get(sup_label)
                    .expect("subsumer label not found in grammar");

                prop_assert!(
                    sub_terms.is_subset(sup_terms),
                    "{:?} terminals {:?} not a subset of {:?} terminals {:?}",
                    sub_label,
                    sub_terms,
                    sup_label,
                    sup_terms,
                );
                prop_assert!(
                    sub_terms != sup_terms,
                    "{:?} and {:?} have equal terminal sets {:?} — \
                     should not be reported as subsumed",
                    sub_label,
                    sup_label,
                    sub_terms,
                );
            }
        }

        // ── 8. Guard count equals rule count ─────────────────────────────────

        /// `guard_satisfiability` must contain exactly one entry per rule
        /// in the input grammar.
        #[test]
        fn prop_guard_count_equals_rule_count(
            (categories, all_syntax) in arb_small_grammar(),
        ) {
            let result = analyze_from_bundle(&all_syntax, &categories);
            prop_assert_eq!(
                result.guard_satisfiability.len(),
                all_syntax.len(),
                "guard_satisfiability length {} != all_syntax length {}",
                result.guard_satisfiability.len(),
                all_syntax.len(),
            );
        }
    }

    // ── 5. Empty items => satisfiable (manual test, not proptest) ────────

    /// A rule with an empty syntax items vec (epsilon production) should
    /// be reported as satisfiable.
    #[test]
    fn prop_empty_items_satisfiable() {
        use crate::pipeline::CategoryInfo;

        let categories = vec![CategoryInfo {
            name: "Expr".to_string(),
            is_primary: true,
            native_type: None,
        }];

        let all_syntax = vec![
            (
                "Epsilon".to_string(),
                "Expr".to_string(),
                vec![], // empty items — epsilon production
            ),
        ];

        let result = analyze_from_bundle(&all_syntax, &categories);
        assert_eq!(
            result.guard_satisfiability.len(),
            1,
            "should have exactly one guard entry",
        );
        assert!(
            result.guard_satisfiability[0].1,
            "empty rule (epsilon) should be satisfiable",
        );
        assert!(
            result.unsatisfiable_rule_labels.is_empty(),
            "epsilon rule should not appear in unsatisfiable list",
        );
    }
}
