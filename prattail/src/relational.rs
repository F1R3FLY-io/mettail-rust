//! Relational weight domain for WPDS analysis.
//!
//! Based on Reps, Lal & Kidd (2007), Definition 7: the relational weight domain
//! on a finite set G is `(2^{G×G}, ∪, ;, ∅, id)` — weights are binary relations
//! on G, combine is union, extend is relational composition.
//!
//! This is the weight domain used by Boolean programs (SLAM/BLAST-style). The
//! carrier represents sets of (source, target) state pairs, where `G` is a finite
//! set of abstract states (e.g., variable valuations over a finite domain).
//!
//! ## Why Not `Copy`
//!
//! The `Semiring` trait requires `Copy`. `RelationalWeight` uses `HashSet<(G, G)>`
//! which is heap-allocated. We provide a separate `HeapSemiring` trait for
//! non-`Copy` weight domains, and bridge functions to use them with the existing
//! WPDS infrastructure.
//!
//! ## Applications
//!
//! - Model operational semantics of `language!` as WPDS rules weighted by
//!   state transformations
//! - MOVP(S, T) = the net state transformation from initial configs S to target T
//! - Interprocedural Boolean program analysis (SLAM/BLAST)

use std::collections::HashSet;
use std::fmt;
use std::hash::Hash;

/// A semiring for heap-allocated weight domains that cannot implement `Copy`.
///
/// Mirrors the `Semiring` trait but without the `Copy` bound, enabling
/// weight domains like `RelationalWeight` and `ProvenanceWeight`.
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

/// Relational weight: binary relation on a finite set G.
///
/// The semiring `(2^{G×G}, ∪, ;, ∅, id)`:
/// - `plus` = union (any pair reachable via either relation)
/// - `times` = relational composition (sequential composition of state transforms)
/// - `zero` = ∅ (no state pairs — unreachable)
/// - `one` = id (identity relation — no state change)
///
/// G must be a finite type with known universe for the identity relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RelationalWeight<G: Clone + Eq + Hash + fmt::Debug + Send + Sync + 'static> {
    /// Set of (source, target) state pairs.
    pub pairs: HashSet<(G, G)>,
    /// The full universe of G values (needed to construct the identity relation).
    /// Stored here so `one()` can produce the correct identity.
    universe: Vec<G>,
}

impl<G: Clone + Eq + Hash + fmt::Debug + Ord + Send + Sync + 'static> RelationalWeight<G> {
    /// Create a relational weight from a set of pairs and the universe.
    pub fn new(pairs: HashSet<(G, G)>, universe: Vec<G>) -> Self {
        RelationalWeight { pairs, universe }
    }

    /// Create the empty relation (zero).
    pub fn empty(universe: Vec<G>) -> Self {
        RelationalWeight {
            pairs: HashSet::new(),
            universe,
        }
    }

    /// Create the identity relation (one).
    pub fn identity(universe: Vec<G>) -> Self {
        let pairs: HashSet<(G, G)> = universe.iter().map(|g| (g.clone(), g.clone())).collect();
        RelationalWeight { pairs, universe }
    }

    /// Create a singleton relation {(a, b)}.
    pub fn singleton(a: G, b: G, universe: Vec<G>) -> Self {
        let mut pairs = HashSet::new();
        pairs.insert((a, b));
        RelationalWeight { pairs, universe }
    }

    /// Number of pairs in the relation.
    pub fn size(&self) -> usize {
        self.pairs.len()
    }

    /// Whether the relation contains a specific pair.
    pub fn contains(&self, a: &G, b: &G) -> bool {
        self.pairs.contains(&(a.clone(), b.clone()))
    }

    /// Domain: set of source elements.
    pub fn domain(&self) -> HashSet<G> {
        self.pairs.iter().map(|(a, _)| a.clone()).collect()
    }

    /// Range: set of target elements.
    pub fn range(&self) -> HashSet<G> {
        self.pairs.iter().map(|(_, b)| b.clone()).collect()
    }

    /// Image of a specific element: {b | (a, b) ∈ R}.
    pub fn image(&self, a: &G) -> HashSet<G> {
        self.pairs
            .iter()
            .filter(|(src, _)| src == a)
            .map(|(_, tgt)| tgt.clone())
            .collect()
    }

    /// Preimage of a specific element: {a | (a, b) ∈ R}.
    pub fn preimage(&self, b: &G) -> HashSet<G> {
        self.pairs
            .iter()
            .filter(|(_, tgt)| tgt == b)
            .map(|(src, _)| src.clone())
            .collect()
    }
}

impl<G: Clone + Eq + Hash + fmt::Debug + Ord + Send + Sync + 'static> HeapSemiring
    for RelationalWeight<G>
{
    fn zero() -> Self {
        // Without universe context, return empty relation.
        // Callers must use `empty(universe)` when universe matters.
        RelationalWeight {
            pairs: HashSet::new(),
            universe: Vec::new(),
        }
    }

    fn one() -> Self {
        // Without universe context, return empty identity.
        // Callers must use `identity(universe)` when universe matters.
        RelationalWeight {
            pairs: HashSet::new(),
            universe: Vec::new(),
        }
    }

    fn plus(&self, other: &Self) -> Self {
        let pairs: HashSet<(G, G)> = self.pairs.union(&other.pairs).cloned().collect();
        let universe = if self.universe.len() >= other.universe.len() {
            self.universe.clone()
        } else {
            other.universe.clone()
        };
        RelationalWeight { pairs, universe }
    }

    fn times(&self, other: &Self) -> Self {
        // Relational composition: (a,c) ∈ R₁;R₂ iff ∃b: (a,b)∈R₁ ∧ (b,c)∈R₂
        let mut pairs = HashSet::new();
        for (a, b) in &self.pairs {
            for (b2, c) in &other.pairs {
                if b == b2 {
                    pairs.insert((a.clone(), c.clone()));
                }
            }
        }
        let universe = if self.universe.len() >= other.universe.len() {
            self.universe.clone()
        } else {
            other.universe.clone()
        };
        RelationalWeight { pairs, universe }
    }

    fn is_zero(&self) -> bool {
        self.pairs.is_empty()
    }

    fn is_one(&self) -> bool {
        if self.universe.is_empty() {
            return self.pairs.is_empty();
        }
        self.pairs.len() == self.universe.len()
            && self.universe.iter().all(|g| self.pairs.contains(&(g.clone(), g.clone())))
    }

    fn approx_eq(&self, other: &Self, _epsilon: f64) -> bool {
        self.pairs == other.pairs
    }
}

impl<G: Clone + Eq + Hash + fmt::Debug + Ord + Send + Sync + 'static> fmt::Display
    for RelationalWeight<G>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        let mut sorted: Vec<_> = self.pairs.iter().collect();
        sorted.sort_by(|a, b| format!("{:?}", a).cmp(&format!("{:?}", b)));
        let mut first = true;
        for (a, b) in sorted {
            if !first {
                write!(f, ", ")?;
            }
            first = false;
            write!(f, "({:?}, {:?})", a, b)?;
        }
        write!(f, "}}")
    }
}

/// A Weighted Pushdown System using heap-allocated weight domains.
///
/// Mirrors `Wpds<W>` but with `HeapSemiring` bound instead of `Semiring`.
/// This enables WPDS analysis with relational and provenance weight domains.
#[derive(Debug, Clone)]
pub struct HeapWpds<W: HeapSemiring> {
    /// Stack alphabet Γ.
    pub stack_symbols: Vec<crate::wpds::StackSymbol>,
    /// Index from stack symbol to position.
    pub symbol_index: std::collections::HashMap<crate::wpds::StackSymbol, usize>,
    /// PDS rules Δ.
    pub rules: Vec<HeapWpdsRule<W>>,
    /// Rules indexed by source stack symbol.
    pub rules_by_source: std::collections::HashMap<crate::wpds::StackSymbol, Vec<usize>>,
    /// Initial stack symbol.
    pub initial_symbol: crate::wpds::StackSymbol,
    /// Grammar name.
    pub grammar_name: String,
}

/// A PDS rule with heap-allocated weights.
#[derive(Debug, Clone)]
pub enum HeapWpdsRule<W: HeapSemiring> {
    /// Pop rule: `⟨p, γ⟩ ↪ ⟨p', ε⟩`.
    Pop {
        from_gamma: crate::wpds::StackSymbol,
        weight: W,
    },
    /// Replace rule: `⟨p, γ⟩ ↪ ⟨p', γ'⟩`.
    Replace {
        from_gamma: crate::wpds::StackSymbol,
        to_gamma: crate::wpds::StackSymbol,
        weight: W,
    },
    /// Push rule: `⟨p, γ⟩ ↪ ⟨p', γ' γ''⟩`.
    Push {
        from_gamma: crate::wpds::StackSymbol,
        to_gamma_bottom: crate::wpds::StackSymbol,
        to_gamma_top: crate::wpds::StackSymbol,
        weight: W,
    },
}

impl<W: HeapSemiring> HeapWpdsRule<W> {
    /// The source stack symbol.
    pub fn from_gamma(&self) -> &crate::wpds::StackSymbol {
        match self {
            HeapWpdsRule::Pop { from_gamma, .. }
            | HeapWpdsRule::Replace { from_gamma, .. }
            | HeapWpdsRule::Push { from_gamma, .. } => from_gamma,
        }
    }

    /// The weight.
    pub fn weight(&self) -> &W {
        match self {
            HeapWpdsRule::Pop { weight, .. }
            | HeapWpdsRule::Replace { weight, .. }
            | HeapWpdsRule::Push { weight, .. } => weight,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type G = u8;

    fn universe() -> Vec<G> {
        vec![0, 1, 2]
    }

    #[test]
    fn test_empty_is_zero() {
        let r: RelationalWeight<G> = RelationalWeight::empty(universe());
        assert!(r.is_zero());
        assert!(!r.is_one());
    }

    #[test]
    fn test_identity_is_one() {
        let r: RelationalWeight<G> = RelationalWeight::identity(universe());
        assert!(r.is_one());
        assert!(!r.is_zero());
        assert_eq!(r.size(), 3);
    }

    #[test]
    fn test_union_plus() {
        let r1 = RelationalWeight::singleton(0u8, 1u8, universe());
        let r2 = RelationalWeight::singleton(1u8, 2u8, universe());
        let sum = r1.plus(&r2);
        assert_eq!(sum.size(), 2);
        assert!(sum.contains(&0, &1));
        assert!(sum.contains(&1, &2));
    }

    #[test]
    fn test_composition_times() {
        // {(0,1)} ; {(1,2)} = {(0,2)}
        let r1 = RelationalWeight::singleton(0u8, 1u8, universe());
        let r2 = RelationalWeight::singleton(1u8, 2u8, universe());
        let product = r1.times(&r2);
        assert_eq!(product.size(), 1);
        assert!(product.contains(&0, &2));
    }

    #[test]
    fn test_zero_annihilates() {
        let r = RelationalWeight::singleton(0u8, 1u8, universe());
        let z = RelationalWeight::empty(universe());
        assert!(r.times(&z).is_zero());
        assert!(z.times(&r).is_zero());
    }

    #[test]
    fn test_identity_is_neutral() {
        let r = RelationalWeight::singleton(0u8, 1u8, universe());
        let id = RelationalWeight::identity(universe());
        let ri = r.times(&id);
        let ir = id.times(&r);
        assert_eq!(ri.pairs, r.pairs);
        assert_eq!(ir.pairs, r.pairs);
    }

    #[test]
    fn test_plus_is_commutative() {
        let r1 = RelationalWeight::singleton(0u8, 1u8, universe());
        let r2 = RelationalWeight::singleton(1u8, 2u8, universe());
        assert_eq!(r1.plus(&r2).pairs, r2.plus(&r1).pairs);
    }

    #[test]
    fn test_times_is_associative() {
        let r1 = RelationalWeight::singleton(0u8, 1u8, universe());
        let r2 = RelationalWeight::singleton(1u8, 2u8, universe());
        let r3 = RelationalWeight::singleton(2u8, 0u8, universe());
        let lhs = r1.times(&r2).times(&r3);
        let rhs = r1.times(&r2.times(&r3));
        assert_eq!(lhs.pairs, rhs.pairs);
    }

    #[test]
    fn test_distributive() {
        let r1 = RelationalWeight::singleton(0u8, 1u8, universe());
        let r2 = RelationalWeight::singleton(1u8, 2u8, universe());
        let r3 = RelationalWeight::singleton(1u8, 0u8, universe());
        let lhs = r1.times(&r2.plus(&r3));
        let rhs = r1.times(&r2).plus(&r1.times(&r3));
        assert_eq!(lhs.pairs, rhs.pairs);
    }

    #[test]
    fn test_domain_and_range() {
        let mut pairs = HashSet::new();
        pairs.insert((0u8, 1u8));
        pairs.insert((0, 2));
        pairs.insert((1, 2));
        let r = RelationalWeight::new(pairs, universe());
        assert_eq!(r.domain().len(), 2);
        assert_eq!(r.range().len(), 2);
    }

    #[test]
    fn test_image_and_preimage() {
        let mut pairs = HashSet::new();
        pairs.insert((0u8, 1u8));
        pairs.insert((0, 2));
        pairs.insert((1, 2));
        let r = RelationalWeight::new(pairs, universe());
        assert_eq!(r.image(&0).len(), 2);
        assert_eq!(r.preimage(&2).len(), 2);
    }

    #[test]
    fn test_display() {
        let r = RelationalWeight::singleton(0u8, 1u8, universe());
        let s = r.to_string();
        assert!(s.contains("(0, 1)"));
    }

    #[test]
    fn test_approx_eq() {
        let r1 = RelationalWeight::singleton(0u8, 1u8, universe());
        let r2 = RelationalWeight::singleton(0u8, 1u8, universe());
        assert!(r1.approx_eq(&r2, 0.0));
    }
}
