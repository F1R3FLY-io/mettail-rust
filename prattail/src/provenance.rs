//! Provenance semiring `N[X]`: polynomial semiring tracking HOW facts are derived.
//!
//! Based on Green, Karvounarakis & Tannen (2007), *Provenance Semirings*.
//!
//! The provenance semiring tracks not just WHETHER a fact is derivable, but HOW
//! and WHY. The carrier set is the set of polynomials with natural number
//! coefficients over a set of base-fact variables X.
//!
//! ## Provenance Types
//!
//! | Provenance type     | Semiring         | Tracks                                   |
//! |---------------------|------------------|------------------------------------------|
//! | Which-provenance    | BooleanWeight    | Is fact derivable? (yes/no)              |
//! | How-provenance      | N[X]             | Which combinations of base facts derive  |
//! | Why-provenance      | Powerset(trees)  | All possible derivation trees            |
//! | Confidence-prov.    | ViterbiWeight    | Most confident derivation                |
//! | Cost-provenance     | TropicalWeight   | Cheapest derivation                      |
//!
//! ## Representation
//!
//! A provenance polynomial `p ∈ N[X]` is represented as a sum of monomials:
//! ```text
//! p = c₁·x₁^a₁·x₂^a₂·...·xₙ^aₙ + c₂·... + ...
//! ```
//! where each `cᵢ` is a natural number coefficient and each `xⱼ^aⱼ` tracks
//! which base facts (identified by `ProvenanceVar`) contribute to the derivation.
//!
//! ## Semiring Operations
//!
//! - `plus` (⊕) = polynomial addition (union of derivation alternatives)
//! - `times` (⊗) = polynomial multiplication (conjunction of derivation steps)
//! - `zero` = 0 (no derivation)
//! - `one` = 1 (trivial derivation — no base facts needed)
//!
//! ## Example
//!
//! If base facts are `x₁` (axiom A) and `x₂` (axiom B), and a derived fact
//! can be proven either by combining A+B or by using A twice:
//! ```text
//! provenance = x₁·x₂ + x₁²
//! ```
//! This tells us: the fact has two derivations, one using A∧B, another using A twice.

use std::collections::BTreeMap;
use std::fmt;

/// A provenance variable identifying a base fact.
///
/// Variables are ordered (for canonical monomial representation) and must be
/// unique within a derivation context.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ProvenanceVar(pub String);

impl ProvenanceVar {
    /// Create a new provenance variable.
    pub fn new(name: impl Into<String>) -> Self {
        ProvenanceVar(name.into())
    }
}

impl fmt::Display for ProvenanceVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A monomial: a product of provenance variables with exponents.
///
/// Represented as an ordered map from variable to exponent (natural number).
/// The empty monomial (no variables) represents the constant `1`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Monomial {
    /// Variables and their exponents, sorted by variable for canonical form.
    pub factors: BTreeMap<ProvenanceVar, u32>,
}

impl Monomial {
    /// The constant monomial `1` (empty product).
    pub fn one() -> Self {
        Monomial { factors: BTreeMap::new() }
    }

    /// A single-variable monomial `x^1`.
    pub fn var(v: ProvenanceVar) -> Self {
        let mut factors = BTreeMap::new();
        factors.insert(v, 1);
        Monomial { factors }
    }

    /// Multiply two monomials (add exponents).
    pub fn multiply(&self, other: &Monomial) -> Monomial {
        let mut result = self.factors.clone();
        for (var, &exp) in &other.factors {
            *result.entry(var.clone()).or_insert(0) += exp;
        }
        Monomial { factors: result }
    }

    /// Whether this is the constant monomial `1`.
    pub fn is_one(&self) -> bool {
        self.factors.is_empty()
    }

    /// Total degree (sum of all exponents).
    pub fn degree(&self) -> u32 {
        self.factors.values().sum()
    }

    /// Variables involved in this monomial.
    pub fn variables(&self) -> Vec<&ProvenanceVar> {
        self.factors.keys().collect()
    }
}

impl fmt::Display for Monomial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.factors.is_empty() {
            return write!(f, "1");
        }
        let mut first = true;
        for (var, &exp) in &self.factors {
            if !first {
                write!(f, "·")?;
            }
            first = false;
            if exp == 1 {
                write!(f, "{}", var)?;
            } else {
                write!(f, "{}^{}", var, exp)?;
            }
        }
        Ok(())
    }
}

/// Provenance polynomial `N[X]`: a sum of weighted monomials.
///
/// This is the **how-provenance** semiring from Green et al. (2007).
/// Each term tracks a distinct combination of base facts that derives the result.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenanceWeight {
    /// Terms: monomial → coefficient (natural number).
    /// Zero polynomial has empty terms map.
    pub terms: BTreeMap<Monomial, u64>,
}

impl ProvenanceWeight {
    /// The zero polynomial (no derivation).
    pub fn zero() -> Self {
        ProvenanceWeight { terms: BTreeMap::new() }
    }

    /// The constant polynomial `1` (trivial derivation).
    pub fn one() -> Self {
        let mut terms = BTreeMap::new();
        terms.insert(Monomial::one(), 1);
        ProvenanceWeight { terms }
    }

    /// A single-variable polynomial `x` (derivation uses base fact x).
    pub fn var(v: ProvenanceVar) -> Self {
        let mut terms = BTreeMap::new();
        terms.insert(Monomial::var(v), 1);
        ProvenanceWeight { terms }
    }

    /// A constant polynomial with value `n`.
    pub fn constant(n: u64) -> Self {
        if n == 0 {
            return Self::zero();
        }
        let mut terms = BTreeMap::new();
        terms.insert(Monomial::one(), n);
        ProvenanceWeight { terms }
    }

    /// Polynomial addition: `p₁ ⊕ p₂` — union of derivation alternatives.
    ///
    /// Adds coefficients for matching monomials.
    pub fn plus(&self, other: &ProvenanceWeight) -> ProvenanceWeight {
        let mut result = self.terms.clone();
        for (mono, &coeff) in &other.terms {
            *result.entry(mono.clone()).or_insert(0) += coeff;
        }
        // Remove zero-coefficient terms.
        result.retain(|_, c| *c > 0);
        ProvenanceWeight { terms: result }
    }

    /// Polynomial multiplication: `p₁ ⊗ p₂` — conjunction of derivation steps.
    ///
    /// Multiplies every term in `self` with every term in `other`.
    pub fn times(&self, other: &ProvenanceWeight) -> ProvenanceWeight {
        let mut result = BTreeMap::new();
        for (m1, &c1) in &self.terms {
            for (m2, &c2) in &other.terms {
                let product_mono = m1.multiply(m2);
                *result.entry(product_mono).or_insert(0u64) += c1 * c2;
            }
        }
        result.retain(|_, c| *c > 0);
        ProvenanceWeight { terms: result }
    }

    /// Whether this is the zero polynomial (no derivation).
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// Whether this is the constant polynomial `1`.
    pub fn is_one(&self) -> bool {
        self.terms.len() == 1
            && self.terms.get(&Monomial::one()) == Some(&1)
    }

    /// Number of distinct monomials (derivation alternatives).
    pub fn num_alternatives(&self) -> usize {
        self.terms.len()
    }

    /// Total coefficient sum (total derivation count across all alternatives).
    pub fn total_count(&self) -> u64 {
        self.terms.values().sum()
    }

    /// All provenance variables referenced across all monomials.
    pub fn all_variables(&self) -> Vec<ProvenanceVar> {
        let mut vars: std::collections::BTreeSet<ProvenanceVar> = std::collections::BTreeSet::new();
        for mono in self.terms.keys() {
            for var in mono.factors.keys() {
                vars.insert(var.clone());
            }
        }
        vars.into_iter().collect()
    }

    /// Evaluate the polynomial by substituting each variable with a value
    /// from the given semiring, returning the aggregate weight.
    ///
    /// This is the homomorphism from N[X] to any semiring W, given a
    /// valuation `v: X → W`. It collapses provenance into a concrete weight.
    pub fn evaluate<W: crate::automata::semiring::Semiring>(
        &self,
        valuation: &impl Fn(&ProvenanceVar) -> W,
    ) -> W {
        let mut result = W::zero();
        for (mono, &coeff) in &self.terms {
            // Evaluate the monomial: product of variable valuations raised to exponents.
            let mut mono_val = W::one();
            for (var, &exp) in &mono.factors {
                let var_val = valuation(var);
                for _ in 0..exp {
                    mono_val = mono_val.times(&var_val);
                }
            }
            // Multiply by coefficient (repeated addition).
            let mut term_val = W::zero();
            for _ in 0..coeff {
                term_val = term_val.plus(&mono_val);
            }
            result = result.plus(&term_val);
        }
        result
    }

    /// Project to Boolean provenance (which-provenance):
    /// returns true iff the polynomial is non-zero.
    pub fn to_boolean(&self) -> bool {
        !self.is_zero()
    }

    /// Project to counting provenance: total number of derivations.
    pub fn to_counting(&self) -> u64 {
        self.total_count()
    }

    /// Find the "missing monomial" — what base fact(s) would need to be added
    /// to make a currently-zero polynomial non-zero. Returns `None` if already non-zero.
    ///
    /// This is used for repair suggestions: "which base facts are missing?"
    pub fn missing_for_nonzero(&self) -> Option<Vec<ProvenanceVar>> {
        if !self.is_zero() {
            return None;
        }
        // If zero, we can't determine what's missing from the polynomial itself.
        // The caller should compare against the expected polynomial.
        Some(Vec::new())
    }
}

impl fmt::Display for ProvenanceWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.terms.is_empty() {
            return write!(f, "0");
        }
        let mut first = true;
        for (mono, &coeff) in &self.terms {
            if !first {
                write!(f, " + ")?;
            }
            first = false;
            if mono.is_one() {
                write!(f, "{}", coeff)?;
            } else if coeff == 1 {
                write!(f, "{}", mono)?;
            } else {
                write!(f, "{}·{}", coeff, mono)?;
            }
        }
        Ok(())
    }
}

impl Default for ProvenanceWeight {
    fn default() -> Self {
        Self::one()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline-level provenance tracking result.
#[derive(Debug, Clone)]
pub struct ProvenanceAnalysis {
    /// How-provenance polynomials for key facts (label → polynomial string).
    pub provenance_traces: Vec<(String, String)>,
}

/// Pipeline bridge: track provenance for grammar rules.
///
/// For each rule in `all_syntax`, creates a single-variable provenance polynomial
/// (the rule label as a `ProvenanceVar`), capturing the base-level "how" provenance.
/// The resulting `ProvenanceAnalysis` records these polynomials as displayable strings
/// for diagnostic output.
///
/// Returns `None` if `all_syntax` is empty (no rules to track).
pub fn track_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    _categories: &[crate::pipeline::CategoryInfo],
) -> Option<ProvenanceAnalysis> {
    if all_syntax.is_empty() {
        return None;
    }
    // Build provenance weight for each rule.
    let mut traces = Vec::new();
    for (label, _cat, _items) in all_syntax {
        let var = ProvenanceVar(label.clone());
        let weight = ProvenanceWeight::var(var);
        traces.push((label.clone(), format!("{}", weight)));
    }
    Some(ProvenanceAnalysis { provenance_traces: traces })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn x(name: &str) -> ProvenanceVar {
        ProvenanceVar::new(name)
    }

    #[test]
    fn test_zero_and_one() {
        let zero = ProvenanceWeight::zero();
        let one = ProvenanceWeight::one();
        assert!(zero.is_zero());
        assert!(!zero.is_one());
        assert!(one.is_one());
        assert!(!one.is_zero());
    }

    #[test]
    fn test_var() {
        let p = ProvenanceWeight::var(x("a"));
        assert!(!p.is_zero());
        assert!(!p.is_one());
        assert_eq!(p.num_alternatives(), 1);
        assert_eq!(p.total_count(), 1);
    }

    #[test]
    fn test_plus_union() {
        // x₁ + x₂ = two alternatives
        let p1 = ProvenanceWeight::var(x("x1"));
        let p2 = ProvenanceWeight::var(x("x2"));
        let sum = p1.plus(&p2);
        assert_eq!(sum.num_alternatives(), 2);
        assert_eq!(sum.total_count(), 2);
    }

    #[test]
    fn test_plus_combines_like_terms() {
        // x₁ + x₁ = 2·x₁
        let p1 = ProvenanceWeight::var(x("x1"));
        let sum = p1.plus(&p1);
        assert_eq!(sum.num_alternatives(), 1);
        assert_eq!(sum.total_count(), 2);
    }

    #[test]
    fn test_times_conjunction() {
        // x₁ · x₂ = one monomial with two variables
        let p1 = ProvenanceWeight::var(x("x1"));
        let p2 = ProvenanceWeight::var(x("x2"));
        let product = p1.times(&p2);
        assert_eq!(product.num_alternatives(), 1);
        let mono = product.terms.keys().next().expect("should have one monomial");
        assert_eq!(mono.degree(), 2);
    }

    #[test]
    fn test_times_self_squares() {
        // x₁ · x₁ = x₁²
        let p = ProvenanceWeight::var(x("x1"));
        let sq = p.times(&p);
        assert_eq!(sq.num_alternatives(), 1);
        let mono = sq.terms.keys().next().expect("should have one monomial");
        assert_eq!(mono.degree(), 2);
        assert_eq!(mono.factors.get(&x("x1")), Some(&2));
    }

    #[test]
    fn test_zero_annihilates() {
        let p = ProvenanceWeight::var(x("a"));
        let z = ProvenanceWeight::zero();
        assert!(p.times(&z).is_zero());
        assert!(z.times(&p).is_zero());
    }

    #[test]
    fn test_one_identity() {
        let p = ProvenanceWeight::var(x("a"));
        let one = ProvenanceWeight::one();
        assert_eq!(p.times(&one), p);
        assert_eq!(one.times(&p), p);
    }

    #[test]
    fn test_zero_identity_for_plus() {
        let p = ProvenanceWeight::var(x("a"));
        let z = ProvenanceWeight::zero();
        assert_eq!(p.plus(&z), p);
        assert_eq!(z.plus(&p), p);
    }

    #[test]
    fn test_distributive() {
        // x₁ · (x₂ + x₃) = x₁·x₂ + x₁·x₃
        let x1 = ProvenanceWeight::var(x("x1"));
        let x2 = ProvenanceWeight::var(x("x2"));
        let x3 = ProvenanceWeight::var(x("x3"));
        let lhs = x1.times(&x2.plus(&x3));
        let rhs = x1.times(&x2).plus(&x1.times(&x3));
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_display() {
        let zero = ProvenanceWeight::zero();
        assert_eq!(zero.to_string(), "0");

        let one = ProvenanceWeight::one();
        assert_eq!(one.to_string(), "1");

        let p = ProvenanceWeight::var(x("a"));
        assert_eq!(p.to_string(), "a");

        let two_a = p.plus(&p);
        assert_eq!(two_a.to_string(), "2·a");
    }

    #[test]
    fn test_constant() {
        let c3 = ProvenanceWeight::constant(3);
        assert_eq!(c3.total_count(), 3);
        assert_eq!(c3.to_string(), "3");

        let c0 = ProvenanceWeight::constant(0);
        assert!(c0.is_zero());
    }

    #[test]
    fn test_all_variables() {
        let p = ProvenanceWeight::var(x("b"))
            .plus(&ProvenanceWeight::var(x("a")).times(&ProvenanceWeight::var(x("c"))));
        let vars = p.all_variables();
        assert_eq!(vars.len(), 3);
        assert_eq!(vars[0].0, "a");
        assert_eq!(vars[1].0, "b");
        assert_eq!(vars[2].0, "c");
    }

    #[test]
    fn test_evaluate_to_boolean() {
        use crate::automata::semiring::BooleanWeight;

        let p = ProvenanceWeight::var(x("a")).plus(&ProvenanceWeight::var(x("b")));
        let result = p.evaluate(&|_: &ProvenanceVar| BooleanWeight(true));
        assert_eq!(result, BooleanWeight(true));

        let zero = ProvenanceWeight::zero();
        let result = zero.evaluate(&|_: &ProvenanceVar| BooleanWeight(true));
        assert_eq!(result, BooleanWeight(false));
    }

    #[test]
    fn test_evaluate_to_counting() {
        use crate::automata::semiring::CountingWeight;

        // x₁ + x₂: each variable maps to count 1 → total = 2
        let p = ProvenanceWeight::var(x("x1")).plus(&ProvenanceWeight::var(x("x2")));
        let result = p.evaluate(&|_: &ProvenanceVar| CountingWeight(1));
        assert_eq!(result, CountingWeight(2));
    }

    #[test]
    fn test_evaluate_to_tropical() {
        use crate::automata::semiring::TropicalWeight;

        // x₁ + x₂: each with cost 1.0, tropical plus = min → result = 1.0
        let p = ProvenanceWeight::var(x("x1")).plus(&ProvenanceWeight::var(x("x2")));
        let result = p.evaluate(&|_: &ProvenanceVar| TropicalWeight(1.0));
        assert_eq!(result, TropicalWeight(1.0));
    }

    #[test]
    fn test_monomial_display() {
        let m1 = Monomial::one();
        assert_eq!(m1.to_string(), "1");

        let m2 = Monomial::var(x("x"));
        assert_eq!(m2.to_string(), "x");

        let m3 = m2.multiply(&m2);
        assert_eq!(m3.to_string(), "x^2");
    }

    #[test]
    fn test_to_boolean_and_counting() {
        let p = ProvenanceWeight::var(x("a")).plus(&ProvenanceWeight::var(x("b")));
        assert!(p.to_boolean());
        assert_eq!(p.to_counting(), 2);

        assert!(!ProvenanceWeight::zero().to_boolean());
        assert_eq!(ProvenanceWeight::zero().to_counting(), 0);
    }

    #[test]
    fn test_complex_polynomial() {
        // (x₁ + x₂) · (x₃ + x₄) = x₁·x₃ + x₁·x₄ + x₂·x₃ + x₂·x₄
        let x1 = ProvenanceWeight::var(x("x1"));
        let x2 = ProvenanceWeight::var(x("x2"));
        let x3 = ProvenanceWeight::var(x("x3"));
        let x4 = ProvenanceWeight::var(x("x4"));
        let product = x1.plus(&x2).times(&x3.plus(&x4));
        assert_eq!(product.num_alternatives(), 4);
        assert_eq!(product.total_count(), 4);
        assert_eq!(product.all_variables().len(), 4);
    }

    #[test]
    fn test_commutativity_of_plus() {
        let a = ProvenanceWeight::var(x("a"));
        let b = ProvenanceWeight::var(x("b"));
        assert_eq!(a.plus(&b), b.plus(&a));
    }

    #[test]
    fn test_associativity_of_times() {
        let a = ProvenanceWeight::var(x("a"));
        let b = ProvenanceWeight::var(x("b"));
        let c = ProvenanceWeight::var(x("c"));
        let lhs = a.times(&b).times(&c);
        let rhs = a.times(&b.times(&c));
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_missing_for_nonzero() {
        let zero = ProvenanceWeight::zero();
        assert!(zero.missing_for_nonzero().is_some());

        let p = ProvenanceWeight::var(x("a"));
        assert!(p.missing_for_nonzero().is_none());
    }

    #[test]
    fn test_track_from_bundle_basic() {
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![(
            "Add".to_string(),
            "Expr".to_string(),
            vec![
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "a".to_string(),
                },
                crate::SyntaxItemSpec::Terminal("+".to_string()),
                crate::SyntaxItemSpec::NonTerminal {
                    category: "Expr".to_string(),
                    param_name: "b".to_string(),
                },
            ],
        )];
        let cats = vec![crate::pipeline::CategoryInfo {
            name: "Expr".to_string(),
            native_type: None,
            is_primary: true,
        }];
        let result = track_from_bundle(&syntax, &cats);
        assert!(result.is_some(), "should produce provenance analysis for non-empty syntax");
        let analysis = result.expect("expected Some");
        assert!(!analysis.provenance_traces.is_empty(), "should have at least one trace");
    }

    #[test]
    fn test_track_from_bundle_empty() {
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![];
        let cats = vec![crate::pipeline::CategoryInfo {
            name: "Expr".to_string(),
            native_type: None,
            is_primary: true,
        }];
        let result = track_from_bundle(&syntax, &cats);
        assert!(result.is_none(), "should return None for empty syntax");
    }
}
