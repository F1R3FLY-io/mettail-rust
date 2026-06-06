//! Expectation semiring: `(weight: f64, expected_cost: f64)`.
//!
//! Combines a log-domain weight with an expected cost accumulated along paths.
//! The semiring structure follows Eisner (2002) "Parameter estimation for
//! probabilistic finite-state transducers":
//!
//! - `⊕`: logsumexp on weight, weighted combination on expected cost
//! - `⊗`: addition on weight, cross-product accumulation on expected cost
//! - `0`: `(+inf, 0.0)` — unreachable path
//! - `1`: `(0.0, 0.0)` — zero-cost, zero-expectation identity
//!
//! ## Applications
//!
//! - **Expected parse cost**: weight = log-probability, cost = parse tree depth
//! - **Risk-aware scheduling**: weight = transition probability, cost = latency
//! - **Gradient computation**: the expectation semiring naturally computes
//!   ∂/∂θ of the total path weight (Eisner 2002, §4).

use std::fmt;

use mettail_prattail::automata::semiring::Semiring;

/// Expectation semiring weight: `(w, c)` where `w` is a log-domain weight
/// and `c` is the expected cost.
///
/// The carrier is a pair of f64 values. The weight component `w` behaves
/// like a [`LogWeight`](mettail_prattail::automata::semiring::LogWeight)
/// (negative log probability), while `c` tracks the expected cost weighted
/// by the probability mass.
///
/// ## Semiring operations
///
/// **Plus** (combine parallel paths):
/// ```text
/// (w₁, c₁) ⊕ (w₂, c₂) = (logsumexp(w₁, w₂), (exp(-w₁)·c₁ + exp(-w₂)·c₂) / (exp(-w₁) + exp(-w₂)))
/// ```
///
/// **Times** (sequence path segments):
/// ```text
/// (w₁, c₁) ⊗ (w₂, c₂) = (w₁ + w₂, c₁ + c₂)
/// ```
#[derive(Clone, Copy, Debug)]
pub struct ExpectationWeight {
    /// Log-domain weight (negative log probability). Lower = more probable.
    pub weight: f64,
    /// Expected cost (probability-weighted cost accumulator).
    pub expected_cost: f64,
}

impl ExpectationWeight {
    /// Create a new expectation weight.
    #[inline]
    pub const fn new(weight: f64, expected_cost: f64) -> Self {
        ExpectationWeight { weight, expected_cost }
    }

    /// Create from a probability and cost.
    ///
    /// Converts `p` to log-domain: `w = -ln(p)`.
    #[inline]
    pub fn from_probability(p: f64, cost: f64) -> Self {
        assert!(p > 0.0, "ExpectationWeight::from_probability: p must be > 0, got {p}");
        ExpectationWeight { weight: -p.ln(), expected_cost: cost }
    }

    /// Convert the weight back to a probability: `p = exp(-w)`.
    #[inline]
    pub fn to_probability(&self) -> f64 {
        (-self.weight).exp()
    }

    /// Numerically stable log-sum-exp: `-ln(exp(-a) + exp(-b))`.
    ///
    /// Uses the identity: `logsumexp(a, b) = min(a, b) - ln(1 + exp(-|a-b|))`.
    /// For `|a-b| > 20`, the correction term is negligible and dropped.
    #[inline]
    fn log_sum_exp(a: f64, b: f64) -> f64 {
        if a == f64::INFINITY {
            return b;
        }
        if b == f64::INFINITY {
            return a;
        }
        let min_val = a.min(b);
        let diff = (a - b).abs();
        if diff > 20.0 {
            min_val
        } else {
            min_val - (1.0 + (-diff).exp()).ln()
        }
    }
}

impl Semiring for ExpectationWeight {
    /// Zero = `(+inf, 0.0)`: unreachable path with no cost contribution.
    #[inline]
    fn zero() -> Self {
        ExpectationWeight {
            weight: f64::INFINITY,
            expected_cost: 0.0,
        }
    }

    /// One = `(0.0, 0.0)`: probability 1, zero cost.
    #[inline]
    fn one() -> Self {
        ExpectationWeight { weight: 0.0, expected_cost: 0.0 }
    }

    /// Plus: combine parallel paths.
    ///
    /// Weight: logsumexp (probability addition in log-domain).
    /// Cost: probability-weighted average of costs.
    #[inline]
    fn plus(&self, other: &Self) -> Self {
        if self.is_zero() {
            return *other;
        }
        if other.is_zero() {
            return *self;
        }

        let new_weight = Self::log_sum_exp(self.weight, other.weight);

        // Compute weighted cost: (p1*c1 + p2*c2) / (p1 + p2)
        // In log domain: p_i = exp(-w_i), sum = exp(-new_weight)
        // Numerically: shift by new_weight for stability
        let p1 = (-(self.weight - new_weight)).exp();
        let p2 = (-(other.weight - new_weight)).exp();
        let p_sum = p1 + p2;
        let new_cost = if p_sum > 0.0 {
            (p1 * self.expected_cost + p2 * other.expected_cost) / p_sum
        } else {
            0.0
        };

        ExpectationWeight {
            weight: new_weight,
            expected_cost: new_cost,
        }
    }

    /// Times: sequence path segments.
    ///
    /// Weight: addition (probability multiplication in log-domain).
    /// Cost: addition (costs accumulate along a path).
    #[inline]
    fn times(&self, other: &Self) -> Self {
        ExpectationWeight {
            weight: self.weight + other.weight,
            expected_cost: self.expected_cost + other.expected_cost,
        }
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.weight.is_infinite() && self.weight.is_sign_positive()
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.weight == 0.0 && self.expected_cost == 0.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        if self.is_zero() && other.is_zero() {
            return true;
        }
        if self.is_zero() || other.is_zero() {
            return false;
        }
        (self.weight - other.weight).abs() <= epsilon
            && (self.expected_cost - other.expected_cost).abs() <= epsilon
    }
}

impl PartialEq for ExpectationWeight {
    fn eq(&self, other: &Self) -> bool {
        self.weight.to_bits() == other.weight.to_bits()
            && self.expected_cost.to_bits() == other.expected_cost.to_bits()
    }
}

impl Eq for ExpectationWeight {}

impl std::hash::Hash for ExpectationWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.weight.to_bits().hash(state);
        self.expected_cost.to_bits().hash(state);
    }
}

impl fmt::Display for ExpectationWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "(inf, 0)")
        } else {
            write!(f, "({:.4}, {:.4})", self.weight, self.expected_cost)
        }
    }
}

impl Default for ExpectationWeight {
    fn default() -> Self {
        Self::one()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zero_identity() {
        let a = ExpectationWeight::new(1.0, 2.0);
        let sum = a.plus(&ExpectationWeight::zero());
        assert!(sum.approx_eq(&a, 1e-10), "zero is additive identity");
    }

    #[test]
    fn test_one_identity() {
        let a = ExpectationWeight::new(1.0, 2.0);
        let prod = a.times(&ExpectationWeight::one());
        assert!(prod.approx_eq(&a, 1e-10), "one is multiplicative identity");
    }

    #[test]
    fn test_times_accumulates_cost() {
        let a = ExpectationWeight::new(1.0, 3.0);
        let b = ExpectationWeight::new(2.0, 4.0);
        let prod = a.times(&b);
        assert!((prod.weight - 3.0).abs() < 1e-10, "weights add: {}", prod.weight);
        assert!((prod.expected_cost - 7.0).abs() < 1e-10, "costs add: {}", prod.expected_cost);
    }

    #[test]
    fn test_plus_combines_paths() {
        // Two paths with equal probability (weight 0.0 = prob 1.0 each)
        let a = ExpectationWeight::new(0.0, 10.0);
        let b = ExpectationWeight::new(0.0, 20.0);
        let sum = a.plus(&b);
        // Expected cost should be average: (1.0*10 + 1.0*20) / (1.0 + 1.0) = 15.0
        assert!(
            (sum.expected_cost - 15.0).abs() < 1e-10,
            "equal-weight plus averages cost: {}",
            sum.expected_cost
        );
    }

    #[test]
    fn test_from_probability() {
        let w = ExpectationWeight::from_probability(0.5, 3.0);
        assert!((w.to_probability() - 0.5).abs() < 1e-10);
        assert!((w.expected_cost - 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_zero_annihilates() {
        let a = ExpectationWeight::new(1.0, 5.0);
        let z = ExpectationWeight::zero();
        let prod = a.times(&z);
        assert!(prod.is_zero(), "zero annihilates on right");
        let prod2 = z.times(&a);
        assert!(prod2.is_zero(), "zero annihilates on left");
    }
}
