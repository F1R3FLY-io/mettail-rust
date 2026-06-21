use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// LogWeight (feature = "wfst-log")
// ══════════════════════════════════════════════════════════════════════════════

/// Log semiring weight: `(R+ union {+inf}, log-sum-exp, +, +inf, 0.0)`.
///
/// Represents negative log probabilities: `w = -ln(p)`.
///
/// - `plus = log-sum-exp`: combines probabilities: `-ln(exp(-a) + exp(-b))`
/// - `times = +`: multiplies probabilities: `-ln(p * q) = -ln(p) + -ln(q)`
/// - `zero = +inf`: probability 0 (identity for log-sum-exp)
/// - `one = 0.0`: probability 1 (identity for multiplication)
///
/// Unlike `TropicalWeight`, `LogWeight` is **not idempotent**: `plus(a, a) != a`
/// because `exp(-a) + exp(-a) = 2*exp(-a)`, so `-ln(2*exp(-a)) = a - ln(2) != a`.
///
/// This is the semiring used for forward-backward scoring, N-best extraction,
/// and weight training.
///
/// ## Numerical Stability
///
/// The `log_sum_exp` helper uses the standard trick: factor out the smaller
/// value to avoid overflow/underflow. For very large differences (`|a-b| > 20`),
/// the smaller term contributes < `exp(-20) ≈ 2e-9` and is safely dropped.
#[derive(Clone, Copy)]
pub struct LogWeight(pub f64);

impl LogWeight {
    /// Create a new log weight from a raw negative-log value.
    #[inline]
    pub const fn new(value: f64) -> Self {
        LogWeight(value)
    }

    /// Get the underlying `f64` value.
    #[inline]
    pub const fn value(self) -> f64 {
        self.0
    }

    /// Create a log weight from a probability `p` in `(0, 1]`.
    ///
    /// `w = -ln(p)`. Panics if `p <= 0`.
    #[inline]
    pub fn from_probability(p: f64) -> Self {
        assert!(p > 0.0, "LogWeight::from_probability: p must be > 0, got {p}");
        LogWeight(-p.ln())
    }

    /// Convert back to a probability: `p = exp(-w)`.
    #[inline]
    pub fn to_probability(self) -> f64 {
        (-self.0).exp()
    }

    /// Numerically stable log-sum-exp: `-ln(exp(-a) + exp(-b))`.
    ///
    /// Uses the identity: `logsumexp(a, b) = min(a, b) - ln(1 + exp(-|a-b|))`.
    /// For `|a-b| > 20`, the correction term is negligible and is dropped.
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
            min_val // fast path: correction < 2e-9
        } else {
            min_val - (1.0 + (-diff).exp()).ln()
        }
    }

    /// Positive infinity (probability 0 / zero element).
    #[inline]
    pub const fn infinity() -> Self {
        LogWeight(f64::INFINITY)
    }

    /// Whether this weight is infinite (probability 0).
    #[inline]
    pub fn is_infinite(self) -> bool {
        self.0.is_infinite() && self.0.is_sign_positive()
    }
}

impl Semiring for LogWeight {
    #[inline]
    fn zero() -> Self {
        LogWeight(f64::INFINITY) // p = 0
    }

    #[inline]
    fn one() -> Self {
        LogWeight(0.0) // p = 1
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        LogWeight(Self::log_sum_exp(self.0, other.0))
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        LogWeight(self.0 + other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_infinite() && self.0.is_sign_positive()
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0 == 0.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        if self.is_zero() && other.is_zero() {
            true
        } else if self.is_zero() || other.is_zero() {
            false
        } else {
            (self.0 - other.0).abs() <= epsilon
        }
    }
}

impl fmt::Debug for LogWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "LogWeight(inf)")
        } else {
            write!(f, "LogWeight({:.4})", self.0)
        }
    }
}

impl fmt::Display for LogWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "inf")
        } else {
            write!(f, "{:.4}", self.0)
        }
    }
}

impl PartialEq for LogWeight {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == Ordering::Equal
    }
}

impl Eq for LogWeight {}

impl PartialOrd for LogWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for LogWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.total_cmp(&other.0)
    }
}

impl std::hash::Hash for LogWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl Default for LogWeight {
    fn default() -> Self {
        Self::one()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// EntropyWeight (Expectation Semiring, feature = "wfst-log")
// ══════════════════════════════════════════════════════════════════════════════

/// Expectation semiring for computing parse distribution entropy.
///
/// Based on Li & Eisner (2009), "First- and Second-Order Expectation Semirings".
///
/// **Semiring:** `(ℝ × ℝ, ⊕, ⊗, (∞, 0), (0, 0))`
///
/// The carrier set is pairs `(w, e)` where:
/// - `w` = total weight in negative log-probability space (like LogWeight)
/// - `e` = expected value accumulated under the distribution
///
/// **Operations:**
/// - `⊕ (plus)`: Combine parallel paths. For weights, `log-sum-exp(w₁, w₂)`.
///   For expectations, weighted mixture: `(p₁·e₁ + p₂·e₂) / (p₁ + p₂)` where
///   `pᵢ = exp(-wᵢ)`, computed in log-space for numerical stability.
/// - `⊗ (times)`: Sequence path segments. Weights add: `w₁ + w₂`.
///   Expectations add: `e₁ + e₂`.
/// - `0̄ = (∞, 0.0)`: No paths (zero probability, zero expectation).
/// - `1̄ = (0.0, 0.0)`: Single path with probability 1, zero expectation.
///
/// **Shannon Entropy Computation:**
/// To compute Shannon entropy H = -Σ pᵢ ln(pᵢ), set each arc's expectation
/// component `e` to the arc's negative log-probability `w`. Then after
/// forward-backward, the total expectation at the final state gives H.
///
/// **Applications:**
/// - Adaptive beam width (wider beam at high-entropy dispatch points)
/// - Grammar design feedback ("category Proc has 2.3 bits entropy at `Ident`")
/// - Training convergence criterion (stop when total entropy stabilizes)
///
/// Feature-gated behind `wfst-log`.
#[derive(Clone, Copy)]
pub struct EntropyWeight {
    /// Total weight in negative log-probability space.
    pub weight: f64,
    /// Accumulated expected value (entropy contribution).
    pub expectation: f64,
}

impl EntropyWeight {
    /// Create an EntropyWeight from weight and expectation components.
    #[inline]
    pub const fn new(weight: f64, expectation: f64) -> Self {
        EntropyWeight { weight, expectation }
    }

    /// Create an EntropyWeight for a single arc with the given weight.
    ///
    /// For Shannon entropy computation, set expectation = weight (the arc's
    /// negative log-probability). This way, after forward-backward, the total
    /// expectation gives H = -Σ pᵢ ln(pᵢ).
    #[inline]
    pub const fn from_arc_weight(weight: f64) -> Self {
        EntropyWeight { weight, expectation: weight }
    }

    /// Get the weight component.
    #[inline]
    pub const fn weight(&self) -> f64 {
        self.weight
    }

    /// Get the expectation component.
    #[inline]
    pub const fn expectation(&self) -> f64 {
        self.expectation
    }

    /// Compute entropy in bits (divide by ln(2)).
    #[inline]
    pub fn entropy_bits(&self) -> f64 {
        self.expectation / std::f64::consts::LN_2
    }

    /// Numerically stable log-sum-exp: `-ln(exp(-a) + exp(-b))`.
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

impl Semiring for EntropyWeight {
    /// Zero = (∞, 0.0): no paths, zero expectation.
    #[inline]
    fn zero() -> Self {
        EntropyWeight { weight: f64::INFINITY, expectation: 0.0 }
    }

    /// One = (0.0, 0.0): single zero-cost path, zero expectation.
    #[inline]
    fn one() -> Self {
        EntropyWeight { weight: 0.0, expectation: 0.0 }
    }

    /// Plus = combine parallel paths.
    ///
    /// Weight: `log-sum-exp(w₁, w₂)` — combines probabilities.
    /// Expectation: weighted mixture `(p₁·e₁ + p₂·e₂) / (p₁ + p₂)`.
    ///
    /// In log space: if `w₁ ≤ w₂`, then
    ///   `new_e = e₁ + softplus(w₁ - w₂) * (e₂ - e₁) / (1 + exp(w₁ - w₂))`
    /// but more stably computed as:
    ///   `new_e = (p₁·e₁ + p₂·e₂) / (p₁ + p₂)`
    /// where `pᵢ = exp(-wᵢ)`.
    fn plus(&self, other: &Self) -> Self {
        if self.weight == f64::INFINITY {
            return *other;
        }
        if other.weight == f64::INFINITY {
            return *self;
        }

        let new_weight = Self::log_sum_exp(self.weight, other.weight);

        // Compute the weighted mixture of expectations:
        //   new_e = (p_self · e_self + p_other · e_other) / (p_self + p_other)
        // where pᵢ = exp(-wᵢ).
        //
        // For numerical stability, factor out exp(-w_min) from numerator
        // and denominator, where w_min = min(w_self, w_other):
        //   p_self / p_max = exp(-(w_self - w_min))
        //   p_other / p_max = exp(-(w_other - w_min))
        //   new_e = (r_self · e_self + r_other · e_other) / (r_self + r_other)
        //
        // This is symmetric and always commutative.
        let w_min = self.weight.min(other.weight);

        let diff_self = self.weight - w_min; // ≥ 0
        let diff_other = other.weight - w_min; // ≥ 0

        if diff_self > 20.0 {
            // other dominates (self has negligible probability)
            EntropyWeight {
                weight: new_weight,
                expectation: other.expectation,
            }
        } else if diff_other > 20.0 {
            // self dominates (other has negligible probability)
            EntropyWeight {
                weight: new_weight,
                expectation: self.expectation,
            }
        } else {
            let r_self = (-diff_self).exp(); // relative probability of self
            let r_other = (-diff_other).exp(); // relative probability of other
            let denom = r_self + r_other;
            let new_expectation = (r_self * self.expectation + r_other * other.expectation) / denom;

            EntropyWeight {
                weight: new_weight,
                expectation: new_expectation,
            }
        }
    }

    /// Times = sequence path segments.
    /// Weight: `w₁ + w₂` (multiply probabilities in log space).
    /// Expectation: `e₁ + e₂` (additive over path segments).
    #[inline]
    fn times(&self, other: &Self) -> Self {
        EntropyWeight {
            weight: self.weight + other.weight,
            expectation: self.expectation + other.expectation,
        }
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.weight.is_infinite() && self.weight.is_sign_positive()
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.weight == 0.0 && self.expectation == 0.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        if self.is_zero() && other.is_zero() {
            true
        } else if self.is_zero() || other.is_zero() {
            false
        } else {
            (self.weight - other.weight).abs() <= epsilon
                && (self.expectation - other.expectation).abs() <= epsilon
        }
    }
}

impl fmt::Debug for EntropyWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "EntropyWeight(inf, 0)")
        } else {
            write!(f, "EntropyWeight({:.4}, {:.4})", self.weight, self.expectation)
        }
    }
}

impl fmt::Display for EntropyWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "(inf, 0)")
        } else {
            write!(f, "({:.4}, {:.4})", self.weight, self.expectation)
        }
    }
}

impl PartialEq for EntropyWeight {
    fn eq(&self, other: &Self) -> bool {
        self.weight.total_cmp(&other.weight) == Ordering::Equal
            && self.expectation.total_cmp(&other.expectation) == Ordering::Equal
    }
}

impl Eq for EntropyWeight {}

impl PartialOrd for EntropyWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Ordered by weight first (lower = more probable), then expectation.
impl Ord for EntropyWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        self.weight
            .total_cmp(&other.weight)
            .then_with(|| self.expectation.total_cmp(&other.expectation))
    }
}

impl std::hash::Hash for EntropyWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.weight.to_bits().hash(state);
        self.expectation.to_bits().hash(state);
    }
}

impl Default for EntropyWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for LogWeight {}

// LogWeight is NOT idempotent: plus(a, a) = a - ln(2) ≠ a
impl CompleteSemiring for LogWeight {}

impl StarSemiring for LogWeight {
    /// `star(a) = -ln(1 / (1 - exp(-a)))` for `a > 0`.
    ///
    /// In probability space: `p* = 1/(1-p)` (geometric series sum).
    /// In negative-log space: `star(a) = -ln(1/(1 - exp(-a)))`.
    /// For `a = 0` (p = 1): diverges — return zero (unreachable).
    /// For `a = +∞` (p = 0): `star(∞) = 0.0` (one) — empty path.
    fn star(&self) -> Self {
        if self.is_zero() {
            return Self::one(); // p = 0 → 1/(1-0) = 1 → -ln(1) = 0
        }
        if self.0 == 0.0 {
            return Self::zero(); // p = 1 → 1/(1-1) diverges
        }
        let p = (-self.0).exp();
        if p >= 1.0 {
            return Self::zero(); // diverges
        }
        LogWeight(-(1.0 / (1.0 - p)).ln())
    }
}

impl DetectableZero for EntropyWeight {}

// EntropyWeight is NOT idempotent (inherits from LogWeight)
impl CompleteSemiring for EntropyWeight {}

impl StarSemiring for EntropyWeight {
    /// Star for the expectation semiring. The weight component uses the
    /// LogWeight star formula. The expectation component is derived from
    /// the fixed-point equation `star(a) = 1 ⊕ a ⊗ star(a)`:
    ///
    /// Solving for `e_star`: `e_star = p · s · e` where `p = exp(-w)`,
    /// `s = 1/(1-p)`, giving `e_star = exp(-(w + star_w)) · e`.
    fn star(&self) -> Self {
        if self.weight == f64::INFINITY {
            // p = 0 → star = 1, expectation = 0
            return Self::one();
        }
        if self.weight == 0.0 {
            // p = 1 → diverges
            return Self::zero();
        }
        let p = (-self.weight).exp();
        if p >= 1.0 {
            return Self::zero();
        }
        let s = 1.0 / (1.0 - p); // geometric sum in probability space
        let star_weight = -s.ln();
        // From fixed-point: e_star = exp(-(w + star_w)) × e = p × s × e
        let star_expectation = p * s * self.expectation;
        EntropyWeight {
            weight: star_weight,
            expectation: star_expectation,
        }
    }
}
