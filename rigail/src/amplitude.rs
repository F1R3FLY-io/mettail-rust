use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// AmplitudeWeight — Complex Amplitude Semiring (feature: quantum)
// ══════════════════════════════════════════════════════════════════════════════

/// Complex-amplitude semiring `(ℂ, +, ×, 0+0i, 1+0i)` for quantum CTMC
/// simulation.
///
/// **Algebra:**
/// - `plus` (parallel): complex addition — models quantum interference
/// - `times` (sequential): complex multiplication — models sequential amplitude
///   composition
/// - `zero`: `0 + 0i` — no amplitude (unreachable state)
/// - `one`: `1 + 0i` — unit amplitude (identity for composition)
///
/// This is technically a ring (additive inverses exist: `-z`), but satisfies
/// all `Semiring` trait requirements.
///
/// **Properties:**
/// - NOT idempotent: `z + z = 2z ≠ z` in general
/// - NOT a star semiring: geometric series diverges for `|z| ≥ 1`
/// - NOT complete: infinite sums do not generally converge
///
/// **Measurement (Born rule):** `|z|² = re² + im²` gives the classical
/// observation probability. Use [`norm_sqr()`](Self::norm_sqr) or
/// [`to_probability()`](Self::to_probability).
///
/// **Ordering:** By `norm_sqr()` (Born rule probability), *reversed* so that
/// higher probability = "better" (lower in `Ord`), matching the convention
/// used by `ViterbiWeight`.
///
/// **Caveat:** Viterbi path selection does not apply directly to quantum
/// lattices because amplitude interference can cause cancellation. Use full
/// forward propagation followed by Born-rule measurement, or pair with a
/// classical priority channel via `ProductWeight<AmplitudeWeight, TropicalWeight>`.
#[derive(Clone, Copy)]
pub struct AmplitudeWeight(pub num_complex::Complex64);

impl AmplitudeWeight {
    /// Create an amplitude weight from real and imaginary parts.
    #[inline]
    pub fn new(re: f64, im: f64) -> Self {
        AmplitudeWeight(num_complex::Complex64::new(re, im))
    }

    /// Squared magnitude (Born rule): `|z|² = re² + im²`.
    #[inline]
    pub fn norm_sqr(self) -> f64 {
        self.0.norm_sqr()
    }

    /// Create from a classical probability `p ∈ [0, 1]`.
    ///
    /// Produces a real amplitude `√p + 0i` whose Born rule gives `p`.
    #[inline]
    pub fn from_probability(p: f64) -> Self {
        debug_assert!(
            (0.0..=1.0).contains(&p),
            "AmplitudeWeight::from_probability: p must be in [0, 1], got {p}"
        );
        AmplitudeWeight(num_complex::Complex64::new(p.sqrt(), 0.0))
    }

    /// Collapse to classical probability via the Born rule: `|z|²`.
    #[inline]
    pub fn to_probability(self) -> f64 {
        self.0.norm_sqr()
    }
}

/// Convert from a `LogWeight` (negative log-probability) to a real amplitude.
///
/// `AmplitudeWeight(√exp(-w) + 0i)` = `AmplitudeWeight(exp(-w/2) + 0i)`.
/// The resulting amplitude's Born rule gives `exp(-w)`, the original probability.
impl AmplitudeWeight {
    #[inline]
    pub fn from_log_weight(w: LogWeight) -> Self {
        if w.is_zero() {
            AmplitudeWeight::zero()
        } else {
            AmplitudeWeight(num_complex::Complex64::new((-w.value() / 2.0).exp(), 0.0))
        }
    }
}

impl Semiring for AmplitudeWeight {
    #[inline]
    fn zero() -> Self {
        AmplitudeWeight(num_complex::Complex64::new(0.0, 0.0))
    }

    #[inline]
    fn one() -> Self {
        AmplitudeWeight(num_complex::Complex64::new(1.0, 0.0))
    }

    #[inline]
    fn plus(&self, other: &Self) -> Self {
        AmplitudeWeight(self.0 + other.0)
    }

    #[inline]
    fn times(&self, other: &Self) -> Self {
        AmplitudeWeight(self.0 * other.0)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.re == 0.0 && self.0.im == 0.0
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.0.re == 1.0 && self.0.im == 0.0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        (self.0.re - other.0.re).abs() <= epsilon && (self.0.im - other.0.im).abs() <= epsilon
    }
}

impl fmt::Debug for AmplitudeWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AmplitudeWeight({:+.4}{:+.4}i)", self.0.re, self.0.im)
    }
}

impl fmt::Display for AmplitudeWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:+.4}{:+.4}i", self.0.re, self.0.im)
    }
}

impl PartialEq for AmplitudeWeight {
    fn eq(&self, other: &Self) -> bool {
        self.0.re.total_cmp(&other.0.re) == Ordering::Equal
            && self.0.im.total_cmp(&other.0.im) == Ordering::Equal
    }
}

impl Eq for AmplitudeWeight {}

impl PartialOrd for AmplitudeWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Higher Born-rule probability = "better" (lower in ordering).
/// Reversed so generic min-based algorithms select highest probability.
/// Ties broken by real part then imaginary part for determinism.
impl Ord for AmplitudeWeight {
    fn cmp(&self, other: &Self) -> Ordering {
        let self_norm = self.0.norm_sqr();
        let other_norm = other.0.norm_sqr();
        // Reverse: higher norm² = "lower" (better)
        match other_norm.total_cmp(&self_norm) {
            Ordering::Equal => {
                // Tiebreak: real part then imaginary part (ascending)
                match self.0.re.total_cmp(&other.0.re) {
                    Ordering::Equal => self.0.im.total_cmp(&other.0.im),
                    ord => ord,
                }
            },
            ord => ord,
        }
    }
}

impl std::hash::Hash for AmplitudeWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.re.to_bits().hash(state);
        self.0.im.to_bits().hash(state);
    }
}

impl Default for AmplitudeWeight {
    fn default() -> Self {
        Self::one()
    }
}

impl DetectableZero for AmplitudeWeight {}
