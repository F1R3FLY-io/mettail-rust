//! Streaming weight semiring: online statistics via Welford's algorithm.
//!
//! Tracks running statistics (count, mean, M2, min, max) that can be
//! merged efficiently without storing all individual values. Based on
//! Welford (1962) "Note on a method for calculating corrected sums of
//! squares and products" and Chan et al. (1979) for parallel merge.
//!
//! ## Semiring structure
//!
//! - `⊕` = parallel merge (combine two independent streams of observations)
//! - `⊗` = sequential composition (append one stream's observations after another)
//! - `0` = empty stream (identity for merge)
//! - `1` = empty stream (identity for sequential composition)
//!
//! Note: For streaming statistics, `0 = 1 = empty stream` because:
//! - Merging with an empty stream leaves statistics unchanged (plus identity)
//! - Appending an empty stream leaves statistics unchanged (times identity)
//!
//! ## Applications
//!
//! - **Runtime monitoring**: aggregate metrics along automaton execution paths
//! - **Performance profiling**: track latency distributions per transition
//! - **Anomaly detection**: compare streaming statistics against baselines

use std::fmt;

use mettail_prattail::automata::semiring::Semiring;

/// Streaming statistics weight using Welford's online algorithm.
///
/// Maintains sufficient statistics for computing mean, variance, min, and max
/// over a stream of observations, with O(1) space and O(1) per-observation
/// update cost.
///
/// The variance can be recovered as `m2 / (count - 1)` for sample variance
/// or `m2 / count` for population variance.
#[derive(Clone, Copy, Debug)]
pub struct StreamingWeight {
    /// Number of observations in this stream.
    pub count: u64,
    /// Running mean of all observations.
    pub mean: f64,
    /// Sum of squared deviations from the mean: `Σ(xᵢ - mean)²`.
    /// Used to compute variance: `variance = m2 / (count - 1)`.
    pub m2: f64,
    /// Minimum observed value (`f64::INFINITY` if no observations).
    pub min: f64,
    /// Maximum observed value (`f64::NEG_INFINITY` if no observations).
    pub max: f64,
}

impl StreamingWeight {
    /// Create an empty streaming weight (no observations).
    #[inline]
    pub const fn empty() -> Self {
        StreamingWeight {
            count: 0,
            mean: 0.0,
            m2: 0.0,
            min: f64::INFINITY,
            max: f64::NEG_INFINITY,
        }
    }

    /// Create a streaming weight from a single observation.
    #[inline]
    pub const fn singleton(value: f64) -> Self {
        StreamingWeight {
            count: 1,
            mean: value,
            m2: 0.0,
            min: value,
            max: value,
        }
    }

    /// Add a single observation to the stream (Welford's online update).
    ///
    /// Updates count, mean, and M2 in a single pass with O(1) cost.
    #[inline]
    pub fn observe(&mut self, value: f64) {
        self.count += 1;
        let delta = value - self.mean;
        self.mean += delta / self.count as f64;
        let delta2 = value - self.mean;
        self.m2 += delta * delta2;
        if value < self.min {
            self.min = value;
        }
        if value > self.max {
            self.max = value;
        }
    }

    /// Merge two independent streams (Chan et al. parallel Welford).
    ///
    /// Combines the statistics from two independently collected streams
    /// into a single stream representing the union of all observations.
    #[inline]
    pub fn merge(&self, other: &Self) -> Self {
        if self.count == 0 {
            return *other;
        }
        if other.count == 0 {
            return *self;
        }

        let total_count = self.count + other.count;
        let delta = other.mean - self.mean;
        let new_mean = self.mean + delta * (other.count as f64 / total_count as f64);
        let new_m2 = self.m2
            + other.m2
            + delta * delta * (self.count as f64 * other.count as f64 / total_count as f64);

        StreamingWeight {
            count: total_count,
            mean: new_mean,
            m2: new_m2,
            min: self.min.min(other.min),
            max: self.max.max(other.max),
        }
    }

    /// Compute the population variance: `M2 / count`.
    ///
    /// Returns `0.0` if `count == 0`.
    #[inline]
    pub fn population_variance(&self) -> f64 {
        if self.count == 0 {
            0.0
        } else {
            self.m2 / self.count as f64
        }
    }

    /// Compute the sample variance: `M2 / (count - 1)`.
    ///
    /// Returns `0.0` if `count < 2`.
    #[inline]
    pub fn sample_variance(&self) -> f64 {
        if self.count < 2 {
            0.0
        } else {
            self.m2 / (self.count - 1) as f64
        }
    }

    /// Compute the population standard deviation.
    #[inline]
    pub fn population_stddev(&self) -> f64 {
        self.population_variance().sqrt()
    }

    /// Compute the sample standard deviation.
    #[inline]
    pub fn sample_stddev(&self) -> f64 {
        self.sample_variance().sqrt()
    }

    /// The range of observed values: `max - min`.
    ///
    /// Returns `0.0` if no observations.
    #[inline]
    pub fn range(&self) -> f64 {
        if self.count == 0 {
            0.0
        } else {
            self.max - self.min
        }
    }
}

impl Semiring for StreamingWeight {
    /// Zero = empty stream (identity for parallel merge).
    #[inline]
    fn zero() -> Self {
        Self::empty()
    }

    /// One = empty stream (identity for sequential composition).
    #[inline]
    fn one() -> Self {
        Self::empty()
    }

    /// Plus = parallel merge of two independent observation streams.
    #[inline]
    fn plus(&self, other: &Self) -> Self {
        self.merge(other)
    }

    /// Times = sequential composition (same as merge for streaming stats,
    /// since the combined statistics are order-independent).
    #[inline]
    fn times(&self, other: &Self) -> Self {
        self.merge(other)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.count == 0
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.count == 0
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        if self.count != other.count {
            return false;
        }
        if self.count == 0 && other.count == 0 {
            return true;
        }
        (self.mean - other.mean).abs() <= epsilon
            && (self.m2 - other.m2).abs() <= epsilon
            && (self.min - other.min).abs() <= epsilon
            && (self.max - other.max).abs() <= epsilon
    }
}

impl PartialEq for StreamingWeight {
    fn eq(&self, other: &Self) -> bool {
        self.count == other.count
            && self.mean.to_bits() == other.mean.to_bits()
            && self.m2.to_bits() == other.m2.to_bits()
            && self.min.to_bits() == other.min.to_bits()
            && self.max.to_bits() == other.max.to_bits()
    }
}

impl Eq for StreamingWeight {}

impl std::hash::Hash for StreamingWeight {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.count.hash(state);
        self.mean.to_bits().hash(state);
        self.m2.to_bits().hash(state);
        self.min.to_bits().hash(state);
        self.max.to_bits().hash(state);
    }
}

impl fmt::Display for StreamingWeight {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.count == 0 {
            write!(f, "StreamingWeight(empty)")
        } else {
            write!(
                f,
                "StreamingWeight(n={}, mean={:.4}, var={:.4}, range=[{:.4}, {:.4}])",
                self.count,
                self.mean,
                self.population_variance(),
                self.min,
                self.max,
            )
        }
    }
}

impl Default for StreamingWeight {
    fn default() -> Self {
        Self::empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_is_zero_and_one() {
        let e = StreamingWeight::empty();
        assert!(e.is_zero());
        assert!(e.is_one());
    }

    #[test]
    fn test_singleton() {
        let s = StreamingWeight::singleton(42.0);
        assert_eq!(s.count, 1);
        assert!((s.mean - 42.0).abs() < 1e-10);
        assert!((s.m2 - 0.0).abs() < 1e-10);
        assert!((s.min - 42.0).abs() < 1e-10);
        assert!((s.max - 42.0).abs() < 1e-10);
    }

    #[test]
    fn test_observe_sequence() {
        let mut sw = StreamingWeight::empty();
        sw.observe(2.0);
        sw.observe(4.0);
        sw.observe(6.0);
        assert_eq!(sw.count, 3);
        assert!((sw.mean - 4.0).abs() < 1e-10, "mean = {}", sw.mean);
        // Population variance of {2, 4, 6} = ((2-4)^2 + (4-4)^2 + (6-4)^2) / 3 = 8/3
        let expected_var = 8.0 / 3.0;
        assert!(
            (sw.population_variance() - expected_var).abs() < 1e-10,
            "pop_var = {}",
            sw.population_variance()
        );
        assert!((sw.min - 2.0).abs() < 1e-10);
        assert!((sw.max - 6.0).abs() < 1e-10);
    }

    #[test]
    fn test_merge_equals_sequential() {
        // Build stream A from [1, 2, 3]
        let mut a = StreamingWeight::empty();
        a.observe(1.0);
        a.observe(2.0);
        a.observe(3.0);

        // Build stream B from [4, 5]
        let mut b = StreamingWeight::empty();
        b.observe(4.0);
        b.observe(5.0);

        // Merge
        let merged = a.merge(&b);

        // Build sequential from [1, 2, 3, 4, 5]
        let mut seq = StreamingWeight::empty();
        for v in &[1.0, 2.0, 3.0, 4.0, 5.0] {
            seq.observe(*v);
        }

        assert_eq!(merged.count, seq.count);
        assert!(
            (merged.mean - seq.mean).abs() < 1e-10,
            "merged.mean={}, seq.mean={}",
            merged.mean,
            seq.mean
        );
        assert!((merged.m2 - seq.m2).abs() < 1e-10, "merged.m2={}, seq.m2={}", merged.m2, seq.m2);
        assert!((merged.min - seq.min).abs() < 1e-10);
        assert!((merged.max - seq.max).abs() < 1e-10);
    }

    #[test]
    fn test_zero_identity_for_plus() {
        let a = StreamingWeight::singleton(7.0);
        let sum = a.plus(&StreamingWeight::zero());
        assert_eq!(sum.count, a.count);
        assert!((sum.mean - a.mean).abs() < 1e-10);
    }

    #[test]
    fn test_one_identity_for_times() {
        let a = StreamingWeight::singleton(7.0);
        let prod = a.times(&StreamingWeight::one());
        assert_eq!(prod.count, a.count);
        assert!((prod.mean - a.mean).abs() < 1e-10);
    }

    #[test]
    fn test_range() {
        let mut sw = StreamingWeight::empty();
        sw.observe(10.0);
        sw.observe(20.0);
        sw.observe(15.0);
        assert!((sw.range() - 10.0).abs() < 1e-10);
    }

    #[test]
    fn test_sample_variance() {
        let mut sw = StreamingWeight::empty();
        sw.observe(2.0);
        sw.observe(4.0);
        sw.observe(6.0);
        // Sample variance of {2, 4, 6} = 8/2 = 4.0
        assert!(
            (sw.sample_variance() - 4.0).abs() < 1e-10,
            "sample_var = {}",
            sw.sample_variance()
        );
    }
}
