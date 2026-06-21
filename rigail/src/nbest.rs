use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// NbestWeight (Viterbi-N-Best Semiring)
// ══════════════════════════════════════════════════════════════════════════════

/// A single entry in the N-best list: (path_id, weight).
///
/// `path_id` identifies which derivation this entry represents.
/// `weight` is the TropicalWeight cost. Lower = better.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct NbestEntry {
    /// Identifier for the derivation path.
    pub path_id: u32,
    /// Cost of this path (tropical weight).
    pub weight: TropicalWeight,
}

impl NbestEntry {
    /// Create a new N-best entry.
    #[inline]
    pub const fn new(path_id: u32, weight: TropicalWeight) -> Self {
        NbestEntry { path_id, weight }
    }
}

/// Viterbi-N-Best semiring with a fixed-size bounded array.
///
/// **Semiring:** `(Sorted[N], merge_nbest, concat_nbest, [], [(0, 0.0)])`
///
/// Tracks the N best alternative parses simultaneously. Each entry is a
/// `(path_id, TropicalWeight)` pair sorted by weight (lowest = best).
///
/// - `⊕ (plus)` = merge two sorted arrays, keep top N by weight
/// - `⊗ (times)` = cross-product of entries (add weights, combine path IDs),
///   keep top N
/// - `0̄` = empty array (no paths)
/// - `1̄` = single entry `(0, 0.0)` (one zero-cost path)
///
/// **Applications:**
/// - Lazy disambiguation: try best; if fails, fall back to 2nd-best
/// - Confidence scoring: large gap between #1 and #2 → commit immediately
/// - Parse forest construction: N-best paths form compact forest
///
/// The const generic `N` controls how many alternatives are tracked.
/// Common values: `N = 4` (parse forest), `N = 2` (confidence gap).
///
/// **Copy compliance:** Uses `[Option<NbestEntry>; N]` with fixed-size array,
/// satisfying the `Copy` bound on `Semiring`. The `Option` wrapper allows
/// sparse arrays (fewer than N entries).
#[derive(Clone, Copy, Debug)]
pub struct NbestWeight<const N: usize> {
    /// Sorted entries: `entries[0]` is best (lowest weight).
    /// `None` values are at the end (the array is packed).
    entries: [Option<NbestEntry>; N],
    /// Number of valid entries (count of `Some` values).
    len: usize,
}

impl<const N: usize> NbestWeight<N> {
    /// Create an empty N-best weight (zero element).
    #[inline]
    pub const fn empty() -> Self {
        NbestWeight { entries: [None; N], len: 0 }
    }

    /// Create an N-best weight with a single entry.
    pub fn singleton(path_id: u32, weight: TropicalWeight) -> Self {
        let mut entries = [None; N];
        entries[0] = Some(NbestEntry::new(path_id, weight));
        NbestWeight { entries, len: 1 }
    }

    /// Create from a slice of entries (sorts and truncates to N).
    pub fn from_entries(mut input: Vec<NbestEntry>) -> Self {
        input.sort_by_key(|entry| entry.weight);
        input.dedup_by(|a, b| a.path_id == b.path_id);
        let mut entries = [None; N];
        let len = input.len().min(N);
        for (i, entry) in input.into_iter().take(N).enumerate() {
            entries[i] = Some(entry);
        }
        NbestWeight { entries, len }
    }

    /// Number of valid entries.
    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Whether this is empty (zero element).
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Get the i-th best entry (0-indexed).
    #[inline]
    pub const fn get(&self, index: usize) -> Option<&NbestEntry> {
        if index < self.len {
            self.entries[index].as_ref()
        } else {
            None
        }
    }

    /// Get the best (lowest-weight) entry.
    #[inline]
    pub const fn best(&self) -> Option<&NbestEntry> {
        self.get(0)
    }

    /// Get the weight gap between the best and second-best entries.
    ///
    /// A large gap indicates high confidence in the best parse.
    /// Returns `f64::INFINITY` if fewer than 2 entries.
    pub fn confidence_gap(&self) -> f64 {
        match (self.get(0), self.get(1)) {
            (Some(best), Some(second)) => second.weight.value() - best.weight.value(),
            _ => f64::INFINITY,
        }
    }

    /// Iterate over valid entries.
    pub fn iter(&self) -> impl Iterator<Item = &NbestEntry> {
        self.entries[..self.len].iter().filter_map(|e| e.as_ref())
    }

    /// Merge two sorted N-best lists, keeping the top N by weight.
    /// Deduplicates by path_id (keeps the lower-weight occurrence).
    fn merge_nbest(&self, other: &Self) -> Self {
        let mut merged: [Option<NbestEntry>; N] = [None; N];
        let mut count = 0;
        let mut i = 0;
        let mut j = 0;

        // Two-pointer merge of sorted arrays
        while count < N && (i < self.len || j < other.len) {
            let take_self = if i >= self.len {
                false
            } else if j >= other.len {
                true
            } else {
                let a = self.entries[i].as_ref().expect("valid entry at i");
                let b = other.entries[j].as_ref().expect("valid entry at j");
                a.weight <= b.weight
            };

            let entry = if take_self {
                let e = self.entries[i].expect("valid entry at i");
                i += 1;
                e
            } else {
                let e = other.entries[j].expect("valid entry at j");
                j += 1;
                e
            };

            // Dedup: skip if this path_id is already in merged
            let is_dup = merged[..count]
                .iter()
                .any(|m| m.is_some_and(|m| m.path_id == entry.path_id));
            if !is_dup {
                merged[count] = Some(entry);
                count += 1;
            }
        }

        NbestWeight { entries: merged, len: count }
    }

    /// Cross-product of two N-best lists: combine each pair (add weights,
    /// combine path IDs via XOR hash), keep top N results.
    fn concat_nbest(&self, other: &Self) -> Self {
        if self.is_empty() || other.is_empty() {
            return Self::empty();
        }

        // Collect all cross-product entries
        // Capacity: at most self.len * other.len, capped at N
        let mut candidates: Vec<NbestEntry> = Vec::with_capacity(self.len * other.len);
        for a in self.iter() {
            for b in other.iter() {
                let combined_weight = a.weight.times(&b.weight);
                // Combine path IDs: use a hash-like combination
                // Wrapping multiply + XOR gives good distribution
                let combined_id = a.path_id.wrapping_mul(31).wrapping_add(b.path_id);
                candidates.push(NbestEntry::new(combined_id, combined_weight));
            }
        }

        Self::from_entries(candidates)
    }
}

impl<const N: usize> Semiring for NbestWeight<N> {
    /// Zero = empty array (no paths).
    #[inline]
    fn zero() -> Self {
        Self::empty()
    }

    /// One = single entry (path 0, weight 0.0).
    #[inline]
    fn one() -> Self {
        Self::singleton(0, TropicalWeight::one())
    }

    /// Plus = merge two N-best lists, keep top N.
    #[inline]
    fn plus(&self, other: &Self) -> Self {
        self.merge_nbest(other)
    }

    /// Times = cross-product, keep top N.
    #[inline]
    fn times(&self, other: &Self) -> Self {
        self.concat_nbest(other)
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.is_empty()
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.len == 1 && self.entries[0].is_some_and(|e| e.path_id == 0 && e.weight.is_one())
    }

    fn approx_eq(&self, other: &Self, epsilon: f64) -> bool {
        if self.len != other.len {
            return false;
        }
        for i in 0..self.len {
            match (self.entries[i], other.entries[i]) {
                (Some(a), Some(b)) => {
                    if a.path_id != b.path_id || !a.weight.approx_eq(&b.weight, epsilon) {
                        return false;
                    }
                },
                (None, None) => {},
                _ => return false,
            }
        }
        true
    }
}

impl<const N: usize> PartialEq for NbestWeight<N> {
    fn eq(&self, other: &Self) -> bool {
        if self.len != other.len {
            return false;
        }
        for i in 0..self.len {
            if self.entries[i] != other.entries[i] {
                return false;
            }
        }
        true
    }
}

impl<const N: usize> Eq for NbestWeight<N> {}

impl<const N: usize> PartialOrd for NbestWeight<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Ordered by the best (first) entry's weight. Empty (zero) is worst.
impl<const N: usize> Ord for NbestWeight<N> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.best(), other.best()) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Greater, // empty = worst
            (Some(_), None) => Ordering::Less,
            (Some(a), Some(b)) => a
                .weight
                .cmp(&b.weight)
                .then_with(|| self.len.cmp(&other.len)),
        }
    }
}

impl<const N: usize> std::hash::Hash for NbestWeight<N> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.len.hash(state);
        for i in 0..self.len {
            self.entries[i].hash(state);
        }
    }
}

impl<const N: usize> fmt::Display for NbestWeight<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for i in 0..self.len {
            if i > 0 {
                write!(f, ", ")?;
            }
            if let Some(e) = &self.entries[i] {
                write!(f, "({}:{:.1})", e.path_id, e.weight.value())?;
            }
        }
        write!(f, "]")
    }
}

impl<const N: usize> Default for NbestWeight<N> {
    fn default() -> Self {
        Self::one()
    }
}

impl<const N: usize> DetectableZero for NbestWeight<N> {}
