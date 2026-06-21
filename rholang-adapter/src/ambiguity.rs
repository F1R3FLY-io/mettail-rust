//! Ambiguity witness collection for MeTTaIL's Rho backend.
//!
//! RSpace is free to choose the order in which enabled communications fire.
//! That scheduler choice must not choose away semantic alternatives. Generated
//! Rho backends therefore represent ambiguity as explicit witness facts keyed
//! by exact semantic identity. Disabled/refuted alternatives are absent;
//! enabled alternatives are inserted idempotently; duplicate keys are accepted
//! only when they carry the same payload.

use std::collections::BTreeMap;

/// One possible semantic alternative exposed by a Rho backend.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AmbiguityCandidate<K, V> {
    /// Exact semantic identity for the alternative.
    pub key: K,
    /// Caller-owned witness payload for observation or continuation handoff.
    pub value: V,
    /// Disabled candidates are not observable alternatives.
    pub enabled: bool,
}

impl<K, V> AmbiguityCandidate<K, V> {
    /// Construct an enabled ambiguity witness.
    pub fn enabled(key: K, value: V) -> Self {
        Self { key, value, enabled: true }
    }

    /// Construct a disabled ambiguity witness.
    pub fn disabled(key: K, value: V) -> Self {
        Self { key, value, enabled: false }
    }
}

/// A conflict between exact-key identity and witness payload.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AmbiguityWitnessConflict<K> {
    /// The key whose payload was not unique.
    pub key: K,
}

/// Exact-key ambiguity observation set.
#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AmbiguityWitnessSet<K, V> {
    witnesses: BTreeMap<K, V>,
}

impl<K, V> Default for AmbiguityWitnessSet<K, V> {
    fn default() -> Self {
        Self { witnesses: BTreeMap::new() }
    }
}

impl<K: Ord, V: Eq> AmbiguityWitnessSet<K, V> {
    /// Insert one enabled witness, accepting exact duplicates idempotently.
    ///
    /// A duplicate key with a different payload is rejected instead of silently
    /// overwriting one semantic alternative with another.
    pub fn insert(&mut self, key: K, value: V) -> Result<(), AmbiguityWitnessConflict<K>>
    where
        K: Clone,
    {
        if let Some(existing) = self.witnesses.get(&key) {
            if existing == &value {
                return Ok(());
            }
            return Err(AmbiguityWitnessConflict { key });
        }

        self.witnesses.insert(key, value);
        Ok(())
    }

    /// Observe candidates in a particular scheduler order.
    pub fn observe_schedule<I>(candidates: I) -> Result<Self, AmbiguityWitnessConflict<K>>
    where
        I: IntoIterator<Item = AmbiguityCandidate<K, V>>,
        K: Clone,
    {
        let mut set = Self::default();
        for candidate in candidates {
            if candidate.enabled {
                set.insert(candidate.key, candidate.value)?;
            }
        }
        Ok(set)
    }

    pub fn len(&self) -> usize {
        self.witnesses.len()
    }

    pub fn is_empty(&self) -> bool {
        self.witnesses.is_empty()
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        self.witnesses.get(key)
    }

    pub fn contains_key(&self, key: &K) -> bool {
        self.witnesses.contains_key(key)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.witnesses.iter()
    }

    pub fn into_inner(self) -> BTreeMap<K, V> {
        self.witnesses
    }
}

/// Collect every enabled ambiguity witness, preserving exact-key uniqueness.
pub fn collect_enabled_ambiguity_witnesses<K, V>(
    candidates: impl IntoIterator<Item = AmbiguityCandidate<K, V>>,
) -> Result<AmbiguityWitnessSet<K, V>, AmbiguityWitnessConflict<K>>
where
    K: Clone + Ord,
    V: Eq,
{
    AmbiguityWitnessSet::observe_schedule(candidates)
}

/// Relational predicate for whether an enabled witness appears in the observed set.
pub fn ambiguity_observes_key<K, V>(candidates: &[AmbiguityCandidate<K, V>], key: &K) -> bool
where
    K: Clone + Ord,
    V: Eq + Clone,
{
    collect_enabled_ambiguity_witnesses(candidates.iter().cloned())
        .is_ok_and(|set| set.contains_key(key))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn observed(
        candidates: Vec<AmbiguityCandidate<&'static str, &'static str>>,
    ) -> BTreeMap<&'static str, &'static str> {
        collect_enabled_ambiguity_witnesses(candidates)
            .expect("test witnesses must be conflict-free")
            .into_inner()
    }

    #[test]
    fn collects_every_enabled_witness() {
        let witnesses = observed(vec![
            AmbiguityCandidate::enabled("a", "left branch"),
            AmbiguityCandidate::disabled("b", "refuted branch"),
            AmbiguityCandidate::enabled("c", "right branch"),
        ]);

        assert_eq!(witnesses.len(), 2);
        assert_eq!(witnesses.get("a"), Some(&"left branch"));
        assert_eq!(witnesses.get("c"), Some(&"right branch"));
        assert!(!witnesses.contains_key("b"));
    }

    #[test]
    fn schedule_order_preserves_observed_witness_set() {
        let left = observed(vec![
            AmbiguityCandidate::enabled("a", "left branch"),
            AmbiguityCandidate::enabled("b", "right branch"),
            AmbiguityCandidate::enabled("c", "fallback branch"),
        ]);
        let right = observed(vec![
            AmbiguityCandidate::enabled("c", "fallback branch"),
            AmbiguityCandidate::enabled("a", "left branch"),
            AmbiguityCandidate::enabled("b", "right branch"),
        ]);

        assert_eq!(left, right);
    }

    #[test]
    fn exact_duplicate_witness_is_idempotent() {
        let witnesses = observed(vec![
            AmbiguityCandidate::enabled("a", "branch"),
            AmbiguityCandidate::enabled("a", "branch"),
        ]);

        assert_eq!(witnesses.len(), 1);
        assert_eq!(witnesses.get("a"), Some(&"branch"));
    }

    #[test]
    fn duplicate_key_with_different_payload_is_rejected() {
        let conflict = collect_enabled_ambiguity_witnesses(vec![
            AmbiguityCandidate::enabled("a", "branch-1"),
            AmbiguityCandidate::enabled("a", "branch-2"),
        ])
        .expect_err("conflicting exact-key payloads must reject");

        assert_eq!(conflict, AmbiguityWitnessConflict { key: "a" });
    }

    #[test]
    fn disabled_conflicting_payload_is_ignored() {
        let witnesses = observed(vec![
            AmbiguityCandidate::enabled("a", "branch"),
            AmbiguityCandidate::disabled("a", "refuted-conflict"),
        ]);

        assert_eq!(witnesses.len(), 1);
        assert_eq!(witnesses.get("a"), Some(&"branch"));
    }

    #[test]
    fn observes_key_only_when_enabled_and_conflict_free() {
        let candidates = vec![
            AmbiguityCandidate::enabled("a", "branch"),
            AmbiguityCandidate::disabled("b", "refuted"),
        ];

        assert!(ambiguity_observes_key(&candidates, &"a"));
        assert!(!ambiguity_observes_key(&candidates, &"b"));
        assert!(!ambiguity_observes_key(&candidates, &"missing"));

        let conflicting = vec![
            AmbiguityCandidate::enabled("a", "branch-1"),
            AmbiguityCandidate::enabled("a", "branch-2"),
        ];
        assert!(!ambiguity_observes_key(&conflicting, &"a"));
    }
}
