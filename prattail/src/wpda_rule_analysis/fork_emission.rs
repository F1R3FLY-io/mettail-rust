//! Original fork-emission descriptor accumulator, shared without a new derivation.
//!
//! Equal-position observations retain the first bucket tag. A differing position
//! moves the row into the ambiguous map; later observations append there without
//! deduplication. The two ordered maps and their diagnostic history are preserved
//! by `into_parts`. These positions remain census data, not election evidence.
//!
//! `ForkEmissionAccumulatorProjection.v` models the concrete recording branches,
//! ordered readbacks, disjointness and ownership transfer. Callers retain the
//! original `usize` capacity and allocation preconditions.

use std::collections::BTreeMap;

/// One derived site-2 row: the rule's initiating-branch static declaration
/// position within its dispatch bucket.
#[derive(Debug, Clone)]
pub struct ForkEmissionOrdinalRow {
    pub emission_ordinal: u16,
    /// Human-readable bucket identity for collision diagnostics (the
    /// bucket's token pattern + guard, or a site label).
    pub bucket_tag: String,
}

/// The original per-grammar fork-emission ordinal accumulator.
///
/// Emitters record their actual declaration positions here; this model never
/// re-derives them from grammar syntax. Recording ambiguity changes the census,
/// not the parser election policy. Token emission remains with the caller.
#[derive(Debug, Default)]
pub struct ForkEmissionOrdinalModel {
    /// `(category_src_idx, rule_index_in_category) -> row`, ordered for
    /// deterministic emission (BTreeMap — the generated match arms must be
    /// byte-stable across builds).
    site2_rows: BTreeMap<(u16, u16), ForkEmissionOrdinalRow>,
    /// Option A: rules whose initiating branch position DIFFERS across
    /// dispatch buckets — classified ambiguous, moved OUT of `site2_rows`
    /// (they resolve through the site-2 fallback `0`), with every observed
    /// `bucket-tag@position` retained for the doc comment + diagnostics.
    ambiguous_multi_bucket: BTreeMap<(u16, u16), Vec<String>>,
}

impl ForkEmissionOrdinalModel {
    pub fn new() -> Self {
        Self::default()
    }

    /// Record one site-2 row at the rule's static declaration position.
    ///
    /// Amendment-6 detection, Option-A resolution (coordinator decision
    /// 2026-07-14): each `(cat, rule)` keeps AT MOST ONE derived row —
    ///   - first observation: the row is recorded;
    ///   - an equal-position duplicate (the same rule reachable through
    ///     another bucket at the SAME declared position): dedups silently
    ///     to the single row (no ambiguity — the static position IS
    ///     single-valued);
    ///   - a DIFFERING-position observation: the rule is reclassified
    ///     AMBIGUOUS-MULTI-BUCKET — its row is REMOVED (it joins the
    ///     underived remainder = the fallback `0`, today's trait-default
    ///     value, zero K-C movement) and every colliding `bucket@position`
    ///     is retained for the generated doc comment + the codegen
    ///     diagnostic line. No panic (probe P7: shipped grammars collide
    ///     legitimately via per-FIRST-token projection dispatch), and no
    ///     guessed ordinal.
    pub fn record_site2_row(
        &mut self,
        category_src_idx: u16,
        rule_index_in_category: u16,
        emission_ordinal: u16,
        bucket_tag: &str,
    ) {
        let key = (category_src_idx, rule_index_in_category);
        if let Some(tags) = self.ambiguous_multi_bucket.get_mut(&key) {
            // Already ambiguous: retain the additional observation.
            tags.push(format!("{bucket_tag}@{emission_ordinal}"));
            return;
        }
        match self.site2_rows.get(&key) {
            Some(existing) if existing.emission_ordinal != emission_ordinal => {
                let removed = self
                    .site2_rows
                    .remove(&key)
                    .expect("the just-matched row is present");
                self.ambiguous_multi_bucket.insert(
                    key,
                    vec![
                        format!("{}@{}", removed.bucket_tag, removed.emission_ordinal),
                        format!("{bucket_tag}@{emission_ordinal}"),
                    ],
                );
            },
            Some(_) => {}, // equal-position duplicate: one row.
            None => {
                self.site2_rows.insert(
                    key,
                    ForkEmissionOrdinalRow {
                        emission_ordinal,
                        bucket_tag: bucket_tag.to_string(),
                    },
                );
            },
        }
    }

    /// Number of derived (single-valued) site-2 rows.
    pub fn site2_row_count(&self) -> usize {
        self.site2_rows.len()
    }

    /// Number of ambiguous-multi-bucket rules (fallback-resolved).
    pub fn ambiguous_rule_count(&self) -> usize {
        self.ambiguous_multi_bucket.len()
    }

    /// readback of a derived ordinal (`None` = underived,
    /// including the ambiguous class).
    pub fn site2_ordinal(&self, cat: u16, rule: u16) -> Option<u16> {
        self.site2_rows
            .get(&(cat, rule))
            .map(|r| r.emission_ordinal)
    }

    /// readback of the ambiguous classification.
    pub fn is_ambiguous_multi_bucket(&self, cat: u16, rule: u16) -> bool {
        self.ambiguous_multi_bucket.contains_key(&(cat, rule))
    }

    /// census DOMAIN: every `(cat, rule)` key the emitters
    /// recorded: derived keys followed by ambiguous-multi-bucket keys. The F1
    /// value-identity units iterate exactly this domain (per the
    /// coordinator requirement: derive the domain from the census, don't
    /// sample blindly).
    pub fn census_keys(&self) -> Vec<(u16, u16)> {
        let mut keys: Vec<(u16, u16)> =
            Vec::with_capacity(self.site2_rows.len() + self.ambiguous_multi_bucket.len());
        keys.extend(self.site2_rows.keys().copied());
        keys.extend(self.ambiguous_multi_bucket.keys().copied());
        keys
    }

    /// Move both original maps to the caller without sorting or reconstruction.
    pub fn into_parts(self) -> ForkEmissionOrdinalParts {
        (self.site2_rows, self.ambiguous_multi_bucket)
    }
}

/// Owned original maps, in derived-then-ambiguous order.
pub type ForkEmissionOrdinalParts =
    (BTreeMap<(u16, u16), ForkEmissionOrdinalRow>, BTreeMap<(u16, u16), Vec<String>>);
