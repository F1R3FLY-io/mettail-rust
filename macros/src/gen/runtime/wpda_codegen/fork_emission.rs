//! Task #10 item 1 (ledger `s2_stageA_ledger.md` :968-970 / :1000-1004 /
//! :1048-1056): the PER-GRAMMAR GENERATED `fork_emission_ordinal` table —
//! the K-C election tiebreak's ordinal source, replacing the walker-trait
//! default (`0|2 => 0, 1|3 => 1, _ => MAX`) for generated engines.
//!
//! Semantics (red-team amendment 6, as refined by the coordinator's
//! Option-A decision after probe P7 fired): a site-2 value is the
//! initiating branch's STATIC DECLARATION POSITION within its dispatch
//! bucket — the index of the branch in the emitter's declaration order,
//! counting runtime-gated slots (the CrossCatLhs push is runtime-gated but
//! occupies its declared position); the no-fork singleton fast path has no
//! peer branches, so its rules get 0.
//!
//! ★ MULTI-BUCKET AMBIGUITY (P7 answered AFFIRMATIVELY — Option A,
//! coordinator decision 2026-07-14): a rule can legitimately be initiated
//! from SEVERAL dispatch buckets (`CrossCatProjection` descriptors are
//! inserted once per token of FIRST(source)), and its declaration position
//! generally DIFFERS per bucket. The `(site_kind, cat, rule)` key space
//! cannot represent a per-bucket position — the walker's realize-time
//! site-2 query has no dispatch-token context — so such a rule has NO
//! well-defined static ordinal. Policy: the rule is classified
//! AMBIGUOUS-MULTI-BUCKET and joins the UNDERIVED REMAINDER (the site-2
//! fallback `0` = the walker-trait default's site-2 value — zero K-C
//! movement for the ambiguous class, byte-identical to the pre-table
//! behavior). No silent wrong ordinal can exist: ambiguous rules get NO
//! derived ordinal, not a guessed one. Detection stays LOUD-BUT-NONFATAL:
//! the ambiguous count + each rule's colliding bucket names go into the
//! generated table's doc comment AND a codegen diagnostic line. (A
//! dispatch-context-keyed table could derive exact per-bucket ordinals —
//! recorded as a ledger boundary note in §"#10 item-1", deliberately not a
//! code TODO.)
//!
//! Derivation discipline: rows are recorded BY THE EMITTERS as they emit
//! (`prefix::emit_unified_arm`, `prefix::emit_paren_dispatch_arms`, the
//! binder.rs optional-group constants) — never re-derived from the grammar
//! model — so the table can never diverge from what is actually emitted.
//! The S1-ON emission is the derivation base: a `GroupFirst` disposition
//! emits the group's ONE spine trigger branch, so EVERY member of the group
//! derives its row at that branch's position (via
//! [`super::factoring::SpineEmission::group_members`]); `GroupRest`
//! descriptors emit nothing and derive nothing. F5-2 mixfix cohorts are
//! OPERAND-LEADING by construction (the A7-mixfix codegen assert), so their
//! members have no prefix-dispatch initiating branch and derive NO site-2
//! rows — the walker's site-2 query for their unary fires resolves through
//! the `0` fallback (the trait default's site-2 value, byte-identical).
//!
//! Site coverage (the walker queries site kinds 0/1/2 only —
//! `wpda_walker.rs` `cgll_pure_ktuple` decision pushes):
//!   - site 0 = optional-group TAKE  → `binder::OPTIONAL_GROUP_TAKE_BRANCH_INDEX` (0)
//!   - site 1 = optional-group SKIP  → `binder::OPTIONAL_GROUP_SKIP_BRANCH_INDEX` (1)
//!   - site 2 = kept-wrapper fire    → the per-(cat, rule) row match, `_ => 0`
//!     (fallback 0 — NOT MAX: the walker's site-2 query domain (any unary
//!     non-coercion fire) is broader than the trigger-initiated rule set;
//!     0 is the trait default's site-2 value, so the underived remainder —
//!     the ambiguous-multi-bucket class, the `(`-grouping NParen-class
//!     (whose grouping branches come FIRST in `emit_paren_dispatch_arms`'
//!     layout and thus sit at index 0 anyway), and the operand-leading
//!     mixfix cohorts — stays byte-identical)
//!   - site 3 = grouping-TRANSPARENT → 1, MIRRORING the trait default's
//!     `3 => 1` (site 3 is structurally absent from the forest and never
//!     queried — the MAX pad happens in `CgllKTuple::lt`'s padding, not
//!     here; mirroring keeps the generated fn value-identical to the
//!     default on every input, queried or not)
//!   - site > 3 → `u16::MAX` (the trait default's `_` arm)

use proc_macro2::TokenStream;
use quote::quote;
use std::collections::BTreeMap;

/// One derived site-2 row: the rule's initiating-branch static declaration
/// position within its dispatch bucket.
#[derive(Debug, Clone)]
struct ForkEmissionOrdinalRow {
    emission_ordinal: u16,
    /// Human-readable bucket identity for collision diagnostics (the
    /// bucket's token pattern + guard, or a site label).
    bucket_tag: String,
}

/// The per-grammar fork-emission ordinal model, filled by the prefix/binder
/// emitters during engine generation and emitted as the module-level
/// `WPDA_FORK_EMISSION_ORDINAL` fn beside the Parikh tables.
#[derive(Debug, Default)]
pub(crate) struct ForkEmissionOrdinalModel {
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
    pub(crate) fn new() -> Self {
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
    pub(crate) fn record_site2_row(
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
    pub(crate) fn site2_row_count(&self) -> usize {
        self.site2_rows.len()
    }

    /// Number of ambiguous-multi-bucket rules (fallback-resolved).
    pub(crate) fn ambiguous_rule_count(&self) -> usize {
        self.ambiguous_multi_bucket.len()
    }

    /// Test-facing readback of a derived ordinal (`None` = underived,
    /// including the ambiguous class).
    #[cfg(test)]
    pub(crate) fn site2_ordinal(&self, cat: u16, rule: u16) -> Option<u16> {
        self.site2_rows.get(&(cat, rule)).map(|r| r.emission_ordinal)
    }

    /// Test-facing readback of the ambiguous classification.
    #[cfg(test)]
    pub(crate) fn is_ambiguous_multi_bucket(&self, cat: u16, rule: u16) -> bool {
        self.ambiguous_multi_bucket.contains_key(&(cat, rule))
    }

    /// Test-facing census DOMAIN: every `(cat, rule)` key the emitters
    /// recorded — derived rows ∪ ambiguous-multi-bucket keys. The F1
    /// value-identity units iterate exactly this domain (per the
    /// coordinator requirement: derive the domain from the census, don't
    /// sample blindly).
    #[cfg(test)]
    pub(crate) fn census_keys(&self) -> Vec<(u16, u16)> {
        let mut keys: Vec<(u16, u16)> =
            Vec::with_capacity(self.site2_rows.len() + self.ambiguous_multi_bucket.len());
        keys.extend(self.site2_rows.keys().copied());
        keys.extend(self.ambiguous_multi_bucket.keys().copied());
        keys
    }

    /// The VALUE the emitted `WPDA_FORK_EMISSION_ORDINAL` returns for a
    /// query — kept in LOCKSTEP with [`Self::into_tokens`] (the value-
    /// identity units compare this against the walker-trait default over
    /// the census-derived domain; the stream-shape units pin that
    /// `into_tokens` emits exactly these semantics).
    ///
    /// F1 (coordinator decision, 2026-07-14): ELECTION-INERT — value-
    /// identical to the walker-trait default (`0|2 => 0, 1|3 => 1,
    /// _ => MAX`) on EVERY input, independent of the recorded census.
    // Consumed only by the cfg(test) value-identity / stream-shape units
    // (fork_emission.rs + factoring.rs); dead in the non-test lib build.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn emitted_value(&self, site_kind: u8, cat: u16, rule: u16) -> u16 {
        let _ = (cat, rule);
        match site_kind {
            0 => super::binder::OPTIONAL_GROUP_TAKE_BRANCH_INDEX,
            1 => super::binder::OPTIONAL_GROUP_SKIP_BRANCH_INDEX,
            2 => 0,
            3 => 1,
            _ => u16::MAX,
        }
    }

    /// Emit the module-level table fn. `lang_name` feeds the generated doc
    /// comment (the `parikh_inventory_doc` precedent) and the loud-but-
    /// nonfatal collision diagnostic line.
    ///
    /// ★ F1 — THE ACTIVATION POINT (coordinator decision 2026-07-14 after
    /// the `*(@(p))` adjudication; capability documentation, deliberately
    /// NOT a TODO): this fn is the ONE emission policy point where derived
    /// site-2 positions could become ELECTION-ACTIVE — by emitting the
    /// recorded `site2_rows` as nonzero match arms instead of the inert
    /// `2u8 => 0u16` below. The use case the ledger names is the
    /// grp_d1-class per-grammar preference (a grammar that wants the
    /// TRANSPARENT kept-vs-transparent twin elected). Any future activation
    /// REQUIRES this leg's full A/B adjudication discipline: per-input
    /// election traces against the classic lever
    /// (`PRATTAIL_NO_CANONICAL_GLL=1`), toward-classic deltas enumerated
    /// for explicit user sign-off, away-from-classic = derivation bug. The
    /// empirical finding that forced F1 (banked in ledger §"#10 item-1"):
    /// K-C compares decisions of candidates whose fires originate in
    /// DIFFERENT dispatch buckets — cross-bucket positions are not a
    /// classic temporal order (the committed `*(@(p))` pin flipped
    /// away-from-classic under true positions: NParen@1-in-the-`(`-bucket
    /// vs NQuote@0-in-the-`@`-bucket), so the UNIFORM site-2 value is
    /// load-bearing for cross-site ties and IS the classic-faithful
    /// per-grammar assignment for every current grammar.
    pub(crate) fn into_tokens(self, lang_name: &str) -> TokenStream {
        let take_idx = super::binder::OPTIONAL_GROUP_TAKE_BRANCH_INDEX;
        let skip_idx = super::binder::OPTIONAL_GROUP_SKIP_BRANCH_INDEX;
        let total_rows = self.site2_row_count();
        let ambiguous_count = self.ambiguous_rule_count();
        // F1 detection surface 1/2: the derived-position census + the
        // ambiguous inventory in the generated doc comment — RECORDED,
        // inspectable, never election-active.
        let mut nonzero = 0usize;
        let mut census_entries: Vec<String> = Vec::with_capacity(self.site2_rows.len());
        for (&(cat, rule), row) in &self.site2_rows {
            if row.emission_ordinal == 0 {
                continue;
            }
            nonzero += 1;
            census_entries.push(format!(
                "(cat {cat}, rule {rule})@{} [{}]",
                row.emission_ordinal, row.bucket_tag
            ));
        }
        let census_doc = if census_entries.is_empty() {
            String::new()
        } else {
            format!(
                " Derived NONZERO static positions (census-only, election-inert): {}.",
                census_entries.join("; ")
            )
        };
        let ambiguous_doc = if self.ambiguous_multi_bucket.is_empty() {
            String::new()
        } else {
            let entries: Vec<String> = self
                .ambiguous_multi_bucket
                .iter()
                .map(|(&(cat, rule), tags)| {
                    format!("(cat {cat}, rule {rule}): {}", tags.join(" vs "))
                })
                .collect();
            format!(
                " AMBIGUOUS-MULTI-BUCKET (fallback-0-resolved, Option A): {}.",
                entries.join("; ")
            )
        };
        let doc = format!(
            " Task #10 item 1 (F1, 2026-07-14): per-grammar fork-emission ordinal table \
             for `{}` — ELECTION-INERT: value-identical to the walker-trait default on \
             every input (site 0 TAKE = {}; site 1 SKIP = {}; site 2 = 0 uniformly — \
             the uniform value is LOAD-BEARING for K-C cross-bucket ties, see the \
             activation-point rustdoc on `ForkEmissionOrdinalModel::into_tokens`; site 3 \
             = 1 mirroring the default; others MAX). The emitters recorded {} \
             single-valued static declaration position(s) ({} nonzero) and {} \
             ambiguous-multi-bucket rule(s) — census below.{}{}",
            lang_name,
            take_idx,
            skip_idx,
            total_rows,
            nonzero,
            ambiguous_count,
            census_doc,
            ambiguous_doc,
        );
        // F1 detection surface 2/2: the loud-but-nonfatal codegen
        // diagnostic line (the DIS-lint summary style — printed once per
        // generated language when ambiguity exists).
        if !self.ambiguous_multi_bucket.is_empty() {
            eprintln!(
                "note[FORK-ORD] ({lang_name}): {ambiguous_count} multi-bucket-ambiguous \
                 rule(s) resolved to the site-2 fallback 0 (zero K-C movement); \
                 inventory in WPDA_FORK_EMISSION_ORDINAL's doc comment",
            );
        }
        quote! {
            #[doc = #doc]
            #[allow(non_snake_case, clippy::match_single_binding)]
            pub fn WPDA_FORK_EMISSION_ORDINAL(site_kind: u8, cat: u16, rule: u16) -> u16 {
                let _ = (cat, rule);
                match site_kind {
                    0u8 => #take_idx,
                    1u8 => #skip_idx,
                    // F1: election-inert — the uniform site-2 value (the
                    // walker-trait default's); the derived census lives in
                    // the doc comment above, never in the match.
                    2u8 => 0u16,
                    3u8 => 1u16,
                    _ => u16::MAX,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_value_duplicate_dedups_to_one_row() {
        let mut model = ForkEmissionOrdinalModel::new();
        model.record_site2_row(0, 4, 2, "bucket-a");
        model.record_site2_row(0, 4, 2, "bucket-b"); // same position: dedup.
        assert_eq!(model.site2_row_count(), 1);
        assert_eq!(model.site2_ordinal(0, 4), Some(2));
        assert!(!model.is_ambiguous_multi_bucket(0, 4));
    }

    /// Option A (coordinator decision 2026-07-14, replacing the amendment-6
    /// panic after probe P7 fired on shipped grammars): a differing-position
    /// multi-bucket observation reclassifies the rule AMBIGUOUS — no derived
    /// row (fallback 0 = the trait default, zero K-C movement), no panic,
    /// every bucket observation retained.
    #[test]
    fn conflicting_ordinal_classifies_ambiguous_and_falls_back() {
        let mut model = ForkEmissionOrdinalModel::new();
        model.record_site2_row(0, 4, 2, "bucket-a");
        model.record_site2_row(0, 4, 3, "bucket-b"); // differing position.
        assert_eq!(model.site2_row_count(), 0, "the row LEAVES the derived set");
        assert_eq!(model.site2_ordinal(0, 4), None, "no guessed ordinal");
        assert!(model.is_ambiguous_multi_bucket(0, 4));
        assert_eq!(model.ambiguous_rule_count(), 1);
        // Later observations stay in the ambiguous class (retained, no row).
        model.record_site2_row(0, 4, 7, "bucket-c");
        assert_eq!(model.site2_ordinal(0, 4), None);
        assert_eq!(model.site2_row_count(), 0);
        // The emitted table carries no arm for the ambiguous rule and the
        // doc records the inventory.
        let ts = model.into_tokens("ToyLang").to_string();
        assert!(!ts.contains("(0u16 , 4u16)"), "ambiguous rule not emitted: {ts}");
        assert!(ts.contains("AMBIGUOUS-MULTI-BUCKET"), "doc inventory present: {ts}");
        assert!(ts.contains("bucket-a@2"), "first observation retained: {ts}");
        assert!(ts.contains("bucket-b@3"), "second observation retained: {ts}");
        assert!(ts.contains("bucket-c@7"), "later observation retained: {ts}");
    }

    /// F1 (coordinator decision 2026-07-14): the emitted table is
    /// ELECTION-INERT — value-identical to the walker-trait default —
    /// REGARDLESS of the recorded census; the derived positions live in the
    /// doc comment only. This is the strongest shape pin: even a model FULL
    /// of nonzero rows emits the inert fn.
    #[test]
    fn emitted_table_is_election_inert_for_any_model() {
        let mut model = ForkEmissionOrdinalModel::new();
        model.record_site2_row(1, 7, 3, "bucket-x");
        model.record_site2_row(1, 8, 0, "bucket-x"); // fallback-equal.
        model.record_site2_row(2, 9, 11, "bucket-y");
        let ts = model.into_tokens("ToyLang").to_string();
        assert!(ts.contains("WPDA_FORK_EMISSION_ORDINAL"));
        // Site 0/1 route through the binder constants (0/1 today).
        assert!(ts.contains("0u8 => 0u16"), "TAKE row = the binder const 0: {ts}");
        assert!(ts.contains("1u8 => 1u16"), "SKIP row = the binder const 1: {ts}");
        // F1: the site-2 arm is the INERT uniform 0 — no per-rule match arms
        // exist in the emitted stream.
        assert!(ts.contains("2u8 => 0u16"), "site 2 = the inert uniform 0: {ts}");
        assert!(
            !ts.contains("(1u16 , 7u16)") && !ts.contains("(2u16 , 9u16)"),
            "derived rows must NOT be election-active: {ts}"
        );
        // The census still records the derived nonzero positions.
        assert!(
            ts.contains("(cat 1, rule 7)@3 [bucket-x]"),
            "census entry present in the doc: {ts}"
        );
        assert!(
            ts.contains("(cat 2, rule 9)@11 [bucket-y]"),
            "census entry present in the doc: {ts}"
        );
        // Site 3 mirrors the trait default's 1; others MAX.
        assert!(ts.contains("3u8 => 1u16"));
        assert!(ts.contains("_ => u16 :: MAX"));
    }

    /// F1 value-identity: `emitted_value` (the lockstep mirror of the
    /// emitted fn) equals the walker-trait default (`0|2 => 0, 1|3 => 1,
    /// _ => MAX`) over the census-derived domain — derived keys, ambiguous
    /// keys, and an out-of-census key, across every site kind.
    #[test]
    fn emitted_value_matches_the_walker_trait_default() {
        let mut model = ForkEmissionOrdinalModel::new();
        model.record_site2_row(1, 7, 3, "bucket-x"); // derived nonzero.
        model.record_site2_row(0, 4, 2, "bucket-a"); // becomes ambiguous:
        model.record_site2_row(0, 4, 3, "bucket-b");
        let trait_default = |site_kind: u8| -> u16 {
            match site_kind {
                0 | 2 => 0,
                1 | 3 => 1,
                _ => u16::MAX,
            }
        };
        let domain: [(u16, u16); 3] = [(1, 7), (0, 4), (9, 9)];
        for &(cat, rule) in &domain {
            for site_kind in [0u8, 1, 2, 3, 4, 255] {
                assert_eq!(
                    model.emitted_value(site_kind, cat, rule),
                    trait_default(site_kind),
                    "F1 value-identity at site {site_kind}, (cat {cat}, rule {rule})",
                );
            }
        }
    }
}
