//! Typed admission for the existing native HashBag reconstruction stages.
//!
//! `NativeHashBagStageCharge` composes complete Hash/Eq receipts with the
//! original table's flat work. The caller still supplies source-ordered owned
//! entries and their independent normal-cleanup credits before reconstruction.
//! This emitter neither constructs entries nor changes their native operations.

use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

pub(super) fn generate_hashbag_rebuild_admission(language: &LanguageDef) -> TokenStream {
    let adapters = language.types.iter().map(|ty| {
        let category = &ty.name;
        let suffix = category.to_string().to_lowercase();
        let admit = format_ident!("admit_bag_rebuild_{}", suffix);
        let hash = format_ident!("inspect_hash_contribution_{}", suffix);
        let equal = format_ident!("inspect_comparison_contributions_{}", suffix);
        quote! {
            #[allow(dead_code)]
            fn #admit<E>(
                step: mettail_runtime::HashBagRebuildStep<'_, #category>,
                reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
            ) -> Result<(), mettail_runtime::BindingFailure<E>> {
                use mettail_runtime::{BindingFailure, HashBagRebuildMode, HashBagRebuildStep};
                use mettail_runtime::binding_receipt::BindingCharge;
                if !mettail_runtime::CHECKED_FX_PROFILE_AVAILABLE
                    || !mettail_runtime::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE
                {
                    return Err(BindingFailure::UnsupportedProfile);
                }
                // Accumulator lifetime and fixed stage routing are inspection,
                // separately spent before the eventual native-stage payment.
                mettail_runtime::reserve_binding_parts(3, 1, 0, reserve)?;
                let overflow = || BindingFailure::SizeOverflow;
                let charge = match step {
                    HashBagRebuildStep::Start { width, .. } => {
                        let work = width.checked_mul(3).and_then(|v| v.checked_add(11))
                            .ok_or_else(overflow)?;
                        let records = width.checked_add(4).ok_or_else(overflow)?;
                        BindingCharge::new(work, records, 0).map_err(|_| overflow())?
                    },
                    HashBagRebuildStep::Insert {
                        mode: HashBagRebuildMode::CloneEntries, count: 0, ..
                    } => {
                        // clone_zero_flat: reconstruction's checked-total
                        // wrapper plus insert_n's zero test. Incoming root
                        // disposal was separately paid by its producer.
                        return mettail_runtime::reserve_binding_parts(2, 0, 0, reserve);
                    },
                    HashBagRebuildStep::Insert { mode, key, retained, .. } => {
                        let (mut charge, growth) =
                            inspect_bag_rebuild_insert_flat(&retained, mode, reserve)?;
                        let cloning = mode == HashBagRebuildMode::CloneEntries;
                        let incoming = #hash(key, reserve).map_err(BindingFailure::from)?;
                        accumulate_bag_rebuild_scaled(
                            &mut charge, incoming, if cloning { 3 } else { 1 }, reserve)?;
                        let retained_hash_factor = usize::from(growth) + if cloning { 4 } else { 0 };
                        retained.try_for_each_entry(reserve, |stored, _count, reserve| {
                            // Preserve occurrences and the native operand direction;
                            // no semantic comparison runs during this inspection.
                            mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
                            if retained_hash_factor != 0 {
                                let hash = #hash(stored, reserve).map_err(BindingFailure::from)?;
                                accumulate_bag_rebuild_scaled(
                                    &mut charge, hash, retained_hash_factor, reserve)?;
                            }
                            let (left, right) = if cloning { (stored, key) } else { (key, stored) };
                            let equality = #equal(
                                left, right, InspectCmpContributionMode::Eq, reserve,
                            ).map_err(BindingFailure::from)?;
                            accumulate_bag_rebuild_scaled(&mut charge, equality, 1, reserve)
                        })?;
                        charge
                    },
                    HashBagRebuildStep::FinalBindingSummary { retained } => {
                        let (entries, _capacity, _buckets, groups) =
                            inspect_bag_rebuild_geometry(&retained, reserve)?;
                        let work = bag_rebuild_scan_work(entries, groups)
                            .and_then(|v| v.checked_add(1))
                            .and_then(|v| entries.checked_mul(2).and_then(|more| v.checked_add(more)))
                            .ok_or_else(overflow)?;
                        let mut charge = BindingCharge::new(work, 0, 0).map_err(|_| overflow())?;
                        retained.try_for_each_entry(reserve, |stored, _count, reserve| {
                            let hash = #hash(stored, reserve).map_err(BindingFailure::from)?;
                            accumulate_bag_rebuild_scaled(&mut charge, hash, 2, reserve)
                        })?;
                        charge
                    },
                };
                // No stage is authorized by metadata inspection alone. The
                // original runtime action follows only after this succeeds.
                charge.reserve(reserve)
            }
        }
    });
    quote! {
        // These pure arithmetic projections are called only inside paid
        // fixed-size metadata groups. They do not scan or operate on keys.
        fn bag_rebuild_scan_work(entries: usize, groups: usize) -> Option<usize> {
            entries.checked_mul(4)?.checked_add(groups.checked_mul(19)?)
        }

        fn bag_rebuild_probe_work(groups: usize, candidates: usize) -> Option<usize> {
            groups.checked_mul(22)?.checked_add(candidates.checked_mul(2)?)?.checked_add(17)
        }

        fn inspect_bag_rebuild_geometry<T, E>(
            retained: &mettail_runtime::HashBagRetainedEntries<'_, T>,
            reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
        ) -> Result<(usize, usize, usize, usize), mettail_runtime::BindingFailure<E>> {
            use mettail_runtime::BindingFailure;
            if !mettail_runtime::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
                return Err(BindingFailure::UnsupportedProfile);
            }
            mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
            // The private retained view exists only between completed native
            // insertions in a fresh, tombstone-free accumulator. Its actual
            // bucket count is representable; this is not a prospective size.
            let buckets = retained.checked_bucket_count().ok_or(
                BindingFailure::InvalidCollectionInput(
                    "retained counts table has invalid native geometry"))?;
            let entries = retained.distinct_len();
            let capacity = retained.capacity();
            if entries > capacity {
                return Err(BindingFailure::InvalidCollectionInput(
                    "retained counts table exceeds its native capacity"));
            }
            let groups = 1 + (buckets - 1) / 16;
            Ok((entries, capacity, buckets, groups))
        }

        fn inspect_bag_rebuild_insert_flat<T, E>(
            retained: &mettail_runtime::HashBagRetainedEntries<'_, T>,
            mode: mettail_runtime::HashBagRebuildMode,
            reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
        ) -> Result<(mettail_runtime::binding_receipt::BindingCharge, bool),
            mettail_runtime::BindingFailure<E>> {
            use mettail_runtime::{BindingFailure, HashBagRebuildMode};
            use mettail_runtime::binding_receipt::BindingCharge;
            let (entries, capacity, old_buckets, old_groups) =
                inspect_bag_rebuild_geometry(retained, reserve)?;
            mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
            let overflow = || BindingFailure::SizeOverflow;
            // Binding can reserve before recognizing an equal key. For Clone,
            // possible vacant growth safely covers an occupied-key outcome.
            let growth = entries == capacity;
            let buckets = if growth {
                if old_buckets == 1 { 4 }
                else { old_buckets.checked_mul(2).ok_or_else(overflow)? }
            } else { old_buckets };
            let allocation_bytes = if growth {
                // NativeHashBagGrowth establishes this exact selection. Check
                // the native intermediate arithmetic too, before insertion.
                let request = capacity.checked_add(1).ok_or_else(overflow)?;
                if request >= 15 {
                    let adjusted = request.checked_mul(8).ok_or_else(overflow)? / 7;
                    adjusted.checked_next_power_of_two().ok_or_else(overflow)?;
                }
                retained.checked_table_layout(buckets).ok_or_else(overflow)?.0.size()
            } else { 0 };
            let groups = 1 + (buckets - 1) / 16;
            let probe = match mode {
                HashBagRebuildMode::BindingEntries => bag_rebuild_probe_work(groups, entries),
                HashBagRebuildMode::CloneEntries => bag_rebuild_probe_work(old_groups, entries)
                    .and_then(|v| bag_rebuild_probe_work(groups, 0).and_then(|more| v.checked_add(more)))
                    .and_then(|v| v.checked_add(4)),
            }.ok_or_else(overflow)?;
            let resize = if growth {
                bag_rebuild_scan_work(entries, old_groups)
                    .and_then(|v| bag_rebuild_probe_work(groups, 0)
                        .and_then(|one| entries.checked_mul(one))
                        .and_then(|more| v.checked_add(more)))
                    .and_then(|v| v.checked_add(entries))
                    .and_then(|v| entries.checked_mul(4).and_then(|more| v.checked_add(more)))
                    .and_then(|v| entries.checked_mul(std::mem::size_of::<(T, usize)>())
                        .and_then(|more| v.checked_add(more)))
                    .and_then(|v| buckets.checked_add(16).and_then(|more| v.checked_add(more)))
                    .and_then(|v| v.checked_add(3)).ok_or_else(overflow)?
            } else { 0 };
            let post_entries = entries.checked_add(1).ok_or_else(overflow)?;
            let cleanup = bag_rebuild_scan_work(post_entries, groups)
                .and_then(|v| v.checked_add(post_entries))
                .and_then(|v| v.checked_add(6)).ok_or_else(overflow)?;
            let work = probe.checked_add(1).and_then(|v| v.checked_add(resize))
                .and_then(|v| v.checked_add(cleanup)).ok_or_else(overflow)?;
            let charge = BindingCharge::new(work, usize::from(growth), allocation_bytes)
                .map_err(|_| overflow())?;
            Ok((charge, growth))
        }

        fn accumulate_bag_rebuild_scaled<E>(
            state: &mut mettail_runtime::binding_receipt::BindingCharge,
            contribution: mettail_runtime::binding_receipt::BindingCharge,
            factor: usize,
            reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
        ) -> Result<(), mettail_runtime::BindingFailure<E>> {
            // NativeInspectionAccumulation: pay before checked scaling; the
            // existing accumulator separately pays before checked addition.
            mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)?;
            let scaled = contribution.checked_scale(factor)
                .map_err(|_| mettail_runtime::BindingFailure::SizeOverflow)?;
            state.try_accumulate_parts(
                scaled.base_work(), scaled.records(), scaled.owned_bytes(), reserve)
        }

        #(#adapters)*
    }
}
