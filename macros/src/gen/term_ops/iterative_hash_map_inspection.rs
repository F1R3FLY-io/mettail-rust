//! Native Map Hash accounting through the existing comparison worklist.
use super::*;

pub(super) fn generate_map_hash_contribution_inspection(language: &LanguageDef) -> TokenStream {
    let required = required_map_hash_categories(language);
    let helpers = language.types.iter().filter(|ty| required.contains(&ty.name.to_string())).map(|ty| {
        let category = &ty.name;
        let helper = format_ident!("inspect_map_hash_contributions_{}", category.to_string().to_lowercase());
        let variant = format_ident!("Cmp{}", category);
        quote! {
            fn #helper<E>(
                source: &mettail_runtime::HashMapLit<#category, #category>,
                state: &mut mettail_runtime::binding_receipt::BindingCharge,
                reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
            ) -> Result<(), mettail_runtime::KeyHashFailure<E>> {
                if !mettail_runtime::CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
                    return Err(mettail_runtime::KeyHashFailure::UnsupportedProfile);
                }
                // Check both the future native pair allocation and the
                // inspector's larger erased roster before allocating either.
                mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)
                    .map_err(mettail_runtime::KeyHashFailure::Admission)?;
                let n = source.len();
                let overflow = || mettail_runtime::KeyHashFailure::Admission(
                    mettail_runtime::BindingFailure::SizeOverflow);
                std::alloc::Layout::array::<(&#category, &#category)>(n).map_err(|_| overflow())?;
                std::alloc::Layout::array::<mettail_runtime::CollectionCmpItem>(n).map_err(|_| overflow())?;
                let original = source.try_comparison_roster(reserve)?;
                let constructor = |left: *const (), right: *const ()|
                    InspectCmpContributionTask::#variant(left.cast::<#category>(), right.cast::<#category>());
                let mut cursor = InspectCmpPairCursor::try_for_map_hash(
                    original, constructor, constructor, reserve)?;
                inspect_native_map_hash_overhead(state, n, cursor.factors[0], reserve)?;
                while let Some(pair) = cursor.try_next(reserve)? {
                    // The same immutable source retains every original pointer.
                    // Each native callback invokes a FULL public Ord root;
                    // neither role uses the nested-child-only allowance.
                    mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)
                        .map_err(mettail_runtime::KeyHashFailure::Admission)?;
                    let roles = [Some(pair.primary), pair.secondary];
                    for role in roles {
                        mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)
                            .map_err(mettail_runtime::KeyHashFailure::Admission)?;
                        let Some((left, right)) = role else { continue };
                        let charge = inspect_cmp_contribution_worklist(
                            constructor(left, right), InspectCmpContributionMode::Ord,
                            pair.factor, reserve)?;
                        state.try_accumulate_parts(charge.base_work(), charge.records(),
                            charge.owned_bytes(), reserve)
                            .map_err(mettail_runtime::KeyHashFailure::Admission)?;
                    }
                }
                Ok(())
            }
        }
    });
    quote! {
        fn inspect_native_map_hash_overhead<E>(
            state: &mut mettail_runtime::binding_receipt::BindingCharge,
            n: usize, callbacks: usize,
            reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
        ) -> Result<(), mettail_runtime::KeyHashFailure<E>> {
            // Fixed metadata calculation, not native execution. The verified
            // components are added monotonically; conservative overlap is not
            // subtracted without an event-identification proof.
            mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)
                .map_err(mettail_runtime::KeyHashFailure::Admission)?;
            let overflow = || mettail_runtime::KeyHashFailure::Admission(
                mettail_runtime::BindingFailure::SizeOverflow);
            let core = n.checked_mul(n).and_then(|square| square.checked_mul(320))
                .and_then(|work| n.checked_mul(1024).and_then(|more| work.checked_add(more)))
                .and_then(|work| work.checked_add(1133)).ok_or_else(overflow)?;
            let shell = n.checked_mul(10).and_then(|work| work.checked_add(19))
                .and_then(|work| work.checked_add(usize::from(n != 0))).ok_or_else(overflow)?;
            let roster_records = n.checked_add(1).ok_or_else(overflow)?;
            let roster_work = roster_records.checked_mul(2).ok_or_else(overflow)?;
            let adapter = callbacks.checked_mul(5).ok_or_else(overflow)?;
            let (scratch_work, scratch_records) = if n > 20 {
                // Pinned 64-bit borrowed-pair profile: 4096 / 16 = 256 slots.
                // The outer buffer is reused by eager fallback/small sorting.
                let q = (n - n / 2).max(n.min(500_000)).max(48);
                if q > 256 {
                    let records = q.checked_add(1).ok_or_else(overflow)?;
                    let work = records.checked_mul(2).and_then(|work| work.checked_add(530))
                        .ok_or_else(overflow)?;
                    (work, records.checked_add(258).ok_or_else(overflow)?)
                } else { (530, 258) }
            } else { (0, 0) };
            // NativeStableSortWorkBound: core control and cumulative records.
            // NativeMapTrustedCollect + original reverse-consuming loop: shell.
            // Flat owner laws: roster/scratch construction and normal disposal.
            // Full Ord bodies are added separately, once per original role.
            for (work, records) in [
                (core, core), (shell, 0), (2, 0),
                (roster_work, roster_records), (0, 1),
                (adapter, 0), (scratch_work, scratch_records),
            ] {
                state.try_accumulate_parts(work, records, 0, reserve)
                    .map_err(mettail_runtime::KeyHashFailure::Admission)?;
            }
            Ok(())
        }
        #(#helpers)*
    }
}
