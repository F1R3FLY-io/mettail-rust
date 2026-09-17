//! Private contribution traversal using the original comparison handlers.
use super::*;

/// Assemble borrowed typed jobs and their collection-component allowances,
/// not another comparator. This private receipt is accounting data, not
/// authority to execute native comparisons or reconstruction.
#[allow(dead_code)]
pub(super) fn generate_comparison_contribution_inspection(language: &LanguageDef) -> TokenStream {
    let emission = CmpEmissionNames::inspect_contributions();
    let task_enum = &emission.task_enum;
    let scaled = CmpEmissionNames::inspect_scaled_accumulation_helper();
    let cursor = generate_collection_contribution_cursor();
    let support = generate_cmp_support_fns(language, &emission);
    let variants = language.types.iter().map(|ty| {
        let cat = &ty.name;
        let variant = format_ident!("Cmp{}", cat);
        quote! { #variant(*const #cat, *const #cat) }
    });
    let handlers = language.types.iter().map(|ty| {
        let eq = generate_eq_category_handler(&ty.name, language, &emission);
        let ord = generate_cmp_category_handler(&ty.name, language, &emission);
        quote! { #eq #ord }
    });
    let arms = language.types.iter().map(|ty| {
        let cat = &ty.name;
        let variant = format_ident!("Cmp{}", cat);
        let eq = emission.eq_handler(cat);
        let ord = emission.cmp_handler(cat);
        quote! {
            #task_enum::#variant(left, right) => match mode {
                InspectCmpContributionMode::Eq =>
                    #eq(&mut stack, left, right, &mut state, mode, factor, reserve)?,
                InspectCmpContributionMode::Ord =>
                    #ord(&mut stack, left, right, &mut state, mode, factor, reserve)?,
            }
        }
    });
    let interfaces = language.types.iter().map(|ty| {
        let cat = &ty.name;
        let variant = format_ident!("Cmp{}", cat);
        let function =
            format_ident!("inspect_comparison_contributions_{}", cat.to_string().to_lowercase());
        quote! {
            #[allow(dead_code)]
            fn #function<E>(
                left: &#cat, right: &#cat, mode: InspectCmpContributionMode,
                reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
            ) -> Result<mettail_runtime::binding_receipt::BindingCharge,
                mettail_runtime::NativeComparisonFailure<E>> {
                // These immutable roots retain every descendant pointer until
                // the local worklist, including flat roster owners, is dropped.
                inspect_cmp_contribution_worklist(#task_enum::#variant(left, right), mode, 1, reserve)
            }
        }
    });
    quote! {
        #[derive(Clone, Copy)]
        enum InspectCmpContributionMode { Eq, Ord }
        enum #task_enum {
            #(#variants,)*
            Collection(InspectCmpPairCursor),
        }
        struct InspectCmpContributionFrame {
            task: #task_enum,
            mode: InspectCmpContributionMode,
            factor: usize,
        }
        #scaled
        #cursor
        #support
        #(#handlers)*

        fn inspect_cmp_contribution_worklist<E>(
            root: #task_enum, mode: InspectCmpContributionMode,
            initial_factor: usize,
            reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
        ) -> Result<mettail_runtime::binding_receipt::BindingCharge,
            mettail_runtime::NativeComparisonFailure<E>> {
            // Header and root task have distinct paid normal-cleanup slots.
            mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)
                .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
            let mut stack = Vec::new();
            mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)
                .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
            stack.push(InspectCmpContributionFrame { task: root, mode, factor: initial_factor });
            let mut state = mettail_runtime::binding_receipt::BindingCharge::ZERO;
            // Original local wrapper/root lifecycle, not a fresh wrapper per
            // nested collection callback. Continuation costs compose separately.
            inspect_cmp_scaled_contribution(&mut state, 19, 3, 0, initial_factor, reserve)?;
            loop {
                mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)
                    .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
                let Some(InspectCmpContributionFrame { task, mode, factor }) = stack.pop()
                else { break };
                mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)
                    .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
                match task {
                    #(#arms,)*
                    #task_enum::Collection(cursor) => {
                        inspect_cmp_expand_collection(cursor, &mut stack, &mut state, reserve)?;
                    }
                }
            }
            Ok(state)
        }
        #(#interfaces)*
    }
}

/// GeneratedComparisonPairCursor proves this fixed-family, row-major cursor
/// visits every original directed occurrence exactly once. No Cartesian list,
/// expanded repetition list, native comparison, or recursive call is needed.
fn generate_collection_contribution_cursor() -> TokenStream {
    quote! {
        #[derive(Clone, Copy)]
        enum InspectCmpPairFamily { LeftSort, RightSort, CrossLex }

        #[derive(Clone, Copy)]
        enum InspectCmpCollectionSource {
            Map,
            Bag { left_scan: usize, right_scan: usize },
        }

        fn inspect_cmp_add_collection_overhead<E>(
            state: &mut mettail_runtime::binding_receipt::BindingCharge,
            n: usize, m: usize, source: InspectCmpCollectionSource,
            mode: InspectCmpContributionMode, factor: usize,
            reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
        ) -> Result<(), mettail_runtime::NativeComparisonFailure<E>> {
            // Pay before this bounded metadata calculation. Named components
            // remain separate from child bodies and their existing 4W/1R
            // pushes; Bag's original length comparison is counted by its arm.
            mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)
                .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
            let overflow = || mettail_runtime::NativeComparisonFailure::Admission(
                mettail_runtime::BindingFailure::SizeOverflow);
            let width = n.checked_add(m).ok_or_else(overflow)?;
            let sort_requests = n.checked_mul(n.saturating_sub(1))
                .and_then(|left| m.checked_mul(m.saturating_sub(1))
                    .and_then(|right| left.checked_add(right))).ok_or_else(overflow)?;
            let requests = sort_requests.checked_add(width).ok_or_else(overflow)?;
            let (requests, preparation) = match source {
                InspectCmpCollectionSource::Map => (
                    requests.checked_mul(2).ok_or_else(overflow)?,
                    width.checked_mul(7).and_then(|work| work.checked_add(22))
                        .ok_or_else(overflow)?,
                ),
                InspectCmpCollectionSource::Bag { left_scan, right_scan } => (
                    requests,
                    width.checked_mul(7).and_then(|work| work.checked_add(20))
                        .and_then(|work| work.checked_add(left_scan))
                        .and_then(|work| work.checked_add(right_scan)).ok_or_else(overflow)?,
                ),
            };
            // GeneratedCollectionPreparation: actual producer and sum words.
            // AdmittedCollectionComparisonOwnership: four flat buffers plus
            // one Box, each with its eventual normal-disposal credit.
            let buffer_work = width.checked_mul(4).and_then(|work| work.checked_add(10))
                .ok_or_else(overflow)?;
            let buffer_records = width.checked_mul(2).and_then(|count| count.checked_add(5))
                .ok_or_else(overflow)?;
            // NativeCollectionCoreInventory: source-derived 23B+11L+28.
            let core = sort_requests.checked_mul(23)
                .and_then(|work| width.checked_mul(11).and_then(|more| work.checked_add(more)))
                .and_then(|work| work.checked_add(28)).ok_or_else(overflow)?;
            // GeneratedCollectionContinuationCover: Ord Start overhead or
            // Eq's auxiliary wrapper. Typed child pushes are NOT added again.
            let (start_work, start_records) = match mode {
                InspectCmpContributionMode::Ord => (7usize, 1usize),
                InspectCmpContributionMode::Eq => (27usize, 3usize),
            };
            let continuation_work = requests.checked_mul(9)
                .and_then(|work| work.checked_add(start_work)).ok_or_else(overflow)?;
            let continuation_records = requests.checked_add(start_records).ok_or_else(overflow)?;
            for (work, records) in [
                (preparation, 0), (buffer_work, buffer_records),
                (core, 0), (continuation_work, continuation_records),
            ] {
                inspect_cmp_scaled_contribution(state, work, records, 0, factor, reserve)?;
            }
            Ok(())
        }

        struct InspectCmpPairCursor {
            left: mettail_runtime::CheckedCmpRoster,
            right: mettail_runtime::CheckedCmpRoster,
            widths: [usize; 2],
            factors: [usize; 3],
            family: Option<InspectCmpPairFamily>,
            row: usize,
            col: usize,
            primary: fn(*const (), *const ()) -> InspectCmpContributionTask,
            secondary: Option<fn(*const (), *const ()) -> InspectCmpContributionTask>,
        }
        struct InspectCmpPair {
            primary: (*const (), *const ()),
            secondary: Option<(*const (), *const ())>,
            factor: usize,
        }

        impl InspectCmpPairCursor {
            fn try_for_map_hash<E>(
                original: mettail_runtime::CheckedCmpRoster,
                primary: fn(*const (), *const ()) -> InspectCmpContributionTask,
                secondary: fn(*const (), *const ()) -> InspectCmpContributionTask,
                reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
            ) -> Result<Self, mettail_runtime::NativeComparisonFailure<E>> {
                mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)
                    .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
                let width = original.try_items(reserve)?.len();
                // Original stable-sort dispatch has no callback below two
                // entries. For larger widths use its verified full-width
                // bound, not the collection PDA's different merge bound.
                let factor = if width < 2 { 0 } else {
                    width.checked_mul(width).and_then(|square| square.checked_mul(10))
                        .and_then(|work| width.checked_mul(32).and_then(|more| work.checked_add(more)))
                        .ok_or(mettail_runtime::NativeComparisonFailure::Admission(
                            mettail_runtime::BindingFailure::SizeOverflow))?
                };
                let empty = mettail_runtime::CheckedCmpRoster::try_with_capacity(0, reserve)?;
                mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)
                    .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
                Ok(Self {
                    left: original, right: empty, widths: [width, 0], factors: [factor, 0, 0],
                    family: Some(InspectCmpPairFamily::LeftSort), row: 0, col: 0,
                    primary, secondary: Some(secondary),
                })
            }

            fn dimensions(&self, family: InspectCmpPairFamily) -> (usize, usize, usize) {
                match family {
                    InspectCmpPairFamily::LeftSort => (self.widths[0], self.widths[0], self.factors[0]),
                    InspectCmpPairFamily::RightSort => (self.widths[1], self.widths[1], self.factors[1]),
                    InspectCmpPairFamily::CrossLex => (self.widths[0], self.widths[1], self.factors[2]),
                }
            }
            fn following(family: InspectCmpPairFamily) -> Option<InspectCmpPairFamily> {
                match family {
                    InspectCmpPairFamily::LeftSort => Some(InspectCmpPairFamily::RightSort),
                    InspectCmpPairFamily::RightSort => Some(InspectCmpPairFamily::CrossLex),
                    InspectCmpPairFamily::CrossLex => None,
                }
            }
            fn try_next<E>(
                &mut self, reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
            ) -> Result<Option<InspectCmpPair>, mettail_runtime::NativeComparisonFailure<E>> {
                loop {
                    // One fixed family/position control group per attempt.
                    // Skipping can advance at most the three enum families.
                    mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)
                        .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
                    let Some(family) = self.family else { return Ok(None) };
                    let (rows, cols, factor) = self.dimensions(family);
                    if rows == 0 || cols == 0 || factor == 0 {
                        self.family = Self::following(family);
                        self.row = 0;
                        self.col = 0;
                        continue;
                    }
                    let (left, right) = match family {
                        InspectCmpPairFamily::LeftSort => (&self.left, &self.left),
                        InspectCmpPairFamily::RightSort => (&self.right, &self.right),
                        InspectCmpPairFamily::CrossLex => (&self.left, &self.right),
                    };
                    let left = left.try_items(reserve)?;
                    let right = right.try_items(reserve)?;
                    mettail_runtime::reserve_binding_parts(2, 0, 0, reserve)
                        .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
                    let left = left.get(self.row).ok_or(
                        mettail_runtime::NativeComparisonFailure::InvalidCollectionInput(
                            "comparison inspection row outside its original roster"))?;
                    let right = right.get(self.col).ok_or(
                        mettail_runtime::NativeComparisonFailure::InvalidCollectionInput(
                            "comparison inspection column outside its original roster"))?;
                    let (left, left_secondary, _) = left.try_parts(reserve)?;
                    let (right, right_secondary, _) = right.try_parts(reserve)?;
                    let secondary = match (left_secondary, right_secondary) {
                        (Some(left), Some(right)) => Some((left, right)),
                        _ => None,
                    };
                    // PairCursor's bounded increments: a live coordinate is
                    // strictly below its representable dimension. Keep checked
                    // arithmetic here so an invariant defect still fails closed.
                    mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)
                        .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
                    let col = self.col.checked_add(1).ok_or(
                        mettail_runtime::NativeComparisonFailure::Admission(
                            mettail_runtime::BindingFailure::SizeOverflow))?;
                    if col < cols {
                        self.col = col;
                    } else {
                        let row = self.row.checked_add(1).ok_or(
                            mettail_runtime::NativeComparisonFailure::Admission(
                                mettail_runtime::BindingFailure::SizeOverflow))?;
                        self.col = 0;
                        if row < rows { self.row = row; }
                        else { self.row = 0; self.family = Self::following(family); }
                    }
                    return Ok(Some(InspectCmpPair { primary: (left, right), secondary, factor }));
                }
            }
        }

        fn inspect_cmp_schedule_collection<E>(
            stack: &mut Vec<InspectCmpContributionFrame>,
            state: &mut mettail_runtime::binding_receipt::BindingCharge,
            left: mettail_runtime::CheckedCmpRoster,
            right: mettail_runtime::CheckedCmpRoster,
            source: InspectCmpCollectionSource,
            primary: fn(*const (), *const ()) -> InspectCmpContributionTask,
            secondary: Option<fn(*const (), *const ()) -> InspectCmpContributionTask>,
            mode: InspectCmpContributionMode,
            factor: usize,
            reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
        ) -> Result<(), mettail_runtime::NativeComparisonFailure<E>> {
            // Pay before fixed metadata arithmetic; each roster already owns
            // construction/disposal credit from its original checked producer.
            mettail_runtime::reserve_binding_parts(1, 0, 0, reserve)
                .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
            let n = left.try_items(reserve)?.len();
            let m = right.try_items(reserve)?.len();
            inspect_cmp_add_collection_overhead(state, n, m, source, mode, factor, reserve)?;
            let overflow = || mettail_runtime::NativeComparisonFailure::Admission(
                mettail_runtime::BindingFailure::SizeOverflow);
            let left_factor = n.checked_mul(n.saturating_sub(1))
                .and_then(|count| count.checked_mul(factor)).ok_or_else(overflow)?;
            let right_factor = m.checked_mul(m.saturating_sub(1))
                .and_then(|count| count.checked_mul(factor)).ok_or_else(overflow)?;
            let cross_factor = n.checked_add(m)
                .and_then(|count| count.checked_mul(factor)).ok_or_else(overflow)?;
            mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)
                .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
            stack.push(InspectCmpContributionFrame {
                task: InspectCmpContributionTask::Collection(InspectCmpPairCursor {
                    left, right, widths: [n, m], factors: [left_factor, right_factor, cross_factor],
                    family: Some(InspectCmpPairFamily::LeftSort), row: 0, col: 0,
                    primary, secondary,
                }),
                mode, factor,
            });
            Ok(())
        }

        fn inspect_cmp_expand_collection<E>(
            mut cursor: InspectCmpPairCursor,
            stack: &mut Vec<InspectCmpContributionFrame>,
            state: &mut mettail_runtime::binding_receipt::BindingCharge,
            reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
        ) -> Result<(), mettail_runtime::NativeComparisonFailure<E>> {
            let Some(pair) = cursor.try_next(reserve)? else { return Ok(()) };
            let primary = cursor.primary;
            let secondary = cursor.secondary;
            // Requeueing the inspector's flat cursor is metadata-only: it is
            // NOT another native comparison task or callback occurrence.
            mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)
                .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
            stack.push(InspectCmpContributionFrame {
                task: InspectCmpContributionTask::Collection(cursor),
                mode: InspectCmpContributionMode::Ord, factor: 1,
            });
            // Retain secondary work even when an unknown primary result might
            // decide the actual comparator. Both roles use original pointers.
            if let Some((left, right)) = pair.secondary {
                let constructor = secondary.ok_or(
                    mettail_runtime::NativeComparisonFailure::InvalidCollectionInput(
                        "comparison inspection has no secondary category constructor"))?;
                inspect_cmp_scaled_contribution(state, 4, 1, 0, pair.factor, reserve)?;
                mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)
                    .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
                stack.push(InspectCmpContributionFrame {
                    task: constructor(left, right), mode: InspectCmpContributionMode::Ord,
                    factor: pair.factor,
                });
            }
            inspect_cmp_scaled_contribution(state, 4, 1, 0, pair.factor, reserve)?;
            mettail_runtime::reserve_binding_parts(2, 1, 0, reserve)
                .map_err(mettail_runtime::NativeComparisonFailure::Admission)?;
            stack.push(InspectCmpContributionFrame {
                task: primary(pair.primary.0, pair.primary.1), mode: InspectCmpContributionMode::Ord,
                factor: pair.factor,
            });
            Ok(())
        }
    }
}
