use std::cmp::Ordering;
use std::convert::Infallible;

use crate::{
    reserve_binding_parts, BindingFailure, NativeComparisonFailure,
    CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE,
};

// Both public entrypoints execute the same state transitions. Only the checked
// policy adds admission; ordinary operation has no fallible arithmetic policy.
trait CollectionCmpPolicy {
    type Error;
    fn work(&mut self, work: usize) -> Result<(), Self::Error>;
    fn flat_slots(&mut self, slots: usize) -> Result<(), Self::Error>;
    fn protocol(&mut self, message: &'static str) -> Self::Error;
}

struct OrdinaryPolicy;
impl CollectionCmpPolicy for OrdinaryPolicy {
    type Error = Infallible;
    fn work(&mut self, _: usize) -> Result<(), Infallible> {
        Ok(())
    }
    fn flat_slots(&mut self, _: usize) -> Result<(), Infallible> {
        Ok(())
    }
    fn protocol(&mut self, message: &'static str) -> Infallible {
        panic!("{message}")
    }
}

struct CheckedPolicy<'a, R>(&'a mut R);
impl<E, R: FnMut(usize, usize) -> Result<(), E>> CollectionCmpPolicy for CheckedPolicy<'_, R> {
    type Error = NativeComparisonFailure<E>;
    fn work(&mut self, work: usize) -> Result<(), Self::Error> {
        reserve_binding_parts(work, 0, 0, self.0).map_err(NativeComparisonFailure::Admission)
    }
    fn flat_slots(&mut self, slots: usize) -> Result<(), Self::Error> {
        self.work(1)?;
        let records = slots
            .checked_add(1)
            .ok_or(NativeComparisonFailure::Admission(BindingFailure::SizeOverflow))?;
        let work = records
            .checked_mul(2)
            .ok_or(NativeComparisonFailure::Admission(BindingFailure::SizeOverflow))?;
        reserve_binding_parts(work, records, 0, self.0).map_err(NativeComparisonFailure::Admission)
    }
    fn protocol(&mut self, message: &'static str) -> Self::Error {
        NativeComparisonFailure::InvalidCollectionInput(message)
    }
}

fn ordinary_result<T>(result: Result<T, Infallible>) -> T {
    match result {
        Ok(value) => value,
        Err(never) => match never {},
    }
}

/// A flat pointer roster with prepaid construction and eventual disposal.
///
/// Reserved width, not allocator capacity, bounds pushes. Partial filling is
/// permitted; this does not certify complete source iteration. The caller must
/// retain the borrowed terms and restore each requested pointer's correct type,
/// as with [`CollectionCmpItem`]. No child term is copied or owned here.
#[derive(Debug)]
pub struct CheckedCmpRoster {
    items: Vec<CollectionCmpItem>,
    total: usize,
    reserved_width: usize,
}

impl CheckedCmpRoster {
    /// Pays for borrowing the initialized, unsorted entry slice.
    ///
    /// This preserves every stored occurrence, including aliases, and exposes
    /// neither unused reserved slots nor expanded repetitions. The slice
    /// borrows this roster, not the terms referenced by its raw pointers:
    /// callers must still retain those terms and recover their original types.
    /// Subsequent iteration, indexing, and child jobs need separate admission.
    pub fn try_items<E>(
        &self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<&[CollectionCmpItem], NativeComparisonFailure<E>> {
        // RholangInitialGraphResources: precharged_action with work=1,
        // units=0 and the pure entries projection. No owner mutation.
        CheckedPolicy(reserve).work(1)?;
        Ok(&self.items)
    }

    pub fn try_with_capacity<E>(
        expected_len: usize,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, NativeComparisonFailure<E>> {
        if !CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
            return Err(NativeComparisonFailure::UnsupportedProfile);
        }
        CheckedPolicy(reserve).flat_slots(expected_len)?;
        Ok(Self {
            items: Vec::with_capacity(expected_len),
            total: 0,
            reserved_width: expected_len,
        })
    }

    // Validation precedes item construction; slot copy/disposal is prepaid.
    fn admit_push<E>(
        &self,
        repetitions: usize,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<usize, NativeComparisonFailure<E>> {
        let mut policy = CheckedPolicy(reserve);
        policy.work(1)?;
        if repetitions == 0 {
            return Err(policy.protocol("collection comparison items must be present"));
        }
        if self.items.len() >= self.reserved_width {
            return Err(policy.protocol("collection comparison roster exceeds its reserved width"));
        }
        self.total
            .checked_add(repetitions)
            .ok_or(NativeComparisonFailure::Admission(BindingFailure::SizeOverflow))
    }

    pub fn try_push_unary<T, E>(
        &mut self,
        value: &T,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<(), NativeComparisonFailure<E>> {
        let total = self.admit_push(1, reserve)?;
        self.items.push(CollectionCmpItem::unary(value));
        self.total = total;
        Ok(())
    }

    pub fn try_push_repeated<T, E>(
        &mut self,
        value: &T,
        repetitions: usize,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<(), NativeComparisonFailure<E>> {
        let total = self.admit_push(repetitions, reserve)?;
        self.items
            .push(CollectionCmpItem::repeated(value, repetitions));
        self.total = total;
        Ok(())
    }

    pub fn try_push_pair<K, V, E>(
        &mut self,
        primary: &K,
        secondary: &V,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<(), NativeComparisonFailure<E>> {
        let total = self.admit_push(1, reserve)?;
        self.items.push(CollectionCmpItem::pair(primary, secondary));
        self.total = total;
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
pub struct CollectionCmpItem {
    primary: *const (),
    secondary: Option<*const ()>,
    repetitions: usize,
}

impl CollectionCmpItem {
    /// Pays before copying this entry's original flat metadata.
    ///
    /// No pointer is dereferenced, compared, cast, or validated. The secondary
    /// role and compressed repetition count are preserved exactly; this is
    /// not the unit-pair validation performed by [`Self::try_pair_ptrs`].
    /// The caller retains the original terms and their typed-role association.
    pub fn try_parts<E>(
        &self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<(*const (), Option<*const ()>, usize), NativeComparisonFailure<E>> {
        // Same precharged pure-projection law as CheckedCmpRoster::try_items.
        CheckedPolicy(reserve).work(1)?;
        Ok((self.primary, self.secondary, self.repetitions))
    }

    #[inline]
    pub fn unary<T>(value: &T) -> Self {
        Self::repeated(value, 1)
    }

    #[inline]
    pub fn repeated<T>(value: &T, repetitions: usize) -> Self {
        assert!(repetitions > 0, "collection comparison items must be present");
        Self {
            primary: value as *const T as *const (),
            secondary: None,
            repetitions,
        }
    }

    #[inline]
    pub fn pair<K, V>(primary: &K, secondary: &V) -> Self {
        Self {
            primary: primary as *const K as *const (),
            secondary: Some(secondary as *const V as *const ()),
            repetitions: 1,
        }
    }

    /// Admits flat metadata inspection and returns a unit pair's exact pointers.
    ///
    /// This does not dereference, compare, or certify the borrowed terms. The
    /// caller must retain them and restore their original types before use.
    pub fn try_pair_ptrs<E>(
        &self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<(*const (), *const ()), NativeComparisonFailure<E>> {
        let mut policy = CheckedPolicy(reserve);
        policy.work(1)?;
        match (self.secondary, self.repetitions) {
            (Some(secondary), 1) => Ok((self.primary, secondary)),
            _ => Err(policy.protocol("collection sort requires a unit-multiplicity pair")),
        }
    }
}

/// Consumed continuation for the existing stable bottom-up merge sorter.
///
/// Construction accepts only a prepaid roster. Each comparison request returns
/// the same owner; budget or protocol refusal consumes it. Requested entry
/// comparisons remain the caller's responsibility and need their own admission.
#[derive(Debug)]
pub struct CheckedCollectionSortPda {
    machine: Box<MergeSortPda>,
}

#[derive(Debug)]
pub enum CheckedCollectionSortStep {
    CompareEntries {
        machine: CheckedCollectionSortPda,
        left: CollectionCmpItem,
        right: CollectionCmpItem,
    },
    Done(CheckedSortedCmpRoster),
}

/// Completed sort storage with prepaid normal disposal and admitted reverse pops.
///
/// There is intentionally no append or mutable-slice interface: a merge swap
/// can leave the source allocation smaller than the input's reserved width.
/// These flat records borrow child terms; this owner does not keep them alive.
#[derive(Debug)]
pub struct CheckedSortedCmpRoster {
    items: Vec<CollectionCmpItem>,
}

impl CheckedSortedCmpRoster {
    /// Pays before removing the last sorted entry, including a terminal empty
    /// pop. Reservation failure leaves the remaining roster unchanged.
    pub fn try_pop<E>(
        &mut self,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Option<CollectionCmpItem>, NativeComparisonFailure<E>> {
        CheckedPolicy(reserve).work(1)?;
        Ok(self.items.pop())
    }
}

impl CheckedCollectionSortPda {
    pub fn try_new<E>(
        input: CheckedCmpRoster,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, NativeComparisonFailure<E>> {
        if !CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
            return Err(NativeComparisonFailure::UnsupportedProfile);
        }
        reserve_binding_parts(2, 1, 0, reserve).map_err(NativeComparisonFailure::Admission)?;
        let machine = MergeSortPda::new(input.items, &mut CheckedPolicy(reserve))?;
        Ok(Self { machine: Box::new(machine) })
    }

    /// Supplies exactly one ordering after a request, or None for the initial
    /// step. Done transfers only the sorted source buffer, never a continuation.
    pub fn try_resume<E>(
        mut self,
        result: Option<Ordering>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<CheckedCollectionSortStep, NativeComparisonFailure<E>> {
        let mut policy = CheckedPolicy(reserve);
        policy.work(1)?;
        if let Some(ordering) = result {
            self.machine.accept(ordering, &mut policy)?;
        }
        let step = self.machine.step(&mut policy)?;
        policy.work(1)?;
        match step {
            MergeSortStep::Compare(left, right) => {
                Ok(CheckedCollectionSortStep::CompareEntries { machine: self, left, right })
            },
            MergeSortStep::Done => {
                self.machine.release_scratch(&mut policy)?;
                policy.work(1)?;
                let MergeSortPda { source, .. } = *self.machine;
                Ok(CheckedCollectionSortStep::Done(CheckedSortedCmpRoster { items: source }))
            },
        }
    }
}

/// Sort a borrowed slice with the existing paid stable merge machine.
///
/// Only references enter the two sort buffers: no source payload is cloned,
/// moved, hashed, or dropped. The comparator must reserve its own inspection
/// and comparison work through the same callback before comparing the exact
/// requested pair. A refusal drops only prepaid flat reference storage.
///
/// The driver is the same initial/resume/accept/Done protocol used by
/// [`CheckedCollectionSortPda`]. The generic entry laws in
/// `MergeSortPdaNativeOuter` and `AdmittedCollectionSortOwnership` apply to
/// these shallow entries; they do not establish a cost for arbitrary `Copy`
/// payloads. URI preparation uses this interface to retain each URI's binder
/// association without reconstructing typed references from raw pointers.
pub fn try_sort_borrowed_by<'a, T, E, R, F>(
    source: &'a [T],
    reserve: &mut R,
    mut compare: F,
) -> Result<Vec<&'a T>, NativeComparisonFailure<E>>
where
    R: FnMut(usize, usize) -> Result<(), E>,
    F: FnMut(&T, &T, &mut R) -> Result<Ordering, NativeComparisonFailure<E>>,
{
    if !CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
        return Err(NativeComparisonFailure::UnsupportedProfile);
    }
    CheckedPolicy(reserve).flat_slots(source.len())?;
    let mut entries = Vec::with_capacity(source.len());
    reserve_binding_parts(1, 1, 0, reserve).map_err(NativeComparisonFailure::Admission)?;
    let mut source = source.iter();
    loop {
        CheckedPolicy(reserve).work(1)?;
        let Some(entry) = source.next() else { break };
        CheckedPolicy(reserve).work(1)?;
        entries.push(entry);
    }
    reserve_binding_parts(2, 1, 0, reserve).map_err(NativeComparisonFailure::Admission)?;
    let mut machine = Box::new(MergeSortPda::new(entries, &mut CheckedPolicy(reserve))?);
    let mut result = None;
    loop {
        let mut policy = CheckedPolicy(&mut *reserve);
        policy.work(1)?;
        if let Some(ordering) = result.take() {
            machine.accept(ordering, &mut policy)?;
        }
        let step = machine.step(&mut policy)?;
        policy.work(1)?;
        match step {
            MergeSortStep::Compare(left, right) => {
                result = Some(compare(left, right, reserve)?);
            },
            MergeSortStep::Done => {
                machine.release_scratch(&mut policy)?;
                policy.work(1)?;
                let MergeSortPda { source, .. } = *machine;
                return Ok(source);
            },
        }
    }
}

#[derive(Debug)]
pub enum CollectionCmpStep {
    Compare {
        role: CollectionCmpRole,
        left: *const (),
        right: *const (),
    },
    Done(Ordering),
}

/// Owns rosters and scratch storage whose normal cleanup was prepaid.
///
/// No conversion from an arbitrary ordinary machine exists. Reservations cover
/// logical source groups and flat slots, not physical allocator execution or
/// panic recovery. Native term comparison is still requested from the caller.
#[derive(Debug)]
pub struct CheckedCollectionCmpPda {
    machine: Box<CollectionCmpPda>,
}

#[derive(Debug)]
pub enum CheckedCollectionCmpStep {
    Compare {
        machine: CheckedCollectionCmpPda,
        role: CollectionCmpRole,
        left: *const (),
        right: *const (),
    },
    Done(Ordering),
}

impl CheckedCollectionCmpPda {
    pub fn try_new<E>(
        lead: Ordering,
        left: CheckedCmpRoster,
        right: CheckedCmpRoster,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<Self, NativeComparisonFailure<E>> {
        if !CHECKED_NATIVE_COMPARISON_PROFILE_AVAILABLE {
            return Err(NativeComparisonFailure::UnsupportedProfile);
        }
        reserve_binding_parts(2, 1, 0, reserve).map_err(NativeComparisonFailure::Admission)?;
        let machine = CollectionCmpPda::from_parts(
            lead,
            left.items,
            right.items,
            left.total,
            right.total,
            &mut CheckedPolicy(reserve),
        )?;
        Ok(Self { machine: Box::new(machine) })
    }

    /// Consumes the continuation. Refusal exposes no partially advanced owner;
    /// a successful Compare transfers its existing storage credit unchanged.
    pub fn try_resume<E>(
        mut self,
        result: Option<Ordering>,
        reserve: &mut impl FnMut(usize, usize) -> Result<(), E>,
    ) -> Result<CheckedCollectionCmpStep, NativeComparisonFailure<E>> {
        match self
            .machine
            .resume_with(result, &mut CheckedPolicy(reserve))?
        {
            CollectionCmpStep::Compare { role, left, right } => {
                Ok(CheckedCollectionCmpStep::Compare { machine: self, role, left, right })
            },
            CollectionCmpStep::Done(ordering) => Ok(CheckedCollectionCmpStep::Done(ordering)),
        }
    }
}

/// Identifies which structural position a collection comparison requests.
///
/// Unary collections and map keys use [`Primary`](Self::Primary); map values
/// use [`Secondary`](Self::Secondary).  The distinction is part of the erased
/// PDA protocol because heterogeneous `Map<K, V>` and `PathMap<K, V>` carriers
/// must restore the correct generated category before dereferencing either
/// pointer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CollectionCmpRole {
    Primary,
    Secondary,
}

#[derive(Debug)]
pub struct CollectionCmpPda {
    phase: Phase,
    left: MergeSortPda,
    right: MergeSortPda,
    pending: Option<PendingTermCmp>,
    lead: Ordering,
    left_total: usize,
    right_total: usize,
    left_index: usize,
    right_index: usize,
    left_remaining: usize,
    right_remaining: usize,
}

impl CollectionCmpPda {
    pub fn new(
        lead: Ordering,
        left: Vec<CollectionCmpItem>,
        right: Vec<CollectionCmpItem>,
    ) -> Self {
        let left_total = left.iter().map(|item| item.repetitions).sum();
        let right_total = right.iter().map(|item| item.repetitions).sum();
        ordinary_result(Self::from_parts(
            lead,
            left,
            right,
            left_total,
            right_total,
            &mut OrdinaryPolicy,
        ))
    }

    fn from_parts<P: CollectionCmpPolicy>(
        lead: Ordering,
        left: Vec<CollectionCmpItem>,
        right: Vec<CollectionCmpItem>,
        left_total: usize,
        right_total: usize,
        policy: &mut P,
    ) -> Result<Self, P::Error> {
        policy.work(1)?;
        Ok(Self {
            phase: Phase::Lead,
            left: MergeSortPda::new(left, policy)?,
            right: MergeSortPda::new(right, policy)?,
            pending: None,
            lead,
            left_total,
            right_total,
            left_index: 0,
            right_index: 0,
            left_remaining: 0,
            right_remaining: 0,
        })
    }

    pub fn resume(&mut self, result: Option<Ordering>) -> CollectionCmpStep {
        ordinary_result(self.resume_with(result, &mut OrdinaryPolicy))
    }

    fn resume_with<P: CollectionCmpPolicy>(
        &mut self,
        result: Option<Ordering>,
        policy: &mut P,
    ) -> Result<CollectionCmpStep, P::Error> {
        policy.work(1)?;
        match (self.pending.take(), result) {
            (Some(pending), Some(ordering)) => {
                if let Some(step) = self.accept_term_comparison(pending, ordering, policy)? {
                    return Ok(step);
                }
            },
            (None, None) => {},
            (Some(pending), None) => {
                self.pending = Some(pending);
                return Err(policy
                    .protocol("collection comparison PDA resumed without its requested result"));
            },
            (None, Some(_)) => {
                return Err(
                    policy.protocol("collection comparison PDA received an unrequested result")
                );
            },
        }

        loop {
            policy.work(1)?;
            match self.phase {
                Phase::Lead => {
                    if self.lead != Ordering::Equal {
                        self.phase = Phase::Done;
                        return Ok(CollectionCmpStep::Done(self.lead));
                    }
                    self.phase = Phase::SortLeft;
                },
                Phase::SortLeft => {
                    let step = self.left.step(policy)?;
                    policy.work(1)?;
                    match step {
                        MergeSortStep::Compare(left, right) => {
                            if let Some(step) = self.request_item_comparison(
                                left,
                                right,
                                Destination::SortLeft,
                                policy,
                            )? {
                                return Ok(step);
                            }
                        },
                        MergeSortStep::Done => {
                            self.left.release_scratch(policy)?;
                            self.phase = Phase::SortRight;
                        },
                    }
                },
                Phase::SortRight => {
                    let step = self.right.step(policy)?;
                    policy.work(1)?;
                    match step {
                        MergeSortStep::Compare(left, right) => {
                            if let Some(step) = self.request_item_comparison(
                                left,
                                right,
                                Destination::SortRight,
                                policy,
                            )? {
                                return Ok(step);
                            }
                        },
                        MergeSortStep::Done => {
                            self.right.release_scratch(policy)?;
                            self.phase = Phase::Lexicographic;
                        },
                    }
                },
                Phase::Lexicographic => {
                    let Some(left) = self.current_left(policy)? else {
                        policy.work(2)?;
                        self.phase = Phase::Done;
                        return Ok(CollectionCmpStep::Done(self.left_total.cmp(&self.right_total)));
                    };
                    let Some(right) = self.current_right(policy)? else {
                        policy.work(2)?;
                        self.phase = Phase::Done;
                        return Ok(CollectionCmpStep::Done(self.left_total.cmp(&self.right_total)));
                    };
                    if let Some(step) = self.request_item_comparison(
                        left,
                        right,
                        Destination::Lexicographic,
                        policy,
                    )? {
                        return Ok(step);
                    }
                },
                Phase::Done => {
                    return Err(
                        policy.protocol("collection comparison PDA resumed after completion")
                    )
                },
            }
        }
    }

    fn request_item_comparison<P: CollectionCmpPolicy>(
        &mut self,
        left: CollectionCmpItem,
        right: CollectionCmpItem,
        destination: Destination,
        policy: &mut P,
    ) -> Result<Option<CollectionCmpStep>, P::Error> {
        policy.work(1)?;
        if left.primary == right.primary {
            return self.request_secondary_or_accept(left, right, destination, policy);
        }
        self.pending = Some(PendingTermCmp::Primary { left, right, destination });
        Ok(Some(CollectionCmpStep::Compare {
            role: CollectionCmpRole::Primary,
            left: left.primary,
            right: right.primary,
        }))
    }

    fn request_secondary_or_accept<P: CollectionCmpPolicy>(
        &mut self,
        left: CollectionCmpItem,
        right: CollectionCmpItem,
        destination: Destination,
        policy: &mut P,
    ) -> Result<Option<CollectionCmpStep>, P::Error> {
        policy.work(1)?;
        match (left.secondary, right.secondary) {
            (None, None) => {
                self.accept_item_comparison(destination, Ordering::Equal, policy)?;
                Ok(None)
            },
            (None, Some(_)) => {
                self.accept_item_comparison(destination, Ordering::Less, policy)?;
                Ok(None)
            },
            (Some(_), None) => {
                self.accept_item_comparison(destination, Ordering::Greater, policy)?;
                Ok(None)
            },
            (Some(left), Some(right)) if left == right => {
                self.accept_item_comparison(destination, Ordering::Equal, policy)?;
                Ok(None)
            },
            (Some(left), Some(right)) => {
                self.pending = Some(PendingTermCmp::Secondary { destination });
                Ok(Some(CollectionCmpStep::Compare {
                    role: CollectionCmpRole::Secondary,
                    left,
                    right,
                }))
            },
        }
    }

    fn accept_term_comparison<P: CollectionCmpPolicy>(
        &mut self,
        pending: PendingTermCmp,
        ordering: Ordering,
        policy: &mut P,
    ) -> Result<Option<CollectionCmpStep>, P::Error> {
        policy.work(1)?;
        match pending {
            PendingTermCmp::Primary { left, right, destination } => {
                if ordering == Ordering::Equal {
                    return self.request_secondary_or_accept(left, right, destination, policy);
                }
                self.accept_item_comparison(destination, ordering, policy)?;
            },
            PendingTermCmp::Secondary { destination } => {
                self.accept_item_comparison(destination, ordering, policy)?;
            },
        }
        Ok(None)
    }

    fn accept_item_comparison<P: CollectionCmpPolicy>(
        &mut self,
        destination: Destination,
        ordering: Ordering,
        policy: &mut P,
    ) -> Result<(), P::Error> {
        policy.work(1)?;
        match destination {
            Destination::SortLeft => self.left.accept(ordering, policy)?,
            Destination::SortRight => self.right.accept(ordering, policy)?,
            Destination::Lexicographic if ordering == Ordering::Equal => {
                self.advance_equal_run(policy)?
            },
            Destination::Lexicographic => {
                self.lead = ordering;
                self.phase = Phase::Lead;
            },
        }
        Ok(())
    }

    fn current_left<P: CollectionCmpPolicy>(
        &mut self,
        policy: &mut P,
    ) -> Result<Option<CollectionCmpItem>, P::Error> {
        policy.work(1)?;
        let Some(&item) = self.left.items().get(self.left_index) else {
            return Ok(None);
        };
        if self.left_remaining == 0 {
            self.left_remaining = item.repetitions;
        }
        Ok(Some(item))
    }

    fn current_right<P: CollectionCmpPolicy>(
        &mut self,
        policy: &mut P,
    ) -> Result<Option<CollectionCmpItem>, P::Error> {
        policy.work(1)?;
        let Some(&item) = self.right.items().get(self.right_index) else {
            return Ok(None);
        };
        if self.right_remaining == 0 {
            self.right_remaining = item.repetitions;
        }
        Ok(Some(item))
    }

    fn advance_equal_run<P: CollectionCmpPolicy>(
        &mut self,
        policy: &mut P,
    ) -> Result<(), P::Error> {
        policy.work(1)?;
        let consumed = self.left_remaining.min(self.right_remaining);
        self.left_remaining -= consumed;
        self.right_remaining -= consumed;
        if self.left_remaining == 0 {
            self.left_index += 1;
        }
        if self.right_remaining == 0 {
            self.right_index += 1;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
enum Phase {
    Lead,
    SortLeft,
    SortRight,
    Lexicographic,
    Done,
}

#[derive(Clone, Copy, Debug)]
enum Destination {
    SortLeft,
    SortRight,
    Lexicographic,
}

#[derive(Clone, Copy, Debug)]
enum PendingTermCmp {
    Primary {
        left: CollectionCmpItem,
        right: CollectionCmpItem,
        destination: Destination,
    },
    Secondary {
        destination: Destination,
    },
}

#[derive(Debug)]
struct MergeSortPda<Entry = CollectionCmpItem> {
    source: Vec<Entry>,
    target: Option<Vec<Entry>>,
    width: usize,
    start: usize,
    middle: usize,
    end: usize,
    left: usize,
    right: usize,
    output: usize,
    waiting: bool,
    done: bool,
}

impl<Entry: Copy> MergeSortPda<Entry> {
    fn new<P: CollectionCmpPolicy>(source: Vec<Entry>, policy: &mut P) -> Result<Self, P::Error> {
        policy.work(1)?;
        let done = source.len() < 2;
        let mut pda = Self {
            source,
            target: None,
            width: 1,
            start: 0,
            middle: 0,
            end: 0,
            left: 0,
            right: 0,
            output: 0,
            waiting: false,
            done,
        };
        pda.reset_run(policy)?;
        Ok(pda)
    }

    fn items(&self) -> &[Entry] {
        &self.source
    }

    fn step<P: CollectionCmpPolicy>(
        &mut self,
        policy: &mut P,
    ) -> Result<MergeSortStep<Entry>, P::Error> {
        policy.work(1)?;
        if self.waiting {
            return Err(policy.protocol("merge-sort PDA advanced before comparison result"));
        }
        if !self.done && self.target.is_none() {
            policy.flat_slots(self.source.len())?;
            self.target = Some(self.source.clone());
        }
        while {
            policy.work(1)?;
            !self.done
        } {
            policy.work(1)?;
            if self.left < self.middle && self.right < self.end {
                self.waiting = true;
                return Ok(MergeSortStep::Compare(self.source[self.left], self.source[self.right]));
            }
            while {
                policy.work(1)?;
                self.left < self.middle
            } {
                policy.work(1)?;
                self.target.as_mut().expect("merge target exists")[self.output] =
                    self.source[self.left];
                self.left += 1;
                self.output += 1;
            }
            while {
                policy.work(1)?;
                self.right < self.end
            } {
                policy.work(1)?;
                self.target.as_mut().expect("merge target exists")[self.output] =
                    self.source[self.right];
                self.right += 1;
                self.output += 1;
            }
            policy.work(1)?;
            self.start = self.end;
            if self.start >= self.source.len() {
                policy.work(1)?;
                std::mem::swap(
                    &mut self.source,
                    self.target.as_mut().expect("merge target exists"),
                );
                self.width = self.width.saturating_mul(2);
                if self.width >= self.source.len() {
                    self.done = true;
                    break;
                }
                self.start = 0;
            }
            self.reset_run(policy)?;
        }
        Ok(MergeSortStep::Done)
    }

    fn accept<P: CollectionCmpPolicy>(
        &mut self,
        ordering: Ordering,
        policy: &mut P,
    ) -> Result<(), P::Error> {
        policy.work(1)?;
        if !self.waiting {
            return Err(policy.protocol("merge-sort PDA received an unrequested comparison result"));
        }
        self.waiting = false;
        if ordering != Ordering::Greater {
            policy.work(1)?;
            self.target.as_mut().expect("merge target exists")[self.output] =
                self.source[self.left];
            self.left += 1;
        } else {
            policy.work(1)?;
            self.target.as_mut().expect("merge target exists")[self.output] =
                self.source[self.right];
            self.right += 1;
        }
        self.output += 1;
        Ok(())
    }

    fn reset_run<P: CollectionCmpPolicy>(&mut self, policy: &mut P) -> Result<(), P::Error> {
        policy.work(1)?;
        self.middle = self.start.saturating_add(self.width).min(self.source.len());
        self.end = self
            .start
            .saturating_add(self.width.saturating_mul(2))
            .min(self.source.len());
        self.left = self.start;
        self.right = self.middle;
        self.output = self.start;
        Ok(())
    }

    fn release_scratch<P: CollectionCmpPolicy>(&mut self, policy: &mut P) -> Result<(), P::Error> {
        policy.work(1)?;
        self.target = None;
        Ok(())
    }
}

enum MergeSortStep<Entry = CollectionCmpItem> {
    Compare(Entry, Entry),
    Done,
}

#[cfg(all(test, mettail_checked_native_comparison_profile))]
#[path = "collection_cmp_pda_checked_tests.rs"]
mod checked_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn run(mut pda: CollectionCmpPda) -> Ordering {
        let mut result = None;
        loop {
            match pda.resume(result.take()) {
                CollectionCmpStep::Compare { left, right, .. } => {
                    result = Some(unsafe { (*(left.cast::<i32>())).cmp(&*(right.cast::<i32>())) });
                },
                CollectionCmpStep::Done(ordering) => return ordering,
            }
        }
    }

    fn unary(values: &[i32]) -> Vec<CollectionCmpItem> {
        values.iter().map(CollectionCmpItem::unary).collect()
    }

    proptest! {
        #[test]
        fn unary_items_match_sorted_vector_order(left in prop::collection::vec(any::<i32>(), 0..80), right in prop::collection::vec(any::<i32>(), 0..80)) {
            let mut expected_left = left.clone();
            let mut expected_right = right.clone();
            expected_left.sort();
            expected_right.sort();
            prop_assert_eq!(run(CollectionCmpPda::new(Ordering::Equal, unary(&left), unary(&right))), expected_left.cmp(&expected_right));
        }

        #[test]
        fn paired_items_match_sorted_tuple_order(left in prop::collection::vec((any::<i32>(), any::<i32>()), 0..80), right in prop::collection::vec((any::<i32>(), any::<i32>()), 0..80)) {
            let left_items = left.iter().map(|(a, b)| CollectionCmpItem::pair(a, b)).collect();
            let right_items = right.iter().map(|(a, b)| CollectionCmpItem::pair(a, b)).collect();
            let mut expected_left = left.clone();
            let mut expected_right = right.clone();
            expected_left.sort();
            expected_right.sort();
            prop_assert_eq!(run(CollectionCmpPda::new(Ordering::Equal, left_items, right_items)), expected_left.cmp(&expected_right));
        }

        #[test]
        fn repeated_items_match_expanded_bag_order(left in prop::collection::vec((any::<i32>(), 1usize..20), 0..30), right in prop::collection::vec((any::<i32>(), 1usize..20), 0..30)) {
            let left_items = left.iter().map(|(value, count)| CollectionCmpItem::repeated(value, *count)).collect();
            let right_items = right.iter().map(|(value, count)| CollectionCmpItem::repeated(value, *count)).collect();
            let mut expected_left: Vec<i32> = left.iter().flat_map(|(value, count)| std::iter::repeat_n(*value, *count)).collect();
            let mut expected_right: Vec<i32> = right.iter().flat_map(|(value, count)| std::iter::repeat_n(*value, *count)).collect();
            expected_left.sort();
            expected_right.sort();
            prop_assert_eq!(run(CollectionCmpPda::new(Ordering::Equal, left_items, right_items)), expected_left.cmp(&expected_right));
        }
    }

    #[test]
    fn heterogeneous_pairs_report_the_exact_pointer_role() {
        let left = [(1_i32, String::from("left"))];
        let right = [(1_i32, String::from("right"))];
        let left_items = left
            .iter()
            .map(|(key, value)| CollectionCmpItem::pair(key, value))
            .collect();
        let right_items = right
            .iter()
            .map(|(key, value)| CollectionCmpItem::pair(key, value))
            .collect();
        let mut pda = CollectionCmpPda::new(Ordering::Equal, left_items, right_items);
        let mut result = None;
        let mut saw_primary = false;
        let mut saw_secondary = false;

        loop {
            match pda.resume(result.take()) {
                CollectionCmpStep::Compare { role, left, right } => match role {
                    CollectionCmpRole::Primary => {
                        saw_primary = true;
                        result =
                            Some(unsafe { (*(left.cast::<i32>())).cmp(&*(right.cast::<i32>())) });
                    },
                    CollectionCmpRole::Secondary => {
                        saw_secondary = true;
                        result = Some(unsafe {
                            (*(left.cast::<String>())).cmp(&*(right.cast::<String>()))
                        });
                    },
                },
                CollectionCmpStep::Done(ordering) => {
                    assert_eq!(ordering, Ordering::Less);
                    break;
                },
            }
        }

        assert!(saw_primary);
        assert!(saw_secondary);
    }

    #[test]
    fn leading_order_short_circuits_before_element_comparison() {
        let left = [1];
        let right = [0];
        assert_eq!(
            run(CollectionCmpPda::new(Ordering::Less, unary(&left), unary(&right))),
            Ordering::Less,
        );
    }
}
