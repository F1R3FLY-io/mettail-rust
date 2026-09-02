use std::cmp::Ordering;

#[derive(Clone, Copy, Debug)]
pub struct CollectionCmpItem {
    primary: *const (),
    secondary: Option<*const ()>,
    repetitions: usize,
}

impl CollectionCmpItem {
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
        Self {
            phase: Phase::Lead,
            left: MergeSortPda::new(left),
            right: MergeSortPda::new(right),
            pending: None,
            lead,
            left_total,
            right_total,
            left_index: 0,
            right_index: 0,
            left_remaining: 0,
            right_remaining: 0,
        }
    }

    pub fn resume(&mut self, result: Option<Ordering>) -> CollectionCmpStep {
        match (self.pending.take(), result) {
            (Some(pending), Some(ordering)) => {
                if let Some(step) = self.accept_term_comparison(pending, ordering) {
                    return step;
                }
            },
            (None, None) => {},
            (Some(pending), None) => {
                self.pending = Some(pending);
                panic!("collection comparison PDA resumed without its requested result");
            },
            (None, Some(_)) => {
                panic!("collection comparison PDA received an unrequested result");
            },
        }

        loop {
            match self.phase {
                Phase::Lead => {
                    if self.lead != Ordering::Equal {
                        self.phase = Phase::Done;
                        return CollectionCmpStep::Done(self.lead);
                    }
                    self.phase = Phase::SortLeft;
                },
                Phase::SortLeft => match self.left.step() {
                    MergeSortStep::Compare(left, right) => {
                        if let Some(step) =
                            self.request_item_comparison(left, right, Destination::SortLeft)
                        {
                            return step;
                        }
                    },
                    MergeSortStep::Done => {
                        self.left.release_scratch();
                        self.phase = Phase::SortRight;
                    },
                },
                Phase::SortRight => match self.right.step() {
                    MergeSortStep::Compare(left, right) => {
                        if let Some(step) =
                            self.request_item_comparison(left, right, Destination::SortRight)
                        {
                            return step;
                        }
                    },
                    MergeSortStep::Done => {
                        self.right.release_scratch();
                        self.phase = Phase::Lexicographic;
                    },
                },
                Phase::Lexicographic => {
                    let Some(left) = self.current_left() else {
                        self.phase = Phase::Done;
                        return CollectionCmpStep::Done(self.left_total.cmp(&self.right_total));
                    };
                    let Some(right) = self.current_right() else {
                        self.phase = Phase::Done;
                        return CollectionCmpStep::Done(self.left_total.cmp(&self.right_total));
                    };
                    if let Some(step) =
                        self.request_item_comparison(left, right, Destination::Lexicographic)
                    {
                        return step;
                    }
                },
                Phase::Done => panic!("collection comparison PDA resumed after completion"),
            }
        }
    }

    fn request_item_comparison(
        &mut self,
        left: CollectionCmpItem,
        right: CollectionCmpItem,
        destination: Destination,
    ) -> Option<CollectionCmpStep> {
        if left.primary == right.primary {
            return self.request_secondary_or_accept(left, right, destination);
        }
        self.pending = Some(PendingTermCmp::Primary { left, right, destination });
        Some(CollectionCmpStep::Compare {
            role: CollectionCmpRole::Primary,
            left: left.primary,
            right: right.primary,
        })
    }

    fn request_secondary_or_accept(
        &mut self,
        left: CollectionCmpItem,
        right: CollectionCmpItem,
        destination: Destination,
    ) -> Option<CollectionCmpStep> {
        match (left.secondary, right.secondary) {
            (None, None) => {
                self.accept_item_comparison(destination, Ordering::Equal);
                None
            },
            (None, Some(_)) => {
                self.accept_item_comparison(destination, Ordering::Less);
                None
            },
            (Some(_), None) => {
                self.accept_item_comparison(destination, Ordering::Greater);
                None
            },
            (Some(left), Some(right)) if left == right => {
                self.accept_item_comparison(destination, Ordering::Equal);
                None
            },
            (Some(left), Some(right)) => {
                self.pending = Some(PendingTermCmp::Secondary { destination });
                Some(CollectionCmpStep::Compare {
                    role: CollectionCmpRole::Secondary,
                    left,
                    right,
                })
            },
        }
    }

    fn accept_term_comparison(
        &mut self,
        pending: PendingTermCmp,
        ordering: Ordering,
    ) -> Option<CollectionCmpStep> {
        match pending {
            PendingTermCmp::Primary { left, right, destination } => {
                if ordering == Ordering::Equal {
                    return self.request_secondary_or_accept(left, right, destination);
                }
                self.accept_item_comparison(destination, ordering);
            },
            PendingTermCmp::Secondary { destination } => {
                self.accept_item_comparison(destination, ordering);
            },
        }
        None
    }

    fn accept_item_comparison(&mut self, destination: Destination, ordering: Ordering) {
        match destination {
            Destination::SortLeft => self.left.accept(ordering),
            Destination::SortRight => self.right.accept(ordering),
            Destination::Lexicographic if ordering == Ordering::Equal => self.advance_equal_run(),
            Destination::Lexicographic => {
                self.lead = ordering;
                self.phase = Phase::Lead;
            },
        }
    }

    fn current_left(&mut self) -> Option<CollectionCmpItem> {
        let item = *self.left.items().get(self.left_index)?;
        if self.left_remaining == 0 {
            self.left_remaining = item.repetitions;
        }
        Some(item)
    }

    fn current_right(&mut self) -> Option<CollectionCmpItem> {
        let item = *self.right.items().get(self.right_index)?;
        if self.right_remaining == 0 {
            self.right_remaining = item.repetitions;
        }
        Some(item)
    }

    fn advance_equal_run(&mut self) {
        let consumed = self.left_remaining.min(self.right_remaining);
        self.left_remaining -= consumed;
        self.right_remaining -= consumed;
        if self.left_remaining == 0 {
            self.left_index += 1;
        }
        if self.right_remaining == 0 {
            self.right_index += 1;
        }
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
struct MergeSortPda {
    source: Vec<CollectionCmpItem>,
    target: Option<Vec<CollectionCmpItem>>,
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

impl MergeSortPda {
    fn new(source: Vec<CollectionCmpItem>) -> Self {
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
        pda.reset_run();
        pda
    }

    fn items(&self) -> &[CollectionCmpItem] {
        &self.source
    }

    fn step(&mut self) -> MergeSortStep {
        assert!(!self.waiting, "merge-sort PDA advanced before comparison result");
        if !self.done && self.target.is_none() {
            self.target = Some(self.source.clone());
        }
        while !self.done {
            if self.left < self.middle && self.right < self.end {
                self.waiting = true;
                return MergeSortStep::Compare(self.source[self.left], self.source[self.right]);
            }
            while self.left < self.middle {
                self.target.as_mut().expect("merge target exists")[self.output] =
                    self.source[self.left];
                self.left += 1;
                self.output += 1;
            }
            while self.right < self.end {
                self.target.as_mut().expect("merge target exists")[self.output] =
                    self.source[self.right];
                self.right += 1;
                self.output += 1;
            }
            self.start = self.end;
            if self.start >= self.source.len() {
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
            self.reset_run();
        }
        MergeSortStep::Done
    }

    fn accept(&mut self, ordering: Ordering) {
        assert!(self.waiting, "merge-sort PDA received an unrequested comparison result");
        self.waiting = false;
        if ordering != Ordering::Greater {
            self.target.as_mut().expect("merge target exists")[self.output] =
                self.source[self.left];
            self.left += 1;
        } else {
            self.target.as_mut().expect("merge target exists")[self.output] =
                self.source[self.right];
            self.right += 1;
        }
        self.output += 1;
    }

    fn reset_run(&mut self) {
        self.middle = self.start.saturating_add(self.width).min(self.source.len());
        self.end = self
            .start
            .saturating_add(self.width.saturating_mul(2))
            .min(self.source.len());
        self.left = self.start;
        self.right = self.middle;
        self.output = self.start;
    }

    fn release_scratch(&mut self) {
        self.target = None;
    }
}

enum MergeSortStep {
    Compare(CollectionCmpItem, CollectionCmpItem),
    Done,
}

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
