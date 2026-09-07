//! Source-ordered Cartesian coordinates without allocating the product.
//!
//! Each digit is an occurrence, even when several rows share the same forest
//! node or contain equal values. The rightmost digit changes fastest. The
//! implementation refines `CartesianCursor.v`: initialization distinguishes
//! zero rows from an empty row, and advancing removes exactly one coordinate.
//! This cursor does not assert that its input families are complete, rank
//! candidates, deduplicate values, or impose an output quota.

use super::ReconstructionFailure;

#[derive(Debug)]
struct Digit {
    bound: usize,
    index: usize,
}

#[derive(Debug)]
pub(crate) struct CartesianCursor {
    digits: Vec<Digit>,
    has_current: bool,
}

impl CartesianCursor {
    /// Bounds are row lengths, not their product. Check the width before
    /// reserving storage; allocation failure is not an empty semantic family.
    pub(crate) fn try_new(
        bounds: impl ExactSizeIterator<Item = usize>,
        max_width: usize,
    ) -> Result<Self, ReconstructionFailure> {
        let width = bounds.len();
        if width > max_width {
            return Err(ReconstructionFailure::TraversalLimit { limit: max_width });
        }
        let mut digits = Vec::new();
        digits
            .try_reserve_exact(width)
            .map_err(|_| ReconstructionFailure::AllocationFailed { requested: width })?;
        let mut has_current = true;
        for bound in bounds {
            has_current &= bound != 0;
            digits.push(Digit { bound, index: 0 });
        }
        Ok(Self { digits, has_current })
    }

    /// Borrow the current source-ordered coordinate. The caller advances only
    /// after consuming this occurrence; pausing leaves the exact suffix intact.
    pub(crate) fn current(&self) -> Option<impl ExactSizeIterator<Item = usize> + '_> {
        self.has_current
            .then(|| self.digits.iter().map(|digit| digit.index))
    }

    /// In-place mixed-radix carry, with constant native stack usage. Testing
    /// against bound - 1 precedes the increment, including at usize::MAX.
    pub(crate) fn advance(&mut self) -> bool {
        if !self.has_current {
            return false;
        }
        for digit in self.digits.iter_mut().rev() {
            // A live cursor has only positive bounds, established by try_new.
            if digit.index < digit.bound - 1 {
                digit.index += 1;
                return true;
            }
            digit.index = 0;
        }
        self.has_current = false;
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn coordinates(bounds: &[usize]) -> Vec<Vec<usize>> {
        let mut cursor = CartesianCursor::try_new(bounds.iter().copied(), bounds.len())
            .expect("small coordinate bounds");
        let mut result = Vec::new();
        loop {
            let Some(indices) = cursor.current() else {
                break;
            };
            result.push(indices.collect());
            cursor.advance();
        }
        assert!(!cursor.advance(), "exhaustion must be stable");
        result
    }

    // Deliberately independent, bounded test oracle; never used by production.
    fn product_oracle(bounds: &[usize]) -> Vec<Vec<usize>> {
        let Some((&bound, tail)) = bounds.split_first() else {
            return vec![Vec::new()];
        };
        let suffixes = product_oracle(tail);
        (0..bound)
            .flat_map(|index| {
                suffixes.iter().map(move |suffix| {
                    std::iter::once(index)
                        .chain(suffix.iter().copied())
                        .collect()
                })
            })
            .collect()
    }

    #[test]
    fn cartesian_cursor_matches_all_small_ordered_products() {
        for width in 0..=4 {
            for mut encoded in 0..4usize.pow(width as u32) {
                let bounds: Vec<_> = (0..width)
                    .map(|_| {
                        let bound = encoded % 4;
                        encoded /= 4;
                        bound
                    })
                    .collect();
                assert_eq!(coordinates(&bounds), product_oracle(&bounds), "{bounds:?}");
            }
        }
    }

    #[test]
    fn cartesian_cursor_distinguishes_empty_row_from_zero_rows() {
        assert_eq!(coordinates(&[]), vec![Vec::<usize>::new()]);
        assert!(coordinates(&[2, 0, 2]).is_empty());
        assert_eq!(coordinates(&[2, 2]), vec![vec![0, 0], vec![0, 1], vec![1, 0], vec![1, 1]]);
    }

    #[test]
    fn cartesian_cursor_resumes_without_replay_or_skipping() {
        let mut cursor = CartesianCursor::try_new([2, 2].into_iter(), 2).expect("two rows");
        assert_eq!(cursor.current().expect("first").collect::<Vec<_>>(), vec![0, 0]);
        assert!(cursor.advance());
        assert_eq!(cursor.current().expect("second").collect::<Vec<_>>(), vec![0, 1]);
        assert_eq!(cursor.current().expect("still second").collect::<Vec<_>>(), vec![0, 1]);
        assert!(cursor.advance());
        assert_eq!(cursor.current().expect("third").collect::<Vec<_>>(), vec![1, 0]);
    }

    #[test]
    fn cartesian_cursor_never_multiplies_cardinalities_or_overflows_carry() {
        let mut cursor = CartesianCursor::try_new([usize::MAX, usize::MAX].into_iter(), 2)
            .expect("only two digits are stored");
        cursor.digits[0].index = usize::MAX - 1;
        cursor.digits[1].index = usize::MAX - 2;
        assert!(cursor.advance());
        assert_eq!(cursor.current().expect("last").collect::<Vec<_>>(), vec![usize::MAX - 1; 2]);
        assert!(!cursor.advance());
        assert!(cursor.current().is_none());
    }

    #[test]
    fn cartesian_cursor_checks_width_before_reading_or_allocating_rows() {
        let bounds = std::iter::repeat_n(1, 17).map(|_| panic!("must not read a rejected row"));
        assert!(matches!(
            CartesianCursor::try_new(bounds, 16),
            Err(ReconstructionFailure::TraversalLimit { limit: 16 })
        ));
        assert!(matches!(
            CartesianCursor::try_new(std::iter::repeat_n(1, usize::MAX), usize::MAX),
            Err(ReconstructionFailure::AllocationFailed { requested: usize::MAX })
        ));
    }

    #[test]
    fn cartesian_cursor_carries_a_wide_coordinate_on_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let mut cursor = CartesianCursor::try_new(std::iter::repeat_n(1, 100_000), 100_000)
                    .expect("bounded wide cursor");
                assert_eq!(cursor.current().expect("one coordinate").count(), 100_000);
                assert!(!cursor.advance());
                assert!(cursor.current().is_none());
            })
            .expect("small-stack thread")
            .join()
            .expect("wide carry must remain stack safe");
    }
}
