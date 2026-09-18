//! Retained-shape arithmetic for the existing owned native values.
//!
//! This implements the finite receipt algebra in RholangDeepConstructionSize.v.
//! Counts are logical records and payload lengths, not allocations, RSS, gas,
//! or operation charges. Callers admit iterator work and native construction
//! separately. The arithmetic uses constant storage with no internal heap
//! allocation, native constructor invocation, or Par scan.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReceiptError {
    Overflow,
    IncompleteMapPair { children: usize },
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct NativeCounts {
    pub(crate) heads: usize,
    pub(crate) payload_bytes: usize,
    pub(crate) name_entries: usize,
    pub(crate) metadata_bytes: usize,
    pub(crate) descendant_pars: usize,
    pub(crate) receive_binds: usize,
    pub(crate) map_pairs: usize,
    pub(crate) remainder_vars: usize,
}

fn add(left: usize, right: usize) -> Result<usize, ReceiptError> {
    left.checked_add(right).ok_or(ReceiptError::Overflow)
}

impl NativeCounts {
    pub(crate) fn checked_add(self, right: Self) -> Result<Self, ReceiptError> {
        Ok(Self {
            heads: add(self.heads, right.heads)?,
            payload_bytes: add(self.payload_bytes, right.payload_bytes)?,
            name_entries: add(self.name_entries, right.name_entries)?,
            metadata_bytes: add(self.metadata_bytes, right.metadata_bytes)?,
            descendant_pars: add(self.descendant_pars, right.descendant_pars)?,
            receive_binds: add(self.receive_binds, right.receive_binds)?,
            map_pairs: add(self.map_pairs, right.map_pairs)?,
            remainder_vars: add(self.remainder_vars, right.remainder_vars)?,
        })
    }
}

/// Constructor-local retained fields, already supplied by their source owner.
/// Resource-equivalent constructors share a variant: Plain covers fixed-size
/// scalar, Boolean, variable, unary/binary and connective heads; Payload covers text
/// and admitted host-name byte payloads. Receive slot names are not native
/// payloads. Fresh counts include all URI/key occurrences, not distinct names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NativeHead {
    Plain,
    Payload {
        bytes: usize,
    },
    List {
        remainder: bool,
    },
    Map {
        remainder: bool,
    },
    Method {
        name_bytes: usize,
    },
    Send,
    Fresh {
        uri_entries: usize,
        uri_bytes: usize,
        injection_entries: usize,
        key_bytes: usize,
    },
    Receive {
        binds: usize,
        remainders: usize,
    },
}

impl NativeHead {
    fn local_counts(
        self,
        outer_metadata_bytes: usize,
        children: usize,
    ) -> Result<NativeCounts, ReceiptError> {
        let mut counts = NativeCounts { heads: 1, ..NativeCounts::default() };
        match self {
            Self::Plain => {},
            Self::Payload { bytes } => counts.payload_bytes = bytes,
            Self::List { remainder } => {
                counts.metadata_bytes = outer_metadata_bytes;
                counts.remainder_vars = usize::from(remainder);
            },
            Self::Map { remainder } => {
                if children % 2 != 0 {
                    return Err(ReceiptError::IncompleteMapPair { children });
                }
                counts.metadata_bytes = outer_metadata_bytes;
                counts.map_pairs = children / 2;
                counts.remainder_vars = usize::from(remainder);
            },
            Self::Method { name_bytes } => {
                counts.payload_bytes = name_bytes;
                counts.metadata_bytes = outer_metadata_bytes;
            },
            Self::Send => counts.metadata_bytes = outer_metadata_bytes,
            Self::Fresh {
                uri_entries,
                uri_bytes,
                injection_entries,
                key_bytes,
            } => {
                counts.name_entries = add(uri_entries, injection_entries)?;
                counts.payload_bytes = add(uri_bytes, key_bytes)?;
                counts.metadata_bytes = outer_metadata_bytes;
            },
            Self::Receive { binds, remainders } => {
                counts.receive_binds = binds;
                counts.remainder_vars = remainders;
                counts.metadata_bytes = outer_metadata_bytes;
            },
        }
        Ok(counts)
    }
}

/// Current outer Par metadata is separate from owned head/descendant metadata.
/// Components are exact when the producer retains all supplied children. If
/// native map construction removes duplicate entries, input sums conservatively
/// bound the retained image; this type does not claim to identify that selection.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct NativeReceipt {
    pub(crate) outer_metadata_bytes: usize,
    pub(crate) owned: NativeCounts,
}

impl NativeReceipt {
    pub(crate) fn empty() -> Self {
        Self::default()
    }

    /// Fold borrowed receipts in constructor order, counting repeated children
    /// repeatedly. Child roots become descendants, and their outer metadata
    /// becomes nested metadata. Caller admission covers this iterator's cost.
    pub(crate) fn construct<'a>(
        head: NativeHead,
        outer_metadata_bytes: usize,
        children: impl IntoIterator<Item = &'a Self>,
    ) -> Result<Self, ReceiptError> {
        let mut child_count = 0;
        let mut owned = NativeCounts::default();
        for child in children {
            child_count = add(child_count, 1)?;
            let embedded = NativeCounts {
                metadata_bytes: add(child.outer_metadata_bytes, child.owned.metadata_bytes)?,
                descendant_pars: add(child.owned.descendant_pars, 1)?,
                ..child.owned
            };
            owned = owned.checked_add(embedded)?;
        }
        owned = head
            .local_counts(outer_metadata_bytes, child_count)?
            .checked_add(owned)?;
        Ok(Self { outer_metadata_bytes, owned })
    }

    /// Retained output of unchanged Par::append. Appended roots are not
    /// embedded children; their outer metadata is joined, not added as nested.
    pub(crate) fn append(&self, right: &Self) -> Result<Self, ReceiptError> {
        Ok(Self {
            outer_metadata_bytes: self.outer_metadata_bytes.max(right.outer_metadata_bytes),
            owned: self.owned.checked_add(right.owned)?,
        })
    }

    /// Owned head content copied by the native append helper: twice left plus
    /// right. Outer metadata passes, clone control and temporary/drop work are
    /// separate operations. This is not the retained-output receipt.
    pub(crate) fn append_copy_counts(&self, right: &Self) -> Result<NativeCounts, ReceiptError> {
        self.owned.checked_add(self.owned)?.checked_add(right.owned)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn leaf(head: NativeHead, outer: usize) -> NativeReceipt {
        NativeReceipt::construct(head, outer, []).expect("finite leaf")
    }

    fn axis_counts(axis: usize, value: usize) -> NativeCounts {
        let mut counts = NativeCounts::default();
        match axis {
            0 => counts.heads = value,
            1 => counts.payload_bytes = value,
            2 => counts.name_entries = value,
            3 => counts.metadata_bytes = value,
            4 => counts.descendant_pars = value,
            5 => counts.receive_binds = value,
            6 => counts.map_pairs = value,
            7 => counts.remainder_vars = value,
            _ => panic!("test axis"),
        }
        counts
    }

    #[test]
    fn every_owned_axis_checks_sum_and_copy_overflow() {
        for axis in 0..8 {
            let maximum = axis_counts(axis, usize::MAX);
            let one = axis_counts(axis, 1);
            assert_eq!(maximum.checked_add(one), Err(ReceiptError::Overflow), "axis {axis}");
            assert_eq!(maximum.checked_add(NativeCounts::default()), Ok(maximum));
            let left = NativeReceipt { outer_metadata_bytes: 0, owned: maximum };
            let right = NativeReceipt { outer_metadata_bytes: 0, owned: one };
            assert_eq!(left.append(&right), Err(ReceiptError::Overflow), "axis {axis}");
            assert_eq!(
                left.append_copy_counts(&NativeReceipt::empty()),
                Err(ReceiptError::Overflow)
            );
            let half = NativeReceipt {
                outer_metadata_bytes: 0,
                owned: axis_counts(axis, usize::MAX / 2),
            };
            assert_eq!(half.append_copy_counts(&right), Ok(maximum));
        }
    }

    #[test]
    fn every_child_axis_is_checked_when_embedded_and_accumulated() {
        for axis in 0..8 {
            let child = NativeReceipt {
                outer_metadata_bytes: 0,
                owned: axis_counts(axis, usize::MAX),
            };
            assert_eq!(
                NativeReceipt::construct(NativeHead::Plain, 0, [&child, &child]),
                Err(ReceiptError::Overflow),
                "axis {axis}"
            );
        }
        let metadata = NativeReceipt {
            outer_metadata_bytes: usize::MAX,
            owned: NativeCounts {
                metadata_bytes: 1,
                ..NativeCounts::default()
            },
        };
        assert_eq!(
            NativeReceipt::construct(NativeHead::Plain, 0, [&metadata]),
            Err(ReceiptError::Overflow)
        );
        let deep = NativeReceipt {
            outer_metadata_bytes: 0,
            owned: NativeCounts {
                descendant_pars: usize::MAX,
                ..NativeCounts::default()
            },
        };
        assert_eq!(
            NativeReceipt::construct(NativeHead::Plain, 0, [&deep]),
            Err(ReceiptError::Overflow)
        );
    }

    #[test]
    fn constructor_local_sums_check_overflow() {
        for head in [
            NativeHead::Fresh {
                uri_entries: usize::MAX,
                uri_bytes: 0,
                injection_entries: 1,
                key_bytes: 0,
            },
            NativeHead::Fresh {
                uri_entries: 0,
                uri_bytes: usize::MAX,
                injection_entries: 0,
                key_bytes: 1,
            },
        ] {
            assert_eq!(NativeReceipt::construct(head, 0, []), Err(ReceiptError::Overflow));
        }
        let child = leaf(NativeHead::Plain, 1);
        assert_eq!(
            NativeReceipt::construct(NativeHead::List { remainder: false }, usize::MAX, [&child]),
            Err(ReceiptError::Overflow)
        );
    }

    #[test]
    fn ddl_inner_metadata_is_distinct_from_ordinary_lists_and_outer_append() {
        let child = leaf(NativeHead::Plain, 3);
        let ordinary = NativeReceipt::construct(NativeHead::List { remainder: false }, 3, [&child])
            .expect("ordinary list retains finite child and inner metadata");
        let ddl = NativeReceipt::construct(NativeHead::List { remainder: false }, 0, [&child])
            .expect("DDL list retains finite child metadata only");
        assert_eq!(
            ordinary,
            NativeReceipt {
                outer_metadata_bytes: 3,
                owned: NativeCounts {
                    heads: 2,
                    metadata_bytes: 6,
                    descendant_pars: 1,
                    ..NativeCounts::default()
                },
            }
        );
        assert_eq!(
            ddl,
            NativeReceipt {
                outer_metadata_bytes: 0,
                owned: NativeCounts {
                    heads: 2,
                    metadata_bytes: 3,
                    descendant_pars: 1,
                    ..NativeCounts::default()
                },
            }
        );
        assert_eq!(
            ordinary.append(&ddl).expect("finite mixed list append"),
            NativeReceipt {
                outer_metadata_bytes: 3,
                owned: NativeCounts {
                    heads: 4,
                    metadata_bytes: 9,
                    descendant_pars: 2,
                    ..NativeCounts::default()
                },
            }
        );
        assert_eq!(
            ordinary
                .append_copy_counts(&ddl)
                .expect("finite ordinary-left append copies"),
            NativeCounts {
                heads: 6,
                metadata_bytes: 15,
                descendant_pars: 3,
                ..NativeCounts::default()
            }
        );
        assert_eq!(
            ddl.append_copy_counts(&ordinary)
                .expect("finite DDL-left append copies"),
            NativeCounts {
                heads: 6,
                metadata_bytes: 12,
                descendant_pars: 3,
                ..NativeCounts::default()
            }
        );
    }

    #[test]
    fn repeated_children_and_method_name_bytes_are_not_deduplicated() {
        let child = leaf(NativeHead::Payload { bytes: "λ".len() }, 3);
        assert_eq!(
            NativeReceipt::construct(NativeHead::Method { name_bytes: 3 }, 3, [&child, &child])
                .expect("finite method with repeated child occurrences"),
            NativeReceipt {
                outer_metadata_bytes: 3,
                owned: NativeCounts {
                    heads: 3,
                    payload_bytes: 7,
                    metadata_bytes: 9,
                    descendant_pars: 2,
                    ..NativeCounts::default()
                },
            }
        );
    }

    #[test]
    fn mixed_local_fields_preserve_fresh_receive_send_and_remainders() {
        let child = leaf(NativeHead::Payload { bytes: 2 }, 4);
        let receive = NativeReceipt::construct(
            NativeHead::Receive { binds: 2, remainders: 1 },
            3,
            [&child, &child, &child, &child, &child],
        )
        .expect("finite two-bind receive receipt");
        let fresh = NativeReceipt::construct(
            NativeHead::Fresh {
                uri_entries: 2,
                uri_bytes: 7,
                injection_entries: 3,
                key_bytes: 5,
            },
            1,
            [&receive, &child, &child, &child],
        )
        .expect("finite Fresh receipt with three injection occurrences");
        assert_eq!(
            fresh,
            NativeReceipt {
                outer_metadata_bytes: 1,
                owned: NativeCounts {
                    heads: 10,
                    payload_bytes: 28,
                    name_entries: 5,
                    metadata_bytes: 39,
                    descendant_pars: 9,
                    receive_binds: 2,
                    map_pairs: 0,
                    remainder_vars: 1,
                },
            }
        );
        assert_eq!(
            NativeReceipt::construct(NativeHead::Send, 3, [&child])
                .expect("finite send receipt")
                .owned
                .metadata_bytes,
            7
        );
        assert_eq!(
            leaf(NativeHead::List { remainder: true }, 0)
                .owned
                .remainder_vars,
            1
        );
        assert_eq!(
            leaf(NativeHead::Map { remainder: true }, 0)
                .owned
                .remainder_vars,
            1
        );
    }

    #[test]
    fn map_input_receipts_bound_duplicate_selection_without_claiming_exactness() {
        let key = leaf(NativeHead::Payload { bytes: 1 }, 0);
        let old_value = leaf(NativeHead::Payload { bytes: 9 }, 0);
        let new_value = leaf(NativeHead::Payload { bytes: 2 }, 0);
        let upper = NativeReceipt::construct(
            NativeHead::Map { remainder: false },
            0,
            [&key, &old_value, &key, &new_value],
        )
        .expect("finite map input bound including both duplicate-key occurrences");
        assert_eq!(
            upper.owned,
            NativeCounts {
                heads: 5,
                payload_bytes: 13,
                descendant_pars: 4,
                map_pairs: 2,
                ..NativeCounts::default()
            }
        );
        let retained =
            NativeReceipt::construct(NativeHead::Map { remainder: false }, 0, [&key, &new_value])
                .expect("finite selected map entry receipt");
        assert_eq!(
            retained.owned,
            NativeCounts {
                heads: 3,
                payload_bytes: 3,
                descendant_pars: 2,
                map_pairs: 1,
                ..NativeCounts::default()
            }
        );
        assert!(retained.owned.heads <= upper.owned.heads);
        assert!(retained.owned.payload_bytes <= upper.owned.payload_bytes);
        assert!(retained.owned.descendant_pars <= upper.owned.descendant_pars);
        assert!(retained.owned.map_pairs <= upper.owned.map_pairs);
        assert_eq!(
            NativeReceipt::construct(NativeHead::Map { remainder: false }, 0, [&key]),
            Err(ReceiptError::IncompleteMapPair { children: 1 })
        );
    }

    #[test]
    fn empty_append_and_outer_maximum_do_not_add_metadata() {
        let left = NativeReceipt {
            outer_metadata_bytes: usize::MAX,
            owned: NativeCounts::default(),
        };
        let right = NativeReceipt {
            outer_metadata_bytes: usize::MAX,
            owned: NativeCounts::default(),
        };
        assert_eq!(left.append(&right), Ok(left));
        assert_eq!(left.append_copy_counts(&right), Ok(NativeCounts::default()));
        assert_eq!(left.append(&NativeReceipt::empty()), Ok(left));
        assert_eq!(NativeReceipt::empty().append(&left), Ok(left));
    }
}
