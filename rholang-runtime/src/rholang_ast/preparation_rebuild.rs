//! Paid collection adapters for the existing body-replacement worklist.
//!
//! The worklist supplies actual ordered owned outputs, not an assumed pure
//! transformation. Its independent root cleanup is already paid. Native
//! insertion order and collision behavior remain the original collection's.

use super::*;
use mettail_runtime::{HashBag, HashBagRebuildMode, HashMapLit};

pub(super) fn parallel(
    source: &HashBag<Proc>,
    children: Vec<Proc>,
    policy: SourcePreparation,
    reserve: &mut StorageReservation<'_>,
) -> Result<HashBag<Proc>, RholangAstLowerError> {
    if policy == SourcePreparation::Original {
        return Ok(children.into_iter().collect());
    }
    preparation_scope::reserve_parts(1, 0, 0, reserve)?;
    let width = children.len();
    std::alloc::Layout::array::<(Proc, usize)>(width)
        .map_err(|_| RholangAstLowerError::PreparationSizeOverflow)?;
    let work = width
        .checked_mul(3)
        .and_then(|n| n.checked_add(3))
        .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
    let records = width
        .checked_add(1)
        .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
    preparation_scope::reserve_parts(work, records, 0, reserve)?;
    let mut entries = Vec::with_capacity(width);
    // Each transformed occurrence corresponds to one original iter_elements
    // occurrence. Clone mode SUMS colliding count-one entries; binding mode
    // would incorrectly replace counts and transport the source total.
    for child in children {
        entries.push((child, 1));
    }
    Proc::try_rebuild_hashbag_entries(
        source,
        entries,
        HashBagRebuildMode::CloneEntries,
        &mut |work, units| reserve(work, units),
    )
    .map_err(preparation_scope::binding_failure)
}

pub(super) fn map(
    source: &HashMapLit<Proc, Proc>,
    entries: Vec<(Proc, Proc)>,
    policy: SourcePreparation,
    reserve: &mut StorageReservation<'_>,
) -> Result<HashMapLit<Proc, Proc>, RholangAstLowerError> {
    if policy == SourcePreparation::Original {
        let mut result = HashMapLit::new();
        for (key, value) in entries {
            result.insert(key, value);
        }
        return Ok(result);
    }
    Proc::try_rebuild_map_entries(source, entries, &mut |work, units| reserve(work, units))
        .map_err(preparation_scope::binding_failure)
}
