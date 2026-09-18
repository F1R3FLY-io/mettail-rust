//! Admission for the existing FLT projection and map-free request encoder.
//!
//! These adapters inspect borrowed arguments before invoking the original
//! helper. They neither parse guest text nor scan an already-produced request.
//! Records and byte visits are logical charges, not allocator/RSS bounds.

use super::*;

fn overflow() -> RholangAstLowerError {
    RholangAstLowerError::PreparationSizeOverflow
}

fn add(left: usize, right: usize) -> Result<usize, RholangAstLowerError> {
    left.checked_add(right).ok_or_else(overflow)
}

fn mul(left: usize, right: usize) -> Result<usize, RholangAstLowerError> {
    left.checked_mul(right).ok_or_else(overflow)
}

fn reserve(
    policy: SourcePreparation,
    reservation: &mut StorageReservation<'_>,
    work: usize,
    records: usize,
    bytes: usize,
) -> Result<(), RholangAstLowerError> {
    match policy {
        SourcePreparation::Original => Ok(()),
        SourcePreparation::Checked => {
            preparation_scope::reserve_parts(work, records, bytes, reservation)
        },
    }
}

/// Exact old projection after all copies and both output rosters are admitted.
/// Source ranges remain on the borrowed source; the wire projection has never
/// transported them. Repeated hole occurrences are not deduplicated.
pub(super) fn template_parts(
    template: ScopedFltTemplate<'_>,
    policy: SourcePreparation,
    reservation: &mut StorageReservation<'_>,
) -> Result<(Vec<RuntimeTemplatePiece>, Vec<NamedRuntimeTemplateHole>), RholangAstLowerError> {
    if policy == SourcePreparation::Original {
        return Ok(runtime_template_parts(template));
    }
    reserve(policy, reservation, 4, 2, 0)?;
    let records = add(template.pieces.len(), template.telescope.len())?;
    reserve(policy, reservation, records, records, 0)?;
    let mut pieces = template.pieces.iter();
    loop {
        reserve(policy, reservation, 3, 0, 0)?;
        let Some(piece) = pieces.next() else { break };
        if let mettail_runtime::FltTemplatePiece::Text { text, .. } = piece {
            reserve(policy, reservation, 1, 1, text.len())?;
        }
    }
    let mut holes = template.telescope.iter();
    loop {
        reserve(policy, reservation, 3, 0, 0)?;
        let Some(hole) = holes.next() else { break };
        reserve(policy, reservation, 1, 1, hole.name.len())?;
        if let Some(category) = &hole.category {
            reserve(policy, reservation, 1, 1, category.len())?;
        }
    }
    // The final cancellation boundary precedes both original map/collects.
    reserve(policy, reservation, 1, 0, 0)?;
    Ok(runtime_template_parts(template))
}

/// Admit one original wire_list. All child metadata lengths are bounded by
/// `metadata`; union preserves that bound (including noncanonical clear bytes).
/// Each child pays its clone, the union allocation/byte loop, both iterator
/// passes, and cleanup. The final metadata clone and with_exprs' clone of the
/// outer Par metadata are admitted separately.
fn list(
    width: usize,
    metadata: usize,
    policy: SourcePreparation,
    reservation: &mut StorageReservation<'_>,
) -> Result<(), RholangAstLowerError> {
    let work = add(add(8, mul(2, metadata)?)?, mul(width, add(5, mul(6, metadata)?)?)?)?;
    let records = add(7, mul(width, 3)?)?;
    let bytes = mul(add(mul(width, 2)?, 2)?, metadata)?;
    reserve(policy, reservation, work, records, bytes)
}

fn text(
    bytes: usize,
    policy: SourcePreparation,
    reservation: &mut StorageReservation<'_>,
) -> Result<(), RholangAstLowerError> {
    reserve(policy, reservation, 3, 3, bytes)
}

/// The unchanged encoders clone the same literal/name/category strings once
/// more into shallow target leaves. Every inner list here is closed.
fn template_wire(
    pieces: &[RuntimeTemplatePiece],
    holes: &[NamedRuntimeTemplateHole],
    policy: SourcePreparation,
    reservation: &mut StorageReservation<'_>,
) -> Result<(), RholangAstLowerError> {
    reserve(policy, reservation, 4, 2, 0)?;
    let mut pieces_iter = pieces.iter();
    loop {
        reserve(policy, reservation, 3, 0, 0)?;
        let Some(piece) = pieces_iter.next() else {
            break;
        };
        text(4, policy, reservation)?; // exact "text" or "hole" tag
        match piece {
            RuntimeTemplatePiece::Text(value) => text(value.len(), policy, reservation)?,
            RuntimeTemplatePiece::Hole(_) => reserve(policy, reservation, 3, 3, 0)?,
        }
        list(2, 0, policy, reservation)?;
    }
    list(pieces.len(), 0, policy, reservation)?;
    let mut holes_iter = holes.iter();
    loop {
        reserve(policy, reservation, 3, 0, 0)?;
        let Some(hole) = holes_iter.next() else { break };
        reserve(policy, reservation, 3, 3, 0)?; // u32 -> i64 and integer leaf
        text(hole.name.len(), policy, reservation)?;
        match &hole.category {
            Some(category) => text(category.len(), policy, reservation)?,
            None => reserve(policy, reservation, 1, 1, 0)?,
        }
        list(3, 0, policy, reservation)?;
    }
    list(holes.len(), 0, policy, reservation)
}

/// Retain the existing pattern encoder, including all literal bytes and child
/// metadata. Handle and reply are moved, not cloned or recursively inspected.
/// Their production, template validation and lexical lookup remain caller
/// obligations; this function admits precisely the map-free wire operation.
pub(super) fn pattern_request(
    handle: Par,
    pieces: &[RuntimeTemplatePiece],
    holes: &[NamedRuntimeTemplateHole],
    category: &str,
    reply: Par,
    policy: SourcePreparation,
    reservation: &mut StorageReservation<'_>,
) -> Result<Par, RholangAstLowerError> {
    if policy == SourcePreparation::Checked {
        template_wire(pieces, holes, policy, reservation)?;
        text(crate::language_install::LANGUAGE_FLT_PATTERN_ABI_V1.len(), policy, reservation)?;
        text(category.len(), policy, reservation)?;
        reserve(policy, reservation, 3, 0, 0)?;
        list(6, handle.locally_free.len().max(reply.locally_free.len()), policy, reservation)?;
        reserve(policy, reservation, 1, 0, 0)?;
    }
    Ok(crate::language_install::encode_flt_pattern_call(
        handle, pieces, holes, category, reply,
    ))
}

#[cfg(test)]
#[path = "preparation_flt_tests.rs"]
mod tests;
