//! Paid derivation around the existing lexical-environment helpers.
//!
//! Inspect borrowed key lengths only after reserving their occurrence count.
//! Reserve the complete copy/shift/retention charge before constructing either
//! map. Iteration order cannot change the aggregate charge; duplicate input
//! slots still pay for the copies performed by the existing insertion loop.
//! Units describe logical entries and owned bytes, not physical hash capacity,
//! collision counts, native memory, or a CPU-time bound.

use super::*;

/// Borrow the inputs until admission; never prepare a copied context first.
pub(super) enum EnvironmentDerivation<'a> {
    Binders(&'a [Binder<String>]),
    SourceBinders(&'a [Binder<String>]),
    Slots(&'a [ReceiveSlot]),
    Pattern,
    Empty,
}

/// One retained environment record, every copied occurrence, every shifted old
/// entry, and every owned key byte. All arithmetic precedes the atomic debit.
fn environment_copy_cost(
    occurrences: usize,
    shifted: usize,
    key_bytes: usize,
) -> Result<(usize, usize), RholangAstLowerError> {
    let records = occurrences
        .checked_add(1)
        .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
    let work = records
        .checked_add(shifted)
        .and_then(|work| work.checked_add(key_bytes))
        .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
    let units = records
        .checked_mul(4)
        .and_then(|units| units.checked_add(key_bytes))
        .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
    Ok((work, units))
}

fn add_key_bytes(total: &mut usize, bytes: usize) -> Result<(), RholangAstLowerError> {
    *total = total
        .checked_add(bytes)
        .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;
    Ok(())
}

fn variable_name_bytes(var: &FreeVar<String>) -> usize {
    // An unnamed identity is valid here. pretty_var_name() would reject it.
    var.pretty_name.as_ref().map_or(0, String::len)
}

impl EnvArena<'_> {
    pub(super) fn derive(
        &mut self,
        parent: EnvId,
        derivation: EnvironmentDerivation<'_>,
        reserve: &mut StorageReservation<'_>,
    ) -> Result<EnvId, RholangAstLowerError> {
        // Constant-size validity check before any copied environment exists.
        scope::next_environment_index(self.derived.len())?;
        let source = self.get(parent);
        let old = match derivation {
            EnvironmentDerivation::Empty => 0,
            _ => source
                .binders
                .len()
                .checked_add(source.hole_binders.len())
                .and_then(|count| count.checked_add(source.construction_holes.len()))
                .ok_or(RholangAstLowerError::PreparationSizeOverflow)?,
        };
        let (added, shifted) = match derivation {
            EnvironmentDerivation::Binders(binders) => (binders.len(), old),
            EnvironmentDerivation::SourceBinders(binders) => (
                binders
                    .len()
                    .checked_mul(2)
                    .ok_or(RholangAstLowerError::PreparationSizeOverflow)?,
                old,
            ),
            EnvironmentDerivation::Slots(slots) => (
                slots
                    .len()
                    .checked_mul(2)
                    .ok_or(RholangAstLowerError::PreparationSizeOverflow)?,
                old,
            ),
            EnvironmentDerivation::Pattern | EnvironmentDerivation::Empty => (0, 0),
        };
        let occurrences = old
            .checked_add(added)
            .ok_or(RholangAstLowerError::PreparationSizeOverflow)?;

        // Phase one pays the full inspection before touching the iterators.
        // Per-key polls do not debit payload, so HashMap iteration order cannot
        // expose an order-dependent partially paid key prefix.
        reserve(occurrences, 0)?;
        let mut key_bytes = 0;
        if !matches!(derivation, EnvironmentDerivation::Empty) {
            for var in source.binders.keys() {
                reserve(0, 0)?;
                add_key_bytes(&mut key_bytes, variable_name_bytes(var))?;
            }
            for name in source.hole_binders.keys() {
                reserve(0, 0)?;
                add_key_bytes(&mut key_bytes, name.len())?;
            }
            for name in source.construction_holes.keys() {
                reserve(0, 0)?;
                add_key_bytes(&mut key_bytes, name.len())?;
            }
        }
        match derivation {
            EnvironmentDerivation::Binders(binders) => {
                for binder in binders {
                    reserve(0, 0)?;
                    add_key_bytes(&mut key_bytes, variable_name_bytes(&binder.0))?;
                }
            },
            EnvironmentDerivation::SourceBinders(binders) => {
                for binder in binders {
                    reserve(0, 0)?;
                    let bytes = variable_name_bytes(&binder.0);
                    add_key_bytes(&mut key_bytes, bytes)?;
                    add_key_bytes(&mut key_bytes, bytes)?;
                }
            },
            EnvironmentDerivation::Slots(slots) => {
                for slot in slots {
                    reserve(0, 0)?;
                    let bytes = match slot {
                        ReceiveSlot::Moniker(binder) => variable_name_bytes(&binder.0),
                        ReceiveSlot::Hole(name) => name.len(),
                    };
                    add_key_bytes(&mut key_bytes, bytes)?;
                    add_key_bytes(&mut key_bytes, bytes)?;
                }
            },
            EnvironmentDerivation::Pattern | EnvironmentDerivation::Empty => {},
        }
        reserve(0, 0)?;

        // Phase two includes the single EnvArena record/append. No helper or
        // key clone has run yet; a refusal leaves the arena and input intact.
        let (work, units) = environment_copy_cost(occurrences, shifted, key_bytes)?;
        reserve(work, units)?;
        let derived = match derivation {
            EnvironmentDerivation::Binders(binders) => extend_env(source, binders)?,
            EnvironmentDerivation::SourceBinders(binders) => {
                source.extend_source_binders(binders)?
            },
            EnvironmentDerivation::Slots(slots) => source.extend_slots(slots)?,
            EnvironmentDerivation::Pattern => source.in_pattern_position(),
            EnvironmentDerivation::Empty => match source.admission {
                SourceAdmissionMode::Harness => BoundEnv::new(),
                SourceAdmissionMode::Public => source.without_lexical_bindings(),
            },
        };
        self.push(derived)
    }
}

#[cfg(test)]
mod tests;
