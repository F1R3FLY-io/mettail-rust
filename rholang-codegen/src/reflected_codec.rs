//! Bounded views and scalar codecs for the existing reflected FLT ABI.
//!
//! These helpers share the admission recognizers and reflection writers. The
//! closed adapter adds canonical nominal enrollment; it does not tighten the
//! more general existing admission policy or parse another source language.

use crate::dynamic_admission::{
    decode_boolean_label, decode_hex_into, decode_integer_label, decode_private_tag,
    positional_children, positional_parts, private_tag_bytes, text_label_payload,
};
use crate::dynamic_reflection::{
    write_dynamic_native_label, DynamicNativeRef, DynamicReflectionError, BOOLEAN_LABEL,
    INTEGER_LABEL, TEXT_LABEL,
};
use crate::{ground_marker_tag_par, parse_reflected_tag, REFLECTED_TERM_ABI_PREFIX};
use mettail_grammar_core::DynamicValue;
use models::rhoapi::Par;
use prost::Message;

/// A scoped borrow of cumulative caller work and a decreasing payload allowance.
///
/// Payload bytes reserve materialized scalar buffers and fixed-width logical
/// index slots, not allocator capacity, hash-table overhead or RSS. Successful
/// reservations are never refunded by a later malformed input or allocation
/// failure. All results of one operation
/// must share the allowance. Use [`Self::finish`] to carry unused bytes across a
/// kernel call that needs to borrow the same work counter and cancellation hook.
pub struct ReflectedCodecBudget<'a, C> {
    work: &'a mut u64,
    work_limit: u64,
    remaining_bytes: usize,
    is_cancelled: &'a mut C,
}

impl<'a, C: FnMut() -> bool> ReflectedCodecBudget<'a, C> {
    pub fn new(
        work: &'a mut u64,
        work_limit: u64,
        remaining_bytes: usize,
        is_cancelled: &'a mut C,
    ) -> Self {
        Self {
            work,
            work_limit,
            remaining_bytes,
            is_cancelled,
        }
    }

    /// Check both dimensions before changing either balance. Even a zero-unit
    /// reservation rejects an already overdrawn incoming work counter.
    pub fn charge(&mut self, units: usize, bytes: usize) -> Result<(), DynamicReflectionError> {
        if (self.is_cancelled)() {
            return Err(DynamicReflectionError::Cancelled);
        }
        let units = u64::try_from(units).map_err(|_| DynamicReflectionError::WorkLimit)?;
        let total = self
            .work
            .checked_add(units)
            .filter(|total| *total <= self.work_limit)
            .ok_or(DynamicReflectionError::WorkLimit)?;
        let remaining = self
            .remaining_bytes
            .checked_sub(bytes)
            .ok_or(DynamicReflectionError::PayloadByteLimit)?;
        *self.work = total;
        self.remaining_bytes = remaining;
        Ok(())
    }

    pub fn work_used(&self) -> u64 {
        *self.work
    }

    pub fn remaining_bytes(&self) -> usize {
        self.remaining_bytes
    }

    /// Run a trusted, separately accounted stage with the remaining work
    /// ceiling and absorb its reported usage on every result, including errors.
    /// The callback's counter starts at zero. Its byte-size limits are separate
    /// from this converter's payload allowance, which is carried unchanged.
    /// A report beyond the supplied work ceiling is refused, never saturated.
    pub fn run_accounted_stage<T>(
        &mut self,
        run: impl FnOnce(u64, &mut C) -> (T, u64),
    ) -> Result<T, DynamicReflectionError> {
        self.charge(0, 0)?;
        let remaining = self.work_limit - *self.work;
        let (result, used) = run(remaining, self.is_cancelled);
        let total = self
            .work
            .checked_add(used)
            .filter(|total| *total <= self.work_limit)
            .ok_or(DynamicReflectionError::WorkLimit)?;
        *self.work = total;
        Ok(result)
    }

    /// Release the work/cancellation borrows without replenishing the byte
    /// allowance. Pass this remainder, not the original ceiling, to the next
    /// stage of the same operation.
    pub fn finish(self) -> usize {
        self.remaining_bytes
    }
}

/// Canonical closed-constructor marker bound to the exact reflected owner.
/// Neither this context nor a reflected owner string grants language authority.
pub struct ReflectedPositionalContext<'a> {
    fingerprint: &'a str,
    ground_marker: Par,
}

impl<'a> ReflectedPositionalContext<'a> {
    pub fn new<C: FnMut() -> bool>(
        fingerprint: &'a str,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<Self, DynamicReflectionError> {
        budget.charge(fingerprint.len(), 0)?;
        if fingerprint.is_empty() || fingerprint.contains('.') {
            return Err(DynamicReflectionError::InvalidFingerprint);
        }
        // The existing writer emits a nonempty protobuf String: key byte,
        // length delimiter, then the tag bytes. Count before materializing it.
        let tag_len = REFLECTED_TERM_ABI_PREFIX
            .len()
            .checked_add(fingerprint.len())
            .and_then(|len| len.checked_add(1 + "^gnd".len()))
            .ok_or(DynamicReflectionError::PayloadByteLimit)?;
        let wire_len = tag_len
            .checked_add(prost::length_delimiter_len(tag_len))
            .and_then(|len| len.checked_add(1))
            .ok_or(DynamicReflectionError::PayloadByteLimit)?;
        let materialized = tag_len
            .checked_add(wire_len)
            .ok_or(DynamicReflectionError::PayloadByteLimit)?;
        budget.charge(materialized, materialized)?;
        Ok(Self {
            fingerprint,
            ground_marker: ground_marker_tag_par(fingerprint, true),
        })
    }

    /// Assemble one node with the existing reflection body, moving the actual
    /// already-reflected children in order. This is not a typing or admission
    /// certificate: the caller supplies checked child sorts and ground bits.
    ///
    /// The flat planning pass reserves scalar tag buffers, metadata copies and
    /// four-byte logical occurrence slots before assembly. It never measures a
    /// recursive Par encoding or clones a child subtree. The input tuple vector
    /// is charged where the traversal creates it, not again here. On refusal,
    /// owned children use the existing stack-safe Par destructor.
    pub fn assemble<C: FnMut() -> bool>(
        &self,
        label: &str,
        children: Vec<(Par, bool)>,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<(Par, bool), DynamicReflectionError> {
        let planning_work = children
            .len()
            .checked_add(label.len())
            .and_then(|units| units.checked_add(1))
            .ok_or(DynamicReflectionError::WorkLimit)?;
        budget.charge(planning_work, 0)?;
        let marked = crate::is_marked_object_label(label);
        let mut scalar_bytes = reflected_tag_payload_bytes(self.fingerprint.len(), label.len())?;
        if marked {
            // The shared body writes ^gnd or ^nog, which have equal widths.
            // It must not substitute the context's cached true marker for false.
            scalar_bytes = scalar_bytes
                .checked_add(reflected_tag_payload_bytes(self.fingerprint.len(), "^gnd".len())?)
                .ok_or(DynamicReflectionError::PayloadByteLimit)?;
        }
        let mut metadata_bytes = 0usize;
        let mut prefix_max = 0usize;
        for (child, _) in &children {
            let length = child.locally_free.len();
            prefix_max = prefix_max.max(length);
            // clone the child's bitset, then allocate the padded union result
            metadata_bytes = metadata_bytes
                .checked_add(length)
                .and_then(|bytes| bytes.checked_add(prefix_max))
                .ok_or(DynamicReflectionError::PayloadByteLimit)?;
        }
        metadata_bytes = prefix_max
            .checked_mul(2)
            .and_then(|copies| metadata_bytes.checked_add(copies))
            .ok_or(DynamicReflectionError::PayloadByteLimit)?;
        let element_slots = children
            .len()
            .checked_add(2)
            .ok_or(DynamicReflectionError::PayloadByteLimit)?;
        // Element-buffer slots, tag/marker unforgeables, outer expression.
        let slot_bytes = element_slots
            .checked_add(2 + usize::from(marked))
            .and_then(|slots| slots.checked_mul(4))
            .ok_or(DynamicReflectionError::PayloadByteLimit)?;
        let bytes = scalar_bytes
            .checked_add(metadata_bytes)
            .and_then(|bytes| bytes.checked_add(slot_bytes))
            .ok_or(DynamicReflectionError::PayloadByteLimit)?;
        budget.charge(bytes, bytes)?;
        let mut elements = Vec::new();
        elements
            .try_reserve_exact(element_slots)
            .map_err(|_| DynamicReflectionError::AllocationFailed)?;
        Ok(crate::rho_net_lower::assemble_positional_node(
            label,
            children,
            self.fingerprint,
            elements,
        ))
    }

    /// Observe a single closed positional head, retaining the original child
    /// slice. `None` means no strict view was established, not category membership
    /// or a complete semantic rejection. Child sorts are checked by the adapter.
    ///
    /// Every decoded private tag must equal its canonical reencoding. Otherwise
    /// distinct nominal IDs (for example unknown protobuf fields) would silently
    /// coalesce. Marked constructors must carry the exact true ground marker.
    pub fn view<'p, C: FnMut() -> bool>(
        &self,
        par: &'p Par,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<Option<ReflectedPositionalHead<'p>>, DynamicReflectionError> {
        budget.charge(1, 0)?;
        let Some((head, raw_children)) = positional_parts(par) else {
            return Ok(None);
        };
        let Some(bytes) = private_tag_bytes(head) else {
            return Ok(None);
        };
        // Decode only after reserving the flat encoded input. Never ask for
        // recursive Par::encoded_len or clone a complete reflected subtree.
        budget.charge(bytes.len(), bytes.len())?;
        let Some(tag) = decode_private_tag(bytes) else {
            return Ok(None);
        };
        let canonical_len = tag.encoded_len();
        budget.charge(canonical_len, canonical_len)?;
        let mut canonical = Vec::new();
        canonical
            .try_reserve_exact(canonical_len)
            .map_err(|_| DynamicReflectionError::AllocationFailed)?;
        tag.encode(&mut canonical)
            .expect("reserved exact scalar protobuf capacity");
        if canonical != bytes {
            return Ok(None);
        }
        budget.charge(tag.len(), 0)?;
        let Some((owner, label)) = parse_reflected_tag(&tag) else {
            return Ok(None);
        };
        if owner != self.fingerprint {
            return Ok(None);
        }
        if crate::is_marked_object_label(label) {
            let Some(marker) = raw_children.first() else {
                return Ok(None);
            };
            let Some(marker_bytes) = private_tag_bytes(marker) else {
                return Ok(None);
            };
            budget.charge(marker_bytes.len(), 0)?;
        }
        let Some(children) =
            positional_children(label, raw_children, |marker| marker == &self.ground_marker)
        else {
            return Ok(None);
        };
        budget.charge(children.len(), 0)?;
        let label_start = tag.len() - label.len();
        Ok(Some(ReflectedPositionalHead { tag, label_start, children }))
    }
}

/// Materialized tag String plus its existing protobuf String byte buffer.
/// Valid context fingerprints make the full tag nonempty, so the key byte is
/// always present. Capacity-growth and allocator headers are not payload bytes.
fn reflected_tag_payload_bytes(
    fingerprint_len: usize,
    label_len: usize,
) -> Result<usize, DynamicReflectionError> {
    let tag_len = REFLECTED_TERM_ABI_PREFIX
        .len()
        .checked_add(fingerprint_len)
        .and_then(|len| len.checked_add(1))
        .and_then(|len| len.checked_add(label_len))
        .ok_or(DynamicReflectionError::PayloadByteLimit)?;
    let wire_len = tag_len
        .checked_add(prost::length_delimiter_len(tag_len))
        .and_then(|len| len.checked_add(1))
        .ok_or(DynamicReflectionError::PayloadByteLimit)?;
    tag_len
        .checked_add(wire_len)
        .ok_or(DynamicReflectionError::PayloadByteLimit)
}

/// One owned decoded tag plus borrowed ordered child occurrences. The label is
/// a slice of the tag, so observation does not allocate another label String.
pub struct ReflectedPositionalHead<'a> {
    tag: String,
    label_start: usize,
    children: &'a [Par],
}

impl<'a> ReflectedPositionalHead<'a> {
    pub fn label(&self) -> &str {
        &self.tag[self.label_start..]
    }

    pub fn children(&self) -> &'a [Par] {
        self.children
    }
}

/// Decode the existing native label ABI, not guest-language source. A returned
/// value has exactly one of the Text, Integer or Boolean variants. The enclosing
/// head must still be nullary and owned by the expected installed language.
pub fn decode_dynamic_native_label<C: FnMut() -> bool>(
    label: &str,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<Option<DynamicValue>, DynamicReflectionError> {
    budget.charge(label.len(), 0)?;
    if let Some(hex) = text_label_payload(label) {
        let length = hex.len() / 2;
        budget.charge(length, length)?;
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(length)
            .map_err(|_| DynamicReflectionError::AllocationFailed)?;
        decode_hex_into(hex, &mut bytes);
        return Ok(String::from_utf8(bytes).ok().map(DynamicValue::Text));
    }
    if label.starts_with(INTEGER_LABEL) {
        // The existing canonicality check formats one i128; reserve its maximum
        // signed decimal length before that formatting allocation.
        budget.charge(40, 40)?;
        return Ok(decode_integer_label(label).map(DynamicValue::Integer));
    }
    Ok(decode_boolean_label(label).map(DynamicValue::Boolean))
}

/// Write the existing native reflection label with a pre-reserved scalar buffer.
/// Integer reservation is conservatively 40 decimal bytes; String and Boolean
/// lengths are exact. Reservations describe payload work, not allocator RSS.
pub fn encode_dynamic_native_label<C: FnMut() -> bool>(
    value: DynamicNativeRef<'_>,
    budget: &mut ReflectedCodecBudget<'_, C>,
) -> Result<String, DynamicReflectionError> {
    let length = match value {
        DynamicNativeRef::Text(text) => text
            .len()
            .checked_mul(2)
            .and_then(|len| len.checked_add(TEXT_LABEL.len())),
        DynamicNativeRef::Integer(_) => INTEGER_LABEL.len().checked_add(40),
        DynamicNativeRef::Boolean(value) => {
            BOOLEAN_LABEL.len().checked_add(if value { 4 } else { 5 })
        },
    }
    .ok_or(DynamicReflectionError::PayloadByteLimit)?;
    budget.charge(length, length)?;
    let mut label = String::new();
    label
        .try_reserve_exact(length)
        .map_err(|_| DynamicReflectionError::AllocationFailed)?;
    write_dynamic_native_label(&mut label, value);
    Ok(label)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{dynamic_syntax_to_ground_term, reflect_ground_term_par, GroundTerm};
    use mettail_grammar_core::GrammarCoreV1;
    use std::collections::BTreeMap;

    const FP: &str = "checked-reflected-test";

    fn assembly_children() -> Vec<(Par, bool)> {
        [("One", vec![1], true), ("Two", vec![0, 2, 0], false), ("One", vec![4, 0], true)]
            .into_iter()
            .map(|(label, free, ground)| {
                let mut par = reflect_ground_term_par(&GroundTerm::nullary(label), FP);
                par.locally_free = free;
                (par, ground)
            })
            .collect()
    }

    #[test]
    fn reflected_codec_assembly_preserves_markers_order_and_exact_metadata() {
        use models::rhoapi::expr::ExprInstance::EListBody;

        let mut work = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1_000_000, 1_000_000, &mut cancelled);
        let context = ReflectedPositionalContext::new(FP, &mut budget).expect("context");
        for (label, ground) in [("Node.A", false), ("^bound", false), ("^free", true)] {
            let children = assembly_children();
            let expected_children = children
                .iter()
                .map(|(par, _)| par.clone())
                .collect::<Vec<_>>();
            let term = GroundTerm::new(
                label,
                vec![
                    GroundTerm::nullary("One"),
                    GroundTerm::nullary("Two"),
                    GroundTerm::nullary("One"),
                ],
            );
            let expected =
                crate::rho_net_lower::assemble_positional_ground_node(&term, children.clone(), FP);
            let (par, actual_ground) = context
                .assemble(label, children, &mut budget)
                .expect("assembly");
            assert_eq!((&par, actual_ground), (&expected.0, expected.1));
            assert_eq!(actual_ground, ground, "label-specific ground policy");
            let Some(EListBody(list)) = &par.exprs[0].expr_instance else {
                panic!("positional list envelope");
            };
            assert_eq!(list.ps.len(), 5);
            assert_eq!(list.ps[1], ground_marker_tag_par(FP, ground));
            assert_eq!(&list.ps[2..], expected_children.as_slice());
            // Par::eq omits these bytes; test them independently, including padding.
            assert_eq!(par.locally_free, [5, 2, 0]);
            assert_eq!(list.locally_free, [5, 2, 0]);
            for (actual, expected) in list.ps[2..].iter().zip(&expected_children) {
                assert_eq!(actual.locally_free, expected.locally_free);
            }
            assert_eq!(par.locally_free, expected.0.locally_free);
            assert!(!par.connective_used);
            assert!(!list.connective_used);
            assert!(list.remainder.is_none());
        }
        for label in ["Leaf", "^dynamic-integer:7"] {
            let expected = reflect_ground_term_par(&GroundTerm::nullary(label), FP);
            let (actual, ground) = context.assemble(label, vec![], &mut budget).expect("leaf");
            assert_eq!(actual, expected);
            assert!(ground);
            let Some(EListBody(list)) = &actual.exprs[0].expr_instance else {
                panic!("list");
            };
            assert_eq!(list.ps.len(), if label == "Leaf" { 2 } else { 1 });
            assert!(actual.locally_free.is_empty());
            assert!(list.locally_free.is_empty());
        }
    }

    #[test]
    fn reflected_codec_assembly_reserves_complete_payload_before_materialization() {
        let mut setup_work = 0;
        let mut cancelled = || false;
        let mut setup =
            ReflectedCodecBudget::new(&mut setup_work, 100_000, 100_000, &mut cancelled);
        let context = ReflectedPositionalContext::new(FP, &mut setup).expect("context");
        setup.finish();
        let tag = crate::rho_net_lower::reflect_tag(FP, "Node");
        let marker = crate::rho_net_lower::reflect_tag(FP, "^gnd");
        let scalars = tag.len() + tag.encoded_len() + marker.len() + marker.encoded_len();
        // Child lengths 1,3,2; prefix maxima 1,3,3; two final 3-byte copies.
        let metadata = (1 + 3 + 2) + (1 + 3 + 3) + 2 * 3;
        let slots = 4 * ((3 + 2) + 2 + 1);
        let exact = scalars + metadata + slots;
        let planning = 1 + "Node".len() + 3;
        for allowance in [exact - 1, exact] {
            let mut work = 7;
            let mut budget =
                ReflectedCodecBudget::new(&mut work, 100_000, allowance, &mut cancelled);
            let result = context.assemble("Node", assembly_children(), &mut budget);
            if allowance == exact {
                assert!(result.is_ok());
                assert_eq!(budget.remaining_bytes(), 0);
                assert_eq!(budget.work_used(), (7 + planning + exact) as u64);
            } else {
                assert!(matches!(result, Err(DynamicReflectionError::PayloadByteLimit)));
                assert_eq!(budget.remaining_bytes(), allowance);
                assert_eq!(budget.work_used(), (7 + planning) as u64);
            }
        }
        for cancel_at in [1, 2] {
            let mut calls = 0;
            let mut cancelled = || {
                calls += 1;
                calls == cancel_at
            };
            let mut work = 7;
            let mut budget = ReflectedCodecBudget::new(&mut work, 100_000, exact, &mut cancelled);
            assert!(matches!(
                context.assemble("Node", assembly_children(), &mut budget),
                Err(DynamicReflectionError::Cancelled)
            ));
            assert_eq!(budget.remaining_bytes(), exact);
            assert_eq!(
                budget.work_used(),
                if cancel_at == 1 {
                    7
                } else {
                    (7 + planning) as u64
                }
            );
        }
        assert_eq!(
            reflected_tag_payload_bytes(usize::MAX, 0),
            Err(DynamicReflectionError::PayloadByteLimit)
        );
        assert_eq!(
            reflected_tag_payload_bytes(0, usize::MAX),
            Err(DynamicReflectionError::PayloadByteLimit)
        );
    }

    #[test]
    fn reflected_codec_assembly_error_drops_deep_owned_children_on_small_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut term = GroundTerm::nullary("Leaf");
                for _ in 0..20_000 {
                    term = GroundTerm::new("Node", vec![term]);
                }
                let par = reflect_ground_term_par(&term, FP);
                let mut work = 0;
                let mut cancelled = || false;
                let mut setup =
                    ReflectedCodecBudget::new(&mut work, 100_000, 100_000, &mut cancelled);
                let context = ReflectedPositionalContext::new(FP, &mut setup).expect("context");
                setup.finish();
                let mut exhausted =
                    ReflectedCodecBudget::new(&mut work, 100_000, 0, &mut cancelled);
                assert!(matches!(
                    context.assemble("Node", vec![(par, true)], &mut exhausted),
                    Err(DynamicReflectionError::PayloadByteLimit)
                ));
            })
            .expect("small-stack worker")
            .join()
            .expect("stack-safe assembly refusal");
    }

    #[test]
    fn reflected_codec_accounted_stage_preserves_error_usage_and_payload_allowance() {
        for result in [Ok(7), Err("rejected")] {
            let mut work = 3;
            let mut cancelled = || false;
            let mut budget = ReflectedCodecBudget::new(&mut work, 10, 17, &mut cancelled);
            let observed = budget
                .run_accounted_stage(|remaining, cancel| {
                    assert_eq!(remaining, 7);
                    assert!(!cancel());
                    (result, 5)
                })
                .expect("bounded stage report");
            assert_eq!(observed, result);
            assert_eq!((budget.work_used(), budget.remaining_bytes()), (8, 17));
            assert_eq!(
                budget.run_accounted_stage(|remaining, _| {
                    assert_eq!(remaining, 2);
                    ((), 2)
                }),
                Ok(())
            );
            assert_eq!((budget.work_used(), budget.remaining_bytes()), (10, 17));
        }
    }

    #[test]
    fn reflected_codec_accounted_stage_rejects_bad_reports_and_preflight_failure() {
        for (prefix, ceiling, reported) in [(3, 10, 8), (u64::MAX - 1, u64::MAX, 2)] {
            let mut work = prefix;
            let mut cancelled = || false;
            let mut budget = ReflectedCodecBudget::new(&mut work, ceiling, 17, &mut cancelled);
            assert_eq!(
                budget.run_accounted_stage(|_, _| ((), reported)),
                Err(DynamicReflectionError::WorkLimit)
            );
            assert_eq!((budget.work_used(), budget.remaining_bytes()), (prefix, 17));
        }
        for (prefix, ceiling, cancel, expected) in [
            (11, 10, false, DynamicReflectionError::WorkLimit),
            (3, 10, true, DynamicReflectionError::Cancelled),
        ] {
            let mut work = prefix;
            let mut cancelled = || cancel;
            let mut budget = ReflectedCodecBudget::new(&mut work, ceiling, 17, &mut cancelled);
            let result: Result<(), _> = budget
                .run_accounted_stage(|_, _| panic!("failed preflight must not run the stage"));
            assert_eq!(result, Err(expected));
            assert_eq!((budget.work_used(), budget.remaining_bytes()), (prefix, 17));
        }
        let mut calls = 0;
        let mut cancelled = || {
            calls += 1;
            calls == 2
        };
        let mut work = 3;
        let mut budget = ReflectedCodecBudget::new(&mut work, 10, 17, &mut cancelled);
        assert_eq!(
            budget.run_accounted_stage(|_, cancel| {
                assert!(cancel());
                (Err::<(), _>(DynamicReflectionError::Cancelled), 2)
            }),
            Ok(Err(DynamicReflectionError::Cancelled))
        );
        assert_eq!((budget.work_used(), budget.remaining_bytes()), (5, 17));
    }

    #[test]
    fn reflected_codec_reservations_are_atomic_and_preserve_the_prefix() {
        let mut work = 3;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 8, 5, &mut cancelled);
        budget.charge(2, 3).expect("first reservation");
        assert_eq!((budget.work_used(), budget.remaining_bytes()), (5, 2));
        assert_eq!(budget.charge(1, 3), Err(DynamicReflectionError::PayloadByteLimit));
        assert_eq!((budget.work_used(), budget.remaining_bytes()), (5, 2));
        assert_eq!(budget.charge(4, 0), Err(DynamicReflectionError::WorkLimit));
        assert_eq!((budget.work_used(), budget.remaining_bytes()), (5, 2));
        let remaining = budget.finish();
        assert_eq!((work, remaining), (5, 2));
        let mut continued = ReflectedCodecBudget::new(&mut work, 8, remaining, &mut cancelled);
        continued
            .charge(3, 2)
            .expect("remaining allowance, not the original ceiling");
        assert_eq!((continued.work_used(), continued.remaining_bytes()), (8, 0));

        for (used, limit, units) in [(9, 8, 0), (u64::MAX, u64::MAX, 1)] {
            let mut work = used;
            let mut budget = ReflectedCodecBudget::new(&mut work, limit, 5, &mut cancelled);
            assert_eq!(budget.charge(units, 0), Err(DynamicReflectionError::WorkLimit));
            assert_eq!((budget.work_used(), budget.remaining_bytes()), (used, 5));
        }
        let mut cancelled = || true;
        let mut work = 0;
        let mut budget = ReflectedCodecBudget::new(&mut work, 8, 5, &mut cancelled);
        assert_eq!(budget.charge(1, 1), Err(DynamicReflectionError::Cancelled));
        assert_eq!((budget.work_used(), budget.remaining_bytes()), (0, 5));
    }

    #[test]
    fn reflected_codec_context_checks_owner_before_constructing_marker() {
        for fingerprint in ["", "bad.owner"] {
            let mut work = 0;
            let mut cancelled = || false;
            let mut budget = ReflectedCodecBudget::new(&mut work, 100, 0, &mut cancelled);
            assert!(matches!(
                ReflectedPositionalContext::new(fingerprint, &mut budget),
                Err(DynamicReflectionError::InvalidFingerprint)
            ));
            assert_eq!(budget.remaining_bytes(), 0);
        }
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 1000, 0, &mut cancelled);
        assert!(matches!(
            ReflectedPositionalContext::new(FP, &mut budget),
            Err(DynamicReflectionError::PayloadByteLimit)
        ));
        assert_eq!(budget.work_used(), FP.len() as u64);
    }

    #[test]
    fn reflected_codec_head_preserves_dotted_label_and_child_occurrences() {
        let term =
            GroundTerm::new("A.B", vec![GroundTerm::nullary("One"), GroundTerm::nullary("One")]);
        let par = reflect_ground_term_par(&term, FP);
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 100_000, 100_000, &mut cancelled);
        let context = ReflectedPositionalContext::new(FP, &mut budget).expect("context");
        let head = context
            .view(&par, &mut budget)
            .expect("bounded view")
            .expect("closed head");
        assert_eq!(head.label(), "A.B");
        assert_eq!(head.children().len(), 2);
        let (_, original) = positional_parts(&par).expect("positional fixture");
        assert_eq!(head.children().as_ptr(), original[1..].as_ptr());
        for child in head.children() {
            let child = context
                .view(child, &mut budget)
                .expect("child view")
                .expect("closed child");
            assert_eq!(child.label(), "One");
            assert!(child.children().is_empty());
        }
        let other =
            ReflectedPositionalContext::new("another-owner", &mut budget).expect("other context");
        assert!(other
            .view(&par, &mut budget)
            .expect("owner check")
            .is_none());
    }

    #[test]
    fn reflected_codec_native_round_trips_share_existing_reflector() {
        for value in [
            DynamicValue::Text(String::new()),
            DynamicValue::Text("α\0💡".into()),
            DynamicValue::Integer(i128::MIN),
            DynamicValue::Integer(i128::MAX),
            DynamicValue::Integer(0),
            DynamicValue::Boolean(false),
            DynamicValue::Boolean(true),
        ] {
            let native = match &value {
                DynamicValue::Text(text) => DynamicNativeRef::Text(text),
                DynamicValue::Integer(integer) => DynamicNativeRef::Integer(*integer),
                DynamicValue::Boolean(boolean) => DynamicNativeRef::Boolean(*boolean),
                _ => unreachable!("fixture consists only of native scalars"),
            };
            let mut work = 0;
            let mut cancelled = || false;
            let mut budget = ReflectedCodecBudget::new(&mut work, 100_000, 100_000, &mut cancelled);
            let label = encode_dynamic_native_label(native, &mut budget).expect("native writer");
            let ground = dynamic_syntax_to_ground_term(
                &value,
                &GrammarCoreV1::new("Native"),
                &BTreeMap::new(),
            )
            .expect("existing reflector");
            assert_eq!(ground.constructor, label);
            assert_eq!(
                decode_dynamic_native_label(&label, &mut budget).expect("native reader"),
                Some(value)
            );
            let par = reflect_ground_term_par(&ground, FP);
            let context = ReflectedPositionalContext::new(FP, &mut budget).expect("context");
            let head = context
                .view(&par, &mut budget)
                .expect("view")
                .expect("native head");
            assert_eq!(head.label(), label);
            assert!(head.children().is_empty(), "native reserved labels are unmarked");
        }
    }

    #[test]
    fn reflected_codec_native_rejects_noncanonical_payloads() {
        for label in [
            "^dynamic-text:fF",
            "^dynamic-text:f",
            "^dynamic-text:ff",
            "^dynamic-integer:+1",
            "^dynamic-integer:01",
            "^dynamic-integer:-0",
            "^dynamic-integer:170141183460469231731687303715884105728",
            "^dynamic-boolean:True",
            "^dynamic-boolean:1",
            "Other",
        ] {
            let mut work = 0;
            let mut cancelled = || false;
            let mut budget = ReflectedCodecBudget::new(&mut work, 100_000, 100_000, &mut cancelled);
            assert_eq!(
                decode_dynamic_native_label(label, &mut budget).expect("bounded rejection"),
                None,
                "{label}"
            );
        }
    }

    #[test]
    fn reflected_codec_precharges_decoding_and_encoding_and_keeps_failed_prefix() {
        let label = "^dynamic-text:61";
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget = ReflectedCodecBudget::new(&mut work, 100, 0, &mut cancelled);
        assert_eq!(
            decode_dynamic_native_label(label, &mut budget),
            Err(DynamicReflectionError::PayloadByteLimit)
        );
        assert_eq!(
            budget.work_used(),
            label.len() as u64,
            "the completed input scan is not refunded"
        );
        let before = budget.work_used();
        assert_eq!(
            encode_dynamic_native_label(DynamicNativeRef::Text("abc"), &mut budget),
            Err(DynamicReflectionError::PayloadByteLimit)
        );
        assert_eq!(budget.work_used(), before, "failed atomic output reservation spends nothing");
        let mut calls = 0;
        let mut cancel_after_scan = || {
            calls += 1;
            calls == 2
        };
        let mut work = 0;
        let mut budget = ReflectedCodecBudget::new(&mut work, 100, 100, &mut cancel_after_scan);
        assert_eq!(
            decode_dynamic_native_label(label, &mut budget),
            Err(DynamicReflectionError::Cancelled)
        );
        assert_eq!((budget.work_used(), budget.remaining_bytes()), (label.len() as u64, 100));
    }

    #[test]
    fn reflected_codec_head_checks_each_allocation_boundary() {
        let par = reflect_ground_term_par(&GroundTerm::nullary("Leaf"), FP);
        let mut work = 0;
        let mut cancelled = || false;
        let mut setup = ReflectedCodecBudget::new(&mut work, 100_000, 100_000, &mut cancelled);
        let context = ReflectedPositionalContext::new(FP, &mut setup).expect("context");
        setup.finish();
        let (head, _) = positional_parts(&par).expect("fixture head");
        let wire_len = private_tag_bytes(head).expect("fixture private tag").len();
        for (allowance, expected_work) in [(0, 1), (wire_len, 1 + wire_len as u64)] {
            let mut work = 0;
            let mut budget =
                ReflectedCodecBudget::new(&mut work, 100_000, allowance, &mut cancelled);
            assert!(matches!(
                context.view(&par, &mut budget),
                Err(DynamicReflectionError::PayloadByteLimit)
            ));
            assert_eq!(budget.work_used(), expected_work);
            assert_eq!(budget.remaining_bytes(), 0);
        }
        for (cancel_at, spent_work, spent_bytes) in [(2, 1, 0), (3, 1 + wire_len as u64, wire_len)]
        {
            let mut calls = 0;
            let mut cancel_before_allocation = || {
                calls += 1;
                calls == cancel_at
            };
            let mut work = 0;
            let mut budget = ReflectedCodecBudget::new(
                &mut work,
                100_000,
                100_000,
                &mut cancel_before_allocation,
            );
            assert!(matches!(
                context.view(&par, &mut budget),
                Err(DynamicReflectionError::Cancelled)
            ));
            assert_eq!(
                (budget.work_used(), budget.remaining_bytes()),
                (spent_work, 100_000 - spent_bytes)
            );
        }
    }

    #[test]
    fn reflected_codec_walk_and_error_cleanup_are_small_stack_safe() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut term = GroundTerm::nullary("Leaf");
                for _ in 0..20_000 {
                    term = GroundTerm::new("Node", vec![term]);
                }
                let par = reflect_ground_term_par(&term, FP);
                let mut work = 0;
                let mut cancelled = || false;
                let mut budget =
                    ReflectedCodecBudget::new(&mut work, 20_000_000, 20_000_000, &mut cancelled);
                let context = ReflectedPositionalContext::new(FP, &mut budget).expect("context");
                let mut current = &par;
                let mut count = 0;
                loop {
                    let head = context
                        .view(current, &mut budget)
                        .expect("bounded view")
                        .expect("strict head");
                    count += 1;
                    match head.children() {
                        [] => break,
                        [child] => current = child,
                        _ => panic!("unary fixture"),
                    }
                }
                assert_eq!(count, 20_001);
                let remainder = budget.finish();
                let mut exhausted =
                    ReflectedCodecBudget::new(&mut work, 0, remainder, &mut cancelled);
                assert!(matches!(
                    context.view(&par, &mut exhausted),
                    Err(DynamicReflectionError::WorkLimit)
                ));
                // Ordinary scope cleanup exercises the existing iterative Par and
                // GroundTerm destructors, including the error exit's retained input.
            })
            .expect("small-stack worker")
            .join()
            .expect("stack-safe codec traversal");
    }
}
