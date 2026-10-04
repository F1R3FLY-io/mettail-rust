//! Checked installed one-step rewrites for lookahead's existing breadth-first search.
//!
//! The first supported slice is one closed FLT at the subject root.  Host and
//! guest state remain separate: a rewrite changes only the checked guest slot,
//! never a tuplespace snapshot.  Any mixed configuration is refused until an
//! exact path-aware composite reifier can retain both halves without guessing.

use std::sync::Arc;

use mettail_dovetail_runtime::{
    SemanticInputLimits, SemanticTransitionDecision, SemanticTransitionInput,
    SemanticTransitionLimits,
};
use mettail_grammar_core::LanguageRight;
use mettail_rholang_codegen::{
    encode_dynamic_native_label, DynamicNativeRef, ReflectedCodecBudget, ReflectedPositionalContext,
};
use models::rhoapi::{expr::ExprInstance, tagged_continuation::TaggedCont, Par};
use rholang::rust::interpreter::accounting::{costs::Cost, RuntimeBudget};
use rholang::rust::interpreter::metering::MeteredMachine;

use crate::installed_flt::InstalledFltAdapter;
use crate::language_install::{exact_expr, grammar_fingerprint_label, RholangLanguageRuntime};
use crate::semantic_service::InstalledSemanticBundle;
use crate::semantic_wire::encode_normalization_step_v1;

use super::occurrences::{scan_top_level_reflected_exprs, validate_reifiable_host_par};
use super::search::{CheckedGuestEdge, CheckedGuestProvider};
use super::server::AdmittedLookaheadBinding;
use super::{
    CheckedGuestConfiguration, GuestRewriteIdentity, GuestSlotState, SpeculationError,
    SpeculativeState,
};

const SLOT_DESCRIPTOR_BYTES: usize = 24;
const COMPOSITE_REIFICATION_DEPTH: usize = 64;

fn refuse(message: &'static str) -> SpeculationError {
    SpeculationError::Bootstrap(message.into())
}

fn never_cancelled() -> bool {
    false
}

/// An operation-local bridge from sealed installed bindings to the searcher's
/// checked edge roster. All kernel and codec work is charged to `host`, even if
/// the operation later refuses. The host snapshot is never edited here.
pub(crate) struct InstalledCheckedGuestProvider {
    runtime: Arc<RholangLanguageRuntime>,
    bindings: Vec<AdmittedLookaheadBinding>,
    host: RuntimeBudget,
    staged_guest: Option<Par>,
}

impl InstalledCheckedGuestProvider {
    pub(crate) fn new(
        runtime: Arc<RholangLanguageRuntime>,
        bindings: Vec<AdmittedLookaheadBinding>,
        host: RuntimeBudget,
    ) -> Result<Self, SpeculationError> {
        if bindings.len() != 1 || !bindings[0].path.is_empty() || bindings[0].context != 0 {
            return Err(refuse("installed lookahead currently requires one closed root binding"));
        }
        Ok(Self {
            runtime,
            bindings,
            host,
            staged_guest: None,
        })
    }

    fn binding(&self) -> &AdmittedLookaheadBinding {
        &self.bindings[0]
    }

    fn metered<T>(
        &self,
        operation: impl FnOnce(
            &mut ReflectedCodecBudget<'_, fn() -> bool>,
            SemanticTransitionLimits,
        ) -> Result<T, SpeculationError>,
    ) -> Result<T, SpeculationError> {
        let policy = self.runtime.service().policy().semantic_service;
        let limits =
            policy.effective(self.binding().installed.language_core().theory.limits, policy);
        let available = self.host.remaining().value.max(0) as u64;
        let ceiling = limits.execution.work.min(available);
        if ceiling == 0 {
            return Err(refuse("installed lookahead has no funded host work"));
        }
        let mut used = 0;
        let mut cancelled: fn() -> bool = never_cancelled;
        let mut budget = ReflectedCodecBudget::new(
            &mut used,
            ceiling,
            limits.boundary_payload_bytes,
            &mut cancelled,
        );
        let result =
            operation(&mut budget, SemanticTransitionLimits { work: ceiling, ..limits.execution });
        let spent = budget.work_used();
        drop(budget);
        if spent != 0 {
            let charge = i64::try_from(spent)
                .map_err(|_| refuse("installed lookahead work exceeds host charge domain"))?;
            MeteredMachine::new(self.host.clone())
                .reserve_primitive(Cost::create(charge, "installed lookahead guest operation"))
                .map_err(|_| refuse("installed lookahead exhausted host phlogiston"))?;
        }
        result
    }

    fn live_owner<C: FnMut() -> bool>(
        &self,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<(), SpeculationError> {
        budget
            .charge(1, 0)
            .map_err(|_| refuse("installed lookahead owner check exhausted budget"))?;
        let binding = self.binding();
        let live = self
            .runtime
            .service()
            .table()
            .authorize(&binding.handle, LanguageRight::Reduce)
            .map_err(|_| refuse("installed lookahead owner is revoked or lacks Reduce"))?;
        if !Arc::ptr_eq(&live, &binding.installed) {
            return Err(refuse("installed lookahead owner changed after admission"));
        }
        Ok(())
    }

    fn require_empty_host(host: &SpeculativeState) -> Result<(), SpeculationError> {
        // The installed bootstrap tables are ambient, but any ordinary datum,
        // continuation or join means this is not a direct-root-only request.
        // Inspect the store maps without reifying (and allocating) a hostile
        // composite configuration before a budget is available.
        if !host.data.values().all(Vec::is_empty)
            || !host.continuations.values().all(Vec::is_empty)
            || !host.joins.values().all(Vec::is_empty)
        {
            return Err(refuse("installed lookahead mixed host/guest state is not yet supported"));
        }
        Ok(())
    }

    fn checked_input<C: FnMut() -> bool>(
        &self,
        value: &Par,
        adapter: &InstalledFltAdapter<'_>,
        limits: SemanticTransitionLimits,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<SemanticTransitionInput, SpeculationError> {
        let native = match exact_expr(value) {
            Some(ExprInstance::GString(text)) => Some(DynamicNativeRef::Text(text)),
            Some(ExprInstance::GInt(integer)) => {
                Some(DynamicNativeRef::Integer(i128::from(*integer)))
            },
            Some(ExprInstance::GBool(boolean)) => Some(DynamicNativeRef::Boolean(*boolean)),
            _ => None,
        };
        let reflected_native = if let Some(native) = native {
            let fingerprint = grammar_fingerprint_label(
                self.binding().installed.commitment().language_fingerprint,
            );
            let context = ReflectedPositionalContext::new(&fingerprint, budget)
                .map_err(|_| refuse("installed lookahead native reflection exhausted budget"))?;
            let label = encode_dynamic_native_label(native, budget)
                .map_err(|_| refuse("installed lookahead native reflection failed"))?;
            Some(
                context
                    .assemble(&label, Vec::new(), budget)
                    .map_err(|_| refuse("installed lookahead native reflection failed"))?
                    .0,
            )
        } else {
            None
        };
        adapter
            .to_kernel(
                reflected_native.as_ref().unwrap_or(value),
                self.binding().category,
                SemanticInputLimits {
                    work: limits.work,
                    nodes: limits.term_nodes,
                    bytes: limits.term_bytes,
                },
                budget,
            )
            .map_err(|_| refuse("installed lookahead guest value failed exact re-admission"))
    }

    fn composite_public<C: FnMut() -> bool>(
        &self,
        host: &SpeculativeState,
        guest: &Par,
        budget: &mut ReflectedCodecBudget<'_, C>,
    ) -> Result<Par, SpeculationError> {
        for (channel, data) in &host.data {
            validate_reifiable_host_par(channel, COMPOSITE_REIFICATION_DEPTH, budget)
                .map_err(|_| refuse("installed lookahead host channel is not safely reifiable"))?;
            for datum in data {
                budget
                    .charge(1, std::mem::size_of_val(datum))
                    .map_err(|_| refuse("installed lookahead host datum exceeds budget"))?;
                for value in &datum.a.pars {
                    validate_reifiable_host_par(value, COMPOSITE_REIFICATION_DEPTH, budget)
                        .map_err(|_| {
                            refuse("installed lookahead host datum hides a guest or exceeds budget")
                        })?;
                }
            }
        }
        for (channels, waiting) in &host.continuations {
            for channel in channels {
                validate_reifiable_host_par(channel, COMPOSITE_REIFICATION_DEPTH, budget).map_err(
                    |_| refuse("installed lookahead receive channel is not safely reifiable"),
                )?;
            }
            for continuation in waiting {
                budget
                    .charge(1, std::mem::size_of_val(continuation))
                    .map_err(|_| refuse("installed lookahead continuation exceeds budget"))?;
                for pattern in continuation.patterns.iter() {
                    for value in &pattern.patterns {
                        validate_reifiable_host_par(value, COMPOSITE_REIFICATION_DEPTH, budget)
                            .map_err(|_| refuse("installed lookahead host pattern hides a guest or exceeds budget"))?;
                    }
                }
                if let Some(guard) = &continuation.continuation.guard {
                    validate_reifiable_host_par(guard, COMPOSITE_REIFICATION_DEPTH, budget)
                        .map_err(|_| {
                            refuse("installed lookahead host guard hides a guest or exceeds budget")
                        })?;
                }
                if let Some(TaggedCont::ParBody(body)) = &continuation.continuation.tagged_cont {
                    if let Some(process) = &body.body {
                        validate_reifiable_host_par(process, COMPOSITE_REIFICATION_DEPTH, budget)
                            .map_err(|_| {
                            refuse("installed lookahead host body hides a guest or exceeds budget")
                        })?;
                    }
                }
            }
        }
        for channel in host.joins.keys() {
            validate_reifiable_host_par(channel, COMPOSITE_REIFICATION_DEPTH, budget)
                .map_err(|_| refuse("installed lookahead join channel is not safely reifiable"))?;
        }
        let reified = super::delivery::reify(host)
            .map_err(|_| refuse("installed lookahead host state cannot be reified"))?;
        budget
            .charge(1, std::mem::size_of::<Par>())
            .map_err(|_| refuse("installed lookahead composite assembly exceeds budget"))?;
        Ok(reified.append(guest.clone()))
    }
}

impl CheckedGuestProvider for InstalledCheckedGuestProvider {
    fn prepare_host_program(&mut self, submitted: &Par) -> Result<Par, SpeculationError> {
        let Some(index) = self.binding().top_level_expr else {
            return Ok(submitted.clone());
        };
        let (host_program, guest) = self.metered(|budget, _limits| {
            self.live_owner(budget)?;
            let occurrences = scan_top_level_reflected_exprs(submitted, budget).map_err(|_| {
                refuse("installed composite subject scan failed or exceeded budget")
            })?;
            let [occurrence] = occurrences.as_slice() else {
                return Err(refuse("installed composite requires exactly one top-level guest"));
            };
            if occurrence.index != index {
                return Err(refuse("installed composite locator changed before saturation"));
            }
            let fingerprint = grammar_fingerprint_label(
                self.binding().installed.commitment().language_fingerprint,
            );
            if occurrence.fingerprint != fingerprint {
                return Err(refuse("installed composite owner changed before saturation"));
            }
            // `Par::clone` is iterative in the shared models crate. The
            // complete scanner above charges the source tree before copying.
            let mut host_program = submitted.clone();
            let mut guest = Par::default();
            guest.exprs.push(host_program.exprs.remove(index));
            Ok((host_program, guest))
        })?;
        self.staged_guest = Some(guest);
        Ok(host_program)
    }

    fn initial(
        &mut self,
        submitted: &Par,
        saturated_host: &SpeculativeState,
    ) -> Result<CheckedGuestConfiguration, SpeculationError> {
        let composite = self.binding().top_level_expr.is_some();
        if !composite {
            Self::require_empty_host(saturated_host)?;
        }
        let guest = if composite {
            self.staged_guest
                .take()
                .ok_or_else(|| refuse("installed composite was not split before saturation"))?
        } else {
            submitted.clone()
        };
        self.metered(|budget, limits| {
            self.live_owner(budget)?;
            let binding = self.binding();
            let adapter = InstalledFltAdapter::new(&binding.installed, budget)
                .map_err(|_| refuse("installed lookahead FLT adapter could not be prepared"))?;
            let checked = self.checked_input(&guest, &adapter, limits, budget)?;
            if checked.exact_key().as_bytes() != binding.input.exact_key().as_bytes() {
                return Err(refuse(
                    "installed lookahead submitted root differs from admitted owner binding",
                ));
            }
            let key = binding.input.exact_key().as_bytes();
            let copy_bytes = key
                .len()
                .checked_mul(3)
                .ok_or_else(|| refuse("installed lookahead root key is too large"))?;
            budget
                .charge(3, copy_bytes)
                .map_err(|_| refuse("installed lookahead root exceeds budget"))?;
            let public_configuration = if composite {
                self.composite_public(saturated_host, &guest, budget)?
            } else {
                guest.clone()
            };
            Ok(CheckedGuestConfiguration {
                slots: vec![GuestSlotState {
                    binding_index: 0,
                    value: guest,
                    exact_key: key.to_vec(),
                }],
                public_configuration,
            })
        })
    }

    fn complete_roster(
        &mut self,
        host: &SpeculativeState,
        current: &CheckedGuestConfiguration,
    ) -> Result<Vec<CheckedGuestEdge>, SpeculationError> {
        let composite = self.binding().top_level_expr.is_some();
        if !composite {
            Self::require_empty_host(host)?;
        }
        let [slot] = current.slots.as_slice() else {
            return Err(refuse("installed lookahead lost its single checked root slot"));
        };
        if slot.binding_index != 0 || (!composite && current.public_configuration != slot.value) {
            return Err(refuse("installed lookahead root configuration is inconsistent"));
        }
        self.metered(|budget, limits| {
            self.live_owner(budget)?;
            if composite
                && self.composite_public(host, &slot.value, budget)? != current.public_configuration
            {
                return Err(refuse(
                    "installed composite public state differs from checked host and guest",
                ));
            }
            let binding = self.binding();
            let prepared = InstalledSemanticBundle::prepare(
                self.runtime.service().table(),
                &binding.handle,
                &[LanguageRight::Reduce],
                budget,
            )
            .map_err(|_| refuse("installed lookahead semantic image is unavailable"))?;
            if !Arc::ptr_eq(prepared.installed(), &binding.installed) {
                return Err(refuse("installed lookahead semantic owner changed"));
            }
            let adapter = InstalledFltAdapter::new(prepared.installed(), budget)
                .map_err(|_| refuse("installed lookahead FLT adapter could not be prepared"))?;
            let input = self.checked_input(&slot.value, &adapter, limits, budget)?;
            if input.exact_key().as_bytes() != slot.exact_key {
                return Err(refuse("installed lookahead root changed under its binding"));
            }
            let admission = input.admission_work();
            let executed = budget
                .run_accounted_stage(|remaining, cancel| {
                    let Some(ceiling) = admission.checked_add(remaining) else {
                        return (Err(refuse("installed lookahead kernel ceiling overflow")), 0);
                    };
                    match prepared.execute_step_roster_accounted(
                        binding.sort,
                        input,
                        SemanticTransitionLimits { work: ceiling, ..limits },
                        cancel,
                    ) {
                        Err(_) => {
                            (Err(refuse("installed lookahead rewrite kernel unavailable")), 0)
                        },
                        Ok((decision, aggregate)) => match aggregate.checked_sub(admission) {
                            Some(extra) => (Ok((decision, aggregate)), extra),
                            None => (
                                Err(refuse("installed lookahead kernel underreported admission")),
                                0,
                            ),
                        },
                    }
                })
                .map_err(|_| refuse("installed lookahead rewrite roster exhausted budget"))??;
            let (decision, aggregate) = executed;
            let proven = match decision {
                SemanticTransitionDecision::ProvenSteps(proven) => proven,
                SemanticTransitionDecision::Undetermined { .. } => {
                    return Err(refuse("installed lookahead rewrite roster is undetermined"));
                },
                SemanticTransitionDecision::Refuted(_) => {
                    return Err(refuse("installed lookahead rewrite roster was refuted"));
                },
                _ => {
                    return Err(refuse("installed lookahead kernel returned the wrong roster kind"))
                },
            };
            let commitment = binding.installed.commitment();
            if proven.work != aggregate
                || proven.language_fingerprint != commitment.language_fingerprint
                || proven.theory_fingerprint != commitment.theory_fingerprint
                || Some(proven.image_fingerprint) != commitment.semantic_image_fingerprint
                || proven.relation_sort != binding.sort
                || proven.input != slot.exact_key
            {
                return Err(refuse("installed lookahead rewrite roster has wrong owner or input"));
            }
            let outputs = adapter
                .reflect_rewrite_steps(&proven, binding.sort, budget)
                .map_err(|_| refuse("installed lookahead could not reflect the complete roster"))?;
            if outputs.len() != proven.occurrences.len() {
                return Err(refuse("installed lookahead reflected roster length changed"));
            }
            let bytes = outputs
                .len()
                .checked_mul(SLOT_DESCRIPTOR_BYTES)
                .ok_or_else(|| refuse("installed lookahead successor roster is too large"))?;
            budget
                .charge(outputs.len(), bytes)
                .map_err(|_| refuse("installed lookahead successor roster exceeds budget"))?;
            let mut edges = Vec::new();
            edges
                .try_reserve(outputs.len())
                .map_err(|_| refuse("installed lookahead successor roster allocation failed"))?;
            for (position, (occurrence, output)) in
                proven.occurrences.into_iter().zip(outputs).enumerate()
            {
                if occurrence.ordinal != position
                    || occurrence.output_sort != binding.sort
                    || occurrence.receipt.before != slot.exact_key
                {
                    return Err(refuse("installed lookahead rewrite occurrence is out of order"));
                }
                let checked = self.checked_input(&output, &adapter, limits, budget)?;
                let key = checked.exact_key().as_bytes();
                budget
                    .charge(key.len(), key.len())
                    .map_err(|_| refuse("installed lookahead successor key exceeds budget"))?;
                if occurrence.receipt.after != key {
                    return Err(refuse("installed lookahead rewrite proof has wrong target"));
                }
                let receipt = encode_normalization_step_v1(occurrence.receipt, budget)
                    .map_err(|_| refuse("installed lookahead proof encoding failed"))?;
                let ordinal = u64::try_from(occurrence.ordinal)
                    .map_err(|_| refuse("installed lookahead proof ordinal overflow"))?;
                budget
                    .charge(2, key.len())
                    .map_err(|_| refuse("installed lookahead successor exceeds budget"))?;
                let identity = match binding.top_level_expr {
                    Some(index) => GuestRewriteIdentity::top_level_expr(
                        u32::try_from(index)
                            .map_err(|_| refuse("installed composite locator overflow"))?,
                        commitment.language_fingerprint,
                        proven.image_fingerprint,
                        ordinal,
                        receipt,
                    ),
                    None => GuestRewriteIdentity::new(
                        binding.path.clone(),
                        commitment.language_fingerprint,
                        proven.image_fingerprint,
                        ordinal,
                        receipt,
                    ),
                };
                edges.push(CheckedGuestEdge {
                    identity,
                    successor: CheckedGuestConfiguration {
                        slots: vec![GuestSlotState {
                            binding_index: 0,
                            value: output.clone(),
                            exact_key: key.to_vec(),
                        }],
                        public_configuration: if composite {
                            self.composite_public(host, &output, budget)?
                        } else {
                            output
                        },
                    },
                });
            }
            Ok(edges)
        })
    }

    fn after_host_comm(
        &mut self,
        previous: &CheckedGuestConfiguration,
        host: &SpeculativeState,
    ) -> Result<CheckedGuestConfiguration, SpeculationError> {
        let composite = self.binding().top_level_expr.is_some();
        if !composite {
            Self::require_empty_host(host)?;
        }
        let [slot] = previous.slots.as_slice() else {
            return Err(refuse("installed lookahead lost its single checked root slot"));
        };
        if slot.binding_index != 0 || (!composite && previous.public_configuration != slot.value) {
            return Err(refuse("installed lookahead root configuration is inconsistent"));
        }
        self.metered(|budget, limits| {
            self.live_owner(budget)?;
            let adapter = InstalledFltAdapter::new(&self.binding().installed, budget)
                .map_err(|_| refuse("installed lookahead FLT adapter could not be prepared"))?;
            let input = self.checked_input(&slot.value, &adapter, limits, budget)?;
            if input.exact_key().as_bytes() != slot.exact_key {
                return Err(refuse("installed lookahead root changed after host COMM"));
            }
            let retained_bytes = slot
                .exact_key
                .len()
                .checked_mul(2)
                .ok_or_else(|| refuse("installed lookahead retained root is too large"))?;
            budget
                .charge(2, retained_bytes)
                .map_err(|_| refuse("installed lookahead retained root exceeds budget"))?;
            if composite {
                Ok(CheckedGuestConfiguration {
                    slots: previous.slots.clone(),
                    public_configuration: self.composite_public(host, &slot.value, budget)?,
                })
            } else {
                Ok(previous.clone())
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    use crypto::rust::hash::blake2b512_random::Blake2b512Random;
    use mettail_grammar_core::RuntimeTemplatePiece;

    use crate::speculation::search::Lookahead;
    use crate::speculation::service::{LeafProjection, LookaheadRequest, LookaheadService};
    use crate::speculation::TraceStepIdentity;

    use models::rhoapi::{ReceiveBind, Send};
    use models::rust::utils::{new_freevar_par, new_gint_par, new_gstring_par, new_receive_par};

    fn one_host_comm() -> Par {
        let channel = new_gstring_par("installed-composite-host".into(), Vec::new(), false);
        let send = Par::default().with_sends(vec![Send {
            chan: Some(channel.clone()),
            data: vec![new_gint_par(1, Vec::new(), false)],
            persistent: false,
            locally_free: Vec::new(),
            connective_used: false,
        }]);
        let receive = new_receive_par(
            vec![ReceiveBind {
                patterns: vec![new_freevar_par(0, Vec::new())],
                source: Some(channel),
                remainder: None,
                free_count: 1,
            }],
            Par::default(),
            false,
            false,
            1,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        send.append(receive)
    }

    #[test]
    fn empty_history_buckets_are_inert_but_occupied_host_buckets_refuse() {
        let mut host = SpeculativeState::default();
        let channel = Par::default();
        let group = vec![channel.clone()];
        host.data.insert(channel.clone(), Vec::new());
        host.continuations.insert(group.clone(), Vec::new());
        host.joins.insert(channel.clone(), Vec::new());
        InstalledCheckedGuestProvider::require_empty_host(&host)
            .expect("empty history-cache buckets carry no host process");

        host.data
            .get_mut(&channel)
            .unwrap()
            .push(Default::default());
        assert!(InstalledCheckedGuestProvider::require_empty_host(&host).is_err());
        host.data.get_mut(&channel).unwrap().clear();

        host.continuations
            .get_mut(&group)
            .unwrap()
            .push(Default::default());
        assert!(InstalledCheckedGuestProvider::require_empty_host(&host).is_err());
        host.continuations.get_mut(&group).unwrap().clear();

        host.joins.get_mut(&channel).unwrap().push(group);
        assert!(InstalledCheckedGuestProvider::require_empty_host(&host).is_err());
    }

    #[test]
    fn installed_regex_root_uses_checked_rewrite_roster_and_retains_proofs() {
        let (runtime, token, installed) =
            crate::language_install::tests::installed_flt_adapter_fixture();
        let subject = runtime
            .construct_template(
                &token,
                &[RuntimeTemplatePiece::Text("a+".into())],
                &[],
                Some("Pattern"),
                &BTreeMap::new(),
            )
            .expect("actual installed Regex FLT");
        let handle = runtime
            .resolve(&token, LanguageRight::Reduce)
            .expect("Reduce grant");
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget =
            ReflectedCodecBudget::new(&mut work, 10_000_000, 10_000_000, &mut cancelled);
        let adapter = InstalledFltAdapter::new(&installed, &mut budget).expect("checked adapter");
        let (category, sort) = adapter
            .select_category("Pattern", &mut budget)
            .expect("Pattern");
        let input = adapter
            .to_kernel(
                &subject,
                category,
                SemanticInputLimits {
                    work: 1_000_000,
                    nodes: 10_000,
                    bytes: 1_000_000,
                },
                &mut budget,
            )
            .expect("checked root");
        let host = RuntimeBudget::new(Cost::create(10_000_000, "installed lookahead test"));
        let mut provider = InstalledCheckedGuestProvider::new(
            Arc::new(runtime),
            vec![AdmittedLookaheadBinding {
                path: Vec::new(),
                top_level_expr: None,
                handle,
                installed,
                sort,
                category,
                context: 0,
                input,
            }],
            host,
        )
        .expect("direct root is supported");
        let empty = SpeculativeState::default();
        let root = provider
            .initial(&subject, &empty)
            .expect("checked initial root");
        let edges = provider
            .complete_roster(&empty, &root)
            .expect("complete Regex step roster");
        assert!(!edges.is_empty(), "ExpandPlus supplies a directed rewrite");
        for (position, edge) in edges.iter().enumerate() {
            assert_eq!(edge.identity.ordinal, position as u64);
            assert!(edge.identity.location.is_empty());
            assert_eq!(edge.successor.slots.len(), 1);
            assert_eq!(edge.successor.public_configuration, edge.successor.slots[0].value);
            assert_ne!(edge.successor.public_configuration, subject);
        }
    }

    #[tokio::test]
    async fn service_replies_with_a_real_installed_regex_rewrite_not_the_inert_root() {
        let (runtime, token, installed) =
            crate::language_install::tests::installed_flt_adapter_fixture();
        let subject = runtime
            .construct_template(
                &token,
                &[RuntimeTemplatePiece::Text("a+".into())],
                &[],
                Some("Pattern"),
                &BTreeMap::new(),
            )
            .expect("actual installed Regex FLT");
        let handle = runtime
            .resolve(&token, LanguageRight::Reduce)
            .expect("Reduce grant");
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget =
            ReflectedCodecBudget::new(&mut work, 10_000_000, 10_000_000, &mut cancelled);
        let adapter = InstalledFltAdapter::new(&installed, &mut budget).expect("checked adapter");
        let (category, sort) = adapter
            .select_category("Pattern", &mut budget)
            .expect("Pattern");
        let input = adapter
            .to_kernel(
                &subject,
                category,
                SemanticInputLimits {
                    work: 1_000_000,
                    nodes: 10_000,
                    bytes: 1_000_000,
                },
                &mut budget,
            )
            .expect("checked root");
        let binding = AdmittedLookaheadBinding {
            path: Vec::new(),
            top_level_expr: None,
            handle,
            installed,
            sort,
            category,
            context: 0,
            input,
        };
        let host = RuntimeBudget::new(Cost::create(10_000_000, "installed lookahead service test"));
        let response = LookaheadService::serve(
            LookaheadRequest::new(subject.clone(), Lookahead::Unbounded)
                .with_projection(LeafProjection::InstalledGuestRoot)
                .with_installed_bindings(Arc::new(runtime), vec![binding]),
            Blake2b512Random::create_from_length(128),
            &host,
        )
        .await
        .expect("bounded installed service request");
        assert!(response.error.is_none());
        assert!(response.failure.is_empty());
        assert!(response.truncated.is_empty());
        assert!(!response.reply.is_empty(), "a+ has a checked successor");
        assert!(response.reply.iter().all(|result| result != &subject));
        assert!(response.exploration.success.iter().all(|leaf| {
            leaf.trace.len() == 1
                && matches!(
                    leaf.trace.step_identities().as_slice(),
                    [TraceStepIdentity::GuestRewrite(_)]
                )
        }));
    }

    #[tokio::test]
    async fn top_level_installed_guest_and_host_comm_share_one_every_trace_search() {
        let (runtime, token, installed) =
            crate::language_install::tests::installed_flt_adapter_fixture();
        let guest = runtime
            .construct_template(
                &token,
                &[RuntimeTemplatePiece::Text("a+".into())],
                &[],
                Some("Pattern"),
                &BTreeMap::new(),
            )
            .expect("installed Regex FLT");
        let handle = runtime
            .resolve(&token, LanguageRight::Reduce)
            .expect("Reduce grant");
        let mut work = 0;
        let mut cancelled = || false;
        let mut budget =
            ReflectedCodecBudget::new(&mut work, 10_000_000, 10_000_000, &mut cancelled);
        let adapter = InstalledFltAdapter::new(&installed, &mut budget).expect("checked adapter");
        let (category, sort) = adapter
            .select_category("Pattern", &mut budget)
            .expect("Pattern");
        let input = adapter
            .to_kernel(
                &guest,
                category,
                SemanticInputLimits {
                    work: 1_000_000,
                    nodes: 10_000,
                    bytes: 1_000_000,
                },
                &mut budget,
            )
            .expect("checked guest term");
        drop(budget);
        let subject = guest.append(one_host_comm());
        let binding = AdmittedLookaheadBinding {
            path: Vec::new(),
            top_level_expr: Some(0),
            handle,
            installed,
            sort,
            category,
            context: 0,
            input,
        };
        let host = RuntimeBudget::new(Cost::create(10_000_000, "mixed lookahead test"));
        let response = LookaheadService::serve(
            LookaheadRequest::new(subject.clone(), Lookahead::Steps(2))
                .with_projection(LeafProjection::Configuration)
                .with_installed_bindings(Arc::new(runtime), vec![binding]),
            Blake2b512Random::create_from_length(128),
            &host,
        )
        .await
        .expect("mixed installed search is admitted");
        assert!(response.error.is_none());
        assert!(response.failure.is_empty());
        assert!(response.truncated.is_empty());
        assert_eq!(
            response.exploration.success.len(),
            2,
            "one guest edge and one host COMM have both orders"
        );
        let identities: Vec<_> = response
            .exploration
            .success
            .iter()
            .map(|leaf| leaf.trace.step_identities())
            .chain(
                response
                    .exploration
                    .truncated
                    .iter()
                    .map(|leaf| leaf.branch.trace.step_identities()),
            )
            .collect();
        assert!(identities.iter().any(|trace| matches!(
            trace.as_slice(),
            [TraceStepIdentity::HostComm(_), TraceStepIdentity::GuestRewrite(_)]
        )));
        assert!(identities.iter().any(|trace| matches!(
            trace.as_slice(),
            [TraceStepIdentity::GuestRewrite(_), TraceStepIdentity::HostComm(_)]
        )));
    }
}
