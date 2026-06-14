//! Call-by-need budget admission for generic Rho lowering.
//!
//! The generic CBN/need path represents non-native computations as thunks.
//! This module is the compile-time/runtime-planning contract for bounded force
//! admission: every force consumes one lookahead step, and a cold force that
//! must allocate a memo cell also consumes one heap cell.

use std::collections::{BTreeMap, BTreeSet};

use models::rhoapi::{MatchCase, Par, Receive, ReceiveBind};
use models::rust::utils::{
    new_boundvar_par, new_freevar_par, new_gstring_par, new_match_par, new_new_par,
    new_receive_par, new_send_par, union,
};

use crate::ast::{RhoAstBuildError, RhoAstLiteral};
use crate::lower::{RhoAstProgram, RhoAstValidationProfile, RhoProgram};
use crate::validate::{RhoValidationError, ValidatedRhoProgram};

/// Remaining admission budget for generic call-by-need forcing.
#[must_use]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallByNeedBudget {
    pub lookahead_remaining: usize,
    pub heap_remaining: usize,
}

impl CallByNeedBudget {
    pub const fn new(lookahead_remaining: usize, heap_remaining: usize) -> Self {
        Self { lookahead_remaining, heap_remaining }
    }
}

/// Whether a force observes an existing memo cell or must create one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallByNeedForce {
    MemoHit,
    MemoMiss,
}

/// Reason a call-by-need force is not admitted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallByNeedBudgetBlocker {
    LookaheadExceeded,
    HeapBudgetExceeded,
}

/// Result of checking whether a force may run under the current budget.
#[must_use]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallByNeedAdmission {
    pub budget_after: CallByNeedBudget,
    pub blocker: Option<CallByNeedBudgetBlocker>,
}

impl CallByNeedAdmission {
    pub const fn allowed(budget_after: CallByNeedBudget) -> Self {
        Self { budget_after, blocker: None }
    }

    pub const fn blocked(blocker: CallByNeedBudgetBlocker, budget_after: CallByNeedBudget) -> Self {
        Self { budget_after, blocker: Some(blocker) }
    }

    pub const fn is_allowed(&self) -> bool {
        self.blocker.is_none()
    }
}

/// Admit one generic call-by-need force under `budget`.
///
/// Failed admission preserves the incoming budget. A memo hit does not allocate
/// a heap cell; a memo miss does.
pub const fn admit_call_by_need_force(
    force: CallByNeedForce,
    budget: CallByNeedBudget,
) -> CallByNeedAdmission {
    if budget.lookahead_remaining == 0 {
        return CallByNeedAdmission::blocked(CallByNeedBudgetBlocker::LookaheadExceeded, budget);
    }

    let after_lookahead = budget.lookahead_remaining - 1;
    match force {
        CallByNeedForce::MemoHit => CallByNeedAdmission::allowed(CallByNeedBudget::new(
            after_lookahead,
            budget.heap_remaining,
        )),
        CallByNeedForce::MemoMiss => {
            if budget.heap_remaining == 0 {
                CallByNeedAdmission::blocked(CallByNeedBudgetBlocker::HeapBudgetExceeded, budget)
            } else {
                CallByNeedAdmission::allowed(CallByNeedBudget::new(
                    after_lookahead,
                    budget.heap_remaining - 1,
                ))
            }
        },
    }
}

/// Initial memo state for the generated call-by-need thunk slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallByNeedInitialState {
    Cold,
    Hot,
}

impl CallByNeedInitialState {
    const fn token(self) -> &'static str {
        match self {
            Self::Cold => "cold",
            Self::Hot => "hot",
        }
    }
}

/// Invalid parameterization for a generated call-by-need thunk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallByNeedThunkSpecError {
    InvalidValue(RhoAstBuildError),
    EmptyEvalMarker,
    EmptyOutputChannel,
    EmptyEvalChannel,
    ObservationChannelsMustDiffer,
}

/// Parameterization for a generated M-RHO.2 call-by-need thunk.
///
/// The shape stays fixed so the validator can continue proving the topology:
/// one private thunk contract, one state cell, one memo cell, and two observer
/// continuations. The payload, compute marker, and public observation channels
/// are generated-language parameters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallByNeedThunkSpec {
    initial_state: CallByNeedInitialState,
    value: RhoAstLiteral,
    eval_marker: String,
    out_channel: String,
    eval_channel: String,
}

impl CallByNeedThunkSpec {
    pub fn new(
        initial_state: CallByNeedInitialState,
        value: RhoAstLiteral,
        eval_marker: impl Into<String>,
        out_channel: impl Into<String>,
        eval_channel: impl Into<String>,
    ) -> Result<Self, CallByNeedThunkSpecError> {
        let spec = Self {
            initial_state,
            value,
            eval_marker: eval_marker.into(),
            out_channel: out_channel.into(),
            eval_channel: eval_channel.into(),
        };
        spec.validate()?;
        Ok(spec)
    }

    pub fn default_for(initial_state: CallByNeedInitialState) -> Self {
        Self {
            initial_state,
            value: RhoAstLiteral::String("value".to_string()),
            eval_marker: "compute".to_string(),
            out_channel: "OUT".to_string(),
            eval_channel: "EVAL".to_string(),
        }
    }

    pub fn initial_state(&self) -> CallByNeedInitialState {
        self.initial_state
    }

    pub fn value(&self) -> &RhoAstLiteral {
        &self.value
    }

    pub fn eval_marker(&self) -> &str {
        &self.eval_marker
    }

    pub fn out_channel(&self) -> &str {
        &self.out_channel
    }

    pub fn eval_channel(&self) -> &str {
        &self.eval_channel
    }

    fn validate(&self) -> Result<(), CallByNeedThunkSpecError> {
        self.value
            .try_to_par()
            .map_err(CallByNeedThunkSpecError::InvalidValue)?;
        if self.eval_marker.is_empty() {
            return Err(CallByNeedThunkSpecError::EmptyEvalMarker);
        }
        if self.out_channel.is_empty() {
            return Err(CallByNeedThunkSpecError::EmptyOutputChannel);
        }
        if self.eval_channel.is_empty() {
            return Err(CallByNeedThunkSpecError::EmptyEvalChannel);
        }
        if self.out_channel == self.eval_channel {
            return Err(CallByNeedThunkSpecError::ObservationChannelsMustDiffer);
        }
        Ok(())
    }
}

/// Named evidence gate for accepting a planned call-by-need thunk artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CallByNeedPlanEvidenceGate {
    Proof,
    RuntimeOracle,
    Budget,
}

/// Evidence references required before a call-by-need thunk can be used through
/// the planned execution boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallByNeedPlanEvidence {
    pub proof_evidence_refs: Vec<String>,
    pub runtime_oracle_evidence_refs: Vec<String>,
    pub budget_evidence_refs: Vec<String>,
}

impl CallByNeedPlanEvidence {
    fn diagnostics(&self) -> Vec<CallByNeedPlanEvidenceDiagnostic> {
        let mut diagnostics = Vec::new();
        diagnose_evidence_refs(
            CallByNeedPlanEvidenceGate::Proof,
            &self.proof_evidence_refs,
            &mut diagnostics,
        );
        diagnose_evidence_refs(
            CallByNeedPlanEvidenceGate::RuntimeOracle,
            &self.runtime_oracle_evidence_refs,
            &mut diagnostics,
        );
        diagnose_evidence_refs(
            CallByNeedPlanEvidenceGate::Budget,
            &self.budget_evidence_refs,
            &mut diagnostics,
        );
        diagnostics
    }

    fn accepted_refs(&self) -> Vec<String> {
        let mut refs = BTreeSet::new();
        push_evidence_refs(&mut refs, &self.proof_evidence_refs);
        push_evidence_refs(&mut refs, &self.runtime_oracle_evidence_refs);
        push_evidence_refs(&mut refs, &self.budget_evidence_refs);
        refs.insert("mettail-rho-codegen:call-by-need-artifact-validation:NormalizedAst".into());
        refs.insert("mettail-rho-codegen:call-by-need-budget-admission:two-forces".into());
        refs.into_iter().collect()
    }
}

/// Evidence-reference hygiene diagnostics for call-by-need planning.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallByNeedPlanEvidenceDiagnostic {
    MissingEvidenceRefs { gate: CallByNeedPlanEvidenceGate },
    BlankEvidenceRef { gate: CallByNeedPlanEvidenceGate },
}

/// One force admission decision inside a planned thunk execution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallByNeedForceAdmissionRecord {
    pub force_index: usize,
    pub force: CallByNeedForce,
    pub budget_before: CallByNeedBudget,
    pub admission: CallByNeedAdmission,
}

/// Planned M-RHO.2 call-by-need thunk artifact.
///
/// This is the need-specific counterpart to the scalar default-backend plan:
/// it keeps budget admission, validation, and evidence references attached to
/// the executable `ValidatedRhoProgram` so runtime code does not inject a bare
/// shape-validated artifact by accident.
#[derive(Debug, Clone, PartialEq)]
pub struct CallByNeedThunkPlan {
    spec: CallByNeedThunkSpec,
    budget_before: CallByNeedBudget,
    budget_after: CallByNeedBudget,
    force_admissions: Vec<CallByNeedForceAdmissionRecord>,
    validated_program: ValidatedRhoProgram,
    evidence_refs: Vec<String>,
}

impl CallByNeedThunkPlan {
    pub fn spec(&self) -> &CallByNeedThunkSpec {
        &self.spec
    }

    pub fn initial_state(&self) -> CallByNeedInitialState {
        self.spec.initial_state()
    }

    pub fn budget_before(&self) -> CallByNeedBudget {
        self.budget_before
    }

    pub fn budget_after(&self) -> CallByNeedBudget {
        self.budget_after
    }

    pub fn force_admissions(&self) -> &[CallByNeedForceAdmissionRecord] {
        &self.force_admissions
    }

    pub fn program(&self) -> &ValidatedRhoProgram {
        &self.validated_program
    }

    pub fn evidence_refs(&self) -> &[String] {
        &self.evidence_refs
    }
}

/// Rejected call-by-need plan with all diagnostics preserved.
#[derive(Debug, Clone, PartialEq)]
pub struct CallByNeedThunkPlanError {
    pub initial_state: CallByNeedInitialState,
    pub budget_before: CallByNeedBudget,
    pub force_admissions: Box<[CallByNeedForceAdmissionRecord]>,
    pub validation_errors: Box<[RhoValidationError]>,
    pub evidence_diagnostics: Box<[CallByNeedPlanEvidenceDiagnostic]>,
}

/// Build a planned call-by-need thunk artifact after budget admission,
/// generated-shape validation, and evidence-reference checks.
pub fn plan_call_by_need_thunk(
    initial_state: CallByNeedInitialState,
    budget: CallByNeedBudget,
    evidence: CallByNeedPlanEvidence,
) -> Result<CallByNeedThunkPlan, CallByNeedThunkPlanError> {
    plan_call_by_need_thunk_with_spec(
        CallByNeedThunkSpec::default_for(initial_state),
        budget,
        evidence,
    )
}

/// Build a planned call-by-need thunk with generated-language payload and
/// observation-channel parameters.
pub fn plan_call_by_need_thunk_with_spec(
    spec: CallByNeedThunkSpec,
    budget: CallByNeedBudget,
    evidence: CallByNeedPlanEvidence,
) -> Result<CallByNeedThunkPlan, CallByNeedThunkPlanError> {
    let initial_state = spec.initial_state();
    let (force_admissions, budget_after) = admit_force_sequence(initial_state, budget);
    let blocked_by_budget = force_admissions
        .iter()
        .any(|record| !record.admission.is_allowed());
    let validated_program =
        ValidatedRhoProgram::try_from(build_call_by_need_thunk_program_from_spec(spec.clone()));
    let validation_errors = validated_program.clone().err().unwrap_or_default();
    let evidence_diagnostics = evidence.diagnostics();

    if !blocked_by_budget && validation_errors.is_empty() && evidence_diagnostics.is_empty() {
        Ok(CallByNeedThunkPlan {
            spec,
            budget_before: budget,
            budget_after,
            force_admissions,
            validated_program: validated_program
                .expect("empty validation errors require a validated need program"),
            evidence_refs: evidence.accepted_refs(),
        })
    } else {
        Err(CallByNeedThunkPlanError {
            initial_state,
            budget_before: budget,
            force_admissions: force_admissions.into_boxed_slice(),
            validation_errors: validation_errors.into_boxed_slice(),
            evidence_diagnostics: evidence_diagnostics.into_boxed_slice(),
        })
    }
}

fn force_sequence(initial_state: CallByNeedInitialState) -> [CallByNeedForce; 2] {
    match initial_state {
        CallByNeedInitialState::Cold => [CallByNeedForce::MemoMiss, CallByNeedForce::MemoHit],
        CallByNeedInitialState::Hot => [CallByNeedForce::MemoHit, CallByNeedForce::MemoHit],
    }
}

fn admit_force_sequence(
    initial_state: CallByNeedInitialState,
    budget: CallByNeedBudget,
) -> (Vec<CallByNeedForceAdmissionRecord>, CallByNeedBudget) {
    let mut current = budget;
    let mut records = Vec::new();

    for (force_index, force) in force_sequence(initial_state).into_iter().enumerate() {
        let budget_before = current;
        let admission = admit_call_by_need_force(force, current);
        records.push(CallByNeedForceAdmissionRecord {
            force_index,
            force,
            budget_before,
            admission,
        });
        if admission.is_allowed() {
            current = admission.budget_after;
        } else {
            break;
        }
    }

    (records, current)
}

fn diagnose_evidence_refs(
    gate: CallByNeedPlanEvidenceGate,
    refs: &[String],
    diagnostics: &mut Vec<CallByNeedPlanEvidenceDiagnostic>,
) {
    if refs.is_empty() {
        diagnostics.push(CallByNeedPlanEvidenceDiagnostic::MissingEvidenceRefs { gate });
    }
    for evidence_ref in refs {
        if evidence_ref.trim().is_empty() {
            diagnostics.push(CallByNeedPlanEvidenceDiagnostic::BlankEvidenceRef { gate });
        }
    }
}

fn push_evidence_refs(out: &mut BTreeSet<String>, refs: &[String]) {
    for evidence_ref in refs {
        let trimmed = evidence_ref.trim();
        if !trimmed.is_empty() {
            out.insert(trimmed.to_string());
        }
    }
}

/// Normalized AST artifact for the current M-RHO.2 call-by-need thunk slice.
#[derive(Debug, Clone, PartialEq)]
pub struct CallByNeedThunkAst {
    spec: CallByNeedThunkSpec,
    par: Par,
    text_annotation: String,
}

impl CallByNeedThunkAst {
    pub fn spec(&self) -> &CallByNeedThunkSpec {
        &self.spec
    }

    pub fn initial_state(&self) -> CallByNeedInitialState {
        self.spec.initial_state()
    }

    pub fn par(&self) -> &Par {
        &self.par
    }

    /// Reader/debug annotation. This text is not parsed as the execution path.
    pub fn text_annotation(&self) -> &str {
        &self.text_annotation
    }

    /// Convert this AST-first thunk artifact into the generic Rho program
    /// boundary. The resulting `RhoProgram` still carries
    /// `RhoArtifactKind::NormalizedAst`; the validation profile records that it
    /// must satisfy the call-by-need thunk shape rather than the scalar-contract
    /// shape.
    pub fn into_program(self) -> RhoProgram {
        RhoProgram::Ast(RhoAstProgram::new_with_profile(
            self.par,
            self.text_annotation,
            RhoAstValidationProfile::CallByNeedThunk,
        ))
    }
}

/// Build the AST-first call-by-need thunk as a validation-gated Rho program.
///
/// This is the generated-backend boundary for the current M-RHO.2 thunk slice.
/// Tests and runtime helpers should validate this `RhoProgram` before
/// injection instead of executing the raw `Par` returned by
/// [`CallByNeedThunkAst::par`].
pub fn build_call_by_need_thunk_program(initial_state: CallByNeedInitialState) -> RhoProgram {
    build_call_by_need_thunk_program_from_spec(CallByNeedThunkSpec::default_for(initial_state))
}

/// Build a validation-gated Rho program for a parameterized generated-language
/// call-by-need thunk.
pub fn build_call_by_need_thunk_program_from_spec(spec: CallByNeedThunkSpec) -> RhoProgram {
    build_call_by_need_thunk_ast_from_spec(spec).into_program()
}

/// Build the default AST-first call-by-need thunk used by the generic CBN/need
/// runtime oracle.
///
/// This compatibility helper delegates to
/// [`build_call_by_need_thunk_ast_from_spec`] with the sample fixture
/// `value`/`compute`/`OUT`/`EVAL`. The generated process is equivalent to this
/// reader annotation:
///
/// ```text
/// new thunk, state, memo, ret1, ret2 in {
///   state!(initial) |
///   memo!!("value")? |
///   contract thunk(k) = {
///     for (@s <- state) {
///       match s {
///         "cold" => {
///           state!("hot") | memo!!("value") | @"EVAL"!("compute") | k!("value")
///         }
///         "hot" => {
///           state!("hot") | for (@v <<- memo) { k!(v) }
///         }
///       }
///     }
///   } |
///   thunk!(*ret1) |
///   for (@v1 <- ret1) { @"OUT"!(v1) | thunk!(*ret2) } |
///   for (@v2 <- ret2) { @"OUT"!(v2) }
/// }
/// ```
///
/// The function constructs `rhoapi::Par` directly. The annotation above is a
/// readable projection, not a source-text round trip.
pub fn build_call_by_need_thunk_ast(initial_state: CallByNeedInitialState) -> CallByNeedThunkAst {
    build_call_by_need_thunk_ast_from_spec(CallByNeedThunkSpec::default_for(initial_state))
}

/// Build a parameterized AST-first call-by-need thunk.
///
/// The topology matches the verified default thunk exactly; only the
/// generated-language value, evaluation marker, and public observation channels
/// come from [`CallByNeedThunkSpec`].
pub fn build_call_by_need_thunk_ast_from_spec(spec: CallByNeedThunkSpec) -> CallByNeedThunkAst {
    // new thunk, state, memo, ret1, ret2 in ...
    //
    // f1r3node's normalizer indexes new-bound names in reverse syntactic order:
    // thunk=4, state=3, memo=2, ret1=1, ret2=0.
    const THUNK: i32 = 4;
    const STATE: i32 = 3;
    const MEMO: i32 = 2;
    const RET1: i32 = 1;
    const RET2: i32 = 0;

    let mut body = send_name(STATE, vec![string_par(spec.initial_state().token())], false);
    if spec.initial_state() == CallByNeedInitialState::Hot {
        body = body.append(send_name(MEMO, vec![value_par(&spec)], true));
    }
    body = body
        .append(thunk_contract(THUNK, STATE, MEMO, &spec))
        .append(send_name(THUNK, vec![bound_name(RET1)], false))
        .append(first_force_observer(RET1, THUNK, RET2, spec.out_channel()))
        .append(second_force_observer(RET2, spec.out_channel()));

    let par = new_new_par(5, body, Vec::new(), BTreeMap::new(), Vec::new(), Vec::new(), false);
    let value = spec.value().annotation();
    let text_annotation = match spec.initial_state() {
        CallByNeedInitialState::Cold => {
            format!(
                "call-by-need thunk AST: cold initial force computes {marker:?}, memoizes {value}, and second force reads memo on {out:?}",
                marker = spec.eval_marker(),
                value = value,
                out = spec.out_channel(),
            )
        },
        CallByNeedInitialState::Hot => {
            format!(
                "call-by-need thunk AST: hot initial force reads existing memo {value} on {out:?} without compute marker {marker:?}",
                value = value,
                out = spec.out_channel(),
                marker = spec.eval_marker(),
            )
        },
    };

    CallByNeedThunkAst { spec, par, text_annotation }
}

fn thunk_contract(thunk: i32, state: i32, memo: i32, spec: &CallByNeedThunkSpec) -> Par {
    let source = bound_name(thunk);
    let body = state_receive(state, memo, spec);
    let locally_free =
        union(source.locally_free.clone(), filter_and_adjust_bitset(&body.locally_free, 1));
    let receive = Receive {
        binds: vec![ReceiveBind {
            patterns: vec![new_freevar_par(0, Vec::new())],
            source: Some(source),
            remainder: None,
            free_count: 1,
        }],
        body: Some(body),
        persistent: true,
        peek: false,
        bind_count: 1,
        locally_free: locally_free.clone(),
        connective_used: false,
        condition: None,
    };
    new_receive_par(
        receive.binds,
        receive.body.expect("body was constructed above"),
        receive.persistent,
        receive.peek,
        receive.bind_count,
        receive.locally_free,
        receive.connective_used,
        locally_free,
        false,
    )
}

fn state_receive(state: i32, memo: i32, spec: &CallByNeedThunkSpec) -> Par {
    let cold = cold_branch(state + 2, memo + 2, spec);
    let hot = hot_branch(state + 2, memo + 2);
    let target = bound_value(0);
    let match_locally_free = locally_free_union([&target, &cold, &hot]);
    let body = new_match_par(
        target,
        vec![
            MatchCase {
                pattern: Some(string_par("cold")),
                source: Some(cold),
                free_count: 0,
                guard: None,
            },
            MatchCase {
                pattern: Some(string_par("hot")),
                source: Some(hot),
                free_count: 0,
                guard: None,
            },
        ],
        match_locally_free.clone(),
        false,
        match_locally_free,
        false,
    );

    receive_one_from_par(bound_name(state + 1), body, false)
}

fn cold_branch(state: i32, memo: i32, spec: &CallByNeedThunkSpec) -> Par {
    // Inside the state receive body, BoundVar(1) is the thunk return channel k
    // and BoundVar(0) is the matched state token.
    send_name(state, vec![string_par("hot")], false)
        .append(send_name(memo, vec![value_par(spec)], true))
        .append(send_text_channel(
            spec.eval_channel(),
            vec![string_par(spec.eval_marker())],
            false,
        ))
        .append(new_send_par(
            bound_value(1),
            vec![value_par(spec)],
            false,
            bitvec(&[1]),
            false,
            bitvec(&[1]),
            false,
        ))
}

fn hot_branch(state: i32, memo: i32) -> Par {
    // The nested memo peek introduces v at BoundVar(0), shifting k to
    // BoundVar(2). The persistent memo cell is read without consumption.
    let memo_body = new_send_par(
        bound_value(2),
        vec![bound_value(0)],
        false,
        bitvec(&[0, 2]),
        false,
        bitvec(&[0, 2]),
        false,
    );
    let memo_receive = receive_one_from_par(bound_name(memo), memo_body, true);

    send_name(state, vec![string_par("hot")], false).append(memo_receive)
}

fn first_force_observer(ret1: i32, thunk: i32, ret2: i32, out_channel: &str) -> Par {
    let body = send_text_channel(out_channel, vec![bound_value(0)], false).append(send_name(
        thunk + 1,
        vec![bound_name(ret2 + 1)],
        false,
    ));
    receive_one(ret1, body)
}

fn second_force_observer(ret2: i32, out_channel: &str) -> Par {
    let body = send_text_channel(out_channel, vec![bound_value(0)], false);
    receive_one(ret2, body)
}

fn receive_one(source: i32, body: Par) -> Par {
    receive_one_from_par(bound_name(source), body, false)
}

fn receive_one_from_par(source: Par, body: Par, peek: bool) -> Par {
    let locally_free =
        union(source.locally_free.clone(), filter_and_adjust_bitset(&body.locally_free, 1));
    new_receive_par(
        vec![ReceiveBind {
            patterns: vec![new_freevar_par(0, Vec::new())],
            source: Some(source),
            remainder: None,
            free_count: 1,
        }],
        body,
        false,
        peek,
        1,
        locally_free.clone(),
        false,
        locally_free,
        false,
    )
}

fn send_name(channel: i32, data: Vec<Par>, persistent: bool) -> Par {
    let locally_free = data
        .iter()
        .fold(bitvec(&[channel as usize]), |acc, item| union(acc, item.locally_free.clone()));
    new_send_par(
        bound_name(channel),
        data,
        persistent,
        locally_free.clone(),
        false,
        locally_free,
        false,
    )
}

fn send_text_channel(channel: &str, data: Vec<Par>, persistent: bool) -> Par {
    let locally_free = data
        .iter()
        .fold(Vec::new(), |acc, item| union(acc, item.locally_free.clone()));
    new_send_par(
        new_gstring_par(channel.to_string(), Vec::new(), false),
        data,
        persistent,
        locally_free.clone(),
        false,
        locally_free,
        false,
    )
}

fn bound_name(index: i32) -> Par {
    new_boundvar_par(index, bitvec(&[index as usize]), false)
}

fn bound_value(index: i32) -> Par {
    new_boundvar_par(index, bitvec(&[index as usize]), false)
}

fn string_par(value: &str) -> Par {
    new_gstring_par(value.to_string(), Vec::new(), false)
}

fn value_par(spec: &CallByNeedThunkSpec) -> Par {
    spec.value()
        .try_to_par()
        .expect("CallByNeedThunkSpec validation guarantees a closed Rho value payload")
}

fn locally_free_union<'a>(parts: impl IntoIterator<Item = &'a Par>) -> Vec<u8> {
    parts
        .into_iter()
        .fold(Vec::new(), |acc, part| union(acc, part.locally_free.clone()))
}

fn filter_and_adjust_bitset(bitset: &[u8], bind_count: usize) -> Vec<u8> {
    let adjusted = bitset
        .iter()
        .enumerate()
        .flat_map(|(byte_index, byte)| {
            (0..8).filter_map(move |bit| {
                if byte & (1 << bit) == 0 {
                    None
                } else {
                    Some(byte_index * 8 + bit)
                }
            })
        })
        .filter_map(|index| index.checked_sub(bind_count))
        .collect::<Vec<_>>();
    bitvec(&adjusted)
}

fn bitvec(indices: &[usize]) -> Vec<u8> {
    let Some(max_index) = indices.iter().copied().max() else {
        return Vec::new();
    };
    let mut bytes = vec![0_u8; (max_index / 8) + 1];
    for index in indices {
        bytes[index / 8] |= 1 << (index % 8);
    }
    bytes
}

#[cfg(test)]
mod tests {
    use super::*;
    use models::rhoapi::expr::ExprInstance;

    fn passing_evidence() -> CallByNeedPlanEvidence {
        CallByNeedPlanEvidence {
            proof_evidence_refs: vec![
                "formal/rocq/rho_bridge/theories/RhoCallByNeedObservation.v".into()
            ],
            runtime_oracle_evidence_refs: vec![
                "mettail-rho-runtime/tests/rho_call_by_need.rs".into()
            ],
            budget_evidence_refs: vec![
                "formal/rocq/rho_bridge/theories/RhoCallByNeedBudget.v".into()
            ],
        }
    }

    #[test]
    fn memo_hit_consumes_lookahead_but_not_heap() {
        let admission =
            admit_call_by_need_force(CallByNeedForce::MemoHit, CallByNeedBudget::new(3, 2));

        assert!(admission.is_allowed());
        assert_eq!(admission.budget_after, CallByNeedBudget::new(2, 2));
    }

    #[test]
    fn memo_miss_consumes_lookahead_and_one_heap_cell() {
        let admission =
            admit_call_by_need_force(CallByNeedForce::MemoMiss, CallByNeedBudget::new(3, 2));

        assert!(admission.is_allowed());
        assert_eq!(admission.budget_after, CallByNeedBudget::new(2, 1));
    }

    #[test]
    fn zero_lookahead_blocks_before_heap_accounting() {
        let budget = CallByNeedBudget::new(0, 0);
        let admission = admit_call_by_need_force(CallByNeedForce::MemoMiss, budget);

        assert!(!admission.is_allowed());
        assert_eq!(admission.blocker, Some(CallByNeedBudgetBlocker::LookaheadExceeded));
        assert_eq!(admission.budget_after, budget);
    }

    #[test]
    fn cold_force_without_heap_budget_blocks_without_consuming_lookahead() {
        let budget = CallByNeedBudget::new(4, 0);
        let admission = admit_call_by_need_force(CallByNeedForce::MemoMiss, budget);

        assert!(!admission.is_allowed());
        assert_eq!(admission.blocker, Some(CallByNeedBudgetBlocker::HeapBudgetExceeded));
        assert_eq!(admission.budget_after, budget);
    }

    #[test]
    fn call_by_need_thunk_builder_emits_normalized_ast_without_source_text() {
        let program = build_call_by_need_thunk_ast(CallByNeedInitialState::Cold);

        assert_eq!(program.initial_state(), CallByNeedInitialState::Cold);
        assert!(program.text_annotation().contains("call-by-need thunk AST"));
        assert!(program.par().sends.is_empty());
        assert_eq!(program.par().news.len(), 1);

        let new_body = program.par().news[0]
            .p
            .as_ref()
            .expect("new body should be present");
        assert_eq!(new_body.receives.len(), 3);
        assert_eq!(new_body.sends.len(), 2);

        let state_send = &new_body.sends[0];
        assert!(!state_send.persistent);
        assert_eq!(gstring(&state_send.data[0]), Some("cold"));
    }

    #[test]
    fn hot_thunk_builder_installs_persistent_memo_seed() {
        let program = build_call_by_need_thunk_ast(CallByNeedInitialState::Hot);
        let new_body = program.par().news[0]
            .p
            .as_ref()
            .expect("new body should be present");

        assert_eq!(new_body.sends.len(), 3);
        assert_eq!(gstring(&new_body.sends[0].data[0]), Some("hot"));
        assert!(new_body.sends[1].persistent, "hot state must seed the memo persistently");
        assert_eq!(gstring(&new_body.sends[1].data[0]), Some("value"));
    }

    #[test]
    fn parameterized_thunk_builder_uses_generated_payload_and_channels() {
        let spec = CallByNeedThunkSpec::new(
            CallByNeedInitialState::Hot,
            RhoAstLiteral::Int(42),
            "calculator-add",
            "RESULT",
            "TRACE",
        )
        .expect("parameterized spec is valid");
        let program = build_call_by_need_thunk_ast_from_spec(spec.clone());
        let new_body = program.par().news[0]
            .p
            .as_ref()
            .expect("new body should be present");

        assert_eq!(program.spec(), &spec);
        assert!(matches!(only_expr(&new_body.sends[1].data[0]), ExprInstance::GInt(42)));
        assert!(
            program.text_annotation().contains("calculator-add"),
            "reader annotation should preserve the generated eval marker"
        );
        assert!(
            program.text_annotation().contains("42"),
            "reader annotation should preserve the generated value for diagnostics"
        );
    }

    #[test]
    fn thunk_spec_rejects_empty_or_ambiguous_observation_parameters() {
        assert_eq!(
            CallByNeedThunkSpec::new(
                CallByNeedInitialState::Cold,
                RhoAstLiteral::String("value".to_string()),
                "",
                "OUT",
                "EVAL",
            ),
            Err(CallByNeedThunkSpecError::EmptyEvalMarker)
        );
        assert_eq!(
            CallByNeedThunkSpec::new(
                CallByNeedInitialState::Cold,
                RhoAstLiteral::String("value".to_string()),
                "compute",
                "",
                "EVAL",
            ),
            Err(CallByNeedThunkSpecError::EmptyOutputChannel)
        );
        assert_eq!(
            CallByNeedThunkSpec::new(
                CallByNeedInitialState::Cold,
                RhoAstLiteral::String("value".to_string()),
                "compute",
                "OUT",
                "",
            ),
            Err(CallByNeedThunkSpecError::EmptyEvalChannel)
        );
        assert_eq!(
            CallByNeedThunkSpec::new(
                CallByNeedInitialState::Cold,
                RhoAstLiteral::String("value".to_string()),
                "compute",
                "OUT",
                "OUT",
            ),
            Err(CallByNeedThunkSpecError::ObservationChannelsMustDiffer)
        );
    }

    #[test]
    fn planned_cold_thunk_records_budget_validation_and_evidence() {
        let plan = plan_call_by_need_thunk(
            CallByNeedInitialState::Cold,
            CallByNeedBudget::new(2, 1),
            passing_evidence(),
        )
        .expect("cold thunk has enough lookahead and heap budget");

        assert_eq!(plan.initial_state(), CallByNeedInitialState::Cold);
        assert_eq!(plan.spec(), &CallByNeedThunkSpec::default_for(CallByNeedInitialState::Cold));
        assert_eq!(plan.budget_before(), CallByNeedBudget::new(2, 1));
        assert_eq!(plan.budget_after(), CallByNeedBudget::new(0, 0));
        assert_eq!(plan.force_admissions().len(), 2);
        assert_eq!(plan.force_admissions()[0].force, CallByNeedForce::MemoMiss);
        assert_eq!(plan.force_admissions()[1].force, CallByNeedForce::MemoHit);
        assert!(!plan.evidence_refs().is_empty());
        assert_eq!(plan.program().artifact_kind(), crate::lower::RhoArtifactKind::NormalizedAst);
    }

    #[test]
    fn planned_parameterized_thunk_preserves_spec() {
        let spec = CallByNeedThunkSpec::new(
            CallByNeedInitialState::Cold,
            RhoAstLiteral::String("forty-two".to_string()),
            "eval-add",
            "RESULT",
            "TRACE",
        )
        .expect("parameterized spec is valid");
        let plan = plan_call_by_need_thunk_with_spec(
            spec.clone(),
            CallByNeedBudget::new(2, 1),
            passing_evidence(),
        )
        .expect("parameterized cold thunk has enough budget");

        assert_eq!(plan.spec(), &spec);
        assert!(plan.program().text_annotation().contains("forty-two"));
    }

    #[test]
    fn planned_hot_thunk_does_not_require_heap_budget() {
        let plan = plan_call_by_need_thunk(
            CallByNeedInitialState::Hot,
            CallByNeedBudget::new(2, 0),
            passing_evidence(),
        )
        .expect("hot thunk forces are memo hits");

        assert_eq!(plan.budget_after(), CallByNeedBudget::new(0, 0));
        assert_eq!(plan.force_admissions()[0].force, CallByNeedForce::MemoHit);
        assert_eq!(plan.force_admissions()[1].force, CallByNeedForce::MemoHit);
    }

    #[test]
    fn planned_cold_thunk_rejects_insufficient_heap_budget() {
        let err = plan_call_by_need_thunk(
            CallByNeedInitialState::Cold,
            CallByNeedBudget::new(2, 0),
            passing_evidence(),
        )
        .expect_err("cold thunk must allocate one memo cell");

        assert!(err.validation_errors.is_empty());
        assert!(err.evidence_diagnostics.is_empty());
        assert_eq!(err.force_admissions.len(), 1);
        assert_eq!(
            err.force_admissions[0].admission.blocker,
            Some(CallByNeedBudgetBlocker::HeapBudgetExceeded)
        );
    }

    #[test]
    fn planned_thunk_rejects_missing_evidence_refs() {
        let err = plan_call_by_need_thunk(
            CallByNeedInitialState::Hot,
            CallByNeedBudget::new(2, 0),
            CallByNeedPlanEvidence {
                proof_evidence_refs: Vec::new(),
                runtime_oracle_evidence_refs: vec![" ".into()],
                budget_evidence_refs: Vec::new(),
            },
        )
        .expect_err("planned need execution requires evidence references");

        assert!(err.validation_errors.is_empty());
        assert_eq!(
            err.evidence_diagnostics.as_ref(),
            [
                CallByNeedPlanEvidenceDiagnostic::MissingEvidenceRefs {
                    gate: CallByNeedPlanEvidenceGate::Proof,
                },
                CallByNeedPlanEvidenceDiagnostic::BlankEvidenceRef {
                    gate: CallByNeedPlanEvidenceGate::RuntimeOracle,
                },
                CallByNeedPlanEvidenceDiagnostic::MissingEvidenceRefs {
                    gate: CallByNeedPlanEvidenceGate::Budget,
                },
            ]
        );
    }

    fn gstring(par: &Par) -> Option<&str> {
        let [expr] = par.exprs.as_slice() else {
            return None;
        };
        match expr.expr_instance.as_ref()? {
            ExprInstance::GString(value) => Some(value),
            _ => None,
        }
    }

    fn only_expr(par: &Par) -> &ExprInstance {
        let [expr] = par.exprs.as_slice() else {
            panic!("expected exactly one expression");
        };
        expr.expr_instance
            .as_ref()
            .expect("expected expression payload")
    }
}
