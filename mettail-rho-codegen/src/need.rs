//! Call-by-need budget admission for generic Rho lowering.
//!
//! The generic CBN/need path represents non-native computations as thunks.
//! This module is the compile-time/runtime-planning contract for bounded force
//! admission: every force consumes one lookahead step, and a cold force that
//! must allocate a memo cell also consumes one heap cell.

use std::collections::BTreeMap;

use models::rhoapi::{MatchCase, Par, Receive, ReceiveBind};
use models::rust::utils::{
    new_boundvar_par, new_freevar_par, new_gstring_par, new_match_par, new_new_par,
    new_receive_par, new_send_par, union,
};

use crate::lower::{RhoAstProgram, RhoAstValidationProfile, RhoProgram};

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

/// Normalized AST artifact for the current M-RHO.2 call-by-need thunk slice.
#[derive(Debug, Clone, PartialEq)]
pub struct CallByNeedThunkAst {
    initial_state: CallByNeedInitialState,
    par: Par,
    text_annotation: String,
}

impl CallByNeedThunkAst {
    pub fn initial_state(&self) -> CallByNeedInitialState {
        self.initial_state
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
    build_call_by_need_thunk_ast(initial_state).into_program()
}

/// Build the AST-first call-by-need thunk used by the generic CBN/need runtime
/// oracle.
///
/// The generated process is equivalent to this reader annotation:
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
/// The function constructs `rhoapi::Par` directly. The annotation above is not
/// a source-text round trip.
pub fn build_call_by_need_thunk_ast(initial_state: CallByNeedInitialState) -> CallByNeedThunkAst {
    // new thunk, state, memo, ret1, ret2 in ...
    //
    // f1r3node's normalizer indexes new-bound names in reverse syntactic order:
    // thunk=4, state=3, memo=2, ret1=1, ret2=0.
    const THUNK: i32 = 4;
    const STATE: i32 = 3;
    const MEMO: i32 = 2;
    const RET1: i32 = 1;
    const RET2: i32 = 0;

    let mut body = send_name(STATE, vec![string_par(initial_state.token())], false);
    if initial_state == CallByNeedInitialState::Hot {
        body = body.append(send_name(MEMO, vec![string_par("value")], true));
    }
    body = body
        .append(thunk_contract(THUNK, STATE, MEMO))
        .append(send_name(THUNK, vec![bound_name(RET1)], false))
        .append(first_force_observer(RET1, THUNK, RET2))
        .append(second_force_observer(RET2));

    let par = new_new_par(5, body, Vec::new(), BTreeMap::new(), Vec::new(), Vec::new(), false);
    let text_annotation = match initial_state {
        CallByNeedInitialState::Cold => {
            "call-by-need thunk AST: cold initial force computes once, memoizes, and second force reads memo"
        },
        CallByNeedInitialState::Hot => {
            "call-by-need thunk AST: hot initial force reads existing memo without compute marker"
        },
    }
    .to_string();

    CallByNeedThunkAst { initial_state, par, text_annotation }
}

fn thunk_contract(thunk: i32, state: i32, memo: i32) -> Par {
    let source = bound_name(thunk);
    let body = state_receive(state, memo);
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

fn state_receive(state: i32, memo: i32) -> Par {
    let cold = cold_branch(state + 2, memo + 2);
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

fn cold_branch(state: i32, memo: i32) -> Par {
    // Inside the state receive body, BoundVar(1) is the thunk return channel k
    // and BoundVar(0) is the matched state token.
    send_name(state, vec![string_par("hot")], false)
        .append(send_name(memo, vec![string_par("value")], true))
        .append(send_text_channel("EVAL", vec![string_par("compute")], false))
        .append(new_send_par(
            bound_value(1),
            vec![string_par("value")],
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

fn first_force_observer(ret1: i32, thunk: i32, ret2: i32) -> Par {
    let body = send_text_channel("OUT", vec![bound_value(0)], false).append(send_name(
        thunk + 1,
        vec![bound_name(ret2 + 1)],
        false,
    ));
    receive_one(ret1, body)
}

fn second_force_observer(ret2: i32) -> Par {
    let body = send_text_channel("OUT", vec![bound_value(0)], false);
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

    fn gstring(par: &Par) -> Option<&str> {
        let [expr] = par.exprs.as_slice() else {
            return None;
        };
        match expr.expr_instance.as_ref()? {
            ExprInstance::GString(value) => Some(value),
            _ => None,
        }
    }
}
