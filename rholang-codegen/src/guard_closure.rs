//! Guard **closedness** — the two structural predicates that decide whether a lowered
//! `Receive.condition` (or `MatchCase.guard`) could possibly be decided at compile time.
//!
//! Both predicates are pure, total functions of a `models::rhoapi::Par`. They contain no
//! judgement about *where* a guard is evaluated — that is routing, and routing is decided
//! exactly once per guard by the lowering (see [`crate::guard_closure`]'s companion,
//! `mettail_rholang_runtime::guard_discharge`, and the ROUTE-SITE INVARIANT recorded there).
//!
//! # Why this lives in `rholang-codegen` and not next to the discharge decision
//!
//! The discharge decision itself (`guard_discharge::classify`) needs `rho-pure-eval` and the
//! reducer's `SpatialMatcherOracle`, so it lives in `rholang-runtime`. But the *closedness*
//! half needs nothing but `models`, and three guard-**constructing** sites in THIS crate —
//! [`crate::rho_net_flt::flt_receive_par`], [`crate::rho_net_lower`]'s
//! `ac_nonlinear_condition` and `nonlinear_consistency_condition` — must be able to assert
//! that what they build is *never* dischargeable. The crate graph is one-way
//! (`rholang-runtime` → `rholang-codegen`), so the predicate has to live at the bottom or be
//! duplicated. One home, no duplication: it lives here and `guard_discharge` re-exports it.
//!
//! # D0 — the binder-closed guard
//!
//! [`is_binder_closed`] answers: *does this condition mention any variable at all?*
//!
//! It is the whole soundness argument for compile-time guard discharge. `rho-pure-eval`'s
//! evaluator (`rho_pure_eval::eval_with`) reads its `Env` at exactly one place —
//! `resolve_var`, reached only from the `ExprInstance::EVarBody` arm. `VarRefBody` is a
//! *connective*, and connectives are copied through unevaluated (so a condition carrying one
//! can never extract to a boolean). Therefore:
//!
//! > if `is_binder_closed(φ)` then `eval_with(φ, env, oracle)` yields the same result for
//! > **every** `env` — in particular for the empty `Env` the compiler has and for the
//! > binder-populated `Env` the matcher builds at COMM time.
//!
//! The compile-time call is then *the same function on the same input* as the runtime call.
//! No model, no abstraction, no gap. (Mechanized as `T-GD-5 env_independence_of_closed_conditions`
//! in `formal/rocq/rho_bridge/theories/GuardDischargeSoundness.v`.)
//!
//! # Fail-closed by construction
//!
//! The walk is **total** and has **no wildcard-true arm**. Every `rhoapi` node kind that can
//! carry a variable is enumerated explicitly; the residual `_ => false` arms mean a node kind
//! this module has never been taught about is *not* closed. A new `rhoapi` constructor can
//! therefore only ever make the predicate *more* conservative, never silently license a
//! discharge — pinned by `a_new_rhoapi_constructor_cannot_silently_become_closed`.
//!
//! # Ground operands (the substrate-routing boundary)
//!
//! [`all_operands_ground`] is the second, independent conjunct required before a guard may be
//! folded at compile time: *every operand of every node is a value already settled at lowering
//! time.* For a binder-closed D0 guard this is entailed — there are no operands left to route
//! — but the boundary is **checked, not assumed**, so that when the Dovetail/SFT wiring plan
//! introduces substrate-routed (`S`) nodes, a node whose operands are not ground cannot drift
//! into the dischargeable set. `is_binder_closed ⇒ all_operands_ground` is pinned by
//! `binder_closed_implies_operands_ground`; the converse does not hold (a `Send` carrying only
//! literals is closed of variables but is not a settled operand).

use models::rhoapi::connective::ConnectiveInstance;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::var::VarInstance;
use models::rhoapi::{
    Bundle, Connective, EAnd, EDiv, EEq, EList, EMap, EMatches, EMethod, EMinus, EMinusMinus, EMod,
    EMult, ENeg, ENeq, ENot, EOr, EPercentPercent, EPlus, EPlusPlus, ESet, ETuple, EVar, Expr, ELt,
    ELte, EGt, EGte, GUnforgeable, If, KeyValuePair, Match, MatchCase, New, Par, Receive,
    ReceiveBind, Send, Var,
};

// ════════════════════════════════════════════════════════════════════════════════════════════
// D0 — binder-closedness
// ════════════════════════════════════════════════════════════════════════════════════════════

/// `true` iff `par` mentions **no variable anywhere** — no `EVarBody` (bound, free or
/// wildcard), no `VarRefBody` connective, and no collection/bind `remainder` binder.
///
/// This is the D0 predicate: the sound class for compile-time guard discharge. See the module
/// docs for the soundness argument and the fail-closed discipline.
///
/// The walk recurses into **every** `Par` slot, including the process slots
/// (`sends`/`receives`/`news`/`matches`/`bundles`/`conditionals`), because a `Par` can be
/// nested inside an expression (an `EMatches` target, an `EList` element, …). Process slots
/// can never appear in a *dischargeable* condition — `rho_pure_eval` copies them through
/// unevaluated, so the condition cannot extract to a boolean — but that refusal is
/// `machine_verdict`'s job, not this predicate's; keeping the two orthogonal is what lets a
/// caller ask "does this mention a variable?" without also asking "does this evaluate?".
pub fn is_binder_closed(par: &Par) -> bool {
    par.sends.iter().all(send_is_binder_closed)
        && par.receives.iter().all(receive_is_binder_closed)
        && par.news.iter().all(new_is_binder_closed)
        && par.matches.iter().all(match_is_binder_closed)
        && par.bundles.iter().all(bundle_is_binder_closed)
        && par.conditionals.iter().all(if_is_binder_closed)
        && par.unforgeables.iter().all(unforgeable_is_binder_closed)
        && par.connectives.iter().all(connective_is_binder_closed)
        && par.exprs.iter().all(expr_is_binder_closed)
}

fn opt_par_is_binder_closed(par: Option<&Par>) -> bool {
    // A missing required sub-`Par` is malformed input; fail CLOSED.
    match par {
        Some(inner) => is_binder_closed(inner),
        None => false,
    }
}

fn send_is_binder_closed(send: &Send) -> bool {
    let Send { chan, data, persistent: _, locally_free: _, connective_used: _ } = send;
    opt_par_is_binder_closed(chan.as_ref()) && data.iter().all(is_binder_closed)
}

fn receive_is_binder_closed(receive: &Receive) -> bool {
    let Receive {
        binds,
        body,
        persistent: _,
        peek: _,
        bind_count: _,
        locally_free: _,
        connective_used: _,
        condition,
    } = receive;
    // A receive BINDS: its `free_count` binders are exactly the variables its body and its own
    // guard may mention. A receive nested inside a guard is therefore never binder-closed in
    // the sense this predicate certifies (the sub-condition's `BoundVar`s resolve against a
    // frame that does not exist at lowering time), unless it binds nothing at all.
    binds.iter().all(receive_bind_is_binder_closed)
        && opt_par_is_binder_closed(body.as_ref())
        && match condition {
            Some(cond) => is_binder_closed(cond),
            None => true,
        }
}

fn receive_bind_is_binder_closed(bind: &ReceiveBind) -> bool {
    let ReceiveBind { patterns, source, remainder, free_count } = bind;
    *free_count == 0
        && remainder.is_none()
        && patterns.iter().all(is_binder_closed)
        && opt_par_is_binder_closed(source.as_ref())
}

fn new_is_binder_closed(new: &New) -> bool {
    let New { bind_count, p, uri: _, injections, locally_free: _ } = new;
    // `new` introduces `bind_count` fresh UNFORGEABLE names whose identity is determined by
    // the deploy's random state at run time, not at lowering time. A non-trivial `new` is
    // therefore never closed. `injections` binds URI-referenced system values supplied by the
    // node at deploy time — likewise not lowering-time constants.
    *bind_count == 0 && injections.is_empty() && opt_par_is_binder_closed(p.as_ref())
}

fn match_is_binder_closed(m: &Match) -> bool {
    let Match { target, cases, locally_free: _, connective_used: _ } = m;
    opt_par_is_binder_closed(target.as_ref()) && cases.iter().all(match_case_is_binder_closed)
}

fn match_case_is_binder_closed(case: &MatchCase) -> bool {
    let MatchCase { pattern, source, free_count, guard } = case;
    *free_count == 0
        && opt_par_is_binder_closed(pattern.as_ref())
        && opt_par_is_binder_closed(source.as_ref())
        && match guard {
            Some(g) => is_binder_closed(g),
            None => true,
        }
}

fn bundle_is_binder_closed(bundle: &Bundle) -> bool {
    let Bundle { body, write_flag: _, read_flag: _ } = bundle;
    opt_par_is_binder_closed(body.as_ref())
}

fn if_is_binder_closed(conditional: &If) -> bool {
    let If { condition, if_true, if_false, locally_free: _, connective_used: _ } = conditional;
    opt_par_is_binder_closed(condition.as_ref())
        && opt_par_is_binder_closed(if_true.as_ref())
        && opt_par_is_binder_closed(if_false.as_ref())
}

/// An unforgeable name (`GPrivate`, `GDeployId`, `GDeployerId`, `GSysAuthToken`) is a run-time
/// identity, not a lowering-time constant, so it is never closed. Enumerated as a named case
/// rather than folded into a `_` arm so the refusal is deliberate and greppable.
fn unforgeable_is_binder_closed(_unforgeable: &GUnforgeable) -> bool {
    false
}

fn connective_is_binder_closed(connective: &Connective) -> bool {
    match connective.connective_instance.as_ref() {
        // `~x` / `x /\ y` / `x \/ y` over closed bodies mention no variable.
        Some(ConnectiveInstance::ConnNotBody(body)) => is_binder_closed(body),
        Some(ConnectiveInstance::ConnAndBody(body)) | Some(ConnectiveInstance::ConnOrBody(body)) => {
            body.ps.iter().all(is_binder_closed)
        },
        // `=x` — a VARIABLE reference by construction. The whole point of D0.
        Some(ConnectiveInstance::VarRefBody(_)) => false,
        // Type connectives (`Bool`, `Int`, `String`, `Uri`, `ByteArray`) mention no variable.
        Some(ConnectiveInstance::ConnBool(_))
        | Some(ConnectiveInstance::ConnInt(_))
        | Some(ConnectiveInstance::ConnString(_))
        | Some(ConnectiveInstance::ConnUri(_))
        | Some(ConnectiveInstance::ConnByteArray(_)) => true,
        // Malformed, or a constructor this module has never been taught about: fail CLOSED.
        None => false,
    }
}

fn var_is_binder_closed(var: &Var) -> bool {
    // Every `Var` instance IS a variable mention — `BoundVar` resolves against the run-time
    // env, `FreeVar` against a match frame, `Wildcard` is a binder that swallows anything.
    // Enumerated exhaustively (no `_` arm) so a new `VarInstance` breaks the build here.
    match var.var_instance.as_ref() {
        Some(VarInstance::BoundVar(_))
        | Some(VarInstance::FreeVar(_))
        | Some(VarInstance::Wildcard(_))
        | None => false,
    }
}

fn expr_is_binder_closed(expr: &Expr) -> bool {
    let Some(instance) = expr.expr_instance.as_ref() else {
        return false; // malformed: fail CLOSED
    };
    match instance {
        // ── Ground literals: no variable, by definition. ────────────────────────────────────
        ExprInstance::GBool(_)
        | ExprInstance::GInt(_)
        | ExprInstance::GString(_)
        | ExprInstance::GUri(_)
        | ExprInstance::GByteArray(_)
        | ExprInstance::GDouble(_)
        | ExprInstance::GBigInt(_)
        | ExprInstance::GBigRat(_)
        | ExprInstance::GFixedPoint(_) => true,

        // ── THE variable node. ──────────────────────────────────────────────────────────────
        ExprInstance::EVarBody(EVar { v }) => match v {
            Some(var) => var_is_binder_closed(var),
            None => false,
        },

        // ── Unary operators. ────────────────────────────────────────────────────────────────
        ExprInstance::ENotBody(ENot { p }) | ExprInstance::ENegBody(ENeg { p }) => {
            opt_par_is_binder_closed(p.as_ref())
        },

        // ── Binary operators (arithmetic, comparison, logic, string/collection). ────────────
        ExprInstance::EMultBody(EMult { p1, p2 })
        | ExprInstance::EDivBody(EDiv { p1, p2 })
        | ExprInstance::EModBody(EMod { p1, p2 })
        | ExprInstance::EPlusBody(EPlus { p1, p2 })
        | ExprInstance::EMinusBody(EMinus { p1, p2 })
        | ExprInstance::ELtBody(ELt { p1, p2 })
        | ExprInstance::ELteBody(ELte { p1, p2 })
        | ExprInstance::EGtBody(EGt { p1, p2 })
        | ExprInstance::EGteBody(EGte { p1, p2 })
        | ExprInstance::EEqBody(EEq { p1, p2 })
        | ExprInstance::ENeqBody(ENeq { p1, p2 })
        | ExprInstance::EAndBody(EAnd { p1, p2 })
        | ExprInstance::EOrBody(EOr { p1, p2 })
        | ExprInstance::EPercentPercentBody(EPercentPercent { p1, p2 })
        | ExprInstance::EPlusPlusBody(EPlusPlus { p1, p2 })
        | ExprInstance::EMinusMinusBody(EMinusMinus { p1, p2 }) => {
            opt_par_is_binder_closed(p1.as_ref()) && opt_par_is_binder_closed(p2.as_ref())
        },

        // ── Collections. A `remainder` is a BINDER (`xs` in `[1, 2 ... xs]`). ───────────────
        ExprInstance::EListBody(EList { ps, remainder, locally_free: _, connective_used: _ })
        | ExprInstance::ESetBody(ESet { ps, remainder, locally_free: _, connective_used: _ }) => {
            remainder.is_none() && ps.iter().all(is_binder_closed)
        },
        ExprInstance::ETupleBody(ETuple { ps, locally_free: _, connective_used: _ }) => {
            ps.iter().all(is_binder_closed)
        },
        ExprInstance::EMapBody(EMap { kvs, remainder, locally_free: _, connective_used: _ }) => {
            remainder.is_none() && kvs.iter().all(key_value_pair_is_binder_closed)
        },

        // ── Method dispatch. ────────────────────────────────────────────────────────────────
        ExprInstance::EMethodBody(EMethod {
            method_name: _,
            target,
            arguments,
            locally_free: _,
            connective_used: _,
        }) => opt_par_is_binder_closed(target.as_ref()) && arguments.iter().all(is_binder_closed),

        // ── The spatial satisfaction operator. Both sides walked: the PATTERN is passed to
        //    the matcher verbatim (never evaluated, so its variables never read the env), but
        //    a pattern with binders is not a lowering-time constant either, so the
        //    conservative answer is the right one. ───────────────────────────────────────────
        ExprInstance::EMatchesBody(EMatches { target, pattern }) => {
            opt_par_is_binder_closed(target.as_ref()) && opt_par_is_binder_closed(pattern.as_ref())
        },

        // ── Structures whose closedness this module has never been taught to decide.
        //    NOT a wildcard arm: each is named, so adding a new `ExprInstance` variant is a
        //    compile error here rather than a silent `true`. ─────────────────────────────────
        ExprInstance::EPathmapBody(_) | ExprInstance::EZipperBody(_) => false,
    }
}

fn key_value_pair_is_binder_closed(kv: &KeyValuePair) -> bool {
    let KeyValuePair { key, value } = kv;
    opt_par_is_binder_closed(key.as_ref()) && opt_par_is_binder_closed(value.as_ref())
}

// ════════════════════════════════════════════════════════════════════════════════════════════
// The substrate-routing boundary — ground operands
// ════════════════════════════════════════════════════════════════════════════════════════════

/// `true` iff every operand reachable in `par` is a **value already settled at lowering time**:
/// a ground literal, a collection of such, or an operator over such.
///
/// This is the explicit form of the Dovetail/SFT wiring plan's constraint that a
/// substrate-routed (`S`) node may be folded at compile time **only if its operands are ground
/// at lowering time**. For a D0 (binder-closed) condition the constraint is entailed, but
/// `guard_discharge::classify` requires it as an *independent conjunct* so the boundary is
/// checked rather than assumed: when `S` nodes arrive, a node whose operands are not ground
/// cannot drift into the dischargeable set by riding on D0's definition.
///
/// Distinct from [`is_binder_closed`] in both directions of intent:
/// * closedness asks "does this mention a variable?" — a `Send` of literals is *closed*;
/// * groundness asks "is this a settled value?" — a `Send` of literals is *not* an operand,
///   so it is not ground.
pub fn all_operands_ground(par: &Par) -> bool {
    // A settled operand is a pure VALUE: no process slots at all (a send/receive/new/match/
    // bundle/conditional is a computation, not a value), no unforgeable (run-time identity),
    // no connective (a pattern fragment, copied through unevaluated).
    par.sends.is_empty()
        && par.receives.is_empty()
        && par.news.is_empty()
        && par.matches.is_empty()
        && par.bundles.is_empty()
        && par.conditionals.is_empty()
        && par.unforgeables.is_empty()
        && par.connectives.is_empty()
        && par.exprs.iter().all(expr_operands_ground)
}

fn opt_par_operands_ground(par: Option<&Par>) -> bool {
    match par {
        Some(inner) => all_operands_ground(inner),
        None => false,
    }
}

fn expr_operands_ground(expr: &Expr) -> bool {
    let Some(instance) = expr.expr_instance.as_ref() else {
        return false;
    };
    match instance {
        ExprInstance::GBool(_)
        | ExprInstance::GInt(_)
        | ExprInstance::GString(_)
        | ExprInstance::GUri(_)
        | ExprInstance::GByteArray(_)
        | ExprInstance::GDouble(_)
        | ExprInstance::GBigInt(_)
        | ExprInstance::GBigRat(_)
        | ExprInstance::GFixedPoint(_) => true,

        // A variable is by definition NOT settled at lowering time.
        ExprInstance::EVarBody(_) => false,

        ExprInstance::ENotBody(ENot { p }) | ExprInstance::ENegBody(ENeg { p }) => {
            opt_par_operands_ground(p.as_ref())
        },

        ExprInstance::EMultBody(EMult { p1, p2 })
        | ExprInstance::EDivBody(EDiv { p1, p2 })
        | ExprInstance::EModBody(EMod { p1, p2 })
        | ExprInstance::EPlusBody(EPlus { p1, p2 })
        | ExprInstance::EMinusBody(EMinus { p1, p2 })
        | ExprInstance::ELtBody(ELt { p1, p2 })
        | ExprInstance::ELteBody(ELte { p1, p2 })
        | ExprInstance::EGtBody(EGt { p1, p2 })
        | ExprInstance::EGteBody(EGte { p1, p2 })
        | ExprInstance::EEqBody(EEq { p1, p2 })
        | ExprInstance::ENeqBody(ENeq { p1, p2 })
        | ExprInstance::EAndBody(EAnd { p1, p2 })
        | ExprInstance::EOrBody(EOr { p1, p2 })
        | ExprInstance::EPercentPercentBody(EPercentPercent { p1, p2 })
        | ExprInstance::EPlusPlusBody(EPlusPlus { p1, p2 })
        | ExprInstance::EMinusMinusBody(EMinusMinus { p1, p2 }) => {
            opt_par_operands_ground(p1.as_ref()) && opt_par_operands_ground(p2.as_ref())
        },

        ExprInstance::EListBody(EList { ps, remainder, locally_free: _, connective_used: _ })
        | ExprInstance::ESetBody(ESet { ps, remainder, locally_free: _, connective_used: _ }) => {
            remainder.is_none() && ps.iter().all(all_operands_ground)
        },
        ExprInstance::ETupleBody(ETuple { ps, locally_free: _, connective_used: _ }) => {
            ps.iter().all(all_operands_ground)
        },
        ExprInstance::EMapBody(EMap { kvs, remainder, locally_free: _, connective_used: _ }) => {
            remainder.is_none()
                && kvs.iter().all(|KeyValuePair { key, value }| {
                    opt_par_operands_ground(key.as_ref()) && opt_par_operands_ground(value.as_ref())
                })
        },

        // A method call's target/arguments may be ground, but the METHOD is dispatched by the
        // reducer, not by `rho-pure-eval` (which answers `UnsupportedExpression`). Refuse.
        ExprInstance::EMethodBody(_) => false,

        // `t matches φ` is decided by the reducer's own spatial matcher, injected as an oracle.
        // Its verdict is a pure function of `(target, pattern)` — settled once both are ground.
        // The PATTERN is not evaluated, so it need only be free of unsettled operands; the
        // conservative `all_operands_ground` on both sides is what makes that checkable.
        ExprInstance::EMatchesBody(EMatches { target, pattern }) => {
            opt_par_operands_ground(target.as_ref()) && opt_par_operands_ground(pattern.as_ref())
        },

        // Named, not wildcarded: a new `ExprInstance` is a compile error here.
        ExprInstance::EPathmapBody(_) | ExprInstance::EZipperBody(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use models::create_bit_vector;
    use models::rhoapi::{Bundle, EMatches, GPrivate, GUnforgeable, New, Send};
    use models::rust::utils::{
        new_boundvar_par, new_freevar_par, new_gbool_par, new_gint_par, new_gstring_par,
        new_wildcard_par,
    };

    fn expr_par(instance: ExprInstance) -> Par {
        Par { exprs: vec![Expr { expr_instance: Some(instance) }], ..Par::default() }
    }

    fn eq(p1: Par, p2: Par) -> Par {
        expr_par(ExprInstance::EEqBody(EEq { p1: Some(p1), p2: Some(p2) }))
    }

    #[test]
    fn ground_literals_are_closed_and_ground() {
        for par in [
            new_gint_par(7, Vec::new(), false),
            new_gbool_par(true, Vec::new(), false),
            new_gstring_par("hi".to_string(), Vec::new(), false),
        ] {
            assert!(is_binder_closed(&par), "{par:?}");
            assert!(all_operands_ground(&par), "{par:?}");
        }
    }

    #[test]
    fn an_operator_over_literals_is_closed_and_ground() {
        let par = eq(new_gint_par(1, Vec::new(), false), new_gint_par(1, Vec::new(), false));
        assert!(is_binder_closed(&par));
        assert!(all_operands_ground(&par));
    }

    #[test]
    fn every_var_flavour_is_refused() {
        for par in [
            new_boundvar_par(0, create_bit_vector(&[0]), false),
            new_freevar_par(0, Vec::new()),
            new_wildcard_par(Vec::new(), true),
        ] {
            assert!(!is_binder_closed(&par), "{par:?} must not be binder-closed");
            assert!(!all_operands_ground(&par), "{par:?} must not be ground");
        }
    }

    #[test]
    fn a_var_nested_arbitrarily_deep_is_still_found() {
        // EEq(EAnd(ENot(BoundVar 3), true), false) — the var is three operators down.
        let deep = eq(
            expr_par(ExprInstance::EAndBody(EAnd {
                p1: Some(expr_par(ExprInstance::ENotBody(ENot {
                    p: Some(new_boundvar_par(3, create_bit_vector(&[3]), false)),
                }))),
                p2: Some(new_gbool_par(true, Vec::new(), false)),
            })),
            new_gbool_par(false, Vec::new(), false),
        );
        assert!(!is_binder_closed(&deep));
        assert!(!all_operands_ground(&deep));
    }

    #[test]
    fn a_var_inside_a_collection_is_found() {
        let list = expr_par(ExprInstance::EListBody(EList {
            ps: vec![new_gint_par(1, Vec::new(), false), new_boundvar_par(0, create_bit_vector(&[0]), false)],
            locally_free: create_bit_vector(&[0]),
            connective_used: false,
            remainder: None,
        }));
        assert!(!is_binder_closed(&list));
        assert!(!all_operands_ground(&list));
    }

    #[test]
    fn a_collection_remainder_is_a_binder() {
        let list = expr_par(ExprInstance::EListBody(EList {
            ps: vec![new_gint_par(1, Vec::new(), false)],
            locally_free: Vec::new(),
            connective_used: false,
            remainder: Some(Var { var_instance: Some(VarInstance::FreeVar(0)) }),
        }));
        assert!(!is_binder_closed(&list), "`[1 ... xs]` binds `xs`");
        assert!(!all_operands_ground(&list));
    }

    #[test]
    fn a_varref_connective_is_refused() {
        let varref = Par {
            connectives: vec![Connective {
                connective_instance: Some(ConnectiveInstance::VarRefBody(
                    models::rhoapi::VarRef { index: 0, depth: 1 },
                )),
            }],
            ..Par::default()
        };
        assert!(!is_binder_closed(&varref), "`=x` is a variable reference");
        assert!(!all_operands_ground(&varref));
    }

    #[test]
    fn an_unforgeable_name_is_a_runtime_identity_not_a_constant() {
        let unf = Par {
            unforgeables: vec![GUnforgeable {
                unf_instance: Some(models::rhoapi::g_unforgeable::UnfInstance::GPrivateBody(
                    GPrivate { id: vec![1, 2, 3] },
                )),
            }],
            ..Par::default()
        };
        assert!(!is_binder_closed(&unf));
        assert!(!all_operands_ground(&unf));
    }

    #[test]
    fn a_new_binder_is_refused_but_a_zero_width_new_is_transparent() {
        let bound = Par {
            news: vec![New {
                bind_count: 1,
                p: Some(new_gint_par(1, Vec::new(), false)),
                uri: Vec::new(),
                injections: Default::default(),
                locally_free: Vec::new(),
            }],
            ..Par::default()
        };
        assert!(!is_binder_closed(&bound), "`new x in 1` binds a fresh unforgeable");
    }

    #[test]
    fn a_receive_that_binds_is_refused() {
        let recv = Par {
            receives: vec![Receive {
                binds: vec![ReceiveBind {
                    patterns: vec![new_freevar_par(0, Vec::new())],
                    source: Some(new_gstring_par("c".to_string(), Vec::new(), false)),
                    remainder: None,
                    free_count: 1,
                }],
                body: Some(Par::default()),
                persistent: false,
                peek: false,
                bind_count: 1,
                locally_free: Vec::new(),
                connective_used: false,
                condition: None,
            }],
            ..Par::default()
        };
        assert!(!is_binder_closed(&recv));
    }

    /// Closedness and groundness are genuinely different questions: a literal-only `Send`
    /// mentions no variable but is a COMPUTATION, not a settled operand.
    #[test]
    fn closedness_and_groundness_differ_on_a_literal_send() {
        let send = Par {
            sends: vec![Send {
                chan: Some(new_gstring_par("c".to_string(), Vec::new(), false)),
                data: vec![new_gint_par(1, Vec::new(), false)],
                persistent: false,
                locally_free: Vec::new(),
                connective_used: false,
            }],
            ..Par::default()
        };
        assert!(is_binder_closed(&send), "no variable is mentioned");
        assert!(!all_operands_ground(&send), "a send is not a settled operand");
    }

    /// ★ The substrate-routing boundary, CHECKED not assumed (wiring-plan constraint 2):
    /// on every *operand-shaped* condition the discharge path can see, binder-closedness
    /// implies operand-groundness. The converse fails (previous test), which is why
    /// `classify` conjoins both rather than deriving one from the other.
    #[test]
    fn binder_closed_implies_operands_ground_on_operand_shaped_conditions() {
        let closed_operands = [
            new_gint_par(1, Vec::new(), false),
            new_gbool_par(false, Vec::new(), false),
            eq(new_gint_par(1, Vec::new(), false), new_gint_par(2, Vec::new(), false)),
            expr_par(ExprInstance::EAndBody(EAnd {
                p1: Some(new_gbool_par(true, Vec::new(), false)),
                p2: Some(new_gbool_par(false, Vec::new(), false)),
            })),
            expr_par(ExprInstance::EMatchesBody(EMatches {
                target: Some(new_gint_par(1, Vec::new(), false)),
                pattern: Some(new_gint_par(1, Vec::new(), false)),
            })),
        ];
        for par in closed_operands {
            assert!(is_binder_closed(&par), "{par:?}");
            assert!(
                all_operands_ground(&par),
                "binder-closed operand-shaped condition must also be ground: {par:?}"
            );
        }
    }

    /// ★ FAIL-CLOSED EXHAUSTIVENESS. `is_binder_closed`/`all_operands_ground` have no
    /// wildcard-`true` arm, so a NEW `rhoapi` constructor can never silently become "closed".
    ///
    /// The match below is deliberately written WITHOUT a `_` arm over every `ExprInstance`
    /// variant this module knows: adding a variant to `rhoapi` breaks THIS test's compilation,
    /// forcing an explicit decision, exactly as it breaks `expr_is_binder_closed`. The body
    /// records the decision each known variant carries.
    #[test]
    fn a_new_rhoapi_constructor_cannot_silently_become_closed() {
        fn decision_is_recorded(instance: &ExprInstance) -> bool {
            match instance {
                // Ground literals: closed.
                ExprInstance::GBool(_)
                | ExprInstance::GInt(_)
                | ExprInstance::GString(_)
                | ExprInstance::GUri(_)
                | ExprInstance::GByteArray(_)
                | ExprInstance::GDouble(_)
                | ExprInstance::GBigInt(_)
                | ExprInstance::GBigRat(_)
                | ExprInstance::GFixedPoint(_) => true,
                // Variable: refused.
                ExprInstance::EVarBody(_) => true,
                // Operators / collections / method / matches: decided structurally.
                ExprInstance::ENotBody(_)
                | ExprInstance::ENegBody(_)
                | ExprInstance::EMultBody(_)
                | ExprInstance::EDivBody(_)
                | ExprInstance::EModBody(_)
                | ExprInstance::EPlusBody(_)
                | ExprInstance::EMinusBody(_)
                | ExprInstance::ELtBody(_)
                | ExprInstance::ELteBody(_)
                | ExprInstance::EGtBody(_)
                | ExprInstance::EGteBody(_)
                | ExprInstance::EEqBody(_)
                | ExprInstance::ENeqBody(_)
                | ExprInstance::EAndBody(_)
                | ExprInstance::EOrBody(_)
                | ExprInstance::EPercentPercentBody(_)
                | ExprInstance::EPlusPlusBody(_)
                | ExprInstance::EMinusMinusBody(_)
                | ExprInstance::EListBody(_)
                | ExprInstance::ETupleBody(_)
                | ExprInstance::ESetBody(_)
                | ExprInstance::EMapBody(_)
                | ExprInstance::EMethodBody(_)
                | ExprInstance::EMatchesBody(_) => true,
                // Structures with no closedness decision: refused.
                ExprInstance::EPathmapBody(_) | ExprInstance::EZipperBody(_) => true,
            }
        }
        assert!(decision_is_recorded(&ExprInstance::GBool(true)));

        // The same discipline for `VarInstance` and `ConnectiveInstance`.
        fn var_decision_is_recorded(instance: &VarInstance) -> bool {
            match instance {
                VarInstance::BoundVar(_) | VarInstance::FreeVar(_) | VarInstance::Wildcard(_) => {
                    true
                },
            }
        }
        assert!(var_decision_is_recorded(&VarInstance::BoundVar(0)));

        fn connective_decision_is_recorded(instance: &ConnectiveInstance) -> bool {
            match instance {
                ConnectiveInstance::ConnAndBody(_)
                | ConnectiveInstance::ConnOrBody(_)
                | ConnectiveInstance::ConnNotBody(_)
                | ConnectiveInstance::VarRefBody(_)
                | ConnectiveInstance::ConnBool(_)
                | ConnectiveInstance::ConnInt(_)
                | ConnectiveInstance::ConnString(_)
                | ConnectiveInstance::ConnUri(_)
                | ConnectiveInstance::ConnByteArray(_) => true,
            }
        }
        assert!(connective_decision_is_recorded(&ConnectiveInstance::ConnBool(true)));
    }

    /// A `Bundle` is transparent to closedness: it is a permission wrapper, not a binder.
    #[test]
    fn a_bundle_is_transparent_to_closedness() {
        let bundled = Par {
            bundles: vec![Bundle {
                body: Some(new_gint_par(1, Vec::new(), false)),
                write_flag: true,
                read_flag: true,
            }],
            ..Par::default()
        };
        assert!(is_binder_closed(&bundled));
        assert!(!all_operands_ground(&bundled), "a bundle is not a settled operand");
    }
}
