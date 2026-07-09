//! Stage 4 S-binder — the COMMITTED, reproducible **property** floor for the FV theorem
//! `DeBruijnSubstTRS.v` (`subst_normal_form_is_debruijn_beta`:
//! `NF(subst(0, a, b)) = b[a/0]`, the capture-avoiding de-Bruijn β-substitution).
//!
//! The testing mandate is that every FV-proven property is ALSO example- AND property-tested
//! (randomized). The example floor already exists — `rho_net_subst_trs_reducer.rs` (`trs_case1/2/3`,
//! the full `^cmp`/`^pred`/`^shiftk`/`^subst`/`^shift` cascade on the live reducer) and
//! `rho_net_beta_firing.rs` (four firing tests). What was missing is a COMMITTED, reproducible
//! *randomized* cross-check: the red-team's "35 000 random terms × 3 oracles" run was in-sandbox
//! (an agent's throwaway, never committed). This file makes that floor reproducible.
//!
//! ─────────────────────────────────────────────────────────────────────────────────────────────
//! THREE ORACLES, cross-checked over random well-scoped de-Bruijn `(a, b)` pairs
//! ─────────────────────────────────────────────────────────────────────────────────────────────
//!
//!   (1) THE LIVE REDUCER      — seed `^subst(⟦Z⟧, a, b, @OUT)` on the installed five-receiver TRS
//!                               and run the β-substitution cascade to its normal form ON the real
//!                               f1r3node `RhoRuntime`/`RSpace` (no host loop). This is the
//!                               load-bearing oracle — it exercises the ACTUAL in-Rho mechanism,
//!                               including the unary-Peano `^cmp`/`^pred` numeral dispatch.
//!   (2) THE OPERATIONAL TRS    — an INDEPENDENT pure-Rust small-step rewrite system (`Tm` + `step`,
//!                               mirroring the `head_step`/congruence structure of `DeBruijnSubstTRS.v`
//!                               §2), normalized to a fixed point. Its bounded step count is an
//!                               executable strong-normalization (SN) witness.
//!   (3) THE DENOTATIONAL SPEC  — `reference_beta_subst(a, b) = subst(0, a, b)`, a pure-Rust
//!                               capture-avoiding de-Bruijn substitution written FROM THE DEFINITION
//!                               (λσ / de Bruijn), INDEPENDENTLY of the generated TRS rules. This is
//!                               the yardstick `b[a/0]`.
//!
//! WHAT RUNS WHERE (honest about cost — the reducer run dominates):
//!
//!   * `subst_trs_reference_matches_operational_trs_over_many_terms` — the HIGH-VOLUME floor
//!     (default 20 000 terms, env `SUBST_TRS_FLOOR_CASES`). Pure Rust, no reducer: oracle (2) vs
//!     oracle (3) — the reproducible analogue of the sandbox's 35 000-term cross-check — plus a
//!     per-term SN step-bound witness. A few seconds at the default count (the small-step normalizer
//!     rewrites and clones structurally rather than evaluating denotationally, which is exactly what
//!     makes it an INDEPENDENT oracle; raise/lower the count with `SUBST_TRS_FLOOR_CASES`).
//!   * `subst_trs_cascade_on_reducer_matches_reference` — the MECHANISM check (default 48 terms,
//!     env `SUBST_TRS_REDUCER_CASES`). Each case drives the LIVE cascade (oracle 1) and cross-checks
//!     the observed NF against oracle (3) rendered to the observation ABI. This is the load-bearing
//!     test; the count is kept sane because each reducer cascade is heavy.
//!   * `reducer_observation_rendering_is_correct_on_hand_picked_cases` — a small deterministic guard
//!     that validates the observation RENDERING (especially the Peano encoding of a *surviving*
//!     decremented `^bound` in the NF — a shape none of the committed example NFs exercise) against
//!     hand-computed ground truth, so a rendering bug is never mistaken for a TRS counterexample.
//!
//! Because (1) == (3) and (2) == (3), all three oracles agree by transitivity — the reproducible
//! executable image of `beta_seed_unique_nf_is_debruijn_beta`.
//!
//! If the randomized reducer loop ever reports a counterexample whose observed NF differs from the
//! reference `b[a/0]` (and the rendering guard passes), that is a GENUINE de-Bruijn TRS bug: STOP
//! and report the `(a, b)` pair — do not paper over it.
#![cfg(feature = "runtime-report")]

use std::cmp::Ordering;

use mettail_rholang_codegen::{
    reflect_ground_term_par, subst_seed_send_par, subst_trs_program_par, GroundTerm,
    BOUND_VAR_REFLECT_LABEL, FREE_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL, PEANO_SUCC_REFLECT_LABEL,
    PEANO_ZERO_REFLECT_LABEL,
};
use mettail_rholang_runtime::run_normalized_par_for_oracle_and_read_runtime_values;
use mettail_runtime::RuntimeObservationValue;
use models::rhoapi::Par;
use proptest::prelude::*;
use proptest::test_runner::{Config, TestCaseError, TestRunner};

/// A fixed test fingerprint — the installed TRS receivers' `Match` tags and the seed's reflected
/// terms use the SAME `reflect_tag(fp, …)`, so they rendezvous. Any consistent string suffices (the
/// decoder strips the fingerprint back to the bare constructor label).
const FP: &str = "trs-prop-probe";

/// A generous per-term step ceiling for the pure-Rust operational normalizer. The system is
/// STRONGLY NORMALIZING (`subst_trs_terminating`), so for a well-formed seed the fixed point is
/// reached in far fewer steps than this; tripping it would falsify the SN proof and is reported.
const MAX_TRS_STEPS: usize = 200_000;

// ═════════════════════════════════════════════════════════════════════════════════════════════
// 1. The de-Bruijn OBJECT term algebra (the normal forms) and the object signature.
// ═════════════════════════════════════════════════════════════════════════════════════════════

/// A reflected de-Bruijn OBJECT term — the shape of a normal form (`Obj` in `DeBruijnSubstTRS.v`).
///
///   * `Bound(k)` — a `^bound(peano k)` de-Bruijn index leaf.
///   * `Free(x)`  — a `^free x` free-variable leaf (`x` an object-signature nullary name).
///   * `Lam(b)`   — a `^lambda b` binder node (its bound variable de-Bruijn-implicit).
///   * `Node(op, ts)` — a non-reserved object constructor `op(t…)` (here `A`/`B` nullary, `F` unary,
///     `App` binary — the constructors the installed object-congruence arms are derived from).
#[derive(Clone, Debug, PartialEq, Eq)]
enum RefTerm {
    Bound(usize),
    Free(String),
    Lam(Box<RefTerm>),
    Node(String, Vec<RefTerm>),
}

// ═════════════════════════════════════════════════════════════════════════════════════════════
// 2. Oracle (3): the DENOTATIONAL capture-avoiding de-Bruijn β-substitution `b[a/0]`.
//
//    Transcribed from the de-Bruijn / λσ DEFINITION (identical in content to `oshift`/`oshiftk`/
//    `osubst` in `DeBruijnSubstTRS.v` §1, but written independently from the calculus, NOT from the
//    generated TRS rules — it is the yardstick, so it must not depend on the mechanism under test).
// ═════════════════════════════════════════════════════════════════════════════════════════════

/// de-Bruijn SHIFT: lift every free index `>= c` by one; `Lam` increments the cutoff `c` (this is
/// the capture-avoidance discipline).
fn ref_shift(c: usize, t: &RefTerm) -> RefTerm {
    match t {
        RefTerm::Bound(n) => RefTerm::Bound(if *n < c { *n } else { *n + 1 }),
        RefTerm::Free(x) => RefTerm::Free(x.clone()),
        RefTerm::Lam(b) => RefTerm::Lam(Box::new(ref_shift(c + 1, b))),
        RefTerm::Node(op, ts) => {
            RefTerm::Node(op.clone(), ts.iter().map(|t| ref_shift(c, t)).collect())
        },
    }
}

/// Iterated shift: `k` successive `shift 0` passes (the `^shiftk` receiver).
fn ref_shiftk(k: usize, a: &RefTerm) -> RefTerm {
    let mut acc = a.clone();
    for _ in 0..k {
        acc = ref_shift(0, &acc);
    }
    acc
}

/// de-Bruijn single SUBSTITUTION `t[a/j]`. On a bound index `n`: `n = j` ⟹ replace with `a` lifted
/// past the `j` binders it now sits under (`shiftk j a` — CAPTURE AVOIDANCE); `n > j` ⟹ decrement
/// (the binder `j` is being removed); `n < j` ⟹ leave it. Under `Lam`, `j` INCREMENTS (depth).
fn ref_subst(j: usize, a: &RefTerm, t: &RefTerm) -> RefTerm {
    match t {
        RefTerm::Bound(n) => match n.cmp(&j) {
            Ordering::Equal => ref_shiftk(j, a),
            Ordering::Greater => RefTerm::Bound(n - 1),
            Ordering::Less => RefTerm::Bound(*n),
        },
        RefTerm::Free(x) => RefTerm::Free(x.clone()),
        RefTerm::Lam(b) => RefTerm::Lam(Box::new(ref_subst(j + 1, a, b))),
        RefTerm::Node(op, ts) => {
            RefTerm::Node(op.clone(), ts.iter().map(|t| ref_subst(j, a, t)).collect())
        },
    }
}

/// The de-Bruijn β reduct `b[a/0]` (`odbeta` in the FV file).
fn reference_beta_subst(a: &RefTerm, b: &RefTerm) -> RefTerm {
    ref_subst(0, a, b)
}

// ═════════════════════════════════════════════════════════════════════════════════════════════
// 3. Oracle (2): the INDEPENDENT small-step operational TRS (the `Tm` + `step` model).
//
//    Mirrors `head_step` / the congruence closure of `DeBruijnSubstTRS.v` §2. The index arguments
//    are `usize` (the same sound abstraction of the `^cmp`/`^pred` unary-numeral dispatch the FV
//    file documents). Normalizing this small-step system is a genuinely separate computation from
//    the denotational `ref_subst` above (it rewrites machinery nodes step by step rather than
//    evaluating them structurally), so agreement between the two is a real cross-check.
// ═════════════════════════════════════════════════════════════════════════════════════════════

/// The TRS term algebra: object terms plus the three reduction-machinery nodes.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Tm {
    Bound(usize),
    Free(String),
    Lam(Box<Tm>),
    Node(String, Vec<Tm>),
    Shift(usize, Box<Tm>),
    Shiftk(usize, Box<Tm>),
    Subst(usize, Box<Tm>, Box<Tm>),
}

/// Embed an object term as a machinery-free `Tm`.
fn embed(o: &RefTerm) -> Tm {
    match o {
        RefTerm::Bound(n) => Tm::Bound(*n),
        RefTerm::Free(x) => Tm::Free(x.clone()),
        RefTerm::Lam(b) => Tm::Lam(Box::new(embed(b))),
        RefTerm::Node(op, ts) => Tm::Node(op.clone(), ts.iter().map(embed).collect()),
    }
}

/// A `Tm` is an OBJECT (a normal form: no machinery node anywhere) — mirrors `is_obj`.
fn is_obj(t: &Tm) -> bool {
    match t {
        Tm::Bound(_) | Tm::Free(_) => true,
        Tm::Lam(b) => is_obj(b),
        Tm::Node(_, ts) => ts.iter().all(is_obj),
        Tm::Shift(_, _) | Tm::Shiftk(_, _) | Tm::Subst(_, _, _) => false,
    }
}

/// The C1/C2 head rules: contract a redex whose machinery operand's object head is exposed. Returns
/// `None` when `t` is not a head redex (a leaf, an object node, or a machinery node whose operand is
/// itself still machinery — the caller then reduces that operand by congruence first).
fn head_step(t: &Tm) -> Option<Tm> {
    match t {
        Tm::Shift(c, inner) => match inner.as_ref() {
            Tm::Bound(n) => Some(Tm::Bound(if *n < *c { *n } else { *n + 1 })),
            Tm::Free(x) => Some(Tm::Free(x.clone())),
            Tm::Lam(b) => Some(Tm::Lam(Box::new(Tm::Shift(*c + 1, b.clone())))),
            Tm::Node(op, ts) => Some(Tm::Node(
                op.clone(),
                ts.iter().map(|s| Tm::Shift(*c, Box::new(s.clone()))).collect(),
            )),
            _ => None,
        },
        Tm::Shiftk(k, a) => match k {
            0 => Some(a.as_ref().clone()),
            _ => Some(Tm::Shift(0, Box::new(Tm::Shiftk(k - 1, a.clone())))),
        },
        Tm::Subst(j, a, inner) => match inner.as_ref() {
            Tm::Bound(n) => Some(match n.cmp(j) {
                Ordering::Equal => Tm::Shiftk(*j, a.clone()),
                Ordering::Greater => Tm::Bound(n - 1),
                Ordering::Less => Tm::Bound(*n),
            }),
            Tm::Free(x) => Some(Tm::Free(x.clone())),
            Tm::Lam(b) => Some(Tm::Lam(Box::new(Tm::Subst(*j + 1, a.clone(), b.clone())))),
            Tm::Node(op, ts) => Some(Tm::Node(
                op.clone(),
                ts.iter().map(|s| Tm::Subst(*j, a.clone(), Box::new(s.clone()))).collect(),
            )),
            _ => None,
        },
        _ => None,
    }
}

/// Reduce the leftmost reducible child of a node (the `s_node` congruence), returning the rewritten
/// child vector, or `None` if every child is already a normal form.
fn step_first_child(children: &[Tm]) -> Option<Vec<Tm>> {
    for (i, child) in children.iter().enumerate() {
        if let Some(reduced) = step_once(child) {
            let mut out = children.to_vec();
            out[i] = reduced;
            return Some(out);
        }
    }
    None
}

/// One small step: a head contraction if available, else congruence into the leftmost redex.
/// `None` iff `t` is a normal form.
fn step_once(t: &Tm) -> Option<Tm> {
    if let Some(reduced) = head_step(t) {
        return Some(reduced);
    }
    match t {
        Tm::Bound(_) | Tm::Free(_) => None,
        Tm::Lam(b) => step_once(b).map(|b2| Tm::Lam(Box::new(b2))),
        Tm::Node(op, ts) => step_first_child(ts).map(|ts2| Tm::Node(op.clone(), ts2)),
        Tm::Shift(c, inner) => step_once(inner).map(|u| Tm::Shift(*c, Box::new(u))),
        Tm::Shiftk(k, a) => step_once(a).map(|u| Tm::Shiftk(*k, Box::new(u))),
        Tm::Subst(j, a, inner) => {
            if let Some(a2) = step_once(a) {
                return Some(Tm::Subst(*j, Box::new(a2), inner.clone()));
            }
            step_once(inner).map(|u| Tm::Subst(*j, a.clone(), Box::new(u)))
        },
    }
}

/// Normalize the operational TRS to its fixed point, returning the normal form and the step count
/// (the executable SN witness). `Err(steps)` iff the step ceiling is exceeded (would falsify SN).
fn normalize_operational(mut t: Tm, max_steps: usize) -> Result<(Tm, usize), usize> {
    let mut steps = 0usize;
    while let Some(next) = step_once(&t) {
        t = next;
        steps += 1;
        if steps > max_steps {
            return Err(steps);
        }
    }
    Ok((t, steps))
}

// ═════════════════════════════════════════════════════════════════════════════════════════════
// 4. Oracle (1) bridge: reflect a `RefTerm` into the reducer seed, and render the reference reduct
//    into the observation-value ABI the reducer decodes to.
// ═════════════════════════════════════════════════════════════════════════════════════════════

fn g_nullary(label: &str) -> GroundTerm {
    GroundTerm::nullary(label)
}
fn g_node(label: &str, children: Vec<GroundTerm>) -> GroundTerm {
    GroundTerm::new(label, children)
}
/// `^bound(peano(depth))` — the reserved bound-index leaf, its Peano numeral `S(S(…Z))` built with
/// `depth` `S`s over `Z`.
fn g_bound(depth: usize) -> GroundTerm {
    let mut peano = g_nullary(PEANO_ZERO_REFLECT_LABEL);
    for _ in 0..depth {
        peano = g_node(PEANO_SUCC_REFLECT_LABEL, vec![peano]);
    }
    g_node(BOUND_VAR_REFLECT_LABEL, vec![peano])
}
fn g_free(name: &str) -> GroundTerm {
    g_node(FREE_VAR_REFLECT_LABEL, vec![g_nullary(name)])
}
fn g_lambda(body: GroundTerm) -> GroundTerm {
    g_node(LAMBDA_REFLECT_LABEL, vec![body])
}

/// Reflect a `RefTerm` into the ground `GroundTerm` the seed carries.
fn term_to_ground(t: &RefTerm) -> GroundTerm {
    match t {
        RefTerm::Bound(k) => g_bound(*k),
        RefTerm::Free(x) => g_free(x),
        RefTerm::Lam(b) => g_lambda(term_to_ground(b)),
        RefTerm::Node(op, ts) => g_node(op, ts.iter().map(term_to_ground).collect()),
    }
}

/// A LambdaDemo-shaped def: the object-congruence source for the installed `^subst`/`^shift`
/// receivers. `App` (arity 2), `F` (arity 1), `A`/`B` (arity 0) are the object constructors the
/// generator emits; `Lam` is the excluded `^lambda` binder. Extends the reducer harness's
/// `lambda_like_def` with a second nullary `B` (a couple of leaf tags), so the reduct's structural
/// identity — WHICH nullary survived — is a non-trivial assertion.
fn lambda_like_def() -> mettail_ast::language::LanguageDef {
    let fragment = r#"
        name: LambdaDemo,
        types { Term },
        terms {
            Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term ;
            App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term ;
            F . a:Term |- "f" "(" a ")" : Term ;
            A . |- "A" : Term ;
            B . |- "B" : Term ;
        },
        equations {},
        rewrites { Beta . |- (App (Lam fun) arg) ~> (eval fun arg) ; }
    "#;
    syn::parse_str::<mettail_ast::language::LanguageDef>(fragment).expect("probe def parses")
}

/// `subst_trs_program_par(def) ∥ ^subst(⟦Z⟧, ⟦a⟧, ⟦b⟧, @"OUT")` — install the five reserved TRS
/// receivers and fire one seed whose β-normal form rests on `@"OUT"`. Reduces `b[a/0]`.
fn trs_program(arg: GroundTerm, body: GroundTerm) -> Par {
    let def = lambda_like_def();
    let seed = subst_seed_send_par(
        FP,
        reflect_ground_term_par(&arg, FP),
        reflect_ground_term_par(&body, FP),
        "OUT",
    );
    subst_trs_program_par(&def, FP).append(seed)
}

/// The observation-value peano numeral `S(S(…Z))` for a surviving de-Bruijn index `k`.
fn peano_obs(k: usize) -> RuntimeObservationValue {
    let mut p = onull(PEANO_ZERO_REFLECT_LABEL);
    for _ in 0..k {
        p = oterm(PEANO_SUCC_REFLECT_LABEL, vec![p]);
    }
    p
}

/// Render a reference OBJECT term into the `RuntimeObservationValue` the reducer's
/// `decode_reflected_term` produces for that same term (the recursive `{ constructor, children }`
/// image of the reflected `EList` ABI). This is how oracle (3) is compared against oracle (1).
fn render_obs(t: &RefTerm) -> RuntimeObservationValue {
    match t {
        RefTerm::Bound(k) => oterm(BOUND_VAR_REFLECT_LABEL, vec![peano_obs(*k)]),
        RefTerm::Free(x) => oterm(FREE_VAR_REFLECT_LABEL, vec![onull(x)]),
        RefTerm::Lam(b) => oterm(LAMBDA_REFLECT_LABEL, vec![render_obs(b)]),
        RefTerm::Node(op, ts) => oterm(op, ts.iter().map(render_obs).collect()),
    }
}

fn oterm(constructor: &str, children: Vec<RuntimeObservationValue>) -> RuntimeObservationValue {
    RuntimeObservationValue::Term { constructor: constructor.to_string(), children }
}
fn onull(constructor: &str) -> RuntimeObservationValue {
    oterm(constructor, Vec::new())
}

// ═════════════════════════════════════════════════════════════════════════════════════════════
// 5. The random well-scoped de-Bruijn term generator (a proptest `Strategy`).
//
//    `arb_term(binder_depth, depth)` produces terms that are WELL-SCOPED under `binder_depth`
//    enclosing binders: every `Bound(k)` has `k < binder_depth`, so it points at a real binder
//    (the redex binder or an enclosing `Lam`). This is CRUCIAL: it keeps `b[a/0]` meaningful AND
//    keeps the unary-Peano numerals small (bounded by the binder depth), so each reducer cascade
//    is fast. `depth` bounds the structural height (hence the node count).
// ═════════════════════════════════════════════════════════════════════════════════════════════

/// Leaves in scope: a free variable (`c`/`d`), a nullary object node (`A`/`B`), and — only when at
/// least one binder is in scope — a bound index `0..binder_depth` (weighted up, to exercise subst).
fn arb_leaf(binder_depth: usize) -> BoxedStrategy<RefTerm> {
    let free = prop_oneof![Just("c"), Just("d")].prop_map(|s| RefTerm::Free(s.to_string()));
    let nullary =
        prop_oneof![Just("A"), Just("B")].prop_map(|s| RefTerm::Node(s.to_string(), Vec::new()));
    if binder_depth > 0 {
        let bound = (0..binder_depth).prop_map(RefTerm::Bound);
        prop_oneof![2 => free, 2 => nullary, 3 => bound].boxed()
    } else {
        prop_oneof![1 => free, 1 => nullary].boxed()
    }
}

/// A well-scoped term of structural height at most `depth`, under `binder_depth` enclosing binders.
/// Leaves are weighted over the recursive constructors so the expected size stays small.
fn arb_term(binder_depth: usize, depth: usize) -> BoxedStrategy<RefTerm> {
    if depth == 0 {
        return arb_leaf(binder_depth);
    }
    let leaf = arb_leaf(binder_depth);
    let lam = arb_term(binder_depth + 1, depth - 1).prop_map(|b| RefTerm::Lam(Box::new(b)));
    let unary =
        arb_term(binder_depth, depth - 1).prop_map(|c| RefTerm::Node("F".to_string(), vec![c]));
    let binary = (arb_term(binder_depth, depth - 1), arb_term(binder_depth, depth - 1))
        .prop_map(|(x, y)| RefTerm::Node("App".to_string(), vec![x, y]));
    prop_oneof![
        4 => leaf,
        2 => lam,
        2 => unary,
        2 => binary,
    ]
    .boxed()
}

/// A random `(a, b)` pair. `a` (the replacement / argument) is generated under `0..=2` ambient
/// binders — so it sometimes carries FREE indices that `^shiftk` must lift (exercising the shift
/// machinery), sometimes is closed. `b` (the substitution scope / lambda body) is generated under
/// `1..=2` binders — index `0` (the redex var, the `Eq`⟹`shiftk` branch) is always in scope, and
/// `1` (a `Gt`⟹`pred` outer reference) is often in scope.
fn arb_term_pair(max_depth: usize) -> impl Strategy<Value = (RefTerm, RefTerm)> {
    let arg = (0usize..=2).prop_flat_map(move |da| arb_term(da, max_depth));
    let body = (1usize..=2).prop_flat_map(move |db| arb_term(db, max_depth));
    (arg, body)
}

/// Read a case count from an environment variable, defaulting when unset/unparsable.
fn env_cases(var: &str, default: u32) -> u32 {
    std::env::var(var).ok().and_then(|s| s.parse().ok()).unwrap_or(default)
}

// ═════════════════════════════════════════════════════════════════════════════════════════════
// 6. THE TESTS.
// ═════════════════════════════════════════════════════════════════════════════════════════════

/// HIGH-VOLUME FLOOR — oracle (2) vs oracle (3), no reducer. For many random well-scoped `(a, b)`
/// the INDEPENDENT small-step operational TRS reaches, from the seed `subst(0, a, b)`, a normal
/// form that (a) is an OBJECT (no residual machinery), (b) equals the denotational reference
/// `b[a/0]`, and (c) is reached within the SN step ceiling. This is the reproducible executable
/// image of `beta_seed_unique_nf_is_debruijn_beta` at the abstract-TRS level, and the committed
/// analogue of the sandbox's 35 000-term × oracles cross-check.
#[test]
fn subst_trs_reference_matches_operational_trs_over_many_terms() {
    let cases = env_cases("SUBST_TRS_FLOOR_CASES", 20_000);
    let mut runner =
        TestRunner::new(Config { cases, failure_persistence: None, ..Config::default() });
    runner
        .run(&arb_term_pair(3), |(a, b)| {
            let reference = reference_beta_subst(&a, &b);
            let seed = Tm::Subst(0, Box::new(embed(&a)), Box::new(embed(&b)));
            let (nf, steps) = normalize_operational(seed, MAX_TRS_STEPS).map_err(|steps| {
                TestCaseError::fail(format!(
                    "operational TRS exceeded {steps} steps (SN witness broken): a={a:?} b={b:?}"
                ))
            })?;
            prop_assert!(
                is_obj(&nf),
                "operational NF still carries reduction machinery: a={:?} b={:?} nf={:?}",
                a,
                b,
                nf
            );
            prop_assert_eq!(
                &nf,
                &embed(&reference),
                "operational TRS NF must equal the denotational de-Bruijn b[a/0]: a={:?} b={:?}",
                a,
                b
            );
            prop_assert!(steps <= MAX_TRS_STEPS);
            Ok(())
        })
        .expect("operational TRS agrees with the denotational de-Bruijn b[a/0] on every term");
}

/// MECHANISM CHECK — oracle (1) vs oracle (3). For each random well-scoped `(a, b)`, seed the
/// installed five-receiver de-Bruijn subst/shift TRS with `^subst(⟦Z⟧, a, b, @OUT)` and run the
/// β-substitution cascade to its normal form ON THE LIVE f1r3node reducer; the single value that
/// lands on `OUT` must equal the reference `b[a/0]` rendered to the observation ABI. The count is
/// modest because each cascade is a real RSpace evaluation; raise it with `SUBST_TRS_REDUCER_CASES`.
#[test]
fn subst_trs_cascade_on_reducer_matches_reference() {
    let cases = env_cases("SUBST_TRS_REDUCER_CASES", 48);
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("a tokio runtime for the reducer cascade");
    let mut runner =
        TestRunner::new(Config { cases, failure_persistence: None, ..Config::default() });
    runner
        .run(&arb_term_pair(3), |(a, b)| {
            let reference = reference_beta_subst(&a, &b);
            let expected = render_obs(&reference);
            let program = trs_program(term_to_ground(&a), term_to_ground(&b));
            let observed = rt
                .block_on(run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT"))
                .map_err(|e| {
                    TestCaseError::fail(format!("reducer run errored: {e} (a={a:?} b={b:?})"))
                })?;
            prop_assert_eq!(
                observed,
                vec![expected],
                "in-Rho β cascade NF must equal the de-Bruijn reference b[a/0]:\n  a         = {:?}\n  b         = {:?}\n  b[a/0]    = {:?}",
                a,
                b,
                reference
            );
            Ok(())
        })
        .expect("the live in-Rho subst TRS cascade computes b[a/0] for every generated (a, b)");
}

/// RENDERING GUARD — pins the observation ABI (oracle (1)'s decoded shape) against hand-computed
/// ground truth, so a rendering bug in `render_obs` can never be misread as a TRS counterexample.
/// The critical cases are the ones that leave a SURVIVING, decremented `^bound` in the normal form
/// (`subst(0, A, ^bound 1) → ^bound 0`; `subst(0, A, F(^bound 2)) → F(^bound 1)`) — a Peano-encoded
/// shape none of the committed example NFs (`F(A)`, `λ.c`, `App(A, A)`) exercise. Each case asserts
/// the live reducer output equals the hand value AND that `render_obs(reference)` equals it too.
#[test]
fn reducer_observation_rendering_is_correct_on_hand_picked_cases() {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("a tokio runtime for the reducer cascade");

    // (a, b, hand-computed expected observation for the NF of subst(0, a, b)).
    let cases: Vec<(RefTerm, RefTerm, RuntimeObservationValue)> = vec![
        // subst(0, A, ^bound 1): n=1 > j=0 ⟹ pred ⟹ ^bound 0 (a SURVIVING decremented index).
        (
            RefTerm::Node("A".to_string(), vec![]),
            RefTerm::Bound(1),
            oterm(BOUND_VAR_REFLECT_LABEL, vec![onull(PEANO_ZERO_REFLECT_LABEL)]),
        ),
        // subst(0, A, F(^bound 2)) ⟹ F(^bound 1): object descent + pred (^bound 2 → ^bound 1).
        (
            RefTerm::Node("A".to_string(), vec![]),
            RefTerm::Node("F".to_string(), vec![RefTerm::Bound(2)]),
            oterm(
                "F",
                vec![oterm(
                    BOUND_VAR_REFLECT_LABEL,
                    vec![oterm(PEANO_SUCC_REFLECT_LABEL, vec![onull(PEANO_ZERO_REFLECT_LABEL)])],
                )],
            ),
        ),
        // subst(0, B, ^lambda(^bound 1)) ⟹ ^lambda(shiftk(1, B)) = ^lambda(B): depth increment then
        // ^bound(S Z) compares Eq ⟹ ^shiftk(S Z, B) = ^shift(Z, B) = B (nullary inert under shift).
        (
            RefTerm::Node("B".to_string(), vec![]),
            RefTerm::Lam(Box::new(RefTerm::Bound(1))),
            oterm(LAMBDA_REFLECT_LABEL, vec![onull("B")]),
        ),
        // subst(0, A, F(^bound 0)) ⟹ F(A): the committed case1, as a rendering anchor.
        (
            RefTerm::Node("A".to_string(), vec![]),
            RefTerm::Node("F".to_string(), vec![RefTerm::Bound(0)]),
            oterm("F", vec![onull("A")]),
        ),
    ];

    for (a, b, hand_expected) in &cases {
        // The hand-computed value must equal both the denotational reference rendering AND the live
        // reducer output — so the guard validates render_obs, ref_subst, and the reducer together.
        assert_eq!(
            &render_obs(&reference_beta_subst(a, b)),
            hand_expected,
            "render_obs(reference) disagrees with the hand value for a={a:?} b={b:?}"
        );
        let program = trs_program(term_to_ground(a), term_to_ground(b));
        let observed = rt
            .block_on(run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT"))
            .expect("the hand-picked TRS program runs on the reducer");
        assert_eq!(
            observed,
            vec![hand_expected.clone()],
            "the live reducer NF must equal the hand-computed b[a/0] for a={a:?} b={b:?}"
        );
    }
}
