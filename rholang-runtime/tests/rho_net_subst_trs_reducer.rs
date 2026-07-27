//! Stage 4 S-binder SLICE 2a — the GENERATED de-Bruijn subst/shift TRS reduces `^subst(Z, a, b)`
//! to the β-normal form ON THE LIVE f1r3node reducer, driven ONLY by the five reserved receivers
//! ([`mettail_rholang_codegen::subst_trs_program_par`]) + a direct seed send
//! ([`mettail_rholang_codegen::subst_seed_send_par`]) — NO host loop, NO automaton match.
//!
//! This is the REAL-`Par` analogue of the hand-written Rholang spike
//! `rholang-runtime/tests/spike_subst_driver.rs` (which proved the ALGORITHM on the reducer): here
//! the receivers + seed are built by the codegen [`Par`] emitters that the installed β program uses,
//! so a passing observation validates the reflected-`EList` encoding + the De Bruijn / `locally_free`
//! discipline of the generated receivers INDEPENDENTLY of the β-match wiring (SLICE 2a de-risk).
//!
//! The three cases mirror the spike's `case1`/`case2`/`case3`:
//!   * `case1`  `subst(Z, A, F(^bound Z))            → F(A)`      — object descent (F) + `^shiftk`.
//!   * `case2`  `subst(Z, ^free c, ^lambda(^bound(S Z))) → ^lambda(^free c)` — depth increment.
//!   * `case3`  `subst(Z, A, App(^bound Z, ^bound Z)) → App(A, A)` — sibling co-reduction (arity 2).
#![cfg(feature = "runtime-report")]

use mettail_rholang_codegen::{
    reflect_ground_term_par, subst_seed_send_par, subst_trs_program_par, GroundTerm,
    BOUND_VAR_REFLECT_LABEL, FREE_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
    PEANO_SUCC_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL,
};
use mettail_rholang_runtime::run_normalized_par_for_oracle_and_read_runtime_values;
use mettail_runtime::RuntimeObservationValue;
use models::rhoapi::Par;

/// A fixed test fingerprint — the TRS receivers' `Match` tags and the seed's reflected terms use the
/// SAME `reflect_tag(fp, …)`, so they rendezvous. (The install path threads the plan fingerprint;
/// for this isolated de-risk any consistent string suffices — the decoder strips it.)
const FP: &str = "trs-reducer-probe";

/// A LambdaDemo-shaped def (App/F/A structural + Lam binder + Beta) — the object-congruence source
/// for `^subst`/`^shift` (App arity 2, F arity 1, A arity 0; Lam is the excluded `^lambda` binder).
fn lambda_like_def() -> mettail_ast::language::LanguageDef {
    let fragment = r#"
        name: LambdaDemo,
        types { Term },
        terms {
            Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term ;
            App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term ;
            F . a:Term |- "f" "(" a ")" : Term ;
            A . |- "A" : Term ;
        },
        equations {},
        rewrites { Beta . |- (App (Lam fun) arg) ~> (eval fun arg) ; }
    "#;
    syn::parse_str::<mettail_ast::language::LanguageDef>(fragment).expect("probe def parses")
}

/// `subst_trs_program_par(def) ∥ ^subst(⟦Z⟧, ⟦a⟧, ⟦b⟧, @"OUT")` — install the five receivers and
/// fire one seed whose NF rests on `@"OUT"`.
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

fn nullary(label: &str) -> GroundTerm {
    GroundTerm::nullary(label)
}
fn node(label: &str, children: Vec<GroundTerm>) -> GroundTerm {
    GroundTerm::new(label, children)
}
/// `^bound(peano(depth))`.
fn bound(depth: usize) -> GroundTerm {
    let mut peano = nullary(PEANO_ZERO_REFLECT_LABEL);
    for _ in 0..depth {
        peano = node(PEANO_SUCC_REFLECT_LABEL, vec![peano]);
    }
    node(BOUND_VAR_REFLECT_LABEL, vec![peano])
}
fn free(name: &str) -> GroundTerm {
    node(FREE_VAR_REFLECT_LABEL, vec![nullary(name)])
}
fn lambda(body: GroundTerm) -> GroundTerm {
    node(LAMBDA_REFLECT_LABEL, vec![body])
}

// Observation-value builders (the decoded shape — the ABI fingerprint is stripped to the label).
fn oterm(constructor: &str, children: Vec<RuntimeObservationValue>) -> RuntimeObservationValue {
    RuntimeObservationValue::Term {
        constructor: constructor.to_string(),
        children,
    }
}
fn onull(constructor: &str) -> RuntimeObservationValue {
    oterm(constructor, Vec::new())
}

/// `case1` — `subst(Z, A, F(^bound Z)) → F(A)`. Object descent into F (arity 1) then `^bound Z` at
/// depth `Z` compares `Eq` ⟹ `^shiftk(Z, A) = A`. The β-normal form of `(λ. f(0)) A`.
#[tokio::test]
async fn trs_case1_object_descent_and_shiftk_reduces_on_the_reducer() {
    let program = trs_program(nullary("A"), node("F", vec![bound(0)]));
    let observed = run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
        .await
        .expect("the TRS program runs on the reducer");
    assert_eq!(
        observed,
        vec![oterm("F", vec![onull("A")])],
        "subst(Z, A, F(^bound Z)) must reduce to F(A) — object descent + shiftk fired in-Rho",
    );
}

/// `case2` — `subst(Z, ^free c, ^lambda(^bound(S Z))) → ^lambda(^free c)`. The C1 depth INCREMENT
/// under `^lambda` (`Z → S Z`) then `^bound(S Z)` at depth `S Z` compares `Eq` ⟹ `^shiftk(S Z,
/// ^free c) = ^shift(Z, ^free c) = ^free c` (free vars inert under shift). The NF of `(λ.λ.1) c`.
#[tokio::test]
async fn trs_case2_nested_binder_depth_increment_reduces_on_the_reducer() {
    let program = trs_program(free("c"), lambda(bound(1)));
    let observed = run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
        .await
        .expect("the TRS program runs on the reducer");
    assert_eq!(
        observed,
        vec![oterm(LAMBDA_REFLECT_LABEL, vec![oterm(FREE_VAR_REFLECT_LABEL, vec![onull("c")])])],
        "subst(Z, ^free c, ^lambda(^bound(S Z))) must reduce to ^lambda(^free c) — depth increment + shiftk",
    );
}

/// `case3` — `subst(Z, A, App(^bound Z, ^bound Z)) → App(A, A)`. Object descent into App (arity 2)
/// spawns TWO sibling `^subst(Z, A, ^bound Z)` redexes that co-reduce to `A` and rejoin via the
/// atomic continuation JOIN (`for(@s0 <- r0 & @s1 <- r1){ ret!(App(s0, s1)) }`) — NO widening.
#[tokio::test]
async fn trs_case3_object_descent_two_sibling_substs_coreduce_on_the_reducer() {
    let program = trs_program(nullary("A"), node("App", vec![bound(0), bound(0)]));
    let observed = run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
        .await
        .expect("the TRS program runs on the reducer");
    assert_eq!(
        observed,
        vec![oterm("App", vec![onull("A"), onull("A")])],
        "subst(Z, A, App(^bound Z, ^bound Z)) must reduce to App(A, A) — sibling co-reduction, no widening",
    );
}
