//! DE-RISKING SPIKE — S-binder in-Rho substitution **reduction driver** (Driver-B).
//!
//! Goal: prove that a SELF-RE-SPREADING receiver cascade implementing the blueprint's
//! generated de-Bruijn subst/shift TRS reduces `^subst(Z, a, body)` to its β-normal form ON THE
//! LIVE f1r3node reducer — inside ONE `inj`, with NO host loop, NO `Value → GroundTerm`
//! de-reflection, and NO all-sites locator — and that MULTIPLE sibling subst redexes co-reduce
//! in that same run (the "widening").
//!
//! The red-team found the HOST-loop driver (Driver-A) blocked: `in_rho_match_all_sites_call_par`
//! fails closed with `NestedEntryMultiSite` when `sites.len() > 1`, there is no
//! `RuntimeObservationValue::Term → GroundTerm` de-reflection, and the replay loop has no
//! step-to-step feedback. This spike demonstrates the ALTERNATIVE (Driver-B, the paper's
//! `for(⟦L⟧ ⇐ c(ℓ)){ c(ℓ)!(⟦R⟧_ℓ) | <re-install> }` idiom): the receivers themselves, once
//! installed, cascade `^subst → … → NF` with no host in the loop.
//!
//! ## Encoding (smallest object alphabet that suffices)
//! Terms are tagged Rholang tuples; Peano indices keep `cmp`/`shift` STRUCTURAL (blueprint C2):
//!   * Peano `Z`  = `"Z"`            `S(n)` = `("S", n)`
//!   * `^bound(n)` = `("bound", n)`  `^lambda(body)` = `("lambda", body)`  `^free(x)` = `("free", x)`
//!   * ONE binary object constructor `f`: `("f", t1, t2)`
//!
//! Each TRS "rule family" is ONE persistent `contract` that dispatches on its subject via an inner
//! `match` and RE-SPREADS reduced sub-work by re-invoking the SAME contracts (self / mutual
//! recursion) with fresh return channels. This is exactly the generated set-automaton σ-receiver
//! shape (one receiver per rule root, dispatching on the head tag), with the recursion supplying
//! the multi-round cascade the blueprint §6 calls the "driver".
//!
//! The generated TRS (blueprint §4.2, corrected depth-indexed C1):
//! ```text
//! subst(j,a,bound n)   -> cmp(n,j){ Eq->shiftk(j,a) ; Gt->bound(pred n) ; Lt->bound n }
//! subst(j,a,lambda b)  -> lambda(subst(S j, a, b))            -- target index INCREMENTS under a binder
//! subst(j,a,free x)    -> free x
//! subst(j,a,f(t1,t2))  -> f(subst(j,a,t1), subst(j,a,t2))     -- object descent: TWO sibling redexes
//! shift(c,bound n)     -> cmp(n,c){ Lt->bound n ; _->bound(S n) }
//! shift(c,lambda b)    -> lambda(shift(S c, b))
//! shift(c,free x)      -> free x
//! shift(c,f(t1,t2))    -> f(shift(c,t1), shift(c,t2))
//! shiftk(Z,a)=a ; shiftk(S k,a)=shift(Z, shiftk(k,a))
//! cmp(Z,Z)=Eq; cmp(Z,S_)=Lt; cmp(S_,Z)=Gt; cmp(S m,S n)=cmp(m,n)
//! pred(Z)=Z; pred(S n)=n
//! ```
//!
//! Executed on the REAL reducer via `Compiler::source_to_adt` (parse + normalize to a `Par`) then
//! `run_normalized_par_for_oracle_and_read_runtime_values` (`create_rho_runtime`, in-memory RSpace)
//! — the identical reducer the campaign firing tests use.
#![cfg(feature = "runtime-report")]

use mettail_rholang_runtime::run_normalized_par_for_oracle_and_read_runtime_values;
use mettail_runtime::RuntimeObservationValue;
use rholang::rust::interpreter::compiler::compiler::Compiler;

/// The mutually-recursive subst/shift/cmp/shiftk/pred contracts, bound by the enclosing
/// `new subst, shift, cmp, shiftk, pred, result in { … }`. Every reduced sub-term is produced by
/// RE-INVOKING these same contracts on a fresh return channel — the self-re-spreading cascade.
const TRS_CONTRACTS: &str = r#"
  contract cmp(@m, @n, ret) = {
    match m {
      "Z" => { match n { "Z" => { ret!("Eq") } ("S", _) => { ret!("Lt") } } }
      ("S", mm) => { match n { "Z" => { ret!("Gt") } ("S", nn) => { cmp!(mm, nn, *ret) } } }
    }
  } |
  contract pred(@n, ret) = {
    match n { "Z" => { ret!("Z") } ("S", m) => { ret!(m) } }
  } |
  contract shiftk(@k, @a, ret) = {
    match k {
      "Z" => { ret!(a) }
      ("S", kk) => { new r in { shiftk!(kk, a, *r) | for (@sk <- r) { shift!("Z", sk, *ret) } } }
    }
  } |
  contract shift(@c, @t, ret) = {
    match t {
      ("bound", n) => {
        new r in {
          cmp!(n, c, *r) |
          for (@cr <- r) {
            match cr { "Lt" => { ret!(("bound", n)) } _ => { ret!(("bound", ("S", n))) } }
          }
        }
      }
      ("lambda", body) => {
        new r in { shift!(("S", c), body, *r) | for (@rb <- r) { ret!(("lambda", rb)) } }
      }
      ("free", x) => { ret!(("free", x)) }
      ("f", t1, t2) => {
        new r1, r2 in {
          shift!(c, t1, *r1) | shift!(c, t2, *r2) |
          for (@s1 <- r1 & @s2 <- r2) { ret!(("f", s1, s2)) }
        }
      }
    }
  } |
  contract subst(@j, @a, @t, ret) = {
    match t {
      ("bound", n) => {
        new r in {
          cmp!(n, j, *r) |
          for (@cr <- r) {
            match cr {
              "Eq" => { shiftk!(j, a, *ret) }
              "Gt" => { new rp in { pred!(n, *rp) | for (@pn <- rp) { ret!(("bound", pn)) } } }
              "Lt" => { ret!(("bound", n)) }
            }
          }
        }
      }
      ("lambda", body) => {
        new r in { subst!(("S", j), a, body, *r) | for (@rb <- r) { ret!(("lambda", rb)) } }
      }
      ("free", x) => { ret!(("free", x)) }
      ("f", t1, t2) => {
        new r1, r2 in {
          subst!(j, a, t1, *r1) | subst!(j, a, t2, *r2) |
          for (@s1 <- r1 & @s2 <- r2) { ret!(("f", s1, s2)) }
        }
      }
    }
  }
"#;

/// Wrap the TRS contracts + a `subst!`/seed call + the OUT observer in one `new` scope, so the seed
/// self-drives the cascade to NF and the NF rests on the public `@"OUT"` channel.
fn trs_program(seed_call: &str) -> String {
    let mut src = String::new();
    src.push_str("new subst, shift, cmp, shiftk, pred, result in {\n");
    src.push_str(TRS_CONTRACTS);
    src.push_str(" |\n  ");
    src.push_str(seed_call);
    src.push_str(" |\n  for (@nf <- result) { @\"OUT\"!(nf) }\n}\n");
    src
}

/// Compile Rholang source to a normalized `Par` (parse + normalize — the same front end
/// `evaluate_with_term` uses), then inject it on a fresh in-memory `create_rho_runtime` and read
/// every closed value resting on `@"OUT"`.
async fn run_to_nf(source: &str) -> Vec<RuntimeObservationValue> {
    let par = Compiler::source_to_adt(source)
        .unwrap_or_else(|e| panic!("spike source must normalize:\n{source}\n{e:?}"));
    run_normalized_par_for_oracle_and_read_runtime_values(&par, "OUT")
        .await
        .unwrap_or_else(|e| panic!("spike program must run on the reducer:\n{source}\n{e}"))
}

// ---- structural NF builders (the reflected-term decode shape) --------------------------------

fn text(s: &str) -> RuntimeObservationValue {
    RuntimeObservationValue::Text(s.to_string())
}
fn tuple(items: Vec<RuntimeObservationValue>) -> RuntimeObservationValue {
    RuntimeObservationValue::Tuple(items)
}
/// `("free", x)` — an object atom / free variable in the tagged encoding.
fn free(x: &str) -> RuntimeObservationValue {
    tuple(vec![text("free"), text(x)])
}
/// `("lambda", body)`.
fn lambda(body: RuntimeObservationValue) -> RuntimeObservationValue {
    tuple(vec![text("lambda"), body])
}
/// `("f", t1, t2)`.
fn f2(t1: RuntimeObservationValue, t2: RuntimeObservationValue) -> RuntimeObservationValue {
    tuple(vec![text("f"), t1, t2])
}

// ============================================================================================
// PROBES — localize the two mechanism assumptions independently of the full TRS.
// ============================================================================================

/// Probe 1: a self-recursive persistent contract with inner `match` dispatch reduces a Peano
/// comparison on the reducer. `cmp(S S Z, S Z) = Gt` requires the recursion `cmp(S m,S n)=cmp(m,n)`
/// to fire twice, so a `"Gt"` on OUT is evidence that persistent-contract self-re-spreading +
/// structural `match` dispatch work end-to-end.
#[tokio::test]
async fn probe_recursive_contract_dispatch_reduces_peano_cmp() {
    let program = r#"
      new cmp, result in {
        contract cmp(@m, @n, ret) = {
          match m {
            "Z" => { match n { "Z" => { ret!("Eq") } ("S", _) => { ret!("Lt") } } }
            ("S", mm) => { match n { "Z" => { ret!("Gt") } ("S", nn) => { cmp!(mm, nn, *ret) } } }
          }
        } |
        cmp!(("S", ("S", "Z")), ("S", "Z"), *result) |
        for (@r <- result) { @"OUT"!(r) }
      }
    "#;
    let observed = run_to_nf(program).await;
    assert_eq!(observed, vec![text("Gt")], "cmp(2,1) must reduce to Gt via the recursive cascade");
}

/// Probe 2 (the runtime "widening" in isolation): ONE persistent contract serves TWO parallel
/// calls in the same run. This is the RSpace-level analogue of the `NestedEntryMultiSite` concern —
/// it shows the RUNTIME has NO problem with parallel same-shape requests against one persistent
/// σ-receiver (the gate is a COMPILE-TIME codegen guard, not a reducer limit). Both `p` and `q`
/// must land on OUT.
#[tokio::test]
async fn probe_one_persistent_contract_serves_two_parallel_calls() {
    let program = r#"
      new id, r1, r2 in {
        contract id(@x, ret) = { ret!(x) } |
        id!("p", *r1) | id!("q", *r2) |
        for (@a <- r1) { @"OUT"!(a) } |
        for (@b <- r2) { @"OUT"!(b) }
      }
    "#;
    let mut observed = run_to_nf(program).await;
    observed.sort();
    assert_eq!(
        observed,
        vec![text("p"), text("q")],
        "one persistent contract must serve both parallel calls (no runtime multi-site contention)"
    );
}

// ============================================================================================
// THE THREE REQUIRED CASES — the self-re-spreading subst cascade reduces to NF on the reducer.
// ============================================================================================

/// Case 1 — `(λ.0) a → a`. Seed `^subst(Z, a, ^bound Z)`.
/// Trace: `subst(Z, a, bound Z)` → `cmp(Z,Z)=Eq` → `shiftk(Z, a) = a`. NF = `a = ("free","a")`.
#[tokio::test]
async fn case1_beta_identity_subst_reduces_to_the_argument() {
    let seed = r#"subst!("Z", ("free", "a"), ("bound", "Z"), *result)"#;
    let observed = run_to_nf(&trs_program(seed)).await;
    println!("case1 NF = {observed:?}");
    assert_eq!(
        observed,
        vec![free("a")],
        "(λ.0) a must reduce to a — the subst cascade self-drove to NF on the reducer"
    );
}

/// Case 2 — `(λ.λ.1) c → λ.c` (nested binder + `shiftk`). Seed `^subst(Z, c, ^lambda(^bound (S Z)))`.
/// Trace: descend under λ (depth `Z → S Z`); `subst(S Z, c, bound(S Z))` → `cmp(S Z,S Z)=Eq` →
/// `shiftk(S Z, c) = shift(Z, shiftk(Z, c)) = shift(Z, c) = c` (c is `free`, inert under shift).
/// NF = `λ.c = ("lambda", ("free","c"))`. This is the C1 depth-increment witness.
#[tokio::test]
async fn case2_nested_binder_subst_reduces_with_shiftk() {
    let seed = r#"subst!("Z", ("free", "c"), ("lambda", ("bound", ("S", "Z"))), *result)"#;
    let observed = run_to_nf(&trs_program(seed)).await;
    println!("case2 NF = {observed:?}");
    assert_eq!(
        observed,
        vec![lambda(free("c"))],
        "(λ.λ.1) c must reduce to λ.c — depth increment + shiftk cascade fired on the reducer"
    );
}

/// Case 3 — the WIDENING (multi-nested-site). Seed `^subst(Z, a, f(^bound Z, ^bound Z))`.
/// The object-descent rule `subst(j,a,f(t1,t2)) → f(subst(j,a,t1), subst(j,a,t2))` creates TWO
/// sibling subst redexes (exactly the red-team's `NestedEntryMultiSite` trigger). Both fire as
/// parallel COMMs against the one persistent `subst` receiver and co-reduce in the SAME run:
/// each `subst(Z, a, bound Z) → a`. NF = `f(a, a) = ("f", ("free","a"), ("free","a"))`.
#[tokio::test]
async fn case3_object_descent_widening_two_sibling_substs_coreduce() {
    let seed =
        r#"subst!("Z", ("free", "a"), ("f", ("bound", "Z"), ("bound", "Z")), *result)"#;
    let observed = run_to_nf(&trs_program(seed)).await;
    println!("case3 NF = {observed:?}");
    assert_eq!(
        observed,
        vec![f2(free("a"), free("a"))],
        "subst descending into f spawned TWO sibling subst redexes that co-reduced to f(a, a)"
    );
}

/// Case 3b — the pre-seeded two-redex variant: `f(^subst(Z,a,^bound Z), ^subst(Z,c,^bound Z))`
/// with the two substs ALREADY present as siblings (distinct arguments a, c), built directly as an
/// `f` whose children are two independent `subst!` cascades joined into `("f", …, …)`. Both
/// distinct subst redexes co-reduce in one run → `f(a, c)`. Complements case 3 (descent-created)
/// with the directly-seeded sibling form.
#[tokio::test]
async fn case3b_two_preseeded_sibling_substs_coreduce() {
    let program = format!(
        "new subst, shift, cmp, shiftk, pred, result, r1, r2 in {{\n{TRS_CONTRACTS} |\n  \
         subst!(\"Z\", (\"free\", \"a\"), (\"bound\", \"Z\"), *r1) |\n  \
         subst!(\"Z\", (\"free\", \"c\"), (\"bound\", \"Z\"), *r2) |\n  \
         for (@s1 <- r1 & @s2 <- r2) {{ result!((\"f\", s1, s2)) }} |\n  \
         for (@nf <- result) {{ @\"OUT\"!(nf) }}\n}}\n"
    );
    let observed = run_to_nf(&program).await;
    println!("case3b NF = {observed:?}");
    assert_eq!(
        observed,
        vec![f2(free("a"), free("c"))],
        "two directly-seeded sibling subst redexes co-reduced to f(a, c) in one run"
    );
}
