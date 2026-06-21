(*
 * MettaOslfLawsConformance: MeTTaIL's OSLF resource logic (`MettaResourceLogic`,
 * rholang-adapter) satisfies the four OSLF linear-resource-logic conformance
 * laws — the SECOND instance of the funding-soundness capstone (after
 * f1r3node-rust's `DefaultResourceLogic` / `RhoGslt`), the way `CAUntypedLambda.v`
 * is a second instance of `GSLTOSLFCapstone.v`.
 *
 * `MettaResourceLogic` DELEGATES `is_funded` to the verified
 * `delta_sigma::is_funded`, which on a fully-resolvable demand computes
 *   is_funded(Δ, Σ, margin) = (Δ + margin ≤ Σ)
 * (f1r3node-rust rholang/.../accounting/delta_sigma.rs:479). This file models that
 * exact decision procedure and proves the four laws the host's `#[cfg(test)]`
 * conformance harness checks (resource_logic.rs:137-200), which the mettail-side
 * re-hosted kit (rholang-adapter `conformance.rs`, decision B1-a) runs against
 * `MettaResourceLogic`:
 *   - law_sound            : funded iff Σ ≥ Δ + margin           (decidable funds)
 *   - law_reject_underfunded : positive demand vs zero supply rejected
 *   - law_supply_monotone  : more supply never un-funds (no contraction)
 *   - law_decidable        : the judgment is total (a verdict always exists)
 *
 * These mirror, and are justified by, the Qed-closed f1r3node-rust lemmas
 * `LinearLogicResources.v::{funds, funding_decidable, strict_reject_when_underfunded,
 * ll_linear_no_contraction}` — re-stated here over the modelled decision procedure
 * (cross-repo `Require Import` is not wired; the reuse is by faithful re-statement
 * + citation, the same "second instance" discipline as `CAUntypedLambda.v`).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Section MettaOslfLaws.

  (* The funding decision `delta_sigma::is_funded` computes for a resolvable demand
     `lb` (= Δ), supply `supply` (= Σ_s), and shard `margin`:
     `required := lb + margin; supply >= required`. We model it as a boolean
     decision procedure over the naturals (the law grid uses non-negative values;
     the host uses i128 internally only to avoid overflow). *)
  Definition is_funded (lb supply margin : nat) : bool :=
    Nat.leb (lb + margin) supply.

  (* Law (sound proof-checker, both directions): funded iff Σ ≥ Δ + margin. *)
  Theorem law_sound : forall lb supply margin,
    is_funded lb supply margin = true <-> lb + margin <= supply.
  Proof.
    intros lb supply margin. unfold is_funded. apply Nat.leb_le.
  Qed.

  (* Law (reject underfunded): a positive demand against zero supply at zero margin
     is rejected (the image of `strict_reject_when_underfunded`). *)
  Theorem law_reject_underfunded : forall lb,
    0 < lb -> is_funded lb 0 0 = false.
  Proof.
    intros lb H. unfold is_funded. apply Nat.leb_gt. lia.
  Qed.

  (* Law (no contraction / supply monotone): increasing supply never turns a
     funded demand UNfunded (the image of `ll_linear_no_contraction`). *)
  Theorem law_supply_monotone : forall lb supply margin,
    is_funded lb supply margin = true -> is_funded lb (S supply) margin = true.
  Proof.
    intros lb supply margin H. unfold is_funded in *.
    apply Nat.leb_le. apply Nat.leb_le in H. lia.
  Qed.

  (* Law (decidable): the funding judgment is total — a verdict always exists. *)
  Theorem law_decidable : forall lb supply margin,
    is_funded lb supply margin = true \/ is_funded lb supply margin = false.
  Proof.
    intros lb supply margin. destruct (is_funded lb supply margin).
    - left. reflexivity.
    - right. reflexivity.
  Qed.

  (* The capstone (cf. `cost_accounted_calculus_is_gslt_with_oslf_logic`):
     MeTTaIL's delegating resource logic is a sound OSLF funding proof checker. *)
  Theorem metta_resource_logic_is_oslf_sound :
    (forall lb supply margin, is_funded lb supply margin = true <-> lb + margin <= supply)
    /\ (forall lb, 0 < lb -> is_funded lb 0 0 = false)
    /\ (forall lb supply margin,
          is_funded lb supply margin = true -> is_funded lb (S supply) margin = true)
    /\ (forall lb supply margin,
          is_funded lb supply margin = true \/ is_funded lb supply margin = false).
  Proof.
    split. { exact law_sound. }
    split. { exact law_reject_underfunded. }
    split. { exact law_supply_monotone. }
    exact law_decidable.
  Qed.

End MettaOslfLaws.
