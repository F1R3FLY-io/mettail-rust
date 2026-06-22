(*
 * HindleyMilnerWiringSound: soundness of WIRING the hindley_milner base-sort
 * consistency pass into the analysis layer (OSLF Phase 6 wiring lemma).
 *
 * The Rust `hindley_milner::analyze_from_bundle` re-derives each constructor's
 * principal ARROW type from its field sorts (`HmType::Arrow` over `HmType::Mono`)
 * and checks the inferred result sort `unify`s with the DECLARED `rule.category`;
 * a disagreement is surfaced as the HM01 sort-mismatch lint (a Note). The pass
 * uses ONLY `Mono`/`Arrow` (no `HmTerm`, no fresh type variables), so HM's
 * `unify` on two base sorts is exact decidable equality (no subtyping —
 * hindley_milner.rs:216).
 *
 * This file certifies the two wiring properties the pass relies on, mirroring the
 * shipped Martelli-Montanari facts of `formal/rocq/unification/theories/
 * UnificationSoundness.v` (const-clash unsatisfiability) but self-contained over
 * the two-sort (Mono/Arrow) restriction:
 *
 *   - hm_principal_arrow_wf : a constructor's inferred arrow, applied to arguments
 *       of ITS OWN declared field sorts, yields its declared result sort
 *       (inference is consistent with the declaration on a well-formed grammar —
 *       why the pass is inert on every real grammar).
 *   - hm_consistency_exact  : base-sort unify succeeds iff the sorts are EQUAL
 *       (HM has no subtyping).
 *   - hm01_lint_sound       : a sort-mismatch verdict (unify fails) implies the
 *       declared and inferred sorts genuinely differ — the HM01 note never fires
 *       on agreeing sorts (soundness of the dead/mismatch lint).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
Import ListNotations.

(* Base sorts are identified by a nat (the category index). *)
Inductive Sort : Type := S_id (n : nat).

Definition mono_eqb (a b : Sort) : bool :=
  match a, b with
  | S_id m, S_id n => Nat.eqb m n
  end.

(* A constructor's inferred principal type: its field (argument) sorts and its
   result sort. The Rust arrow `S1 -> ... -> Sn -> R` is this pair. *)
Record CtorType : Type := { arg_sorts : list Sort; result_sort : Sort }.

(* Pointwise sort agreement of formals vs actuals (the `unify` of a Mono arrow
   spine, with no subtyping). *)
Fixpoint sorts_match (formals actuals : list Sort) : bool :=
  match formals, actuals with
  | [], [] => true
  | f :: fs, a :: bs => mono_eqb f a && sorts_match fs bs
  | _, _ => false
  end.

(* Applying the constructor's arrow to actual argument sorts: yields the result
   sort iff the actuals match the formals. *)
Definition apply_ctor (ct : CtorType) (actuals : list Sort) : option Sort :=
  if sorts_match (arg_sorts ct) actuals then Some (result_sort ct) else None.

(* ── helpers ─────────────────────────────────────────────────────────────── *)

Lemma mono_eqb_refl : forall s, mono_eqb s s = true.
Proof. intros [n]. simpl. apply Nat.eqb_refl. Qed.

Lemma sorts_match_refl : forall l, sorts_match l l = true.
Proof.
  induction l as [| s ss IH]; simpl.
  - reflexivity.
  - rewrite mono_eqb_refl. simpl. exact IH.
Qed.

(* ── wiring soundness ────────────────────────────────────────────────────── *)

(* A constructor's inferred arrow, applied to arguments of its own declared field
   sorts, yields its declared result sort: inference agrees with the declaration
   on a well-formed grammar (so the pass is inert — no mismatch — on every real
   grammar, whose field sorts ARE the declared ones). *)
Theorem hm_principal_arrow_wf : forall ct : CtorType,
  apply_ctor ct (arg_sorts ct) = Some (result_sort ct).
Proof.
  intro ct. unfold apply_ctor. rewrite sorts_match_refl. reflexivity.
Qed.

(* Base-sort unify is EXACT equality (no subtyping): it succeeds iff the sorts
   are equal. *)
Theorem hm_consistency_exact : forall declared inferred : Sort,
  mono_eqb declared inferred = true -> declared = inferred.
Proof.
  intros [m] [n] H. simpl in H. apply Nat.eqb_eq in H. subst. reflexivity.
Qed.

(* The HM01 sort-mismatch lint soundness: a mismatch verdict (unify fails) implies
   the declared and inferred sorts genuinely differ — the note never fires on
   agreeing sorts. *)
Theorem hm01_lint_sound : forall declared inferred : Sort,
  mono_eqb declared inferred = false -> declared <> inferred.
Proof.
  intros [m] [n] H Heq. injection Heq as Heq. subst.
  rewrite mono_eqb_refl in H. discriminate.
Qed.

Print Assumptions hm_principal_arrow_wf.
Print Assumptions hm_consistency_exact.
Print Assumptions hm01_lint_sound.
