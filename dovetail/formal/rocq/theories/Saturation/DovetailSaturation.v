(*
 * DovetailSaturation: abstract rules-as-data saturation obligations.
 *
 * The executable engine stores exact e-classes/e-nodes, then rule saturation
 * only adds equalities or rewrites; budget exhaustion is an explicit outcome.
 * This file proves the abstract obligations Dovetail relies on:
 *   - one saturation step is monotone;
 *   - iterated saturation is monotone;
 *   - if generated facts are sound, saturation preserves soundness;
 *   - bounded execution reports either the saturated state or a budget overflow.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Import ListNotations.

Section DovetailSaturation.

  Inductive Fact : Type :=
    | EqFact : nat -> nat -> Fact
    | RwFact : nat -> nat -> Fact.

  Definition State : Type := Fact -> Prop.

  Definition subset (s t : State) : Prop :=
    forall f, s f -> t f.

  Definition union_state (s generated : State) : State :=
    fun f => s f \/ generated f.

  Definition sound_state (good : Fact -> Prop) (s : State) : Prop :=
    forall f, s f -> good f.

  Definition saturate_step (s generated : State) : State :=
    union_state s generated.

  Lemma subset_refl : forall s, subset s s.
  Proof. unfold subset. auto. Qed.

  Lemma subset_trans : forall a b c,
    subset a b -> subset b c -> subset a c.
  Proof.
    unfold subset. intros a b c Hab Hbc f Hf. apply Hbc. apply Hab. exact Hf.
  Qed.

  Theorem saturate_step_monotone : forall s generated,
    subset s (saturate_step s generated).
  Proof.
    unfold subset, saturate_step, union_state. intros s generated f Hf. left. exact Hf.
  Qed.

  Theorem saturate_step_sound : forall good s generated,
    sound_state good s ->
    sound_state good generated ->
    sound_state good (saturate_step s generated).
  Proof.
    unfold sound_state, saturate_step, union_state.
    intros good s generated Hs Hg f Hf.
    destruct Hf as [Hf | Hf].
    - apply Hs. exact Hf.
    - apply Hg. exact Hf.
  Qed.

  Fixpoint saturate_n (n : nat) (generated : State) (s : State) : State :=
    match n with
    | O => s
    | S n' => saturate_n n' generated (saturate_step s generated)
    end.

  Theorem saturate_n_monotone : forall n generated s,
    subset s (saturate_n n generated s).
  Proof.
    induction n as [| n IH]; intros generated s.
    - apply subset_refl.
    - simpl. apply subset_trans with (b := saturate_step s generated).
      + apply saturate_step_monotone.
      + apply IH.
  Qed.

  Theorem saturate_n_sound : forall n good generated s,
    sound_state good s ->
    sound_state good generated ->
    sound_state good (saturate_n n generated s).
  Proof.
    induction n as [| n IH]; intros good generated s Hs Hg.
    - exact Hs.
    - simpl. apply IH.
      + apply saturate_step_sound; assumption.
      + exact Hg.
  Qed.

  Inductive SaturationResult : Type :=
    | Saturated : State -> SaturationResult
    | SaturationBudgetOverflow : State -> SaturationResult.

  Definition bounded_saturate (fuel budget : nat) (generated : State) (s : State)
    : SaturationResult :=
    if fuel <=? budget
    then Saturated (saturate_n fuel generated s)
    else SaturationBudgetOverflow (saturate_n budget generated s).

  Theorem bounded_saturate_reports_overflow : forall fuel budget generated s out,
    budget < fuel ->
    bounded_saturate fuel budget generated s = SaturationBudgetOverflow out ->
    out = saturate_n budget generated s.
  Proof.
    intros fuel budget generated s out Hlt Hres.
    unfold bounded_saturate in Hres.
    destruct (fuel <=? budget) eqn:Hle.
    - apply Nat.leb_le in Hle. lia.
    - inversion Hres. reflexivity.
  Qed.

End DovetailSaturation.
