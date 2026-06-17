(*
 * DovetailSaturation: abstract rules-as-data saturation obligations.
 *
 * The executable engine stores exact e-classes/e-nodes, then rule saturation
 * only adds equalities or rewrites; budget and iteration exhaustion are explicit
 * outcomes.
 * This file proves the abstract obligations Dovetail relies on:
 *   - one saturation step is monotone;
 *   - iterated saturation is monotone;
 *   - if generated facts are sound, saturation preserves soundness;
 *   - bounded execution reports exactly one terminal outcome: converged,
 *     node-limit, or iteration-limit.
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

  Inductive SaturationOutcome : Type :=
    | Converged
    | NodeLimit
    | IterationLimit.

  Record SatStats : Type := {
    sat_iterations : nat;
    sat_total_merges : nat
  }.

  Record SatReport : Type := {
    sat_outcome : SaturationOutcome;
    sat_stats : SatStats;
    sat_state : State
  }.

  Inductive SaturationResult : Type :=
    | Saturated : State -> SaturationResult
    | SaturationBudgetOverflow : State -> SaturationResult
    | SaturationIterationExhausted : State -> SaturationResult.

  Definition outcome_of (r : SaturationResult) : SaturationOutcome :=
    match r with
    | Saturated _ => Converged
    | SaturationBudgetOverflow _ => NodeLimit
    | SaturationIterationExhausted _ => IterationLimit
    end.

  Definition state_of (r : SaturationResult) : State :=
    match r with
    | Saturated s => s
    | SaturationBudgetOverflow s => s
    | SaturationIterationExhausted s => s
    end.

  (* `fuel` is the abstract number of iterations required to reach a fixpoint.
     `budget` is the first iteration at which a fresh-node refusal occurs.
     `max_iters` is the Rust caller's iteration cap. Node budget wins ties,
     matching `rules.rs`, where budget is checked inside the iteration body
     before the loop can return `IterationLimit`. *)
  Definition bounded_saturate
    (fuel budget max_iters : nat) (generated : State) (s : State)
    : SaturationResult :=
    if fuel <=? budget then
      if fuel <=? max_iters
      then Saturated (saturate_n fuel generated s)
      else SaturationIterationExhausted (saturate_n max_iters generated s)
    else if budget <=? max_iters
      then SaturationBudgetOverflow (saturate_n budget generated s)
      else SaturationIterationExhausted (saturate_n max_iters generated s).

  Definition bounded_saturate_report
    (fuel budget max_iters merges : nat) (generated : State) (s : State)
    : SatReport :=
    let r := bounded_saturate fuel budget max_iters generated s in
    {|
      sat_outcome := outcome_of r;
      sat_stats := {|
        sat_iterations :=
          match r with
          | Saturated _ => fuel
          | SaturationBudgetOverflow _ => budget
          | SaturationIterationExhausted _ => max_iters
          end;
        sat_total_merges := merges
      |};
      sat_state := state_of r
    |}.

  Theorem bounded_saturate_reports_overflow :
    forall fuel budget max_iters generated s out,
    budget < fuel ->
    budget <= max_iters ->
    bounded_saturate fuel budget max_iters generated s =
      SaturationBudgetOverflow out ->
    out = saturate_n budget generated s.
  Proof.
    intros fuel budget max_iters generated s out Hlt Hbudget_first Hres.
    unfold bounded_saturate in Hres.
    destruct (fuel <=? budget) eqn:Hle.
    - apply Nat.leb_le in Hle. lia.
    - destruct (budget <=? max_iters) eqn:Hbudget.
      + inversion Hres. reflexivity.
      + apply Nat.leb_gt in Hbudget. lia.
  Qed.

  Theorem bounded_saturate_reports_iteration_limit :
    forall fuel budget max_iters generated s out,
    max_iters < fuel ->
    max_iters < budget ->
    bounded_saturate fuel budget max_iters generated s =
      SaturationIterationExhausted out ->
    out = saturate_n max_iters generated s.
  Proof.
    intros fuel budget max_iters generated s out Hfuel Hbudget Hres.
    unfold bounded_saturate in Hres.
    destruct (fuel <=? budget) eqn:Hle.
    - destruct (fuel <=? max_iters) eqn:Hfuel_le.
      + apply Nat.leb_le in Hfuel_le. lia.
      + inversion Hres. reflexivity.
    - destruct (budget <=? max_iters) eqn:Hbudget_le.
      + apply Nat.leb_le in Hbudget_le. lia.
      + inversion Hres. reflexivity.
  Qed.

  Theorem bounded_saturate_reports_converged :
    forall fuel budget max_iters generated s out,
    fuel <= budget ->
    fuel <= max_iters ->
    bounded_saturate fuel budget max_iters generated s = Saturated out ->
    out = saturate_n fuel generated s.
  Proof.
    intros fuel budget max_iters generated s out Hbudget Hiter Hres.
    unfold bounded_saturate in Hres.
    destruct (fuel <=? budget) eqn:Hbudget_le.
    - destruct (fuel <=? max_iters) eqn:Hiter_le.
      + inversion Hres. reflexivity.
      + apply Nat.leb_gt in Hiter_le. lia.
    - apply Nat.leb_gt in Hbudget_le. lia.
  Qed.

  Theorem report_outcome_matches_result :
    forall fuel budget max_iters merges generated s,
    sat_outcome (bounded_saturate_report fuel budget max_iters merges generated s) =
      outcome_of (bounded_saturate fuel budget max_iters generated s).
  Proof. intros. reflexivity. Qed.

  Theorem report_state_matches_result :
    forall fuel budget max_iters merges generated s,
    sat_state (bounded_saturate_report fuel budget max_iters merges generated s) =
      state_of (bounded_saturate fuel budget max_iters generated s).
  Proof. intros. reflexivity. Qed.

  Theorem node_limit_report_is_not_converged : forall stats st,
    sat_outcome {| sat_outcome := NodeLimit; sat_stats := stats; sat_state := st |} <> Converged.
  Proof. intros stats st H. discriminate. Qed.

  Theorem iteration_limit_report_is_not_converged : forall stats st,
    sat_outcome {| sat_outcome := IterationLimit; sat_stats := stats; sat_state := st |} <> Converged.
  Proof. intros stats st H. discriminate. Qed.

  Theorem converged_report_has_converged_outcome : forall stats st,
    sat_outcome {| sat_outcome := Converged; sat_stats := stats; sat_state := st |} = Converged.
  Proof. reflexivity. Qed.

  (* ======================================================================= *)
  (* Native-fold reduction (Increment 3): the native dispatcher adds, for a   *)
  (* fold redex e-class `redex` whose native body computes the result e-class *)
  (* `result`, the equality fact `EqFact redex result`. The ONE trust boundary*)
  (* — that this computed equality is GSLT-valid — is modeled as a PREMISE     *)
  (* `good (native_fact redex result)`, threaded through the soundness         *)
  (* theorems, NOT as an `Axiom` (per the project's zero-admission rule).      *)
  (* ======================================================================= *)

  Definition native_fact (redex result : nat) : Fact := EqFact redex result.

  Definition native_generated (redex result : nat) : State :=
    fun f => f = native_fact redex result.

  (* Given the native-soundness premise, the native-generated state is sound. *)
  Theorem native_generated_sound : forall good redex result,
    good (native_fact redex result) ->
    sound_state good (native_generated redex result).
  Proof.
    unfold sound_state, native_generated. intros good redex result Hgood f Hf.
    subst f. exact Hgood.
  Qed.

  (* Saturating a sound state with a sound native fold preserves soundness:    *)
  (* the saturation/native bridge, composing `saturate_n_sound` with the       *)
  (* native-soundness premise.                                                 *)
  Theorem native_fold_saturation_sound : forall n good s redex result,
    sound_state good s ->
    good (native_fact redex result) ->
    sound_state good (saturate_n n (native_generated redex result) s).
  Proof.
    intros n good s redex result Hs Hgood.
    apply saturate_n_sound; [exact Hs |].
    apply native_generated_sound. exact Hgood.
  Qed.

  (* `native_refire_is_noop`: a re-fired fold whose result equality is already *)
  (* present adds nothing — the step is a no-op as a set. The folded normal     *)
  (* form (a `Cast*` literal) re-matches no fold LHS, so a re-fire produces the *)
  (* SAME already-present equality and the state does not grow.                *)
  Theorem native_refire_is_noop : forall s redex result,
    s (native_fact redex result) ->
    subset (saturate_step s (native_generated redex result)) s.
  Proof.
    unfold subset, saturate_step, union_state, native_generated.
    intros s redex result Hin f [Hf | Hf].
    - exact Hf.
    - subst f. exact Hin.
  Qed.

  Theorem native_refire_state_unchanged : forall s redex result,
    s (native_fact redex result) ->
    subset s (saturate_step s (native_generated redex result)) /\
    subset (saturate_step s (native_generated redex result)) s.
  Proof.
    intros s redex result Hin. split.
    - apply saturate_step_monotone.
    - apply native_refire_is_noop. exact Hin.
  Qed.

  (* ======================================================================= *)
  (* OSLF funding bridge: a fold transition is funded iff its demand `delta`   *)
  (* plus a `margin` fits the supply `sigma` (the node budget Sigma). This is  *)
  (* the OSLF `is_funded` realized at the saturation budget, with its laws.    *)
  (* ======================================================================= *)

  Definition fold_transition_funded (delta margin sigma : nat) : bool :=
    delta + margin <=? sigma.

  (* OSLF law `sound`: funded iff supply meets demand + margin. *)
  Theorem fold_funding_sound : forall delta margin sigma,
    fold_transition_funded delta margin sigma = true <-> delta + margin <= sigma.
  Proof. intros. unfold fold_transition_funded. apply Nat.leb_le. Qed.

  (* OSLF law `supply-monotone` (no-contraction): more supply never un-funds. *)
  Theorem fold_funding_supply_monotone : forall delta margin sigma sigma',
    sigma <= sigma' ->
    fold_transition_funded delta margin sigma = true ->
    fold_transition_funded delta margin sigma' = true.
  Proof.
    intros delta margin sigma sigma' Hle Hfund.
    apply fold_funding_sound in Hfund. apply fold_funding_sound. lia.
  Qed.

  (* OSLF law `reject-underfunded`: positive demand against zero supply refused. *)
  Theorem fold_funding_rejects_underfunded : forall delta margin,
    0 < delta ->
    fold_transition_funded delta margin 0 = false.
  Proof.
    intros delta margin Hpos. unfold fold_transition_funded.
    apply Nat.leb_gt. lia.
  Qed.

  Theorem funded_fold_demand_within_supply : forall delta margin sigma,
    fold_transition_funded delta margin sigma = true ->
    delta <= sigma.
  Proof.
    intros delta margin sigma Hfund. apply fold_funding_sound in Hfund. lia.
  Qed.

  (* Funding-to-saturation bridge: a funded fold transition (demand within the *)
  (* supply Sigma) saturates within budget — taking the fold's demand `delta`   *)
  (* as the fuel, the bounded saturation reaches `Saturated`, never            *)
  (* `SaturationBudgetOverflow`.                                               *)
  Theorem funded_fold_saturates_within_budget :
    forall delta margin sigma max_iters generated s,
    fold_transition_funded delta margin sigma = true ->
    delta <= max_iters ->
    exists out, bounded_saturate delta sigma max_iters generated s = Saturated out.
  Proof.
    intros delta margin sigma max_iters generated s Hfund Hiter.
    apply funded_fold_demand_within_supply in Hfund.
    unfold bounded_saturate.
    apply Nat.leb_le in Hfund. apply Nat.leb_le in Hiter.
    rewrite Hfund, Hiter. eexists. reflexivity.
  Qed.

End DovetailSaturation.
