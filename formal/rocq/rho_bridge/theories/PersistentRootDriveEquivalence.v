(*
 * PersistentRootDriveEquivalence: the certified production R3 root driver is
 * equivalent to both the bounded recursive root oracle and the already-proved
 * general in-Rho quiescence driver on its complete admitted envelope.
 *
 * The Rust certificate admits exactly a positive spine
 *
 *   App((lambda. bound 0), ... App((lambda. bound 0), tail) ...)
 *
 * whose terminal tail is beta-normal.  One persistent pattern-guard COMM removes
 * one spine cell.  Consequently the exact contraction count is a ranking
 * function, not an artificial traversal limit.  This file makes that argument
 * executable in Rocq and connects it to InRhoQuiescenceDriver.drives.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions, no Parameters.
 *)

From Stdlib Require Import List PeanoNat.
From RhoBridge Require Import DeBruijnSubstTRS InRhoQuiescenceDriver.

Import ListNotations.

Section PersistentRootDriveEquivalence.

  Variable app : nat.

  Definition identity_redex (argument : Obj) : Obj :=
    oNode app [oLam (oBound 0); argument].

  Fixpoint identity_spine (contractions : nat) (tail : Obj) : Obj :=
    match contractions with
    | O => tail
    | S remaining => identity_redex (identity_spine remaining tail)
    end.

  (* The historical recursive equation, retained only as the bounded oracle. *)
  Fixpoint recursive_root_oracle (fuel : nat) (term : Obj) : Obj :=
    match fuel with
    | O => term
    | S remaining =>
        match term with
        | oNode op' [oLam (oBound 0); argument] =>
            if Nat.eqb op' app
            then recursive_root_oracle remaining argument
            else term
        | _ => term
        end
    end.

  (* One visible R3 accept/firing.  The generated implementation keeps the
     pattern-guard receivers persistent and republishes the contractum, so a
     complete execution is the counted reflexive-transitive closure below. *)
  Inductive persistent_root_step : Obj -> Obj -> Prop :=
    | persistent_identity_fire : forall argument,
        persistent_root_step (identity_redex argument) argument.

  Inductive persistent_root_run : nat -> Obj -> Obj -> Prop :=
    | persistent_root_done : forall term,
        persistent_root_run 0 term term
    | persistent_root_more : forall n term next result,
        persistent_root_step term next ->
        persistent_root_run n next result ->
        persistent_root_run (S n) term result.

  Lemma identity_beta_is_argument : forall argument,
    odbeta argument (oBound 0) = argument.
  Proof.
    intro argument. unfold odbeta. simpl. reflexivity.
  Qed.

  Lemma recursive_oracle_consumes_certified_spine : forall n tail,
    recursive_root_oracle n (identity_spine n tail) = tail.
  Proof.
    induction n as [| n IH]; intro tail; simpl.
    - reflexivity.
    - rewrite Nat.eqb_refl. apply IH.
  Qed.

  Lemma persistent_run_consumes_certified_spine : forall n tail,
    persistent_root_run n (identity_spine n tail) tail.
  Proof.
    induction n as [| n IH]; intro tail; simpl.
    - apply persistent_root_done.
    - eapply persistent_root_more.
      + apply persistent_identity_fire.
      + apply IH.
  Qed.

  Lemma persistent_root_step_deterministic : forall term left right,
    persistent_root_step term left ->
    persistent_root_step term right ->
    left = right.
  Proof.
    intros term left right Hleft Hright.
    inversion Hleft; inversion Hright; subst.
    unfold identity_redex in *. congruence.
  Qed.

  Lemma persistent_root_run_deterministic : forall n term left right,
    persistent_root_run n term left ->
    persistent_root_run n term right ->
    left = right.
  Proof.
    intros n term left right Hleft.
    generalize dependent right.
    induction Hleft as [term | n term next left Hstep Hrun IH];
      intros right Hright.
    - inversion Hright. reflexivity.
    - inversion Hright as [| n' term' next' right' Hstep' Hrun']; subst.
      assert (Hnext : next = next') by
        (eapply persistent_root_step_deterministic; eassumption).
      subst next'. eapply IH. exact Hrun'.
  Qed.

  (* A beta-normal tail is passed through unchanged even at fuel zero.  This is
     the bridge from the persistent root-only relation to the existing general
     driver's arm-by-arm model. *)
  Lemma general_driver_preserves_nf_at_zero : forall tail,
    lam_nf app tail -> drives app 0 tail (DDone tail).
  Proof.
    intros tail Hnf. induction Hnf as
      [x | n | body Hbody IHbody | left right Hleft IHleft Hright IHright Hhead].
    - apply d_free.
    - apply d_bound.
    - apply d_lam_done. exact IHbody.
    - eapply d_descend_done.
      + unfold not_beta_redex. intros body argument Heq.
        inversion Heq; subst. apply (Hhead body). reflexivity.
      + exact IHleft.
      + exact IHright.
      + apply rc_done. unfold not_beta_redex. intros body argument Heq.
        inversion Heq; subst. apply (Hhead body). reflexivity.
  Qed.

  Lemma general_driver_consumes_certified_spine : forall n tail,
    lam_nf app tail ->
    drives app n (identity_spine n tail) (DDone tail).
  Proof.
    induction n as [| n IH]; intros tail Hnf; simpl.
    - apply general_driver_preserves_nf_at_zero. exact Hnf.
    - apply d_redex_fire. rewrite identity_beta_is_argument. apply IH. exact Hnf.
  Qed.

  (* The generated certificate's exact admitted envelope gives the same result
     in all three semantics. *)
  Theorem certified_persistent_recursive_general_equivalence : forall n tail,
    lam_nf app tail ->
    persistent_root_run n (identity_spine n tail) tail
    /\ recursive_root_oracle n (identity_spine n tail) = tail
    /\ drives app n (identity_spine n tail) (DDone tail).
  Proof.
    intros n tail Hnf. repeat split.
    - apply persistent_run_consumes_certified_spine.
    - apply recursive_oracle_consumes_certified_spine.
    - apply general_driver_consumes_certified_spine. exact Hnf.
  Qed.

  (* The exact count is observable: if a counted persistent run over a certified
     spine reaches any result, determinism forces that result to be the tail. *)
  Theorem certified_run_has_unique_result : forall n tail result,
    persistent_root_run n (identity_spine n tail) result -> result = tail.
  Proof.
    intros n tail result Hrun.
    eapply persistent_root_run_deterministic.
    - exact Hrun.
    - apply persistent_run_consumes_certified_spine.
  Qed.

  (* Non-vacuity: two different persistent accepts really occur before the tail
     is returned, matching the production identity-chain regression. *)
  Theorem persistent_two_fire_nonvacuous : forall x,
    persistent_root_run 2 (identity_spine 2 (oFree x)) (oFree x)
    /\ identity_spine 2 (oFree x) <> oFree x.
  Proof.
    intro x. split.
    - apply persistent_run_consumes_certified_spine.
    - simpl. discriminate.
  Qed.

End PersistentRootDriveEquivalence.

Print Assumptions certified_persistent_recursive_general_equivalence.
Print Assumptions certified_run_has_unique_result.
Print Assumptions persistent_two_fire_nonvacuous.
