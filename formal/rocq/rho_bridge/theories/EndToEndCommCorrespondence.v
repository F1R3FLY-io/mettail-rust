(*
 * EndToEndCommCorrespondence: the per-step Rho COMM correspondence lifts to a
 * full FINITE-TRACE correspondence (pgmcp #1956 Epic 8 — the end-to-end opcorr
 * obligation).
 *
 * The knotted-topoi paper states operational correspondence as a bisimulation of
 * context-labelled transition systems (Proposition/Obligation "opcorr"). Its
 * implementation image discharges this PER STEP: `LinearCommCorrespondence.v` and
 * `CommReductionCorrespondence.v` prove that a single lowered Rho COMM step is
 * matched by a source COMM step (and conversely) with the same observable barbs.
 * What remained open (flagged in docs/architecture/rho-native-integration/13 §6)
 * is the END-TO-END lift: a whole reduction SEQUENCE corresponds, not just one step.
 *
 * This theory closes that gap at the level of labelled transition systems: GIVEN a
 * relation `R` that is a step-wise bisimulation with matching barbs (exactly what
 * the per-step correspondence establishes for the COMM lowering), R lifts to
 * finite traces — every source trace from a related state is matched by a lowered
 * trace with the same labels, ending in related states with equal barbs, and
 * conversely. Composed with the concrete per-step `R` of `LinearCommCorrespondence.v`,
 * this yields the paper's finite-execution operational correspondence.
 *
 * `R`, `step`, `barb`, and the bisimulation conditions are section parameters
 * (universally quantified when the section closes), so the theorems are
 * assumption-free (`Print Assumptions` reports "Closed under the global context").
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
Import ListNotations.

Section EndToEndCommCorrespondence.

  (* A state is a whole program configuration; a label is a context-labelled COMM
     event c(ℓ); an observation is the barb (resting sends on the out channels). *)
  Variable State Label Obs : Type.
  Variable step : State -> Label -> State -> Prop.
  Variable barb : State -> Obs.

  (* The per-step correspondence relation (concretely: source config ~ lowered
     config). *)
  Variable R : State -> State -> Prop.

  (* R is a step-wise bisimulation with matching barbs — the exact content of the
     per-step opcorr proofs. *)
  Hypothesis R_barb : forall s t, R s t -> barb s = barb t.
  Hypothesis R_forward : forall s t l s',
    R s t -> step s l s' -> exists t', step t l t' /\ R s' t'.
  Hypothesis R_backward : forall s t l t',
    R s t -> step t l t' -> exists s', step s l s' /\ R s' t'.

  (* Finite label-indexed multi-step reduction. *)
  Inductive steps : State -> list Label -> State -> Prop :=
    | steps_nil : forall s, steps s [] s
    | steps_cons : forall s l s' ls s'',
        step s l s' -> steps s' ls s'' -> steps s (l :: ls) s''.

  (* FORWARD: a source trace is matched by a lowered trace with the same labels,
     ending in related states with equal barbs. *)
  Theorem forward_trace_correspondence : forall s t ls s',
    R s t -> steps s ls s' ->
    exists t', steps t ls t' /\ R s' t' /\ barb s' = barb t'.
  Proof.
    intros s t ls s' HR Hsteps. revert t HR.
    induction Hsteps as [s | s l s0 ls s' Hstep Hsteps IH]; intros t HR.
    - exists t. split; [constructor | split; [exact HR | apply R_barb; exact HR]].
    - destruct (R_forward s t l s0 HR Hstep) as [t0 [Ht0step Ht0R]].
      destruct (IH t0 Ht0R) as [t' [Ht'steps [Ht'R Ht'barb]]].
      exists t'. split.
      + apply steps_cons with (s' := t0); [exact Ht0step | exact Ht'steps].
      + split; [exact Ht'R | exact Ht'barb].
  Qed.

  (* BACKWARD: symmetrically, every lowered trace is matched by a source trace. *)
  Theorem backward_trace_correspondence : forall s t ls t',
    R s t -> steps t ls t' ->
    exists s', steps s ls s' /\ R s' t' /\ barb s' = barb t'.
  Proof.
    intros s t ls t' HR Hsteps. revert s HR.
    induction Hsteps as [t | t l t0 ls t' Hstep Hsteps IH]; intros s HR.
    - exists s. split; [constructor | split; [exact HR | apply R_barb; exact HR]].
    - destruct (R_backward s t l t0 HR Hstep) as [s0 [Hs0step Hs0R]].
      destruct (IH s0 Hs0R) as [s' [Hs'steps [Hs'R Hs'barb]]].
      exists s'. split.
      + apply steps_cons with (s' := s0); [exact Hs0step | exact Hs'steps].
      + split; [exact Hs'R | exact Hs'barb].
  Qed.

  (* Corollary — observable trace equivalence: related states admit the same
     finite label-traces (each direction reaches a barb-equal related state). This
     is the paper's finite-execution operational correspondence. *)
  Theorem finite_trace_barb_equivalence : forall s t ls,
    R s t ->
    (forall s', steps s ls s' -> exists t', steps t ls t' /\ barb s' = barb t') /\
    (forall t', steps t ls t' -> exists s', steps s ls s' /\ barb s' = barb t').
  Proof.
    intros s t ls HR. split.
    - intros s' Hs. destruct (forward_trace_correspondence s t ls s' HR Hs)
        as [t' [Ht' [_ Hbarb]]]. exists t'. split; [exact Ht' | exact Hbarb].
    - intros t' Ht. destruct (backward_trace_correspondence s t ls t' HR Ht)
        as [s' [Hs' [_ Hbarb]]]. exists s'. split; [exact Hs' | exact Hbarb].
  Qed.

End EndToEndCommCorrespondence.

Print Assumptions forward_trace_correspondence.
Print Assumptions backward_trace_correspondence.
Print Assumptions finite_trace_barb_equivalence.
