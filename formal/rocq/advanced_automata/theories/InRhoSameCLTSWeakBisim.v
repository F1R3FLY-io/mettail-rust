(*
 * InRhoSameCLTSWeakBisim: obligation (iii) of the in-Rho matching verification plan
 * (docs 16) — the load-bearing `rem:nonopt` discharge. The in-Rho `sa:`/`eq:`
 * matching COMMs are internal (τ, unobservable), so the SOUND scheme (channel keyed
 * by the runtime LOCATION ℓ) and the OPTIMAL scheme (channel keyed by the interned
 * StateId trace `tc(K)`) induce the SAME context-labelled transition system: they
 * are weakly bisimilar. This is the tex's asserted-but-unproven claim.
 *
 * Discharge chain (plan 16 §3): (ii) O1-totality + (viii) tc-injectivity/R_op ⇒
 * (iii) weak bisimulation. Here `chain_complete` is discharged by `positions_count`
 * (ii, SymbolOnceInjective) and `no_crosstalk` by `tc_sound` (viii,
 * TcChannelNamingQuotient); the sound side's no-cross-talk uses the location
 * injectivity `site_inj` (the `prop:opcorr` premise the term algebra guarantees,
 * discharged as a Hypothesis — the honest-premise pattern of InRhoMatchPositional's
 * `arity_consistent`).
 *
 * Model boundary (plan 16 §0, consistent with Phase A/B): (iii) proves the
 * CHANNEL-SCHEME INDEPENDENCE of the visible CLTS at the schedule / labelled-
 * transition level. It does NOT model rho-calculus reduction (Par/RSpace) — the
 * emitted `Par`'s RSpace-faithfulness is the runtime tests' + (i)'s job, and the
 * whole-⟦G⟧ finite-trace opcorr is (v)'s (via EndToEndCommCorrespondence). The
 * τ/erase backbone mirrors rho_bridge/RhoCommScheduleFamily.v (re-derived locally,
 * ~25 lines, to keep this AdvancedAutomata file's ii/viii imports self-contained).
 *
 * Non-vacuity (the real risk, since @K = quotient at depth-1): the sound scheme is
 * keyed by LOCATION, so two redexes at DIFFERENT locations with the same context
 * get DISTINCT sound channels but the SAME optimal channel — the optimal scheme's
 * cross-location sharing is exactly what is shown invisible. `optimal_shares_where_
 * sound_separates` is the standing witness.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool PeanoNat List.
Import ListNotations.
From AdvancedAutomata Require Import PositionalSetAutomatonSound.
From AdvancedAutomata Require Import SymbolOnceInjective.
From AdvancedAutomata Require Import TcChannelNamingQuotient.
(* is_weak_bisimulation below mirrors RegisterEquivalence.is_bisimulation's two-clause
   shape (cited, not imported — no cross-file dependency needed). *)

(* The outermost op of an M1 context (0 for a non-App, unreachable under m1_pattern). *)
Definition op0 (p : Pat) : nat := match p with PApp o _ => o | _ => 0 end.

Section InRhoSameCLTSWeakBisim.
  Definition Redex := nat.

  (* A CLTS state's enabled redexes, each with its matched M1 context and runtime
     location. Abstract (Section Variables) so the theorems quantify over all firings. *)
  Variable rs : list Redex.
  Variable K : Redex -> Pat.
  Variable site : Redex -> nat.
  Hypothesis K_M1 : forall r, In r rs -> m1_pattern (K r) = true.
  (* The sound (location) channel's injectivity — prop:opcorr / def:loc; the runtime
     term algebra guarantees it, discharged as a Hypothesis (not an Axiom). *)
  Hypothesis site_inj :
    forall r r', In r rs -> In r' rs -> site r = site r' -> r = r'.

  Definition arity_of (r : Redex) : nat :=
    match K r with PApp _ args => length args | _ => 0 end.

  (* ---- τ backbone (mirrors RhoCommScheduleFamily's erase/observation) ---- *)
  Inductive Obs : Type := ObsFire (r : Redex) | ObsComplete.

  (* A matching step, polymorphic in the channel payload C, so the two schemes'
     schedules genuinely DIFFER before erasure yet erase to the same Obs list. *)
  Inductive MatchStep (C : Type) : Type :=
  | Reserve (r : Redex)
  | SaInspect (r : Redex) (c : C)
  | EqCheck (r : Redex) (c : C)
  | Fire (r : Redex)
  | Complete.
  Arguments Reserve {C} r.
  Arguments SaInspect {C} r c.
  Arguments EqCheck {C} r c.
  Arguments Fire {C} r.
  Arguments Complete {C}.

  Definition step_obs {C} (s : MatchStep C) : list Obs :=
    match s with
    | Fire r => [ObsFire r]
    | Complete => [ObsComplete]
    | Reserve _ | SaInspect _ _ | EqCheck _ _ => []   (* sa:/eq: are τ *)
    end.
  Fixpoint erase {C} (l : list (MatchStep C)) : list Obs :=
    match l with [] => [] | s :: t => step_obs s ++ erase t end.

  (* One firing's schedule fragment: Reserve, the sa: inspection chain (τ), then Fire. *)
  Definition frag {C} (ch : Redex -> list C) (r : Redex) : list (MatchStep C) :=
    Reserve r :: map (fun c => SaInspect r c) (ch r) ++ [Fire r].
  Definition sched {C} (ch : Redex -> list C) (order : list Redex) : list (MatchStep C) :=
    flat_map (frag ch) order ++ [Complete].

  Lemma erase_app : forall C (l1 l2 : list (MatchStep C)),
    erase (l1 ++ l2) = erase l1 ++ erase l2.
  Proof.
    intros C l1 l2. induction l1 as [| s t IH]; simpl.
    - reflexivity.
    - rewrite IH, app_assoc. reflexivity.
  Qed.

  Lemma erase_sa_map : forall C (r : Redex) (cs : list C),
    erase (map (fun c => SaInspect r c) cs) = [].
  Proof.
    intros C r cs. induction cs as [| c cs' IH]; simpl; [reflexivity | exact IH].
  Qed.

  Lemma erase_frag : forall C (ch : Redex -> list C) (r : Redex),
    erase (frag ch r) = [ObsFire r].
  Proof.
    intros C ch r. unfold frag. simpl. rewrite erase_app, erase_sa_map. reflexivity.
  Qed.

  Lemma erase_flatmap_frag : forall C (ch : Redex -> list C) (order : list Redex),
    erase (flat_map (frag ch) order) = map ObsFire order.
  Proof.
    intros C ch order. induction order as [| r rest IH].
    - reflexivity.
    - cbn [flat_map map]. rewrite erase_app, erase_frag, IH. reflexivity.
  Qed.

  Lemma erase_sched : forall C (ch : Redex -> list C) (order : list Redex),
    erase (sched ch order) = map ObsFire order ++ [ObsComplete].
  Proof.
    intros C ch order. unfold sched. rewrite erase_app, erase_flatmap_frag. reflexivity.
  Qed.

  (* The two schemes: sound = per-location channels; optimal = per-StateId (trace). *)
  Definition sound_ch (r : Redex) : list Channel :=
    map (chan (site r) (op0 (K r))) (positions (K r)).
  Definition opt_ch (r : Redex) : list (option (nat * nat)) :=
    map (fun _ => trace (K r)) (positions (K r)).

  (* ---- Theorem A: the two schemes have the same visible schedule (τ-erasure) ---- *)
  Theorem optimal_visible_equals_sound : forall order,
    erase (sched opt_ch order) = erase (sched sound_ch order).
  Proof.
    intro order. rewrite !erase_sched. reflexivity.
  Qed.

  (* ---- the weak-step CLTS (tau-then-visible-then-tau) ---- *)
  Definition Cfg := list Redex.

  (* the sa: chain inspects every surface position (the τ*-prefix is complete). *)
  Definition chain_complete {C} (ch : Redex -> list C) (r : Redex) : Prop :=
    length (ch r) = S (arity_of r).
  (* the channel routing is unambiguous: anything sharing r's key fires the same rule. *)
  Definition no_crosstalk (key : Redex -> option (nat * nat)) (r : Redex) : Prop :=
    forall r', In r' rs -> key r' = key r -> op_equiv (K r') (K r) = true.

  Inductive weak_step (C : Type) (ch : Redex -> list C)
      (key : Redex -> option (nat * nat)) : Cfg -> Obs -> Cfg -> Prop :=
  | w_fire : forall f r,
      In r rs -> ~ In r f -> chain_complete ch r -> no_crosstalk key r ->
      weak_step C ch key f (ObsFire r) (r :: f)
  | w_complete : forall f,
      (forall r, In r rs -> In r f) ->
      weak_step C ch key f ObsComplete f.

  Definition sound_key (r : Redex) : option (nat * nat) := Some (site r, op0 (K r)).
  Definition optimal_key (r : Redex) : option (nat * nat) := trace (K r).

  (* the CLTS-state relation: the same fired set. *)
  Definition R (fo fs : Cfg) : Prop := forall r, In r fo <-> In r fs.

  Definition is_weak_bisimulation
      (Rel : Cfg -> Cfg -> Prop) (t1 t2 : Cfg -> Obs -> Cfg -> Prop) : Prop :=
    (forall c1 c2 a c1', Rel c1 c2 -> t1 c1 a c1' -> exists c2', t2 c2 a c2' /\ Rel c1' c2')
    /\ (forall c1 c2 a c2', Rel c1 c2 -> t2 c2 a c2' -> exists c1', t1 c1 a c1' /\ Rel c1' c2').

  Lemma R_cons : forall r c1 c2, R c1 c2 -> R (r :: c1) (r :: c2).
  Proof.
    intros r c1 c2 H x. simpl. split.
    - intros [E | I]; [left; exact E | right; apply (proj1 (H x)); exact I].
    - intros [E | I]; [left; exact E | right; apply (proj2 (H x)); exact I].
  Qed.

  Lemma op_equiv_refl : forall p, m1_pattern p = true -> op_equiv p p = true.
  Proof.
    intros p Hm. destruct p as [| op args | op args]; try discriminate Hm.
    unfold op_equiv. rewrite !Nat.eqb_refl. reflexivity.
  Qed.

  (* ---- provenance: ii ⇒ chain-totality, viii ⇒ no-cross-talk ---- *)

  Lemma m1_is_app : forall p, m1_pattern p = true -> exists op args, p = PApp op args.
  Proof.
    intros p Hm. destruct p as [| op args | op args]; try discriminate Hm.
    exists op, args. reflexivity.
  Qed.

  (* the sa: chain covers all 1+arity positions — SymbolOnceInjective's positions_count (ii). *)
  Lemma optimal_chain_total_from_O1 : forall r,
    m1_pattern (K r) = true -> chain_complete opt_ch r.
  Proof.
    intros r Hm. destruct (m1_is_app (K r) Hm) as [op [args HK]].
    unfold chain_complete, opt_ch, arity_of. rewrite HK, length_map. apply positions_count.
  Qed.

  Lemma sound_chain_total_from_O1 : forall r,
    m1_pattern (K r) = true -> chain_complete sound_ch r.
  Proof.
    intros r Hm. destruct (m1_is_app (K r) Hm) as [op [args HK]].
    unfold chain_complete, sound_ch, arity_of. rewrite HK, length_map. apply positions_count.
  Qed.

  (* distinct R_op contexts get distinct optimal channels — TcChannelNamingQuotient (viii). *)
  Lemma optimal_no_crosstalk_from_tc : forall r, In r rs -> no_crosstalk optimal_key r.
  Proof.
    intros r Hr r' Hr' Hkey. unfold optimal_key in Hkey.
    apply tc_sound; [apply K_M1; exact Hr' | apply K_M1; exact Hr | exact Hkey].
  Qed.

  (* the sound channel is per-location; sharing it forces the same redex — site_inj. *)
  Lemma sound_no_crosstalk_from_site : forall r, In r rs -> no_crosstalk sound_key r.
  Proof.
    intros r Hr r' Hr' Hkey. unfold sound_key in Hkey.
    injection Hkey as Hsite _.
    assert (Hrr : r' = r) by (apply (site_inj r' r Hr' Hr); exact Hsite).
    subst r'. apply op_equiv_refl. apply K_M1. exact Hr.
  Qed.

  (* ---- the two schemes are weakly bisimilar ⇒ same CLTS ---- *)
  Theorem same_clts_weak_bisim :
    is_weak_bisimulation R
      (weak_step (option (nat * nat)) opt_ch optimal_key)
      (weak_step Channel sound_ch sound_key).
  Proof.
    split.
    - (* forward: optimal fires ⇒ sound matches *)
      intros c1 c2 a c1' HR Hstep.
      inversion Hstep as [f r Hrs Hnin Hcc Hnc | f0 Hall]; subst.
      + exists (r :: c2). split.
        * apply w_fire.
          -- exact Hrs.
          -- intro Hin. apply Hnin. apply (proj2 (HR r)). exact Hin.
          -- apply sound_chain_total_from_O1. apply K_M1. exact Hrs.
          -- apply sound_no_crosstalk_from_site. exact Hrs.
        * apply R_cons. exact HR.
      + exists c2. split.
        * apply w_complete. intros r Hr. apply (proj1 (HR r)). apply Hall. exact Hr.
        * exact HR.
    - (* backward: sound fires ⇒ optimal matches *)
      intros c1 c2 a c2' HR Hstep.
      inversion Hstep as [f r Hrs Hnin Hcc Hnc | f0 Hall]; subst.
      + exists (r :: c1). split.
        * apply w_fire.
          -- exact Hrs.
          -- intro Hin. apply Hnin. apply (proj1 (HR r)). exact Hin.
          -- apply optimal_chain_total_from_O1. apply K_M1. exact Hrs.
          -- apply optimal_no_crosstalk_from_tc. exact Hrs.
        * apply R_cons. exact HR.
      + exists c1. split.
        * apply w_complete. intros r Hr. apply (proj2 (HR r)). apply Hall. exact Hr.
        * exact HR.
  Qed.

End InRhoSameCLTSWeakBisim.

(* ---- non-vacuity: the optimal scheme SHARES where the sound scheme SEPARATES ----
   Two swap-shaped redexes at distinct locations 1 ≠ 2 share the optimal channel
   (trace ignores location) but get distinct sound channels (per-location). So
   `same_clts_weak_bisim` is not the trivial "the schemes are identical" statement —
   this is the concrete pair the M2a runtime O3-fan-out test exercises. *)
Theorem optimal_shares_where_sound_separates :
  exists (Kf : nat -> Pat) (sitef : nat -> nat) (r1 r2 : nat),
    sitef r1 <> sitef r2
    /\ trace (Kf r1) = trace (Kf r2)
    /\ Some (sitef r1, op0 (Kf r1)) <> Some (sitef r2, op0 (Kf r2)).
Proof.
  exists (fun _ => PApp 0 [PVar]), (fun r => r), 1, 2.
  repeat split; first [ discriminate | reflexivity ].
Qed.

Print Assumptions optimal_visible_equals_sound.
Print Assumptions same_clts_weak_bisim.
Print Assumptions optimal_shares_where_sound_separates.
