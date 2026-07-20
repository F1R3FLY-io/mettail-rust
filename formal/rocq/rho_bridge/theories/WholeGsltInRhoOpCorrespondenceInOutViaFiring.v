(*
 * WholeGsltInRhoOpCorrespondenceInOutViaFiring: the In/Out (FAcNested) NON-VACUITY WITNESS —
 * the Stage-5 capstone's slotted `FAcNested` arm DISCHARGED, non-vacuously, from the landed
 * operational firing FV `AmbientInOutFiring`.
 *
 * ---------------------------------------------------------------------------------
 * WHAT THIS FILE IS
 * ---------------------------------------------------------------------------------
 *
 * The capstone `WholeGsltInRhoOpCorrespondence.v` carries a base-only non-vacuity witness
 * (`swapdemo_base_finite_trace_opcorr`): it instantiates the whole harness with the common-carrier
 * sum `GC := GSrc SourceState | GRho RhoState`, discharges the `FBase` arm from the landed
 * `LinearCommCorrespondence.comm_step_complete/sound`, and discharges the OTHER SIX families
 * (including `FAcNested`) VACUOUSLY (that model only fires base).
 *
 * THIS file does for In/Out exactly what the base witness does for base — the depth-2 mirror. It
 * instantiates the SAME abstract capstone (`whole_gslt_in_rho_opcorrespondence`) with an
 * `InOutDemo` common-carrier sum `GCio := GSrcIO InOutSrcState | GRhoIO InOutRhoState`, whose step
 * is the In/Out reduction / lowered In/Out COMM, and discharges the `FAcNested` arm NON-VACUOUSLY
 * from `AmbientInOutFiring.inout_step_complete / inout_step_sound` (the OTHER six families discharge
 * vacuously — this model fires only In/Out). This is the CONCRETE proof that the `FAcNested` arm is
 * dischargeable — not merely asserted — putting In/Out on EQUAL FOOTING with the `FAcStructural`
 * (OpenRule) arm, which cites `AmbientOpenFiring`. As a corollary it yields a concrete `Closed`
 * finite-trace operational correspondence for the In/Out reduction THROUGH the capstone.
 *
 * This is the ESTABLISHED companion idiom (cf. `WholeGsltInRhoOpCorrespondenceOptimalViaSameClts.v`,
 * which backs the (iii) `matching_locus_*` hypotheses from the landed obligation): the main harness
 * `WholeGsltInRhoOpCorrespondence.v` carries only the base witness + a cited `FAcNested` comment;
 * this additive companion supplies the In/Out discharge, keeping every capstone theorem byte-
 * identical (the 6+4 Closed results are untouched). `AmbientInOutFiring` (a RhoBridge theory that
 * transitively depends on `AdvancedAutomata.InRhoAcMatchMultiset`) resolves via the
 * `-Q ../advanced_automata/theories AdvancedAutomata` edge already in rho_bridge/_CoqProject.
 *
 * A-S5.7 (the trailing section below): the In/Out arm is RE-INSTANTIATED against the harness's
 * §5 UPGRADED (iterated-driving) premise shapes — the FAcNested BURST arms discharged from the
 * same landed inout_step_complete/sound via the §5.0 pointwise burst lift, the other families
 * vacuous-or-empty, yielding the In/Out iterated finite-trace opcorr plus the decision-(3)
 * PER-TRACE quiescence instance (any-valid-reduction; no unique-NF claim — Ambient is
 * non-confluent, and only THE GIVEN schedule's resting endpoint is spoken of).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions, no Parameters.
 *)

From Stdlib Require Import List.
Import ListNotations.
From RhoBridge Require Import EndToEndCommCorrespondence.
From RhoBridge Require Import WholeGsltInRhoOpCorrespondence.
From RhoBridge Require Import AmbientInOutFiring.

(* The InOutDemo common-carrier sum: a source In/Out config or a lowered in-Rho In/Out config
   (the depth-2 mirror of the base witness's `GC := GSrc _ | GRho _`). *)
Inductive GCio : Type :=
  | GSrcIO (s : InOutSrcState)
  | GRhoIO (r : InOutRhoState).

(* `gstep` dispatches on the tag: source In/Out reduction on GSrcIO, lowered In/Out COMM on GRhoIO;
   it never crosses tags. The label/datum is the fired top reduct (a nat id). *)
Definition nvio_step (a : GCio) (d : nat) (b : GCio) : Prop :=
  match a, b with
  | GSrcIO s, GSrcIO s' => source_inout_comm s d s'
  | GRhoIO r, GRhoIO r' => rho_inout_comm r d r'
  | _, _ => False
  end.

Definition nvio_barb (a : GCio) : list nat :=
  match a with
  | GSrcIO s => ios_outputs s
  | GRhoIO r => ior_outputs r
  end.

(* Rgio relates a source In/Out config to its lowered image. *)
Definition nvio_R (a b : GCio) : Prop :=
  match a, b with
  | GSrcIO s, GRhoIO r => r = lower_inout s
  | _, _ => False
  end.

(* This model fires only the In/Out (FAcNested) family. *)
Definition nvio_family (_ : nat) : option Family := Some FAcNested.

(* The lowered image of the source In/Out reduct is exactly the lowered image of the source config
   after the step: the sum-carrier glue (the depth-2 mirror of the base `rho_comm_lowers_step`). *)
Lemma rho_inout_lowers_step : forall s l s' r',
  source_inout_comm s l s' -> rho_inout_comm (lower_inout s) l r' -> r' = lower_inout s'.
Proof.
  intros s l s' r' Hsrc Hrho.
  destruct Hsrc as [_ [_ Hs']].
  destruct Hrho as [_ [_ Hr']].
  subst s' r'. unfold lower_inout. cbn. reflexivity.
Qed.

Lemma nvio_Rgio_barb : forall a b, nvio_R a b -> nvio_barb a = nvio_barb b.
Proof.
  intros a b HR. destruct a as [s | r]; destruct b as [s2 | r2]; cbn in HR; try contradiction.
  subst r2. cbn. reflexivity.
Qed.

(* The FAcNested forward arm, DISCHARGED from AmbientInOutFiring.inout_step_complete. *)
Lemma nvio_fwd_ac_nested : forall a b l a',
  nvio_family l = Some FAcNested -> nvio_R a b -> nvio_step a l a' ->
  exists b', nvio_step b l b' /\ nvio_R a' b'.
Proof.
  intros a b l a' _ HR Hstep.
  destruct a as [s0 | r0]; destruct b as [s1 | r1]; cbn in HR; try contradiction.
  subst r1.
  destruct a' as [s0' | r']; cbn in Hstep; try contradiction.
  destruct (inout_step_complete s0 l s0' Hstep) as [r' [Hrho _]].
  exists (GRhoIO r'). cbn. split.
  - exact Hrho.
  - exact (rho_inout_lowers_step s0 l s0' r' Hstep Hrho).
Qed.

(* The FAcNested backward arm, DISCHARGED from AmbientInOutFiring.inout_step_sound. *)
Lemma nvio_bwd_ac_nested : forall a b l b',
  nvio_family l = Some FAcNested -> nvio_R a b -> nvio_step b l b' ->
  exists a', nvio_step a l a' /\ nvio_R a' b'.
Proof.
  intros a b l b' _ HR Hstep.
  destruct a as [s0 | r0]; destruct b as [s1 | r1]; cbn in HR; try contradiction.
  subst r1.
  destruct b' as [s1' | r']; cbn in Hstep; try contradiction.
  destruct (inout_step_sound s0 l r' Hstep) as [s0' [Hsrc _]].
  exists (GSrcIO s0'). cbn. split.
  - exact Hsrc.
  - exact (rho_inout_lowers_step s0 l s0' r' Hsrc Hstep).
Qed.

(* The InOutDemo In/Out finite-trace operational correspondence, obtained by instantiating the
   abstract capstone `whole_gslt_in_rho_opcorrespondence`. Simultaneously the non-vacuity witness
   (all §4.1 hypotheses jointly satisfiable, with the FAcNested arm SATISFIED — not vacuous) and a
   concrete Closed finite-trace opcorr for the In/Out reduction THROUGH the capstone. The six
   non-In/Out families discharge vacuously (this model never fires them), the gate holds (every
   label is FAcNested), and the initial Rgio is the lowering. *)
Theorem inoutdemo_nested_finite_trace_opcorr : forall (s : InOutSrcState) ls,
  (forall a', steps GCio nat nvio_step (GSrcIO s) ls a' ->
      exists b', steps GCio nat nvio_step (GRhoIO (lower_inout s)) ls b' /\ nvio_barb a' = nvio_barb b') /\
  (forall b', steps GCio nat nvio_step (GRhoIO (lower_inout s)) ls b' ->
      exists a', steps GCio nat nvio_step (GSrcIO s) ls a' /\ nvio_barb a' = nvio_barb b').
Proof.
  intros s ls.
  apply (whole_gslt_in_rho_opcorrespondence GCio nat (list nat)
           nvio_step nvio_barb nvio_R nvio_family).
  - exact nvio_Rgio_barb.
  - intros a b l a' H _ _; cbn in H; discriminate H.   (* fwd_base — vacuous *)
  - intros a b l b' H _ _; cbn in H; discriminate H.   (* bwd_base *)
  - intros a b l a' H _ _; cbn in H; discriminate H.   (* fwd_join *)
  - intros a b l b' H _ _; cbn in H; discriminate H.   (* bwd_join *)
  - intros a b l a' H _ _; cbn in H; discriminate H.   (* fwd_ac_linear *)
  - intros a b l b' H _ _; cbn in H; discriminate H.   (* bwd_ac_linear *)
  - intros a b l a' H _ _; cbn in H; discriminate H.   (* fwd_ac_structural *)
  - intros a b l b' H _ _; cbn in H; discriminate H.   (* bwd_ac_structural *)
  - intros a b l a' H _ _; cbn in H; discriminate H.   (* fwd_binder_beta *)
  - intros a b l b' H _ _; cbn in H; discriminate H.   (* bwd_binder_beta *)
  - intros a b l a' H _ _; cbn in H; discriminate H.   (* fwd_native *)
  - intros a b l b' H _ _; cbn in H; discriminate H.   (* bwd_native *)
  - exact nvio_fwd_ac_nested.                          (* fwd_ac_nested — REAL (AmbientInOutFiring) *)
  - exact nvio_bwd_ac_nested.                          (* bwd_ac_nested — REAL (AmbientInOutFiring) *)
  - intros l; cbn; discriminate.                       (* g_install_gate_admits *)
  - cbn. reflexivity.                                  (* initial Rgio = the lowering *)
Qed.

(* ---- 4.8 parity: the InOutDemo In/Out reduction over the OPTIMAL matching ----
   As in the base witness `swapdemo_base_opcorr_over_optimal`, a single In/Out depth-2 firing has no
   location/StateId distinction, so the OPTIMAL scheme coincides with the SOUND scheme here
   (`gstep_opt := nvio_step`, `Rso := nvio_eq` = identity). Discharging the three additional
   `matching_locus_*` hypotheses (trivially, sound = optimal) shows the (iii)-threaded harness
   context is inhabited for In/Out too — the In/Out arm composes with the O1-optimal upgrade exactly
   as the base arm does. *)
Definition nvio_eq (a b : GCio) : Prop := a = b.

Theorem inoutdemo_nested_opcorr_over_optimal : forall (s : InOutSrcState) (t u : GCio) ls,
  nvio_R (GSrcIO s) t -> nvio_eq t u ->
  (forall a', steps GCio nat nvio_step (GSrcIO s) ls a' ->
      exists u', steps GCio nat nvio_step u ls u' /\ nvio_barb a' = nvio_barb u') /\
  (forall u', steps GCio nat nvio_step u ls u' ->
      exists a', steps GCio nat nvio_step (GSrcIO s) ls a' /\ nvio_barb a' = nvio_barb u').
Proof.
  intros s t u ls Hrgio Hrso.
  eapply (whole_gslt_opcorr_over_optimal_matching GCio nat (list nat)
           nvio_step nvio_barb nvio_R nvio_family nvio_step nvio_eq).
  - exact nvio_Rgio_barb.
  - intros a b l a' H _ _; cbn in H; discriminate H.
  - intros a b l b' H _ _; cbn in H; discriminate H.
  - intros a b l a' H _ _; cbn in H; discriminate H.
  - intros a b l b' H _ _; cbn in H; discriminate H.
  - intros a b l a' H _ _; cbn in H; discriminate H.
  - intros a b l b' H _ _; cbn in H; discriminate H.
  - intros a b l a' H _ _; cbn in H; discriminate H.
  - intros a b l b' H _ _; cbn in H; discriminate H.
  - intros a b l a' H _ _; cbn in H; discriminate H.
  - intros a b l b' H _ _; cbn in H; discriminate H.
  - intros a b l a' H _ _; cbn in H; discriminate H.
  - intros a b l b' H _ _; cbn in H; discriminate H.
  - exact nvio_fwd_ac_nested.
  - exact nvio_bwd_ac_nested.
  - intros l; cbn; discriminate.
  - intros a b Hab; unfold nvio_eq in Hab; subst b; reflexivity.
  - intros a b l a' Hab Hstep; unfold nvio_eq in Hab; subst b;
      exists a'; split; [exact Hstep | unfold nvio_eq; reflexivity].
  - intros a b l b' Hab Hstep; unfold nvio_eq in Hab; subst b;
      exists b'; split; [exact Hstep | unfold nvio_eq; reflexivity].
  - exact Hrgio.
  - exact Hrso.
Qed.

(* Fully concrete corollary: the InOutDemo source<->optimal-in-Rho finite-trace opcorr, where the
   optimal image is the lowered config (sound = optimal for a single In/Out firing). *)
Corollary inoutdemo_nested_opcorr_over_optimal_concrete : forall (s : InOutSrcState) ls,
  (forall a', steps GCio nat nvio_step (GSrcIO s) ls a' ->
      exists u', steps GCio nat nvio_step (GRhoIO (lower_inout s)) ls u' /\ nvio_barb a' = nvio_barb u') /\
  (forall u', steps GCio nat nvio_step (GRhoIO (lower_inout s)) ls u' ->
      exists a', steps GCio nat nvio_step (GSrcIO s) ls a' /\ nvio_barb a' = nvio_barb u').
Proof.
  intros s ls.
  apply (inoutdemo_nested_opcorr_over_optimal s (GRhoIO (lower_inout s)) (GRhoIO (lower_inout s)) ls).
  - cbn. reflexivity.
  - unfold nvio_eq. reflexivity.
Qed.

(* Zero-admission confirmation. *)
Print Assumptions inoutdemo_nested_finite_trace_opcorr.
Print Assumptions inoutdemo_nested_opcorr_over_optimal.
Print Assumptions inoutdemo_nested_opcorr_over_optimal_concrete.

(* ================================================================================
   A-S5.7 — the In/Out arm RE-INSTANTIATED against the UPGRADED (iterated-driving)
   premise shapes (harness §5, plan v2 §7.4): the FAcNested BURST arms are discharged
   from the SAME landed AmbientInOutFiring.inout_step_complete/sound via the §5.0
   pointwise burst lift; the other families' bursts are vacuous-or-empty under
   nvio_family. Quiescence is PER-TRACE (user decision (3)): the instance below
   speaks only of THE GIVEN drive schedule's resting endpoint — Ambient is
   non-confluent and no unique-normal-form claim is made.
   ================================================================================ *)

Lemma nvio_fwd_ac_nested_burst : forall s t ls s',
  Forall (fun l => nvio_family l = Some FAcNested) ls -> nvio_R s t ->
  steps GCio nat nvio_step s ls s' ->
  exists t', steps GCio nat nvio_step t ls t' /\ nvio_R s' t'.
Proof.
  exact (per_step_arm_lifts_to_burst_forward GCio nat nvio_step nvio_R
           (fun l => nvio_family l = Some FAcNested) nvio_fwd_ac_nested).
Qed.

Lemma nvio_bwd_ac_nested_burst : forall s t ls t',
  Forall (fun l => nvio_family l = Some FAcNested) ls -> nvio_R s t ->
  steps GCio nat nvio_step t ls t' ->
  exists s', steps GCio nat nvio_step s ls s' /\ nvio_R s' t'.
Proof.
  exact (per_step_arm_lifts_to_burst_backward GCio nat nvio_step nvio_R
           (fun l => nvio_family l = Some FAcNested) nvio_bwd_ac_nested).
Qed.

(* A nonempty family-homogeneous burst of any family other than FAcNested is
   uninhabited under nvio_family; the empty burst is matched reflexively. *)
Lemma nvio_vacuous_burst_fwd : forall F, F <> FAcNested -> forall s t ls s',
  Forall (fun l => nvio_family l = Some F) ls -> nvio_R s t ->
  steps GCio nat nvio_step s ls s' ->
  exists t', steps GCio nat nvio_step t ls t' /\ nvio_R s' t'.
Proof.
  intros F Hne s t ls s' Hfam HR Hs.
  destruct ls as [| l ls0].
  - apply steps_nil_inv in Hs. subst s'.
    exists t. split; [constructor | exact HR].
  - exfalso.
    inversion Hfam as [| x xs Hhead Htail]; subst.
    cbn in Hhead. injection Hhead as Heq. subst F.
    apply Hne. reflexivity.
Qed.

Lemma nvio_vacuous_burst_bwd : forall F, F <> FAcNested -> forall s t ls t',
  Forall (fun l => nvio_family l = Some F) ls -> nvio_R s t ->
  steps GCio nat nvio_step t ls t' ->
  exists s', steps GCio nat nvio_step s ls s' /\ nvio_R s' t'.
Proof.
  intros F Hne s t ls t' Hfam HR Ht.
  destruct ls as [| l ls0].
  - apply steps_nil_inv in Ht. subst t'.
    exists s. split; [constructor | exact HR].
  - exfalso.
    inversion Hfam as [| x xs Hhead Htail]; subst.
    cbn in Hhead. injection Hhead as Heq. subst F.
    apply Hne. reflexivity.
Qed.

(* The In/Out iterated finite-trace opcorr THROUGH THE §5 ITERATED HARNESS: every
   burst premise discharged, the FAcNested pair SATISFIED (not vacuous). *)
Theorem inoutdemo_nested_iterated_opcorr : forall (s : InOutSrcState) ls,
  (forall a', steps GCio nat nvio_step (GSrcIO s) ls a' ->
      exists b', steps GCio nat nvio_step (GRhoIO (lower_inout s)) ls b'
                 /\ nvio_barb a' = nvio_barb b') /\
  (forall b', steps GCio nat nvio_step (GRhoIO (lower_inout s)) ls b' ->
      exists a', steps GCio nat nvio_step (GSrcIO s) ls a'
                 /\ nvio_barb a' = nvio_barb b').
Proof.
  intros s ls.
  apply (whole_gslt_in_rho_opcorrespondence_iterated GCio nat (list nat)
           nvio_step nvio_barb nvio_R nvio_family).
  - exact nvio_Rgio_barb.
  - apply nvio_vacuous_burst_fwd; discriminate.
  - apply nvio_vacuous_burst_bwd; discriminate.
  - apply nvio_vacuous_burst_fwd; discriminate.
  - apply nvio_vacuous_burst_bwd; discriminate.
  - apply nvio_vacuous_burst_fwd; discriminate.
  - apply nvio_vacuous_burst_bwd; discriminate.
  - apply nvio_vacuous_burst_fwd; discriminate.
  - apply nvio_vacuous_burst_bwd; discriminate.
  - apply nvio_vacuous_burst_fwd; discriminate.
  - apply nvio_vacuous_burst_bwd; discriminate.
  - apply nvio_vacuous_burst_fwd; discriminate.
  - apply nvio_vacuous_burst_bwd; discriminate.
  - exact nvio_fwd_ac_nested_burst.
  - exact nvio_bwd_ac_nested_burst.
  - intros l; cbn; discriminate.
  - cbn. reflexivity.
Qed.

(* The In/Out PER-TRACE quiescence instance (decision (3)): a resting source drive
   schedule is mirrored by a resting in-Rho drive schedule — equal barbs, related
   endpoints, THIS schedule only (membership form, no unique-NF claim). *)
Theorem inoutdemo_nested_per_trace_quiescence : forall (s : InOutSrcState) sched s',
  drive_schedule GCio nat nvio_step nvio_family (GSrcIO s) sched s' ->
  gquiescent GCio nat nvio_step s' ->
  exists t', drive_schedule GCio nat nvio_step nvio_family
               (GRhoIO (lower_inout s)) sched t'
             /\ nvio_R s' t' /\ nvio_barb s' = nvio_barb t'
             /\ gquiescent GCio nat nvio_step t'.
Proof.
  intros s sched s' Hsched Hq.
  refine (whole_gslt_per_trace_quiescence_forward GCio nat (list nat)
            nvio_step nvio_barb nvio_R nvio_family
            nvio_Rgio_barb
            _ _ _ _ _ _ _ _ _ _ _ _
            nvio_fwd_ac_nested_burst nvio_bwd_ac_nested_burst
            _
            (GSrcIO s) (GRhoIO (lower_inout s)) sched s'
            _ Hsched Hq).
  - apply nvio_vacuous_burst_fwd; discriminate.
  - apply nvio_vacuous_burst_bwd; discriminate.
  - apply nvio_vacuous_burst_fwd; discriminate.
  - apply nvio_vacuous_burst_bwd; discriminate.
  - apply nvio_vacuous_burst_fwd; discriminate.
  - apply nvio_vacuous_burst_bwd; discriminate.
  - apply nvio_vacuous_burst_fwd; discriminate.
  - apply nvio_vacuous_burst_bwd; discriminate.
  - apply nvio_vacuous_burst_fwd; discriminate.
  - apply nvio_vacuous_burst_bwd; discriminate.
  - apply nvio_vacuous_burst_fwd; discriminate.
  - apply nvio_vacuous_burst_bwd; discriminate.
  - intros l; cbn; discriminate.
  - cbn. reflexivity.
Qed.

(* Zero-admission confirmation (A-S5.7 iterated re-instantiation). *)
Print Assumptions nvio_fwd_ac_nested_burst.
Print Assumptions nvio_bwd_ac_nested_burst.
Print Assumptions inoutdemo_nested_iterated_opcorr.
Print Assumptions inoutdemo_nested_per_trace_quiescence.
