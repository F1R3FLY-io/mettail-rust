(*
 * WholeGsltInRhoOpCorrespondenceIteratedViaDriver: the A-S5.7 ITERATED-DRIVING
 * DISCHARGE WITNESS — the Stage-5 capstone's §5 upgraded FBinderBeta burst premises
 * are backed, LITERALLY, by the landed InRhoQuiescenceDriver theorems (plan v2 §7.4
 * "discharged by (1)"): `drive_weak_bisim` (the iterated beta weak bisimulation over
 * aiter/citer chains) for the firing chains, and the A-S5.5 bag-model pair
 * `bag_quiescence_sound` / `driver_flatten_agrees_with_add_flattened_bag` for the AC
 * families' per-trace rest condition.
 *
 * ---------------------------------------------------------------------------------
 * WHAT THIS FILE IS
 * ---------------------------------------------------------------------------------
 *
 * The §5 iterated harness (WholeGsltInRhoOpCorrespondence.v) re-states the per-family
 * premises over DRIVE-MEDIATED MULTI-STEP TRACES (family-homogeneous `steps` bursts).
 * This companion does for the upgraded FBinderBeta arm what the SwapDemo §5.4 witness
 * does for FBase and the In/Out companion does for FAcNested — and it goes one step
 * further, closing the loop with the driver FV itself:
 *
 *   (a) BURST DISCHARGE: instantiate the §5 iterated capstone with the beta
 *       common-carrier sum `DCbeta := DAbs Obj | DConc Tm` (the
 *       InRhoBetaCascadeWeakBisim carriers), labels = the fired App op, and discharge
 *       the FBinderBeta burst arms NON-VACUOUSLY from the landed
 *       forward_simulation / backward_simulation via the §5.0 pointwise burst lift —
 *       the label-preserving refinement of drive_weak_bisim's chain lift
 *       (`betadrive_iterated_opcorr`).
 *
 *   (b) CHAIN DISCHARGE (the drive_weak_bisim consumption): harness bursts on this
 *       carrier PROJECT to the driver's iterated chains and back
 *       (`abs_steps_project_to_aiter`, `conc_steps_project_to_citer`,
 *       `citer_yields_conc_steps`), and the matching chain for an iterated abstract
 *       beta chain is DELIVERED BY `drive_weak_bisim` (proj1/proj2 consumed
 *       literally: `beta_burst_discharged_by_drive_weak_bisim` and its backward
 *       dual). The two-firing witness chain of
 *       InRhoQuiescenceDriver.drive_two_firing_nonvacuous re-expresses as a concrete
 *       harness burst (`beta_burst_two_firing_nonvacuous`), so the chain face is not
 *       vacuously satisfied.
 *
 *   (c) BAG-MODEL REST GROUNDING: the A-S5.5 additions are consumed literally —
 *       every bag drive rests FLAT and agrees with the host `add_flattened_bag`
 *       flatten (`ambient_burst_rest_flat_and_host_agreeing`), the per-trace
 *       (decision (3)) rest shape behind the Ambient families' quiescent burst
 *       endpoints. PER-TRACE only: one derivation is quantified; no cross-schedule
 *       unique-NF claim is made (Ambient is non-confluent).
 *
 * This is the ESTABLISHED companion idiom (cf.
 * WholeGsltInRhoOpCorrespondenceOptimalViaSameClts.v and ...InOutViaFiring.v): the
 * main harness carries the premises and cited discharge map; the additive companion
 * supplies the literal consumption, keeping every harness theorem byte-identical.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions, no Parameters.
 *)

From Stdlib Require Import List.
Import ListNotations.
From RhoBridge Require Import EndToEndCommCorrespondence.
From RhoBridge Require Import WholeGsltInRhoOpCorrespondence.
From RhoBridge Require Import DeBruijnSubstTRS.
From RhoBridge Require Import InRhoBetaCascadeWeakBisim.
From RhoBridge Require Import InRhoQuiescenceDriver.

(* ================================================================================
   1.  The beta common-carrier sum: an abstract object configuration or a concrete
   reflected-term configuration (the InRhoBetaCascadeWeakBisim carriers).
   ================================================================================ *)

Inductive DCbeta : Type :=
  | DAbs (o : Obj)
  | DConc (c : Tm).

(* One weak visible beta transition, labelled by the fired App op: abstract root
   fire (`awvis`) on DAbs, in-Rho fire-plus-cascade (`cwvis` — tau-star, the seed
   COMM, tau-star) on DConc; never crossing tags. *)
Definition dbeta_step (a : DCbeta) (op : nat) (b : DCbeta) : Prop :=
  match a, b with
  | DAbs o, DAbs o' => awvis op o o'
  | DConc c, DConc c' => cwvis op c c'
  | _, _ => False
  end.

(* The barb: the represented object (`norm` collapses the whole cascade — the
   NF-observation face of the driver's OUT datum). *)
Definition dbeta_barb (a : DCbeta) : Obj :=
  match a with
  | DAbs o => o
  | DConc c => norm c
  end.

(* Rgio: a concrete configuration REPRESENTS the abstract object it evaluates to
   (InRhoBetaCascadeWeakBisim.represents). *)
Definition dbeta_R (a b : DCbeta) : Prop :=
  match a, b with
  | DAbs o, DConc c => represents o c
  | _, _ => False
  end.

(* This model fires only the binder/beta family. *)
Definition dbeta_family (_ : nat) : option Family := Some FBinderBeta.

(* ================================================================================
   2.  The per-step arms from the landed single-fire clauses, and their burst lifts.
   ================================================================================ *)

Lemma dbeta_fwd_step : forall a b l a',
  dbeta_family l = Some FBinderBeta -> dbeta_R a b -> dbeta_step a l a' ->
  exists b', dbeta_step b l b' /\ dbeta_R a' b'.
Proof.
  intros a b l a' _ HR Hstep.
  destruct a as [o | c]; destruct b as [o2 | c2]; cbn in HR; try contradiction.
  destruct a' as [o' | c']; cbn in Hstep; try contradiction.
  destruct (forward_simulation o c2 l o' HR Hstep) as [c' [Hc' HR']].
  exists (DConc c'). cbn. split; [exact Hc' | exact HR'].
Qed.

Lemma dbeta_bwd_step : forall a b l b',
  dbeta_family l = Some FBinderBeta -> dbeta_R a b -> dbeta_step b l b' ->
  exists a', dbeta_step a l a' /\ dbeta_R a' b'.
Proof.
  intros a b l b' _ HR Hstep.
  destruct a as [o | c]; destruct b as [o2 | c2]; cbn in HR; try contradiction.
  destruct b' as [o2' | c']; cbn in Hstep; try contradiction.
  destruct (backward_simulation o c2 l c' HR Hstep) as [o' [Ho' HR']].
  exists (DAbs o'). cbn. split; [exact Ho' | exact HR'].
Qed.

(* The FBinderBeta BURST arms — the §5 upgraded premise shapes — via the §5.0
   pointwise lift (the label-preserving form of drive_weak_bisim's chain lift). *)
Lemma dbeta_fwd_burst : forall s t ls s',
  Forall (fun l => dbeta_family l = Some FBinderBeta) ls -> dbeta_R s t ->
  steps DCbeta nat dbeta_step s ls s' ->
  exists t', steps DCbeta nat dbeta_step t ls t' /\ dbeta_R s' t'.
Proof.
  exact (per_step_arm_lifts_to_burst_forward DCbeta nat dbeta_step dbeta_R
           (fun l => dbeta_family l = Some FBinderBeta) dbeta_fwd_step).
Qed.

Lemma dbeta_bwd_burst : forall s t ls t',
  Forall (fun l => dbeta_family l = Some FBinderBeta) ls -> dbeta_R s t ->
  steps DCbeta nat dbeta_step t ls t' ->
  exists s', steps DCbeta nat dbeta_step s ls s' /\ dbeta_R s' t'.
Proof.
  exact (per_step_arm_lifts_to_burst_backward DCbeta nat dbeta_step dbeta_R
           (fun l => dbeta_family l = Some FBinderBeta) dbeta_bwd_step).
Qed.

(* A nonempty family-homogeneous burst of any family other than FBinderBeta is
   uninhabited under dbeta_family; the empty burst is matched reflexively. *)
Lemma dbeta_vacuous_burst_fwd : forall F, F <> FBinderBeta -> forall s t ls s',
  Forall (fun l => dbeta_family l = Some F) ls -> dbeta_R s t ->
  steps DCbeta nat dbeta_step s ls s' ->
  exists t', steps DCbeta nat dbeta_step t ls t' /\ dbeta_R s' t'.
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

Lemma dbeta_vacuous_burst_bwd : forall F, F <> FBinderBeta -> forall s t ls t',
  Forall (fun l => dbeta_family l = Some F) ls -> dbeta_R s t ->
  steps DCbeta nat dbeta_step t ls t' ->
  exists s', steps DCbeta nat dbeta_step s ls s' /\ dbeta_R s' t'.
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

(* ================================================================================
   3.  (a) BURST DISCHARGE: the iterated capstone instantiated for beta — every §5.1
   burst premise dischargeable with the FBinderBeta arm SATISFIED (not vacuous).
   ================================================================================ *)

Theorem betadrive_iterated_opcorr : forall (o : Obj) (c : Tm) ls,
  represents o c ->
  (forall a', steps DCbeta nat dbeta_step (DAbs o) ls a' ->
      exists b', steps DCbeta nat dbeta_step (DConc c) ls b'
                 /\ dbeta_barb a' = dbeta_barb b') /\
  (forall b', steps DCbeta nat dbeta_step (DConc c) ls b' ->
      exists a', steps DCbeta nat dbeta_step (DAbs o) ls a'
                 /\ dbeta_barb a' = dbeta_barb b').
Proof.
  intros o c ls Hrep.
  apply (whole_gslt_in_rho_opcorrespondence_iterated DCbeta nat Obj
           dbeta_step dbeta_barb dbeta_R dbeta_family).
  - (* Rgio_barb: represents o c means norm c = o, i.e. equal barbs. *)
    intros a b HR.
    destruct a as [o1 | c1]; destruct b as [o2 | c2]; cbn in HR; try contradiction.
    cbn. symmetry. exact HR.
  - apply dbeta_vacuous_burst_fwd; discriminate.
  - apply dbeta_vacuous_burst_bwd; discriminate.
  - apply dbeta_vacuous_burst_fwd; discriminate.
  - apply dbeta_vacuous_burst_bwd; discriminate.
  - apply dbeta_vacuous_burst_fwd; discriminate.
  - apply dbeta_vacuous_burst_bwd; discriminate.
  - apply dbeta_vacuous_burst_fwd; discriminate.
  - apply dbeta_vacuous_burst_bwd; discriminate.
  - exact dbeta_fwd_burst.
  - exact dbeta_bwd_burst.
  - apply dbeta_vacuous_burst_fwd; discriminate.
  - apply dbeta_vacuous_burst_bwd; discriminate.
  - apply dbeta_vacuous_burst_fwd; discriminate.
  - apply dbeta_vacuous_burst_bwd; discriminate.
  - intros l; cbn; discriminate.
  - cbn. exact Hrep.
Qed.

(* ================================================================================
   4.  (b) CHAIN DISCHARGE: harness bursts on this carrier ARE the driver's iterated
   chains, and the matching chain is DELIVERED BY drive_weak_bisim.
   ================================================================================ *)

(* An abstract-side op-homogeneous burst projects to the driver's iterated abstract
   chain `aiter` (the burst's labels are all the one App op of the Lambda fragment —
   exactly the driver's chain shape). *)
Lemma abs_steps_project_to_aiter : forall a ls a',
  steps DCbeta nat dbeta_step a ls a' ->
  forall o op, a = DAbs o -> Forall (fun l => l = op) ls ->
  exists o', a' = DAbs o' /\ aiter op o o'.
Proof.
  intros a ls a' Hsteps.
  induction Hsteps as [a0 | a0 l a1 ls0 a2 Hstep Hsteps IH]; intros o op Heq Hhom;
    subst a0.
  - exists o. split; [reflexivity | apply aiter_refl].
  - inversion Hhom as [| x xs Hl Hhom0]; subst.
    destruct a1 as [o1 | c1]; cbn in Hstep; [| contradiction].
    destruct (IH o1 op eq_refl Hhom0) as [o' [Heq' Hiter]].
    exists o'. split; [exact Heq' | eapply aiter_cons; [exact Hstep | exact Hiter]].
Qed.

(* A concrete-side op-homogeneous burst projects to the driver's iterated concrete
   chain `citer`. *)
Lemma conc_steps_project_to_citer : forall a ls a',
  steps DCbeta nat dbeta_step a ls a' ->
  forall c op, a = DConc c -> Forall (fun l => l = op) ls ->
  exists c', a' = DConc c' /\ citer op c c'.
Proof.
  intros a ls a' Hsteps.
  induction Hsteps as [a0 | a0 l a1 ls0 a2 Hstep Hsteps IH]; intros c op Heq Hhom;
    subst a0.
  - exists c. split; [reflexivity | apply citer_refl].
  - inversion Hhom as [| x xs Hl Hhom0]; subst.
    destruct a1 as [o1 | c1]; cbn in Hstep; [contradiction |].
    destruct (IH c1 op eq_refl Hhom0) as [c' [Heq' Hiter]].
    exists c'. split; [exact Heq' | eapply citer_cons; [exact Hstep | exact Hiter]].
Qed.

(* A driver `citer` chain injects back into a concrete-side harness burst (the
   labels are the chain's op, one per link). *)
Lemma citer_yields_conc_steps : forall op c c',
  citer op c c' ->
  exists ls, Forall (fun l => l = op) ls
    /\ steps DCbeta nat dbeta_step (DConc c) ls (DConc c').
Proof.
  intros op c c' H.
  induction H as [c0 | c0 c1 c2 Hstep H IH].
  - exists []. split; [constructor | constructor].
  - destruct IH as [ls [Hhom Hsteps]].
    exists (op :: ls). split.
    + constructor; [reflexivity | exact Hhom].
    + apply steps_cons with (s' := DConc c1); [exact Hstep | exact Hsteps].
Qed.

(* A driver `aiter` chain injects back into an abstract-side harness burst. *)
Lemma aiter_yields_abs_steps : forall op o o',
  aiter op o o' ->
  exists ls, Forall (fun l => l = op) ls
    /\ steps DCbeta nat dbeta_step (DAbs o) ls (DAbs o').
Proof.
  intros op o o' H.
  induction H as [o0 | o0 o1 o2 Hstep H IH].
  - exists []. split; [constructor | constructor].
  - destruct IH as [ls [Hhom Hsteps]].
    exists (op :: ls). split.
    + constructor; [reflexivity | exact Hhom].
    + apply steps_cons with (s' := DAbs o1); [exact Hstep | exact Hsteps].
Qed.

(* ★ THE DISCHARGE BY drive_weak_bisim, FORWARD (plan v2 §7.4 / the
   InRhoQuiescenceDriver header's "single-step → iterated upgrade the
   WholeGsltInRhoOpCorrespondence premises consume in A-S5.7"): an ITERATED
   abstract beta chain from a represented pair is matched by an in-Rho iterated
   fire-plus-cascade chain — obtained LITERALLY from the landed
   InRhoQuiescenceDriver.drive_weak_bisim (proj1) and re-expressed as a harness
   burst. *)
Theorem beta_burst_discharged_by_drive_weak_bisim : forall o c op o',
  represents o c -> aiter op o o' ->
  exists c' ls,
    represents o' c'
    /\ Forall (fun l => l = op) ls
    /\ steps DCbeta nat dbeta_step (DConc c) ls (DConc c').
Proof.
  intros o c op o' Hrep Hiter.
  destruct (proj1 drive_weak_bisim o c op o' Hrep Hiter) as [c' [Hciter Hrep']].
  destruct (citer_yields_conc_steps op c c' Hciter) as [ls [Hhom Hsteps]].
  exists c', ls. split; [exact Hrep' | split; [exact Hhom | exact Hsteps]].
Qed.

(* ★ THE DISCHARGE BY drive_weak_bisim, BACKWARD: every in-Rho iterated chain
   (stated as an op-homogeneous harness burst) is matched by an abstract firing
   chain — drive_weak_bisim's second clause (proj2), consumed literally. *)
Theorem beta_burst_backward_discharged_by_drive_weak_bisim : forall o c op ls c',
  represents o c ->
  Forall (fun l => l = op) ls ->
  steps DCbeta nat dbeta_step (DConc c) ls (DConc c') ->
  exists o' ls',
    aiter op o o'
    /\ represents o' c'
    /\ Forall (fun l => l = op) ls'
    /\ steps DCbeta nat dbeta_step (DAbs o) ls' (DAbs o').
Proof.
  intros o c op ls c' Hrep Hhom Hsteps.
  destruct (conc_steps_project_to_citer (DConc c) ls (DConc c') Hsteps c op
              eq_refl Hhom) as [c'' [Heq Hciter]].
  injection Heq as Heq. subst c''.
  destruct (proj2 drive_weak_bisim o c op c' Hrep Hciter) as [o' [Hiter Hrep']].
  destruct (aiter_yields_abs_steps op o o' Hiter) as [ls' [Hhom' Hsteps']].
  exists o', ls'.
  split; [exact Hiter | split; [exact Hrep' | split; [exact Hhom' | exact Hsteps']]].
Qed.

(* Non-vacuity of the chain face: the TWO-firing witness chain of
   InRhoQuiescenceDriver.drive_two_firing_nonvacuous — `(lam.0) ((lam.0) x^)` —
   re-expresses as a concrete harness burst ending at the represented NF, so the
   drive_weak_bisim-shaped matching above is not vacuously satisfied. *)
Theorem beta_burst_two_firing_nonvacuous : forall op x,
  exists ls, Forall (fun l => l = op) ls
    /\ steps DCbeta nat dbeta_step
         (DConc (embed (two_chain op x))) ls (DConc (embed (oFree x)))
    /\ dbeta_R (DAbs (oFree x)) (DConc (embed (oFree x))).
Proof.
  intros op x.
  destruct (drive_two_firing_nonvacuous op x) as [_ [Hciter Hrep]].
  destruct (citer_yields_conc_steps op (embed (two_chain op x)) (embed (oFree x))
              Hciter) as [ls [Hhom Hsteps]].
  exists ls. split; [exact Hhom | split; [exact Hsteps | cbn; exact Hrep]].
Qed.

(* ================================================================================
   5.  (c) BAG-MODEL REST GROUNDING: the A-S5.5 additions consumed literally — the
   per-trace (decision (3)) rest shape behind the Ambient (FAcStructural /
   FAcNested) families' quiescent burst endpoints: EVERY bag drive rests FLAT (no
   nested bag hides a sibling redex from the top-level NF scan) AND the driven
   value agrees with the host's `add_flattened_bag` flatten (the §4.7 cross-check
   mirror). PER-TRACE only: one derivation is quantified; no cross-schedule
   unique-NF claim is made (Ambient is non-confluent).
   ================================================================================ *)

Theorem ambient_burst_rest_flat_and_host_agreeing : forall v w,
  bdrives v w -> is_flat w /\ w = bflatten v.
Proof.
  intros v w H. split.
  - exact (bag_quiescence_sound v w H).
  - rewrite (bdrives_deterministic v w H).
    exact (driver_flatten_agrees_with_add_flattened_bag v).
Qed.

(* Zero-admission confirmation. *)
Print Assumptions dbeta_fwd_burst.
Print Assumptions dbeta_bwd_burst.
Print Assumptions betadrive_iterated_opcorr.
Print Assumptions beta_burst_discharged_by_drive_weak_bisim.
Print Assumptions beta_burst_backward_discharged_by_drive_weak_bisim.
Print Assumptions beta_burst_two_firing_nonvacuous.
Print Assumptions ambient_burst_rest_flat_and_host_agreeing.
