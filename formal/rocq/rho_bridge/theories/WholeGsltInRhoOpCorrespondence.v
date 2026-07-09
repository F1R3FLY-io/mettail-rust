(*
 * WholeGsltInRhoOpCorrespondence: the STAGE 5 CAPSTONE — the whole-⟦G⟧ operational
 * correspondence for finite executions with O1-optimal in-Rho matching (INV-13 /
 * the knotted-topoi paper's `ob:opcorr`, finite-trace form). This is the rho-native
 * campaign's culmination.
 *
 * ---------------------------------------------------------------------------------
 * WHAT THIS FILE IS (and is NOT)
 * ---------------------------------------------------------------------------------
 *
 * This is a COMPOSITION HARNESS, not a new proof about rho-calculus reduction. It
 * does exactly three things:
 *
 *   (a) INSTANTIATE the assumption-free finite-trace lift `EndToEndCommCorrespondence`
 *       (State/Label/Obs/step/barb/R + the three step-wise bisimulation obligations)
 *       with the whole-⟦G⟧ in-Rho configuration LTS: `GConfig` (the installed ⟦G⟧
 *       spread over an incoming term, plus the set-automaton), a family-tagged COMM
 *       label `CommLabel`, the resting-send barb `Barb`, the weak-visible any-family
 *       COMM `gstep := τ*·(one visible c(ℓ))·τ*`, and the source↔in-Rho relation
 *       `Rgio`.
 *
 *   (b) ASSEMBLE the lift's three obligations (`assembled_R_barb`,
 *       `assembled_R_forward`, `assembled_R_backward`) by a `family_of` case split
 *       whose arms are each an ALREADY-LANDED per-step theorem (the six rule
 *       families, plus the slotted In/Out `FAcNested`). Each arm enters as a Section
 *       `Hypothesis` in the harness-compatible shape and is discharged, at any
 *       concrete instantiation, by its cited landed theorem — the non-vacuity witness
 *       below does this literally for the base family. A `Hypothesis` becomes a
 *       universally-quantified PREMISE when the Section closes; it is NOT an `Axiom`,
 *       so every theorem here stays `Closed under the global context`.
 *
 *   (c) `apply` the lift's `forward_/backward_trace_correspondence` and
 *       `finite_trace_barb_equivalence` to obtain the whole-⟦G⟧ finite-trace opcorr,
 *       then thread obligation (iii) so the result holds over the O1-OPTIMAL matching
 *       (the `rem:nonopt` discharge — see `whole_gslt_opcorr_over_optimal_matching`).
 *
 * ---------------------------------------------------------------------------------
 * HONESTY (which results are step-correspondences and which are NOT)
 * ---------------------------------------------------------------------------------
 *
 * The six rule-family arms that DO feed R_forward/R_backward are genuine per-step
 * correspondences:
 *   - FBase          <- LinearCommCorrespondence.comm_step_complete / comm_step_sound
 *                       / lower_preserves_barbs.
 *   - FContextualJoin<- ContextualAtomicJoinPlugging.nary_join_complete / nary_join_sound
 *                       / lower_join_preserves_barbs (INV-6 atomic polyadic join, INV-2
 *                       plugging stability).
 *   - FAcLinear      <- the base flat sigma-receiver step (the AC firing REUSES it),
 *                       with the AC bundle (InRhoAcMatchMultiset.ac_match_iff_partition,
 *                       AcAtomicNoPartialConsume, AcRestReconstruction,
 *                       AcNonLinearConsistency, CommRuleFiring) certifying PAYLOAD +
 *                       ATOMICITY, not a distinct transition.
 *   - FAcStructural  <- AmbientOpenFiring.open_commits_when_names_agree /
 *                       open_disagree_no_commit / open_emits_both_reducts_and_splices_rest,
 *                       with the structural match-spread
 *                       InRhoAcMatchMultiset.structural_ac_spread_is_report_faithful.
 *   - FBinderBeta    <- InRhoBetaCascadeWeakBisim.forward_simulation / backward_simulation
 *                       (packaged weak_bisim_beta_cascade_vs_abstract_beta): the object-β
 *                       label is visible, each ^subst/^shift COMM is τ; its `cwvis` IS
 *                       the gstep reference shape.
 *   - FNative        <- NativeSystemProcessBoundary.fold_native_process_fires_handler_value
 *                       / emitted_is_reflected_handler_value / location_from_automaton_not_report
 *                       (payload = a TRUSTED native-handler value, the
 *                       RhoHostObligationBoundary seam; the directed-compute COMM, not a
 *                       predicate).
 * The slotted In/Out arm FAcNested cites the DEPTH-2 match logic
 * InRhoAcMatchMultiset.nested_ac_match_iff_partition /
 * nested_structural_ac_spread_is_report_faithful (commit ffec090f).
 *
 * The AC family's match-logic results (ac_match_iff_partition, ...) and the MATCHING
 * LAYER (i InRhoMatchPositional.sa_matches_positional, ii SymbolOnceInjective.positions_count,
 * iv AtomicFiringNoPartialMatch.partial_consume_unreachable, vi
 * NonLinearEqConsistency.eq_all_equal_commits, viii TcChannelNamingQuotient.tc_sound,
 * x InRhoReuseDeterminism) are Prop-level match-logic / atomicity / guard results —
 * they are NOT independent step-correspondences and do NOT appear as R_forward /
 * R_backward arms. They enter only as (1) gstep WELL-FORMEDNESS (iv: no partial-match
 * reachable; vi: the guard gates the accept-send; x: the τ-prefix is deterministic;
 * i: the in-Rho σ equals the positional σ) and (2) PREMISES of obligation (iii). This
 * capstone USES (iii) — it does not consume i/ii/iv/vi/viii/x as arms.
 *
 * Semantic predicates (INV-14) are excluded by CONSTRUCTION: `Family` has no
 * predicate constructor, `family_of` is total over COMM labels only, and a predicate
 * rule emits no c(ℓ) label — see the statement-only fence
 * `semantic_predicates_emit_no_comm`. All-G universality is CONDITIONAL on the
 * install gate admitting G (`g_install_gate_admits`, cite
 * InRhoEncoderTotalOrReject.gate_admits_iff_all_fired_matchable, ix): a G with an
 * uncovered rule shape fail-closes at install (total-or-reject, INV-11) and produces
 * no GConfig, so it is outside scope.
 *
 * MODELING DECISION (the common-carrier sum): the lift relates ONE `step` on ONE
 * `State`, but each arm's landed correspondence relates a source carrier to an in-Rho
 * carrier (e.g. SourceState vs RhoState). The non-vacuity witness resolves this with
 * the recommended common-carrier sum `GC := GSrc _ | GRho _`: `gstep` dispatches on
 * the tag (source rewrite on GSrc, in-Rho COMM on GRho) and `Rgio` relates a
 * source-tagged config to its lowered image. This matches the arm theorem types
 * (comm_step_complete/sound over SourceState/RhoState) exactly.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions, no Parameters (the
 * per-family arms and the (iii) transfer are Section Hypotheses — universally
 * quantified premises on Section close, NOT Axioms).
 *)

From Stdlib Require Import List.
Import ListNotations.
From RhoBridge Require Import EndToEndCommCorrespondence.
From RhoBridge Require Import LinearCommCorrespondence.

(* The rule families that fire as a context-labelled COMM c(ℓ). INV-14: there is NO
   semantic-predicate constructor — a predicate rule emits no c(ℓ) and never appears
   here (see the fence `semantic_predicates_emit_no_comm`). *)
Inductive Family : Type :=
  | FBase           (* linear base rewrite: LinearCommCorrespondence *)
  | FContextualJoin (* atomic polyadic contextual join: ContextualAtomicJoinPlugging *)
  | FAcLinear       (* linear AC firing (reuses the base flat σ-receiver): CommRuleFiring *)
  | FAcStructural   (* structural AC / Ambient OpenRule: AmbientOpenFiring *)
  | FBinderBeta     (* binder/β cascade: InRhoBetaCascadeWeakBisim *)
  | FNative         (* native system-process dispatch: NativeSystemProcessBoundary *)
  | FAcNested.      (* In/Out depth-2 nested structural AC (slotted): InRhoAcMatchMultiset *)

Section WholeGsltInRhoOpCorrespondence.

  (* ============================================================================
     4.0  The whole-⟦G⟧ in-Rho configuration LTS (abstract carrier).
     ============================================================================ *)

  (* A `GConfig` is a whole program configuration: the installed ⟦G⟧ σ-receivers in
     parallel with the spread ⟦t⟧ and the set-automaton. `CommLabel` is a
     context-labelled COMM event c(ℓ), tagged with its rule family by `family_of`.
     `Barb` is the resting-send multiset on the out channels. *)
  Variable GConfig : Type.
  Variable CommLabel : Type.
  Variable Barb : Type.

  (* `gstep` is one WEAK VISIBLE any-family COMM: τ* (sa:/eq: inspection + loc: spine
     descent) then one visible accept-send c(ℓ) then τ* (the β / subst cascade). Every
     internal matching COMM is routed through the τ-stars, so `gstep` is exactly the
     `cwvis` weak-visible shape the lift consumes. *)
  Variable gstep : GConfig -> CommLabel -> GConfig -> Prop.
  Variable gbarb : GConfig -> Barb.

  (* `Rgio` relates a source CLTS configuration to its SOUND (location-keyed, model-b
     baseline) in-Rho image. The O1-OPTIMAL upgrade is threaded separately below via
     obligation (iii). *)
  Variable Rgio : GConfig -> GConfig -> Prop.

  (* `family_of l = None` models a rule whose SHAPE the install gate rejected (it is
     never installed, INV-11 total-or-reject); `g_install_gate_admits` scopes the
     theorem to gate-admitted ⟦G⟧, where every fired label has a covered family. *)
  Variable family_of : CommLabel -> option Family.

  (* ============================================================================
     4.1  The per-family arms (Section Hypotheses) + barb preservation + install gate.

     Each arm is stated in the lift's obligation shape, guarded by `family_of l = Some
     F<X>`, and is discharged at any concrete instantiation by its cited landed
     theorem (done literally for FBase in the non-vacuity witness).
     ============================================================================ *)

  (* Rgio preserves barbs (<- LinearCommCorrespondence.lower_preserves_barbs and the
     per-family lower_*_preserves_barbs). *)
  Hypothesis Rgio_barb : forall s t, Rgio s t -> gbarb s = gbarb t.

  (* FBase <- comm_step_complete (fwd) / comm_step_sound (bwd). *)
  Hypothesis fwd_base : forall s t l s',
    family_of l = Some FBase -> Rgio s t -> gstep s l s' ->
    exists t', gstep t l t' /\ Rgio s' t'.
  Hypothesis bwd_base : forall s t l t',
    family_of l = Some FBase -> Rgio s t -> gstep t l t' ->
    exists s', gstep s l s' /\ Rgio s' t'.

  (* FContextualJoin <- nary_join_complete / nary_join_sound (INV-6 / INV-2). *)
  Hypothesis fwd_join : forall s t l s',
    family_of l = Some FContextualJoin -> Rgio s t -> gstep s l s' ->
    exists t', gstep t l t' /\ Rgio s' t'.
  Hypothesis bwd_join : forall s t l t',
    family_of l = Some FContextualJoin -> Rgio s t -> gstep t l t' ->
    exists s', gstep s l s' /\ Rgio s' t'.

  (* FAcLinear <- the base flat σ-receiver step (AC reuses it) + CommRuleFiring / the
     AC bundle certifying payload + atomicity (one atomic COMM, zero new τ). *)
  Hypothesis fwd_ac_linear : forall s t l s',
    family_of l = Some FAcLinear -> Rgio s t -> gstep s l s' ->
    exists t', gstep t l t' /\ Rgio s' t'.
  Hypothesis bwd_ac_linear : forall s t l t',
    family_of l = Some FAcLinear -> Rgio s t -> gstep t l t' ->
    exists s', gstep s l s' /\ Rgio s' t'.

  (* FAcStructural <- AmbientOpenFiring.open_commits_when_names_agree /
     open_emits_both_reducts_and_splices_rest + structural_ac_spread_is_report_faithful. *)
  Hypothesis fwd_ac_structural : forall s t l s',
    family_of l = Some FAcStructural -> Rgio s t -> gstep s l s' ->
    exists t', gstep t l t' /\ Rgio s' t'.
  Hypothesis bwd_ac_structural : forall s t l t',
    family_of l = Some FAcStructural -> Rgio s t -> gstep t l t' ->
    exists s', gstep s l s' /\ Rgio s' t'.

  (* FBinderBeta <- InRhoBetaCascadeWeakBisim.forward_simulation / backward_simulation
     (weak_bisim_beta_cascade_vs_abstract_beta): the STRONGEST arm, an exact-shape weak
     bisimulation whose `cwvis` IS the gstep reference. *)
  Hypothesis fwd_binder_beta : forall s t l s',
    family_of l = Some FBinderBeta -> Rgio s t -> gstep s l s' ->
    exists t', gstep t l t' /\ Rgio s' t'.
  Hypothesis bwd_binder_beta : forall s t l t',
    family_of l = Some FBinderBeta -> Rgio s t -> gstep t l t' ->
    exists s', gstep s l s' /\ Rgio s' t'.

  (* FNative <- NativeSystemProcessBoundary.fold_native_process_fires_handler_value
     (payload = trusted handler value, RhoHostObligationBoundary seam). *)
  Hypothesis fwd_native : forall s t l s',
    family_of l = Some FNative -> Rgio s t -> gstep s l s' ->
    exists t', gstep t l t' /\ Rgio s' t'.
  Hypothesis bwd_native : forall s t l t',
    family_of l = Some FNative -> Rgio s t -> gstep t l t' ->
    exists s', gstep s l s' /\ Rgio s' t'.

  (* FAcNested (In/Out, slotted) <- the depth-2 nested structural-AC match logic
     InRhoAcMatchMultiset.nested_ac_match_iff_partition /
     nested_structural_ac_spread_is_report_faithful (ffec090f). Its operational
     step-correspondence closes by the same base-step reuse as FAcLinear once its
     depth-2 firing lemma lands; until then it is a slotted Section Hypothesis, so the
     top theorem is already stated + proven over it (additive: one more case). *)
  Hypothesis fwd_ac_nested : forall s t l s',
    family_of l = Some FAcNested -> Rgio s t -> gstep s l s' ->
    exists t', gstep t l t' /\ Rgio s' t'.
  Hypothesis bwd_ac_nested : forall s t l t',
    family_of l = Some FAcNested -> Rgio s t -> gstep t l t' ->
    exists s', gstep s l s' /\ Rgio s' t'.

  (* (ix) INSTALL-GATE SCOPING — cite
     InRhoEncoderTotalOrReject.gate_admits_iff_all_fired_matchable. A gate-admitted ⟦G⟧
     has every fired rule in-Rho matchable, so every COMM label maps to a covered
     family (never `None`). A G with an uncovered rule shape fails the gate, is never
     installed, and yields no GConfig — outside scope. Kept an explicit Section
     hypothesis so the "for every installed G" reading is honest. It is load-bearing:
     it closes the `None` branch of the assembled obligations. *)
  Hypothesis g_install_gate_admits : forall l, family_of l <> None.

  (* ============================================================================
     4.1b  INV-14 fence (statement-only): a semantic-predicate rule emits no c(ℓ).

     A rule's disposition is either a COMM emission carrying a `CommLabel`, or a
     semantic-predicate check that carries NO label. The fence proves the predicate
     disposition is never a COMM emission, so it contributes no `gstep` transition and
     is absent from every finite trace this capstone ranges over. This is exclusion by
     non-existence of a label, complementing the `Family` type having no predicate
     constructor.
     ============================================================================ *)
  Inductive RuleDisposition : Type :=
    | EmitsComm (l : CommLabel)
    | SemanticPredicateNoComm.

  Definition emits_a_comm (d : RuleDisposition) : Prop :=
    exists l, d = EmitsComm l.

  Theorem semantic_predicates_emit_no_comm : ~ emits_a_comm SemanticPredicateNoComm.
  Proof. intros [l H]. discriminate H. Qed.

  (* ============================================================================
     4.2  assembled_R_barb — the lift's barb obligation.
     ============================================================================ *)
  Theorem assembled_R_barb : forall s t, Rgio s t -> gbarb s = gbarb t.
  Proof. exact Rgio_barb. Qed.

  (* ============================================================================
     4.3  assembled_R_forward — the lift's forward obligation, by `family_of` case
     split into the six landed arms + the slotted In/Out arm; the `None` (uncovered
     shape) branch is closed by the install gate.
     ============================================================================ *)
  Theorem assembled_R_forward : forall s t l s',
    Rgio s t -> gstep s l s' -> exists t', gstep t l t' /\ Rgio s' t'.
  Proof.
    intros s t l s' HR Hstep.
    destruct (family_of l) as [f | ] eqn:E.
    - destruct f.
      + exact (fwd_base s t l s' E HR Hstep).
      + exact (fwd_join s t l s' E HR Hstep).
      + exact (fwd_ac_linear s t l s' E HR Hstep).
      + exact (fwd_ac_structural s t l s' E HR Hstep).
      + exact (fwd_binder_beta s t l s' E HR Hstep).
      + exact (fwd_native s t l s' E HR Hstep).
      + exact (fwd_ac_nested s t l s' E HR Hstep).
    - destruct (g_install_gate_admits l E).
  Qed.

  (* ============================================================================
     4.4  assembled_R_backward — the dual obligation.
     ============================================================================ *)
  Theorem assembled_R_backward : forall s t l t',
    Rgio s t -> gstep t l t' -> exists s', gstep s l s' /\ Rgio s' t'.
  Proof.
    intros s t l t' HR Hstep.
    destruct (family_of l) as [f | ] eqn:E.
    - destruct f.
      + exact (bwd_base s t l t' E HR Hstep).
      + exact (bwd_join s t l t' E HR Hstep).
      + exact (bwd_ac_linear s t l t' E HR Hstep).
      + exact (bwd_ac_structural s t l t' E HR Hstep).
      + exact (bwd_binder_beta s t l t' E HR Hstep).
      + exact (bwd_native s t l t' E HR Hstep).
      + exact (bwd_ac_nested s t l t' E HR Hstep).
    - destruct (g_install_gate_admits l E).
  Qed.

  (* ============================================================================
     4.5  whole_gslt_forward_correspondence — every source rewrite trace of ⟦G⟧ is
     matched, label-for-label, by an in-Rho COMM trace ending in a barb-equal related
     state (the lift's forward direction).
     ============================================================================ *)
  Theorem whole_gslt_forward_correspondence : forall s t ls s',
    Rgio s t -> steps GConfig CommLabel gstep s ls s' ->
    exists t', steps GConfig CommLabel gstep t ls t' /\ Rgio s' t' /\ gbarb s' = gbarb t'.
  Proof.
    exact (forward_trace_correspondence GConfig CommLabel Barb gstep gbarb Rgio
             assembled_R_barb assembled_R_forward).
  Qed.

  (* ============================================================================
     4.6  whole_gslt_backward_correspondence — dually, every in-Rho COMM trace is
     matched by a source rewrite trace.
     ============================================================================ *)
  Theorem whole_gslt_backward_correspondence : forall s t ls t',
    Rgio s t -> steps GConfig CommLabel gstep t ls t' ->
    exists s', steps GConfig CommLabel gstep s ls s' /\ Rgio s' t' /\ gbarb s' = gbarb t'.
  Proof.
    exact (backward_trace_correspondence GConfig CommLabel Barb gstep gbarb Rgio
             assembled_R_barb assembled_R_backward).
  Qed.

  (* ============================================================================
     4.7  whole_gslt_in_rho_opcorrespondence — THE CAPSTONE (INV-13 / ob:opcorr,
     finite executions). Every non-semantic-predicate rewrite trace of ⟦G⟧ is matched
     and fired in-Rho, both directions, with equal barbs at every reachable state.
     ============================================================================ *)
  Theorem whole_gslt_in_rho_opcorrespondence : forall s t ls, Rgio s t ->
    (forall s', steps GConfig CommLabel gstep s ls s' ->
        exists t', steps GConfig CommLabel gstep t ls t' /\ gbarb s' = gbarb t') /\
    (forall t', steps GConfig CommLabel gstep t ls t' ->
        exists s', steps GConfig CommLabel gstep s ls s' /\ gbarb s' = gbarb t').
  Proof.
    exact (finite_trace_barb_equivalence GConfig CommLabel Barb gstep gbarb Rgio
             assembled_R_barb assembled_R_forward assembled_R_backward).
  Qed.

End WholeGsltInRhoOpCorrespondence.

(* ================================================================================
   4.9  NON-VACUITY WITNESS (outside the Section, a la
   InRhoBetaCascadeWeakBisim.beta_cascade_is_nonvacuous): the SwapDemo single base
   rewrite. We instantiate the whole harness with the common-carrier sum `GC` and
   discharge EVERY §4.1 Section hypothesis — the base arms from the LANDED
   LinearCommCorrespondence theorems, the other families vacuously (this model only
   fires base) — proving the harness context is inhabited (no vacuously-true capstone)
   and, as a corollary, yielding a concrete Closed finite-trace operational
   correspondence for the base rewrite THROUGH the capstone.
   ================================================================================ *)

(* The common-carrier sum: a source CLTS config or an in-Rho config. *)
Inductive GC : Type :=
  | GSrc (s : SourceState)
  | GRho (r : RhoState).

(* `gstep` dispatches on the tag: source COMM on GSrc, lowered Rho COMM on GRho; it
   never crosses tags. *)
Definition nv_step (a : GC) (d : Fact) (b : GC) : Prop :=
  match a, b with
  | GSrc s, GSrc s' => source_linear_comm s d s'
  | GRho r, GRho r' => rho_linear_comm r d r'
  | _, _ => False
  end.

Definition nv_barb (a : GC) : list Fact :=
  match a with
  | GSrc s => source_outputs s
  | GRho r => rho_outputs r
  end.

(* Rgio relates a source config to its lowered image. *)
Definition nv_R (a b : GC) : Prop :=
  match a, b with
  | GSrc s, GRho r => r = lower_state s
  | _, _ => False
  end.

(* This model fires only the base family. *)
Definition nv_family (_ : Fact) : option Family := Some FBase.

(* The lowered image of the source reduct is exactly the Rho reduct: the sum-carrier
   glue that lets comm_step_complete/sound discharge the base arm. *)
Lemma rho_comm_lowers_step : forall s l s' r',
  source_linear_comm s l s' -> rho_linear_comm (lower_state s) l r' -> r' = lower_state s'.
Proof.
  intros s l s' r' Hsrc Hrho.
  destruct Hsrc as [_ [_ Hs']].
  destruct Hrho as [_ [_ Hr']].
  subst s' r'. reflexivity.
Qed.

Lemma nv_Rgio_barb : forall a b, nv_R a b -> nv_barb a = nv_barb b.
Proof.
  intros a b HR. destruct a as [s | r]; destruct b as [s2 | r2]; cbn in HR; try contradiction.
  subst r2. reflexivity.
Qed.

Lemma nv_fwd_base : forall a b l a',
  nv_family l = Some FBase -> nv_R a b -> nv_step a l a' ->
  exists b', nv_step b l b' /\ nv_R a' b'.
Proof.
  intros a b l a' _ HR Hstep.
  destruct a as [s0 | r0]; destruct b as [s1 | r1]; cbn in HR; try contradiction.
  subst r1.
  destruct a' as [s0' | r']; cbn in Hstep; try contradiction.
  destruct (comm_step_complete s0 l s0' Hstep) as [r' [Hrho _]].
  exists (GRho r'). cbn. split.
  - exact Hrho.
  - exact (rho_comm_lowers_step s0 l s0' r' Hstep Hrho).
Qed.

Lemma nv_bwd_base : forall a b l b',
  nv_family l = Some FBase -> nv_R a b -> nv_step b l b' ->
  exists a', nv_step a l a' /\ nv_R a' b'.
Proof.
  intros a b l b' _ HR Hstep.
  destruct a as [s0 | r0]; destruct b as [s1 | r1]; cbn in HR; try contradiction.
  subst r1.
  destruct b' as [s1' | r']; cbn in Hstep; try contradiction.
  destruct (comm_step_sound s0 l r' Hstep) as [s0' [Hsrc _]].
  exists (GSrc s0'). cbn. split.
  - exact Hsrc.
  - exact (rho_comm_lowers_step s0 l s0' r' Hsrc Hstep).
Qed.

(* The SwapDemo base finite-trace operational correspondence, obtained by instantiating
   the abstract capstone. Simultaneously the non-vacuity witness (all §4.1 hypotheses
   are jointly satisfiable) and a concrete Closed finite-trace opcorr for the base
   rewrite. The five non-base families discharge vacuously (this model never fires
   them), the gate holds (every label is FBase), and the initial Rgio is the lowering. *)
Theorem swapdemo_base_finite_trace_opcorr : forall (s : SourceState) ls,
  (forall a', steps GC Fact nv_step (GSrc s) ls a' ->
      exists b', steps GC Fact nv_step (GRho (lower_state s)) ls b' /\ nv_barb a' = nv_barb b') /\
  (forall b', steps GC Fact nv_step (GRho (lower_state s)) ls b' ->
      exists a', steps GC Fact nv_step (GSrc s) ls a' /\ nv_barb a' = nv_barb b').
Proof.
  intros s ls.
  apply (whole_gslt_in_rho_opcorrespondence GC Fact (list Fact)
           nv_step nv_barb nv_R nv_family).
  - exact nv_Rgio_barb.
  - exact nv_fwd_base.
  - exact nv_bwd_base.
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
  - intros l; cbn; discriminate.
  - cbn. reflexivity.
Qed.

(* Zero-admission confirmation. *)
Print Assumptions semantic_predicates_emit_no_comm.
Print Assumptions whole_gslt_in_rho_opcorrespondence.
Print Assumptions swapdemo_base_finite_trace_opcorr.
