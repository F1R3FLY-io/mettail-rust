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
 * The slotted In/Out arm FAcNested NOW cites an OPERATIONAL firing lemma too — on
 * equal footing with the other six:
 *   - FAcNested       <- AmbientInOutFiring.inout_step_complete / inout_step_sound
 *                        / inout_lower_preserves_barbs (the DEPTH-2 analogue of the
 *                        FAcStructural OpenRule firing), assembling the depth-2 match
 *                        logic InRhoAcMatchMultiset.nested_ac_match_iff_partition /
 *                        nested_structural_ac_spread_is_report_faithful (commit ffec090f)
 *                        + the cross-level guard AcNonLinearConsistency.
 *                        ac_nl_cross_level_commits / ac_nl_cross_level_reject_safe into
 *                        a source<->in-Rho step-correspondence. It is discharged
 *                        NON-VACUOUSLY (not merely asserted) in the companion witness
 *                        WholeGsltInRhoOpCorrespondenceInOutViaFiring.v.
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
 * ---------------------------------------------------------------------------------
 * A-S5.7 (§5 below): THE ITERATED-DRIVING UPGRADE (plan v2 §7.4)
 * ---------------------------------------------------------------------------------
 *
 * Since the A-S5.6 production flip, one `exec` of a drive-admitted language is one
 * generated `rho_net_drive_invocation_to` seed — the in-Rho quiescence driver firing
 * an ITERATED CHAIN of family COMMs to rest (InRhoQuiescenceDriver.v), not one COMM
 * per invocation. §5 RE-STATES the per-family premises at exactly that granularity:
 * per-family fwd/bwd premises over DRIVE-MEDIATED MULTI-STEP TRACES (family-
 * homogeneous `steps` bursts), assembled into the capstone over whole DRIVE
 * SCHEDULES plus the decision-(3) PER-TRACE quiescence transfer. The upgraded
 * premises are EQUIVALENT in strength to the §4.1 single-step set (each direction is
 * proven: `iterated_premises_recover_step_*` recovers the single-step obligations
 * from singleton bursts, and `per_step_arm_lifts_to_burst_*` lifts any single-step
 * discharge to the burst shape — the same pointwise lift
 * InRhoQuiescenceDriver.drive_weak_bisim performs for beta), so §5 is a CONSERVATIVE
 * EXTENSION: every §4 theorem and Print Assumptions gate below stays in force,
 * byte-identical. The SwapDemo witness is re-instantiated against the upgraded
 * shapes in §5.4; the In/Out and beta-via-driver re-instantiations live in the
 * companions WholeGsltInRhoOpCorrespondenceInOutViaFiring.v and
 * WholeGsltInRhoOpCorrespondenceIteratedViaDriver.v (the latter consumes
 * InRhoQuiescenceDriver.drive_weak_bisim and the A-S5.5 bag-model theorems
 * literally).
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

  (* The (iii) thread (consumed ONLY by whole_gslt_opcorr_over_optimal_matching below):
     `gstep_opt` is the O1-OPTIMAL in-Rho COMM — the channel keyed by the interned
     StateId trace `tc(K)` rather than the runtime location ℓ — and `Rso` relates a
     SOUND in-Rho config to its OPTIMAL image. Declared here so the optimal theorem's
     instantiation supplies all carrier/step parameters up front. *)
  Variable gstep_opt : GConfig -> CommLabel -> GConfig -> Prop.
  Variable Rso : GConfig -> GConfig -> Prop.

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

  (* FAcNested (In/Out) <- AmbientInOutFiring.inout_step_complete / inout_step_sound
     (the operational firing FV — the DEPTH-2 analogue of the FAcStructural OpenRule
     arm), assembled from the depth-2 nested structural-AC match logic
     InRhoAcMatchMultiset.nested_ac_match_iff_partition /
     nested_structural_ac_spread_is_report_faithful (ffec090f) + the cross-level guard
     AcNonLinearConsistency.ac_nl_cross_level_commits / ac_nl_cross_level_reject_safe.
     Its operational step-correspondence NOW LANDED, it is on EQUAL FOOTING with
     FAcStructural: discharged NON-VACUOUSLY in the companion
     WholeGsltInRhoOpCorrespondenceInOutViaFiring.v (inoutdemo_nested_finite_trace_opcorr,
     the depth-2 mirror of the base SwapDemo witness). It remains a slotted Section
     Hypothesis here so the harness carries no import (additive: one more case). *)
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

  (* ============================================================================
     4.8  THE (iii) THREAD — upgrading the capstone from the SOUND baseline to the
     O1-OPTIMAL in-Rho matching (the `rem:nonopt` discharge).

     The six arms establish source↔in-Rho for the SOUND (location-keyed, model-b)
     scheme (that is 4.5/4.6/4.7). Obligation (iii),
     advanced_automata/InRhoSameCLTSWeakBisim.same_clts_weak_bisim, proves the SOUND
     and OPTIMAL channel schemes induce the SAME context-labelled transition system —
     the sa:/eq: matching COMMs are τ, so the two schemes are weakly bisimilar, and
     (its relation R equating the fired-redex sets) barb-preserving. TRANSITIVITY of
     the finite-trace correspondence then upgrades the capstone from "sound baseline"
     to "O1-optimal in-Rho matching".

     The three `matching_locus_*` hypotheses are exactly the shape of
     same_clts_weak_bisim's two bisimulation clauses (fwd/bwd) plus its barb
     preservation. This is BUILD-WIRING OPTION (b) (interim, zero cross-project churn):
     (iii) is threaded as a cited Section Hypothesis, so the theorem stays Closed (a
     Hypothesis is not an Axiom). Option (a) — the literal
     `From AdvancedAutomata Require Import InRhoSameCLTSWeakBisim` discharge — is
     attempted separately (see WholeGsltInRhoOpCorrespondenceOptimalViaSameClts.v /
     the report) so the harness here carries no cross-project -Q edge.
     ============================================================================ *)

  (* (iii) barb preservation: sound and optimal in-Rho images have equal barbs
     (same_clts_weak_bisim's R equates the fired-redex sets, whose resting sends ARE
     the barb). *)
  Hypothesis matching_locus_barb : forall s t, Rso s t -> gbarb s = gbarb t.
  (* (iii) forward: every SOUND COMM is matched, label-for-label, by an OPTIMAL COMM
     (same_clts_weak_bisim's backward clause: sound fires ⇒ optimal matches). *)
  Hypothesis matching_locus_fwd : forall s t l s',
    Rso s t -> gstep s l s' -> exists t', gstep_opt t l t' /\ Rso s' t'.
  (* (iii) backward: every OPTIMAL COMM is matched by a SOUND COMM
     (same_clts_weak_bisim's forward clause: optimal fires ⇒ sound matches). *)
  Hypothesis matching_locus_bwd : forall s t l t',
    Rso s t -> gstep_opt t l t' -> exists s', gstep s l s' /\ Rso s' t'.

  (* The sound↔optimal STEP bisimulation lifts to finite traces — a direct induction
     (the same shape as EndToEndCommCorrespondence.forward_trace_correspondence, but
     relating the two DIFFERENT step relations gstep and gstep_opt under Rso). *)
  Lemma sound_to_optimal_forward : forall s t ls s',
    Rso s t -> steps GConfig CommLabel gstep s ls s' ->
    exists t', steps GConfig CommLabel gstep_opt t ls t' /\ Rso s' t' /\ gbarb s' = gbarb t'.
  Proof.
    intros s t ls s' HR Hsteps. revert t HR.
    induction Hsteps as [s0 | s0 l s1 ls0 s2 Hstep Hsteps IH]; intros t HR.
    - exists t. split; [constructor | split; [exact HR | apply matching_locus_barb; exact HR]].
    - destruct (matching_locus_fwd s0 t l s1 HR Hstep) as [t1 [Ht1step Ht1R]].
      destruct (IH t1 Ht1R) as [t' [Ht'steps [Ht'R Ht'barb]]].
      exists t'. split.
      + econstructor; [exact Ht1step | exact Ht'steps].
      + split; [exact Ht'R | exact Ht'barb].
  Qed.

  Lemma optimal_to_sound_backward : forall s t ls t',
    Rso s t -> steps GConfig CommLabel gstep_opt t ls t' ->
    exists s', steps GConfig CommLabel gstep s ls s' /\ Rso s' t' /\ gbarb s' = gbarb t'.
  Proof.
    intros s t ls t' HR Hsteps. revert s HR.
    induction Hsteps as [t0 | t0 l t1 ls0 t2 Hstep Hsteps IH]; intros s HR.
    - exists s. split; [constructor | split; [exact HR | apply matching_locus_barb; exact HR]].
    - destruct (matching_locus_bwd s t0 l t1 HR Hstep) as [s1 [Hs1step Hs1R]].
      destruct (IH s1 Hs1R) as [s' [Hs'steps [Hs'R Hs'barb]]].
      exists s'. split.
      + econstructor; [exact Hs1step | exact Hs'steps].
      + split; [exact Hs'R | exact Hs'barb].
  Qed.

  (* whole_gslt_opcorr_over_optimal_matching — the capstone over the O1-OPTIMAL in-Rho
     matching: 4.5/4.6 (source↔sound) composed transitively with the (iii) trace
     transfer (sound↔optimal). Every source rewrite trace of ⟦G⟧ is matched by an
     OPTIMAL in-Rho COMM trace with equal barbs, both directions. This is the
     `rem:nonopt` discharge. *)
  Theorem whole_gslt_opcorr_over_optimal_matching : forall s t u ls,
    Rgio s t -> Rso t u ->
    (forall s', steps GConfig CommLabel gstep s ls s' ->
        exists u', steps GConfig CommLabel gstep_opt u ls u' /\ gbarb s' = gbarb u') /\
    (forall u', steps GConfig CommLabel gstep_opt u ls u' ->
        exists s', steps GConfig CommLabel gstep s ls s' /\ gbarb s' = gbarb u').
  Proof.
    intros s t u ls HRst HRtu. split.
    - intros s' Hs.
      destruct (whole_gslt_forward_correspondence s t ls s' HRst Hs)
        as [t' [Ht'steps [_ Hbst]]].
      destruct (sound_to_optimal_forward t u ls t' HRtu Ht'steps)
        as [u' [Hu'steps [_ Hbtu]]].
      exists u'. split; [exact Hu'steps | rewrite Hbst; exact Hbtu].
    - intros u' Hu.
      destruct (optimal_to_sound_backward t u ls u' HRtu Hu)
        as [t' [Ht'steps [_ Hbtu]]].
      destruct (whole_gslt_backward_correspondence s t ls t' HRst Ht'steps)
        as [s' [Hs'steps [_ Hbst]]].
      exists s'. split; [exact Hs'steps | rewrite Hbst; exact Hbtu].
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

(* ---- 4.8 non-vacuity: the SwapDemo base rewrite over the OPTIMAL matching ----
   In this model the OPTIMAL scheme coincides with the SOUND scheme (a single base
   rewrite has no location/StateId distinction), so `gstep_opt := nv_step` and
   `Rso := nv_eq` (identity). Discharging the three additional `matching_locus_*`
   hypotheses (trivially, since sound = optimal here) shows the (iii)-threaded
   harness context is inhabited; the genuine content — that optimal SHARES channels
   where sound SEPARATES yet stays bisimilar — is proven in
   InRhoSameCLTSWeakBisim.optimal_shares_where_sound_separates, which the harness
   consumes via `matching_locus_*`. *)
Definition nv_eq (a b : GC) : Prop := a = b.

Theorem swapdemo_base_opcorr_over_optimal : forall (s : SourceState) (t u : GC) ls,
  nv_R (GSrc s) t -> nv_eq t u ->
  (forall a', steps GC Fact nv_step (GSrc s) ls a' ->
      exists u', steps GC Fact nv_step u ls u' /\ nv_barb a' = nv_barb u') /\
  (forall u', steps GC Fact nv_step u ls u' ->
      exists a', steps GC Fact nv_step (GSrc s) ls a' /\ nv_barb a' = nv_barb u').
Proof.
  intros s t u ls Hrgio Hrso.
  eapply (whole_gslt_opcorr_over_optimal_matching GC Fact (list Fact)
           nv_step nv_barb nv_R nv_family nv_step nv_eq).
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
  - intros a b Hab; unfold nv_eq in Hab; subst b; reflexivity.
  - intros a b l a' Hab Hstep; unfold nv_eq in Hab; subst b;
      exists a'; split; [exact Hstep | unfold nv_eq; reflexivity].
  - intros a b l b' Hab Hstep; unfold nv_eq in Hab; subst b;
      exists b'; split; [exact Hstep | unfold nv_eq; reflexivity].
  - exact Hrgio.
  - exact Hrso.
Qed.

(* Fully concrete corollary: the SwapDemo source↔optimal-in-Rho finite-trace opcorr,
   where the optimal image is the lowered config (sound = optimal for a base rewrite). *)
Corollary swapdemo_base_opcorr_over_optimal_concrete : forall (s : SourceState) ls,
  (forall a', steps GC Fact nv_step (GSrc s) ls a' ->
      exists u', steps GC Fact nv_step (GRho (lower_state s)) ls u' /\ nv_barb a' = nv_barb u') /\
  (forall u', steps GC Fact nv_step (GRho (lower_state s)) ls u' ->
      exists a', steps GC Fact nv_step (GSrc s) ls a' /\ nv_barb a' = nv_barb u').
Proof.
  intros s ls.
  apply (swapdemo_base_opcorr_over_optimal s (GRho (lower_state s)) (GRho (lower_state s)) ls).
  - cbn. reflexivity.
  - unfold nv_eq. reflexivity.
Qed.

(* Zero-admission confirmation. *)
Print Assumptions semantic_predicates_emit_no_comm.
Print Assumptions whole_gslt_in_rho_opcorrespondence.
Print Assumptions swapdemo_base_finite_trace_opcorr.
Print Assumptions whole_gslt_opcorr_over_optimal_matching.
Print Assumptions swapdemo_base_opcorr_over_optimal.
Print Assumptions swapdemo_base_opcorr_over_optimal_concrete.

(* ================================================================================
   5.  A-S5.7 — THE ITERATED-DRIVING UPGRADE (plan v2 §7.4).

   Everything above is the landed single-step harness, byte-identical. This section
   re-states the per-family premises at the PRODUCTION granularity of the A-S5.6
   flip: one exec = one in-Rho quiescence-driver invocation = an ITERATED chain of
   family COMMs (InRhoQuiescenceDriver.v), so the premises range over DRIVE-MEDIATED
   MULTI-STEP TRACES — a family-homogeneous `steps` burst (the visible label chain
   of one driver-invocation segment; the EMPTY burst is the already-quiescent drive,
   the aiter_refl/citer_refl case).

   DISCHARGE MAP (what stands behind each upgraded premise at a concrete
   instantiation — plan v2 §7.4 "discharged by (1)"):
   - FBinderBeta   <- InRhoQuiescenceDriver.drive_weak_bisim, THE iterated beta weak
     bisimulation: its two clauses are exactly this premise pair in chain form at
     the `represents` instantiation; the label-preserving burst form is its per-link
     refinement, obtained from InRhoBetaCascadeWeakBisim.forward_/backward_simulation
     by `per_step_arm_lifts_to_burst_*` — the SAME pointwise lift drive_weak_bisim
     itself performs over aiter/citer. Consumed LITERALLY (proj1/proj2) in the
     companion WholeGsltInRhoOpCorrespondenceIteratedViaDriver.v.
   - FBase / FContextualJoin / FAcLinear / FAcStructural / FNative / FAcNested
     <- their §4.1-cited landed per-step theorems, lifted by
     `per_step_arm_lifts_to_burst_*`; the SwapDemo base arms are re-instantiated
     against the upgraded shapes in §5.4 below, the In/Out arms in the companion
     WholeGsltInRhoOpCorrespondenceInOutViaFiring.v.
   - The AC families' REST condition (the shape of a burst's quiescent endpoint) is
     grounded driver-side by the A-S5.5 bag model: InRhoQuiescenceDriver.
     bag_quiescence_sound (EVERY bag drive rests FLAT — no nested bag hides a
     sibling redex from the NF scan) + driver_flatten_agrees_with_add_flattened_bag
     (the driver's reassembly splice = the host's add_flattened_bag), and
     Lambda-side by InRhoQuiescenceDriver.quiescence_sound (every DDone drive rests
     beta-NF). Quiescence here is PER-TRACE (user decision (3)): the §5.3 theorems
     speak only of THE GIVEN schedule's resting endpoint — no unique-normal-form
     claim is made for the non-confluent families (Ambient).

   CONSERVATIVE EXTENSION: the burst premises are EQUIVALENT to the §4.1 single-step
   premises — `iterated_premises_recover_step_forward/_backward` recover the §4.1
   obligations from singleton bursts (so every §4 conclusion is re-derivable from
   the §5 premise set), and `per_step_arm_lifts_to_burst_*` derive the §5 premises
   from any §4.1-style discharge. No landed statement is weakened; the §4 Print
   Assumptions gates above stay in force.
   ================================================================================ *)

(* ────────────────────────────────────────────────────────────────────────────────
   5.0  Generic trace toolkit: nil/singleton inversions for the closed `steps`
   family, and the pointwise burst lift (the label-preserving form of the
   drive_weak_bisim chain lift).
   ──────────────────────────────────────────────────────────────────────────────── *)

Lemma steps_nil_inv : forall (State Label : Type)
    (step : State -> Label -> State -> Prop) (s s' : State),
  steps State Label step s [] s' -> s' = s.
Proof.
  intros State Label step s s' H.
  remember [] as ls eqn:Hls.
  destruct H as [s0 | s0 l0 s1 ls0 s2 Hstep Htail].
  - reflexivity.
  - discriminate Hls.
Qed.

Lemma steps_singleton_intro : forall (State Label : Type)
    (step : State -> Label -> State -> Prop) (s : State) (l : Label) (s' : State),
  step s l s' -> steps State Label step s [l] s'.
Proof.
  intros State Label step s l s' H.
  eapply steps_cons; [exact H | constructor].
Qed.

Lemma steps_singleton_inv : forall (State Label : Type)
    (step : State -> Label -> State -> Prop) (s : State) (l : Label) (s' : State),
  steps State Label step s [l] s' -> step s l s'.
Proof.
  intros State Label step s l s' H.
  remember [l] as ls eqn:Hls.
  destruct H as [s0 | s0 l0 s1 ls0 s2 Hstep Htail].
  - discriminate Hls.
  - injection Hls as Hl0 Hls0. subst l0 ls0.
    apply steps_nil_inv in Htail. subst s2. exact Hstep.
Qed.

(* The pointwise burst lift, FORWARD: a per-step arm (the §4.1 discharge shape,
   guarded by the label predicate P — concretely `fun l => family_of l = Some F`)
   lifts to the whole family-homogeneous burst. This is the label-preserving form
   of the lift InRhoQuiescenceDriver.drive_weak_bisim performs over aiter/citer
   chains (its proof is the same induction, pointwise over the chain). *)
Lemma per_step_arm_lifts_to_burst_forward :
  forall (GConfig CommLabel : Type)
         (gstep : GConfig -> CommLabel -> GConfig -> Prop)
         (Rgio : GConfig -> GConfig -> Prop)
         (P : CommLabel -> Prop),
    (forall s t l s', P l -> Rgio s t -> gstep s l s' ->
        exists t', gstep t l t' /\ Rgio s' t') ->
    forall s t ls s', Forall P ls -> Rgio s t ->
      steps GConfig CommLabel gstep s ls s' ->
      exists t', steps GConfig CommLabel gstep t ls t' /\ Rgio s' t'.
Proof.
  intros GConfig CommLabel gstep Rgio P Harm s t ls s' Hfam HR Hsteps.
  revert t HR Hfam.
  induction Hsteps as [s0 | s0 l s1 ls0 s2 Hstep Hsteps IH]; intros t HR Hfam.
  - exists t. split; [constructor | exact HR].
  - inversion Hfam as [| x xs HPl Hfam0]; subst.
    destruct (Harm s0 t l s1 HPl HR Hstep) as [t1 [Ht1 HR1]].
    destruct (IH t1 HR1 Hfam0) as [t' [Ht' HR']].
    exists t'. split; [econstructor; [exact Ht1 | exact Ht'] | exact HR'].
Qed.

(* The pointwise burst lift, BACKWARD (the dual: the burst runs on the in-Rho
   side). *)
Lemma per_step_arm_lifts_to_burst_backward :
  forall (GConfig CommLabel : Type)
         (gstep : GConfig -> CommLabel -> GConfig -> Prop)
         (Rgio : GConfig -> GConfig -> Prop)
         (P : CommLabel -> Prop),
    (forall s t l t', P l -> Rgio s t -> gstep t l t' ->
        exists s', gstep s l s' /\ Rgio s' t') ->
    forall s t ls t', Forall P ls -> Rgio s t ->
      steps GConfig CommLabel gstep t ls t' ->
      exists s', steps GConfig CommLabel gstep s ls s' /\ Rgio s' t'.
Proof.
  intros GConfig CommLabel gstep Rgio P Harm s t ls t' Hfam HR Hsteps.
  revert s HR Hfam.
  induction Hsteps as [t0 | t0 l t1 ls0 t2 Hstep Hsteps IH]; intros s HR Hfam.
  - exists s. split; [constructor | exact HR].
  - inversion Hfam as [| x xs HPl Hfam0]; subst.
    destruct (Harm s t0 l t1 HPl HR Hstep) as [s1 [Hs1 HR1]].
    destruct (IH s1 HR1 Hfam0) as [s' [Hs' HR']].
    exists s'. split; [econstructor; [exact Hs1 | exact Hs'] | exact HR'].
Qed.

(* ────────────────────────────────────────────────────────────────────────────────
   5.1  The iterated harness: per-family premises over drive-mediated multi-step
   traces, the assembled capstone, drive schedules, and per-trace quiescence.
   ──────────────────────────────────────────────────────────────────────────────── *)

Section WholeGsltInRhoIteratedDriving.

  (* The same whole-⟦G⟧ carrier surface as §4.0. *)
  Variable GConfig : Type.
  Variable CommLabel : Type.
  Variable Barb : Type.
  Variable gstep : GConfig -> CommLabel -> GConfig -> Prop.
  Variable gbarb : GConfig -> Barb.
  Variable Rgio : GConfig -> GConfig -> Prop.
  Variable family_of : CommLabel -> option Family.

  (* A family-homogeneous label list: the visible chain of ONE driver-invocation
     segment for family F. The empty list is the already-quiescent drive. *)
  Definition family_labels (F : Family) (ls : list CommLabel) : Prop :=
    Forall (fun l => family_of l = Some F) ls.

  (* One drive BURST of family F: a drive-mediated multi-step trace. *)
  Definition drive_burst (F : Family) (s : GConfig) (ls : list CommLabel)
      (s' : GConfig) : Prop :=
    family_labels F ls /\ steps GConfig CommLabel gstep s ls s'.

  (* Rgio preserves barbs (as §4.1). *)
  Hypothesis Rgio_barb : forall s t, Rgio s t -> gbarb s = gbarb t.

  (* ── The UPGRADED per-family premises (plan v2 §7.4): fwd/bwd over bursts. ──
     Discharge citations per family are in the §5 banner above; each is obtained
     from its §4.1-cited landed per-step theorem via `per_step_arm_lifts_to_burst_*`
     (done literally for FBase in §5.4 and for FAcNested / FBinderBeta in the
     companions), and for FBinderBeta the chain form IS
     InRhoQuiescenceDriver.drive_weak_bisim. *)

  Hypothesis drive_fwd_base : forall s t ls s',
    family_labels FBase ls -> Rgio s t ->
    steps GConfig CommLabel gstep s ls s' ->
    exists t', steps GConfig CommLabel gstep t ls t' /\ Rgio s' t'.
  Hypothesis drive_bwd_base : forall s t ls t',
    family_labels FBase ls -> Rgio s t ->
    steps GConfig CommLabel gstep t ls t' ->
    exists s', steps GConfig CommLabel gstep s ls s' /\ Rgio s' t'.

  Hypothesis drive_fwd_join : forall s t ls s',
    family_labels FContextualJoin ls -> Rgio s t ->
    steps GConfig CommLabel gstep s ls s' ->
    exists t', steps GConfig CommLabel gstep t ls t' /\ Rgio s' t'.
  Hypothesis drive_bwd_join : forall s t ls t',
    family_labels FContextualJoin ls -> Rgio s t ->
    steps GConfig CommLabel gstep t ls t' ->
    exists s', steps GConfig CommLabel gstep s ls s' /\ Rgio s' t'.

  Hypothesis drive_fwd_ac_linear : forall s t ls s',
    family_labels FAcLinear ls -> Rgio s t ->
    steps GConfig CommLabel gstep s ls s' ->
    exists t', steps GConfig CommLabel gstep t ls t' /\ Rgio s' t'.
  Hypothesis drive_bwd_ac_linear : forall s t ls t',
    family_labels FAcLinear ls -> Rgio s t ->
    steps GConfig CommLabel gstep t ls t' ->
    exists s', steps GConfig CommLabel gstep s ls s' /\ Rgio s' t'.

  Hypothesis drive_fwd_ac_structural : forall s t ls s',
    family_labels FAcStructural ls -> Rgio s t ->
    steps GConfig CommLabel gstep s ls s' ->
    exists t', steps GConfig CommLabel gstep t ls t' /\ Rgio s' t'.
  Hypothesis drive_bwd_ac_structural : forall s t ls t',
    family_labels FAcStructural ls -> Rgio s t ->
    steps GConfig CommLabel gstep t ls t' ->
    exists s', steps GConfig CommLabel gstep s ls s' /\ Rgio s' t'.

  Hypothesis drive_fwd_binder_beta : forall s t ls s',
    family_labels FBinderBeta ls -> Rgio s t ->
    steps GConfig CommLabel gstep s ls s' ->
    exists t', steps GConfig CommLabel gstep t ls t' /\ Rgio s' t'.
  Hypothesis drive_bwd_binder_beta : forall s t ls t',
    family_labels FBinderBeta ls -> Rgio s t ->
    steps GConfig CommLabel gstep t ls t' ->
    exists s', steps GConfig CommLabel gstep s ls s' /\ Rgio s' t'.

  Hypothesis drive_fwd_native : forall s t ls s',
    family_labels FNative ls -> Rgio s t ->
    steps GConfig CommLabel gstep s ls s' ->
    exists t', steps GConfig CommLabel gstep t ls t' /\ Rgio s' t'.
  Hypothesis drive_bwd_native : forall s t ls t',
    family_labels FNative ls -> Rgio s t ->
    steps GConfig CommLabel gstep t ls t' ->
    exists s', steps GConfig CommLabel gstep s ls s' /\ Rgio s' t'.

  Hypothesis drive_fwd_ac_nested : forall s t ls s',
    family_labels FAcNested ls -> Rgio s t ->
    steps GConfig CommLabel gstep s ls s' ->
    exists t', steps GConfig CommLabel gstep t ls t' /\ Rgio s' t'.
  Hypothesis drive_bwd_ac_nested : forall s t ls t',
    family_labels FAcNested ls -> Rgio s t ->
    steps GConfig CommLabel gstep t ls t' ->
    exists s', steps GConfig CommLabel gstep s ls s' /\ Rgio s' t'.

  (* (ix) install-gate scoping, as §4.1. *)
  Hypothesis g_install_gate_admits : forall l, family_of l <> None.

  (* Family dispatch: pick the burst premise for a family. *)
  Lemma drive_fwd_family : forall F s t ls s',
    family_labels F ls -> Rgio s t ->
    steps GConfig CommLabel gstep s ls s' ->
    exists t', steps GConfig CommLabel gstep t ls t' /\ Rgio s' t'.
  Proof.
    intros F. destruct F.
    - exact drive_fwd_base.
    - exact drive_fwd_join.
    - exact drive_fwd_ac_linear.
    - exact drive_fwd_ac_structural.
    - exact drive_fwd_binder_beta.
    - exact drive_fwd_native.
    - exact drive_fwd_ac_nested.
  Qed.

  Lemma drive_bwd_family : forall F s t ls t',
    family_labels F ls -> Rgio s t ->
    steps GConfig CommLabel gstep t ls t' ->
    exists s', steps GConfig CommLabel gstep s ls s' /\ Rgio s' t'.
  Proof.
    intros F. destruct F.
    - exact drive_bwd_base.
    - exact drive_bwd_join.
    - exact drive_bwd_ac_linear.
    - exact drive_bwd_ac_structural.
    - exact drive_bwd_binder_beta.
    - exact drive_bwd_native.
    - exact drive_bwd_ac_nested.
  Qed.

  (* ── 5.1a  Conservativity: the upgraded premises RECOVER the §4.1 single-step
     obligations (a singleton burst is one step; the gate closes `None`). ── *)

  Lemma iterated_premises_recover_step_forward : forall s t l s',
    Rgio s t -> gstep s l s' ->
    exists t', gstep t l t' /\ Rgio s' t'.
  Proof.
    intros s t l s' HR Hstep.
    destruct (family_of l) as [f | ] eqn:E.
    - assert (Hfam : family_labels f [l])
        by (constructor; [exact E | constructor]).
      destruct (drive_fwd_family f s t [l] s' Hfam HR
                  (steps_singleton_intro GConfig CommLabel gstep s l s' Hstep))
        as [t' [Ht' HR']].
      exists t'. split;
        [exact (steps_singleton_inv GConfig CommLabel gstep t l t' Ht') | exact HR'].
    - destruct (g_install_gate_admits l E).
  Qed.

  Lemma iterated_premises_recover_step_backward : forall s t l t',
    Rgio s t -> gstep t l t' ->
    exists s', gstep s l s' /\ Rgio s' t'.
  Proof.
    intros s t l t' HR Hstep.
    destruct (family_of l) as [f | ] eqn:E.
    - assert (Hfam : family_labels f [l])
        by (constructor; [exact E | constructor]).
      destruct (drive_bwd_family f s t [l] t' Hfam HR
                  (steps_singleton_intro GConfig CommLabel gstep t l t' Hstep))
        as [s' [Hs' HR']].
      exists s'. split;
        [exact (steps_singleton_inv GConfig CommLabel gstep s l s' Hs') | exact HR'].
    - destruct (g_install_gate_admits l E).
  Qed.

  (* ── 5.1b  The finite-trace capstone from the UPGRADED premise set: same
     conclusion as §4.7, premised on bursts (via the recovered obligations fed to
     the landed lift). ── *)
  Theorem whole_gslt_in_rho_opcorrespondence_iterated : forall s t ls, Rgio s t ->
    (forall s', steps GConfig CommLabel gstep s ls s' ->
        exists t', steps GConfig CommLabel gstep t ls t' /\ gbarb s' = gbarb t') /\
    (forall t', steps GConfig CommLabel gstep t ls t' ->
        exists s', steps GConfig CommLabel gstep s ls s' /\ gbarb s' = gbarb t').
  Proof.
    exact (finite_trace_barb_equivalence GConfig CommLabel Barb gstep gbarb Rgio
             Rgio_barb
             iterated_premises_recover_step_forward
             iterated_premises_recover_step_backward).
  Qed.

  (* ── 5.2  ONE driver invocation corresponds: burst-level correspondence, both
     directions (at the FBinderBeta instantiation this is the labelled refinement
     of drive_weak_bisim's clauses). ── *)

  Theorem drive_burst_forward_correspondence : forall F s t ls s',
    Rgio s t -> drive_burst F s ls s' ->
    exists t', drive_burst F t ls t' /\ Rgio s' t' /\ gbarb s' = gbarb t'.
  Proof.
    intros F s t ls s' HR [Hfam Hs].
    destruct (drive_fwd_family F s t ls s' Hfam HR Hs) as [t' [Ht' HR']].
    exists t'. split; [split; [exact Hfam | exact Ht'] |].
    split; [exact HR' | apply Rgio_barb; exact HR'].
  Qed.

  Theorem drive_burst_backward_correspondence : forall F s t ls t',
    Rgio s t -> drive_burst F t ls t' ->
    exists s', drive_burst F s ls s' /\ Rgio s' t' /\ gbarb s' = gbarb t'.
  Proof.
    intros F s t ls t' HR [Hfam Ht].
    destruct (drive_bwd_family F s t ls t' Hfam HR Ht) as [s' [Hs' HR']].
    exists s'. split; [split; [exact Hfam | exact Hs'] |].
    split; [exact HR' | apply Rgio_barb; exact HR'].
  Qed.

  (* A DRIVE SCHEDULE: the whole execution as the flipped runtime performs it — a
     sequence of family-tagged bursts (each one driver-invocation segment). *)
  Inductive drive_schedule : GConfig -> list (Family * list CommLabel) -> GConfig -> Prop :=
    | dsched_nil : forall s, drive_schedule s [] s
    | dsched_cons : forall s F ls s' rest s'',
        drive_burst F s ls s' ->
        drive_schedule s' rest s'' ->
        drive_schedule s ((F, ls) :: rest) s''.

  Theorem drive_schedule_forward_correspondence : forall s t sched s',
    Rgio s t -> drive_schedule s sched s' ->
    exists t', drive_schedule t sched t' /\ Rgio s' t' /\ gbarb s' = gbarb t'.
  Proof.
    intros s t sched s' HR Hsched. revert t HR.
    induction Hsched as [s0 | s0 F ls s1 rest s2 Hburst Hsched IH]; intros t HR.
    - exists t. split; [constructor | split; [exact HR | apply Rgio_barb; exact HR]].
    - destruct Hburst as [Hfam Hs].
      destruct (drive_fwd_family F s0 t ls s1 Hfam HR Hs) as [t1 [Ht1 HR1]].
      destruct (IH t1 HR1) as [t' [Ht' [HR' Hb']]].
      exists t'. split.
      + econstructor; [split; [exact Hfam | exact Ht1] | exact Ht'].
      + split; [exact HR' | exact Hb'].
  Qed.

  Theorem drive_schedule_backward_correspondence : forall s t sched t',
    Rgio s t -> drive_schedule t sched t' ->
    exists s', drive_schedule s sched s' /\ Rgio s' t' /\ gbarb s' = gbarb t'.
  Proof.
    intros s t sched t' HR Hsched. revert s HR.
    induction Hsched as [t0 | t0 F ls t1 rest t2 Hburst Hsched IH]; intros s HR.
    - exists s. split; [constructor | split; [exact HR | apply Rgio_barb; exact HR]].
    - destruct Hburst as [Hfam Ht].
      destruct (drive_bwd_family F s t0 ls t1 Hfam HR Ht) as [s1 [Hs1 HR1]].
      destruct (IH s1 HR1) as [s' [Hs' [HR' Hb']]].
      exists s'. split.
      + econstructor; [split; [exact Hfam | exact Hs1] | exact Hs'].
      + split; [exact HR' | exact Hb'].
  Qed.

  (* THE ITERATED CAPSTONE over drive schedules — burst-for-burst, label-for-label,
     both directions, barb-equal at rest. *)
  Theorem whole_gslt_opcorr_over_drive_schedules : forall s t sched, Rgio s t ->
    (forall s', drive_schedule s sched s' ->
        exists t', drive_schedule t sched t' /\ gbarb s' = gbarb t') /\
    (forall t', drive_schedule t sched t' ->
        exists s', drive_schedule s sched s' /\ gbarb s' = gbarb t').
  Proof.
    intros s t sched HR. split.
    - intros s' Hs.
      destruct (drive_schedule_forward_correspondence s t sched s' HR Hs)
        as [t' [Ht' [_ Hb]]].
      exists t'. split; [exact Ht' | exact Hb].
    - intros t' Ht.
      destruct (drive_schedule_backward_correspondence s t sched t' HR Ht)
        as [s' [Hs' [_ Hb]]].
      exists s'. split; [exact Hs' | exact Hb].
  Qed.

  (* ── 5.3  PER-TRACE QUIESCENCE (user decision (3)). ── *)

  (* Harness-level quiescence: no visible COMM fires — the driver's REST condition
     (the OUT datum lands). Grounded model-side by InRhoQuiescenceDriver.
     quiescence_sound (Lambda: every DDone drive rests beta-NF) and
     bag_quiescence_sound (Ambient: every bag drive rests FLAT). *)
  Definition gquiescent (s : GConfig) : Prop := forall l s', ~ gstep s l s'.

  (* Related states are EQUI-QUIESCENT: the correspondence can neither invent nor
     lose a redex (from the recovered single-step obligations, both directions). *)
  Theorem related_states_equi_quiescent : forall s t,
    Rgio s t -> (gquiescent s <-> gquiescent t).
  Proof.
    intros s t HR. split.
    - intros Hq l t' Hstep.
      destruct (iterated_premises_recover_step_backward s t l t' HR Hstep)
        as [s' [Hs' _]].
      exact (Hq l s' Hs').
    - intros Hq l s' Hstep.
      destruct (iterated_premises_recover_step_forward s t l s' HR Hstep)
        as [t' [Ht' _]].
      exact (Hq l t' Ht').
  Qed.

  (* PER-TRACE quiescence, forward: if THIS schedule rests (its endpoint is
     quiescent), its mirrored schedule rests too, related and barb-equal. No claim
     relates DIFFERENT schedules' resting states — sound for the non-confluent
     families (decision (3): any-valid-reduction, membership-form). *)
  Theorem whole_gslt_per_trace_quiescence_forward : forall s t sched s',
    Rgio s t -> drive_schedule s sched s' -> gquiescent s' ->
    exists t', drive_schedule t sched t' /\ Rgio s' t'
               /\ gbarb s' = gbarb t' /\ gquiescent t'.
  Proof.
    intros s t sched s' HR Hsched Hq.
    destruct (drive_schedule_forward_correspondence s t sched s' HR Hsched)
      as [t' [Ht' [HR' Hb]]].
    exists t'. split; [exact Ht' | split; [exact HR' | split; [exact Hb |]]].
    exact (proj1 (related_states_equi_quiescent s' t' HR') Hq).
  Qed.

  (* PER-TRACE quiescence, backward: an in-Rho schedule that rests is mirrored by
     a source schedule that rests. *)
  Theorem whole_gslt_per_trace_quiescence_backward : forall s t sched t',
    Rgio s t -> drive_schedule t sched t' -> gquiescent t' ->
    exists s', drive_schedule s sched s' /\ Rgio s' t'
               /\ gbarb s' = gbarb t' /\ gquiescent s'.
  Proof.
    intros s t sched t' HR Hsched Hq.
    destruct (drive_schedule_backward_correspondence s t sched t' HR Hsched)
      as [s' [Hs' [HR' Hb]]].
    exists s'. split; [exact Hs' | split; [exact HR' | split; [exact Hb |]]].
    exact (proj2 (related_states_equi_quiescent s' t' HR') Hq).
  Qed.

End WholeGsltInRhoIteratedDriving.

(* ================================================================================
   5.4  SwapDemo RE-INSTANTIATED against the UPGRADED shapes (plan v2 §7.4): the
   base burst arms are discharged from the LANDED comm_step_complete/sound via the
   pointwise burst lift (§5.0); the other families' bursts are vacuous-or-empty
   under `nv_family` (a nonempty burst of any non-base family contradicts
   `nv_family ≡ Some FBase`; the empty burst is matched reflexively — the
   already-quiescent drive). The conclusion coincides with the landed
   `swapdemo_base_finite_trace_opcorr`; what is NEW is the premise route: every
   §5.1 burst premise is dischargeable, so the iterated harness context is
   inhabited (no vacuously-true iterated capstone).
   ================================================================================ *)

Lemma nv_fwd_base_burst : forall s t ls s',
  Forall (fun l => nv_family l = Some FBase) ls -> nv_R s t ->
  steps GC Fact nv_step s ls s' ->
  exists t', steps GC Fact nv_step t ls t' /\ nv_R s' t'.
Proof.
  exact (per_step_arm_lifts_to_burst_forward GC Fact nv_step nv_R
           (fun l => nv_family l = Some FBase) nv_fwd_base).
Qed.

Lemma nv_bwd_base_burst : forall s t ls t',
  Forall (fun l => nv_family l = Some FBase) ls -> nv_R s t ->
  steps GC Fact nv_step t ls t' ->
  exists s', steps GC Fact nv_step s ls s' /\ nv_R s' t'.
Proof.
  exact (per_step_arm_lifts_to_burst_backward GC Fact nv_step nv_R
           (fun l => nv_family l = Some FBase) nv_bwd_base).
Qed.

(* A nonempty family-homogeneous burst of any family other than FBase is
   uninhabited under nv_family; the empty burst is matched reflexively. *)
Lemma nv_vacuous_burst_fwd : forall F, F <> FBase -> forall s t ls s',
  Forall (fun l => nv_family l = Some F) ls -> nv_R s t ->
  steps GC Fact nv_step s ls s' ->
  exists t', steps GC Fact nv_step t ls t' /\ nv_R s' t'.
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

Lemma nv_vacuous_burst_bwd : forall F, F <> FBase -> forall s t ls t',
  Forall (fun l => nv_family l = Some F) ls -> nv_R s t ->
  steps GC Fact nv_step t ls t' ->
  exists s', steps GC Fact nv_step s ls s' /\ nv_R s' t'.
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

(* The SwapDemo base finite-trace opcorr THROUGH THE ITERATED HARNESS: every §5.1
   burst premise discharged (base via the pointwise lift of the landed theorems;
   the rest vacuous-or-empty), the gate holds, the initial Rgio is the lowering. *)
Theorem swapdemo_base_iterated_opcorr : forall (s : SourceState) ls,
  (forall a', steps GC Fact nv_step (GSrc s) ls a' ->
      exists b', steps GC Fact nv_step (GRho (lower_state s)) ls b' /\ nv_barb a' = nv_barb b') /\
  (forall b', steps GC Fact nv_step (GRho (lower_state s)) ls b' ->
      exists a', steps GC Fact nv_step (GSrc s) ls a' /\ nv_barb a' = nv_barb b').
Proof.
  intros s ls.
  apply (whole_gslt_in_rho_opcorrespondence_iterated GC Fact (list Fact)
           nv_step nv_barb nv_R nv_family).
  - exact nv_Rgio_barb.
  - exact nv_fwd_base_burst.
  - exact nv_bwd_base_burst.
  - apply nv_vacuous_burst_fwd; discriminate.
  - apply nv_vacuous_burst_bwd; discriminate.
  - apply nv_vacuous_burst_fwd; discriminate.
  - apply nv_vacuous_burst_bwd; discriminate.
  - apply nv_vacuous_burst_fwd; discriminate.
  - apply nv_vacuous_burst_bwd; discriminate.
  - apply nv_vacuous_burst_fwd; discriminate.
  - apply nv_vacuous_burst_bwd; discriminate.
  - apply nv_vacuous_burst_fwd; discriminate.
  - apply nv_vacuous_burst_bwd; discriminate.
  - apply nv_vacuous_burst_fwd; discriminate.
  - apply nv_vacuous_burst_bwd; discriminate.
  - intros l; cbn; discriminate.
  - cbn. reflexivity.
Qed.

(* The SwapDemo per-trace quiescence instance: a resting source drive schedule is
   mirrored by a resting in-Rho drive schedule (equal barbs, related endpoints). *)
Theorem swapdemo_base_per_trace_quiescence : forall (s : SourceState) sched s',
  drive_schedule GC Fact nv_step nv_family (GSrc s) sched s' ->
  gquiescent GC Fact nv_step s' ->
  exists t', drive_schedule GC Fact nv_step nv_family (GRho (lower_state s)) sched t'
             /\ nv_R s' t' /\ nv_barb s' = nv_barb t'
             /\ gquiescent GC Fact nv_step t'.
Proof.
  intros s sched s' Hsched Hq.
  refine (whole_gslt_per_trace_quiescence_forward GC Fact (list Fact)
            nv_step nv_barb nv_R nv_family
            nv_Rgio_barb
            nv_fwd_base_burst nv_bwd_base_burst
            _ _ _ _ _ _ _ _ _ _ _ _
            _
            (GSrc s) (GRho (lower_state s)) sched s'
            _ Hsched Hq).
  - apply nv_vacuous_burst_fwd; discriminate.
  - apply nv_vacuous_burst_bwd; discriminate.
  - apply nv_vacuous_burst_fwd; discriminate.
  - apply nv_vacuous_burst_bwd; discriminate.
  - apply nv_vacuous_burst_fwd; discriminate.
  - apply nv_vacuous_burst_bwd; discriminate.
  - apply nv_vacuous_burst_fwd; discriminate.
  - apply nv_vacuous_burst_bwd; discriminate.
  - apply nv_vacuous_burst_fwd; discriminate.
  - apply nv_vacuous_burst_bwd; discriminate.
  - apply nv_vacuous_burst_fwd; discriminate.
  - apply nv_vacuous_burst_bwd; discriminate.
  - intros l; cbn; discriminate.
  - cbn. reflexivity.
Qed.

(* Zero-admission confirmation (A-S5.7 iterated upgrade). *)
Print Assumptions steps_nil_inv.
Print Assumptions steps_singleton_inv.
Print Assumptions per_step_arm_lifts_to_burst_forward.
Print Assumptions per_step_arm_lifts_to_burst_backward.
Print Assumptions whole_gslt_in_rho_opcorrespondence_iterated.
Print Assumptions drive_burst_forward_correspondence.
Print Assumptions drive_burst_backward_correspondence.
Print Assumptions whole_gslt_opcorr_over_drive_schedules.
Print Assumptions related_states_equi_quiescent.
Print Assumptions whole_gslt_per_trace_quiescence_forward.
Print Assumptions whole_gslt_per_trace_quiescence_backward.
Print Assumptions swapdemo_base_iterated_opcorr.
Print Assumptions swapdemo_base_per_trace_quiescence.
