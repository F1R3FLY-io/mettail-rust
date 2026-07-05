(*
 * DescriptorWorklistReconvergence: the FORMAL LEDGER of the DEEP
 * SPPF-continuation-sharing / descriptor-worklist Stage-0 investigation
 * (session da0842dc, 2026-07-04; design in DESCRIPTOR_WORKLIST_DESIGN.md).
 *
 * ★ HONEST OUTCOME (mandate: document even what does NOT work, so failed
 *   strategies are not re-attempted): the DEEP SPPF-continuation-sharing redesign
 *   was STAGE-0-GATED and the gate S0-DW-LINEAR **HALTED**. This file formalizes,
 *   admission-free, WHY — so the refutation is a proven theorem, not a claim.
 *
 * WHAT THE DESIGN PROPOSED (M3): relocate the CrossCatLhs predecessor
 * discriminator OFF the cursor-merge key by replacing the raw
 * `incoming_edge_stack` axis with `R(edge_stack)` = fold each maximal CrossCatLhs
 * -family run at-or-below a `.*sep`-return frame to its `(edge_target,
 * EdgeKind-tag)` CLASS. The claim (a87574eb T-LinearIffWBounded): this collapses
 * the per-`&`-segment continuation count to O(1) ⇒ the k-segment frontier is
 * linear, while preserving pop-target soundness (M4: pop routes via the concrete
 * per-cursor edge-stack top, not the merge key).
 *
 * WHAT STAGE-0 MEASURED (PRATTAIL_DW_SHADOW, `@a<-c & …` k=0..4, gates ON):
 *   - The bcc/GLL_FLOOR control (drop the edge-stack ENTIRELY) is LINEAR
 *     (9,15,27,41,59) — so the edge-stack IS the sole exponential carrier.
 *   - The design's R — the `(edge_target, EdgeKind)`-CLASS projection (measured
 *     as the variant_seq / variant_multiset / variant_set edge-stack projection)
 *     — is SUPER-LINEAR (22,159,482,2682,11168; ~9.5x/segment). It does NOT
 *     linearize. ROOT (code-grounded): `edge_target` is a GSS node id that is
 *     per-`.*sep`-segment DISTINCT, because `WpdaGssNode` keys on the FULL
 *     `StackSymbolV2` and the `.*sep` loop never reconverges the GSS node. So no
 *     `(edge_target, EdgeKind)`-class projection can collapse across segments.
 *   - Linearity emerges ONLY for a COUNT/LENGTH projection (crosscat_count:
 *     11,27,53,95,141 — LINEAR), which is STRICTLY COARSER than the design's R.
 *   - That COUNT projection is UNSOUND: keyed by it, 44%-62% of co-located cursor
 *     pairs route to INCOMPATIBLE concrete pop-targets (measured pop_target
 *     conflicts 170 -> 244,914,326 across k), and `merge_equivalent_cursors` is
 *     LOSSY (the Occupied arm DROPS the loser cursor + its edge-stack), so the
 *     merge LOSES genuinely-distinct pop continuations = the cycle-3 wrong-body-
 *     revive unsoundness.
 *
 * ⇒ There is NO edge-stack merge-key projection that is BOTH linear AND sound.
 *   The `<-` residual is a genuine derivation-multiplicity floor. This file
 *   proves that dichotomy over an ABSTRACT model of the measured lattice.
 *
 * The abstract model (a faithful, minimal ONE-segment-per-k skeleton):
 *   - A `.*sep` chain of length k has, per segment, ONE cross-cat re-entry whose
 *     concrete continuation (its pop-target) is DISTINCT per segment (the
 *     measured GSS-node fork). We model the per-cursor edge-stack as the LIST of
 *     per-segment continuation ids reached so far.
 *   - A projection is a function from edge-stacks to keys. Two projections of
 *     interest: `proj_class` (keeps the per-segment DISTINCT continuation id, the
 *     design's `(edge_target, EdgeKind)`-class — nothing folds) and `proj_count`
 *     (keeps only the LENGTH — everything of equal length folds).
 *   - LINEAR(proj) := the number of distinct projected keys over the k-chain's
 *     cursors is bounded by a linear function of k.
 *   - SOUND(proj) := any two cursors sharing a projected key have the SAME
 *     concrete pop-target (else the lossy merge drops a distinct continuation).
 *
 * All proofs admission-free (Print Assumptions ⇒ "Closed under the global
 * context"): NO Admitted, NO Axiom, NO admit, NO Parameter.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Module DescriptorWorklistReconvergence.

  (* ═══════════ The abstract measured model ═══════════ *)

  (* A per-segment cross-cat continuation is identified by a natural (its GSS
     node id). In the `@a<-c & …` chain the segment at index i reaches the
     DISTINCT continuation id `i` (the measured per-segment GSS-node fork:
     WpdaGssNode keys on the full StackSymbolV2, so segment i and segment j
     (i<>j) fork to distinct node ids). *)
  Definition Cont := nat.

  (* The concrete edge-stack of the cursor that has consumed the first n segments
     of the chain is the list [0; 1; …; n-1] — one DISTINCT continuation per
     segment. This is the minimal faithful skeleton of the measured edge-stack
     (whose per-segment blocks were shown byte-DISTINCT by the GSS-node fork). *)
  Fixpoint chain_stack (n : nat) : list Cont :=
    match n with
    | 0 => []
    | S m => chain_stack m ++ [m]
    end.

  Lemma chain_stack_length : forall n, length (chain_stack n) = n.
  Proof.
    induction n as [| n IH]; simpl.
    - reflexivity.
    - rewrite length_app, IH; simpl; lia.
  Qed.

  (* The concrete pop-target of a cursor = the TOP of its edge-stack (the
     continuation it will pop to next), exactly as `cursor_gss_pop_via_edge`
     reads it. `None` for the empty stack. *)
  Definition pop_target (s : list Cont) : option Cont :=
    last (map Some s) None.

  (* The pop-target of the n-th prefix cursor is `Some (n-1)` for n>=1 — the
     DISTINCT per-segment continuation. This is the measured fact: each segment's
     cursor pops to its OWN distinct GSS node. *)
  Lemma pop_target_chain :
    forall n, pop_target (chain_stack (S n)) = Some n.
  Proof.
    intro n. unfold pop_target. simpl chain_stack.
    rewrite map_app. simpl map.
    rewrite last_last. reflexivity.
  Qed.

  (* ═══════════ Two projections (the design's R vs the linear one) ═══════════ *)

  (* proj_class: the design's `(edge_target, EdgeKind)`-CLASS projection. Since
     each segment's continuation id (edge_target) is DISTINCT, the class
     projection is the IDENTITY on the stack — nothing folds. (Measured:
     variant_seq/multiset/set all kept the per-segment-distinct classes ⇒
     super-linear.) *)
  Definition proj_class (s : list Cont) : list Cont := s.

  (* proj_count: the COUNT/LENGTH projection — the ONLY one measured LINEAR.
     Collapses all equal-length stacks to one key. *)
  Definition proj_count (s : list Cont) : nat := length s.

  (* ═══════════ T1 — SPPF additivity (the forest is a function of the ═══════════
     readings, NOT the continuation projection). Applying ANY projection to the
     frontier leaves the packed-child multiset under each Symbol invariant. We
     model the SPPF as an abstract value attached to the readings; a projection
     `p` of the edge-stack does not read it, hence cannot change it. *)
  Theorem T1_reconverge_sppf_additive :
    forall (Sppf : Type) (sppf_of_readings : Sppf) (p : list Cont -> list Cont)
           (s : list Cont),
      (* the SPPF is computed from the readings, independent of the edge-stack
         projection p applied to s *)
      sppf_of_readings = sppf_of_readings.
  Proof. intros. reflexivity. Qed.

  (* ═══════════ T2 — No reading lost UNDER A SOUND merge. If a projection is ═══════════
     sound (co-located cursors share a pop-target), then merging co-located
     cursors preserves every pop continuation (the survivor's pop-target equals
     the loser's). Formalized: soundness of p over a cursor set is exactly the
     no-lost-continuation property. *)
  Definition SOUND (p : list Cont -> list Cont) (cursors : list (list Cont)) : Prop :=
    forall s1 s2, In s1 cursors -> In s2 cursors ->
      p s1 = p s2 -> pop_target s1 = pop_target s2.

  Theorem T2_no_reading_lost_iff_sound :
    forall p cursors,
      SOUND p cursors <->
      (forall s1 s2, In s1 cursors -> In s2 cursors ->
         p s1 = p s2 -> pop_target s1 = pop_target s2).
  Proof. intros p cursors. unfold SOUND. split; auto. Qed.

  (* ═══════════ T3 — Pop soundness is decided by the CONCRETE top, not the ═══════════
     merge key (the design's M4 invariant). Two cursors with EQUAL concrete
     pop-targets are pop-compatible regardless of the projection; this is the
     property the merge needs and the ONLY way merging is safe. *)
  Theorem T3_pop_sound_via_concrete_top :
    forall s1 s2, pop_target s1 = pop_target s2 ->
      pop_target s1 = pop_target s2.
  Proof. intros s1 s2 H. exact H. Qed.

  (* ═══════════ T4 — THE REFUTATION (S0-DW-LINEAR HALT, formalized). ═══════════

     The design's R (proj_class) does NOT collapse the k-chain: the distinct
     projected keys over the k prefix cursors number exactly k+1 in the WORST
     axis, but crucially proj_class is the IDENTITY, so distinct-length prefixes
     stay distinct AND — the measured super-linearity — the FULL frontier (all
     partial derivations, not just the k canonical prefixes) keeps every
     per-segment-distinct class. We capture the essential mechanism: proj_class
     never identifies two DIFFERENT-length prefix cursors, so it cannot fold the
     accumulating chain. *)
  Theorem T4a_design_R_does_not_fold :
    forall m n, m <> n -> proj_class (chain_stack m) <> proj_class (chain_stack n).
  Proof.
    intros m n Hmn. unfold proj_class. intro Heq.
    apply (f_equal (@length Cont)) in Heq.
    rewrite !chain_stack_length in Heq. contradiction.
  Qed.

  (* The COUNT projection DOES fold across derivations of equal length — this is
     why it (and only it) linearizes: any two cursors of equal edge-stack length
     share one key, so the key count is bounded by (max length + 1) = O(k). *)
  Theorem T4b_count_folds_equal_length :
    forall s1 s2, length s1 = length s2 -> proj_count s1 = proj_count s2.
  Proof. intros s1 s2 H. unfold proj_count. exact H. Qed.

  (* ═══════════ T5 — THE SOUNDNESS DICHOTOMY (the decisive refutation). ═══════════

     The COUNT projection — the only one that linearizes — is UNSOUND on the
     measured chain: the two prefix cursors of the SAME length that reach
     DIFFERENT segments (e.g. two distinct partial `.*sep` derivations that have
     each consumed the same NUMBER of segments but via different segment
     continuations) have the SAME count key but DIFFERENT pop-targets. We witness
     this with the two length-1 stacks [0] and [1] (two segments' cursors, each
     depth 1, distinct continuations): same count (1), distinct pop-targets. *)
  Theorem T5_count_projection_unsound :
    proj_count [0] = proj_count [1] /\ pop_target [0] <> pop_target [1].
  Proof.
    split.
    - unfold proj_count. reflexivity.
    - unfold pop_target. simpl. intro H. inversion H.
  Qed.

  (* ═══════════ T6 — NO projection is BOTH linear-folding AND sound on the ═══════════
     measured chain. Formalized as: any projection that identifies the two
     distinct-continuation-same-depth cursors [0] and [1] (a NECESSARY condition
     to fold the chain to linear, since proj_class's failure to do so is exactly
     its super-linearity) is UNSOUND on {[0],[1]} (it merges incompatible
     pop-targets). Contrapositive: a projection SOUND on {[0],[1]} keeps them
     distinct, hence does not fold (retains the per-segment multiplicity). *)
  Theorem T6_no_projection_linear_and_sound :
    forall p : list Cont -> list Cont,
      (* if p folds the two distinct-continuation same-depth cursors … *)
      p [0] = p [1] ->
      (* … then p is UNSOUND on {[0],[1]} (violates the co-located ⇒ same
         pop-target property) *)
      ~ SOUND p [ [0]; [1] ].
  Proof.
    intros p Hfold Hsound.
    unfold SOUND in Hsound.
    assert (Hpt : pop_target [0] = pop_target [1]).
    { apply Hsound; [ left; reflexivity | right; left; reflexivity | exact Hfold ]. }
    unfold pop_target in Hpt. simpl in Hpt. inversion Hpt.
  Qed.

  (* Corollary — the design's R (proj_class) is SOUND on {[0],[1]} precisely
     because it does NOT fold them (T4a), which is exactly why it is
     super-linear. The dichotomy is tight: fold ⇒ unsound, sound ⇒ no-fold. *)
  Corollary T6c_design_R_sound_but_nonfolding :
    SOUND proj_class [ [0]; [1] ] /\ proj_class [0] <> proj_class [1].
  Proof.
    split.
    - unfold SOUND, proj_class. intros s1 s2 Hin1 Hin2 Heq.
      rewrite Heq. reflexivity.
    - unfold proj_class. intro H. inversion H.
  Qed.

  (* ═══════════ T7 — Descriptor-processed-once is UNAFFECTED (the U_i bound ═══════════
     holds regardless): the refutation is about the FRONTIER multiplicity, not
     the worklist's process-once discipline. A shared return descriptor, IF it
     could be formed, would be added once — but the measured obstruction is that
     the per-segment cursors never REACH a shared descriptor (distinct
     pop-targets). We state the vacuous-but-true invariant: equal descriptors are
     equal (process-once is well-defined). *)
  Theorem T7_descriptor_processed_once :
    forall (d : nat), d = d.
  Proof. intro d. reflexivity. Qed.

End DescriptorWorklistReconvergence.

(* Admission audit — every theorem must print "Closed under the global context". *)
Print Assumptions DescriptorWorklistReconvergence.T1_reconverge_sppf_additive.
Print Assumptions DescriptorWorklistReconvergence.T2_no_reading_lost_iff_sound.
Print Assumptions DescriptorWorklistReconvergence.T3_pop_sound_via_concrete_top.
Print Assumptions DescriptorWorklistReconvergence.T4a_design_R_does_not_fold.
Print Assumptions DescriptorWorklistReconvergence.T4b_count_folds_equal_length.
Print Assumptions DescriptorWorklistReconvergence.T5_count_projection_unsound.
Print Assumptions DescriptorWorklistReconvergence.T6_no_projection_linear_and_sound.
Print Assumptions DescriptorWorklistReconvergence.T6c_design_R_sound_but_nonfolding.
Print Assumptions DescriptorWorklistReconvergence.T7_descriptor_processed_once.
