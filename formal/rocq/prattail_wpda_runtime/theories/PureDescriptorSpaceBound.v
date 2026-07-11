(*
 * PureDescriptorSpaceBound: Theorem A of the S2 descriptor-pure canonical-GLL
 * campaign — the DESCRIPTOR-SPACE BOUND: for a fixed grammar the pure
 * descriptor space (L, u, i, w) is polynomial in the token count n (explicit
 * degree FIVE, factored form below), and the worklist is a set-monotone
 * add-once discipline processing each descriptor at most once. Together these
 * bound the number of descriptor processings — the |U| depth-uniformity the
 * Stage-D gate measured (ladder plateau 260/290/291/291/291 at d1..d5,
 * ledger §D.4/§D.5).
 *
 * IMPLEMENTATION ANCHORS (prattail/src at the P5 tree state):
 *   - `CgllPureDescriptor` (wpda_walker.rs @4403): the seven concrete fields
 *     {state, cur_sym, frame_class, ret_slot, u, pos, w} — nothing else may
 *     influence stepping (the C7 purity fence).
 *   - The model's L = (state, cur_sym, frame_class, ret_slot), a FINITE set
 *     for a fixed grammar:
 *       · `cgll_pure_state_slot_ident` (wpda_walker.rs @23859) is the
 *         position-free state identity; the ONLY position-carrying state
 *         field, `PrefixDispatch.pos`, is pinned ≡ i BY CONSTRUCTION at
 *         dequeue (the desync patch @25853-25866, applied BEFORE the dedup
 *         key), and `Error{..}`/`AmbiguityFanout` never enqueue;
 *       · `StackSymbolV2` payloads are grammar-bounded (wpda_runtime.rs:256);
 *       · `CgllFrameClass` is one bit (@4327);
 *       · `CgllRetSlot` (@4344-4368) folds ONLY descent-local grammar data
 *         (caller-symbol hash, pushed cat/rule, kind class, outer_bp, xcat) —
 *         no positions, no chains (amendment 1 / AV2).
 *   - The model's u = GSS node identity (pos, label): `get_or_create_node`
 *     keys nodes on exactly (pos, symbol) (gss.rs, used by `gll_create`
 *     @1435-1446); pure-arm labels are `cgll_pure_v_label` images of ret
 *     slots (@24015) plus the seed labels — a grammar-bounded label space —
 *     so the node space is (label-space × positions): node-bound(n).
 *   - The model's i = the input position, <= n+1 (logical EOI).
 *   - The model's w = ONE hash-consed forest identity (or NONE):
 *       · Symbol       (tag, lo, hi)        — sppf.rs `intern_symbol` @589,
 *         dedup key @590; tags = category tags | CGLL_BIN_TAG;
 *       · Intermediate (base-slot, salt, lo, hi) — sppf.rs
 *         `intern_intermediate` @623 on (slot_id, lo, hi), where the pure
 *         arm's slot_id space factors as grammar-finite base hashes
 *         (`cgll_pure_slot_hash` @23965: position-free state ident × cur_sym,
 *         bits 30/31 reserved) × a position salt (`^ (pos << 1)`, the
 *         annotation-fold salts @24148/@24220);
 *       · leaves       (class, pos)         — Terminal/TriggerTerminal/
 *         Epsilon/OptAbsent/BinderScope interners (sppf.rs dedup maps
 *         @452-486), each keyed by a grammar-finite class × a position.
 *   - Add-once: `step_canonical_pure`'s dequeue loop (wpda_walker.rs
 *     @25800-25872): `seen.insert(cgll_pure_key(&d))` — a descriptor whose
 *     key is already present is SKIPPED (`continue`), i.e. dedup applies at
 *     DEQUEUE over the entire dequeue stream, exactly the `drain` model
 *     below; `cgll_pure_key` (@23841) hashes ALL seven fields.
 *
 * MODEL CORRESPONDENCE (scope statements — what is and is NOT claimed):
 *   1. The model dedups on descriptor VALUES; the implementation dedups on a
 *      64-bit FxHash of the value. A hash collision can only MERGE MORE
 *      (skip a descriptor the model would process), so the upper bound
 *      direction proven here is preserved verbatim under hashing;
 *      completeness under collisions is a separate concern carried by the
 *      gate counters (`slot_collisions = 0` across the battery) and the
 *      pre-flip escalation note (structured ids before flip).
 *   2. The modeled w-space is the position-pair-bounded identity classes
 *      (Symbol / Intermediate / leaf) + NONE — the mandate's "(slot × pos ×
 *      pos)-bounded plus leaf spaces". `CollectionId` identities (keyed
 *      (slot, item-VECTOR), sppf.rs @697) and Packing-leaf identities are
 *      NOT position-pair bounded: descriptors carrying them (marker-close
 *      resumes, P3.a/P3.c) are bounded by the collection-flat multiplicity —
 *      an output-sized quantity (Θ(collection readings), the documented
 *      flatten-at-close regime), not by n alone. The polynomial bound is
 *      therefore claimed for the descriptor population over the modeled
 *      w-classes; this is a scope statement, not a hidden assumption.
 *   3. In-rangeness of every enqueued descriptor (positions <= n+1, grammar
 *      components within their finite spaces) is a hypothesis of the
 *      counting theorems; it corresponds to the constructors above only
 *      producing table symbols/interned identities and `pos <= EOI`.
 *
 * THEOREMS (all admission-free; audited by `Print Assumptions`):
 *   T1 pure_descriptor_space_poly_bound — a duplicate-free, in-range
 *      descriptor set has at most
 *        |L| · (|labels|·(n+2)) · (n+2) · (1 + |tags|·(n+2)² +
 *        |base-slots|·(n+2)³ + |leaf-classes|·(n+2))
 *      elements (exact factored form).
 *   T2 pure_descriptor_space_degree_five — the explicit-degree corollary:
 *      |U| <= (|L|·|labels|·(1+|tags|+|base-slots|+|leaf-classes|)) · (n+2)^5.
 *      The degree-5 term is dominated by the position-salted Intermediate
 *      axis ((n+2)³) times node position × input position ((n+2)²); the
 *      Scott-Johnstone O(n³) classic bound is the special case where w and
 *      the GSS label are functionally determined by (L, lo, i) — a
 *      determination the pure protocol deliberately does NOT assume (w is a
 *      genuine key axis; that is the pack-at-advance design).
 *   T3 drain_seen_monotone        — the worklist's seen set only grows.
 *   T4 drain_never_reprocesses    — a descriptor already seen is never
 *      processed again (processed-at-most-once, half 1).
 *   T5 drain_processed_nodup     — the processed stream is duplicate-free
 *      (processed-at-most-once, half 2).
 *   T6 pure_worklist_processed_bound — composition: on any in-range dequeue
 *      stream the add-once loop performs at most descriptor_space_bound
 *      processings (the |U| polynomial bound as the loop enforces it).
 *
 * FAILED STRATEGIES (documented so they are not re-attempted):
 *   - A direct mixed-radix nat ENCODING of descriptors (enc(d) < K, prove
 *     injectivity arithmetically, then pigeonhole over seq 0 K) drowns in
 *     nonlinear div/mod side conditions. The ENUMERATION route (build the
 *     finite space as map-over-list_prod, prove completeness by `in_prod` +
 *     `in_seq`, count by `length_prod`) is entirely mechanical and is what
 *     is used here; `NoDup_incl_length` supplies the pigeonhole.
 *   - Letting `nia` close the degree-5 corollary in one shot (six symbolic
 *     factors) stalls; splitting into ONE cubic `nia` lemma
 *     (`forest_count_le`) plus `Nat.mul_le_mono_l` and a `ring` reassociation
 *     is robust.
 *
 * Rocq 9.1 compatible. No Admitted, no Axiom, no Parameter (section
 * variables become explicit premises of the closed theorems).
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.

Section PureDescriptorSpaceBound.

  (* ── Grammar constants (fixed-grammar cardinalities) and the input size. ──
     grammar_slots           = |L| — (position-free state ident × cur_sym ×
                               frame_class × ret_slot) combinations.
     gss_label_slots         = the GSS label space — `cgll_pure_v_label`
                               images of ret slots + seed labels.
     symbol_tags             = Symbol identity tags (category | CGLL_BIN_TAG).
     intermediate_base_slots = position-free fold-slot hashes
                               (`cgll_pure_slot_hash` base values incl. the
                               WRAP namespace bit and the D2 rule-id slots).
     leaf_classes            = leaf identity classes (Terminal kinds ×
                               text-handle classes, TriggerTerminal owners,
                               Epsilon, OptAbsent, BinderScope shapes …) —
                               grammar+lexicon-finite.
     n                       = token count; positions range over 0..n+1
                               (logical EOI), i.e. `position_count` values. ── *)
  Variable grammar_slots           : nat.
  Variable gss_label_slots         : nat.
  Variable symbol_tags             : nat.
  Variable intermediate_base_slots : nat.
  Variable leaf_classes            : nat.
  Variable n                       : nat.

  Definition position_count : nat := S (S n).

  (* ── The modeled identities. ── *)

  (* GSS node identity (pos, symbol) — gss.rs `get_or_create_node` key. *)
  Record GssNodeIdent : Type := mkGssNode {
    gss_label : nat;   (* v-label / seed label, < gss_label_slots *)
    gss_pos   : nat    (* creation position, < position_count *)
  }.

  (* Hash-consed forest identity — the sppf.rs dedup keys. *)
  Inductive ForestIdent : Type :=
    | SymbolIdent       : nat -> nat -> nat -> ForestIdent
      (* tag, lo, hi — sppf.rs intern_symbol @589 *)
    | IntermediateIdent : nat -> nat -> nat -> nat -> ForestIdent
      (* base-slot, position-salt, lo, hi — intern_intermediate @623 with the
         pure arm's salted slot factored as (base, salt) *)
    | LeafIdent         : nat -> nat -> ForestIdent.
      (* leaf class, position — the leaf interners' dedup keys *)

  (* One pure descriptor (L, u, i, w) — CgllPureDescriptor @4403 with the
     three L components collapsed into one finite index. *)
  Record PureDescriptor : Type := mkDescriptor {
    descriptor_slot   : nat;                (* L,  < grammar_slots *)
    descriptor_node   : GssNodeIdent;       (* u *)
    descriptor_pos    : nat;                (* i,  < position_count *)
    descriptor_forest : option ForestIdent  (* w;  None = SPPF_ID_NONE *)
  }.

  (* ── Range predicates. ── *)

  Definition gss_in_range (u : GssNodeIdent) : Prop :=
    gss_label u < gss_label_slots /\ gss_pos u < position_count.

  Definition forest_in_range (w : ForestIdent) : Prop :=
    match w with
    | SymbolIdent tag lo hi =>
        tag < symbol_tags /\ lo < position_count /\ hi < position_count
    | IntermediateIdent base salt lo hi =>
        base < intermediate_base_slots /\ salt < position_count
        /\ lo < position_count /\ hi < position_count
    | LeafIdent cls pos =>
        cls < leaf_classes /\ pos < position_count
    end.

  Definition descriptor_in_range (d : PureDescriptor) : Prop :=
    descriptor_slot d < grammar_slots
    /\ gss_in_range (descriptor_node d)
    /\ descriptor_pos d < position_count
    /\ match descriptor_forest d with
       | None => True
       | Some w => forest_in_range w
       end.

  (* ── Enumerations of the finite spaces. ── *)

  Definition positions : list nat := seq 0 position_count.

  Definition gss_enum : list GssNodeIdent :=
    map (fun p => mkGssNode (fst p) (snd p))
        (list_prod (seq 0 gss_label_slots) positions).

  Definition symbol_enum : list ForestIdent :=
    map (fun t => SymbolIdent (fst (fst t)) (snd (fst t)) (snd t))
        (list_prod (list_prod (seq 0 symbol_tags) positions) positions).

  Definition intermediate_enum : list ForestIdent :=
    map (fun t => IntermediateIdent (fst (fst (fst t))) (snd (fst (fst t)))
                                    (snd (fst t)) (snd t))
        (list_prod
           (list_prod (list_prod (seq 0 intermediate_base_slots) positions)
                      positions)
           positions).

  Definition leaf_enum : list ForestIdent :=
    map (fun p => LeafIdent (fst p) (snd p))
        (list_prod (seq 0 leaf_classes) positions).

  Definition forest_enum : list ForestIdent :=
    symbol_enum ++ intermediate_enum ++ leaf_enum.

  Definition w_enum : list (option ForestIdent) :=
    None :: map Some forest_enum.

  Definition descriptor_enum : list PureDescriptor :=
    map (fun t => mkDescriptor (fst (fst (fst t))) (snd (fst (fst t)))
                               (snd (fst t)) (snd t))
        (list_prod
           (list_prod (list_prod (seq 0 grammar_slots) gss_enum) positions)
           w_enum).

  (* ── Enumeration completeness: every in-range value is enumerated. ── *)

  Lemma in_positions : forall p, p < position_count -> In p positions.
  Proof.
    intros p Hp. unfold positions. apply in_seq. lia.
  Qed.

  Lemma gss_enum_complete :
    forall u, gss_in_range u -> In u gss_enum.
  Proof.
    intros [lab pos] [H1 H2]. unfold gss_enum.
    apply in_map_iff. exists (lab, pos). split; [reflexivity |].
    apply in_prod; [apply in_seq; cbn in *; lia | apply in_positions; exact H2].
  Qed.

  Lemma forest_enum_complete :
    forall w, forest_in_range w -> In w forest_enum.
  Proof.
    intros w Hw. unfold forest_enum.
    destruct w as [tag lo hi | base salt lo hi | cls pos];
      cbn in Hw.
    - (* Symbol *)
      apply in_or_app. left.
      apply in_map_iff. exists ((tag, lo), hi). split; [reflexivity |].
      destruct Hw as [H1 [H2 H3]].
      apply in_prod; [apply in_prod |].
      + apply in_seq. lia.
      + apply in_positions. exact H2.
      + apply in_positions. exact H3.
    - (* Intermediate *)
      apply in_or_app. right. apply in_or_app. left.
      apply in_map_iff. exists (((base, salt), lo), hi). split; [reflexivity |].
      destruct Hw as [H1 [H2 [H3 H4]]].
      apply in_prod; [apply in_prod; [apply in_prod |] |].
      + apply in_seq. lia.
      + apply in_positions. exact H2.
      + apply in_positions. exact H3.
      + apply in_positions. exact H4.
    - (* Leaf *)
      apply in_or_app. right. apply in_or_app. right.
      apply in_map_iff. exists (cls, pos). split; [reflexivity |].
      destruct Hw as [H1 H2].
      apply in_prod; [apply in_seq; lia | apply in_positions; exact H2].
  Qed.

  Lemma w_enum_complete :
    forall w, match w with None => True | Some f => forest_in_range f end ->
      In w w_enum.
  Proof.
    intros [f |] Hf; unfold w_enum.
    - right. apply in_map. apply forest_enum_complete. exact Hf.
    - left. reflexivity.
  Qed.

  Lemma descriptor_enum_complete :
    forall d, descriptor_in_range d -> In d descriptor_enum.
  Proof.
    intros [slot node pos w] [H1 [H2 [H3 H4]]].
    unfold descriptor_enum.
    apply in_map_iff. exists (((slot, node), pos), w). split; [reflexivity |].
    apply in_prod; [apply in_prod; [apply in_prod |] |].
    - apply in_seq. cbn in *. lia.
    - apply gss_enum_complete. exact H2.
    - apply in_positions. exact H3.
    - apply w_enum_complete. exact H4.
  Qed.

  (* ── Space cardinalities. ── *)

  Definition forest_ident_count : nat :=
    symbol_tags * position_count * position_count
    + intermediate_base_slots * position_count * position_count * position_count
    + leaf_classes * position_count.

  Definition descriptor_space_bound : nat :=
    grammar_slots * (gss_label_slots * position_count) * position_count
    * S forest_ident_count.

  Lemma forest_enum_length : length forest_enum = forest_ident_count.
  Proof.
    unfold forest_enum, symbol_enum, intermediate_enum, leaf_enum,
           forest_ident_count, positions.
    rewrite !length_app, !length_map, !length_prod, !length_seq.
    (* `length_app` associates the sum to the right; the definition is
       left-associated — `lia` bridges the reassociation. *)
    lia.
  Qed.

  Lemma gss_enum_length :
    length gss_enum = gss_label_slots * position_count.
  Proof.
    unfold gss_enum, positions.
    rewrite length_map, length_prod, !length_seq. reflexivity.
  Qed.

  Lemma w_enum_length : length w_enum = S forest_ident_count.
  Proof.
    unfold w_enum. cbn [length].
    rewrite length_map, forest_enum_length. reflexivity.
  Qed.

  Lemma descriptor_enum_length :
    length descriptor_enum = descriptor_space_bound.
  Proof.
    unfold descriptor_enum, descriptor_space_bound, positions.
    rewrite length_map, !length_prod, gss_enum_length, w_enum_length,
            !length_seq.
    reflexivity.
  Qed.

  (* ═══════════════════════════════════════════════════════════════════════════
     T1 — THE POLYNOMIAL DESCRIPTOR-SPACE BOUND (exact factored form).
     MODEL CORRESPONDENCE: |U| as counted by `step_canonical_pure`'s
     `u_count`/`u_by_pos` (@25872-25873) — the set of DISTINCT descriptor
     values processed — is a NoDup in-range set, so this bound applies to it.
     ═══════════════════════════════════════════════════════════════════════════ *)

  Theorem pure_descriptor_space_poly_bound :
    forall U : list PureDescriptor,
      NoDup U ->
      (forall d, In d U -> descriptor_in_range d) ->
      length U <= descriptor_space_bound.
  Proof.
    intros U Hnd Hrange.
    rewrite <- descriptor_enum_length.
    apply NoDup_incl_length; [exact Hnd |].
    intros d Hd. apply descriptor_enum_complete. apply Hrange. exact Hd.
  Qed.

  (* ═══════════════════════════════════════════════════════════════════════════
     T2 — the EXPLICIT-DEGREE corollary: degree 5 in (n+2).
     ═══════════════════════════════════════════════════════════════════════════ *)

  Lemma forest_count_le :
    S forest_ident_count
    <= S (symbol_tags + intermediate_base_slots + leaf_classes)
       * (position_count * position_count * position_count).
  Proof.
    (* FAILED STRATEGIES: (i) a single `nia` on the whole inequality finds no
       witness (degree 3, four symbolic factors); (ii) even the per-summand
       `nia` goals like `c*P <= c*(P*P*P)` fail. Robust route: one generic
       padding step `x <= x*P` (from 1 <= P via `Nat.mul_le_mono_l`), chained
       instances, and a `ring` redistribution — `lia` then closes over the
       product atoms linearly. *)
    unfold forest_ident_count.
    set (P := position_count).
    assert (HP : 1 <= P) by (unfold P, position_count; lia).
    assert (Hstep : forall x, x <= x * P).
    { intro x. rewrite <- (Nat.mul_1_r x) at 1.
      apply Nat.mul_le_mono_l. exact HP. }
    pose proof (Hstep P) as HP2.                              (* P <= P*P *)
    pose proof (Hstep (P * P)) as HP3.                        (* P*P <= P*P*P *)
    pose proof (Hstep (symbol_tags * P * P)) as HS.           (* tS*P*P <= tS*P*P*P *)
    pose proof (Hstep (leaf_classes * P)) as HL2.             (* tL*P <= tL*P*P *)
    pose proof (Hstep (leaf_classes * P * P)) as HL3.         (* tL*P*P <= tL*P*P*P *)
    replace (S (symbol_tags + intermediate_base_slots + leaf_classes)
             * (P * P * P))
      with (P * P * P
            + symbol_tags * P * P * P
            + intermediate_base_slots * P * P * P
            + leaf_classes * P * P * P)
      by ring.
    lia.
  Qed.

  Theorem pure_descriptor_space_degree_five :
    forall U : list PureDescriptor,
      NoDup U ->
      (forall d, In d U -> descriptor_in_range d) ->
      length U
      <= grammar_slots * gss_label_slots
         * S (symbol_tags + intermediate_base_slots + leaf_classes)
         * (position_count * position_count * position_count
            * position_count * position_count).
  Proof.
    intros U Hnd Hrange.
    eapply Nat.le_trans;
      [apply pure_descriptor_space_poly_bound; assumption |].
    unfold descriptor_space_bound.
    eapply Nat.le_trans.
    - apply Nat.mul_le_mono_l. apply forest_count_le.
    - apply Nat.eq_le_incl. ring.
  Qed.

  (* Power-notation restatement of the same degree-5 bound. *)
  Corollary pure_descriptor_space_degree_five_pow :
    forall U : list PureDescriptor,
      NoDup U ->
      (forall d, In d U -> descriptor_in_range d) ->
      length U
      <= grammar_slots * gss_label_slots
         * S (symbol_tags + intermediate_base_slots + leaf_classes)
         * position_count ^ 5.
  Proof.
    intros U Hnd Hrange.
    replace (position_count ^ 5)
      with (position_count * position_count * position_count
            * position_count * position_count)
      by (cbn [Nat.pow]; ring).
    apply pure_descriptor_space_degree_five; assumption.
  Qed.

  (* ═══════════════════════════════════════════════════════════════════════════
     T3/T4/T5/T6 — THE ADD-ONCE WORKLIST DISCIPLINE.
     MODEL CORRESPONDENCE: `drain seen pending` is the dequeue loop of
     `step_canonical_pure` (@25800-25872) abstracted over its dequeue stream:
     `pending` is the (arbitrary, dynamically produced) sequence of dequeued
     descriptors; per dequeue the loop consults `seen` and either SKIPS
     (`continue` on `!seen.insert(..)`) or PROCESSES (counts `u_count`,
     steps the engine, enqueues successors). The successor dynamics do not
     matter for these theorems — whatever the enqueue side does, the dequeue
     stream is SOME finite list and the skip/process decision is exactly this
     fold. (Closure/completeness of the dynamic loop is Theorem C's file.)
     ═══════════════════════════════════════════════════════════════════════════ *)

  Definition descriptor_eq_dec :
    forall x y : PureDescriptor, {x = y} + {x <> y}.
  Proof. repeat decide equality. Defined.

  (* One drain of a dequeue stream: returns (final seen set, processed
     subsequence in processing order). *)
  Fixpoint drain (seen pending : list PureDescriptor)
    : list PureDescriptor * list PureDescriptor :=
    match pending with
    | [] => (seen, [])
    | d :: rest =>
        if in_dec descriptor_eq_dec d seen
        then drain seen rest
        else let '(fin, proc) := drain (d :: seen) rest in (fin, d :: proc)
    end.

  (* T3 — set-monotonicity: the seen set only grows. *)
  Theorem drain_seen_monotone :
    forall pending seen, incl seen (fst (drain seen pending)).
  Proof.
    induction pending as [|d rest IH]; intro seen; cbn [drain].
    - apply incl_refl.
    - destruct (in_dec descriptor_eq_dec d seen) as [Hin | Hnin].
      + apply IH.
      + destruct (drain (d :: seen) rest) as [fin proc] eqn:E.
        cbn [fst].
        intros x Hx.
        pose proof (IH (d :: seen)) as Hmono. rewrite E in Hmono.
        apply Hmono. right. exact Hx.
  Qed.

  (* T4 — a descriptor already seen is never processed again. *)
  Theorem drain_never_reprocesses :
    forall pending seen d,
      In d seen -> ~ In d (snd (drain seen pending)).
  Proof.
    induction pending as [|e rest IH]; intros seen d Hd; cbn [drain].
    - intro H. exact H.
    - destruct (in_dec descriptor_eq_dec e seen) as [Hin | Hnin].
      + apply IH. exact Hd.
      + destruct (drain (e :: seen) rest) as [fin proc] eqn:E.
        cbn [snd]. intros [Heq | Hproc].
        * subst e. exact (Hnin Hd).
        * pose proof (IH (e :: seen) d (or_intror Hd)) as Hno.
          rewrite E in Hno. exact (Hno Hproc).
  Qed.

  (* T5 — the processed stream is duplicate-free: each descriptor is
     processed AT MOST ONCE (the GLL add-once property). *)
  Theorem drain_processed_nodup :
    forall pending seen, NoDup (snd (drain seen pending)).
  Proof.
    induction pending as [|d rest IH]; intro seen; cbn [drain].
    - constructor.
    - destruct (in_dec descriptor_eq_dec d seen) as [Hin | Hnin].
      + apply IH.
      + destruct (drain (d :: seen) rest) as [fin proc] eqn:E.
        cbn [snd]. constructor.
        * (* d enters seen before the recursive drain: T4 forbids re-processing *)
          pose proof (drain_never_reprocesses rest (d :: seen) d
                        (or_introl eq_refl)) as Hno.
          rewrite E in Hno. exact Hno.
        * pose proof (IH (d :: seen)) as Hnd. rewrite E in Hnd. exact Hnd.
  Qed.

  (* Processed descriptors come from the dequeue stream (for range transfer). *)
  Lemma drain_processed_from_pending :
    forall pending seen d,
      In d (snd (drain seen pending)) -> In d pending.
  Proof.
    induction pending as [|e rest IH]; intros seen d; cbn [drain].
    - intro H. exact H.
    - destruct (in_dec descriptor_eq_dec e seen) as [Hin | Hnin].
      + intro H. right. eapply IH. exact H.
      + destruct (drain (e :: seen) rest) as [fin proc] eqn:E.
        cbn [snd]. intros [Heq | Hproc].
        * left. exact Heq.
        * right. eapply IH. rewrite E. exact Hproc.
  Qed.

  (* T6 — COMPOSITION: on any in-range dequeue stream the add-once loop
     performs at most `descriptor_space_bound` processings. This is the |U|
     bound exactly as the runtime enforces it (u_count = length of the
     processed stream; the 20M budget @25754 is a backstop, not the bound). *)
  Theorem pure_worklist_processed_bound :
    forall pending : list PureDescriptor,
      (forall d, In d pending -> descriptor_in_range d) ->
      length (snd (drain [] pending)) <= descriptor_space_bound.
  Proof.
    intros pending Hrange.
    apply pure_descriptor_space_poly_bound.
    - apply drain_processed_nodup.
    - intros d Hd. apply Hrange.
      eapply drain_processed_from_pending. exact Hd.
  Qed.

End PureDescriptorSpaceBound.

(* ── ADMISSION AUDIT — every theorem must print "Closed under the global context". *)
Print Assumptions pure_descriptor_space_poly_bound.
Print Assumptions pure_descriptor_space_degree_five.
Print Assumptions pure_descriptor_space_degree_five_pow.
Print Assumptions drain_seen_monotone.
Print Assumptions drain_never_reprocesses.
Print Assumptions drain_processed_nodup.
Print Assumptions pure_worklist_processed_bound.
