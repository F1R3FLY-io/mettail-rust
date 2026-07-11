(*
 * PurePackingPreservation: Theorem C of the S2 descriptor-pure canonical-GLL
 * campaign — PACKING PRESERVATION (the L_PACK/L_SHAPE successors): merging
 * descriptors with equal (L, u, i, w) loses no derivation. The realized
 * reading multiset of the forest is INVARIANT under add-once dedup of equal
 * descriptors, because the protocol packs AT ADVANCE: a descriptor's
 * derivation content is inside its `w` (and already interned in the forest)
 * BEFORE any merge can occur, and its stepping is a function of the
 * descriptor VALUE — so the merged twin could only have re-emitted the same
 * facts and re-enqueued the same successors.
 *
 * IMPLEMENTATION ANCHORS (prattail/src at the P5 tree state):
 *   - THE PURITY FENCE: `CgllPureDescriptor` (wpda_walker.rs @4403) — "Dedup
 *     key = FxHash of ALL SEVEN fields (nothing else may influence
 *     stepping)". Stepping consumes exactly the descriptor value: the engine
 *     step reads (state, synthesized frontier symbol = cur_sym, pos, tokens,
 *     frame_ctx) (@25896-25912) where `frame_ctx` is derived from `u`'s
 *     ancestry chain (`cgll_pure_frame_ctx` over `v_parent`, recorded once at
 *     descent and never mutated — a function of `u`); dispatch/descend/
 *     reduce/resume read only descriptor fields + the global tables + the
 *     two GSS/SPPF interning layers.
 *   - PACK-AT-ADVANCE: every scan folds its leaf into `w` at the step itself
 *     (`cgll_pure_fold` @24073 via `cgll_pure_get_node_p` @24034 —
 *     `intern_intermediate` + `intern_packing` + `link_packing_to_symbol`
 *     happen BEFORE the successor descriptor carrying the folded `w` is
 *     enqueued); every reduce interns its `z` Symbol + packing before
 *     resuming callers (R1 @25287-25303, R2 @25304-25399, collection close
 *     @25260-25279). Hence at any dedup event the dropped twin's content is
 *     already in the forest — nothing to reconcile (unlike the retired
 *     classic cursor-merge design, which had to LINK loser packings at merge
 *     time; that was the old RootPSlotPackingPreservation draft's L_PACK).
 *   - INTERNING IS SET-LIKE: `intern_symbol` (sppf.rs @589),
 *     `intern_intermediate` (@623), `intern_packing` (@648) all dedup on
 *     their identity keys and return the existing id; `link_packing_to_symbol`
 *     is idempotent. Re-emission of an existing fact is a no-op — modeled by
 *     `insert_fact`/`intern_all` below.
 *   - THE ⊕-AGGREGATION EDGE CASE: on a dedup hit `intern_packing` ⊕-folds
 *     the new weight into the stored packing (@652-655). The pure arm's ⊕ is
 *     the LexicographicWeight lex-min (rigail/src/lex_weight.rs; ledger §P4
 *     "⊕ keeps the lex-min packing"), which is IDEMPOTENT — so even a
 *     re-emission of the same (packing, weight) leaves the aggregate
 *     unchanged (`weight_plus_idempotent_aggregation` below); add-once makes
 *     this moot, but the model closes the loophole explicitly.
 *   - THE ORDER-INVARIANT SUCCESSOR SET (why `successors` may be modeled as
 *     a FUNCTION of the descriptor although `gll_pop` reads the mutable edge
 *     set): the GSS layer's replay protocol (gss.rs `gll_create` @1435-1483:
 *     edge dedup (target, operand_w) — a duplicate re-add yields NO replay; a
 *     NEW edge replays EVERY recorded pop of `v`; `gll_pop` @1495-1536: the
 *     P set dedups (pos, result_w) — a duplicate pop yields NO returns; a new
 *     pop emits one return per CURRENT edge) makes the total resume set equal
 *     the full product edges(u) × pops(u), each pair EXACTLY ONCE, regardless
 *     of the interleaving. Section 2 proves this product law for the
 *     transcribed protocol (`gss_replay_completeness`,
 *     `gss_resumes_exactly_once`, `gss_resumes_order_invariant`) — it is the
 *     Scott-Johnstone create/pop completeness argument, and it is what
 *     licenses the functional `successors` abstraction of Section 3.
 *
 * MODEL. Section 3 models the driver (`step_canonical_pure` @25750-25992) as
 * a small-step machine over states (seen, work, forest):
 *   - the ADD-ONCE machine: dequeue d; if d ∈ seen SKIP (the dedup/merge
 *     event — walker @25869 `continue`), else PROCESS (record d, intern its
 *     emissions, enqueue its successors);
 *   - the NAIVE machine: always PROCESS (duplicates re-emit + re-enqueue) —
 *     the hypothetical no-dedup engine the invariance is stated against.
 * Both machines are proven to compute, at any COMPLETE state (empty
 * worklist), the same seen-SET — the derivability closure of the seeds — and
 * extensionally the same forest fact set: the union of emissions over the
 * closure. The reading corollary follows for any realize function that is a
 * congruence of the extensional fact set (which `cgll_resolve_binarized` /
 * `cgll_realize_bin_symbol` / `cgll_flatten_ids*` are: they read the forest
 * through identity-keyed node/packing lookups only).
 *
 * WHAT IS NOT CLAIMED: termination (the runtime carries a 20M-step budget
 * backstop @25754; File A bounds the number of PROCESSINGS on any finite
 * trace); and the per-line Rust establishment of the purity fence (that is
 * the compiler-enforced struct + the E-stage debug asserts) — the model
 * proves that GIVEN value-functional stepping and set-like interning,
 * add-once dedup is lossless.
 *
 * THEOREMS (all admission-free; audited by `Print Assumptions`):
 *   T1 intern_all_extensional          — interning = set union (membership).
 *   T2 weight_plus_idempotent_aggregation — duplicate ⊕-contributions are
 *                                        no-ops (lex-min idempotence model).
 *   T3 gss_replay_completeness         — resumes ≡ edges × pops after any
 *                                        operation sequence (the
 *                                        create-after-pop replay law).
 *   T4 gss_resumes_exactly_once        — no (edge, pop) pair resumes twice.
 *   T5 gss_resumes_order_invariant     — the resume set depends only on the
 *                                        SET of operations, not their order.
 *   T6 worklist_computes_closure       — the add-once machine's complete
 *                                        seen set ≡ the derivability closure.
 *   T7 naive_computes_closure          — the naive machine computes the same
 *                                        closure.
 *   T8 forest_facts_are_closure_emissions — at completion the forest is
 *                                        extensionally the closure's
 *                                        emissions (both machines).
 *   T9 add_once_dedup_loses_no_derivation — THE MAIN THEOREM: an add-once
 *                                        complete run and a naive complete
 *                                        run agree on the seen SET and on
 *                                        the forest fact set extensionally.
 *   T10 realized_reading_multiset_invariant — corollary: any fact-set-
 *                                        congruent realize yields the SAME
 *                                        readings under both machines.
 *   T11 pack_at_advance_merge_lossless — at any merge (skip) event,
 *                                        re-interning the dropped twin's
 *                                        ENTIRE emission set changes the
 *                                        forest by nothing: the content was
 *                                        packed before the merge.
 *
 * FAILED STRATEGIES (documented so they are not re-attempted):
 *   - Proving T6 by induction on the RUN alone: the seed/successor coverage
 *     facts needed at the empty-worklist end-state are not stable under a
 *     bare run induction. The standard worklist-invariant pair is required:
 *     SOUND (seen ∪ work ⊆ closure) + CLOSED (seeds ⊆ seen ∪ work; the
 *     successors of every seen element ⊆ seen ∪ work); each is preserved by
 *     both step kinds and yields the two inclusions at completion.
 *   - Stating T9 against a run that "processes the duplicate in place"
 *     within the SAME machine needs a run-splicing lemma; comparing the
 *     add-once machine against the separate NAIVE machine (both to
 *     completion) states the same invariance without splicing.
 *   - `inversion` on steps whose states are record literals leaves projection
 *     redexes; a `cbn` on the projections after `subst` is required before
 *     the membership reasoning (harmless but easy to forget).
 *
 * Rocq 9.1 compatible. No Admitted, no Axiom, no Parameter (section
 * variables/hypotheses become explicit premises of the closed theorems).
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.

(* ── Generic list helpers (used by Sections 2 and 3). ── *)

Lemma nodup_map_injective_on :
  forall (A B : Type) (f : A -> B) (l : list A),
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj Hnd. induction Hnd as [|x l Hnin Hnd IH].
  - constructor.
  - cbn [map]. constructor.
    + intro Hin. apply in_map_iff in Hin.
      destruct Hin as [y [Heq Hy]].
      assert (y = x).
      { apply Hinj; [right; exact Hy | left; reflexivity | exact Heq]. }
      subst y. exact (Hnin Hy).
    + apply IH. intros x0 y0 Hx0 Hy0.
      apply Hinj; right; assumption.
Qed.

Lemma nodup_app_disjoint :
  forall (A : Type) (l1 l2 : list A),
    NoDup l1 -> NoDup l2 ->
    (forall x, In x l1 -> ~ In x l2) ->
    NoDup (l1 ++ l2).
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros l2 Hnd1 Hnd2 Hdisj.
  - exact Hnd2.
  - cbn [app]. inversion Hnd1 as [|? ? Hnin Hnd1']; subst.
    constructor.
    + intro Hin. apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
      * exact (Hnin Hin).
      * exact (Hdisj a (or_introl eq_refl) Hin).
    + apply IH; [exact Hnd1' | exact Hnd2 |].
      intros x Hx. exact (Hdisj x (or_intror Hx)).
Qed.

Section PurePackingPreservation.

  (* ═══════════════════════════════════════════════════════════════════════════
     Section 1 — INTERNING IS SET-LIKE + the ⊕-idempotence edge case.
     ═══════════════════════════════════════════════════════════════════════════ *)

  (* A forest FACT: one hash-consed identity-keyed item — an interned node
     (Symbol/Intermediate/leaf identity) or a packing link
     (parent identity, rule, child identities, i.e. the `dedup_packing` key +
     its `symbol_packings` entry). sppf.rs @418-486 dedup maps. *)
  Variable Fact : Type.
  Hypothesis fact_eq_dec : forall x y : Fact, {x = y} + {x <> y}.

  (* `insert_fact` = one intern_*/link call: a no-op on an existing identity. *)
  Definition insert_fact (fs : list Fact) (f : Fact) : list Fact :=
    if in_dec fact_eq_dec f fs then fs else f :: fs.

  Definition intern_all (fs : list Fact) (new : list Fact) : list Fact :=
    fold_left insert_fact new fs.

  Lemma insert_fact_in_iff :
    forall fs f g, In g (insert_fact fs f) <-> g = f \/ In g fs.
  Proof.
    intros fs f g. unfold insert_fact.
    destruct (in_dec fact_eq_dec f fs) as [Hin | Hnin].
    - split; [tauto |]. intros [Heq | Hg]; [subst g; exact Hin | exact Hg].
    - cbn. split; intros [Heq | Hg]; subst; tauto.
  Qed.

  (* T1 — interning a batch = set union, membership-wise. *)
  Theorem intern_all_extensional :
    forall new fs g, In g (intern_all fs new) <-> In g new \/ In g fs.
  Proof.
    induction new as [|f new IH]; intros fs g; cbn [intern_all fold_left].
    - cbn [In]. tauto.
    - fold (intern_all (insert_fact fs f) new).
      (* `In g (f :: new)` exposes `f = g` while insert_fact_in_iff exposes
         `g = f` — plain tauto treats them as distinct atoms; congruence
         leaves close the symmetric equalities. *)
      rewrite IH, insert_fact_in_iff. cbn [In]. intuition congruence.
  Qed.

  (* T2 — the ⊕-aggregation edge case: ⊕ modeled as lex-min on nat (the
     LexicographicWeight plus is a lexicographic minimum — associative,
     commutative, IDEMPOTENT). A duplicate contribution of the same packing
     weight leaves the ⊕-aggregate unchanged, so even if a merged twin's
     emission were replayed (it is not, by add-once), `intern_packing`'s
     dedup-hit ⊕-fold (sppf.rs @652-655) could not corrupt the weight. *)
  Theorem weight_plus_idempotent_aggregation :
    forall aggregate w,
      Nat.min (Nat.min aggregate w) w = Nat.min aggregate w.
  Proof.
    intros aggregate w.
    rewrite <- Nat.min_assoc, Nat.min_id. reflexivity.
  Qed.

  (* ═══════════════════════════════════════════════════════════════════════════
     Section 2 — GSS REPLAY COMPLETENESS: resumes ≡ edges × pops, exactly
     once, order-invariantly. Transcription of gss.rs `gll_create`
     (@1435-1483) + `gll_pop` (@1495-1536) for one GSS node `u`:
       - an EDGE op adds (target, operand_w) if new, and replays every
         recorded pop against the new edge (create-after-pop);
       - a POP op adds (pos, result_w) to P if new, and emits one resume per
         current edge;
       - duplicate ops are dropped by the respective dedup and emit nothing.
     This law is what makes the driver's successor set a function of the
     descriptor (order-invariant), licensing Section 3's abstraction.
     ═══════════════════════════════════════════════════════════════════════════ *)

  Variable Edge : Type.   (* CanonicalGllEdge identity: (target, operand_w) *)
  Variable Pop  : Type.   (* RecordedPop identity: (pos, result_w) *)
  Hypothesis edge_eq_dec : forall x y : Edge, {x = y} + {x <> y}.
  Hypothesis pop_eq_dec  : forall x y : Pop,  {x = y} + {x <> y}.

  Record GssNodeState : Type := mkGssNodeState {
    gss_edges   : list Edge;          (* CanonicalGssState.edges[u]        *)
    gss_pops    : list Pop;           (* CanonicalGssState.recorded_pops[u] *)
    gss_resumes : list (Edge * Pop)   (* every GllReturn materialized       *)
  }.

  Definition gss_add_edge (e : Edge) (s : GssNodeState) : GssNodeState :=
    if in_dec edge_eq_dec e (gss_edges s)
    then s   (* duplicate edge: no replay (gss.rs @1451-1456) *)
    else mkGssNodeState
           (e :: gss_edges s)
           (gss_pops s)
           (map (fun p => (e, p)) (gss_pops s) ++ gss_resumes s).
           (* create-after-pop replay: every recorded pop × the new edge *)

  Definition gss_add_pop (p : Pop) (s : GssNodeState) : GssNodeState :=
    if in_dec pop_eq_dec p (gss_pops s)
    then s   (* duplicate pop: P is a set, no returns (gss.rs @1510-1514) *)
    else mkGssNodeState
           (gss_edges s)
           (p :: gss_pops s)
           (map (fun e => (e, p)) (gss_edges s) ++ gss_resumes s).
           (* one return per current edge (gss.rs @1517-1535) *)

  Inductive GssOp : Type :=
    | OpEdge : Edge -> GssOp
    | OpPop  : Pop  -> GssOp.

  Definition gss_apply (s : GssNodeState) (o : GssOp) : GssNodeState :=
    match o with
    | OpEdge e => gss_add_edge e s
    | OpPop p  => gss_add_pop p s
    end.

  Definition gss_empty : GssNodeState := mkGssNodeState [] [] [].

  Definition gss_run (ops : list GssOp) : GssNodeState :=
    fold_left gss_apply ops gss_empty.

  (* The protocol invariant bundle. *)
  Definition gss_wf (s : GssNodeState) : Prop :=
    NoDup (gss_edges s)
    /\ NoDup (gss_pops s)
    /\ (forall e p, In (e, p) (gss_resumes s)
                    <-> In e (gss_edges s) /\ In p (gss_pops s))
    /\ NoDup (gss_resumes s).

  Lemma gss_wf_empty : gss_wf gss_empty.
  Proof.
    repeat split; cbn; try constructor; try tauto.
  Qed.

  Lemma pair_map_r_in_iff :
    forall (e x : Edge) (y : Pop) (ps : list Pop),
      In (x, y) (map (fun p => (e, p)) ps) <-> x = e /\ In y ps.
  Proof.
    intros e x y ps. rewrite in_map_iff. split.
    - intros [p [Heq Hp]]. injection Heq as -> ->. tauto.
    - intros [-> Hy]. exists y. tauto.
  Qed.

  Lemma pair_map_l_in_iff :
    forall (p : Pop) (x : Edge) (y : Pop) (es : list Edge),
      In (x, y) (map (fun e => (e, p)) es) <-> In x es /\ y = p.
  Proof.
    intros p x y es. rewrite in_map_iff. split.
    - intros [e [Heq He]]. injection Heq as -> ->. tauto.
    - intros [Hx ->]. exists x. tauto.
  Qed.

  Lemma gss_add_edge_wf :
    forall e s, gss_wf s -> gss_wf (gss_add_edge e s).
  Proof.
    intros e s Hwf. unfold gss_add_edge.
    destruct (in_dec edge_eq_dec e (gss_edges s)) as [Hin | Hnin];
      [exact Hwf |].
    destruct Hwf as [Hed [Hpd [Hiff Hrd]]].
    split; [| split; [| split]]; cbn.
    - constructor; assumption.
    - assumption.
    - intros e0 p0.
      rewrite in_app_iff, pair_map_r_in_iff, Hiff. cbn [In].
      intuition congruence.
    - apply nodup_app_disjoint.
      + apply nodup_map_injective_on; [| exact Hpd].
        intros x y _ _ Heq. injection Heq. tauto.
      + exact Hrd.
      + intros [x y] Hxy Hold.
        apply pair_map_r_in_iff in Hxy. destruct Hxy as [-> _].
        apply Hiff in Hold. destruct Hold as [He _]. exact (Hnin He).
  Qed.

  Lemma gss_add_pop_wf :
    forall p s, gss_wf s -> gss_wf (gss_add_pop p s).
  Proof.
    intros p s Hwf. unfold gss_add_pop.
    destruct (in_dec pop_eq_dec p (gss_pops s)) as [Hin | Hnin];
      [exact Hwf |].
    destruct Hwf as [Hed [Hpd [Hiff Hrd]]].
    split; [| split; [| split]]; cbn.
    - assumption.
    - constructor; assumption.
    - intros e0 p0.
      rewrite in_app_iff, pair_map_l_in_iff, Hiff. cbn [In].
      intuition congruence.
    - apply nodup_app_disjoint.
      + apply nodup_map_injective_on; [| exact Hed].
        intros x y _ _ Heq. injection Heq. tauto.
      + exact Hrd.
      + intros [x y] Hxy Hold.
        apply pair_map_l_in_iff in Hxy. destruct Hxy as [_ ->].
        apply Hiff in Hold. destruct Hold as [_ Hp]. exact (Hnin Hp).
  Qed.

  Lemma gss_run_wf_general :
    forall ops s, gss_wf s -> gss_wf (fold_left gss_apply ops s).
  Proof.
    induction ops as [|o ops IH]; intros s Hwf; cbn [fold_left].
    - exact Hwf.
    - apply IH. destruct o; [apply gss_add_edge_wf | apply gss_add_pop_wf];
        exact Hwf.
  Qed.

  Lemma gss_run_wf : forall ops, gss_wf (gss_run ops).
  Proof.
    intro ops. apply gss_run_wf_general. exact gss_wf_empty.
  Qed.

  (* T3 — THE REPLAY-COMPLETENESS PRODUCT LAW: after any operation sequence,
     the materialized resumes are exactly edges × pops. No (edge, pop)
     pairing is ever missed (the classic-GLL "late edge misses the pop" bug
     class is closed by the create-after-pop replay) and none is fabricated. *)
  Theorem gss_replay_completeness :
    forall ops e p,
      In (e, p) (gss_resumes (gss_run ops))
      <-> In e (gss_edges (gss_run ops)) /\ In p (gss_pops (gss_run ops)).
  Proof.
    intros ops. destruct (gss_run_wf ops) as [_ [_ [Hiff _]]]. exact Hiff.
  Qed.

  (* T4 — EXACTLY ONCE: no (edge, pop) pair is resumed twice (edge dedup by
     (target, operand_w) + P-set dedup by (pos, result_w) jointly). *)
  Theorem gss_resumes_exactly_once :
    forall ops, NoDup (gss_resumes (gss_run ops)).
  Proof.
    intro ops. destruct (gss_run_wf ops) as [_ [_ [_ Hnd]]]. exact Hnd.
  Qed.

  (* Edge/pop membership after a run = membership in the op stream. *)
  Lemma gss_run_edges_in_iff_general :
    forall ops s e,
      In e (gss_edges (fold_left gss_apply ops s))
      <-> In (OpEdge e) ops \/ In e (gss_edges s).
  Proof.
    induction ops as [|o ops IH]; intros s e; cbn [fold_left In].
    - tauto.
    - rewrite IH. destruct o as [e' | p']; cbn.
      + unfold gss_add_edge.
        destruct (in_dec edge_eq_dec e' (gss_edges s)) as [Hin | Hnin];
          cbn [gss_edges].
        * split; [tauto |].
          intros [[Heq | Ho] | He];
            [injection Heq as ->; tauto | tauto | tauto].
        * cbn [In]. split.
          -- intros [Ho | [Heq | He]]; subst; tauto.
          -- intros [[Heq | Ho] | He];
               [injection Heq as ->; tauto | tauto | tauto].
      + unfold gss_add_pop.
        destruct (in_dec pop_eq_dec p' (gss_pops s)) as [Hin | Hnin];
          cbn [gss_edges]; split; intro H;
          repeat match goal with
                 | H : _ \/ _ |- _ => destruct H
                 end;
          subst; try tauto; try discriminate.
  Qed.

  Lemma gss_run_pops_in_iff_general :
    forall ops s p,
      In p (gss_pops (fold_left gss_apply ops s))
      <-> In (OpPop p) ops \/ In p (gss_pops s).
  Proof.
    induction ops as [|o ops IH]; intros s p; cbn [fold_left In].
    - tauto.
    - rewrite IH. destruct o as [e' | p']; cbn.
      + unfold gss_add_edge.
        destruct (in_dec edge_eq_dec e' (gss_edges s)) as [Hin | Hnin];
          cbn [gss_pops]; split; intro H;
          repeat match goal with
                 | H : _ \/ _ |- _ => destruct H
                 end;
          subst; try tauto; try discriminate.
      + unfold gss_add_pop.
        destruct (in_dec pop_eq_dec p' (gss_pops s)) as [Hin | Hnin];
          cbn [gss_pops].
        * split; [tauto |].
          intros [[Heq | Ho] | Hp];
            [injection Heq as ->; tauto | tauto | tauto].
        * cbn [In]. split.
          -- intros [Ho | [Heq | Hp]]; subst; tauto.
          -- intros [[Heq | Ho] | Hp];
               [injection Heq as ->; tauto | tauto | tauto].
  Qed.

  (* T5 — ORDER INVARIANCE: two operation streams containing the same edge
     and pop sets materialize the same resume set — the total successor set
     of a GSS node is a function of WHAT arrived, not WHEN. This is the fact
     that licenses modeling the driver's successor map as a function of the
     descriptor value in Section 3. *)
  Theorem gss_resumes_order_invariant :
    forall ops1 ops2,
      (forall o, In o ops1 <-> In o ops2) ->
      forall e p,
        In (e, p) (gss_resumes (gss_run ops1))
        <-> In (e, p) (gss_resumes (gss_run ops2)).
  Proof.
    intros ops1 ops2 Hsame e p.
    rewrite !gss_replay_completeness.
    unfold gss_run.
    rewrite !(gss_run_edges_in_iff_general _ gss_empty),
            !(gss_run_pops_in_iff_general _ gss_empty).
    cbn [gss_edges gss_pops gss_empty].
    rewrite !(Hsame (OpEdge e)), !(Hsame (OpPop p)).
    tauto.
  Qed.

  (* ═══════════════════════════════════════════════════════════════════════════
     Section 3 — THE WORKLIST MACHINES and the derivability closure.
     ═══════════════════════════════════════════════════════════════════════════ *)

  Variable Descriptor : Type.
  Hypothesis descriptor_eq_dec : forall x y : Descriptor, {x = y} + {x <> y}.

  (* Value-functional stepping (the C7 purity fence + T5's order-invariance):
     the successor descriptors and the emitted forest facts of processing a
     descriptor are functions of its VALUE. *)
  Variable successors : Descriptor -> list Descriptor.
  Variable emissions  : Descriptor -> list Fact.
  Variable seeds      : list Descriptor.

  Record EngineState : Type := mkEngineState {
    es_seen   : list Descriptor;  (* the add-once U set (processed values)  *)
    es_work   : list Descriptor;  (* the pending worklist R                 *)
    es_forest : list Fact         (* the interned forest facts              *)
  }.

  (* The ADD-ONCE machine (walker @25800-25872: dequeue; `seen.insert` skip
     on duplicates; process otherwise). *)
  Inductive engine_step : EngineState -> EngineState -> Prop :=
    | engine_skip : forall seen d work forest,
        In d seen ->
        engine_step (mkEngineState seen (d :: work) forest)
                    (mkEngineState seen work forest)
    | engine_process : forall seen d work forest,
        ~ In d seen ->
        engine_step (mkEngineState seen (d :: work) forest)
                    (mkEngineState (d :: seen)
                                   (successors d ++ work)
                                   (intern_all forest (emissions d))).

  (* The NAIVE machine: no dedup — duplicates re-emit and re-enqueue. *)
  Inductive naive_step : EngineState -> EngineState -> Prop :=
    | naive_process : forall seen d work forest,
        naive_step (mkEngineState seen (d :: work) forest)
                   (mkEngineState (d :: seen)
                                  (successors d ++ work)
                                  (intern_all forest (emissions d))).

  (* Reflexive-transitive runs of an arbitrary step relation. *)
  Inductive machine_run (step : EngineState -> EngineState -> Prop)
    : EngineState -> EngineState -> Prop :=
    | machine_run_refl : forall s, machine_run step s s
    | machine_run_step : forall s t u,
        step s t -> machine_run step t u -> machine_run step s u.

  Lemma machine_run_preserves :
    forall (step : EngineState -> EngineState -> Prop)
           (P : EngineState -> Prop),
      (forall s t, step s t -> P s -> P t) ->
      forall s t, machine_run step s t -> P s -> P t.
  Proof.
    intros step P Hpres s t Hrun.
    induction Hrun as [s | s t u Hst Hrun IH]; intro Hs.
    - exact Hs.
    - apply IH. eapply Hpres; eauto.
  Qed.

  Definition engine_initial : EngineState := mkEngineState [] seeds [].
  Definition engine_complete (s : EngineState) : Prop := es_work s = [].

  (* The derivability closure: everything the protocol can reach from the
     seeds by stepping. *)
  Inductive derivable : Descriptor -> Prop :=
    | derivable_seed : forall d, In d seeds -> derivable d
    | derivable_succ : forall d t,
        derivable d -> In t (successors d) -> derivable t.

  (* ── The worklist invariant pair. ── *)

  Definition state_sound (s : EngineState) : Prop :=
    (forall d, In d (es_seen s) -> derivable d)
    /\ (forall d, In d (es_work s) -> derivable d).

  Definition state_closed (s : EngineState) : Prop :=
    (forall d, In d seeds -> In d (es_seen s) \/ In d (es_work s))
    /\ (forall d, In d (es_seen s) ->
          forall t, In t (successors d) ->
            In t (es_seen s) \/ In t (es_work s)).

  Definition state_forest (s : EngineState) : Prop :=
    forall f, In f (es_forest s)
      <-> exists d, In d (es_seen s) /\ In f (emissions d).

  (* Shared preservation for the PROCESS transition shape (used by both
     machines — the naive machine omits only the freshness guard, which none
     of these proofs consume). *)
  Lemma process_preserves_sound :
    forall seen d work forest,
      state_sound (mkEngineState seen (d :: work) forest) ->
      state_sound (mkEngineState (d :: seen)
                                 (successors d ++ work)
                                 (intern_all forest (emissions d))).
  Proof.
    intros seen d work forest [Hseen Hwork]. cbn in *.
    assert (Hd : derivable d) by (apply Hwork; left; reflexivity).
    split; cbn.
    - intros d0 [-> | H]; [exact Hd | apply Hseen; exact H].
    - intros d0 H. apply in_app_iff in H. destruct H as [H | H].
      + eapply derivable_succ; eauto.
      + apply Hwork. right. exact H.
  Qed.

  Lemma skip_preserves_sound :
    forall seen d work forest,
      state_sound (mkEngineState seen (d :: work) forest) ->
      state_sound (mkEngineState seen work forest).
  Proof.
    intros seen d work forest [Hseen Hwork]. split; cbn in *.
    - exact Hseen.
    - intros d0 H. apply Hwork. right. exact H.
  Qed.

  Lemma process_preserves_closed :
    forall seen d work forest,
      state_closed (mkEngineState seen (d :: work) forest) ->
      state_closed (mkEngineState (d :: seen)
                                  (successors d ++ work)
                                  (intern_all forest (emissions d))).
  Proof.
    intros seen d work forest [Hseeds Hsucc]. split; cbn in *.
    - intros d0 Hd0. destruct (Hseeds d0 Hd0) as [H | [H | H]].
      + left. right. exact H.
      + left. left. exact H.
      + right. apply in_app_iff. right. exact H.
    - intros d0 [-> | Hd0] t Ht.
      + right. apply in_app_iff. left. exact Ht.
      + destruct (Hsucc d0 Hd0 t Ht) as [H | [H | H]].
        * left. right. exact H.
        * left. left. exact H.
        * right. apply in_app_iff. right. exact H.
  Qed.

  Lemma skip_preserves_closed :
    forall seen d work forest,
      In d seen ->
      state_closed (mkEngineState seen (d :: work) forest) ->
      state_closed (mkEngineState seen work forest).
  Proof.
    intros seen d work forest Hd [Hseeds Hsucc]. split; cbn in *.
    - intros d0 Hd0. destruct (Hseeds d0 Hd0) as [H | [-> | H]];
        [left; exact H | left; exact Hd | right; exact H].
    - intros d0 Hd0 t Ht. destruct (Hsucc d0 Hd0 t Ht) as [H | [-> | H]];
        [left; exact H | left; exact Hd | right; exact H].
  Qed.

  Lemma process_preserves_forest :
    forall seen d work forest,
      state_forest (mkEngineState seen (d :: work) forest) ->
      state_forest (mkEngineState (d :: seen)
                                  (successors d ++ work)
                                  (intern_all forest (emissions d))).
  Proof.
    intros seen d work forest Hf. intro f. cbn in *.
    rewrite intern_all_extensional. split.
    - intros [H | H].
      + exists d. tauto.
      + apply Hf in H. destruct H as [d0 [Hd0 Hfd0]].
        exists d0. tauto.
    - intros [d0 [[-> | Hd0] Hfd0]].
      + left. exact Hfd0.
      + right. apply Hf. exists d0. tauto.
  Qed.

  Lemma skip_preserves_forest :
    forall seen d work forest,
      state_forest (mkEngineState seen (d :: work) forest) ->
      state_forest (mkEngineState seen work forest).
  Proof.
    intros seen d work forest Hf. intro f. cbn in *. apply Hf.
  Qed.

  (* Per-machine step preservation, assembled from the shared shapes. *)
  Lemma engine_step_preserves_invariants :
    forall s t, engine_step s t ->
      state_sound s /\ state_closed s /\ state_forest s ->
      state_sound t /\ state_closed t /\ state_forest t.
  Proof.
    intros s t Hstep [Hs [Hc Hf]].
    inversion Hstep; subst.
    - split; [| split].
      + exact (skip_preserves_sound _ _ _ _ Hs).
      + exact (skip_preserves_closed _ _ _ _ H Hc).
      + exact (skip_preserves_forest _ _ _ _ Hf).
    - split; [| split].
      + exact (process_preserves_sound _ _ _ _ Hs).
      + exact (process_preserves_closed _ _ _ _ Hc).
      + exact (process_preserves_forest _ _ _ _ Hf).
  Qed.

  Lemma naive_step_preserves_invariants :
    forall s t, naive_step s t ->
      state_sound s /\ state_closed s /\ state_forest s ->
      state_sound t /\ state_closed t /\ state_forest t.
  Proof.
    intros s t Hstep [Hs [Hc Hf]].
    inversion Hstep; subst.
    split; [| split].
    - exact (process_preserves_sound _ _ _ _ Hs).
    - exact (process_preserves_closed _ _ _ _ Hc).
    - exact (process_preserves_forest _ _ _ _ Hf).
  Qed.

  Lemma initial_invariants :
    state_sound engine_initial /\ state_closed engine_initial
    /\ state_forest engine_initial.
  Proof.
    repeat split; cbn.
    - intros d H. destruct H.
    - intros d H. apply derivable_seed. exact H.
    - intros d H. right. exact H.
    - intros d H. destruct H.
    - intro H. destruct H.
    - intros [d [H _]]. destruct H.
  Qed.

  (* Closure extraction at a complete state. *)
  Lemma complete_state_seen_is_closure :
    forall s,
      state_sound s -> state_closed s -> engine_complete s ->
      forall d, derivable d <-> In d (es_seen s).
  Proof.
    intros s [Hsound _] [Hseeds Hsucc] Hdone d.
    unfold engine_complete in Hdone.
    split.
    - intro Hd. induction Hd as [d Hd | d t Hd IH Ht].
      + destruct (Hseeds d Hd) as [H | H];
          [exact H | rewrite Hdone in H; destruct H].
      + destruct (Hsucc d IH t Ht) as [H | H];
          [exact H | rewrite Hdone in H; destruct H].
    - intro H. apply Hsound. exact H.
  Qed.

  (* T6 — the add-once machine computes exactly the derivability closure. *)
  Theorem worklist_computes_closure :
    forall s,
      machine_run engine_step engine_initial s ->
      engine_complete s ->
      forall d, derivable d <-> In d (es_seen s).
  Proof.
    intros s Hrun Hdone.
    pose proof (machine_run_preserves engine_step _
                  engine_step_preserves_invariants
                  engine_initial s Hrun initial_invariants)
      as [Hs [Hc _]].
    apply complete_state_seen_is_closure; assumption.
  Qed.

  (* T7 — the naive (duplicate-processing) machine computes the same closure. *)
  Theorem naive_computes_closure :
    forall s,
      machine_run naive_step engine_initial s ->
      engine_complete s ->
      forall d, derivable d <-> In d (es_seen s).
  Proof.
    intros s Hrun Hdone.
    pose proof (machine_run_preserves naive_step _
                  naive_step_preserves_invariants
                  engine_initial s Hrun initial_invariants)
      as [Hs [Hc _]].
    apply complete_state_seen_is_closure; assumption.
  Qed.

  (* T8 — at completion, the forest is extensionally the closure's emissions
     (both machines; stated for any run preserving the invariant bundle). *)
  Theorem forest_facts_are_closure_emissions :
    forall (step : EngineState -> EngineState -> Prop),
      (forall s t, step s t ->
         state_sound s /\ state_closed s /\ state_forest s ->
         state_sound t /\ state_closed t /\ state_forest t) ->
      forall s,
        machine_run step engine_initial s ->
        engine_complete s ->
        forall f, In f (es_forest s)
          <-> exists d, derivable d /\ In f (emissions d).
  Proof.
    intros step Hpres s Hrun Hdone f.
    pose proof (machine_run_preserves step _ Hpres engine_initial s Hrun
                  initial_invariants) as [Hs [Hc Hf]].
    rewrite (Hf f).
    split; intros [d [Hd Hfd]]; exists d; split; try exact Hfd.
    - eapply complete_state_seen_is_closure; eassumption.
    - eapply complete_state_seen_is_closure; eassumption.
  Qed.

  (* ═══════════════════════════════════════════════════════════════════════════
     Section 4 — THE MAIN THEOREMS.
     ═══════════════════════════════════════════════════════════════════════════ *)

  (* T9 — ADD-ONCE DEDUP LOSES NO DERIVATION: a complete add-once run and a
     complete naive run agree on the processed SET and, extensionally, on the
     forest. Every packing the duplicate-processing engine would have
     interned, the add-once engine interned — and vice versa. *)
  Theorem add_once_dedup_loses_no_derivation :
    forall s_dedup s_naive,
      machine_run engine_step engine_initial s_dedup ->
      engine_complete s_dedup ->
      machine_run naive_step engine_initial s_naive ->
      engine_complete s_naive ->
      (forall d, In d (es_seen s_dedup) <-> In d (es_seen s_naive))
      /\ (forall f, In f (es_forest s_dedup) <-> In f (es_forest s_naive)).
  Proof.
    intros s1 s2 Hrun1 Hdone1 Hrun2 Hdone2. split.
    - intro d.
      rewrite <- (worklist_computes_closure s1 Hrun1 Hdone1 d).
      exact (naive_computes_closure s2 Hrun2 Hdone2 d).
    - intro f.
      rewrite (forest_facts_are_closure_emissions engine_step
                 engine_step_preserves_invariants s1 Hrun1 Hdone1 f).
      rewrite (forest_facts_are_closure_emissions naive_step
                 naive_step_preserves_invariants s2 Hrun2 Hdone2 f).
      tauto.
  Qed.

  (* T10 — the realized READING MULTISET is invariant: any realize that is a
     congruence of the extensional fact set (which the binarized realize is:
     `cgll_resolve_binarized`/`cgll_realize_bin_symbol`/`cgll_flatten_ids*`
     read the forest exclusively through identity-keyed node and
     packings_of lookups) yields the same readings under both machines. *)
  Variable Reading : Type.
  Variable realize : list Fact -> list Reading.
  Hypothesis realize_reads_fact_set :
    forall fs1 fs2,
      (forall f, In f fs1 <-> In f fs2) ->
      realize fs1 = realize fs2.

  Theorem realized_reading_multiset_invariant :
    forall s_dedup s_naive,
      machine_run engine_step engine_initial s_dedup ->
      engine_complete s_dedup ->
      machine_run naive_step engine_initial s_naive ->
      engine_complete s_naive ->
      realize (es_forest s_dedup) = realize (es_forest s_naive).
  Proof.
    intros s1 s2 Hrun1 Hdone1 Hrun2 Hdone2.
    apply realize_reads_fact_set.
    exact (proj2 (add_once_dedup_loses_no_derivation
                    s1 s2 Hrun1 Hdone1 Hrun2 Hdone2)).
  Qed.

  (* T11 — PACK-AT-ADVANCE, at the merge event itself: in any reachable
     add-once state, a descriptor already processed has its ENTIRE emission
     set already interned — re-interning it (what processing the merged twin
     would have done to the forest) changes nothing. The derivation content
     was inside `w`/the forest BEFORE the merge could occur. *)
  Theorem pack_at_advance_merge_lossless :
    forall s,
      machine_run engine_step engine_initial s ->
      forall d, In d (es_seen s) ->
        forall f, In f (intern_all (es_forest s) (emissions d))
                  <-> In f (es_forest s).
  Proof.
    intros s Hrun d Hd f.
    pose proof (machine_run_preserves engine_step _
                  engine_step_preserves_invariants
                  engine_initial s Hrun initial_invariants)
      as [_ [_ Hf]].
    rewrite intern_all_extensional. split.
    - intros [H | H]; [| exact H].
      apply Hf. exists d. tauto.
    - intro H. right. exact H.
  Qed.

End PurePackingPreservation.

(* ── ADMISSION AUDIT — every theorem must print "Closed under the global context". *)
Print Assumptions intern_all_extensional.
Print Assumptions weight_plus_idempotent_aggregation.
Print Assumptions gss_replay_completeness.
Print Assumptions gss_resumes_exactly_once.
Print Assumptions gss_resumes_order_invariant.
Print Assumptions worklist_computes_closure.
Print Assumptions naive_computes_closure.
Print Assumptions forest_facts_are_closure_emissions.
Print Assumptions add_once_dedup_loses_no_derivation.
Print Assumptions realized_reading_multiset_invariant.
Print Assumptions pack_at_advance_merge_lossless.
