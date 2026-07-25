(*
 * PureForestAcyclicity: Theorem B of the S2 descriptor-pure canonical-GLL
 * campaign — the MONOTONE-FOLD / FOREST WELL-FORMEDNESS theorem: under the
 * implemented fold fences, the accepted-root packing DAG restricted to the
 * flatten-recursion graph is ACYCLIC (the cycle-fence theorem), every
 * descendant chain is length-bounded by a well-founded rank (the
 * flatten-termination witness), and any cycle in the FULL packing graph must
 * pass through a Symbol node (the publish fence's tolerate/refuse
 * classification is exhaustive).
 *
 * IMPLEMENTATION ANCHORS (prattail/src/wpda_walker.rs at the P5 tree state):
 *   - `cgll_pure_get_node_p` (~24034): the weight-carrying binarized getNodeP
 *     fold — interns `Intermediate(slot, lo, hi_z)` and links the binary
 *     `[w, z]` packing. The MONOTONE-FOLD invariant (left part's span_hi <=
 *     hi_z; regression = "the cyclic-forest constructor") is diagnosed by the
 *     env-gated FOLDTRAP right inside it (~24052-24062).
 *   - Fold ORDER fix (ledger §"FOREST-INTEGRITY"): a zero-width weight
 *     carrier attaches to the PRE-consume spine BEFORE any one-token leaf
 *     fold, so the running spine's span_hi never regresses (receipt: FOLDTRAP
 *     w_hi=4 carrier_hi=3, logs_s2p3/).
 *   - WRAP-namespace attach: `cgll_pure_carry_scan_weight` (~24207-24236) —
 *     annotation attach-folds live in the `CGLL_WRAP_TAG` (bit 30) slot
 *     namespace, never a grammar fold slot (receipt: `Inter[109]` became its
 *     own descendant when a zero-width carrier attach re-hit the same-step
 *     grammar-fold identity; `CGLL-PURE-CYCLE-KIDS 113`,
 *     logs_s2p3/new_cycleprobe.log).
 *   - POSITION-SALTED annotation slots: `cgll_pure_fold_sep_marker` (~24148),
 *     `cgll_pure_carry_scan_weight` (~24220), binder-ident/BinderScope folds —
 *     `slot ^ (pos << 1)` — so consecutive same-(sym,state) zero-width folds
 *     mint DISTINCT identities instead of re-hitting one `(slot, lo, hi)` and
 *     closing a monotone packing cycle (receipt: 151→154→151).
 *   - POSITION-COHERENCE fences: `cgll_pure_resume_fold` (~24685-24694,
 *     ~24705-24726: `span_hi > at_pos` refuse + `z_lo < w_hi` overlap refuse)
 *     and `cgll_pure_resume_replace` (~24757-24761) — a mis-paired pop/replay
 *     is refused instead of interning span-inflated/cyclic Intermediates
 *     (receipt: the PNew `new x in { x!(0) }` full-term Symbol replay-folded
 *     into its own rule frame's spine ⇒ flatten diverged at 1 GiB stack).
 *   - The ALWAYS-ON publish cycle fence: `cgll_pure_find_cycle` (~23537,
 *     iterative DFS) applied per accepting root in `step_canonical_pure`
 *     (~26030-26087): an Intermediate-only cycle is REFUSED
 *     (`cyclic_roots_refused`); a cycle whose path contains a Symbol node is
 *     TOLERATED (`cyclic_roots_tolerated`) because `cgll_flatten_ids`
 *     (~23278-23307) recurses ONLY into `Intermediate` nodes — Symbols and
 *     all leaves are flat ELEMENTS (`_ => vec![vec![id]]`), so the flatten
 *     recursion graph is exactly the Intermediate-only packing-child graph,
 *     and `cgll_realize_bin_symbol`'s memo pre-publish guard refutes the
 *     symbol-mediated packing at realize (the classic action-elide analog;
 *     P3 Pocket-A3).
 *   - Identity substrate (prattail/src/sppf.rs): `intern_intermediate` @623
 *     dedups on `(slot_id, lo, hi)`; `intern_symbol` @589 dedups on
 *     `(nt_tag, lo, hi)`; `link_packing_to_symbol` appends a packing under
 *     either; `Sppf::span_hi`/`span_lo` read the identity coordinates.
 *
 * MODEL. Nodes are abstract ids (nat). Two coordinate functions `node_hi`
 * (the identity's span end — sppf.rs `hi_pos`) and `node_salt` (the
 * equal-hi construction tiebreak: the WRAP/position-salt/namespace axis that
 * orders same-span identities within one accepting root's fold history)
 * induce the strict lexicographic CONSTRUCTION ORDER
 *     c ≺ p  iff  hi(c) < hi(p)  ∨  (hi(c) = hi(p) ∧ salt(c) < salt(p)).
 * The packing-child relation is a function `children : nat -> list nat`
 * (node ↦ the union of its packings' children — wpda_walker.rs
 * `cgll_pure_find_cycle`'s `children` closure, ~23540-23558).
 *
 * MODEL CORRESPONDENCE (what the hypotheses formalize — each theorem's block
 * restates its own): the single load-bearing hypothesis is
 *     EDGE DISCIPLINE: every packing child's identity precedes its parent in
 *     the (hi, salt) construction order (restricted to Intermediate parents /
 *     Intermediate children where stated).
 * This is the composite code invariant established by the five fences above:
 * span_hi(child) <= span_hi(parent) is the monotone-fold ordering (getNodeP
 * lo/hi derivation + fold-order fix + the position-coherence fences bounding
 * every resume material by `at_pos`), and salt-precedence on hi-ties is the
 * WRAP-namespace + position-salt freshness of zero-width attaches. The
 * model proves the DISCIPLINE ⇒ ACYCLICITY direction (the design-soundness
 * of the fences); the runtime direction (each Rust link site establishes the
 * discipline) is enforced in-process by the always-on publish DFS fence and
 * observed by the D.2 well-formedness receipts (issues=0 at d1/d4/d5,
 * wfcheck_grp_d5.log) — the model does NOT claim to verify the Rust code
 * line-by-line.
 *
 * THEOREMS (all admission-free; audited by `Print Assumptions`):
 *   T1 descends_precedes            — the construction order is transitive
 *                                     along descendant chains.
 *   T2 packing_dag_acyclic          — THE CYCLE-FENCE THEOREM: no node
 *                                     descends from itself.
 *   T3 no_link_into_own_descendant_chain — no packing links a node into its
 *                                     own descendant chain.
 *   T4 descent_chain_length_bounded — every descendant chain's length is
 *                                     <= the root's (hi, salt) rank: the
 *                                     flatten-termination witness.
 *   T5 packing_path_all_intermediate_precedes / T6
 *      every_packing_cycle_is_symbol_mediated — in the FULL packing graph
 *                                     (Symbol parents unconstrained), every
 *                                     cycle passes through a Symbol node, so
 *                                     the publish fence's REFUSE class
 *                                     (Intermediate-only cycles) is empty
 *                                     under the discipline and its TOLERATE
 *                                     class is exactly the residual.
 *   T7 fold_history_edges_decrease / T8 fold_history_flatten_acyclic /
 *      T9 fold_history_cycles_symbol_mediated — the getNodeP FOLD-EVENT
 *                                     instantiation: per-fold preconditions
 *                                     (monotone left part, salted hi-ties,
 *                                     right part = completed Symbol or
 *                                     construction-prior node) imply the edge
 *                                     discipline, hence T2/T4/T6 for the
 *                                     forest a fold history builds.
 *
 * FAILED STRATEGIES (documented so they are not re-attempted):
 *   - salt := GLOBAL MINT INDEX (allocation order). REFUTED by canonical
 *     dedup re-hits: `intern_intermediate` may RETURN an id allocated at time
 *     t_a and link a packing whose children were allocated at t > t_a (two
 *     lineages reaching the same (slot, lo, hi) — the packing-family
 *     poly-collapse, which is the POINT of the design). Mint order therefore
 *     does NOT decrease across such edges even though no cycle arises; the
 *     salt must be an IDENTITY coordinate (namespace/position-salt class),
 *     not an allocation timestamp.
 *   - Verifying the imperative DFS (`cgll_pure_find_cycle`) directly
 *     (three-color invariants + white-path theorem) was considered and set
 *     aside: the mandate's obligation is the DISCIPLINE ⇒ ACYCLICITY
 *     direction ("prove the invariant … or an equivalent well-founded
 *     measure"); the DFS is the runtime backstop of the same property, and
 *     verifying it would not discharge the discipline obligation.
 *   - A single `descends`-induction proving T4 directly stalls because the
 *     chain-length bound needs the rank of the INTERMEDIATE node, not the
 *     endpoints; the explicit `descent_chain` list predicate with induction
 *     on the list makes the measure argument one line per case.
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

Section PureForestAcyclicity.

  (* ── Identity coordinates ──────────────────────────────────────────────────
     `node_hi`  : the span end of the node's hash-consed identity
                  (sppf.rs `hi_pos` of `Intermediate`/`Symbol`; leaves get
                  their position).
     `node_salt`: the equal-hi construction tiebreak — the composite
                  (namespace, position-salt, within-step attach index) axis:
                  WRAP-tagged carrier attaches (bit 30), position-salted
                  annotation slots (`slot ^ (pos << 1)`), and grammar-dot
                  advances each mint a same-hi identity strictly later in the
                  frame's fold chain than every same-hi identity already in
                  its spine. ── *)
  Variable node_hi   : nat -> nat.
  Variable node_salt : nat -> nat.

  (* The strict lexicographic construction order: c precedes p. *)
  Definition construction_precedes (c p : nat) : Prop :=
    node_hi c < node_hi p
    \/ (node_hi c = node_hi p /\ node_salt c < node_salt p).

  Lemma construction_precedes_trans :
    forall a b c,
      construction_precedes a b ->
      construction_precedes b c ->
      construction_precedes a c.
  Proof.
    unfold construction_precedes. intros a b c Hab Hbc.
    destruct Hab as [Hab | [Hab1 Hab2]]; destruct Hbc as [Hbc | [Hbc1 Hbc2]];
      [left | left | left | right]; lia.
  Qed.

  Lemma construction_precedes_irrefl :
    forall x, ~ construction_precedes x x.
  Proof.
    unfold construction_precedes. intros x [H | [_ H]]; lia.
  Qed.

  (* ── The packing-descendant relation, parameterized by the child map
        (wpda_walker.rs `cgll_pure_find_cycle`'s `children` closure: a node's
        packings' children, flattened). `descends children p c` = c lies on
        p's descendant chain through >= 1 packing edge. ── *)
  Inductive descends (children : nat -> list nat) : nat -> nat -> Prop :=
    | descends_child : forall p c,
        In c (children p) -> descends children p c
    | descends_via : forall p m c,
        In m (children p) -> descends children m c -> descends children p c.

  Lemma descends_trans :
    forall (children : nat -> list nat) (p m q : nat),
      descends children p m -> descends children m q -> descends children p q.
  Proof.
    intros children p m q Hpm. revert q.
    induction Hpm as [p m Hm | p x m Hx Hpm IH]; intros q Hmq.
    - eapply descends_via; [exact Hm | exact Hmq].
    - eapply descends_via; [exact Hx | apply IH; exact Hmq].
  Qed.

  (* ═══════════════════════════════════════════════════════════════════════════
     T1/T2/T3 — the flatten-recursion graph (Intermediate-only packing-child
     relation: `cgll_flatten_ids` recurses only `Intermediate` nodes,
     wpda_walker.rs ~23278-23307). Hypothesis = the EDGE DISCIPLINE the five
     fences establish on exactly this graph.
     ═══════════════════════════════════════════════════════════════════════════ *)

  Section FlattenGraph.

    (* The Intermediate-only packing-child map of one accepting root's forest. *)
    Variable inter_children : nat -> list nat.

    (* MODEL CORRESPONDENCE — the edge discipline. Code invariant: at every
       pure-arm packing-link site whose parent is an `Intermediate`
       (`cgll_pure_get_node_p` fold packings; the Pocket-A2 refolds; the
       amendment-6 carrier attaches), each linked child that is itself an
       `Intermediate` has (hi, salt) lexicographically BELOW the parent:
       hi by the monotone-fold ordering + position-coherence fences, salt by
       the WRAP-namespace/position-salt freshness on hi-ties. *)
    Hypothesis fold_edges_decrease :
      forall p c, In c (inter_children p) -> construction_precedes c p.

    (* T1 — the construction order is transitive along descendant chains. *)
    Theorem descends_precedes :
      forall p c, descends inter_children p c -> construction_precedes c p.
    Proof.
      intros p c Hd. induction Hd as [p c Hc | p m c Hm Hd IH].
      - apply fold_edges_decrease. exact Hc.
      - eapply construction_precedes_trans.
        + exact IH.
        + apply fold_edges_decrease. exact Hm.
    Qed.

    (* T2 — THE CYCLE-FENCE THEOREM: the accepted-root packing DAG restricted
       to the flatten-recursion graph is acyclic. This is the property the
       always-on publish fence checks at runtime (`cyclic_roots_refused`
       would-be class) and the reason `cgll_flatten_ids`' recursion
       terminates on published roots. *)
    Theorem packing_dag_acyclic :
      forall x, ~ descends inter_children x x.
    Proof.
      intros x Hd.
      exact (construction_precedes_irrefl x (descends_precedes x x Hd)).
    Qed.

    (* T3 — no packing links a node into its own descendant chain: if c is
       already a descendant of p, no packing under c may carry p as a child
       (the exact phrasing of the mandate's invariant). *)
    Theorem no_link_into_own_descendant_chain :
      forall p c, descends inter_children p c -> ~ In p (inter_children c).
    Proof.
      intros p c Hd Hin.
      apply (packing_dag_acyclic p).
      (* extend the chain p ⇓ c by the offending edge c → p *)
      eapply descends_trans; [exact Hd |].
      apply descends_child. exact Hin.
    Qed.

    (* ── T4 — the flatten-termination witness: with salts bounded (finitely
          many namespace/salt classes per accepting root — the forest is
          finite), the nat rank hi·(saltBound+1)+salt strictly decreases per
          edge, so every explicit descent chain has length <= rank(root).
          Correspondence: `cgll_flatten_ids`' recursion depth on a published
          root is bounded — the divergence class the PNew receipt exhibited
          cannot occur under the discipline. ── *)

    Variable salt_bound : nat.
    Hypothesis node_salt_bounded : forall x, node_salt x <= salt_bound.

    Definition construction_rank (x : nat) : nat :=
      node_hi x * S salt_bound + node_salt x.

    Lemma construction_precedes_rank_lt :
      forall c p, construction_precedes c p ->
        construction_rank c < construction_rank p.
    Proof.
      unfold construction_precedes, construction_rank.
      intros c p [Hlt | [Heq Hsalt]].
      - (* hi c < hi p: rank c <= hi c·(S B) + B < (hi c + 1)·(S B) <= hi p·(S B) *)
        pose proof (node_salt_bounded c) as Hc.
        assert (S (node_hi c) <= node_hi p) as Hstep by lia.
        assert (S (node_hi c) * S salt_bound <= node_hi p * S salt_bound)
          as Hmul by (apply Nat.mul_le_mono_r; exact Hstep).
        lia.
      - rewrite Heq. lia.
    Qed.

    (* An explicit descent chain: successive packing children from a root. *)
    Fixpoint descent_chain (p : nat) (l : list nat) : Prop :=
      match l with
      | [] => True
      | c :: l' => In c (inter_children p) /\ descent_chain c l'
      end.

    (* T4 — chains are rank-bounded (flatten recursion depth bound). *)
    Theorem descent_chain_length_bounded :
      forall l p, descent_chain p l -> length l <= construction_rank p.
    Proof.
      induction l as [|c l IH]; intros p Hchain.
      - cbn. lia.
      - destruct Hchain as [Hc Hchain].
        cbn [length].
        pose proof (construction_precedes_rank_lt c p
                      (fold_edges_decrease p c Hc)) as Hrank.
        pose proof (IH c Hchain) as Hlen.
        lia.
    Qed.

  End FlattenGraph.

  (* ═══════════════════════════════════════════════════════════════════════════
     T5/T6 — the FULL publish-fence graph (`cgll_pure_find_cycle` traverses the
     packings of BOTH `Symbol` and `Intermediate` nodes, ~23540-23558).
     Symbol-parent edges carry NO discipline hypothesis: the unit-rule label
     collision legitimately places a Symbol on its own packing chain
     (`ForRowSingleNoWhere . b:InputBind |- b : ForRow` re-wraps the
     cat-changing z under the SAME `(ForRow, 0, n)` identity — P3 Pocket-A3).
     THEOREM: every cycle passes through a Symbol node, so the fence's REFUSE
     class (Intermediate-only cycles) is empty under the discipline, and its
     TOLERATE class (symbol-mediated, realize-refuted by the memo guard) is
     exactly the residual.
     ═══════════════════════════════════════════════════════════════════════════ *)

  Section FullPackingGraph.

    Variable is_symbol_node : nat -> bool.       (* SppfNode::Symbol {..} discriminant *)
    Variable packing_children : nat -> list nat. (* full fence graph child map *)

    (* MODEL CORRESPONDENCE: the discipline restricted to edges BETWEEN
       Intermediates — the only edges `cgll_flatten_ids` recurses. Edges out
       of Symbols and edges INTO Symbols are unconstrained. *)
    Hypothesis intermediate_edges_decrease :
      forall p c,
        is_symbol_node p = false ->
        In c (packing_children p) ->
        is_symbol_node c = false ->
        construction_precedes c p.

    (* An explicit path p → … → q through the full graph, recording every
       visited node after p (so a cycle p ⇝ p records its whole node set). *)
    Inductive packing_path : nat -> list nat -> nat -> Prop :=
      | packing_path_last : forall p c,
          In c (packing_children p) -> packing_path p [c] c
      | packing_path_step : forall p c l q,
          In c (packing_children p) ->
          packing_path c l q ->
          packing_path p (c :: l) q.

    (* Helper: a false forallb yields an explicit witness. *)
    Lemma forallb_false_exists :
      forall (f : nat -> bool) (l : list nat),
        forallb f l = false -> exists x, In x l /\ f x = false.
    Proof.
      intros f l. induction l as [|a l IH]; cbn [forallb].
      - discriminate.
      - intro H. apply andb_false_iff in H. destruct H as [H | H].
        + exists a. split; [left; reflexivity | exact H].
        + destruct (IH H) as [x [Hin Hx]].
          exists x. split; [right; exact Hin | exact Hx].
    Qed.

    (* T5 — along an all-Intermediate path the construction order accumulates. *)
    Theorem packing_path_all_intermediate_precedes :
      forall p l q,
        packing_path p l q ->
        forallb (fun x => negb (is_symbol_node x)) (p :: l) = true ->
        construction_precedes q p.
    Proof.
      intros p l q Hpath.
      induction Hpath as [p c Hc | p c l q Hc Hpath IH]; intro Hall.
      - (* single edge p → c, both Intermediates *)
        cbn [forallb] in Hall.
        apply andb_true_iff in Hall. destruct Hall as [Hp Hall].
        apply andb_true_iff in Hall. destruct Hall as [Hcb _].
        apply negb_true_iff in Hp. apply negb_true_iff in Hcb.
        apply intermediate_edges_decrease; assumption.
      - (* step p → c, then c ⇝ q *)
        cbn [forallb] in Hall.
        apply andb_true_iff in Hall. destruct Hall as [Hp Hall'].
        apply negb_true_iff in Hp.
        (* the tail (c :: l) is all-Intermediate — reuse it twice: once for
           the IH (path from c), once to extract c itself. *)
        assert (Hc_int : is_symbol_node c = false).
        { cbn [forallb] in Hall'. apply andb_true_iff in Hall'.
          destruct Hall' as [Hcb _]. apply negb_true_iff in Hcb. exact Hcb. }
        eapply construction_precedes_trans.
        + apply IH. exact Hall'.
        + apply intermediate_edges_decrease; assumption.
    Qed.

    (* T6 — EVERY CYCLE IS SYMBOL-MEDIATED: a packing path from p back to p
       must visit a Symbol node. Hence, under the discipline, the publish
       fence's Intermediate-only REFUSE branch is unreachable and its
       TOLERATE (symbol-mediated) branch is the complete residual class. *)
    Theorem every_packing_cycle_is_symbol_mediated :
      forall p l,
        packing_path p l p ->
        exists s, In s (p :: l) /\ is_symbol_node s = true.
    Proof.
      intros p l Hcycle.
      destruct (forallb (fun x => negb (is_symbol_node x)) (p :: l)) eqn:Hall.
      - (* all-Intermediate cycle: p strictly precedes itself — absurd *)
        exfalso.
        apply (construction_precedes_irrefl p).
        eapply packing_path_all_intermediate_precedes; eauto.
      - destruct (forallb_false_exists _ _ Hall) as [s [Hin Hs]].
        apply negb_false_iff in Hs.
        exists s. split; assumption.
    Qed.

  End FullPackingGraph.

  (* ═══════════════════════════════════════════════════════════════════════════
     T7/T8/T9 — the getNodeP FOLD-EVENT instantiation: the forest as a history
     of binary folds with the implemented per-fold preconditions.
     ═══════════════════════════════════════════════════════════════════════════ *)

  Section FoldHistory.

    (* One `cgll_pure_get_node_p(slot, w, z, lo, hi_z, weight)` event with
       w ≠ NONE ≠ z: parent = the interned `Intermediate(slot, lo, hi_z)`,
       left part = w (the running spine), right part = z (the newly attached
       leaf / completed constituent / carrier / joined operand). First-child
       folds (w = NONE) intern no packing and generate no edge. *)
    Record FoldEvent : Type := mkFoldEvent {
      fold_parent     : nat;
      fold_left_part  : nat;
      fold_right_part : nat
    }.

    Variable is_symbol_node : nat -> bool.
    Variable fold_history : list FoldEvent.

    (* The packing-child map a fold history induces (the fence graph the
       publish DFS walks, restricted to fold-built packings). *)
    Definition fold_children (p : nat) : list nat :=
      flat_map
        (fun e =>
           if Nat.eqb (fold_parent e) p
           then [fold_left_part e; fold_right_part e]
           else [])
        fold_history.

    (* ── The implemented per-fold preconditions (each mapped to its fence): ── *)

    (* Fold parents are Intermediates (`intern_intermediate`), never Symbols. *)
    Hypothesis fold_parents_are_intermediates :
      forall e, In e fold_history -> is_symbol_node (fold_parent e) = false.

    (* MONOTONE FOLD (the FOLDTRAP invariant + fold-order fix + coherence
       fences): the left part's span end never exceeds the fold's hi, and on
       an hi-tie the left part was minted strictly earlier in the same-hi
       salt chain (it IS the frame's previous spine node — WRAP namespace and
       position salts keep every same-hi attach identity fresh). *)
    Hypothesis monotone_fold_left :
      forall e, In e fold_history ->
        node_hi (fold_left_part e) <= node_hi (fold_parent e).
    Hypothesis left_tie_salted :
      forall e, In e fold_history ->
        node_hi (fold_left_part e) = node_hi (fold_parent e) ->
        node_salt (fold_left_part e) < node_salt (fold_parent e).

    (* RIGHT PART: either a completed Symbol / leaf-class node (a flatten
       SINK — Symbols by `cgll_flatten_ids`' element rule; leaves have no
       packings), or a construction-prior Intermediate (the D2 join's operand
       spine and the carrier wrappers: minted before the joining fold, at
       hi <= the fold position with salt-precedence on ties — the coherence
       fences refuse the mis-paired remainder). *)
    Hypothesis right_part_symbol_or_prior :
      forall e, In e fold_history ->
        is_symbol_node (fold_right_part e) = true
        \/ (node_hi (fold_right_part e) <= node_hi (fold_parent e)
            /\ (node_hi (fold_right_part e) = node_hi (fold_parent e) ->
                node_salt (fold_right_part e) < node_salt (fold_parent e))).

    (* Membership inversion for the induced child map. *)
    Lemma fold_children_inv :
      forall p c,
        In c (fold_children p) ->
        exists e, In e fold_history /\ fold_parent e = p
                  /\ (c = fold_left_part e \/ c = fold_right_part e).
    Proof.
      intros p c Hin. unfold fold_children in Hin.
      apply in_flat_map in Hin. destruct Hin as [e [He Hc]].
      destruct (Nat.eqb (fold_parent e) p) eqn:Heq.
      - apply Nat.eqb_eq in Heq.
        cbn in Hc.
        destruct Hc as [Hc | [Hc | []]];
          subst c; exists e; tauto.
      - cbn in Hc. contradiction.
    Qed.

    (* T7 — the fold preconditions imply the edge discipline on
       Intermediate-Intermediate edges of the induced graph. *)
    Theorem fold_history_edges_decrease :
      forall p c,
        is_symbol_node p = false ->
        In c (fold_children p) ->
        is_symbol_node c = false ->
        construction_precedes c p.
    Proof.
      intros p c _ Hin Hc_int.
      destruct (fold_children_inv p c Hin) as [e [He [Hp Hcase]]].
      subst p.
      destruct Hcase as [Hc | Hc]; subst c.
      - (* left part: monotone + salted tie *)
        pose proof (monotone_fold_left e He) as Hle.
        destruct (Nat.eq_dec (node_hi (fold_left_part e))
                             (node_hi (fold_parent e))) as [Heq | Hne].
        + right. split; [exact Heq | apply (left_tie_salted e He Heq)].
        + left. lia.
      - (* right part: the Symbol case contradicts Hc_int; else prior *)
        destruct (right_part_symbol_or_prior e He) as [Hsym | [Hle Htie]].
        + rewrite Hsym in Hc_int. discriminate.
        + destruct (Nat.eq_dec (node_hi (fold_right_part e))
                               (node_hi (fold_parent e))) as [Heq | Hne].
          * right. split; [exact Heq | apply (Htie Heq)].
          * left. lia.
    Qed.

    (* The flatten-recursion restriction of the induced graph: only
       Intermediate children are recursed (`cgll_flatten_ids`' element rule
       for Symbols/leaves). *)
    Definition fold_inter_children (p : nat) : list nat :=
      if is_symbol_node p
      then []
      else filter (fun c => negb (is_symbol_node c)) (fold_children p).

    Lemma fold_inter_children_decrease :
      forall p c, In c (fold_inter_children p) -> construction_precedes c p.
    Proof.
      intros p c Hin. unfold fold_inter_children in Hin.
      destruct (is_symbol_node p) eqn:Hp; [contradiction |].
      apply filter_In in Hin. destruct Hin as [Hin Hc].
      apply negb_true_iff in Hc.
      apply fold_history_edges_decrease; assumption.
    Qed.

    (* T8 — the forest a fenced fold history builds has an ACYCLIC flatten
       graph: `cgll_flatten_ids` cannot revisit a node through its own
       packing descendants on any published root. *)
    Theorem fold_history_flatten_acyclic :
      forall x, ~ descends fold_inter_children x x.
    Proof.
      exact (packing_dag_acyclic fold_inter_children
               fold_inter_children_decrease).
    Qed.

    (* T9 — every cycle of the FULL fold graph is symbol-mediated: the
       publish fence's classification is exhaustive for fold-built forests. *)
    Theorem fold_history_cycles_symbol_mediated :
      forall p l,
        packing_path fold_children p l p ->
        exists s, In s (p :: l) /\ is_symbol_node s = true.
    Proof.
      exact (every_packing_cycle_is_symbol_mediated
               is_symbol_node fold_children fold_history_edges_decrease).
    Qed.

  End FoldHistory.

End PureForestAcyclicity.

(* ── ADMISSION AUDIT — every theorem must print "Closed under the global context". *)
Print Assumptions descends_precedes.
Print Assumptions packing_dag_acyclic.
Print Assumptions no_link_into_own_descendant_chain.
Print Assumptions descent_chain_length_bounded.
Print Assumptions packing_path_all_intermediate_precedes.
Print Assumptions every_packing_cycle_is_symbol_mediated.
Print Assumptions fold_history_edges_decrease.
Print Assumptions fold_history_flatten_acyclic.
Print Assumptions fold_history_cycles_symbol_mediated.
