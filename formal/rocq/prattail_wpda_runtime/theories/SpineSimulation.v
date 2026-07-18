(*
 * SpineSimulation: S1-FACTORING FV-2 (table-level, arm-free) — the honest
 * scope per the F3 plan (s1f3_election_parity_plan.md §3): NOT a full
 * descriptor/GSS runtime bisimulation (covered empirically by the H9
 * asserts + the elected-term A/B, and protocol-wise by FV-3b), but the
 * static trie-path / commit-coordinate correspondence over FV-1's model:
 *
 *   (1) CONSUMED-ITEM PRESERVATION — for every member m with a leaf at
 *       depth d, the spine coordinate at arm k+1 (the pre-root arm is
 *       arm 1) consumes EXACTLY items(m)[k], for every k < d;
 *   (2) CONCATENATION AT COMMIT — spine-consumed ++ member-tail-consumed
 *       = items(m), and the member-side position coverage is exactly
 *       OFF's own 1..total ("arm p consumes positions[p-1]": spine covers
 *       1..d, the commit resume at p = d+1 covers d+1..total);
 *   (3) DIVERGENCE PARTITION — at any interior node the children's edge
 *       items PARTITION the live members by their next item (routing +
 *       completeness + NoDup keys + per-key uniqueness), so a guard death
 *       on a child edge excludes EXACTLY the member set whose own
 *       per-member guards (single-branch GuardedConsumeAndReplace on the
 *       same expected text — binder.rs Literal-arm convention) would die;
 *   (4) FOLD-COUNT PRESERVATION — the number of consumed items per
 *       reading is stance-invariant (the K-A lateness premise cited by
 *       the F3 plan §1.4-P1 for CgllKTuple invariance).
 *
 * Model source: PrattailWpdaRuntime.TrieLeafBijection (FV-1) — members,
 * items, partition_left/add_to_parts, build_node/build_forest, the path
 * law. Rust anchors: macros/src/gen/runtime/wpda_codegen/factoring.rs
 * (build_tree @558-603 partition accumulation; finalize_leaf @516-551
 * identity coordinates), binder.rs (Literal arms = single-branch guarded
 * consumes; final-pos Pop), the F1 emission loop (divergence Fork over
 * trie children, factoring.rs @1138-1343, child_branch_tokens @1060-1101
 * guard payloads).
 *
 * `Print Assumptions` on every theorem must report
 * "Closed under the global context" (zero admission / axiom / parameter;
 * Rocq 9.1).
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From PrattailWpdaRuntime Require Import TrieLeafBijection.
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════
   (1) CONSUMED-ITEM PRESERVATION.
   ═══════════════════════════════════════════════════════════════════════ *)

Lemma nth_error_firstn_lt :
  forall (l : list item) d k,
    k < d -> nth_error (firstn d l) k = nth_error l k.
Proof.
  induction l as [| x xs IH]; intros d k Hk.
  - now rewrite firstn_nil.
  - destruct d as [| d]; [lia |].
    destruct k as [| k]; simpl.
    + reflexivity.
    + apply IH. lia.
Qed.

(* Every spine arm consumes the member's OWN item: arm k+1 (pre-root arm
   = arm 1 consuming items[0], flatten_tree's F1 root-edge convention)
   consumes items(m)[k] for every k below the leaf depth. *)
Theorem consumed_item_preservation :
  forall fuel edge ms t acc m d path,
    build_node fuel 1 edge ms = Some (t, acc) ->
    (forall m', In m' ms -> firstn 1 (m_items m') = [edge]) ->
    In (m, d, path) (leaf_entries [] t) ->
    forall k, k < d -> nth_error path k = nth_error (m_items m) k.
Proof.
  intros fuel edge ms t acc m d path HB Hfirst Hin k Hk.
  destruct (root_path_items fuel edge ms t acc HB Hfirst m d path Hin)
    as [Hpath [Hd1 Hd2]].
  subst path.
  apply nth_error_firstn_lt. exact Hk.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (2) CONCATENATION AT COMMIT.
   ═══════════════════════════════════════════════════════════════════════ *)

(* The spine-consumed prefix plus the member tail reconstitute the member's
   own item sequence, and the prefix length is exactly the leaf depth. *)
Theorem commit_concatenation :
  forall (m : member) (d : nat),
    d <= length (m_items m) ->
    firstn d (m_items m) ++ skipn d (m_items m) = m_items m
    /\ length (firstn d (m_items m)) = d.
Proof.
  intros m d Hd.
  split.
  - apply firstn_skipn.
  - apply firstn_length_le. exact Hd.
Qed.

(* Member-side POSITION coverage: the spine covers member positions 1..d
   (identity pos map, FV-1 theorem (d)), the Binder commit resumes at
   p = d + 1 = binder_pos_at d and the member tail covers d+1..total —
   together EXACTLY OFF's own coverage 1..total. *)
Theorem commit_alignment_binder :
  forall d total,
    d <= total ->
    seq 1 d ++ seq (binder_pos_at d) (total - d) = seq 1 total.
Proof.
  intros d total Hd.
  unfold binder_pos_at.
  replace (S d) with (1 + d) by lia.
  rewrite <- seq_app.
  f_equal. lia.
Qed.

(* The nullary twin: sub_pos cursor coverage 0..(total-1) split at
   sub_pos = leaf_depth (MixfixLiteralRun literal indexing). *)
Theorem commit_alignment_nullary :
  forall d total,
    d <= total ->
    seq 0 d ++ seq (nullary_sub_pos_at d) (total - d) = seq 0 total.
Proof.
  intros d total Hd.
  unfold nullary_sub_pos_at.
  replace d with (0 + d) at 2 by lia.
  rewrite <- seq_app.
  f_equal. lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (3) DIVERGENCE PARTITION.
   ═══════════════════════════════════════════════════════════════════════ *)

(* Routing (soundness): already FV-1's partition_left_inv — restated at
   Q := membership for the divergence phrasing. *)
Theorem divergence_routing :
  forall depth ms parts' accepts' it part m,
    partition_left depth ms [] [] = (parts', accepts') ->
    In (it, part) parts' ->
    In m part ->
    In m ms /\ nth_error (m_items m) depth = Some it.
Proof.
  intros depth ms parts' accepts' it part m HP HinP HinM.
  assert (Hinv : parts_inv depth (fun m' => In m' ms) parts').
  { eapply partition_left_inv;
      [exact HP | intros ? Hx; exact Hx | apply parts_inv_nil]. }
  exact (Hinv _ _ _ HinP HinM).
Qed.

(* add_to_parts key/membership facts. *)
Lemma add_to_parts_preserves :
  forall acc it m i p x,
    In (i, p) acc -> In x p ->
    exists p', In (i, p') (add_to_parts it m acc) /\ In x p'.
Proof.
  induction acc as [| [j js] rest IH]; intros it m i p x HinA HinX.
  - simpl in HinA. contradiction.
  - simpl. destruct (Nat.eqb j it) eqn:Ej.
    + destruct HinA as [Heq | HinA'].
      * inversion Heq; subst j p.
        exists (js ++ [m]).
        split; [left; reflexivity | apply in_or_app; left; exact HinX].
      * exists p. split; [right; exact HinA' | exact HinX].
    + destruct HinA as [Heq | HinA'].
      * inversion Heq; subst j p.
        exists js. split; [left; reflexivity | exact HinX].
      * destruct (IH it m i p x HinA' HinX) as [p' [Hin1 Hin2]].
        exists p'. split; [right; exact Hin1 | exact Hin2].
Qed.

Lemma add_to_parts_adds :
  forall acc it m,
    exists p', In (it, p') (add_to_parts it m acc) /\ In m p'.
Proof.
  induction acc as [| [j js] rest IH]; intros it m; simpl.
  - exists [m]. split; [left; reflexivity | left; reflexivity].
  - destruct (Nat.eqb j it) eqn:Ej.
    + apply Nat.eqb_eq in Ej; subst j.
      exists (js ++ [m]).
      split; [left; reflexivity | apply in_or_app; right; left; reflexivity].
    + destruct (IH it m) as [p' [Hin1 Hin2]].
      exists p'. split; [right; exact Hin1 | exact Hin2].
Qed.

Lemma partition_left_preserves :
  forall depth ms acc accepts parts' accepts' i p x,
    partition_left depth ms acc accepts = (parts', accepts') ->
    In (i, p) acc -> In x p ->
    exists p', In (i, p') parts' /\ In x p'.
Proof.
  intros depth ms.
  induction ms as [| m rest IH];
    intros acc accepts parts' accepts' i p x H HinA HinX; simpl in H.
  - inversion H; subst. exists p. split; assumption.
  - destruct (nth_error (m_items m) depth) as [it0 |] eqn:E.
    + destruct (add_to_parts_preserves acc it0 m _ _ _ HinA HinX)
        as [p' [Hin1 Hin2]].
      exact (IH _ _ _ _ _ _ _ H Hin1 Hin2).
    + exact (IH _ _ _ _ _ _ _ H HinA HinX).
Qed.

(* Completeness: every live member (its item at `depth` exists) lands in
   the part keyed by that item. *)
Theorem divergence_completeness :
  forall depth ms acc accepts parts' accepts' m it,
    partition_left depth ms acc accepts = (parts', accepts') ->
    In m ms ->
    nth_error (m_items m) depth = Some it ->
    exists part, In (it, part) parts' /\ In m part.
Proof.
  intros depth ms.
  induction ms as [| m0 rest IH];
    intros acc accepts parts' accepts' m it H HinM Hnth.
  - simpl in HinM. contradiction.
  - simpl in H.
    destruct HinM as [Heq | HinM'].
    + subst m0.
      rewrite Hnth in H.
      destruct (add_to_parts_adds acc it m) as [p0 [Hin1 Hin2]].
      exact (partition_left_preserves _ _ _ _ _ _ _ _ _ H Hin1 Hin2).
    + destruct (nth_error (m_items m0) depth) as [it0 |] eqn:E0.
      * exact (IH _ _ _ _ _ _ H HinM' Hnth).
      * exact (IH _ _ _ _ _ _ H HinM' Hnth).
Qed.

(* NoDup keys: distinct children carry distinct edge items. *)
Lemma add_to_parts_key_in :
  forall acc it m k,
    In k (map fst (add_to_parts it m acc)) ->
    In k (map fst acc) \/ k = it.
Proof.
  induction acc as [| [j js] rest IH]; intros it m k Hin; simpl in *.
  - destruct Hin as [Heq | []]. right. now symmetry.
  - destruct (Nat.eqb j it) eqn:Ej; simpl in Hin.
    + destruct Hin as [Heq | Hin'];
        [left; left; exact Heq | left; right; exact Hin'].
    + destruct Hin as [Heq | Hin'].
      * left. left. exact Heq.
      * destruct (IH it m k Hin') as [HinR | Hk];
          [left; right; exact HinR | right; exact Hk].
Qed.

Lemma add_to_parts_nodup_keys :
  forall acc it m,
    NoDup (map fst acc) ->
    NoDup (map fst (add_to_parts it m acc)).
Proof.
  induction acc as [| [j js] rest IH]; intros it m HND; simpl.
  - constructor; [intro Habs; exact Habs | constructor].
  - destruct (Nat.eqb j it) eqn:Ej; simpl in *.
    + exact HND.
    + inversion HND; subst.
      constructor.
      * intro Habs.
        destruct (add_to_parts_key_in rest it m j Habs) as [HinR | Hjit].
        -- contradiction.
        -- apply Nat.eqb_neq in Ej. contradiction.
      * apply IH; assumption.
Qed.

Theorem divergence_nodup_keys :
  forall depth ms acc accepts parts' accepts',
    partition_left depth ms acc accepts = (parts', accepts') ->
    NoDup (map fst acc) ->
    NoDup (map fst parts').
Proof.
  intros depth ms.
  induction ms as [| m rest IH];
    intros acc accepts parts' accepts' H HND; simpl in H.
  - inversion H; subst. exact HND.
  - destruct (nth_error (m_items m) depth) as [it |] eqn:E.
    + eapply IH; [exact H | apply add_to_parts_nodup_keys; exact HND].
    + eapply IH; [exact H | exact HND].
Qed.

(* Per-key uniqueness of the child part. *)
Lemma nodup_fst_unique :
  forall (ps : list (item * list member)) it p1 p2,
    NoDup (map fst ps) ->
    In (it, p1) ps -> In (it, p2) ps -> p1 = p2.
Proof.
  induction ps as [| [j js] rest IH]; intros it p1 p2 HND Hin1 Hin2.
  - simpl in Hin1. contradiction.
  - simpl in *.
    inversion HND; subst.
    destruct Hin1 as [Heq1 | Hin1']; destruct Hin2 as [Heq2 | Hin2'].
    + inversion Heq1; inversion Heq2; subst. reflexivity.
    + inversion Heq1; subst.
      exfalso. apply H1.
      apply in_map with (f := fst) in Hin2'. exact Hin2'.
    + inversion Heq2; subst.
      exfalso. apply H1.
      apply in_map with (f := fst) in Hin1'. exact Hin1'.
    + exact (IH it p1 p2 H2 Hin1' Hin2').
Qed.

(* THE DIVERGENCE-PARTITION LAW: the (unique) child keyed `e` holds
   EXACTLY the members whose own next item is `e` — a guard death on
   child `e` kills the SAME set the per-member single-branch guards
   (expected_text = the member's own items[depth]) would kill. *)
Theorem divergence_partition :
  forall depth ms parts' accepts' e part,
    partition_left depth ms [] [] = (parts', accepts') ->
    In (e, part) parts' ->
    forall m,
      In m part
      <-> (In m ms /\ nth_error (m_items m) depth = Some e).
Proof.
  intros depth ms parts' accepts' e part HP HinP m.
  split.
  - intro HinM.
    exact (divergence_routing _ _ _ _ _ _ _ HP HinP HinM).
  - intros [HinMs Hnth].
    destruct (divergence_completeness _ _ _ _ _ _ _ _ HP HinMs Hnth)
      as [part2 [HinP2 HinM2]].
    assert (Hnd : NoDup (map fst parts')).
    { eapply divergence_nodup_keys; [exact HP | constructor]. }
    rewrite (nodup_fst_unique parts' e part part2 Hnd HinP HinP2).
    exact HinM2.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (4) FOLD-COUNT PRESERVATION (the K-A lateness premise).
   ═══════════════════════════════════════════════════════════════════════ *)

(* Item-level: consumed-fold counts split exactly at the commit. *)
Theorem fold_count_items :
  forall (m : member) (d : nat),
    d <= length (m_items m) ->
    length (firstn d (m_items m)) + length (skipn d (m_items m))
    = length (m_items m).
Proof.
  intros m d Hd.
  rewrite <- (firstn_skipn d (m_items m)) at 3.
  rewrite length_app. reflexivity.
Qed.

(* Position-level: spine positions (d) plus member-tail positions
   (total - d) equal the member's own OFF position count. *)
Theorem fold_count_positions :
  forall d total, d <= total -> d + (total - d) = total.
Proof.
  intros d total Hd. lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   INSTANCE PIN — the fortranmodel DO group's divergence node (depth 6,
   Int-vs-Real): partition_left routes DoLoop under item 1 = P(Int,0) and
   DoAssign under item 6 = P(Real,0), disjointly (census
   logs_s1f3/fortranmodel_census.txt).
   ═══════════════════════════════════════════════════════════════════════ *)

Theorem fortranmodel_do_divergence :
  partition_left 6 [do_loop; do_assign] [] []
  = ([(1, [do_loop]); (6, [do_assign])], []).
Proof. vm_compute. reflexivity. Qed.

(* ── Assumption audit — every line must print "Closed under the global
      context". ── *)
Print Assumptions consumed_item_preservation.
Print Assumptions commit_concatenation.
Print Assumptions commit_alignment_binder.
Print Assumptions commit_alignment_nullary.
Print Assumptions divergence_routing.
Print Assumptions divergence_completeness.
Print Assumptions divergence_nodup_keys.
Print Assumptions divergence_partition.
Print Assumptions fold_count_items.
Print Assumptions fold_count_positions.
