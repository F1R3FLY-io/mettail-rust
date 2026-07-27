(*
 * SpineSimulationAccept: S1-FACTORING F5-1 FV-2 extension (table-level,
 * arm-free) — the HONEST SCOPE is unchanged from the shipped
 * SpineSimulation (NOT a full descriptor/GSS runtime bisimulation — that
 * is covered empirically by the H9 asserts + the F5-1 P4/P5 A/B rows, and
 * protocol-wise by FV-3b): the static trie-path / commit-coordinate
 * correspondence, now over the ACCEPT FORK of the F5-1 sibling-leaf model
 * (TrieLeafBijectionAccept):
 *
 *   (1′) CONSUMED-ITEM PRESERVATION over forests — for every member m with
 *        a leaf at depth d anywhere in the group forest (interior-accept or
 *        tail-complete), the spine coordinate at arm k+1 consumes EXACTLY
 *        items(m)[k] for every k < d; the ACCEPT sharpening: the arm
 *        consuming the accept's edge item consumes the member's LAST item —
 *        the commit branch consumes m's k-th item exactly as OFF's pos-k
 *        arm does;
 *   (2′) CONCATENATION AT COMMIT with ε member-tail — for an accept member,
 *        spine-consumed(items[0..d]) ++ member-tail = items(m) with
 *        member-tail = ε (d = |items|); the member-side position coverage
 *        degenerates to "the spine covers ALL of 1..total, the final-pos
 *        resume covers nothing" — the TRUE accept resumes DIRECTLY on its
 *        final-pos Pop arm;
 *   (3′) DIVERGENCE PARTITION over the accept fork — the arm consuming the
 *        accept's edge item emits BOTH the member's typed commit branch AND
 *        the spine-continue branch (`accept_fork_emits_both`: the built
 *        part-forest is `TInterior e cs :: accepts` with the accept leaf a
 *        SIBLING sharing item e); a guard death at the divergence kills
 *        EXACTLY the per-member set (the part = the members whose own next
 *        item is the dead edge — equal to OFF where each member's own
 *        single-branch guard on the same expected text dies); an accept
 *        member and its same-item interior siblings BOTH survive the shared
 *        edge;
 *   (4′) FOLD-COUNT PRESERVATION carries — accept branches add ZERO folds
 *        (the member tail past the commit is empty), supplying the K-A
 *        lateness premise for the accept-enabled emission.
 *
 * Model source: PrattailWpdaRuntime.TrieLeafBijection (FV-1) +
 * PrattailWpdaRuntime.SpineSimulation (FV-2, used verbatim through the
 * partition bridge) + PrattailWpdaRuntime.TrieLeafBijectionAccept (FV-1′).
 * Rust anchors: macros/src/gen/runtime/wpda_codegen/factoring.rs @ HEAD
 * a5296eea (build_tree @632-690 — the accept fork materializes as a
 * divergence Fork over a node's spliced child forest, one branch per
 * child, accept commit branches carrying the member's own OFF-shape
 * action; ★A1 order remainder ++ accepts @618-631), plan §2.2 (the
 * InputBind@ arm-3 accept fork: two ReplaceAndPush branches, both pushing
 * CategoryEntry(Name), replace symbols member-vs-spine).
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
From Stdlib Require Import Sorting.Permutation.
From PrattailWpdaRuntime Require Import TrieLeafBijection.
From PrattailWpdaRuntime Require Import SpineSimulation.
From PrattailWpdaRuntime Require Import TrieLeafBijectionAccept.
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════
   (1′) CONSUMED-ITEM PRESERVATION over the forest.
   ═══════════════════════════════════════════════════════════════════════ *)

(* Every spine arm consumes the member's OWN item — for EVERY leaf of the
   group forest, accepts included (arm k+1 consumes items(m)[k], the F1
   pre-root/root-edge convention preserved by flatten_forest). *)
Theorem consumed_item_preservation_forest :
  forall fuel edge ms f t m d path,
    build_node_a fuel 1 edge ms = Some f ->
    (forall m', In m' ms -> firstn 1 (m_items m') = [edge]) ->
    In t f ->
    In (m, d, path) (leaf_entries [] t) ->
    forall k, k < d -> nth_error path k = nth_error (m_items m) k.
Proof.
  intros fuel edge ms f t m d path HB Hfirst Hint Hin k Hk.
  destruct (root_forest_path_items fuel edge ms f HB Hfirst t Hint
              m d path Hin) as [Hpath [Hd1 Hd2]].
  subst path.
  apply nth_error_firstn_lt. exact Hk.
Qed.

(* The ACCEPT sharpening: a leaf whose depth exhausts the member's item
   sequence spells the FULL sequence — the arm consuming its edge item
   consumes the member's LAST item, exactly as OFF's own final-position
   consuming arm does. *)
Theorem accept_edge_consumes_last_item :
  forall fuel edge ms f t m d path,
    build_node_a fuel 1 edge ms = Some f ->
    (forall m', In m' ms -> firstn 1 (m_items m') = [edge]) ->
    In t f ->
    In (m, d, path) (leaf_entries [] t) ->
    d = length (m_items m) ->
    path = m_items m
    /\ nth_error path (d - 1) = nth_error (m_items m) (d - 1).
Proof.
  intros fuel edge ms f t m d path HB Hfirst Hint Hin Hd.
  destruct (root_forest_path_items fuel edge ms f HB Hfirst t Hint
              m d path Hin) as [Hpath [Hd1 Hd2]].
  assert (Hfull : path = m_items m).
  { eapply accept_path_full_items; [exact Hpath | lia]. }
  split; [exact Hfull |].
  rewrite Hfull. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (2′) CONCATENATION AT COMMIT — the ε member-tail case.
   ═══════════════════════════════════════════════════════════════════════ *)

(* An accept member's spine-consumed prefix IS its whole item sequence; the
   member tail past the commit is EMPTY. *)
Theorem accept_concatenation :
  forall (m : member) (d : nat),
    d = length (m_items m) ->
    firstn d (m_items m) ++ skipn d (m_items m) = m_items m
    /\ skipn d (m_items m) = []
    /\ length (firstn d (m_items m)) = d.
Proof.
  intros m d Hd. subst d.
  split; [apply firstn_skipn | split].
  - apply skipn_all.
  - rewrite firstn_all. reflexivity.
Qed.

(* Position coverage degenerates: the spine covers ALL of the member's OFF
   positions 1..total and the resume at binder_pos_at total = total + 1
   covers NOTHING — the TRUE accept's commit resumes directly on its
   final-pos Pop arm (instantiations of the shipped alignment laws at
   d = total). *)
Corollary accept_alignment_binder :
  forall total,
    seq 1 total ++ seq (binder_pos_at total) (total - total) = seq 1 total.
Proof.
  intro total. apply commit_alignment_binder. lia.
Qed.

Corollary accept_resume_covers_nothing_binder :
  forall total, seq (binder_pos_at total) (total - total) = [].
Proof.
  intro total. replace (total - total) with 0 by lia. reflexivity.
Qed.

Corollary accept_alignment_nullary :
  forall total,
    seq 0 total ++ seq (nullary_sub_pos_at total) (total - total)
    = seq 0 total.
Proof.
  intro total. apply commit_alignment_nullary. lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (3′) DIVERGENCE PARTITION over the accept fork.
   ═══════════════════════════════════════════════════════════════════════ *)

(* Accept-side routing/completeness: a member drains to the accepts of a
   node EXACTLY when its own item sequence exhausts there — the accept
   branch set at the node is the exhausted-member set, no more, no less. *)
Theorem accept_routing :
  forall depth ms parts' accs' m,
    partition_left_m depth ms [] [] = (parts', accs') ->
    (In m accs' <-> In m ms /\ nth_error (m_items m) depth = None).
Proof.
  intros depth ms parts' accs' m H.
  rewrite (partition_left_m_accepts_iff _ _ _ _ _ _ m H).
  cbn [In]. tauto.
Qed.

(* The divergence-partition law transported to the accept-enabled partition
   (same parts as F0 through the bridge): the child keyed `e` holds EXACTLY
   the members whose own next item is `e`. *)
Theorem divergence_partition_m :
  forall depth ms parts' accs' e part,
    partition_left_m depth ms [] [] = (parts', accs') ->
    In (e, part) parts' ->
    forall m,
      In m part <-> (In m ms /\ nth_error (m_items m) depth = Some e).
Proof.
  intros depth ms parts' accs' e part HPm HinP m.
  pose proof (partition_left_m_bridge _ _ _ _ _ _ HPm) as EB.
  cbn [map] in EB.
  exact (divergence_partition depth ms parts' (map m_rule accs') e part
           EB HinP m).
Qed.

(* A guard death on edge `e` at the divergence kills EXACTLY the per-member
   set: a live member (own next item e') dies with the `e`-keyed branch iff
   e' = e — the same set its own single-branch guard (expected_text = its
   own items[depth], the binder.rs Literal-arm convention) would kill. *)
Theorem guard_death_kills_exact_member_set :
  forall depth ms parts' accs' e part m e',
    partition_left_m depth ms [] [] = (parts', accs') ->
    In (e, part) parts' ->
    In m ms ->
    nth_error (m_items m) depth = Some e' ->
    (In m part <-> e' = e).
Proof.
  intros depth ms parts' accs' e part m e' HPm HinP HinMs Hnth.
  split.
  - intro HinPart.
    destruct (proj1 (divergence_partition_m _ _ _ _ _ _ HPm HinP m)
                HinPart) as [_ Hnth'].
    congruence.
  - intro He. subst e'.
    apply (proj2 (divergence_partition_m _ _ _ _ _ _ HPm HinP m)).
    split; assumption.
Qed.

(* An accept member and its same-item interior siblings BOTH survive the
   shared edge: within the part keyed `e`, the exhausting member (length =
   S depth — its LAST item is e) and any continuing member both carry
   items[depth] = e — equal to OFF, where both members' own arms pass the
   same expected text. *)
Theorem accept_and_continuation_both_survive :
  forall depth ms parts' accs' e part m_a m_c,
    partition_left_m depth ms [] [] = (parts', accs') ->
    In (e, part) parts' ->
    In m_a part -> length (m_items m_a) = S depth ->
    In m_c part -> S depth < length (m_items m_c) ->
    nth_error (m_items m_a) depth = Some e
    /\ nth_error (m_items m_c) depth = Some e.
Proof.
  intros depth ms parts' accs' e part m_a m_c HPm HinP HaP _ HcP _.
  split.
  - exact (proj2 (proj1 (divergence_partition_m _ _ _ _ _ _ HPm HinP m_a)
                    HaP)).
  - exact (proj2 (proj1 (divergence_partition_m _ _ _ _ _ _ HPm HinP m_c)
                    HcP)).
Qed.

(* THE ACCEPT-FORK SHAPE THEOREM: when a part holds a member exhausting at
   the node (the accept, length = dep) AND a member continuing past it, the
   built forest for that part is `TInterior e cs :: accepts` with cs
   NONEMPTY and the accept materialized as a SIBLING LEAF carrying the SAME
   edge item e and depth dep — the arm consuming e therefore emits BOTH the
   spine-continue branch (the interior, ★A1-first) AND the member's typed
   commit branch (the accept leaf, whose commit coordinates are
   finalize_commit m_a dep — FV-1′ theorem (d′): the member's OWN
   completion machinery). *)
Theorem accept_fork_emits_both :
  forall fuel dep e part f m_a m_c,
    build_node_a (S fuel) dep e part = Some f ->
    In m_a part -> length (m_items m_a) = dep ->
    In m_c part -> dep < length (m_items m_c) ->
    exists cs accs,
      f = TInterior e cs :: map (fun m => TLeaf e m dep) accs
      /\ cs <> []
      /\ In m_a accs
      /\ In (TLeaf e m_a dep) (map (fun m => TLeaf e m dep) accs).
Proof.
  intros fuel dep e part f m_a m_c HB HaP Halen HcP Hclen.
  destruct part as [| m0 [| m1 ms1]].
  - (* empty part cannot hold m_a *)
    cbn in HaP. contradiction.
  - (* a singleton part would force m_a = m_c, contradicting the lengths *)
    destruct HaP as [Ha | []]. destruct HcP as [Hc | []].
    subst m0. rewrite <- Hc in Hclen. lia.
  - rewrite build_node_a_eq_ge2 in HB.
    destruct (partition_left_m dep (m0 :: m1 :: ms1) [] [])
      as [parts accs] eqn:EPm.
    destruct (build_forest_a fuel (S dep) parts) as [children |] eqn:EF;
      [| discriminate].
    (* the accept member drains to the accepts *)
    assert (HmaAcc : In m_a accs).
    { apply (proj2 (partition_left_m_accepts_iff _ _ _ _ _ _ m_a EPm)).
      right. split; [exact HaP |].
      apply nth_error_None. lia. }
    (* the continuing member routes to a part, so the children are NONEMPTY *)
    assert (Hsome : exists it_c, nth_error (m_items m_c) dep = Some it_c).
    { destruct (nth_error (m_items m_c) dep) as [it_c |] eqn:Ec.
      - exists it_c. reflexivity.
      - apply nth_error_None in Ec. lia. }
    destruct Hsome as [it_c Ec].
    pose proof (partition_left_m_bridge _ _ _ _ _ _ EPm) as EB.
    cbn [map] in EB.
    assert (HinParts : exists part', In (it_c, part') parts /\ In m_c part').
    { eapply divergence_completeness; [exact EB | exact HcP | exact Ec]. }
    destruct HinParts as [part' [HinP' HinM']].
    destruct children as [| c cs].
    + (* children = [] contradicts m_c's presence in the parts *)
      exfalso.
      pose proof (proj2 (build_a_cnt fuel) (S dep) parts []
                    (m_rule m_c) EF) as HC.
      rewrite forest_leaf_rules_nil, cnt_nil in HC.
      assert (HinPR : In (m_rule m_c) (parts_rules parts)).
      { unfold parts_rules.
        apply in_flat_map.
        exists (it_c, part').
        split; [exact HinP' | cbn [snd]; apply in_map; exact HinM']. }
      apply (count_occ_In Nat.eq_dec) in HinPR.
      lia.
    + inversion HB; subst f.
      exists (c :: cs), accs.
      split; [reflexivity | split; [discriminate | split]].
      * exact HmaAcc.
      * exact (in_map (fun m => TLeaf e m dep) accs m_a HmaAcc).
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (4′) FOLD-COUNT PRESERVATION — accept branches add ZERO folds (the K-A
   lateness premise for the accept-enabled emission: the commit branch
   consumes m's k-th item exactly as OFF's pos-k arm does; nothing follows
   member-side).
   ═══════════════════════════════════════════════════════════════════════ *)

Theorem accept_fold_count :
  forall (m : member) (d : nat),
    d = length (m_items m) ->
    length (firstn d (m_items m)) + length (skipn d (m_items m))
    = length (m_items m)
    /\ length (skipn d (m_items m)) = 0.
Proof.
  intros m d Hd.
  split.
  - apply fold_count_items. lia.
  - subst d. rewrite skipn_all. reflexivity.
Qed.

Theorem accept_fold_count_positions :
  forall total, total + (total - total) = total.
Proof.
  intro total. apply fold_count_positions. lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   INSTANCE PINS — the rholang InputBind@ accept fork (the only real
   cohort; item codes and members from TrieLeafBijectionAccept).
   ═══════════════════════════════════════════════════════════════════════ *)

(* The root divergence (depth 1, after the shared P(Proc) operand): the
   `<-`-vs-`<=` split routes {r2, r3} against {r6}, no accepts yet. *)
Theorem rholang_inputbind_root_divergence :
  partition_left_m 1 [ib_query; ib_quoted; ib_persistent] [] []
  = ([(1, [ib_query; ib_quoted]); (6, [ib_persistent])], []).
Proof. vm_compute. reflexivity. Qed.

(* THE ACCEPT FORK (depth 3, at the P(Name) edge): r3 exhausts — it drains
   to the accepts — while r2 continues under its `!` item. *)
Theorem rholang_inputbind_accept_divergence :
  partition_left_m 3 [ib_query; ib_quoted] [] []
  = ([(3, [ib_query])], [ib_quoted]).
Proof. vm_compute. reflexivity. Qed.

(* The built part-forest at the accept edge: the spine-continue interior
   FIRST (★A1), the r3 accept leaf LAST, BOTH carrying the P(Name) = 2
   edge item — the two-branch fork whose fan (2) equals OFF's own two
   CategoryEntry(Name) pushes at this edge (the plan §2.3 cost parity). *)
Theorem rholang_inputbind_accept_fork_shape :
  build_node_a 30 3 2 [ib_query; ib_quoted]
  = Some [TInterior 2 [TLeaf 3 ib_query 4]; TLeaf 2 ib_quoted 3].
Proof. vm_compute. reflexivity. Qed.

Theorem rholang_inputbind_accept_fork_fan :
  length [TInterior 2 [TLeaf 3 ib_query 4]; TLeaf 2 ib_quoted 3] = 2.
Proof. reflexivity. Qed.

(* The generic fork-shape theorem instantiated on the real cohort. *)
Theorem rholang_inputbind_accept_fork_emits_both :
  exists cs accs,
    [TInterior 2 [TLeaf 3 ib_query 4]; TLeaf 2 ib_quoted 3]
    = TInterior 2 cs :: map (fun m => TLeaf 2 m 3) accs
    /\ cs <> []
    /\ In ib_quoted accs
    /\ In (TLeaf 2 ib_quoted 3) (map (fun m => TLeaf 2 m 3) accs).
Proof.
  eapply (accept_fork_emits_both 29 3 2 [ib_query; ib_quoted]
            _ ib_quoted ib_query).
  - exact rholang_inputbind_accept_fork_shape.
  - right. left. reflexivity.
  - reflexivity.
  - left. reflexivity.
  - cbn [m_items ib_query length]. lia.
Qed.

(* Both-survive at the accept edge: r3 (the accept) and r2 (the
   continuation) each carry P(Name) = 2 as their depth-2 item — a guard
   death anywhere else never separates them before the fork. *)
Theorem rholang_inputbind_both_survive_name_edge :
  nth_error (m_items ib_quoted) 2 = Some 2
  /\ nth_error (m_items ib_query) 2 = Some 2.
Proof. vm_compute. split; reflexivity. Qed.

(* The ε member-tail receipts for the r3 accept. *)
Theorem rholang_inputbind_accept_concatenation :
  firstn 3 (m_items ib_quoted) ++ skipn 3 (m_items ib_quoted)
  = m_items ib_quoted
  /\ skipn 3 (m_items ib_quoted) = [].
Proof. vm_compute. split; reflexivity. Qed.

(* ── Assumption audit — every line must print "Closed under the global
      context". ── *)
Print Assumptions consumed_item_preservation_forest.
Print Assumptions accept_edge_consumes_last_item.
Print Assumptions accept_concatenation.
Print Assumptions accept_alignment_binder.
Print Assumptions accept_resume_covers_nothing_binder.
Print Assumptions accept_alignment_nullary.
Print Assumptions accept_routing.
Print Assumptions divergence_partition_m.
Print Assumptions guard_death_kills_exact_member_set.
Print Assumptions accept_and_continuation_both_survive.
Print Assumptions accept_fork_emits_both.
Print Assumptions accept_fold_count.
Print Assumptions accept_fold_count_positions.
Print Assumptions rholang_inputbind_root_divergence.
Print Assumptions rholang_inputbind_accept_divergence.
Print Assumptions rholang_inputbind_accept_fork_shape.
Print Assumptions rholang_inputbind_accept_fork_fan.
Print Assumptions rholang_inputbind_accept_fork_emits_both.
Print Assumptions rholang_inputbind_both_survive_name_edge.
Print Assumptions rholang_inputbind_accept_concatenation.
