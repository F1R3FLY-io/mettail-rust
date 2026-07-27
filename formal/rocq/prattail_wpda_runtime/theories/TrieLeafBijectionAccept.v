(*
 * TrieLeafBijectionAccept: S1-FACTORING F5-1 FV-1 extension (codegen-level,
 * arm-free) — the ACCEPT-ENABLED trie build (`S1F5_ACCEPT_CONTINUE == true`,
 * sibling-leaf form) is a LOSSLESS re-arrangement of its bucket members over
 * FOREST-shaped tries:
 *
 *   (a′) leaves ↔ members is a (total) bijection — the F0 statement
 *        "leaves ∪ interior-accept nodes ↔ members" is realized as a PURE
 *        LEAF bijection because interior-accept members ARE leaves in the
 *        sibling-leaf representation (an accept member is hoisted one edge
 *        earlier as an ordinary leaf sharing its edge item with the
 *        continuation subtree; the ε-branch reading is refuted — no
 *        non-consuming marker-replace ForkActionKind exists, plan §9-FS1);
 *   (b′) every root-to-leaf edge path in the forest spells EXACTLY the
 *        member's own post-trigger item prefix of length leaf_depth — now
 *        holding for accepts with |items| < sibling depths, where the path
 *        is the member's FULL item sequence and the leaf edge its LAST item;
 *   (c′) partition/no-loss: former `InteriorAccept` ineligibles are ABSORBED
 *        into groups (`bucket_partition_a` groups every buildable ≥2-part);
 *        Σ leaves + Σ ineligible + |singletons| = cohort re-derived (INV-8's
 *        formula unchanged), and the absorption is EXACT — the F5-1 forest's
 *        leaf multiset is a permutation of the F0 tree's leaves ++ its
 *        drained interior accepts (`accept_absorption`);
 *   (d′) commit-coordinate alignment: TRUE accepts (untruncated,
 *        total == leaf_depth) get resume_pos = total + 1 (the member's OWN
 *        final-pos Pop arm) with NO member-side remainder; nullary accepts
 *        land tail-complete at sub_pos = parts_len; truncated accepts keep
 *        their member-side remainder (the rule-20 precedent) — "the accept
 *        is the member's own completion machinery";
 *   (e′) the WEAKENED child-item invariant (red-team F-10 restatement): per
 *        node, at most one INTERIOR child per item, and accept leaves share
 *        their edge item with the continuation subtree when one exists (ALL
 *        trees of a node's forest carry the node's edge item); all-twins
 *        parts return accepts-only forests — NEVER `Interior{children: []}`.
 *
 * ── EXTENSION DISCIPLINE ──
 * This file `Require Import`s the shipped F3.2 files and NEVER restates or
 * weakens them: `TrieLeafBijection` supplies the member/tree/partition/
 * builder model and the F0 theorems (used verbatim for the absorption
 * bridge); `SpineSimulation` supplies the NoDup-key machinery
 * (`divergence_nodup_keys`) reused for the (e′) at-most-one-interior proof.
 * The F0 builder `build_node`/`build_forest` and its theorems stay the
 * model of the `accept_continue == false` stance; the new
 * `build_node_a`/`build_forest_a` model the `accept_continue == true`
 * stance, and the two are BRIDGED through `partition_left_m_bridge` (same
 * parts, member-valued accepts).
 *
 * ── CROSS-REFERENCE TABLE (model ↔ the Rust it transcribes;
 *    macros/src/gen/runtime/wpda_codegen/factoring.rs @ HEAD a5296eea) ──
 *
 *   `partition_left_m`         ↔ build_tree's per-node accumulation
 *                                (@652-675): exhausted members
 *                                (items.len() == depth) drain to `accepts`
 *                                AS MEMBERS (they leaf out), the rest
 *                                partition by items[depth] in
 *                                first-occurrence order
 *   `build_node_a`,
 *   `build_forest_a`           ↔ build_tree (@632-690), forest-returning:
 *                                a singleton part is an EARLIEST-UNIQUENESS
 *                                leaf at the current depth (@639-648);
 *                                parents SPLICE child forests into their
 *                                children lists (@676-679); an all-exhausted
 *                                part returns the accepts-only forest
 *                                (@680-685, red-team F-10); otherwise the
 *                                forest is `Interior :: accepts` — the ★A1
 *                                NORMATIVE ORDER `remainder ++ accepts`
 *                                (@618-631, 686-689)
 *   accept leaf edge item      ↔ `SpineTree::Leaf { item: edge_item.clone(),
 *                                member: finalize_leaf(m, depth) }` (@658-661)
 *                                — the accept SHARES the edge INTO the node,
 *                                weakening the child-item invariant exactly
 *                                as documented at SpineTree (@231-237)
 *   `finalize_commit` at
 *   depth == |items|           ↔ finalize_leaf (@555-590) applied VERBATIM
 *                                at exhaustion (the F0 A4 maps need no shape
 *                                extension): Binder resume_pos = depth + 1
 *                                (= positions.len()+1 = the final-pos Pop
 *                                arm for a TRUE accept), Nullary sub_pos =
 *                                depth (= parts_len, tail-complete),
 *                                remainder = truncated || total > depth
 *   `bucket_partition_a`       ↔ build_prefix_factoring_with @ accept_
 *                                continue == true (@723-869): exclusions
 *                                FIRST (abstract `excl`), root partition,
 *                                lone root children → singletons, ≥2-parts
 *                                → groups (interior_accepts stays EMPTY —
 *                                @815-826 is unreachable in this stance)
 *   `forest_leaf_count`        ↔ the eligible-group leaf-count assert
 *                                (@842-848): Σ forest leaves == member count
 *
 * The concrete INSTANCE pinned at the end is the ONLY real interior-accept
 * cohort across all 22 bundled engines (F5-1 plan §1 census, red-team
 * confirmed): rholang `(InputBind, "@")` = {InputBindQuotedQuery = 2,
 * InputBindQuoted = 3 (the accept), InputBindQuotedPersistent = 6}.
 * Item codes: 0 = P(Proc,0) · 1 = L"<-" · 2 = P(Name,0) · 3 = L"!" ·
 * 4 = L"?" · 5 = L"(" · 6 = L"<=".
 * Trie (the committed test pin, factoring.rs
 * `rholang_inputbind_at_cohort_factors_with_accept_continue`):
 *   P(0,0)[L(<-)[P(Name,0)[L(!)=>r2] P(Name,0)=>r3] L(<=)=>r6]
 * — the r3 accept leaf SHARES its P(Name) edge item with the continuation
 * subtree, listed AFTER it (★A1).
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
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════
   The accept-enabled partition: exhausted members drain AS MEMBERS (they
   will leaf out), mirroring build_tree @652-675. `partition_left` (F0)
   drains their RULE INDICES instead; the two runs produce the SAME parts
   (the bridge below), so every F0 parts-side fact transports.
   ═══════════════════════════════════════════════════════════════════════ *)

Fixpoint partition_left_m (depth : nat) (ms : list member)
  (acc : list (item * list member)) (accepts : list member)
  : list (item * list member) * list member :=
  match ms with
  | [] => (acc, accepts)
  | m :: rest =>
      match nth_error (m_items m) depth with
      | Some it => partition_left_m depth rest (add_to_parts it m acc) accepts
      | None    => partition_left_m depth rest acc (accepts ++ [m])
      end
  end.

(* THE BRIDGE: same traversal, same parts; the accept sides are related by
   `map m_rule`. Every parts-side F0 theorem (routing, completeness, NoDup
   keys, the count law) transports through this equation. *)
Lemma partition_left_m_bridge :
  forall depth ms acc maccs parts' maccs',
    partition_left_m depth ms acc maccs = (parts', maccs') ->
    partition_left depth ms acc (map m_rule maccs)
    = (parts', map m_rule maccs').
Proof.
  intros depth ms.
  induction ms as [| m rest IH]; intros acc maccs parts' maccs' H;
    simpl in *.
  - inversion H; subst. reflexivity.
  - destruct (nth_error (m_items m) depth) as [it |] eqn:E.
    + exact (IH _ _ _ _ H).
    + specialize (IH _ _ _ _ H). rewrite map_app in IH. exact IH.
Qed.

(* Accept-side membership: a member drains to the accepts EXACTLY when its
   item sequence exhausts at `depth` (nth_error = None). *)
Lemma partition_left_m_accepts_iff :
  forall depth ms acc maccs parts' maccs' m,
    partition_left_m depth ms acc maccs = (parts', maccs') ->
    (In m maccs' <->
       In m maccs \/ (In m ms /\ nth_error (m_items m) depth = None)).
Proof.
  intros depth ms.
  induction ms as [| m0 rest IH]; intros acc maccs parts' maccs' m H;
    simpl in H.
  - inversion H; subst. simpl. tauto.
  - destruct (nth_error (m_items m0) depth) as [it |] eqn:E.
    + rewrite (IH _ _ _ _ m H). cbn [In].
      split.
      * intros [HmA | [HmR HmN]]; [left; exact HmA |].
        right. split; [right; exact HmR | exact HmN].
      * intros [HmA | [[Heq | HmR] HmN]]; [left; exact HmA | |].
        -- subst m0. rewrite E in HmN. discriminate.
        -- right. split; [exact HmR | exact HmN].
    + rewrite (IH _ _ _ _ m H).
      rewrite in_app_iff. cbn [In].
      split.
      * intros [[HmA | [Heq | []]] | [HmR HmN]].
        -- left; exact HmA.
        -- subst m0. right. split; [left; reflexivity | exact E].
        -- right. split; [right; exact HmR | exact HmN].
      * intros [HmA | [[Heq | HmR] HmN]].
        -- left. left. exact HmA.
        -- subst m0. left. right. left. reflexivity.
        -- right. split; [exact HmR | exact HmN].
Qed.

(* All-exhausted parts (identical-sequence twins) drain WHOLESALE, in member
   order — the F-10 accepts-only premise. *)
Lemma partition_left_m_all_none :
  forall depth ms acc maccs,
    (forall m, In m ms -> nth_error (m_items m) depth = None) ->
    partition_left_m depth ms acc maccs = (acc, maccs ++ ms).
Proof.
  intros depth ms.
  induction ms as [| m rest IH]; intros acc maccs Hall; simpl.
  - now rewrite app_nil_r.
  - rewrite (Hall m (or_introl eq_refl)).
    rewrite IH.
    + now rewrite <- app_assoc.
    + intros m' Hin. apply Hall. right. exact Hin.
Qed.

(* At the bucket's root partition (depth 0) nothing drains, provided every
   live member has a nonempty item sequence (EmptySequence members are
   excluded BEFORE the partition, factoring.rs @770-775). *)
Lemma partition_left_m_no_accepts_at_0 :
  forall ms acc maccs parts' maccs',
    (forall m, In m ms -> m_items m <> []) ->
    partition_left_m 0 ms acc maccs = (parts', maccs') ->
    maccs' = maccs.
Proof.
  induction ms as [| m rest IH]; intros acc maccs parts' maccs' Hne H;
    simpl in H.
  - inversion H; subst. reflexivity.
  - destruct (m_items m) as [| x xs] eqn:E.
    + exfalso. exact (Hne m (or_introl eq_refl) E).
    + eapply IH; [| exact H].
      intros m' Hin. apply Hne. right. exact Hin.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   The forest builder (build_tree @632-690, accept_continue == true).
   Fuel-indexed like the F0 builder; every theorem is conditioned on the
   build RETURNING, and the concrete instances compute at fuel 32.
   ═══════════════════════════════════════════════════════════════════════ *)

Fixpoint build_node_a (fuel : nat) (depth : nat) (edge : item)
  (ms : list member) {struct fuel} : option (list tree) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match ms with
      | [m] => Some [TLeaf edge m depth]
      | _ =>
          match partition_left_m depth ms [] [] with
          | (parts, accs) =>
              match build_forest_a fuel' (S depth) parts with
              | None => None
              | Some children =>
                  match children with
                  | [] => Some (map (fun m => TLeaf edge m depth) accs)
                  | _ :: _ =>
                      (* ★A1 NORMATIVE ORDER: remainder ++ accepts. *)
                      Some (TInterior edge children
                              :: map (fun m => TLeaf edge m depth) accs)
                  end
              end
          end
      end
  end
with build_forest_a (fuel : nat) (depth : nat)
  (ps : list (item * list member)) {struct fuel} : option (list tree) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match ps with
      | [] => Some []
      | (it, part) :: rest =>
          match build_node_a fuel' depth it part with
          | None => None
          | Some f1 =>
              match build_forest_a fuel' depth rest with
              | None => None
              | Some f2 => Some (f1 ++ f2)
              end
          end
      end
  end.

(* Definitional equations (reflexivity — pin the fixpoint unfoldings so
   proofs can rewrite hypotheses reliably; the F0 house pattern). *)
Lemma build_node_a_eq_nil :
  forall fuel depth edge,
    build_node_a (S fuel) depth edge []
    = match build_forest_a fuel (S depth) [] with
      | None => None
      | Some children =>
          match children with
          | [] => Some []
          | _ :: _ => Some [TInterior edge children]
          end
      end.
Proof. reflexivity. Qed.

Lemma build_node_a_eq_one :
  forall fuel depth edge m,
    build_node_a (S fuel) depth edge [m] = Some [TLeaf edge m depth].
Proof. reflexivity. Qed.

Lemma build_node_a_eq_ge2 :
  forall fuel depth edge m0 m1 ms1,
    build_node_a (S fuel) depth edge (m0 :: m1 :: ms1)
    = match partition_left_m depth (m0 :: m1 :: ms1) [] [] with
      | (parts, accs) =>
          match build_forest_a fuel (S depth) parts with
          | None => None
          | Some children =>
              match children with
              | [] => Some (map (fun m => TLeaf edge m depth) accs)
              | _ :: _ =>
                  Some (TInterior edge children
                          :: map (fun m => TLeaf edge m depth) accs)
              end
          end
      end.
Proof. reflexivity. Qed.

Lemma build_forest_a_eq_nil :
  forall fuel depth, build_forest_a (S fuel) depth [] = Some [].
Proof. reflexivity. Qed.

Lemma build_forest_a_eq_cons :
  forall fuel depth it part rest,
    build_forest_a (S fuel) depth ((it, part) :: rest)
    = match build_node_a fuel depth it part with
      | None => None
      | Some f1 =>
          match build_forest_a fuel depth rest with
          | None => None
          | Some f2 => Some (f1 ++ f2)
          end
      end.
Proof. reflexivity. Qed.

(* ═══════════════════════════════════════════════════════════════════════
   Forest bookkeeping helpers.
   ═══════════════════════════════════════════════════════════════════════ *)

Lemma forest_leaf_rules_app :
  forall a b,
    forest_leaf_rules (a ++ b) = forest_leaf_rules a ++ forest_leaf_rules b.
Proof.
  intros a b.
  induction a as [| t rest IH]; simpl.
  - reflexivity.
  - unfold forest_leaf_rules in *. simpl. rewrite IH. now rewrite app_assoc.
Qed.

Lemma forest_leaf_rules_map_leaf :
  forall e d accs,
    forest_leaf_rules (map (fun m => TLeaf e m d) accs) = map m_rule accs.
Proof.
  intros e d accs.
  induction accs as [| a rest IH]; simpl.
  - reflexivity.
  - unfold forest_leaf_rules in *. simpl. now rewrite IH.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   THEOREM (a′) — LEAVES ↔ MEMBERS over the forest, TOTALLY (no drained
   residue: accepts ARE leaves).
   ═══════════════════════════════════════════════════════════════════════ *)

Lemma build_a_cnt :
  forall fuel,
    (forall depth edge ms f r,
        build_node_a fuel depth edge ms = Some f ->
        cnt (forest_leaf_rules f) r = cnt (rules_of ms) r)
    /\
    (forall depth ps f r,
        build_forest_a fuel depth ps = Some f ->
        cnt (forest_leaf_rules f) r = cnt (parts_rules ps) r).
Proof.
  induction fuel as [| fuel IH]; split; intros depth.
  - intros edge ms f r H. discriminate.
  - intros ps f r H. discriminate.
  - (* node, S fuel *)
    intros edge ms f r H.
    destruct ms as [| m0 [| m1 ms1]].
    + (* [] — the empty forest *)
      rewrite build_node_a_eq_nil in H.
      destruct fuel as [| fuel']; [cbn in H; discriminate |].
      rewrite build_forest_a_eq_nil in H.
      cbn in H. inversion H; subst f.
      rewrite forest_leaf_rules_nil, rules_of_nil, !cnt_nil. reflexivity.
    + (* singleton earliest-uniqueness leaf *)
      rewrite build_node_a_eq_one in H.
      inversion H; subst f.
      rewrite forest_leaf_rules_cons, forest_leaf_rules_nil.
      cbn [leaf_rules].
      rewrite rules_of_cons, rules_of_nil, cnt_cons, !cnt_nil.
      rewrite count_occ_app, cnt_nil. lia.
    + (* >= 2 members *)
      rewrite build_node_a_eq_ge2 in H.
      destruct (partition_left_m depth (m0 :: m1 :: ms1) [] [])
        as [parts accs] eqn:EPm.
      destruct (build_forest_a fuel (S depth) parts) as [children |] eqn:EF;
        [| discriminate].
      pose proof (proj2 IH (S depth) parts children r EF) as HF.
      pose proof (partition_left_m_bridge _ _ _ _ _ _ EPm) as EB.
      cbn [map] in EB.
      pose proof (partition_left_cnt _ _ _ _ _ _ r EB) as HP.
      rewrite parts_rules_nil, !cnt_nil in HP.
      destruct children as [| c cs].
      * inversion H; subst f.
        rewrite forest_leaf_rules_map_leaf.
        rewrite forest_leaf_rules_nil, cnt_nil in HF. lia.
      * inversion H; subst f.
        rewrite forest_leaf_rules_cons, leaf_rules_interior,
          forest_leaf_rules_map_leaf.
        rewrite count_occ_app. lia.
  - (* forest, S fuel *)
    intros ps f r H.
    destruct ps as [| [it part] rest].
    + rewrite build_forest_a_eq_nil in H.
      inversion H; subst f.
      rewrite forest_leaf_rules_nil, parts_rules_nil, !cnt_nil. reflexivity.
    + rewrite build_forest_a_eq_cons in H.
      destruct (build_node_a fuel depth it part) as [f1 |] eqn:EN;
        [| discriminate].
      destruct (build_forest_a fuel depth rest) as [f2 |] eqn:EF;
        [| discriminate].
      inversion H; subst f.
      pose proof (proj1 IH depth it part f1 r EN) as H1.
      pose proof (proj2 IH depth rest f2 r EF) as H2.
      rewrite forest_leaf_rules_app, parts_rules_cons, !count_occ_app.
      unfold rules_of in H1. lia.
Qed.

(* The forest bijection: EVERY member — interior-accept or tail-complete —
   maps to exactly one leaf, with no drained residue. *)
Theorem forest_leaf_bijection :
  forall fuel depth edge ms f,
    build_node_a fuel depth edge ms = Some f ->
    Permutation (forest_leaf_rules f) (rules_of ms).
Proof.
  intros fuel depth edge ms f H.
  apply (Permutation_count_occ Nat.eq_dec).
  intro r.
  exact (proj1 (build_a_cnt fuel) _ _ _ _ r H).
Qed.

Theorem forest_leaf_rules_nodup :
  forall fuel depth edge ms f,
    build_node_a fuel depth edge ms = Some f ->
    NoDup (rules_of ms) ->
    NoDup (forest_leaf_rules f).
Proof.
  intros fuel depth edge ms f H HND.
  apply forest_leaf_bijection in H.
  eapply Permutation_NoDup; [apply Permutation_sym; exact H | exact HND].
Qed.

(* The runtime eligible-group leaf-count assert (factoring.rs @842-848) as a
   corollary. *)
Theorem forest_leaf_count :
  forall fuel depth edge ms f,
    build_node_a fuel depth edge ms = Some f ->
    length (forest_leaf_rules f) = length ms.
Proof.
  intros fuel depth edge ms f H.
  apply forest_leaf_bijection in H.
  apply Permutation_length in H.
  unfold rules_of in H. now rewrite length_map in H.
Qed.

(* A nonempty member set builds a nonempty forest (never an empty group). *)
Lemma build_a_nonempty :
  forall fuel depth edge ms f,
    build_node_a fuel depth edge ms = Some f ->
    ms <> [] ->
    f <> [].
Proof.
  intros fuel depth edge ms f H Hne Habs.
  subst f.
  pose proof (forest_leaf_count _ _ _ _ _ H) as HL.
  rewrite forest_leaf_rules_nil in HL.
  destruct ms as [| m rest]; [exact (Hne eq_refl) | cbn in HL; discriminate].
Qed.

(* THE ABSORPTION THEOREM: the F5-1 forest's leaves are a permutation of the
   F0 tree's leaves ++ its drained interior accepts — the interior-accept
   phrasing "leaves ∪ interior-accept nodes ↔ members" realized as a pure
   leaf bijection (the accepts BECOME leaves; the two builders may run at
   independent fuels). *)
Theorem accept_absorption :
  forall fuel fuel0 depth edge ms f t0 acc0,
    build_node_a fuel depth edge ms = Some f ->
    build_node fuel0 depth edge ms = Some (t0, acc0) ->
    Permutation (forest_leaf_rules f) (leaf_rules t0 ++ acc0).
Proof.
  intros fuel fuel0 depth edge ms f t0 acc0 H HA.
  eapply Permutation_trans; [eapply forest_leaf_bijection; exact H |].
  apply Permutation_sym. eapply trie_leaf_bijection. exact HA.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   THEOREM (b′) — PATH-ITEMS PREFIX LAW over the forest. Accept leaves sit
   at the node where their member exhausts, sharing the node's edge item —
   their path is the member's FULL item sequence.
   ═══════════════════════════════════════════════════════════════════════ *)

Lemma build_a_paths :
  forall fuel,
    (forall depth edge ms f pfx,
        build_node_a fuel depth edge ms = Some f ->
        (forall m, In m ms -> firstn depth (m_items m) = pfx ++ [edge]) ->
        S (length pfx) = depth ->
        forall t, In t f ->
        forall m d path, In (m, d, path) (leaf_entries pfx t) ->
          path = firstn d (m_items m)
          /\ depth <= d
          /\ d <= length (m_items m))
    /\
    (forall depth ps f pfx,
        build_forest_a fuel depth ps = Some f ->
        (forall it part m, In (it, part) ps -> In m part ->
            firstn depth (m_items m) = pfx ++ [it]) ->
        S (length pfx) = depth ->
        forall t, In t f ->
        forall m d path, In (m, d, path) (leaf_entries pfx t) ->
          path = firstn d (m_items m)
          /\ depth <= d
          /\ d <= length (m_items m)).
Proof.
  induction fuel as [| fuel IH]; split; intros depth.
  - intros edge ms f pfx HB. discriminate.
  - intros ps f pfx HB. discriminate.
  - (* node, S fuel *)
    intros edge ms f pfx HB Hpfx Hlen t Hint m d path Hin.
    destruct ms as [| m0 [| m1 ms1]].
    + (* [] — the empty forest carries no leaves *)
      rewrite build_node_a_eq_nil in HB.
      destruct fuel as [| fuel']; [cbn in HB; discriminate |].
      rewrite build_forest_a_eq_nil in HB.
      cbn in HB. inversion HB; subst f.
      cbn in Hint. contradiction.
    + (* singleton earliest-uniqueness leaf *)
      rewrite build_node_a_eq_one in HB.
      inversion HB; subst f.
      destruct Hint as [Heqt | []]. subst t.
      cbn [leaf_entries] in Hin.
      destruct Hin as [Heq | []].
      (* FAILED STRATEGY (do not re-attempt): `inversion Heq; subst` — on
         the entry tuple (m0, depth, pfx ++ [edge]) = (m, d, path) the
         blind subst eliminates `depth` (substituting depth := d), breaking
         every later reference to depth. Use the F0 house pattern: explicit
         injection + TARGETED subst of m0/d/path only. *)
      injection Heq as Hm0 Hd Hpath.
      subst m0 d path.
      pose proof (Hpfx m (or_introl eq_refl)) as Hp.
      assert (Hlenf : length (firstn depth (m_items m)) = depth).
      { rewrite Hp. rewrite length_app. cbn [length]. lia. }
      rewrite firstn_length in Hlenf.
      split; [| split].
      * now rewrite <- Hp.
      * lia.
      * lia.
    + (* >= 2 members *)
      rewrite build_node_a_eq_ge2 in HB.
      destruct (partition_left_m depth (m0 :: m1 :: ms1) [] [])
        as [parts accs] eqn:EPm.
      destruct (build_forest_a fuel (S depth) parts) as [children |] eqn:EF;
        [| discriminate].
      pose proof (partition_left_m_bridge _ _ _ _ _ _ EPm) as EB.
      cbn [map] in EB.
      assert (Hinv0 : parts_inv depth
                        (fun m'' => In m'' (m0 :: m1 :: ms1)) parts).
      { eapply partition_left_inv;
          [exact EB | intros ? Hx; exact Hx | apply parts_inv_nil]. }
      assert (Hacc : forall a, In a accs ->
                In a (m0 :: m1 :: ms1)
                /\ nth_error (m_items a) depth = None).
      { intros a HaIn.
        destruct (proj1 (partition_left_m_accepts_iff _ _ _ _ _ _ a EPm)
                    HaIn) as [Habs | Hok]; [contradiction | exact Hok]. }
      (* the shared accept-leaf discharge: the path is the FULL member
         sequence, exhausting exactly at `depth` *)
      assert (HacceptLeaf : forall a m' d' path',
                 In a accs ->
                 In (m', d', path') (leaf_entries pfx (TLeaf edge a depth)) ->
                 path' = firstn d' (m_items m')
                 /\ depth <= d'
                 /\ d' <= length (m_items m')).
      { intros a m' d' path' HaIn Hin'.
        cbn [leaf_entries] in Hin'.
        destruct Hin' as [Heq | []].
        injection Heq as Ha Hd' Hpath'.
        subst a d' path'.
        destruct (Hacc m' HaIn) as [HinMs Hnone].
        pose proof (Hpfx m' HinMs) as Hp.
        assert (Hlenf : length (firstn depth (m_items m')) = depth).
        { rewrite Hp. rewrite length_app. cbn [length]. lia. }
        rewrite firstn_length in Hlenf.
        split; [now rewrite <- Hp | split; lia]. }
      destruct children as [| c cs].
      * (* accepts-only forest *)
        inversion HB; subst f.
        apply in_map_iff in Hint.
        destruct Hint as [a [Heqt HaIn]]. subst t.
        eapply HacceptLeaf; [exact HaIn | exact Hin].
      * (* interior remainder ++ accepts *)
        inversion HB; subst f.
        destruct Hint as [Heqt | Hint'].
        -- (* the interior continuation *)
           subst t.
           rewrite leaf_entries_interior in Hin.
           apply in_flat_map in Hin.
           destruct Hin as [t' [Hint' Hin']].
           assert (Hres : path = firstn d (m_items m)
                          /\ S depth <= d /\ d <= length (m_items m)).
           { eapply (proj2 IH (S depth) parts (c :: cs) (pfx ++ [edge]) EF);
               [| | exact Hint' | exact Hin'].
             - intros it part m' HinP HinM.
               destruct (Hinv0 _ _ _ HinP HinM) as [HinMs Hnth].
               rewrite (firstn_S_nth_error _ _ _ Hnth).
               rewrite (Hpfx _ HinMs).
               now rewrite <- app_assoc.
             - rewrite length_app. cbn [length]. lia. }
           destruct Hres as [Hpath [Hd1 Hd2]].
           split; [exact Hpath | split; [lia | exact Hd2]].
        -- (* an accept sibling *)
           apply in_map_iff in Hint'.
           destruct Hint' as [a [Heqt HaIn]]. subst t.
           eapply HacceptLeaf; [exact HaIn | exact Hin].
  - (* forest, S fuel *)
    intros ps f pfx HB Hps Hlen t Hint m d path Hin.
    destruct ps as [| [it0 part0] rest].
    + rewrite build_forest_a_eq_nil in HB.
      inversion HB; subst f. cbn in Hint. contradiction.
    + rewrite build_forest_a_eq_cons in HB.
      destruct (build_node_a fuel depth it0 part0) as [f1 |] eqn:EN;
        [| discriminate].
      destruct (build_forest_a fuel depth rest) as [f2 |] eqn:EF;
        [| discriminate].
      inversion HB; subst f.
      apply in_app_or in Hint.
      destruct Hint as [Hin1 | Hin2].
      * eapply (proj1 IH depth it0 part0 f1 pfx EN);
          [| exact Hlen | exact Hin1 | exact Hin].
        intros m' HinM. eapply Hps; [left; reflexivity | exact HinM].
      * eapply (proj2 IH depth rest f2 pfx EF);
          [| exact Hlen | exact Hin2 | exact Hin].
        intros it part m' HinP HinM.
        eapply Hps; [right; exact HinP | exact HinM].
Qed.

Theorem forest_path_items_prefix_law :
  forall fuel depth edge ms f pfx,
    build_node_a fuel depth edge ms = Some f ->
    (forall m, In m ms -> firstn depth (m_items m) = pfx ++ [edge]) ->
    S (length pfx) = depth ->
    forall t, In t f ->
    forall m d path, In (m, d, path) (leaf_entries pfx t) ->
      path = firstn d (m_items m)
      /\ depth <= d
      /\ d <= length (m_items m).
Proof.
  intro fuel. exact (proj1 (build_a_paths fuel)).
Qed.

(* Root instantiation: a group forest is built at depth 1 with pfx = [] and
   edge = the group's shared first post-trigger item. *)
Theorem root_forest_path_items :
  forall fuel edge ms f,
    build_node_a fuel 1 edge ms = Some f ->
    (forall m, In m ms -> firstn 1 (m_items m) = [edge]) ->
    forall t, In t f ->
    forall m d path, In (m, d, path) (leaf_entries [] t) ->
      path = firstn d (m_items m) /\ 1 <= d /\ d <= length (m_items m).
Proof.
  intros fuel edge ms f H Hfirst t Hint m d path Hin.
  eapply (forest_path_items_prefix_law fuel 1 edge ms f [] H);
    [| reflexivity | exact Hint | exact Hin].
  intros m' Hm'. apply Hfirst. exact Hm'.
Qed.

(* The accept sharpening: a leaf whose depth reaches the member's item count
   spells the member's FULL sequence — its leaf edge is its LAST item. *)
Theorem accept_path_full_items :
  forall (m : member) (d : nat) (path : list item),
    path = firstn d (m_items m) ->
    length (m_items m) <= d ->
    path = m_items m.
Proof.
  intros m d path Hpath Hd.
  subst path. apply firstn_all2. exact Hd.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   THEOREM (c′) — BUCKET PARTITION with InteriorAccept ABSORPTION (INV-8
   over the accept-enabled model). `excl` abstracts the member-level
   exclusion reasons (A2 CastMachinery / EmptySequence, routed BEFORE the
   root partition, factoring.rs @757-779); unlike the F0 `bucket_step`,
   EVERY buildable ≥2-part becomes a GROUP — `IneligibleReason::
   InteriorAccept` is unreachable in this stance (@815-826).
   ═══════════════════════════════════════════════════════════════════════ *)

Definition bucket_step_a (fuel : nat)
  (st : list (list nat) * list nat * list (list nat))
  (p : item * list member)
  : list (list nat) * list nat * list (list nat) :=
  match st with
  | (gs, ss, is_) =>
      match p with
      | (it, part) =>
          match part with
          | [lone] => (gs, ss ++ [m_rule lone], is_)
          | _ =>
              match build_node_a fuel 1 it part with
              | Some f => (gs ++ [forest_leaf_rules f], ss, is_)
              | None => (gs, ss, is_ ++ [map m_rule part])
              end
          end
      end
  end.

Definition bucket_partition_a (excl : member -> bool) (fuel : nat)
  (bucket : list member)
  : list (list nat) * list nat * list (list nat) :=
  match partition_left_m 0 (filter (fun m => negb (excl m)) bucket) [] [] with
  | (parts, _) =>
      fold_left (bucket_step_a fuel) parts
        ([], map m_rule (filter excl bucket), [])
  end.

Lemma bucket_fold_a_cnt :
  forall fuel parts gs0 ss0 is0 gs1 ss1 is1 r,
    fold_left (bucket_step_a fuel) parts (gs0, ss0, is0) = (gs1, ss1, is1) ->
    cnt (concat gs1) r + cnt ss1 r + cnt (concat is1) r
    = cnt (concat gs0) r + cnt ss0 r + cnt (concat is0) r
      + cnt (parts_rules parts) r.
Proof.
  intros fuel parts.
  induction parts as [| [it part] rest IHp];
    intros gs0 ss0 is0 gs1 ss1 is1 r H.
  - cbn [fold_left] in H.
    inversion H; subst.
    rewrite parts_rules_nil, cnt_nil. lia.
  - destruct part as [| lone [| m1 lrest1]];
      cbn [fold_left bucket_step_a] in H.
    + (* empty part (cannot arise from add_to_parts; handled uniformly) *)
      destruct (build_node_a fuel 1 it []) as [f |] eqn:EN.
      * apply IHp with (r := r) in H.
        pose proof (proj1 (build_a_cnt fuel) 1 it [] f r EN) as HN.
        rewrite rules_of_nil, cnt_nil in HN.
        rewrite H, concat_snoc_cnt.
        rewrite parts_rules_cons. cbn [map].
        rewrite count_occ_app, cnt_nil. lia.
      * apply IHp with (r := r) in H.
        rewrite H, concat_snoc_cnt.
        rewrite parts_rules_cons. cbn [map].
        rewrite count_occ_app, !cnt_nil. lia.
    + (* singleton part -> singletons *)
      apply IHp with (r := r) in H.
      rewrite H, parts_rules_cons, map_rule_one, !count_occ_app. lia.
    + (* >= 2 part -> a GROUP whenever the build returns (absorption) *)
      destruct (build_node_a fuel 1 it (lone :: m1 :: lrest1)) as [f |] eqn:EN.
      * apply IHp with (r := r) in H.
        pose proof (proj1 (build_a_cnt fuel) 1 it (lone :: m1 :: lrest1)
                      f r EN) as HN.
        rewrite H, concat_snoc_cnt.
        rewrite parts_rules_cons, count_occ_app.
        unfold rules_of in HN. lia.
      * apply IHp with (r := r) in H.
        rewrite H, concat_snoc_cnt.
        rewrite parts_rules_cons, count_occ_app. lia.
Qed.

Theorem bucket_partition_a_cover :
  forall excl fuel bucket gs ss is_,
    (forall m, In m bucket -> excl m = false -> m_items m <> []) ->
    bucket_partition_a excl fuel bucket = (gs, ss, is_) ->
    Permutation (concat gs ++ ss ++ concat is_) (rules_of bucket).
Proof.
  intros excl fuel bucket gs ss is_ Hne H.
  unfold bucket_partition_a in H.
  destruct (partition_left_m 0 (filter (fun m => negb (excl m)) bucket) [] [])
    as [parts maccs0] eqn:EPm.
  apply (Permutation_count_occ Nat.eq_dec).
  intro r.
  rewrite !count_occ_app.
  pose proof (bucket_fold_a_cnt fuel parts
                [] (map m_rule (filter excl bucket)) []
                gs ss is_ r H) as HF.
  cbn [concat] in HF.
  rewrite !cnt_nil in HF.
  assert (Hacc : maccs0 = []).
  { eapply partition_left_m_no_accepts_at_0; [| exact EPm].
    intros m Hin.
    apply filter_In in Hin.
    destruct Hin as [HinB Hex].
    apply Hne; [exact HinB |].
    destruct (excl m); [discriminate | reflexivity]. }
  subst maccs0.
  pose proof (partition_left_m_bridge _ _ _ _ _ _ EPm) as EB.
  cbn [map] in EB.
  pose proof (partition_left_cnt 0
                (filter (fun m => negb (excl m)) bucket)
                [] [] parts [] r EB) as HP.
  rewrite parts_rules_nil, !cnt_nil in HP.
  pose proof (filter_split_cnt excl bucket r) as HS.
  unfold rules_of in *. lia.
Qed.

Theorem bucket_partition_a_disjoint :
  forall excl fuel bucket gs ss is_,
    (forall m, In m bucket -> excl m = false -> m_items m <> []) ->
    bucket_partition_a excl fuel bucket = (gs, ss, is_) ->
    NoDup (rules_of bucket) ->
    NoDup (concat gs ++ ss ++ concat is_).
Proof.
  intros excl fuel bucket gs ss is_ Hne H HND.
  eapply Permutation_NoDup;
    [apply Permutation_sym; eapply bucket_partition_a_cover; eauto
    | exact HND].
Qed.

(* INV-8's count formula: Σ group leaves + |singletons| + Σ ineligible
   members = cohort size (grammar_generality_prop.rs INV-8; the ON-branch
   census follows the const). *)
Theorem bucket_partition_a_inv8_count :
  forall excl fuel bucket gs ss is_,
    (forall m, In m bucket -> excl m = false -> m_items m <> []) ->
    bucket_partition_a excl fuel bucket = (gs, ss, is_) ->
    length (concat gs) + length ss + length (concat is_) = length bucket.
Proof.
  intros excl fuel bucket gs ss is_ Hne H.
  pose proof (bucket_partition_a_cover excl fuel bucket gs ss is_ Hne H)
    as HP.
  apply Permutation_length in HP.
  rewrite !length_app in HP.
  unfold rules_of in HP. rewrite length_map in HP.
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   THEOREM (d′) — ACCEPT COMMIT COORDINATES: the accept is the member's OWN
   completion machinery (finalize_leaf applied VERBATIM at exhaustion —
   never a commit+Pop composite, plan §9-FS3).
   ═══════════════════════════════════════════════════════════════════════ *)

(* A TRUE binder accept (untruncated, total == leaf_depth) resumes at
   positions.len() + 1 — the member's EXISTING final-pos Pop → fire arm
   (binder.rs final-pos convention) — with NO member-side remainder. *)
Theorem true_accept_binder_commit :
  forall m d,
    m_kind m = KBinder ->
    m_trunc m = false ->
    m_total m = d ->
    finalize_commit m d = CBinder (m_rule m) (S (m_total m))
    /\ has_remainder m d = false.
Proof.
  intros m d Hk Ht He.
  split.
  - unfold finalize_commit. rewrite Hk. now rewrite He.
  - unfold has_remainder. rewrite Ht. cbn [orb].
    apply Nat.ltb_ge. lia.
Qed.

(* A nullary accept is always TAIL-COMPLETE: its items are exactly its
   trailing literals, so exhaustion means sub_pos = parts_len — the
   tail-complete pop-and-fire arm (no mid-tail nullary accept can exist). *)
Theorem true_accept_nullary_commit :
  forall m d,
    m_kind m = KNullary ->
    m_trunc m = false ->
    m_total m = d ->
    finalize_commit m d = CNullary (m_rule m) 0 (m_total m)
    /\ has_remainder m d = false.
Proof.
  intros m d Hk Ht He.
  split.
  - unfold finalize_commit. rewrite Hk. now rewrite He.
  - unfold has_remainder. rewrite Ht. cbn [orb].
    apply Nat.ltb_ge. lia.
Qed.

(* A truncated accept (collection tail) keeps its member-side remainder —
   the rule-20 has_post_spine_remainder precedent. *)
Theorem truncated_accept_remainder :
  forall m d, m_trunc m = true -> has_remainder m d = true.
Proof.
  intros m d Ht. unfold has_remainder. now rewrite Ht.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   THEOREM (e′) — THE WEAKENED CHILD-ITEM INVARIANT (red-team F-10
   restatement): per node, at most one INTERIOR child per item; accept
   leaves share their edge item with the continuation subtree when one
   exists; no interior node is ever childless.
   ═══════════════════════════════════════════════════════════════════════ *)

Definition titem (t : tree) : item :=
  match t with
  | TLeaf e _ _ => e
  | TInterior e _ => e
  end.

Definition interior_items (ts : list tree) : list item :=
  flat_map (fun t => match t with
                     | TInterior e _ => [e]
                     | TLeaf _ _ _ => []
                     end) ts.

Lemma interior_items_nil : interior_items [] = [].
Proof. reflexivity. Qed.

Lemma interior_items_cons_interior :
  forall e cs rest,
    interior_items (TInterior e cs :: rest) = e :: interior_items rest.
Proof. reflexivity. Qed.

Lemma interior_items_app :
  forall a b,
    interior_items (a ++ b) = interior_items a ++ interior_items b.
Proof.
  intros a b.
  induction a as [| t rest IH]; simpl.
  - reflexivity.
  - unfold interior_items in *. simpl. rewrite IH. now rewrite app_assoc.
Qed.

Lemma interior_items_map_leaf :
  forall e d accs,
    interior_items (map (fun m => TLeaf e m d) accs) = [].
Proof.
  intros e d accs.
  induction accs as [| a rest IH]; simpl; [reflexivity | exact IH].
Qed.

(* The forest well-formedness predicate: every interior node is NONEMPTY
   (F-10: never `Interior{children: []}`) and its children carry at most one
   INTERIOR child per item (leaf children may repeat an item). *)
Inductive wf_forest_tree : tree -> Prop :=
| WfLeafT : forall e m d, wf_forest_tree (TLeaf e m d)
| WfInteriorT : forall e cs,
    cs <> [] ->
    NoDup (interior_items cs) ->
    Forall wf_forest_tree cs ->
    wf_forest_tree (TInterior e cs).

Lemma forall_map_leaf_wf :
  forall e d accs, Forall wf_forest_tree (map (fun m => TLeaf e m d) accs).
Proof.
  intros e d accs.
  induction accs as [| a rest IH]; simpl; constructor;
    [apply WfLeafT | exact IH].
Qed.

Lemma titem_map_leaf :
  forall e d accs t,
    In t (map (fun m => TLeaf e m d) accs) -> titem t = e.
Proof.
  intros e d accs t Hin.
  apply in_map_iff in Hin.
  destruct Hin as [a [Heq _]]. subst t. reflexivity.
Qed.

(* The simultaneous well-formedness theorem: (i) every tree of a node's
   forest carries the node's EDGE item (the sharing law); (ii) the forest
   holds at most ONE interior tree, labeled by that edge; (iii) every tree
   is wf. The forest half additionally tracks that interior labels inject
   into the (NoDup) partition keys. *)
Lemma build_a_wf :
  forall fuel,
    (forall depth edge ms f,
        build_node_a fuel depth edge ms = Some f ->
        (forall t, In t f -> titem t = edge)
        /\ (interior_items f = [] \/ interior_items f = [edge])
        /\ Forall wf_forest_tree f)
    /\
    (forall depth ps f,
        build_forest_a fuel depth ps = Some f ->
        NoDup (map fst ps) ->
        incl (interior_items f) (map fst ps)
        /\ NoDup (interior_items f)
        /\ Forall wf_forest_tree f).
Proof.
  induction fuel as [| fuel IH]; split; intros depth.
  - intros edge ms f H. discriminate.
  - intros ps f H HND. discriminate.
  - (* node, S fuel *)
    intros edge ms f H.
    destruct ms as [| m0 [| m1 ms1]].
    + (* [] *)
      rewrite build_node_a_eq_nil in H.
      destruct fuel as [| fuel']; [cbn in H; discriminate |].
      rewrite build_forest_a_eq_nil in H.
      cbn in H. inversion H; subst f.
      split; [| split].
      * intros t Hin. cbn in Hin. contradiction.
      * left. reflexivity.
      * constructor.
    + (* singleton *)
      rewrite build_node_a_eq_one in H.
      inversion H; subst f.
      split; [| split].
      * intros t Hin. destruct Hin as [Heq | []]. subst t. reflexivity.
      * left. reflexivity.
      * constructor; [apply WfLeafT | constructor].
    + (* >= 2 *)
      rewrite build_node_a_eq_ge2 in H.
      destruct (partition_left_m depth (m0 :: m1 :: ms1) [] [])
        as [parts accs] eqn:EPm.
      destruct (build_forest_a fuel (S depth) parts) as [children |] eqn:EF;
        [| discriminate].
      pose proof (partition_left_m_bridge _ _ _ _ _ _ EPm) as EB.
      cbn [map] in EB.
      assert (HNDparts : NoDup (map fst parts)).
      { eapply divergence_nodup_keys; [exact EB | constructor]. }
      pose proof (proj2 IH (S depth) parts children EF HNDparts)
        as [HinclC [HNDC HWFC]].
      destruct children as [| c cs].
      * (* accepts-only forest *)
        inversion H; subst f.
        split; [| split].
        -- intros t Hin. eapply titem_map_leaf. exact Hin.
        -- left. apply interior_items_map_leaf.
        -- apply forall_map_leaf_wf.
      * (* interior remainder ++ accepts *)
        inversion H; subst f.
        split; [| split].
        -- intros t Hin.
           destruct Hin as [Heq | Hin'].
           ++ subst t. reflexivity.
           ++ eapply titem_map_leaf. exact Hin'.
        -- right.
           rewrite interior_items_cons_interior, interior_items_map_leaf.
           reflexivity.
        -- constructor.
           ++ apply WfInteriorT; [discriminate | exact HNDC | exact HWFC].
           ++ apply forall_map_leaf_wf.
  - (* forest, S fuel *)
    intros ps f H HND.
    destruct ps as [| [it0 part0] rest].
    + rewrite build_forest_a_eq_nil in H.
      inversion H; subst f.
      split; [| split].
      * intros x Hx. cbn in Hx. contradiction.
      * constructor.
      * constructor.
    + rewrite build_forest_a_eq_cons in H.
      destruct (build_node_a fuel depth it0 part0) as [f1 |] eqn:EN;
        [| discriminate].
      destruct (build_forest_a fuel depth rest) as [f2 |] eqn:EF;
        [| discriminate].
      inversion H; subst f.
      cbn [map fst] in HND.
      inversion HND as [| x l Hnotin HNDrest]; subst.
      pose proof (proj1 IH depth it0 part0 f1 EN) as [_ [Hint1 HWF1]].
      pose proof (proj2 IH depth rest f2 EF HNDrest)
        as [Hincl2 [HND2 HWF2]].
      rewrite interior_items_app.
      split; [| split].
      * intros x Hx.
        apply in_app_or in Hx.
        destruct Hx as [Hx1 | Hx2].
        -- destruct Hint1 as [He | He]; rewrite He in Hx1.
           ++ contradiction.
           ++ destruct Hx1 as [Heq | []]. subst x. left. reflexivity.
        -- right. apply Hincl2. exact Hx2.
      * destruct Hint1 as [He | He]; rewrite He.
        -- cbn [app]. exact HND2.
        -- cbn [app]. constructor.
           ++ intro Habs. apply Hnotin. apply Hincl2. exact Habs.
           ++ exact HND2.
      * apply Forall_app. split; [exact HWF1 | exact HWF2].
Qed.

(* (e′) part 1 — THE SHARING LAW: every tree of a node's forest carries the
   node's edge item; in particular an accept leaf's item EQUALS its interior
   sibling's (the continuation subtree) when one exists. *)
Theorem forest_items_uniform :
  forall fuel depth edge ms f,
    build_node_a fuel depth edge ms = Some f ->
    forall t, In t f -> titem t = edge.
Proof.
  intros fuel depth edge ms f H.
  exact (proj1 (proj1 (build_a_wf fuel) depth edge ms f H)).
Qed.

Theorem accepts_share_edge_with_continuation :
  forall fuel depth edge ms f t t',
    build_node_a fuel depth edge ms = Some f ->
    In t f -> In t' f ->
    titem t = titem t'.
Proof.
  intros fuel depth edge ms f t t' H Hin Hin'.
  rewrite (forest_items_uniform _ _ _ _ _ H t Hin).
  rewrite (forest_items_uniform _ _ _ _ _ H t' Hin').
  reflexivity.
Qed.

(* (e′) part 2 — AT MOST ONE INTERIOR PER ITEM: at the forest roots (at most
   one interior, edge-labeled) and, through wf, at every node's children. *)
Theorem at_most_one_interior_root :
  forall fuel depth edge ms f,
    build_node_a fuel depth edge ms = Some f ->
    interior_items f = [] \/ interior_items f = [edge].
Proof.
  intros fuel depth edge ms f H.
  exact (proj1 (proj2 (proj1 (build_a_wf fuel) depth edge ms f H))).
Qed.

Theorem built_forest_wf :
  forall fuel depth edge ms f,
    build_node_a fuel depth edge ms = Some f ->
    Forall wf_forest_tree f.
Proof.
  intros fuel depth edge ms f H.
  exact (proj2 (proj2 (proj1 (build_a_wf fuel) depth edge ms f H))).
Qed.

Theorem wf_interior_children_nodup :
  forall e cs, wf_forest_tree (TInterior e cs) -> NoDup (interior_items cs).
Proof.
  intros e cs H. inversion H. assumption.
Qed.

(* (e′) part 3 — F-10: no interior node in a built forest is ever childless
   (all-twins parts return accepts-only forests instead). *)
Theorem wf_no_empty_interior :
  forall e cs, wf_forest_tree (TInterior e cs) -> cs <> [].
Proof.
  intros e cs H. inversion H. assumption.
Qed.

(* The generic all-twins law: a ≥2-member part whose members ALL exhaust at
   the node returns EXACTLY the accepts-only forest, in member order. *)
Theorem all_exhausted_accepts_only :
  forall fuel depth edge m0 m1 ms1,
    (forall m, In m (m0 :: m1 :: ms1) ->
       nth_error (m_items m) depth = None) ->
    build_node_a (S (S fuel)) depth edge (m0 :: m1 :: ms1)
    = Some (map (fun m => TLeaf edge m depth) (m0 :: m1 :: ms1)).
Proof.
  intros fuel depth edge m0 m1 ms1 Hall.
  rewrite build_node_a_eq_ge2.
  rewrite (partition_left_m_all_none depth (m0 :: m1 :: ms1) [] [] Hall).
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   INSTANCE PIN — the rholang InputBind@ cohort (the ONLY interior-accept
   cohort in all 22 bundled engines; F5-1 plan §1, census red-team
   confirmed; member indices per the committed P1 re-pin: QuotedQuery = 2,
   Quoted = 3 = THE ACCEPT, QuotedPersistent = 6).
   Item codes: 0 = P(Proc,0) · 1 = L"<-" · 2 = P(Name,0) · 3 = L"!" ·
   4 = L"?" · 5 = L"(" · 6 = L"<=".
   InputBindQuotedQuery  (r2): pat <- n ! ? ( ⟨args CUT⟩ — 6 items,
     TRUNCATED at its `args.*sep(",")` collection (8 total positions);
   InputBindQuoted       (r3): pat <- n — 3 items, UNTRUNCATED, total 3 —
     the PROPER PREFIX of r2, exhausting at depth 3 (the TRUE accept);
   InputBindQuotedPersistent (r6): pat <= n — 3 items.
   ═══════════════════════════════════════════════════════════════════════ *)

Definition ib_query : member := MkMember 2 KBinder [0;1;2;3;4;5] 8 true.
Definition ib_quoted : member := MkMember 3 KBinder [0;1;2] 3 false.
Definition ib_persistent : member := MkMember 6 KBinder [0;6;2] 3 false.

(* The committed trie pin (factoring.rs test
   `rholang_inputbind_at_cohort_factors_with_accept_continue`):
     P(0,0)[L(<-)[P(Name,0)[L(!)=>r2] P(Name,0)=>r3] L(<=)=>r6]
   — single-root; the P(Name) node lists the interior continuation BEFORE
   the r3 accept leaf (★A1), both carrying the SAME P(Name) edge item. *)
Definition ib_forest : list tree :=
  [TInterior 0
     [TInterior 1
        [TInterior 2 [TLeaf 3 ib_query 4];
         TLeaf 2 ib_quoted 3];
      TLeaf 6 ib_persistent 2]].

Theorem rholang_inputbind_forest :
  build_node_a 32 1 0 [ib_query; ib_quoted; ib_persistent] = Some ib_forest.
Proof. vm_compute. reflexivity. Qed.

(* Leaves ↔ members incl. the accept; leaf order = the ★A1 normative order
   (remainder-first puts r2 before the r3 accept at the P(Name) node). *)
Theorem rholang_inputbind_leaves :
  forest_leaf_rules ib_forest = [2; 3; 6].
Proof. vm_compute. reflexivity. Qed.

(* The A4 commit coordinates, exactly the committed test pins: r3 the TRUE
   accept (resume 4 = its final-pos Pop arm, NO remainder), r6 the ordinary
   earliest-uniqueness leaf (resume 3, member-side `n` remainder), r2 the
   truncated continuation (resume 5, collection-tail remainder). *)
Theorem rholang_inputbind_commits :
  finalize_commit ib_quoted 3 = CBinder 3 4
  /\ has_remainder ib_quoted 3 = false
  /\ finalize_commit ib_persistent 2 = CBinder 6 3
  /\ has_remainder ib_persistent 2 = true
  /\ finalize_commit ib_query 4 = CBinder 2 5
  /\ has_remainder ib_query 4 = true.
Proof. vm_compute. repeat split. Qed.

(* r3 satisfies the (d′) TRUE-accept law: untruncated, total == leaf depth,
   resume_pos = total + 1 = the member's own final-pos Pop arm. *)
Theorem rholang_inputbind_true_accept :
  finalize_commit ib_quoted 3 = CBinder (m_rule ib_quoted)
                                        (S (m_total ib_quoted))
  /\ has_remainder ib_quoted 3 = false.
Proof.
  apply true_accept_binder_commit; reflexivity.
Qed.

(* Every leaf path spells its member's own item prefix; the r3 accept's path
   IS its full sequence (leaf edge = its last item, P(Name)). *)
Theorem rholang_inputbind_paths :
  flat_map (leaf_entries []) ib_forest
  = [(ib_query, 4, [0;1;2;3]);
     (ib_quoted, 3, [0;1;2]);
     (ib_persistent, 2, [0;6])].
Proof. vm_compute. reflexivity. Qed.

Theorem rholang_inputbind_accept_path_is_full_items :
  firstn 3 (m_items ib_quoted) = m_items ib_quoted.
Proof. vm_compute. reflexivity. Qed.

(* The (e′) sharing pin at the P(Name) node: both children carry item 2 =
   P(Name,0) — the accept SHARES its edge item with the continuation
   subtree — with exactly ONE interior among them. *)
Theorem rholang_inputbind_accept_shares_edge :
  map titem [TInterior 2 [TLeaf 3 ib_query 4]; TLeaf 2 ib_quoted 3]
  = [2; 2]
  /\ interior_items [TInterior 2 [TLeaf 3 ib_query 4]; TLeaf 2 ib_quoted 3]
     = [2].
Proof. vm_compute. split; reflexivity. Qed.

Theorem rholang_inputbind_wf :
  Forall wf_forest_tree ib_forest.
Proof.
  exact (built_forest_wf 32 1 0 [ib_query; ib_quoted; ib_persistent]
           ib_forest rholang_inputbind_forest).
Qed.

(* The (c′) ABSORPTION receipt pair — the SAME bucket under both stances:
   F0 defers the whole part as InteriorAccept-ineligible ([[2;3;6]] in the
   ineligible slot); F5-1 absorbs it as ONE group ([[2;3;6]] in the groups
   slot) — `ineligible 1→0, groups 0→1`, cohort formula 3 = 3 both ways. *)
Theorem rholang_inputbind_bucket_accept_stance :
  bucket_partition_a (fun _ => false) 32
    [ib_query; ib_quoted; ib_persistent]
  = ([[2; 3; 6]], [], []).
Proof. vm_compute. reflexivity. Qed.

Theorem rholang_inputbind_bucket_f0_stance :
  bucket_partition (fun _ => false) 32
    [ib_query; ib_quoted; ib_persistent]
  = ([], [], [[2; 3; 6]]).
Proof. vm_compute. reflexivity. Qed.

(* ── Synthetic witnesses (the committed factoring.rs test shapes) ── *)

(* All-twins: BOTH members exhaust at the node — the accepts-only forest,
   never an empty interior (F-10), at the node itself and spliced. *)
Definition twin_a : member := MkMember 7 KBinder [0;1] 2 false.
Definition twin_b : member := MkMember 8 KBinder [0;1] 2 false.

Theorem all_twins_accepts_only_witness :
  build_node_a 32 2 1 [twin_a; twin_b]
  = Some [TLeaf 1 twin_a 2; TLeaf 1 twin_b 2].
Proof. vm_compute. reflexivity. Qed.

Theorem all_twins_spliced_witness :
  build_node_a 32 1 0 [twin_a; twin_b]
  = Some [TInterior 0 [TLeaf 1 twin_a 2; TLeaf 1 twin_b 2]].
Proof. vm_compute. reflexivity. Qed.

(* Root accept: a member whose WHOLE item list is the root edge produces a
   MULTI-ROOT forest — the pre-root arm itself becomes the accept fork —
   in the ★A1 order (interior remainder first, the accept root last). *)
Definition root_accept_m : member := MkMember 9 KBinder [0] 1 false.
Definition root_long_m : member := MkMember 10 KBinder [0;5] 2 false.

Theorem root_accept_multi_root_witness :
  build_node_a 32 1 0 [root_long_m; root_accept_m]
  = Some [TInterior 0 [TLeaf 5 root_long_m 2]; TLeaf 0 root_accept_m 1].
Proof. vm_compute. reflexivity. Qed.

(* ── Assumption audit — every line must print "Closed under the global
      context". ── *)
Print Assumptions partition_left_m_bridge.
Print Assumptions partition_left_m_accepts_iff.
Print Assumptions partition_left_m_all_none.
Print Assumptions forest_leaf_bijection.
Print Assumptions forest_leaf_rules_nodup.
Print Assumptions forest_leaf_count.
Print Assumptions build_a_nonempty.
Print Assumptions accept_absorption.
Print Assumptions forest_path_items_prefix_law.
Print Assumptions root_forest_path_items.
Print Assumptions accept_path_full_items.
Print Assumptions bucket_partition_a_cover.
Print Assumptions bucket_partition_a_disjoint.
Print Assumptions bucket_partition_a_inv8_count.
Print Assumptions true_accept_binder_commit.
Print Assumptions true_accept_nullary_commit.
Print Assumptions truncated_accept_remainder.
Print Assumptions forest_items_uniform.
Print Assumptions accepts_share_edge_with_continuation.
Print Assumptions at_most_one_interior_root.
Print Assumptions built_forest_wf.
Print Assumptions wf_interior_children_nodup.
Print Assumptions wf_no_empty_interior.
Print Assumptions all_exhausted_accepts_only.
Print Assumptions rholang_inputbind_forest.
Print Assumptions rholang_inputbind_leaves.
Print Assumptions rholang_inputbind_commits.
Print Assumptions rholang_inputbind_true_accept.
Print Assumptions rholang_inputbind_paths.
Print Assumptions rholang_inputbind_accept_path_is_full_items.
Print Assumptions rholang_inputbind_accept_shares_edge.
Print Assumptions rholang_inputbind_wf.
Print Assumptions rholang_inputbind_bucket_accept_stance.
Print Assumptions rholang_inputbind_bucket_f0_stance.
Print Assumptions all_twins_accepts_only_witness.
Print Assumptions all_twins_spliced_witness.
Print Assumptions root_accept_multi_root_witness.
