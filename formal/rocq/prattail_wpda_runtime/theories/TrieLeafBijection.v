(*
 * TrieLeafBijection: S1-FACTORING FV-1 (codegen-level, arm-free) — the
 * factored-spine trie is a LOSSLESS re-arrangement of its bucket members:
 * (a) leaves biject with members (each leaf carries exactly one member; the
 *     leaf-rule multiset + interior accepts is a permutation of the input),
 * (b) every root-to-leaf edge path spells EXACTLY the member's own
 *     post-trigger item prefix of length leaf_depth,
 * (c) the bucket-level partition (excluded singletons + lone-root-child
 *     singletons + eligible groups + ineligible groups) covers the original
 *     rule set as a permutation, disjointly under NoDup (INV-8's runtime
 *     check as a theorem over the model),
 * (d) the typed commit coordinates are the arithmetic identity the
 *     member-side machinery expects ("arm p consumes positions[p-1]").
 *
 * ── CROSS-REFERENCE TABLE (model definition ↔ the Rust it transcribes;
 *    macros/src/gen/runtime/wpda_codegen/factoring.rs @ HEAD ff5209ee) ──
 *
 *   `member`                    ↔ CandidateMember (@370-386): rule idx, kind
 *                                 (Binder/Nullary), the MERGEABLE item
 *                                 prefix `items`, `truncated`,
 *                                 `total_positions`
 *   `item` (nat code)           ↔ SpineItem (@140-158): the merge criterion
 *                                 is EMITTED-ACTION-SHAPE equality (Literal
 *                                 text+required_top_cat; ParamParse
 *                                 cat+cur_bp) — decidable structural
 *                                 equality, so an injective nat encoding is
 *                                 faithful
 *   `finalize_commit`,
 *   `binder_pos_at`,
 *   `nullary_sub_pos_at`,
 *   `has_remainder`             ↔ finalize_leaf (@516-551) + MemberCommit
 *                                 (@173-184) + SpinePosMap (@187-200):
 *                                 Binder resume_pos = leaf_depth + 1,
 *                                 Nullary sub_pos = leaf_depth, identity
 *                                 pos maps, remainder = truncated ||
 *                                 total_positions > leaf_depth
 *   `partition_left`,
 *   `add_to_parts`              ↔ build_tree's order/parts accumulation
 *                                 (@574-596): first-occurrence-order
 *                                 partition by items[depth]; members whose
 *                                 sequence exhausts at the node drain to
 *                                 `interior_accepts` (twins can never form
 *                                 a multi-member leaf)
 *   `build_node`/`build_forest` ↔ build_tree (@558-603), fuel-indexed (the
 *                                 Rust recursion terminates on the finite
 *                                 item lists; every theorem here is
 *                                 conditioned on the build RETURNING, so
 *                                 fuel accounting is inessential — the
 *                                 concrete instances compute at fuel 32):
 *                                 a singleton part is an
 *                                 EARLIEST-UNIQUENESS Leaf at the current
 *                                 depth (@564-573)
 *   `bucket_partition`          ↔ build_prefix_factoring (@615-770):
 *                                 member-level exclusions FIRST (A2 cast /
 *                                 EmptySequence, @651-669 — modeled by an
 *                                 abstract boolean `excl` because the cover
 *                                 argument depends only on WHERE excluded
 *                                 members are routed, not why), then the
 *                                 root partition by items[0] (@673-684),
 *                                 lone root children → singletons
 *                                 (@686-693), ≥2-member parts → groups iff
 *                                 no interior accepts (@703-713)
 *   pre-root edge convention    ↔ flatten_tree (@944-1001): node id 1
 *                                 consumes the ROOT EDGE (the group's first
 *                                 post-trigger item) — the F1 ROOT-EDGE BUG
 *                                 (arm 1 skipping the root's own item) is
 *                                 the live precedent for transcription
 *                                 drift; this model encodes the FIXED
 *                                 semantics: the path INTO a node at depth
 *                                 d has consumed exactly d items
 *                                 = firstn d (member items)
 *   commit coordinate targets   ↔ child_target_tokens (@1005-1055)
 *   emission loop               ↔ build_spine_emission_from (@1119-1343)
 *
 * The concrete INSTANCE pinned at the end is the fortranmodel DO group
 * (S1-F3.0 census, scratchpad/zz_probes/logs_s1f3/fortranmodel_census.txt):
 * members {DoLoop r2, DoAssign r3}, shared spine `( Int , Term ) =`,
 * divergence Int-vs-Real at depth 7, census render
 *   L(()[P(2,0)[L(,)[P(0,0)[L())[L(=)[P(2,0)=>r2 P(3,0)=>r3]]]]]].
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
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════
   The member model.
   ═══════════════════════════════════════════════════════════════════════ *)

Definition item : Type := nat.

Inductive member_kind : Type := KBinder | KNullary.

Record member : Type := MkMember {
  m_rule  : nat;
  m_kind  : member_kind;
  m_items : list item;
  m_total : nat;
  m_trunc : bool
}.

Inductive commit : Type :=
| CBinder  (rule_idx : nat) (resume_pos : nat)
| CNullary (rule_idx : nat) (completed_idx : nat) (sub_pos : nat).

Definition finalize_commit (m : member) (d : nat) : commit :=
  match m_kind m with
  | KBinder  => CBinder  (m_rule m) (S d)
  | KNullary => CNullary (m_rule m) 0 d
  end.

Definition binder_pos_at (k : nat) : nat := S k.
Definition nullary_sub_pos_at (k : nat) : nat := k.

Definition has_remainder (m : member) (d : nat) : bool :=
  m_trunc m || (d <? m_total m).

(* ═══════════════════════════════════════════════════════════════════════
   The trie and the builder.
   ═══════════════════════════════════════════════════════════════════════ *)

Inductive tree : Type :=
| TLeaf     (edge : item) (m : member) (leaf_depth : nat)
| TInterior (edge : item) (children : list tree).

Fixpoint leaf_rules (t : tree) : list nat :=
  match t with
  | TLeaf _ m _ => [m_rule m]
  | TInterior _ cs =>
      (fix go (ts : list tree) : list nat :=
         match ts with
         | [] => []
         | t' :: rest => leaf_rules t' ++ go rest
         end) cs
  end.

Definition forest_leaf_rules (ts : list tree) : list nat :=
  flat_map leaf_rules ts.

Lemma leaf_rules_interior :
  forall e ts, leaf_rules (TInterior e ts) = forest_leaf_rules ts.
Proof.
  intros e ts. unfold forest_leaf_rules.
  induction ts as [| t rest IH]; simpl.
  - reflexivity.
  - now rewrite <- IH.
Qed.

(* Leaf entries with the PATH into them (edge items, root edge first). *)
Fixpoint leaf_entries (pfx : list item) (t : tree)
  : list (member * nat * list item) :=
  match t with
  | TLeaf e m d => [(m, d, pfx ++ [e])]
  | TInterior e cs =>
      (fix go (ts : list tree) : list (member * nat * list item) :=
         match ts with
         | [] => []
         | t' :: rest => leaf_entries (pfx ++ [e]) t' ++ go rest
         end) cs
  end.

Lemma leaf_entries_interior :
  forall pfx e ts,
    leaf_entries pfx (TInterior e ts)
    = flat_map (leaf_entries (pfx ++ [e])) ts.
Proof.
  intros pfx e ts.
  induction ts as [| t rest IH]; simpl.
  - reflexivity.
  - now rewrite <- IH.
Qed.

(* first-occurrence-order partition by the item at `depth`. *)
Fixpoint add_to_parts (it : item) (m : member)
  (parts : list (item * list member)) : list (item * list member) :=
  match parts with
  | [] => [(it, [m])]
  | (i, ms) :: rest =>
      if Nat.eqb i it
      then (i, ms ++ [m]) :: rest
      else (i, ms) :: add_to_parts it m rest
  end.

Fixpoint partition_left (depth : nat) (ms : list member)
  (acc : list (item * list member)) (accepts : list nat)
  : list (item * list member) * list nat :=
  match ms with
  | [] => (acc, accepts)
  | m :: rest =>
      match nth_error (m_items m) depth with
      | Some it => partition_left depth rest (add_to_parts it m acc) accepts
      | None    => partition_left depth rest acc (accepts ++ [m_rule m])
      end
  end.

(* The fuel-indexed builder (both functions decrease on fuel). *)
Fixpoint build_node (fuel : nat) (depth : nat) (edge : item)
  (ms : list member) {struct fuel} : option (tree * list nat) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match ms with
      | [m] => Some (TLeaf edge m depth, [])
      | _ =>
          match partition_left depth ms [] [] with
          | (parts, accepts) =>
              match build_forest fuel' (S depth) parts with
              | None => None
              | Some (children, acc') =>
                  Some (TInterior edge children, accepts ++ acc')
              end
          end
      end
  end
with build_forest (fuel : nat) (depth : nat)
  (ps : list (item * list member)) {struct fuel}
  : option (list tree * list nat) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match ps with
      | [] => Some ([], [])
      | (it, part) :: rest =>
          match build_node fuel' depth it part with
          | None => None
          | Some (t, a1) =>
              match build_forest fuel' depth rest with
              | None => None
              | Some (ts, a2) => Some (t :: ts, a1 ++ a2)
              end
          end
      end
  end.

(* Definitional equations for the builder (reflexivity — these pin the
   fixpoint unfoldings so proofs can rewrite hypotheses reliably; the
   mutual fixpoint resists targeted cbn). *)
Lemma build_node_eq_nil :
  forall fuel depth edge,
    build_node (S fuel) depth edge []
    = match build_forest fuel (S depth) [] with
      | None => None
      | Some (children, acc') => Some (TInterior edge children, acc')
      end.
Proof. reflexivity. Qed.

Lemma build_node_eq_one :
  forall fuel depth edge m,
    build_node (S fuel) depth edge [m] = Some (TLeaf edge m depth, []).
Proof. reflexivity. Qed.

Lemma build_node_eq_ge2 :
  forall fuel depth edge m0 m1 ms1,
    build_node (S fuel) depth edge (m0 :: m1 :: ms1)
    = match partition_left depth (m0 :: m1 :: ms1) [] [] with
      | (parts, accepts) =>
          match build_forest fuel (S depth) parts with
          | None => None
          | Some (children, acc') =>
              Some (TInterior edge children, accepts ++ acc')
          end
      end.
Proof. reflexivity. Qed.

Lemma build_forest_eq_nil :
  forall fuel depth, build_forest (S fuel) depth [] = Some ([], []).
Proof. reflexivity. Qed.

Lemma build_forest_eq_cons :
  forall fuel depth it part rest,
    build_forest (S fuel) depth ((it, part) :: rest)
    = match build_node fuel depth it part with
      | None => None
      | Some (t, a1) =>
          match build_forest fuel depth rest with
          | None => None
          | Some (ts, a2) => Some (t :: ts, a1 ++ a2)
          end
      end.
Proof. reflexivity. Qed.

(* ═══════════════════════════════════════════════════════════════════════
   Rule-multiset bookkeeping (count_occ arithmetic — every permutation
   below is established through Permutation_count_occ).
   ═══════════════════════════════════════════════════════════════════════ *)

Definition rules_of (ms : list member) : list nat := map m_rule ms.
Definition parts_rules (ps : list (item * list member)) : list nat :=
  flat_map (fun p => map m_rule (snd p)) ps.

Notation cnt := (count_occ Nat.eq_dec).

(* Small closed-count facts (destructs stay confined to tiny goals; the big
   proofs below only REWRITE with these, keeping cnt atoms opaque so lia
   closes pure linear equations). *)
Lemma cnt_nil : forall r, cnt [] r = 0.
Proof. reflexivity. Qed.

Lemma cnt_cons : forall x l r, cnt (x :: l) r = cnt [x] r + cnt l r.
Proof.
  intros x l r. simpl.
  destruct (Nat.eq_dec x r); simpl; lia.
Qed.

Lemma parts_rules_nil : parts_rules [] = [].
Proof. reflexivity. Qed.

Lemma parts_rules_cons :
  forall i ms rest,
    parts_rules ((i, ms) :: rest) = map m_rule ms ++ parts_rules rest.
Proof. reflexivity. Qed.

Lemma rules_of_nil : rules_of [] = [].
Proof. reflexivity. Qed.

Lemma rules_of_cons :
  forall m rest, rules_of (m :: rest) = m_rule m :: rules_of rest.
Proof. reflexivity. Qed.

Lemma map_rule_one : forall m, map m_rule [m] = [m_rule m].
Proof. reflexivity. Qed.

Lemma add_to_parts_cnt :
  forall it m parts r,
    cnt (parts_rules (add_to_parts it m parts)) r
    = cnt (parts_rules parts) r + cnt [m_rule m] r.
Proof.
  intros it m parts r.
  induction parts as [| [i ms] rest IH].
  - cbn [add_to_parts].
    rewrite parts_rules_cons, parts_rules_nil, map_rule_one.
    rewrite count_occ_app, !cnt_nil. lia.
  - cbn [add_to_parts].
    destruct (Nat.eqb i it) eqn:E.
    + rewrite !parts_rules_cons.
      rewrite map_app, map_rule_one, !count_occ_app. lia.
    + rewrite !parts_rules_cons.
      rewrite !count_occ_app, IH. lia.
Qed.

Lemma partition_left_cnt :
  forall depth ms acc accepts parts' accepts' r,
    partition_left depth ms acc accepts = (parts', accepts') ->
    cnt (parts_rules parts') r + cnt accepts' r
    = cnt (rules_of ms) r + cnt (parts_rules acc) r + cnt accepts r.
Proof.
  intros depth ms.
  induction ms as [| m rest IH]; intros acc accepts parts' accepts' r H;
    simpl in H.
  - inversion H; subst. rewrite rules_of_nil, cnt_nil. lia.
  - destruct (nth_error (m_items m) depth) as [it |] eqn:E.
    + specialize (IH _ _ _ _ r H).
      rewrite add_to_parts_cnt in IH.
      rewrite rules_of_cons, cnt_cons. lia.
    + specialize (IH _ _ _ _ r H).
      rewrite count_occ_app in IH.
      rewrite rules_of_cons, cnt_cons. lia.
Qed.

Lemma forest_leaf_rules_nil : forest_leaf_rules [] = [].
Proof. reflexivity. Qed.

Lemma forest_leaf_rules_cons :
  forall t rest,
    forest_leaf_rules (t :: rest) = leaf_rules t ++ forest_leaf_rules rest.
Proof. reflexivity. Qed.

(* The simultaneous count theorem for the builder. *)
Lemma build_cnt :
  forall fuel,
    (forall depth edge ms t acc r,
        build_node fuel depth edge ms = Some (t, acc) ->
        cnt (leaf_rules t) r + cnt acc r = cnt (rules_of ms) r)
    /\
    (forall depth ps ts acc r,
        build_forest fuel depth ps = Some (ts, acc) ->
        cnt (forest_leaf_rules ts) r + cnt acc r = cnt (parts_rules ps) r).
Proof.
  induction fuel as [| fuel IH]; split; intros depth.
  - intros edge ms t acc r H. discriminate.
  - intros ps ts acc r H. discriminate.
  - (* node, S fuel *)
    intros edge ms t acc r H.
    destruct ms as [| m0 [| m1 ms1]].
    + (* [] *)
      rewrite build_node_eq_nil in H.
      destruct (build_forest fuel (S depth) []) as [[children acc'] |] eqn:EF;
        [| discriminate].
      inversion H; subst.
      destruct fuel; [discriminate EF |].
      rewrite build_forest_eq_nil in EF.
      inversion EF; subst.
      rewrite leaf_rules_interior, forest_leaf_rules_nil.
      rewrite rules_of_nil, !cnt_nil. lia.
    + (* singleton leaf *)
      rewrite build_node_eq_one in H.
      inversion H; subst.
      cbn [leaf_rules].
      rewrite rules_of_cons, rules_of_nil, cnt_cons, !cnt_nil. lia.
    + (* >= 2 members *)
      rewrite build_node_eq_ge2 in H.
      destruct (partition_left depth (m0 :: m1 :: ms1) [] [])
        as [parts accepts] eqn:EP.
      destruct (build_forest fuel (S depth) parts)
        as [[children acc'] |] eqn:EF; [| discriminate].
      inversion H; subst.
      rewrite leaf_rules_interior.
      pose proof (proj2 IH (S depth) _ _ _ r EF) as HF.
      pose proof (partition_left_cnt _ _ _ _ _ _ r EP) as HP.
      rewrite parts_rules_nil, !cnt_nil in HP.
      rewrite count_occ_app. lia.
  - (* forest, S fuel *)
    intros ps ts acc r H.
    destruct ps as [| [it part] rest].
    + rewrite build_forest_eq_nil in H.
      inversion H; subst.
      rewrite forest_leaf_rules_nil, parts_rules_nil, !cnt_nil. lia.
    + rewrite build_forest_eq_cons in H.
      destruct (build_node fuel depth it part) as [[t1 a1] |] eqn:EN;
        [| discriminate].
      destruct (build_forest fuel depth rest) as [[ts0 a2] |] eqn:EF;
        [| discriminate].
      inversion H; subst.
      pose proof (proj1 IH depth _ _ _ _ r EN) as HN.
      pose proof (proj2 IH depth _ _ _ r EF) as HF.
      unfold rules_of in HN.
      rewrite forest_leaf_rules_cons, parts_rules_cons.
      rewrite !count_occ_app. lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   THEOREM (a) — LEAVES ↔ MEMBERS.
   ═══════════════════════════════════════════════════════════════════════ *)

Theorem trie_leaf_bijection :
  forall fuel depth edge ms t acc,
    build_node fuel depth edge ms = Some (t, acc) ->
    Permutation (leaf_rules t ++ acc) (rules_of ms).
Proof.
  intros fuel depth edge ms t acc H.
  apply (Permutation_count_occ Nat.eq_dec).
  intro r.
  rewrite count_occ_app.
  exact (proj1 (build_cnt fuel) _ _ _ _ _ r H).
Qed.

Theorem eligible_leaves_are_members :
  forall fuel depth edge ms t,
    build_node fuel depth edge ms = Some (t, []) ->
    Permutation (leaf_rules t) (rules_of ms).
Proof.
  intros fuel depth edge ms t H.
  apply trie_leaf_bijection in H.
  now rewrite app_nil_r in H.
Qed.

Theorem eligible_leaf_rules_nodup :
  forall fuel depth edge ms t,
    build_node fuel depth edge ms = Some (t, []) ->
    NoDup (rules_of ms) ->
    NoDup (leaf_rules t).
Proof.
  intros fuel depth edge ms t H HND.
  apply eligible_leaves_are_members in H.
  eapply Permutation_NoDup; [apply Permutation_sym; exact H | exact HND].
Qed.

(* The runtime leaf-count assert (factoring.rs @726-731) as a corollary. *)
Theorem eligible_leaf_count :
  forall fuel depth edge ms t,
    build_node fuel depth edge ms = Some (t, []) ->
    length (leaf_rules t) = length ms.
Proof.
  intros fuel depth edge ms t H.
  apply eligible_leaves_are_members in H.
  apply Permutation_length in H.
  unfold rules_of in H. now rewrite length_map in H.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   THEOREM (b) — PATH-ITEMS PREFIX LAW.
   ═══════════════════════════════════════════════════════════════════════ *)

Lemma firstn_S_nth_error :
  forall (l : list item) d x,
    nth_error l d = Some x -> firstn (S d) l = firstn d l ++ [x].
Proof.
  induction l as [| a l IH]; intros d x H; destruct d; simpl in *.
  - discriminate.
  - discriminate.
  - inversion H; subst. reflexivity.
  - now rewrite (IH _ _ H).
Qed.

(* Invariant carried through the partition: every routed member satisfies Q
   and its item at `depth` is its part's key. *)
Definition parts_inv (depth : nat) (Q : member -> Prop)
  (ps : list (item * list member)) : Prop :=
  forall i p m, In (i, p) ps -> In m p ->
    Q m /\ nth_error (m_items m) depth = Some i.

Lemma parts_inv_nil : forall depth Q, parts_inv depth Q [].
Proof.
  intros depth Q i p m HIn. simpl in HIn. contradiction.
Qed.

Lemma parts_inv_tail :
  forall depth Q hd tl,
    parts_inv depth Q (hd :: tl) -> parts_inv depth Q tl.
Proof.
  intros depth Q hd tl H i p m HIn HinM.
  eapply H; [right; exact HIn | exact HinM].
Qed.

Lemma add_to_parts_inv :
  forall depth Q acc it m,
    parts_inv depth Q acc ->
    Q m ->
    nth_error (m_items m) depth = Some it ->
    parts_inv depth Q (add_to_parts it m acc).
Proof.
  intros depth Q acc.
  induction acc as [| [j js] acc1 IH]; intros it m Hinv HQ Hnth; simpl.
  - intros i p m0 HIn HinM.
    destruct HIn as [Heq | []].
    inversion Heq; subst.
    destruct HinM as [Heq2 | []]; subst.
    split; assumption.
  - destruct (Nat.eqb j it) eqn:Ej.
    + apply Nat.eqb_eq in Ej; subst j.
      intros i p m0 HIn HinM.
      destruct HIn as [Heq | HIn'].
      * inversion Heq; subst.
        apply in_app_or in HinM.
        destruct HinM as [HinJs | [Heq2 | []]].
        -- eapply Hinv; [left; reflexivity | exact HinJs].
        -- subst m0. split; assumption.
      * eapply Hinv; [right; exact HIn' | exact HinM].
    + intros i p m0 HIn HinM.
      destruct HIn as [Heq | HIn'].
      * inversion Heq; subst.
        eapply Hinv; [left; reflexivity | exact HinM].
      * eapply IH; [| exact HQ | exact Hnth | exact HIn' | exact HinM].
        eapply parts_inv_tail. exact Hinv.
Qed.

Lemma partition_left_inv :
  forall depth Q ms acc accepts parts' accepts',
    partition_left depth ms acc accepts = (parts', accepts') ->
    (forall m, In m ms -> Q m) ->
    parts_inv depth Q acc ->
    parts_inv depth Q parts'.
Proof.
  intros depth Q ms.
  induction ms as [| m rest IH]; intros acc accepts parts' accepts' H HQ Hinv;
    simpl in H.
  - inversion H; subst. exact Hinv.
  - destruct (nth_error (m_items m) depth) as [it |] eqn:E.
    + eapply IH; [exact H | |].
      * intros m' Hin. apply HQ. right. exact Hin.
      * apply add_to_parts_inv; [exact Hinv | | exact E].
        apply HQ. left. reflexivity.
    + eapply IH; [exact H | | exact Hinv].
      intros m' Hin. apply HQ. right. exact Hin.
Qed.

(* The simultaneous path theorem. *)
Lemma build_paths :
  forall fuel,
    (forall depth edge ms t acc pfx,
        build_node fuel depth edge ms = Some (t, acc) ->
        (forall m, In m ms -> firstn depth (m_items m) = pfx ++ [edge]) ->
        S (length pfx) = depth ->
        forall m d path,
          In (m, d, path) (leaf_entries pfx t) ->
          path = firstn d (m_items m)
          /\ depth <= d
          /\ d <= length (m_items m))
    /\
    (forall depth ps ts acc pfx,
        build_forest fuel depth ps = Some (ts, acc) ->
        (forall it part m, In (it, part) ps -> In m part ->
            firstn depth (m_items m) = pfx ++ [it]) ->
        S (length pfx) = depth ->
        forall t', In t' ts ->
        forall m d path,
          In (m, d, path) (leaf_entries pfx t') ->
          path = firstn d (m_items m)
          /\ depth <= d
          /\ d <= length (m_items m)).
Proof.
  induction fuel as [| fuel IH]; split; intros depth.
  - intros edge ms t acc pfx HB. discriminate.
  - intros ps ts acc pfx HB. discriminate.
  - (* node, S fuel *)
    intros edge ms t acc pfx HB Hpfx Hlen m d path Hin.
    destruct ms as [| m0 [| m1 ms1]].
    + (* [] — no leaves below *)
      rewrite build_node_eq_nil in HB.
      destruct (build_forest fuel (S depth) []) as [[children acc'] |] eqn:EF;
        [| discriminate].
      inversion HB; subst t acc.
      destruct fuel; [discriminate EF |].
      rewrite build_forest_eq_nil in EF.
      inversion EF; subst children acc'.
      rewrite leaf_entries_interior in Hin.
      cbn in Hin. contradiction.
    + (* singleton leaf at this depth *)
      rewrite build_node_eq_one in HB.
      inversion HB; subst t acc.
      cbn [leaf_entries] in Hin.
      destruct Hin as [Heq | []].
      injection Heq as Hm0 Hd Hpath.
      subst m0 path d.
      pose proof (Hpfx m (or_introl eq_refl)) as Hp.
      assert (Hlenf : length (firstn depth (m_items m)) = depth).
      { rewrite Hp. rewrite length_app. cbn [length]. lia. }
      rewrite firstn_length in Hlenf.
      split; [| split].
      * now rewrite <- Hp.
      * lia.
      * lia.
    + (* interior *)
      rewrite build_node_eq_ge2 in HB.
      destruct (partition_left depth (m0 :: m1 :: ms1) [] [])
        as [parts accepts0] eqn:EP.
      destruct (build_forest fuel (S depth) parts)
        as [[children acc'] |] eqn:EF; [| discriminate].
      inversion HB; subst t acc.
      rewrite leaf_entries_interior in Hin.
      apply in_flat_map in Hin.
      destruct Hin as [t' [Hint' Hin']].
      assert (Hinv0 : parts_inv depth
                        (fun m'' => In m'' (m0 :: m1 :: ms1)) parts).
      { eapply partition_left_inv;
          [exact EP | intros ? Hx; exact Hx | apply parts_inv_nil]. }
      assert (Hres : path = firstn d (m_items m)
                     /\ S depth <= d /\ d <= length (m_items m)).
      { eapply (proj2 IH (S depth) parts children acc' (pfx ++ [edge]) EF);
          [| | exact Hint' | exact Hin'].
        - intros it part m' HinP HinM.
          destruct (Hinv0 _ _ _ HinP HinM) as [HinMs Hnth].
          rewrite (firstn_S_nth_error _ _ _ Hnth).
          rewrite (Hpfx _ HinMs).
          now rewrite <- app_assoc.
        - rewrite length_app. cbn [length]. lia. }
      destruct Hres as [Hpath [Hd1 Hd2]].
      split; [exact Hpath | split; [lia | exact Hd2]].
  - (* forest, S fuel *)
    intros ps ts acc pfx HB Hpfx Hlen t' Hint m d path Hin.
    destruct ps as [| [it0 part0] rest].
    + rewrite build_forest_eq_nil in HB.
      inversion HB; subst ts acc. cbn in Hint. contradiction.
    + rewrite build_forest_eq_cons in HB.
      destruct (build_node fuel depth it0 part0) as [[t1 a1] |] eqn:EN;
        [| discriminate].
      destruct (build_forest fuel depth rest) as [[ts2 a2] |] eqn:EF;
        [| discriminate].
      inversion HB; subst ts acc.
      destruct Hint as [Heq | Hint'].
      * subst t1.
        eapply (proj1 IH depth it0 part0 t' a1 pfx EN);
          [| exact Hlen | exact Hin].
        intros m' HinM.
        eapply Hpfx; [left; reflexivity | exact HinM].
      * eapply (proj2 IH depth rest ts2 a2 pfx EF);
          [| exact Hlen | exact Hint' | exact Hin].
        intros it part m' HinP HinM.
        eapply Hpfx; [right; exact HinP | exact HinM].
Qed.

Theorem path_items_prefix_law :
  forall fuel depth edge ms t acc pfx,
    build_node fuel depth edge ms = Some (t, acc) ->
    (forall m, In m ms -> firstn depth (m_items m) = pfx ++ [edge]) ->
    S (length pfx) = depth ->
    forall m d path,
      In (m, d, path) (leaf_entries pfx t) ->
      path = firstn d (m_items m)
      /\ depth <= d
      /\ d <= length (m_items m).
Proof.
  intro fuel. exact (proj1 (build_paths fuel)).
Qed.

(* Root instantiation: a group is built at depth 1 with pfx = [] and
   edge = the group's shared first post-trigger item — so EVERY leaf path
   spells firstn leaf_depth of its member's items, with
   1 <= leaf_depth <= |items|. *)
Theorem root_path_items :
  forall fuel edge ms t acc,
    build_node fuel 1 edge ms = Some (t, acc) ->
    (forall m, In m ms -> firstn 1 (m_items m) = [edge]) ->
    forall m d path,
      In (m, d, path) (leaf_entries [] t) ->
      path = firstn d (m_items m) /\ 1 <= d /\ d <= length (m_items m).
Proof.
  intros fuel edge ms t acc H Hfirst m d path Hin.
  eapply (path_items_prefix_law fuel 1 edge ms t acc [] H);
    [| reflexivity | exact Hin].
  intros m' Hm'. apply Hfirst. exact Hm'.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   THEOREM (c) — BUCKET PARTITION (INV-8 over the model). `excl` abstracts
   the member-level exclusion reasons (A2 CastMachinery / EmptySequence);
   the cover holds for ANY exclusion predicate, PROVIDED excluded members
   include every empty-items member (they drain to singletons before the
   root partition, exactly like factoring.rs @651-669).
   ═══════════════════════════════════════════════════════════════════════ *)

Definition bucket_step (fuel : nat)
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
              match build_node fuel 1 it part with
              | Some (t, []) => (gs ++ [leaf_rules t], ss, is_)
              | _ => (gs, ss, is_ ++ [map m_rule part])
              end
          end
      end
  end.

Definition bucket_partition (excl : member -> bool) (fuel : nat)
  (bucket : list member)
  : list (list nat) * list nat * list (list nat) :=
  match partition_left 0 (filter (fun m => negb (excl m)) bucket) [] [] with
  | (parts, _) =>
      fold_left (bucket_step fuel) parts
        ([], map m_rule (filter excl bucket), [])
  end.

Lemma partition_left_no_accepts_at_0 :
  forall ms acc accepts parts' accepts',
    (forall m, In m ms -> m_items m <> []) ->
    partition_left 0 ms acc accepts = (parts', accepts') ->
    accepts' = accepts.
Proof.
  induction ms as [| m rest IH]; intros acc accepts parts' accepts' Hne H;
    simpl in H.
  - inversion H; subst. reflexivity.
  - destruct (m_items m) as [| x xs] eqn:E.
    + exfalso. exact (Hne m (or_introl eq_refl) E).
    + eapply IH; [| exact H].
      intros m' Hin. apply Hne. right. exact Hin.
Qed.

Lemma concat_snoc_cnt :
  forall (ls : list (list nat)) (l : list nat) r,
    cnt (concat (ls ++ [l])) r = cnt (concat ls) r + cnt l r.
Proof.
  intros ls l r.
  rewrite concat_app. cbn [concat].
  rewrite !count_occ_app, cnt_nil. lia.
Qed.

Lemma bucket_fold_cnt :
  forall fuel parts gs0 ss0 is0 gs1 ss1 is1 r,
    fold_left (bucket_step fuel) parts (gs0, ss0, is0) = (gs1, ss1, is1) ->
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
      cbn [fold_left bucket_step] in H.
    + (* empty part (cannot arise from add_to_parts; handled uniformly) *)
      destruct (build_node fuel 1 it []) as [[t [| a al]] |] eqn:EN.
      * apply IHp with (r := r) in H.
        pose proof (proj1 (build_cnt fuel) 1 it [] t [] r EN) as HN.
        rewrite rules_of_nil, !cnt_nil in HN.
        rewrite H, concat_snoc_cnt.
        rewrite parts_rules_cons. cbn [map].
        rewrite count_occ_app, cnt_nil. lia.
      * apply IHp with (r := r) in H.
        rewrite H, concat_snoc_cnt.
        rewrite parts_rules_cons. cbn [map].
        rewrite count_occ_app, !cnt_nil. lia.
      * apply IHp with (r := r) in H.
        rewrite H, concat_snoc_cnt.
        rewrite parts_rules_cons. cbn [map].
        rewrite count_occ_app, !cnt_nil. lia.
    + (* singleton part -> singletons *)
      apply IHp with (r := r) in H.
      rewrite H, parts_rules_cons, map_rule_one, !count_occ_app. lia.
    + (* >= 2 part *)
      destruct (build_node fuel 1 it (lone :: m1 :: lrest1))
        as [[t [| a al]] |] eqn:EN.
      * apply IHp with (r := r) in H.
        pose proof (proj1 (build_cnt fuel) 1 it (lone :: m1 :: lrest1)
                      t [] r EN) as HN.
        rewrite cnt_nil in HN.
        rewrite H, concat_snoc_cnt.
        rewrite parts_rules_cons, count_occ_app.
        unfold rules_of in HN. lia.
      * apply IHp with (r := r) in H.
        rewrite H, concat_snoc_cnt.
        rewrite parts_rules_cons, count_occ_app. lia.
      * apply IHp with (r := r) in H.
        rewrite H, concat_snoc_cnt.
        rewrite parts_rules_cons, count_occ_app. lia.
Qed.

Lemma filter_split_cnt :
  forall (excl : member -> bool) bucket r,
    cnt (map m_rule (filter excl bucket)) r
    + cnt (map m_rule (filter (fun m => negb (excl m)) bucket)) r
    = cnt (rules_of bucket) r.
Proof.
  intros excl bucket r.
  induction bucket as [| m rest IH]; simpl.
  - reflexivity.
  - destruct (excl m) eqn:E; simpl;
      destruct (Nat.eq_dec (m_rule m) r); simpl; lia.
Qed.

Theorem bucket_partition_cover :
  forall excl fuel bucket gs ss is_,
    (forall m, In m bucket -> excl m = false -> m_items m <> []) ->
    bucket_partition excl fuel bucket = (gs, ss, is_) ->
    Permutation (concat gs ++ ss ++ concat is_) (rules_of bucket).
Proof.
  intros excl fuel bucket gs ss is_ Hne H.
  unfold bucket_partition in H.
  destruct (partition_left 0 (filter (fun m => negb (excl m)) bucket) [] [])
    as [parts accepts0] eqn:EP.
  apply (Permutation_count_occ Nat.eq_dec).
  intro r.
  rewrite !count_occ_app.
  pose proof (bucket_fold_cnt fuel parts
                [] (map m_rule (filter excl bucket)) []
                gs ss is_ r H) as HF.
  cbn [concat] in HF.
  rewrite !cnt_nil in HF.
  pose proof (partition_left_cnt 0
                (filter (fun m => negb (excl m)) bucket)
                [] [] parts accepts0 r EP) as HP.
  rewrite parts_rules_nil, !cnt_nil in HP.
  assert (Hacc : accepts0 = []).
  { eapply partition_left_no_accepts_at_0; [| exact EP].
    intros m Hin.
    apply filter_In in Hin.
    destruct Hin as [HinB Hex].
    apply Hne; [exact HinB |].
    destruct (excl m); [discriminate | reflexivity]. }
  subst accepts0.
  rewrite cnt_nil in HP.
  pose proof (filter_split_cnt excl bucket r) as HS.
  unfold rules_of in *. lia.
Qed.

Theorem bucket_partition_disjoint :
  forall excl fuel bucket gs ss is_,
    (forall m, In m bucket -> excl m = false -> m_items m <> []) ->
    bucket_partition excl fuel bucket = (gs, ss, is_) ->
    NoDup (rules_of bucket) ->
    NoDup (concat gs ++ ss ++ concat is_).
Proof.
  intros excl fuel bucket gs ss is_ Hne H HND.
  eapply Permutation_NoDup;
    [apply Permutation_sym; eapply bucket_partition_cover; eauto | exact HND].
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   THEOREM (d) — COMMIT COORDINATES.
   ═══════════════════════════════════════════════════════════════════════ *)

Theorem binder_commit_resume :
  forall m d, m_kind m = KBinder ->
    finalize_commit m d = CBinder (m_rule m) (S d).
Proof.
  intros m d Hk. unfold finalize_commit. now rewrite Hk.
Qed.

Theorem nullary_commit_sub_pos :
  forall m d, m_kind m = KNullary ->
    finalize_commit m d = CNullary (m_rule m) 0 d.
Proof.
  intros m d Hk. unfold finalize_commit. now rewrite Hk.
Qed.

(* The identity pos maps agree with the commit coordinates at the leaf. *)
Theorem pos_map_commit_agreement :
  forall d, binder_pos_at d = S d /\ nullary_sub_pos_at d = d.
Proof.
  intro d. split; reflexivity.
Qed.

(* Nullary tail-completeness: with the discovery invariant (untruncated,
   total = item count — factoring.rs @448-468) a nullary leaf has no
   post-spine remainder iff sub_pos consumed the WHOLE literal run
   (sub_pos = leaf_depth = parts_len). *)
Theorem nullary_tail_complete :
  forall m d,
    m_kind m = KNullary ->
    m_trunc m = false ->
    m_total m = length (m_items m) ->
    d <= length (m_items m) ->
    (has_remainder m d = false <-> d = m_total m).
Proof.
  intros m d Hk Ht Htot Hd.
  unfold has_remainder. rewrite Ht. simpl.
  split.
  - intro H. apply Nat.ltb_ge in H. lia.
  - intro H. apply Nat.ltb_ge. lia.
Qed.

(* Binder remainder is byte-faithful to @549. *)
Theorem binder_remainder_shape :
  forall m d, has_remainder m d = m_trunc m || (d <? m_total m).
Proof.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   INSTANCE PIN — the fortranmodel DO group (S1-F3.0 census). Item codes:
   0 = L"(" · 1 = P(Int,0) · 2 = L"," · 3 = P(Term,0) · 4 = L")" ·
   5 = L"=" · 6 = P(Real,0).
   DoLoop  (r2): ( lbl:Int , v:Term ) = lo:Int , hi:Int — 9 items;
   DoAssign(r3): ( lbl:Int , v:Term ) = val:Real        — 7 items.
   Shared spine depth 6, divergence at index 6 (Int vs Real), leaves at
   depth 7; DoLoop resumes at member position 8 WITH remainder (`, hi`),
   DoAssign commits tail-complete.
   ═══════════════════════════════════════════════════════════════════════ *)

Definition do_loop : member :=
  MkMember 2 KBinder [0;1;2;3;4;5;1;2;1] 9 false.
Definition do_assign : member :=
  MkMember 3 KBinder [0;1;2;3;4;5;6] 7 false.

Definition do_tree : tree :=
  TInterior 0
    [TInterior 1
       [TInterior 2
          [TInterior 3
             [TInterior 4
                [TInterior 5
                   [TLeaf 1 do_loop 7; TLeaf 6 do_assign 7]]]]]].

Theorem fortranmodel_do_group_tree :
  build_node 32 1 0 [do_loop; do_assign] = Some (do_tree, []).
Proof. vm_compute. reflexivity. Qed.

Theorem fortranmodel_do_group_leaves :
  leaf_rules do_tree = [2; 3].
Proof. vm_compute. reflexivity. Qed.

Theorem fortranmodel_do_commits :
  finalize_commit do_loop 7 = CBinder 2 8
  /\ finalize_commit do_assign 7 = CBinder 3 8
  /\ has_remainder do_loop 7 = true
  /\ has_remainder do_assign 7 = false.
Proof. vm_compute. repeat split. Qed.

Theorem fortranmodel_do_paths :
  leaf_entries [] do_tree
  = [(do_loop, 7, firstn 7 (m_items do_loop));
     (do_assign, 7, firstn 7 (m_items do_assign))].
Proof. vm_compute. reflexivity. Qed.

(* ── Assumption audit — every line must print "Closed under the global
      context". ── *)
Print Assumptions trie_leaf_bijection.
Print Assumptions eligible_leaves_are_members.
Print Assumptions eligible_leaf_rules_nodup.
Print Assumptions eligible_leaf_count.
Print Assumptions path_items_prefix_law.
Print Assumptions root_path_items.
Print Assumptions bucket_partition_cover.
Print Assumptions bucket_partition_disjoint.
Print Assumptions binder_commit_resume.
Print Assumptions nullary_commit_sub_pos.
Print Assumptions pos_map_commit_agreement.
Print Assumptions nullary_tail_complete.
Print Assumptions binder_remainder_shape.
Print Assumptions fortranmodel_do_group_tree.
Print Assumptions fortranmodel_do_group_leaves.
Print Assumptions fortranmodel_do_commits.
Print Assumptions fortranmodel_do_paths.
