(*
 * NBestExtraction: the Dovetail best-first extractor's SELECTION-LAYER no-prune
 * invariant.
 *
 * Models the extractor (dovetail/src/extract.rs) at the SELECTION layer: from the
 * candidate derivations of an e-class, the output removes an alternative ONLY
 * when its composed weight is the semiring zero (0̄, modeled as `None`). This is
 * the direct formalization of the engine's governing invariant — *weight ORDERS,
 * never PRUNES; the only removal is by evidence* — and of plan Invariant 1 (no
 * dropped alternatives).
 *
 * Proven here (zero-Admitted, zero-Axiom):
 *   - select_complete / no_unrefuted_alternative_dropped : every non-0̄
 *     alternative SURVIVES (no-miss at the selection layer).
 *   - select_sound / select_only_removes_zero : the ONLY removal is the
 *     semiring zero.
 *   - equal_weight_both_survive : equal-weight DISTINCT alternatives BOTH
 *     survive (no weight-merge) — mirrors parser_preserves_ambiguous_alternatives.
 *   - select_prefix_monotone : a longer demand prefix never drops what a shorter
 *     one surfaced (resumability of the lazy stream).
 *   - select_exhausts_on_demand : every non-0̄ alternative appears at some demand
 *     k (exhaustive-on-demand).
 *
 * Companion obligations:
 *   - the best-first ORDERING of the output is proven below in this file; and
 *   - the hypergraph-recursion COMPLETENESS (the candidate set = ALL
 *     derivations) is proven in Extraction/EnumerationCompleteness.v.
 *   E-graph exact-key dedup no-loss is covered by ExactKeys/ExactKeyDedup.v.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

(*  Spec-to-Code Traceability                                              *)
(*  ====================================================================  *)
(*  Rocq Definition          | Rust Implementation              | Location *)
(*  -------------------------+----------------------------------+--------- *)
(*  Cand (option nat * nat)  | Derivation { weight, key }       | extract.rs *)
(*  is_zero = (weight None)  | W::is_zero (composed weight = 0̄) | extract.rs *)
(*  select = filter non-zero | kth: built.push iff !is_zero     | extract.rs *)
(*  ====================================================================  *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Permutation.

Import ListNotations.

Section NBestExtraction.

  (* A candidate derivation: an optional composed weight (None = the semiring
     zero 0̄, "refuted") and a content key (nat, standing for the exact,
     injective ContentKey). *)
  Definition Cand : Type := (option nat * nat)%type.
  Definition cweight (c : Cand) : option nat := fst c.
  Definition is_zero (c : Cand) : bool :=
    match cweight c with
    | None => true
    | Some _ => false
    end.

  (* The extractor's selection: keep exactly the non-0̄ candidates. The ONLY
     removal is by evidence (weight = 0̄ = None); nothing else is dropped. *)
  Definition select (l : list Cand) : list Cand :=
    filter (fun c => negb (is_zero c)) l.

  (* Selection yields only original, non-0̄ candidates. *)
  Lemma select_sound : forall c l,
    In c (select l) -> In c l /\ is_zero c = false.
  Proof.
    intros c l Hin. unfold select in Hin. apply filter_In in Hin.
    destruct Hin as [Hin Hb]. split.
    - exact Hin.
    - apply negb_true_iff. exact Hb.
  Qed.

  (* No-miss (the anti-prune core): every non-0̄ candidate survives selection. *)
  Lemma select_complete : forall c l,
    In c l -> is_zero c = false -> In c (select l).
  Proof.
    intros c l Hin Hnz. unfold select. apply filter_In. split.
    - exact Hin.
    - rewrite Hnz. reflexivity.
  Qed.

  (* The ONLY removal is the semiring zero: anything in the output is non-0̄. *)
  Theorem select_only_removes_zero : forall c l,
    In c (select l) -> is_zero c = false.
  Proof. intros c l H. apply select_sound in H. tauto. Qed.

  (* The anti-prune fence, named: an unrefuted (non-0̄) alternative is NEVER
     absent from the output. Weight ORDERS; it never PRUNES. *)
  Theorem no_unrefuted_alternative_dropped : forall c l,
    In c l -> is_zero c = false -> In c (select l).
  Proof. exact select_complete. Qed.

  (* Equal-weight DISTINCT alternatives BOTH survive (no weight-merge); mirrors
     parser_preserves_ambiguous_alternatives at the extraction layer. *)
  Theorem equal_weight_both_survive : forall w k1 k2 l,
    In (Some w, k1) l -> In (Some w, k2) l -> k1 <> k2 ->
    In (Some w, k1) (select l) /\ In (Some w, k2) (select l).
  Proof.
    intros w k1 k2 l H1 H2 _. split; apply select_complete.
    - exact H1.
    - reflexivity.
    - exact H2.
    - reflexivity.
  Qed.

  (* Helper: membership in a demand prefix implies membership overall. *)
  Lemma in_firstn : forall (n : nat) (x : Cand) (l : list Cand),
    In x (firstn n l) -> In x l.
  Proof.
    intros n x l H.
    rewrite <- (firstn_skipn n l).
    apply in_or_app. left. exact H.
  Qed.

  (* Resumability: a longer demand prefix never drops what a shorter one
     surfaced (the lazy stream only grows). *)
  Theorem select_prefix_monotone : forall k x l,
    In x (firstn k (select l)) -> In x (firstn (S k) (select l)).
  Proof.
    intros k x l H.
    apply (in_firstn k x (firstn (S k) (select l))).
    rewrite firstn_firstn.
    replace (Nat.min k (S k)) with k by lia.
    exact H.
  Qed.

  (* Exhaustive-on-demand: every non-0̄ alternative appears at some demand k. *)
  Theorem select_exhausts_on_demand : forall c l,
    In c l -> is_zero c = false ->
    exists k, In c (firstn k (select l)).
  Proof.
    intros c l Hin Hnz.
    exists (length (select l)).
    rewrite firstn_all.
    apply select_complete; assumption.
  Qed.

  (* ===================================================================== *)
  (*  Best-first ORDERING of the selected output                           *)
  (*                                                                       *)
  (*  The non-0̄ candidates, projected to (cost, key) pairs, are emitted in *)
  (*  non-decreasing (cost, then key) order — the best-first guarantee. We  *)
  (*  prove the projected output is sorted AND a permutation of the kept    *)
  (*  candidates (so the no-prune membership above carries to the ordered   *)
  (*  output). Modeled over `nat * nat` (0̄ excluded), so the order is a     *)
  (*  clean total order (transitivity by `lia`).                           *)
  (* ===================================================================== *)

  (* The non-0̄ candidates as (cost, key) pairs. *)
  Definition keyed (l : list Cand) : list (nat * nat) :=
    flat_map
      (fun c => match fst c with Some w => [(w, snd c)] | None => [] end)
      l.

  Lemma in_keyed : forall w k l,
    In (w, k) (keyed l) <-> In (Some w, k) l.
  Proof.
    intros w k l. unfold keyed. rewrite in_flat_map. split.
    - intros [c [Hc Hin]]. destruct c as [ow ck]. simpl in Hin.
      destruct ow as [w' |].
      + destruct Hin as [H | H].
        * inversion H. subst. exact Hc.
        * contradiction.
      + contradiction.
    - intros H. exists (Some w, k). split.
      + exact H.
      + simpl. left. reflexivity.
  Qed.

  (* Total best-first order on (cost, key): lower cost first, then lower key. *)
  Definition cleb (a b : nat * nat) : bool :=
    let (w1, k1) := a in
    let (w2, k2) := b in
    (w1 <? w2) || ((w1 =? w2) && (k1 <=? k2)).

  Lemma cleb_total : forall a b, cleb a b = true \/ cleb b a = true.
  Proof.
    intros [w1 k1] [w2 k2]. unfold cleb.
    destruct (Nat.lt_trichotomy w1 w2) as [H | [H | H]].
    - left. apply orb_true_iff. left. apply Nat.ltb_lt. exact H.
    - subst. destruct (Nat.le_ge_cases k1 k2) as [Hk | Hk].
      + left. apply orb_true_iff. right. apply andb_true_iff. split.
        * apply Nat.eqb_eq. reflexivity.
        * apply Nat.leb_le. exact Hk.
      + right. apply orb_true_iff. right. apply andb_true_iff. split.
        * apply Nat.eqb_eq. reflexivity.
        * apply Nat.leb_le. exact Hk.
    - right. apply orb_true_iff. left. apply Nat.ltb_lt. exact H.
  Qed.

  Lemma cleb_trans : forall a b c,
    cleb a b = true -> cleb b c = true -> cleb a c = true.
  Proof.
    intros [w1 k1] [w2 k2] [w3 k3]. unfold cleb.
    intros Hab Hbc.
    apply orb_true_iff in Hab. apply orb_true_iff in Hbc. apply orb_true_iff.
    destruct Hab as [Hab | Hab].
    - apply Nat.ltb_lt in Hab.
      destruct Hbc as [Hbc | Hbc].
      + apply Nat.ltb_lt in Hbc. left. apply Nat.ltb_lt. lia.
      + apply andb_true_iff in Hbc. destruct Hbc as [Hbc _].
        apply Nat.eqb_eq in Hbc. left. apply Nat.ltb_lt. lia.
    - apply andb_true_iff in Hab. destruct Hab as [Hab1 Hab2].
      apply Nat.eqb_eq in Hab1. apply Nat.leb_le in Hab2.
      destruct Hbc as [Hbc | Hbc].
      + apply Nat.ltb_lt in Hbc. left. apply Nat.ltb_lt. lia.
      + apply andb_true_iff in Hbc. destruct Hbc as [Hbc1 Hbc2].
        apply Nat.eqb_eq in Hbc1. apply Nat.leb_le in Hbc2.
        right. apply andb_true_iff. split.
        * apply Nat.eqb_eq. lia.
        * apply Nat.leb_le. lia.
  Qed.

  Fixpoint insert (x : nat * nat) (l : list (nat * nat)) : list (nat * nat) :=
    match l with
    | [] => [x]
    | h :: t => if cleb x h then x :: l else h :: insert x t
    end.

  Fixpoint isort (l : list (nat * nat)) : list (nat * nat) :=
    match l with
    | [] => []
    | h :: t => insert h (isort t)
    end.

  Lemma insert_perm : forall x l, Permutation (x :: l) (insert x l).
  Proof.
    intros x l. induction l as [| h t IH]; simpl.
    - apply Permutation_refl.
    - destruct (cleb x h).
      + apply Permutation_refl.
      + eapply Permutation_trans.
        * apply perm_swap.
        * apply perm_skip. exact IH.
  Qed.

  Lemma isort_perm : forall l, Permutation l (isort l).
  Proof.
    induction l as [| h t IH]; simpl.
    - apply Permutation_refl.
    - eapply Permutation_trans.
      + apply perm_skip. exact IH.
      + apply insert_perm.
  Qed.

  Lemma insert_in : forall x y l, In y (insert x l) -> y = x \/ In y l.
  Proof.
    intros x y l. induction l as [| h t IH]; simpl.
    - intros [H | H]. left. symmetry. exact H. contradiction.
    - destruct (cleb x h).
      + simpl. intros [H | [H | H]].
        * left. symmetry. exact H.
        * right. left. exact H.
        * right. right. exact H.
      + simpl. intros [H | H].
        * right. left. exact H.
        * apply IH in H. destruct H as [H | H].
          left. exact H. right. right. exact H.
  Qed.

  (* `sorted l`: the head is `cleb`-below every tail element, and the tail is
     sorted (the strong form, equivalent to fully-sorted for a total order). *)
  Fixpoint sorted (l : list (nat * nat)) : Prop :=
    match l with
    | [] => True
    | h :: t => (forall x, In x t -> cleb h x = true) /\ sorted t
    end.

  Lemma insert_sorted : forall x l, sorted l -> sorted (insert x l).
  Proof.
    intros x l. induction l as [| h t IH]; intros Hs; simpl.
    - split. intros y Hy. inversion Hy. exact I.
    - destruct (cleb x h) eqn:Exh.
      + simpl. split.
        * intros y Hy. destruct Hy as [Hy | Hy].
          -- subst y. exact Exh.
          -- destruct Hs as [Hhd _]. apply (cleb_trans x h y Exh (Hhd y Hy)).
        * exact Hs.
      + simpl. destruct Hs as [Hhd Hst]. split.
        * intros y Hy. apply insert_in in Hy. destruct Hy as [Hy | Hy].
          -- subst y. destruct (cleb_total x h) as [Hc | Hc].
             ++ rewrite Exh in Hc. discriminate.
             ++ exact Hc.
          -- apply Hhd. exact Hy.
        * apply IH. exact Hst.
  Qed.

  Lemma isort_sorted : forall l, sorted (isort l).
  Proof.
    induction l as [| h t IH]; simpl.
    - exact I.
    - apply insert_sorted. exact IH.
  Qed.

  (* The best-first ordered output: the non-0̄ candidates, sorted by (cost,key). *)
  Definition select_ordered (l : list Cand) : list (nat * nat) := isort (keyed l).

  (* The output is sorted best-first. *)
  Theorem select_ordered_sorted : forall l, sorted (select_ordered l).
  Proof. intros l. apply isort_sorted. Qed.

  (* The ordered output is a permutation of the kept candidates — so the
     no-prune membership above carries over: ordering reorders, never drops. *)
  Theorem select_ordered_perm : forall l, Permutation (keyed l) (select_ordered l).
  Proof. intros l. apply isort_perm. Qed.

  (* No-miss carried to the ordered output: every non-0̄ alternative appears. *)
  Theorem select_ordered_complete : forall w k l,
    In (Some w, k) l -> In (w, k) (select_ordered l).
  Proof.
    intros w k l H.
    apply (Permutation_in (w, k) (select_ordered_perm l)).
    apply in_keyed. exact H.
  Qed.

End NBestExtraction.
