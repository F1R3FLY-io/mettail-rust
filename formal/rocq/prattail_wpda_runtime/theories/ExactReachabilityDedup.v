(*
 * ExactReachabilityDedup: eval normal-form reachability must key its visited
 * set by the exact semantic key when that key is available, never solely by a
 * 64-bit term id. This models the Rust runtime change:
 *
 *   TermInfo.exact_key : option Vec<u8>
 *   Rewrite.{from_key,to_key} : option Vec<u8>
 *   ReachableNormalForms.visited : HashSet<ReachKey>
 *
 * Legacy callers that provide only a term_id are expanded to every TermInfo
 * with that id before traversal. Therefore a digest collision cannot silently
 * discard one candidate; the only fallback to a legacy id is for graphs that do
 * not provide exact keys at all.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Section ExactReachabilityDedup.

  Record Term : Type := {
    term_id : nat;
    exact_key : nat;
    is_nf : bool
  }.

  Record Edge : Type := {
    from_key : nat;
    to_key : nat
  }.

  Fixpoint contains_key (k : nat) (keys : list nat) : bool :=
    match keys with
    | [] => false
    | x :: xs => Nat.eqb k x || contains_key k xs
    end.

  Definition insert_key (k : nat) (keys : list nat) : list nat :=
    if contains_key k keys then keys else k :: keys.

  Definition push_legacy_seed (id : nat) (terms : list Term) : list nat :=
    fold_right
      (fun t acc =>
         if Nat.eqb (term_id t) id
         then insert_key (exact_key t) acc
         else acc)
      [] terms.

  Definition push_exact_seed (k : nat) : list nat := [k].

  Definition edge_enabled (k : nat) (e : Edge) : bool :=
    Nat.eqb (from_key e) k.

  Definition exact_successors (k : nat) (edges : list Edge) : list nat :=
    fold_right
      (fun e acc => if edge_enabled k e then insert_key (to_key e) acc else acc)
      [] edges.

  Lemma contains_key_iff : forall k xs,
    contains_key k xs = true <-> In k xs.
  Proof.
    intros k xs. induction xs as [| x xs IH].
    - simpl. split; [discriminate | intros []].
    - simpl. rewrite Bool.orb_true_iff. rewrite Nat.eqb_eq. rewrite IH.
      split.
      + intros [H | H]; [left; symmetry | right]; exact H.
      + intros [H | H]; [left; symmetry | right]; exact H.
  Qed.

  Lemma insert_key_preserves_inserted : forall k xs,
    In k (insert_key k xs).
  Proof.
    intros k xs. unfold insert_key.
    destruct (contains_key k xs) eqn:H.
    - apply contains_key_iff. exact H.
    - simpl. left. reflexivity.
  Qed.

  Lemma insert_key_preserves_existing : forall k x xs,
    In x xs -> In x (insert_key k xs).
  Proof.
    intros k x xs Hin. unfold insert_key.
    destruct (contains_key k xs); [exact Hin | simpl; right; exact Hin].
  Qed.

  Theorem legacy_seed_expands_all_exact_keys : forall id terms t,
    In t terms ->
    term_id t = id ->
    In (exact_key t) (push_legacy_seed id terms).
  Proof.
    intros id terms t Hin Hid.
    induction terms as [| h rest IH].
    - contradiction.
    - simpl in Hin. simpl. destruct Hin as [Heq | Hrest].
      + subst h. rewrite Hid. rewrite Nat.eqb_refl. apply insert_key_preserves_inserted.
      + destruct (Nat.eqb (term_id h) id).
        * apply insert_key_preserves_existing. apply IH. exact Hrest.
        * apply IH. exact Hrest.
  Qed.

  Theorem exact_successor_preserved : forall k edges e,
    In e edges ->
    from_key e = k ->
    In (to_key e) (exact_successors k edges).
  Proof.
    intros k edges e Hin Hfrom.
    induction edges as [| h rest IH].
    - contradiction.
    - simpl in Hin. simpl. destruct Hin as [Heq | Hrest].
      + subst h. unfold edge_enabled. rewrite Hfrom. rewrite Nat.eqb_refl.
        apply insert_key_preserves_inserted.
      + destruct (edge_enabled k h).
        * apply insert_key_preserves_existing. apply IH. exact Hrest.
        * apply IH. exact Hrest.
  Qed.

  (* A concrete collision witness: two terms have the same 64-bit-style id but
     distinct exact keys, and both are retained by legacy expansion. *)
  Example legacy_collision_keeps_both :
    let t0 := {| term_id := 7; exact_key := 10; is_nf := false |} in
    let t1 := {| term_id := 7; exact_key := 20; is_nf := false |} in
    In 10 (push_legacy_seed 7 [t0; t1])
    /\ In 20 (push_legacy_seed 7 [t0; t1]).
  Proof.
    simpl. split.
    - left. reflexivity.
    - right. left. reflexivity.
  Qed.

  (* The negative fence: a visited set keyed only by term_id can lose one of the
     colliding exact alternatives. *)
  Definition id_only_insert (t : Term) (ids : list nat) : list nat :=
    insert_key (term_id t) ids.

  Example id_only_dedup_can_drop_exact_candidate :
    let t0 := {| term_id := 7; exact_key := 10; is_nf := false |} in
    let t1 := {| term_id := 7; exact_key := 20; is_nf := false |} in
    id_only_insert t1 (id_only_insert t0 []) = [7]
    /\ exact_key t0 <> exact_key t1.
  Proof.
    simpl. split; [reflexivity | discriminate].
  Qed.

End ExactReachabilityDedup.
