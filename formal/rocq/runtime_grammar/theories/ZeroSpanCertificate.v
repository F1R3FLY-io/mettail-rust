From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.

Definition Edge := (nat * nat)%type.

Definition edge_valid (count : nat) (edge : Edge) : Prop :=
  fst edge < count /\ snd edge < count.

Definition edge_decreases (rank : nat -> nat) (edge : Edge) : Prop :=
  rank (snd edge) < rank (fst edge).

Definition rank_at (ranks : list nat) (index : nat) : nat :=
  match nth_error ranks index with
  | Some rank => rank
  | None => 0
  end.

Definition edge_decreasesb (ranks : list nat) (edge : Edge) : bool :=
  match nth_error ranks (fst edge), nth_error ranks (snd edge) with
  | Some parent_rank, Some child_rank => Nat.ltb child_rank parent_rank
  | _, _ => false
  end.

Definition verify_zero_span_certificate
    (count : nat) (edges : list Edge) (ranks : list nat) : bool :=
  Nat.eqb (length ranks) count && forallb (edge_decreasesb ranks) edges.

Lemma nth_error_total_under_length :
  forall (values : list nat) count index,
    length values = count -> index < count ->
    exists value, nth_error values index = Some value.
Proof.
  intros values count index Hlength Hbound.
  destruct (nth_error values index) eqn:Hnth; [eauto |].
  apply nth_error_None in Hnth. lia.
Qed.

Theorem verified_edge_is_bounded_and_decreases :
  forall count edges ranks edge,
    verify_zero_span_certificate count edges ranks = true ->
    In edge edges ->
    edge_valid count edge /\ edge_decreases (rank_at ranks) edge.
Proof.
  intros count edges ranks [parent child] Hverify Hin.
  unfold verify_zero_span_certificate in Hverify.
  apply andb_true_iff in Hverify as [Hlength Hall].
  apply Nat.eqb_eq in Hlength.
  rewrite forallb_forall in Hall. specialize (Hall (parent, child) Hin).
  unfold edge_decreasesb in Hall. simpl in Hall.
  destruct (nth_error ranks parent) as [parent_rank|] eqn:Hparent; try discriminate.
  destruct (nth_error ranks child) as [child_rank|] eqn:Hchild; try discriminate.
  apply Nat.ltb_lt in Hall.
  assert (Hparent_bound : parent < length ranks).
  { apply nth_error_Some. rewrite Hparent. discriminate. }
  assert (Hchild_bound : child < length ranks).
  { apply nth_error_Some. rewrite Hchild. discriminate. }
  split.
  - unfold edge_valid. simpl. lia.
  - unfold edge_decreases. simpl.
    unfold rank_at. rewrite Hparent, Hchild.
    exact Hall.
Qed.

Inductive Path (edges : list Edge) : nat -> nat -> Prop :=
| PathEdge : forall parent child,
    In (parent, child) edges -> Path edges parent child
| PathStep : forall parent middle child,
    In (parent, middle) edges -> Path edges middle child -> Path edges parent child.

Theorem verified_path_strictly_decreases :
  forall count edges ranks parent child,
    verify_zero_span_certificate count edges ranks = true ->
    Path edges parent child ->
    rank_at ranks child < rank_at ranks parent.
Proof.
  intros count edges ranks parent child Hverify Hpath.
  induction Hpath.
  - pose proof (verified_edge_is_bounded_and_decreases _ _ _ _ Hverify H) as [_ Hdecrease].
    exact Hdecrease.
  - pose proof (verified_edge_is_bounded_and_decreases _ _ _ _ Hverify H) as [_ Hdecrease].
    unfold edge_decreases in Hdecrease. simpl in Hdecrease. lia.
Qed.

Theorem verified_zero_span_graph_is_acyclic :
  forall count edges ranks node,
    verify_zero_span_certificate count edges ranks = true ->
    ~ Path edges node node.
Proof.
  intros count edges ranks node Hverify Hcycle.
  pose proof (verified_path_strictly_decreases _ _ _ _ _ Hverify Hcycle).
  lia.
Qed.

Print Assumptions verified_edge_is_bounded_and_decreases.
Print Assumptions verified_zero_span_graph_is_acyclic.
