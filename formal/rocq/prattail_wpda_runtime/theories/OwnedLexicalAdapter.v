(** The owned input adapter is a projection of the already-built lexical graph,
    not a lexer. Full positions include mode contexts. Rejected edges remain in
    the borrowed evidence graph; only Accepted edges enter the existing LexDag
    token view, in their original order. Holes remain a separate typed input.

    Rust obligations: use full LexPosition keys, retain the inverse node roster,
    call the original trivia canonicalizer, retain the original edge ordinal,
    never rescan text, and complete checked census/admission before building the
    second view. LogicalEoiObservation supplies the source-specific EOF law.
    The model does not prove a complete parser or authorize discarding evidence.
*)
From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.
Module OwnedLexicalAdapter.

Record Position := { offset : nat; context : nat }.
Record Candidate := { token : nat; target : Position; ordinal : nat }.
Inductive Edge := Accepted (candidate : Candidate) | Refuted (reason : nat).

Fixpoint accepted (edges : list Edge) : list Candidate :=
  match edges with
  | [] => []
  | Accepted candidate :: rest => candidate :: accepted rest
  | Refuted _ :: rest => accepted rest
  end.

Theorem accepted_order : forall left right,
    accepted (left ++ right) = accepted left ++ accepted right.
Proof.
  induction left as [|edge rest IH]; intros; simpl; [reflexivity|].
  destruct edge; simpl; now rewrite IH.
Qed.

Theorem accepted_exactly_original : forall edges candidate,
    In candidate (accepted edges) <-> In (Accepted candidate) edges.
Proof.
  induction edges as [|edge rest IH]; intros candidate; simpl.
  - tauto.
  - destruct edge as [value|reason]; simpl; rewrite IH.
    + split; intros [H|H]; [left; now subst|now right|left; now inversion H|now right].
    + split; [now right|intros [H|H]; [discriminate|assumption]].
Qed.

Theorem original_ordinal_retained : forall candidate rest,
    hd_error (accepted (Accepted candidate :: rest)) = Some candidate.
Proof. reflexivity. Qed.

Definition graph_evidence (edges : list Edge) := edges.
Theorem refutations_remain_observable : forall edges reason,
    In (Refuted reason) edges -> In (Refuted reason) (graph_evidence edges).
Proof. auto. Qed.

Definition position_at (positions : list Position) index := nth_error positions index.
Theorem dense_lookup_preserves_context : forall positions index position,
    position_at positions index = Some position ->
    option_map context (position_at positions index) = Some (context position).
Proof. intros positions index position H; now rewrite H. Qed.

Theorem distinct_contexts_are_distinct_positions : forall byte left right,
    left <> right ->
    {| offset := byte; context := left |} <>
    {| offset := byte; context := right |}.
Proof. intros byte left right H E; inversion E; contradiction. Qed.

Definition admitted nodes edges bytes node_limit edge_limit byte_limit :=
  (nodes <=? node_limit) && (edges <=? edge_limit) && (bytes <=? byte_limit).
Theorem admission_covers_all_storage : forall n e b nl el bl,
    admitted n e b nl el bl = true -> n <= nl /\ e <= el /\ b <= bl.
Proof.
  intros n e b nl el bl H; unfold admitted in H.
  apply andb_true_iff in H as [H B].
  apply andb_true_iff in H as [N E].
  apply Nat.leb_le in N; apply Nat.leb_le in E; apply Nat.leb_le in B; auto.
Qed.

Inductive Input := TextEdge (candidate : Candidate) | TypedHole (id category : nat).
Definition token_candidate input :=
  match input with TextEdge candidate => Some candidate | TypedHole _ _ => None end.
Theorem typed_holes_are_not_text : forall id category,
    token_candidate (TypedHole id category) = None.
Proof. reflexivity. Qed.

Print Assumptions accepted_order.
Print Assumptions accepted_exactly_original.
Print Assumptions original_ordinal_retained.
Print Assumptions refutations_remain_observable.
Print Assumptions dense_lookup_preserves_context.
Print Assumptions distinct_contexts_are_distinct_positions.
Print Assumptions admission_covers_all_storage.
Print Assumptions typed_holes_are_not_text.
End OwnedLexicalAdapter.
