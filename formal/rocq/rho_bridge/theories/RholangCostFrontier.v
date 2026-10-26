(** * Arbitrary-arity residual stack frontier

    Each natural number is an original preorder transfer-cell index. The
    settlement application removes exactly the popped prefix of each authored
    node before the frontier planner runs. An empty prefix releases its authored
    children; a nonempty prefix keeps the whole subtree as one live root.
    The model deliberately does not preserve settlement-scope synthetic IDs
    across a new RSpace publication. The emitted path records original
    provenance for the current receipt, after which the new publication may
    acquire a fresh root ID just as a linear residual tail does. Atomic RSpace
    retirement/publication and fresh source identity are runtime obligations,
    not consequences of this pure tree theorem.
*)

From Stdlib Require Import List Arith Lia Sorting.Permutation.
Import ListNotations.

Module RholangCostFrontier.

Inductive StackTree : Type :=
| Node : list nat -> StackForest -> StackTree
with StackForest : Type :=
| NoChildren : StackForest
| Child : StackTree -> StackForest -> StackForest.

Fixpoint cell_indices (tree : StackTree) : list nat :=
  match tree with
  | Node cells children => cells ++ forest_indices children
  end
with forest_indices (forest : StackForest) : list nat :=
  match forest with
  | NoChildren => []
  | Child tree rest => cell_indices tree ++ forest_indices rest
  end.

(** A frontier entry retains both its original authored path and the complete
    canonical residual subtree. Traversal over [StackForest] gives arbitrary
    arity without flattening a branch into a sibling's authority. *)
Fixpoint frontier (path : list nat) (tree : StackTree)
    : list (list nat * StackTree) :=
  match tree with
  | Node [] children => forest_frontier path 0 children
  | Node (_ :: _) _ => [(path, tree)]
  end
with forest_frontier (path : list nat) (index : nat)
    (forest : StackForest) : list (list nat * StackTree) :=
  match forest with
  | NoChildren => []
  | Child tree rest =>
      frontier (path ++ [index]) tree ++
      forest_frontier path (S index) rest
  end.

Definition published_indices (entries : list (list nat * StackTree))
    : list nat :=
  concat (map (fun entry => cell_indices (snd entry)) entries).

Lemma published_indices_app : forall first second,
  published_indices (first ++ second) =
    published_indices first ++ published_indices second.
Proof.
  intros first second. unfold published_indices.
  rewrite map_app, concat_app. reflexivity.
Qed.

Fixpoint frontier_indices_exact (tree : StackTree) (path : list nat)
    {struct tree} : published_indices (frontier path tree) = cell_indices tree
with forest_frontier_indices_exact (forest : StackForest)
    (path : list nat) (index : nat) {struct forest} :
    published_indices (forest_frontier path index forest) =
    forest_indices forest.
Proof.
  - destruct tree as [cells children]. destruct cells as [|head tail]; cbn.
    + apply forest_frontier_indices_exact.
    + rewrite app_nil_r. reflexivity.
  - destruct forest as [|tree rest]; cbn.
    + reflexivity.
    + change (published_indices
        (frontier (path ++ [index]) tree ++
          forest_frontier path (S index) rest) =
        cell_indices tree ++ forest_indices rest).
      rewrite published_indices_app.
      rewrite frontier_indices_exact, forest_frontier_indices_exact.
      reflexivity.
Defined.

Theorem frontier_has_no_cell_loss_or_duplication : forall tree path,
  published_indices (frontier path tree) = cell_indices tree.
Proof. apply frontier_indices_exact. Qed.

Corollary unique_original_transfer_indices_stay_unique : forall tree path,
  NoDup (cell_indices tree) ->
  NoDup (published_indices (frontier path tree)).
Proof.
  intros tree path Hunique. rewrite frontier_has_no_cell_loss_or_duplication.
  exact Hunique.
Qed.

Fixpoint frontier_heads_live (tree : StackTree) (path : list nat)
    {struct tree} :
    Forall (fun entry => match snd entry with
      | Node [] _ => False | Node (_ :: _) _ => True end)
      (frontier path tree)
with forest_frontier_heads_live (forest : StackForest)
    (path : list nat) (index : nat) {struct forest} :
    Forall (fun entry => match snd entry with
      | Node [] _ => False | Node (_ :: _) _ => True end)
      (forest_frontier path index forest).
Proof.
  - destruct tree as [cells children]. destruct cells as [|head tail]; cbn.
    + apply forest_frontier_heads_live.
    + constructor; [exact I | constructor].
  - destruct forest as [|tree rest]; cbn.
    + constructor.
    + apply Forall_app. split.
      * apply frontier_heads_live.
      * apply forest_frontier_heads_live.
Defined.

Theorem publication_roots_have_live_heads : forall tree path,
  Forall (fun entry => match snd entry with
    | Node [] _ => False | Node (_ :: _) _ => True end)
    (frontier path tree).
Proof. apply frontier_heads_live. Qed.

(** Settlement records each original transfer index exactly once with its
    consumed/retained status. A valid physical pop marks a prefix of each
    branch's local cells consumed; the following stronger theorem works for
    any marks, so it also covers simultaneous pops in arbitrarily many
    sibling branches. Reordering popped indices ahead of retained indices
    cannot mint or erase an occurrence. The frontier theorem above then
    partitions the retained side among published subtrees. *)
Fixpoint consumed_indices (cells : list (nat * bool)) : list nat :=
  match cells with
  | [] => []
  | (index, true) :: rest => index :: consumed_indices rest
  | (_, false) :: rest => consumed_indices rest
  end.

Fixpoint retained_indices (cells : list (nat * bool)) : list nat :=
  match cells with
  | [] => []
  | (_, true) :: rest => retained_indices rest
  | (index, false) :: rest => index :: retained_indices rest
  end.

Theorem each_branch_pop_is_a_prefix_partition :
  forall (cells : list nat) (pop_count : nat),
  firstn pop_count cells ++ skipn pop_count cells = cells.
Proof. intros; apply firstn_skipn. Qed.

Theorem original_transfer_indices_partition : forall cells,
  Permutation
    (consumed_indices cells ++ retained_indices cells)
    (map fst cells).
Proof.
  induction cells as [|[index consumed] rest IH]; cbn.
  - constructor.
  - destruct consumed; cbn.
    + apply perm_skip. exact IH.
    + eapply Permutation_trans.
      * apply Permutation_sym, Permutation_middle.
      * apply perm_skip. exact IH.
Qed.

Corollary original_unique_indices_are_not_minted : forall cells,
  NoDup (map fst cells) ->
  NoDup (consumed_indices cells ++ retained_indices cells).
Proof.
  intros cells Hunique.
  eapply Permutation_NoDup; [|exact Hunique].
  apply Permutation_sym, original_transfer_indices_partition.
Qed.

Theorem settlement_frontier_partitions_original_indices :
  forall cells residual path,
  retained_indices cells = cell_indices residual ->
  Permutation
    (consumed_indices cells ++ published_indices (frontier path residual))
    (map fst cells).
Proof.
  intros cells residual path Hresidual.
  rewrite frontier_has_no_cell_loss_or_duplication.
  rewrite <- Hresidual.
  apply original_transfer_indices_partition.
Qed.

(** The settlement operation is defined on the *authored* tree. A pop count
    belongs to a path, not to a flat global stack; simultaneous sibling pops
    therefore cannot consume each other's cells. The same path function is
    used to mark original transfer occurrences and to compute the residual. *)
Section AuthoredSettlement.
Variable pop_count : list nat -> nat.

Fixpoint settled_tree (path : list nat) (tree : StackTree) : StackTree :=
  match tree with
  | Node cells children =>
      Node (skipn (pop_count path) cells) (settled_forest path 0 children)
  end
with settled_forest (path : list nat) (index : nat)
    (forest : StackForest) : StackForest :=
  match forest with
  | NoChildren => NoChildren
  | Child tree rest =>
      Child (settled_tree (path ++ [index]) tree)
        (settled_forest path (S index) rest)
  end.

Fixpoint marked_tree (path : list nat) (tree : StackTree)
    : list (nat * bool) :=
  match tree with
  | Node cells children =>
      map (fun index => (index, true)) (firstn (pop_count path) cells) ++
      map (fun index => (index, false)) (skipn (pop_count path) cells) ++
      marked_forest path 0 children
  end
with marked_forest (path : list nat) (index : nat)
    (forest : StackForest) : list (nat * bool) :=
  match forest with
  | NoChildren => []
  | Child tree rest =>
      marked_tree (path ++ [index]) tree ++
      marked_forest path (S index) rest
  end.

Lemma retained_indices_app : forall first second,
  retained_indices (first ++ second) =
    retained_indices first ++ retained_indices second.
Proof.
  induction first as [|[index consumed] rest IH]; intros second; cbn.
  - reflexivity.
  - destruct consumed; cbn; rewrite IH; reflexivity.
Qed.

Lemma marked_true_retains_none : forall indices,
  retained_indices (map (fun index => (index, true)) indices) = [].
Proof. induction indices as [|index rest IH]; cbn; auto. Qed.

Lemma marked_false_retains_all : forall indices,
  retained_indices (map (fun index => (index, false)) indices) = indices.
Proof. induction indices as [|index rest IH]; cbn; congruence. Qed.

Lemma marked_true_covers_original : forall (indices : list nat),
  map fst (map (fun index => (index, true)) indices) = indices.
Proof. induction indices as [|index rest IH]; cbn; congruence. Qed.

Lemma marked_false_covers_original : forall (indices : list nat),
  map fst (map (fun index => (index, false)) indices) = indices.
Proof. induction indices as [|index rest IH]; cbn; congruence. Qed.

Fixpoint settlement_retained_exact (tree : StackTree) (path : list nat)
    {struct tree} :
    retained_indices (marked_tree path tree) =
      cell_indices (settled_tree path tree)
with settlement_forest_retained_exact (forest : StackForest)
    (path : list nat) (index : nat) {struct forest} :
    retained_indices (marked_forest path index forest) =
      forest_indices (settled_forest path index forest).
Proof.
  - destruct tree as [cells children]. cbn.
    repeat rewrite retained_indices_app.
    rewrite marked_true_retains_none, marked_false_retains_all.
    rewrite settlement_forest_retained_exact. reflexivity.
  - destruct forest as [|tree rest]; cbn.
    + reflexivity.
    + rewrite retained_indices_app.
      rewrite settlement_retained_exact, settlement_forest_retained_exact.
      reflexivity.
Defined.

Fixpoint settlement_marks_cover_original (tree : StackTree) (path : list nat)
    {struct tree} :
    map fst (marked_tree path tree) = cell_indices tree
with settlement_forest_marks_cover_original (forest : StackForest)
    (path : list nat) (index : nat) {struct forest} :
    map fst (marked_forest path index forest) = forest_indices forest.
Proof.
  - destruct tree as [cells children]. cbn.
    repeat rewrite map_app.
    rewrite marked_true_covers_original, marked_false_covers_original.
    rewrite settlement_forest_marks_cover_original.
    rewrite app_assoc.
    rewrite firstn_skipn. reflexivity.
  - destruct forest as [|tree rest]; cbn.
    + reflexivity.
    + rewrite map_app.
      rewrite settlement_marks_cover_original,
        settlement_forest_marks_cover_original.
      reflexivity.
Defined.

Theorem authored_settlement_frontier_partitions_original :
  forall tree path,
  Permutation
    (consumed_indices (marked_tree path tree) ++
      published_indices (frontier path (settled_tree path tree)))
    (cell_indices tree).
Proof.
  intros tree path.
  eapply Permutation_trans.
  - apply settlement_frontier_partitions_original_indices.
    apply settlement_retained_exact.
  - rewrite settlement_marks_cover_original. reflexivity.
Qed.

(** Each frontier entry becomes one new receipt whose indices are in the
    original transfer-event preorder. All selected branch pops belong to this
    *one* original root transaction; they are not independent old receipts. *)
Definition publication_receipts (entries : list (list nat * StackTree))
    : list (list nat) :=
  map (fun entry => cell_indices (snd entry)) entries.

Lemma publication_receipts_flatten : forall entries,
  concat (publication_receipts entries) = published_indices entries.
Proof. reflexivity. Qed.

(** The ledger has only two externally visible outcomes. In the committed
    outcome the old RSpace datum and old receipt are retired together, then
    each independently live frontier subtree has exactly one receipt group.
    The abort outcome is the original datum/receipt unchanged. Fresh RSpace
    source hashes are deliberately not equated with settlement-scope branch
    IDs; cell-index provenance, not those IDs, is conserved here. *)
Inductive TransactionOutcome := Aborted | Committed.

Record PublicationLedger := {
  old_datum_live : bool;
  old_receipt_live : bool;
  new_subtrees : list (list nat * StackTree);
  new_receipts : list (list nat)
}.

Definition publication_ledger (outcome : TransactionOutcome)
    (tree : StackTree) (path : list nat) : PublicationLedger :=
  match outcome with
  | Aborted =>
      {| old_datum_live := true;
         old_receipt_live := true;
         new_subtrees := [];
         new_receipts := [] |}
  | Committed =>
      let entries := frontier path (settled_tree path tree) in
      {| old_datum_live := false;
         old_receipt_live := false;
         new_subtrees := entries;
         new_receipts := publication_receipts entries |}
  end.

Theorem abort_preserves_old_datum_and_receipt : forall tree path,
  old_datum_live (publication_ledger Aborted tree path) = true /\
  old_receipt_live (publication_ledger Aborted tree path) = true /\
  new_subtrees (publication_ledger Aborted tree path) = [] /\
  new_receipts (publication_ledger Aborted tree path) = [].
Proof. intros; repeat split; reflexivity. Qed.

Theorem commit_retires_old_before_frontier_visibility : forall tree path,
  old_datum_live (publication_ledger Committed tree path) = false /\
  old_receipt_live (publication_ledger Committed tree path) = false /\
  new_receipts (publication_ledger Committed tree path) =
    publication_receipts (new_subtrees (publication_ledger Committed tree path)).
Proof. intros; repeat split; reflexivity. Qed.

Theorem committed_receipts_partition_one_original_birth :
  forall tree path,
  Permutation
    (consumed_indices (marked_tree path tree) ++
      concat (new_receipts (publication_ledger Committed tree path)))
    (cell_indices tree).
Proof.
  intros tree path.
  change (Permutation
    (consumed_indices (marked_tree path tree) ++
      published_indices (frontier path (settled_tree path tree)))
    (cell_indices tree)).
  apply authored_settlement_frontier_partitions_original.
Qed.

Corollary committed_receipts_do_not_duplicate_occurrences :
  forall tree path,
  NoDup (cell_indices tree) ->
  NoDup
    (consumed_indices (marked_tree path tree) ++
      concat (new_receipts (publication_ledger Committed tree path))).
Proof.
  intros tree path Hunique.
  eapply Permutation_NoDup; [|exact Hunique].
  apply Permutation_sym, committed_receipts_partition_one_original_birth.
Qed.

End AuthoredSettlement.

Print Assumptions frontier_has_no_cell_loss_or_duplication.
Print Assumptions publication_roots_have_live_heads.
Print Assumptions original_transfer_indices_partition.
Print Assumptions settlement_frontier_partitions_original_indices.
Print Assumptions authored_settlement_frontier_partitions_original.
Print Assumptions committed_receipts_partition_one_original_birth.
Print Assumptions committed_receipts_do_not_duplicate_occurrences.

End RholangCostFrontier.
