(** Local cleanup allowances for the generated checked binding worker.

    Reuse the existing finite ownership tree and selected-dummy receipt model.
    An edge here denotes an OWNED output occurrence, not an Arc address or
    structural equality class. Source-pinned shallow Arc edges are absent;
    their reference/replacement operations belong to the parent's local facts.
    The Rust source borrow must remain alive through normal-error cleanup.

    This is an additive event bound, not a verification of arbitrary Rust Drop.
    Local copy and cleanup facts must be instantiated from the actual variant,
    payload contracts and admitted container widths. Selected dummy facts may
    not be substituted for those actual-node facts. Panic/TLS teardown and
    physical allocator bounds remain outside this normal-cleanup model.

    Intermediate roots can reside in indexed slots, assembly locals or a
    container. Moving an owned occurrence transfers its existing allowance.
    Map collisions partition key and value occurrences separately: the first
    key and last value may come from different entries. No theorem below
    assumes that whole map entries survive or disappear as indivisible pairs. *)
From Stdlib Require Import List Arith Lia Sorting.Permutation.
From Trampoline Require Import WorklistFoldEquivalence.
From RhoBridge Require Import GeneratedDummyCleanupReservation.
Import ListNotations.

Module GeneratedBindingOutputReservation.
Module W := WorklistFoldEquivalence.
Module D := GeneratedDummyCleanupReservation.

Definition sum_counts {A} (project : A -> D.Counts) (values : list A) : D.Counts :=
  fun event => fold_right (fun value rest => project value event + rest) 0 values.

Lemma sum_counts_app : forall A (project : A -> D.Counts) left right event,
  sum_counts project (left ++ right) event =
    sum_counts project left event + sum_counts project right event.
Proof.
  intros A project left. induction left as [|head tail IH]; intros right event.
  - reflexivity.
  - unfold sum_counts in *. cbn in *. rewrite IH. lia.
Qed.

Lemma sum_counts_permutation :
  forall A (project : A -> D.Counts) left right,
  Permutation left right ->
  forall event, sum_counts project left event = sum_counts project right event.
Proof.
  intros A project left right H. induction H; intro event.
  - reflexivity.
  - unfold sum_counts in *. cbn. now rewrite IHPermutation.
  - unfold sum_counts. cbn. lia.
  - now rewrite IHPermutation1, IHPermutation2.
Qed.

Section Outputs.
Variable dummy_construction dummy_extraction dummy_glue : nat -> D.Counts.
Definition dummy_receipt := D.receipt dummy_construction dummy_extraction dummy_glue.

(** Field occurrences, including repetitions; these are replacement recipes,
    never the actual output children. *)
Variable replacement_recipes : nat -> list W.tree.
Variable actual_copy actual_flat_cleanup : nat -> D.Counts.

Definition replacements (phase : D.Receipt -> D.Counts) tag : D.Counts :=
  sum_counts (fun input event =>
    D.construction (dummy_receipt input) event + phase (dummy_receipt input) event)
    (replacement_recipes tag).

Lemma replacement_active_le_normal : forall tag event,
  replacements D.active_drop tag event <= replacements D.normal_drop tag event.
Proof.
  intros tag event. unfold replacements, sum_counts.
  induction (replacement_recipes tag) as [|input rest IH].
  - reflexivity.
  - cbn [fold_right].
    pose proof (D.active_cleanup_is_componentwise_bounded_by_normal
      dummy_construction dummy_extraction dummy_glue input event).
    unfold dummy_receipt in *. lia.
Qed.

(** Each output reserves the independently rooted case. A popped shell uses
    neither pool acquisition nor final failed-pop/return beyond its own pop.
    Shared-source edges and optional/collection branches contribute only their
    real local operations to actual_flat_cleanup. *)
Definition root_base event :=
  D.atom D.EnterDestructor event + D.atom D.AcquirePool event +
  D.atom D.ExtractChildren event + D.atom D.PopDropTask event +
  D.atom D.ReturnPool event.
Definition popped_base event :=
  D.atom D.PopDropTask event + D.atom D.ExtractChildren event +
  D.atom D.EnterDestructor event.
Definition local_root tag event :=
  root_base event + actual_flat_cleanup tag event + replacements D.normal_drop tag event.
Definition local_popped tag event :=
  popped_base event + actual_flat_cleanup tag event + replacements D.active_drop tag event.
Definition local_credit tag event :=
  D.atom D.ConstructCategory event + actual_copy tag event + local_root tag event.

Lemma local_popped_le_root : forall tag event,
  local_popped tag event <= local_root tag event.
Proof.
  intros. pose proof (replacement_active_le_normal tag event).
  unfold local_popped, local_root, root_base, popped_base. lia.
Qed.

Record OutputReceipt := {
  output_root : D.Counts;
  output_popped : D.Counts;
  output_credit : D.Counts
}.

Definition output_algebra tag (children : list OutputReceipt) : OutputReceipt :=
  {| output_root := fun event =>
       local_root tag event + sum_counts output_popped children event;
     output_popped := fun event =>
       local_popped tag event + sum_counts output_popped children event;
     output_credit := fun event =>
       local_credit tag event + sum_counts output_credit children event |}.
Definition output := @W.recursive_fold OutputReceipt output_algebra.
Definition outputs := @W.recursive_folds OutputReceipt output_algebra.
Definition bounded value := forall event,
  output_popped value event <= output_root value event /\
  output_root value event <= output_credit value event.

Lemma bounded_children : forall children,
  Forall bounded children -> forall event,
  sum_counts output_popped children event <= sum_counts output_credit children event.
Proof.
  intros children H. induction H as [|child rest HC HR IH]; intro event.
  - reflexivity.
  - specialize (HC event). specialize (IH event).
    unfold sum_counts in *. cbn in *. lia.
Qed.

Lemma algebra_bounded : forall tag children,
  Forall bounded children -> bounded (output_algebra tag children).
Proof.
  intros tag children H event.
  pose proof (local_popped_le_root tag event).
  pose proof (bounded_children children H event).
  cbn [output_algebra output_popped output_root output_credit].
  unfold local_credit. split; lia.
Qed.

Theorem owned_outputs_and_forests_are_bounded :
  (forall input, bounded (output input)) /\
  (forall inputs, Forall bounded (outputs inputs)).
Proof.
  apply W.tree_forest_ind.
  - intros tag children IH.
    change (bounded (output_algebra tag (outputs children))).
    now apply algebra_bounded.
  - constructor.
  - intros head HH tail HT. change (Forall bounded (output head :: outputs tail)).
    constructor; assumption.
Qed.

Theorem independently_disposed_partial_roots_are_covered : forall roots,
  Forall bounded roots -> forall event,
  sum_counts output_root roots event <= sum_counts output_credit roots event.
Proof.
  intros roots H. induction H as [|root rest HC HR IH]; intro event.
  - reflexivity.
  - specialize (HC event). specialize (IH event).
    unfold sum_counts in *. cbn in *. lia.
Qed.

Theorem assembly_transfers_existing_child_credits : forall tag children event,
  output_credit (output (W.Node tag children)) event =
    local_credit tag event + sum_counts output_credit (outputs children) event.
Proof. reflexivity. Qed.

(** With no owned children, borrowed source size does not enter the bound.
    The local field facts still pay all shallow Arc and replacement work. *)
Theorem pinned_source_edges_need_only_local_credit : forall tag event,
  output_credit (output (W.Node tag W.FNil)) event = local_credit tag event.
Proof. intros. change (local_credit tag event + 0 = local_credit tag event).
  apply Nat.add_0_r. Qed.

(** Permutation is on ownership OCCURRENCES, so duplicates are not erased.
    The partition premise must follow the actual container insertion law and
    slot ownership transitions; this theorem does not invent that premise. *)
Theorem retained_and_discarded_credits_partition : forall original retained discarded,
  Permutation original (retained ++ discarded) -> forall event,
  sum_counts output_credit original event =
    sum_counts output_credit retained event + sum_counts output_credit discarded event.
Proof.
  intros original retained discarded H event.
  rewrite (sum_counts_permutation OutputReceipt output_credit _ _ H event).
  apply sum_counts_app.
Qed.

Theorem weighted_partial_cleanup_is_covered : forall roots weight,
  Forall bounded roots ->
  D.weighted weight (sum_counts output_root roots) <=
    D.weighted weight (sum_counts output_credit roots).
Proof.
  intros. apply D.weighted_componentwise_bound. intro event.
  now apply independently_disposed_partial_roots_are_covered.
Qed.

Theorem existing_worklist_computes_output_credit : forall input,
  @W.steps OutputReceipt output_algebra
    (@W.State OutputReceipt [W.VisitTree input] [])
    (@W.State OutputReceipt [] [@W.TreeValue OutputReceipt (output input)]).
Proof. intro input. unfold output. apply W.worklist_root_equivalence. Qed.

End Outputs.

Print Assumptions replacement_active_le_normal.
Print Assumptions local_popped_le_root.
Print Assumptions algebra_bounded.
Print Assumptions owned_outputs_and_forests_are_bounded.
Print Assumptions independently_disposed_partial_roots_are_covered.
Print Assumptions assembly_transfers_existing_child_credits.
Print Assumptions pinned_source_edges_need_only_local_credit.
Print Assumptions retained_and_discarded_credits_partition.
Print Assumptions weighted_partial_cleanup_is_covered.
Print Assumptions existing_worklist_computes_output_credit.
End GeneratedBindingOutputReservation.
