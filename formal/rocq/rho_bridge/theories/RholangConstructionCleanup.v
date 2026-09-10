(** Normal, non-panicking cleanup for the scalar/append/Fresh construction image.

    The pinned node's generated Par::drop calls dismantle_in_place. The root
    detaches children into a heap worklist; each popped child detaches its own
    children and then drops an empty shell. That shell's Par::drop calls the
    child table once more, but has no descendants to schedule.

    The explicit transition below uses a top-first stack. Source extraction
    appends children in order to a Vec, hence the reversal before the previous
    pending stack. Structural measurements reuse the deep construction receipt.
    No Rust traversal is added. Exact control counts are not allocation-volume
    bounds or proofs of panic-unwind cleanup, map destruction or all schema
    families. Those obligations remain separate. *)
From Stdlib Require Import List Arith Lia.
From RhoBridge Require Import RholangTargetConstruction RholangDeepConstructionSize.
Import ListNotations.

Definition head_children (head : Head) : list Value :=
  match head with MakeHead _ children => children end.
Definition direct_children (value : Value) : list Value :=
  flat_map head_children (heads_of value).
Definition forest_mass (values : list Value) : nat :=
  sum_sizes (fun value => S (value_owned_count DescendantPars value)) values.

Lemma sum_sizes_flat_map : forall A B (measure : B -> nat) (children : A -> list B) items,
  sum_sizes measure (flat_map children items) =
    sum_sizes (fun item => sum_sizes measure (children item)) items.
Proof.
  intros A B measure children items. induction items as [|item rest IH]; [reflexivity|].
  cbn [flat_map]. rewrite sum_sizes_app, IH. reflexivity.
Qed.

Lemma sum_sizes_rev : forall A (measure : A -> nat) items,
  sum_sizes measure (rev items) = sum_sizes measure items.
Proof.
  intros A measure items. induction items as [|item rest IH]; [reflexivity|].
  cbn [rev]. rewrite sum_sizes_app, IH.
  change (sum_sizes measure rest + (measure item + 0) = measure item + sum_sizes measure rest).
  lia.
Qed.

Lemma head_descendants_are_the_child_forest : forall head,
  head_deep_count DescendantPars head = forest_mass (head_children head).
Proof.
  intros [kind children]. cbn [head_deep_count head_children].
  assert (Hown : head_owned_count DescendantPars kind children = 0).
  { destruct kind; reflexivity. }
  rewrite Hown. reflexivity.
Qed.

Theorem value_descendants_are_the_direct_child_forest : forall value,
  value_owned_count DescendantPars value = forest_mass (direct_children value).
Proof.
  intros [heads summary]. unfold direct_children, forest_mass.
  cbn [heads_of value_owned_count]. rewrite sum_sizes_flat_map.
  apply sum_sizes_extensional. intros head _. apply head_descendants_are_the_child_forest.
Qed.

Lemma forest_mass_bounds_pending_length : forall pending,
  List.length pending <= forest_mass pending.
Proof.
  induction pending as [|value rest IH]; [reflexivity|].
  change (S (List.length rest) <=
    S (value_owned_count DescendantPars value) + forest_mass rest). lia.
Qed.

Definition cleanup_step (pending : list Value) : option (list Value) :=
  match pending with
  | [] => None
  | value :: rest => Some (rev (direct_children value) ++ rest)
  end.

Theorem cleanup_step_consumes_exactly_one_owned_occurrence : forall pending next,
  cleanup_step pending = Some next -> forest_mass pending = S (forest_mass next).
Proof.
  intros [|value rest] next H; [discriminate|]. inversion H; subst next.
  unfold forest_mass at 2. rewrite sum_sizes_app, sum_sizes_rev.
  change (S (value_owned_count DescendantPars value) + forest_mass rest =
    S (forest_mass (direct_children value) + forest_mass rest)).
  now rewrite value_descendants_are_the_direct_child_forest.
Qed.

(** Each nonterminal transition is one outer cleanup-loop pop. Its child-shell
    destructor has an empty inner loop and is counted separately below. *)
Inductive CleanupSteps : nat -> nat -> list Value -> Prop :=
| CleanupDone : forall capacity, CleanupSteps 0 capacity []
| CleanupNext : forall steps capacity pending next,
    List.length pending <= capacity -> cleanup_step pending = Some next ->
    CleanupSteps steps capacity next -> CleanupSteps (S steps) capacity pending.

Theorem cleanup_forest_terminates_with_exact_count_and_bounded_stack :
  forall count pending capacity,
  forest_mass pending = count -> count <= capacity -> CleanupSteps count capacity pending.
Proof.
  induction count as [|count IH]; intros pending capacity HM HC.
  - destruct pending as [|value rest]; [constructor|].
    cbn [forest_mass sum_sizes fold_right] in HM. lia.
  - destruct pending as [|value rest].
    { cbn [forest_mass sum_sizes fold_right] in HM. discriminate. }
    econstructor.
    + pose proof (forest_mass_bounds_pending_length (value :: rest)). lia.
    + reflexivity.
    + apply IH; [|lia].
      pose proof (cleanup_step_consumes_exactly_one_owned_occurrence
        (value :: rest) (rev (direct_children value) ++ rest) eq_refl). lia.
Qed.

Theorem normal_par_drop_has_exact_descendant_worklist : forall value,
  CleanupSteps (value_owned_count DescendantPars value)
    (value_owned_count DescendantPars value) (rev (direct_children value)).
Proof.
  intro value. apply cleanup_forest_terminates_with_exact_count_and_bounded_stack; [|lia].
  unfold forest_mass. rewrite sum_sizes_rev.
  symmetry. apply value_descendants_are_the_direct_child_forest.
Qed.

Record CleanupControl := {
  cleanup_loop_pops : nat;
  par_destructor_entries : nat;
  child_table_calls : nat
}.

(** Source-derived wrapper-count annotation, not additional operational events
    in CleanupSteps. One root destructor/child-table call precedes the loop. Each iteration
    adds one pop, one empty child-shell destructor, and two child-table calls:
    explicit extraction plus the empty shell's generated Drop. The theorem
    below attaches these source-derived counts to the proved loop length; its
    two annotation equalities do not separately prove Rust destructor events. *)
Definition normal_cleanup_control (descendants : nat) : CleanupControl :=
  {| cleanup_loop_pops := descendants;
     par_destructor_entries := S descendants;
     child_table_calls := S (2 * descendants) |}.

Theorem normal_cleanup_control_observes_proved_loop : forall value,
  let descendants := value_owned_count DescendantPars value in
  let control := normal_cleanup_control descendants in
  CleanupSteps (cleanup_loop_pops control) descendants (rev (direct_children value)) /\
  par_destructor_entries control = 1 + descendants /\
  child_table_calls control = 1 + 2 * descendants.
Proof. intro value. split; [apply normal_par_drop_has_exact_descendant_worklist|]. split; reflexivity. Qed.

Print Assumptions value_descendants_are_the_direct_child_forest.
Print Assumptions forest_mass_bounds_pending_length.
Print Assumptions cleanup_step_consumes_exactly_one_owned_occurrence.
Print Assumptions cleanup_forest_terminates_with_exact_count_and_bounded_stack.
Print Assumptions normal_par_drop_has_exact_descendant_worklist.
Print Assumptions normal_cleanup_control_observes_proved_loop.
