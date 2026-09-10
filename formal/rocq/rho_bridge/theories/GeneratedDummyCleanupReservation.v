(** Additive normal-cleanup receipts for the already-selected finite dummy
    recipes in macros/src/gen/term_ops/iterative_drop.rs.

    Reuse the existing finite tree/forest and fold machine. A tag identifies
    one selected constructor. Its children are the selected ChildArc recipes,
    in field order WITH MULTIPLICITY. Each occurrence constructs a fresh Arc;
    this is not a model of arbitrary shared AST ownership.

    Local construction, extraction and flat-field cleanup contracts are
    parameters. They must describe the actual selected defaults/fields.
    No theorem asserts arbitrary Rust Default or whole-Drop correctness.

    C = construction; X = explicit extraction;
    A = destruction with DROP_ACTIVE true;
    P = processing one popped dummy task;
    N = normal root destruction with DROP_ACTIVE false and an available
        empty pool, selecting the existing is_outermost branch.

    Root replacements undergo N after the flag is cleared. Replacements in
    popped task shells undergo A. Panic recovery, TLS teardown, allocator
    capacity and physical memory are outside this model. *)
From Stdlib Require Import List Arith Lia.
From Trampoline Require Import WorklistFoldEquivalence.
From PrattailWpdaRuntime Require Import ReconstructionWorkBudget.
From RhoBridge Require Import
  RholangInitialGraphResources RholangPreparationReservation.
Import ListNotations.

Module GeneratedDummyCleanupReservation.
Module W := WorklistFoldEquivalence.

Inductive Event :=
| ConstructCategory
| EnterDestructor
| ExtractChildren
| HandleField
| PushDropTask
| PopDropTask
| AllocateArc
| CheckArcOwner
| ReleaseFieldArc
| AcquirePool
| ReturnPool
| NativeWork
| NativeRecord
| OwnedByte.

Definition event_eq_dec : forall left right : Event,
  {left = right} + {left <> right}.
Proof. decide equality. Defined.

Definition Counts := Event -> nat.
Definition atom (event : Event) : Counts :=
  fun observed => if event_eq_dec event observed then 1 else 0.

Record Receipt := {
  construction : Counts;
  extraction : Counts;
  active_drop : Counts;
  popped_drop : Counts;
  normal_drop : Counts
}.

Fixpoint sum_receipts
    (project : Receipt -> Counts) (children : list Receipt) : Counts :=
  match children with
  | [] => fun _ => 0
  | child :: rest =>
      fun event => project child event + sum_receipts project rest event
  end.

Section Recipes.

(** Local components EXCLUDE the explicitly modeled category constructor,
    destructor/extraction/loop/pool events and ChildArc operations.

    local_construction: actual flat/default construction.
    local_extraction: actual field handling and empty replacement operations.
    local_field_glue: actual flat field cleanup, excluding category-child
      destructors and automatic release of the listed ChildArcs.

    Counts may include NativeWork/NativeRecord/OwnedByte where the selected
    native contract needs them. These are not guesses from type names. *)
Variable local_construction : nat -> Counts.
Variable local_extraction : nat -> Counts.
Variable local_field_glue : nat -> Counts.

Definition recipe_algebra (tag : nat) (children : list Receipt) : Receipt :=
  let arity := length children in
  let x : Counts := fun event =>
      atom ExtractChildren event
      + local_extraction tag event
      + arity *
          (atom AllocateArc event
           + atom CheckArcOwner event
           + atom PushDropTask event)
      + sum_receipts construction children event in
  let glue : Counts := fun event =>
      local_field_glue tag event
      + arity * atom ReleaseFieldArc event in
  {|
    construction := fun event =>
      atom ConstructCategory event
      + local_construction tag event
      + arity * atom AllocateArc event
      + sum_receipts construction children event;

    extraction := x;

    active_drop := fun event =>
      atom EnterDestructor event
      + glue event
      + sum_receipts active_drop children event;

    popped_drop := fun event =>
      atom PopDropTask event
      + x event
      + sum_receipts popped_drop children event
      + atom EnterDestructor event
      + glue event
      + sum_receipts active_drop children event;

    normal_drop := fun event =>
      atom EnterDestructor event
      + atom AcquirePool event
      + x event
      + sum_receipts popped_drop children event
      + atom PopDropTask event
      + atom ReturnPool event
      + glue event
      + sum_receipts normal_drop children event
  |}.

Definition receipt (input : W.tree) : Receipt :=
  @W.recursive_fold Receipt recipe_algebra input.
Definition receipts (inputs : W.forest) : list Receipt :=
  @W.recursive_folds Receipt recipe_algebra inputs.

(** This is the complete additive recurrence, not a second traversal policy. *)
Theorem selected_constructor_recurrence :
  forall tag children,
  receipt (W.Node tag children) = recipe_algebra tag (receipts children).
Proof. reflexivity. Qed.

Theorem repeated_dependencies_are_counted_twice :
  forall project child event,
  sum_receipts project [child; child] event = 2 * project child event.
Proof.
  intros. cbn [sum_receipts]. lia.
Qed.

Theorem dependency_concatenation_is_additive :
  forall project left right event,
  sum_receipts project (left ++ right) event =
  sum_receipts project left event + sum_receipts project right event.
Proof.
  intros project left.
  induction left as [|head tail IH]; intros right event.
  - reflexivity.
  - cbn [sum_receipts app]. rewrite IH. lia.
Qed.

Definition active_bounded (value : Receipt) : Prop :=
  forall event, active_drop value event <= normal_drop value event.

Lemma sum_active_bounded :
  forall children,
  Forall active_bounded children ->
  forall event,
  sum_receipts active_drop children event <=
  sum_receipts normal_drop children event.
Proof.
  intros children H.
  induction H as [|child rest HC HR IH]; intro event.
  - reflexivity.
  - cbn [sum_receipts].
    specialize (HC event). specialize (IH event). lia.
Qed.

Lemma algebra_active_bounded :
  forall tag children,
  Forall active_bounded children ->
  active_bounded (recipe_algebra tag children).
Proof.
  intros tag children H event.
  pose proof (sum_active_bounded children H event) as HS.
  cbn [recipe_algebra active_drop normal_drop].
  lia.
Qed.

Theorem finite_recipes_and_forests_are_active_bounded :
  (forall input, active_bounded (receipt input)) /\
  (forall inputs, Forall active_bounded (receipts inputs)).
Proof.
  apply W.tree_forest_ind.
  - intros tag children IH.
    change (active_bounded (recipe_algebra tag (receipts children))).
    now apply algebra_active_bounded.
  - constructor.
  - intros head HH tail HT.
    change (Forall active_bounded (receipt head :: receipts tail)).
    constructor; assumption.
Qed.

Theorem active_cleanup_is_componentwise_bounded_by_normal :
  forall input event,
  active_drop (receipt input) event <= normal_drop (receipt input) event.
Proof.
  intros input event.
  exact (proj1 finite_recipes_and_forests_are_active_bounded input event).
Qed.

(** The existing generic worker computes the same finite-recipe algebra.
    This does not establish the concrete Rust descriptor-to-tree mapping. *)
Theorem existing_worklist_computes_receipt :
  forall input,
  @W.steps Receipt recipe_algebra
    (@W.State Receipt [W.VisitTree input] [])
    (@W.State Receipt [] [@W.TreeValue Receipt (receipt input)]).
Proof.
  intro input. unfold receipt.
  apply W.worklist_root_equivalence.
Qed.

End Recipes.

Definition all_events : list Event :=
  [ConstructCategory; EnterDestructor; ExtractChildren; HandleField;
   PushDropTask; PopDropTask; AllocateArc; CheckArcOwner; ReleaseFieldArc;
   AcquirePool; ReturnPool; NativeWork; NativeRecord; OwnedByte].

Fixpoint weighted_over
    (events : list Event) (weight : Event -> nat) (counts : Counts) : nat :=
  match events with
  | [] => 0
  | event :: rest =>
      weight event * counts event + weighted_over rest weight counts
  end.

Definition weighted (weight : Event -> nat) (counts : Counts) :=
  weighted_over all_events weight counts.

Lemma weighted_over_monotone :
  forall events weight left right,
  (forall event, left event <= right event) ->
  weighted_over events weight left <= weighted_over events weight right.
Proof.
  intros events.
  induction events as [|event rest IH]; intros weight left right H.
  - reflexivity.
  - cbn [weighted_over].
    pose proof (H event).
    pose proof (IH weight left right H).
    nia.
Qed.

Theorem weighted_componentwise_bound :
  forall weight left right,
  (forall event, left event <= right event) ->
  weighted weight left <= weighted weight right.
Proof.
  intros. unfold weighted. now apply weighted_over_monotone.
Qed.

(** Concrete logical projection used by reserve_binding_parts. OwnedByte is
    not base work: the existing reservation convention adds it exactly once.
    AcquirePool denotes the local vector header, not a new allocation. *)
Definition base_work_weight (event : Event) : nat :=
  match event with NativeRecord | OwnedByte => 0 | _ => 1 end.
Definition record_weight (event : Event) : nat :=
  match event with
  | ConstructCategory | AllocateArc | PushDropTask | AcquirePool | NativeRecord => 1
  | _ => 0
  end.
Definition byte_weight (event : Event) : nat :=
  match event with OwnedByte => 1 | _ => 0 end.
Definition logical_work_weight (event : Event) : nat :=
  base_work_weight event + byte_weight event.
Definition logical_unit_weight (event : Event) : nat :=
  4 * record_weight event + byte_weight event.

Theorem logical_work_projects_bytes_once :
  forall counts,
  weighted logical_work_weight counts =
    weighted base_work_weight counts + weighted byte_weight counts.
Proof.
  intro counts. unfold weighted, logical_work_weight.
  cbn [weighted_over all_events base_work_weight byte_weight].
  lia.
Qed.

Theorem logical_units_project_records_and_bytes :
  forall counts,
  weighted logical_unit_weight counts =
    4 * weighted record_weight counts + weighted byte_weight counts.
Proof.
  intro counts. unfold weighted, logical_unit_weight.
  cbn [weighted_over all_events record_weight byte_weight].
  lia.
Qed.

Section Reservation.

Variable local_construction : nat -> Counts.
Variable local_extraction : nat -> Counts.
Variable local_field_glue : nat -> Counts.

(** These mappings specify the selected logical accounting convention.
    For example, an Arc-allocation event can contribute one logical record,
    with four units assigned to that record by units_weight. They do not
    assert allocator byte size or an arbitrary native implementation bound. *)
Variable work_weight units_weight : Event -> nat.

Definition selected_receipt :=
  receipt local_construction local_extraction local_field_glue.

Definition work_parts (extra : nat) (input : W.tree) :=
  [extra;
   weighted work_weight (construction (selected_receipt input));
   weighted work_weight (normal_drop (selected_receipt input))].

Definition unit_parts (extra : nat) (input : W.tree) :=
  [extra;
   weighted units_weight (construction (selected_receipt input));
   weighted units_weight (normal_drop (selected_receipt input))].

Definition paid_dummy {A}
    cancelled ceiling available extra_work extra_units input
    (build : unit -> option A) :=
  preparation_action cancelled ceiling available
    (work_parts extra_work input) (unit_parts extra_units input) build.

Theorem reserved_normal_cleanup_also_covers_active :
  forall input,
  weighted work_weight (active_drop (selected_receipt input)) <=
    weighted work_weight (normal_drop (selected_receipt input)) /\
  weighted units_weight (active_drop (selected_receipt input)) <=
    weighted units_weight (normal_drop (selected_receipt input)).
Proof.
  intro input. split; apply weighted_componentwise_bound;
    intro event;
    apply active_cleanup_is_componentwise_bounded_by_normal.
Qed.

Theorem paid_dummy_success_uses_existing_reservation :
  forall A cancelled ceiling available extra_work extra_units input
    (build : unit -> option A) paid value,
  paid_dummy cancelled ceiling available extra_work extra_units input build =
    Accepted paid value ->
  cancelled = false /\ build tt = Some value /\
  total_charge (work_parts extra_work input) <= ceiling /\
  total_charge (unit_parts extra_units input) <= ceiling /\
  work_left paid + total_charge (work_parts extra_work input) =
    work_left available /\
  units_left paid + total_charge (unit_parts extra_units input) =
    units_left available.
Proof.
  intros. unfold paid_dummy in H.
  now apply preparation_success_is_the_same_paid_operation in H.
Qed.

Theorem cancelled_dummy_has_no_result :
  forall A ceiling available extra_work extra_units input
    (build : unit -> option A),
  paid_dummy true ceiling available extra_work extra_units input build =
    Refused available.
Proof.
  intros. apply preparation_cancel_has_no_result.
Qed.

Theorem dummy_overdraw_has_no_result :
  forall A ceiling available extra_work extra_units input
    (build : unit -> option A),
  reserve available
    (total_charge (work_parts extra_work input))
    (total_charge (unit_parts extra_units input)) = None ->
  paid_dummy false ceiling available extra_work extra_units input build =
    Refused available.
Proof.
  intros. unfold paid_dummy.
  now apply preparation_overdraw_has_no_result.
Qed.

Theorem dummy_callback_failure_retains_charge :
  forall A ceiling available extra_work extra_units input rw ru paid
    (build : unit -> option A),
  debit_all ceiling (work_parts extra_work input) = Some rw ->
  debit_all ceiling (unit_parts extra_units input) = Some ru ->
  reserve available
    (total_charge (work_parts extra_work input))
    (total_charge (unit_parts extra_units input)) = Some paid ->
  build tt = None ->
  paid_dummy false ceiling available extra_work extra_units input build =
    Refused paid.
Proof.
  intros. unfold paid_dummy.
  eapply preparation_callback_failure_keeps_the_charge; eassumption.
Qed.

End Reservation.

Print Assumptions selected_constructor_recurrence.
Print Assumptions repeated_dependencies_are_counted_twice.
Print Assumptions dependency_concatenation_is_additive.
Print Assumptions algebra_active_bounded.
Print Assumptions finite_recipes_and_forests_are_active_bounded.
Print Assumptions active_cleanup_is_componentwise_bounded_by_normal.
Print Assumptions existing_worklist_computes_receipt.
Print Assumptions weighted_componentwise_bound.
Print Assumptions logical_work_projects_bytes_once.
Print Assumptions logical_units_project_records_and_bytes.
Print Assumptions reserved_normal_cleanup_also_covers_active.
Print Assumptions paid_dummy_success_uses_existing_reservation.
Print Assumptions cancelled_dummy_has_no_result.
Print Assumptions dummy_overdraw_has_no_result.
Print Assumptions dummy_callback_failure_retains_charge.
End GeneratedDummyCleanupReservation.
