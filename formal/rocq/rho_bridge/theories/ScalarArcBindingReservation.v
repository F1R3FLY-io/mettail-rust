(** Local accounting for required Arc and optional Arc category fields.

    Source boundary: iterative_drop.rs's regular scalar arms replace required
    fields with fresh dummy Arcs, but optional fields use take and leave None.
    Only Arc::into_inner's owned result is pushed. Clone handles remain pinned
    by the source borrow throughout normal cleanup; Open/Close fields wrap
    newly produced owned category results. Counts use the existing logical
    event projection, not allocator bytes, CPU time, or semantic Cost grades.

    The local facts exclude the parent constructor/root base, worker and slot
    transitions, and the child's already-paid output allowance. Required
    fields separately add the selected dummy's construction and normal cleanup.
    Optional fields have no dummy dependency. The available empty-pool premise
    and normal-cleanup boundary are inherited from the imported models.

    Assembly contract: perform every fallible take into BARE category locals
    first. Only after all takes succeed, construct every Arc/Option wrapper and
    the parent, with no fallible callback before publication. The imported
    assembly_transfers_existing_child_credits theorem transfers the child
    allowance without paying it again. These arithmetic facts do not prove
    that a Rust emitter obeys this ordering; its call sites require review.
    In particular these field facts must not stand in for standalone wrapper
    cleanup if a new fallible boundary is introduced after wrapping. Allocator
    failures, unwind, TLS teardown and concurrent source destruction are not
    modeled. *)
From Stdlib Require Import List Arith Lia.
From RhoBridge Require Import
  GeneratedDummyCleanupReservation GeneratedBindingOutputReservation
  FlatBindingLeafReservation.
Import ListNotations.

Module ScalarArcBindingReservation.
Module D := GeneratedDummyCleanupReservation.
Module O := GeneratedBindingOutputReservation.
Module F := FlatBindingLeafReservation.

Inductive Mode := CloneMode | OpenCloseMode.

Definition fresh_wrapper mode :=
  match mode with CloneMode => false | OpenCloseMode => true end.

(** A cloned Arc handle has one logical output record but no referent
    allocation. A fresh owned wrapper uses the existing AllocateArc event. *)
Definition wrapper_construction mode : D.Counts := fun event =>
  match mode with
  | CloneMode => D.atom D.NativeWork event + D.atom D.NativeRecord event
  | OpenCloseMode => D.atom D.AllocateArc event
  end.

Definition owned_push mode : D.Counts := fun event =>
  match mode with
  | CloneMode => 0
  | OpenCloseMode => D.atom D.PushDropTask event
  end.

Theorem wrapper_construction_agrees_with_flat_contract : forall mode event,
  wrapper_construction mode event + D.arc_release event =
  F.arc_wrapper_events (fresh_wrapper mode) event.
Proof.
  intros [] event; unfold wrapper_construction, fresh_wrapper,
    D.arc_release, F.arc_wrapper_events; lia.
Qed.

(** The release/check pair is for the replacement Arc left in the parent.
    The original Arc's into_inner test is a separate CheckArcOwner event. *)
Definition required_cleanup mode : D.Counts := fun event =>
  D.atom D.HandleField event + D.atom D.AllocateArc event +
  D.atom D.CheckArcOwner event + D.arc_release event + owned_push mode event.

Definition required_local mode : D.Counts := fun event =>
  wrapper_construction mode event + required_cleanup mode event.

Definition selected_dummy (receipt : D.Receipt) : D.Counts := fun event =>
  D.construction receipt event + D.normal_drop receipt event.

Definition required_total mode receipt : D.Counts := fun event =>
  required_local mode event + selected_dummy receipt event.

(** Option shell accounting is independent of the category child: one output
    shell, a replacement None from take, the discarded taken Option shell,
    and the remaining None field's cleanup. Some additionally creates an Arc
    wrapper and executes the original Arc's ownership check. No replacement
    dummy Arc survives in an optional field. *)
Definition option_shell : D.Counts := fun event =>
  D.atom D.NativeWork event + D.atom D.NativeRecord event.

Definition optional_construction mode (present : bool) : D.Counts := fun event =>
  option_shell event +
  if present then wrapper_construction mode event else 0.

Definition optional_cleanup mode (present : bool) : D.Counts := fun event =>
  D.atom D.HandleField event + option_shell event +
  D.atom D.NativeWork event + D.atom D.NativeWork event +
  if present then D.atom D.CheckArcOwner event + owned_push mode event else 0.

Definition optional_local mode present : D.Counts := fun event =>
  optional_construction mode present event + optional_cleanup mode present event.

Theorem required_local_projection : forall mode,
  D.weighted D.base_work_weight (required_local mode) =
    (match mode with CloneMode => 6 | OpenCloseMode => 7 end) /\
  D.weighted D.record_weight (required_local mode) =
    (match mode with CloneMode => 2 | OpenCloseMode => 3 end) /\
  D.weighted D.byte_weight (required_local mode) = 0.
Proof. intros []; repeat split; reflexivity. Qed.

Theorem optional_some_local_projection : forall mode,
  D.weighted D.base_work_weight (optional_local mode true) =
    (match mode with CloneMode => 7 | OpenCloseMode => 8 end) /\
  D.weighted D.record_weight (optional_local mode true) =
    (match mode with CloneMode => 3 | OpenCloseMode => 4 end) /\
  D.weighted D.byte_weight (optional_local mode true) = 0.
Proof. intros []; repeat split; reflexivity. Qed.

Theorem optional_none_local_projection : forall mode,
  D.weighted D.base_work_weight (optional_local mode false) = 5 /\
  D.weighted D.record_weight (optional_local mode false) = 2 /\
  D.weighted D.byte_weight (optional_local mode false) = 0.
Proof. intros []; repeat split; reflexivity. Qed.

(** Only the scalar projections are combined here; reservation still uses
    the imported event weights and the existing record/byte convention. *)
Lemma weighted_add : forall weight left right,
  D.weighted weight (fun event => left event + right event) =
  D.weighted weight left + D.weighted weight right.
Proof.
  intros weight left right. unfold D.weighted.
  induction D.all_events as [|event rest IH]; cbn [D.weighted_over]; nia.
Qed.

Theorem required_total_projection : forall mode receipt,
  D.weighted D.base_work_weight (required_total mode receipt) =
    (match mode with CloneMode => 6 | OpenCloseMode => 7 end) +
      D.weighted D.base_work_weight (selected_dummy receipt) /\
  D.weighted D.record_weight (required_total mode receipt) =
    (match mode with CloneMode => 2 | OpenCloseMode => 3 end) +
      D.weighted D.record_weight (selected_dummy receipt) /\
  D.weighted D.byte_weight (required_total mode receipt) =
      D.weighted D.byte_weight (selected_dummy receipt).
Proof.
  intros mode receipt. unfold required_total. rewrite !weighted_add.
  destruct (required_local_projection mode) as [HW [HR HB]].
  rewrite HW, HR, HB. repeat split; lia.
Qed.

Theorem selected_dummy_is_construction_plus_normal : forall weight receipt,
  D.weighted weight (selected_dummy receipt) =
  D.weighted weight (D.construction receipt) +
  D.weighted weight (D.normal_drop receipt).
Proof. intros. unfold selected_dummy. apply weighted_add. Qed.

Definition parent_base event := D.atom D.ConstructCategory event + O.root_base event.

Theorem excluded_parent_base_projection :
  D.weighted D.base_work_weight parent_base = 6 /\
  D.weighted D.record_weight parent_base = 2 /\
  D.weighted D.byte_weight parent_base = 0.
Proof. repeat split; reflexivity. Qed.

(** Instantiation of the existing actual-output local algebra, not a new
    output traversal. Its recursive child-credit sum remains untouched. *)
Theorem required_field_instantiates_output_local :
  forall dc dx dg mode dummy tag event,
  O.local_credit dc dx dg (fun _ => [dummy])
    (fun _ => wrapper_construction mode) (fun _ => required_cleanup mode)
    tag event =
  parent_base event + required_total mode (D.receipt dc dx dg dummy) event.
Proof.
  intros. unfold O.local_credit, O.local_root, O.replacements, O.sum_counts,
    O.dummy_receipt, parent_base, required_total, required_local, selected_dummy.
  cbn [fold_right]. lia.
Qed.

Theorem optional_field_instantiates_output_local :
  forall dc dx dg mode present tag event,
  O.local_credit dc dx dg (fun _ => [])
    (fun _ => optional_construction mode present)
    (fun _ => optional_cleanup mode present) tag event =
  parent_base event + optional_local mode present event.
Proof.
  intros. unfold O.local_credit, O.local_root, O.replacements, O.sum_counts,
    parent_base, optional_local. cbn [fold_right]. lia.
Qed.

Print Assumptions wrapper_construction_agrees_with_flat_contract.
Print Assumptions required_local_projection.
Print Assumptions optional_some_local_projection.
Print Assumptions optional_none_local_projection.
Print Assumptions weighted_add.
Print Assumptions required_total_projection.
Print Assumptions selected_dummy_is_construction_plus_normal.
Print Assumptions excluded_parent_base_projection.
Print Assumptions required_field_instantiates_output_local.
Print Assumptions optional_field_instantiates_output_local.
End ScalarArcBindingReservation.
