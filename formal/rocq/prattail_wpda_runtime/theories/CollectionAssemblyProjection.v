(** Collection-spec assembly: original discovery schedule and checked indices.

    Source: macros/src/gen/runtime/wpda_codegen/collection.rs,
    emit_collection_spec_table, insert_collection_spec_arm, mixfix_rep_slots,
    lookup_element_src_idx. This is an interface/relocation model, not a new
    classifier or collection recognizer. The classifier responses below are
    the original descriptors projected to discovered key/spec rows. Their
    correctness remains the existing classifier/reader correspondence duty.

    Crucial distinction: a conflicting duplicate freezes insertion, but the
    ORIGINAL worker continues later descriptor discovery. An observation error
    instead stops immediately. The label observation occurs only while no
    conflict has been recorded. Equal duplicate rows are idempotent. Semantic
    tables are modeled through CanonicalDispatchTable; diagnostic text and
    first-origin formatting are retained by source relocation and differential
    tests, not asserted equal by this projected model.

    Mathematical callback programs are specifications, never an allocated Rust
    trace or a second runtime algorithm. Rust keeps the original iterative
    loops. Source correspondence additionally requires original row copying,
    ordering, first-category lookup and descriptor-field construction. Existing
    resource admission is supplied by the enclosing owned assembly, not by a
    new grammar-size limit. Allocation, unwinding and global parser correctness
    are outside this narrow proof.
*)
From Stdlib Require Import List Bool Arith Lia.
From RuntimeGrammar Require Import CanonicalDispatchTable.
From PrattailWpdaRuntime Require Import PrefixCallbackFailure
  CollectionReaderProjection.
Import ListNotations.
Set Implicit Arguments.

Module CollectionAssemblyProjection.
Module F := PrefixCallbackFailure.PrefixCallbackFailure.

Section Assembly.
Context {Key Spec Rule Label : Type}.
Variable key_eqb : Key -> Key -> bool.
Variable spec_eqb : Spec -> Spec -> bool.
Definition Row := (Key * Spec)%type.

Record Accumulator := {
  table : list Row;
  conflicted : bool
}.

Definition discover (row : Row) (acc : Accumulator) : Accumulator :=
  if conflicted acc then acc else
  match insert_checked key_eqb spec_eqb row (table acc) with
  | Some rows => {| table := rows; conflicted := false |}
  | None => {| table := table acc; conflicted := true |}
  end.

Theorem recorded_conflict_freezes_insertions : forall row acc,
  conflicted acc = true -> discover row acc = acc.
Proof. intros row acc H; unfold discover; now rewrite H. Qed.

Theorem first_collision_retains_prior_table : forall row acc,
  conflicted acc = false ->
  insert_checked key_eqb spec_eqb row (table acc) = None ->
  discover row acc = {| table := table acc; conflicted := true |}.
Proof. intros row acc H I; unfold discover; now rewrite H, I. Qed.

Theorem successful_insertion_reuses_original_checked_table : forall row acc rows,
  conflicted acc = false ->
  insert_checked key_eqb spec_eqb row (table acc) = Some rows ->
  discover row acc = {| table := rows; conflicted := false |}.
Proof. intros row acc rows H I; unfold discover; now rewrite H, I. Qed.

(** The original three classifier phases and lazy diagnostic observation.
    Coordinates/row values are arguments of requests, not lossy event tags. *)
Inductive Request :=
| InfixRepetitions (rule : Rule)
| CollectionLiteral (rule : Rule)
| BinderCollections (rule : Rule)
| OriginLabel (row : Row).

Definition Response (request : Request) : Type := match request with
| InfixRepetitions _ | BinderCollections _ => list Row
| CollectionLiteral _ => option Row
| OriginLabel _ => Label
end.

Definition Program := @F.Program Request Response Accumulator.
Definition ret (acc : Accumulator) : Program :=
  @F.Return Request Response Accumulator acc.
Definition call (request : Request) (next : Response request -> Program) : Program :=
  @F.Call Request Response Accumulator request next.

Definition row_program (row : Row) (acc : Accumulator)
    (next : Accumulator -> Program) : Program :=
  if conflicted acc then next acc else
  call (OriginLabel row) (fun _ => next (discover row acc)).

Fixpoint rows_program (rows : list Row) (acc : Accumulator)
    (next : Accumulator -> Program) : Program := match rows with
| [] => next acc
| row :: rest => row_program row acc
    (fun after => rows_program rest after next)
end.

Definition after_collection (rule : Rule) (acc : Accumulator)
    (collection : option Row) (next : Accumulator -> Program) : Program :=
  match collection with
  | Some row => row_program row acc next
  | None => call (BinderCollections rule)
      (fun rows => rows_program rows acc next)
  end.

Definition rule_program (rule : Rule) (acc : Accumulator)
    (next : Accumulator -> Program) : Program :=
  call (InfixRepetitions rule) (fun rows =>
    rows_program rows acc (fun after =>
      call (CollectionLiteral rule) (fun collection =>
        after_collection rule after collection next))).

Fixpoint rules_program (rules : list Rule) (acc : Accumulator) : Program :=
  match rules with
  | [] => ret acc
  | rule :: rest => rule_program rule acc (fun after => rules_program rest after)
  end.

Theorem conflict_suppresses_only_label_and_insertion : forall row acc next,
  conflicted acc = true -> row_program row acc next = next acc.
Proof. intros row acc next H; unfold row_program; now rewrite H. Qed.

Theorem conflict_still_visits_remaining_discovery_phases : forall rows acc next,
  conflicted acc = true -> rows_program rows acc next = next acc.
Proof.
  induction rows as [|row rows IH]; intros acc next H; [reflexivity|].
  cbn [rows_program]. rewrite conflict_suppresses_only_label_and_insertion by exact H.
  now apply IH.
Qed.

Theorem label_precedes_each_attempted_checked_insertion : forall row acc next,
  conflicted acc = false ->
  row_program row acc next =
    call (OriginLabel row) (fun _ => next (discover row acc)).
Proof. intros row acc next H; unfold row_program; now rewrite H. Qed.

Theorem collection_success_skips_binder_classifier : forall rule acc row next,
  after_collection rule acc (Some row) next = row_program row acc next.
Proof. reflexivity. Qed.

Theorem collection_absence_requests_binder_classifier : forall rule acc next,
  after_collection rule acc None next =
    call (BinderCollections rule) (fun rows => rows_program rows acc next).
Proof. reflexivity. Qed.

Theorem each_rule_starts_with_original_infix_probe : forall rule acc next,
  rule_program rule acc next =
    call (InfixRepetitions rule) (fun rows =>
      rows_program rows acc (fun after =>
        call (CollectionLiteral rule) (fun collection =>
          after_collection rule after collection next))).
Proof. reflexivity. Qed.

Theorem existing_conflict_does_not_skip_next_rule : forall rule rest acc,
  rules_program (rule :: rest) acc =
    call (InfixRepetitions rule) (fun rows =>
      rows_program rows acc (fun after =>
        call (CollectionLiteral rule) (fun collection =>
          after_collection rule after collection
            (fun final => rules_program rest final)))).
Proof. reflexivity. Qed.

(** The generic checked callback law includes labels as well as classifiers.
    Thus callback refusal after an already recorded conflict remains refusal,
    not a successful empty table and not continuation past that callback. *)
Definition callback_failure_stops := @F.first_error_skips_any_continuation.
Definition callback_failure_has_exact_prefix := @F.failed_run_has_exact_first_failure.
Definition all_ok_preserves_original_program := @F.all_ok_exact_original.
Definition checked_reader_substitution := @F.callback_reader_substitution.

Inductive Publication := Rows (rows : list Row) | Conflict.
Definition finish (acc : Accumulator) : Publication :=
  if conflicted acc then Conflict else Rows (table acc).

Theorem recorded_conflict_cannot_publish_partial_table : forall acc,
  conflicted acc = true -> finish acc = Conflict.
Proof. intros acc H; unfold finish; now rewrite H. Qed.

Theorem complete_nonconflicting_result_is_exact_table : forall acc,
  conflicted acc = false -> finish acc = Rows (table acc).
Proof. intros acc H; unfold finish; now rewrite H. Qed.
End Assembly.

(** These are the exact source integer encodings, not a grammar complexity cap.
    Category/rule indices are checked when visited, element indices only after
    first-position lookup succeeds, and mixfix-part indices only for selected
    repetition parts. Absence stays absence; no whole-roster numeric preflight
    is introduced by this model. *)
Definition checked_index maximum value :=
  if value <=? maximum then Some value else None.
Definition checked_u16 := checked_index 65535.
Definition checked_u8 := checked_index 255.

Theorem checked_index_preserves_exact_representable_coordinate : forall maximum value,
  value <= maximum -> checked_index maximum value = Some value.
Proof. intros maximum value H; apply Nat.leb_le in H; unfold checked_index; now rewrite H. Qed.

Theorem checked_index_refuses_unrepresentable_coordinate : forall maximum value,
  maximum < value -> checked_index maximum value = None.
Proof. intros maximum value H; apply Nat.leb_gt in H; unfold checked_index; now rewrite H. Qed.

Theorem checked_index_never_wraps : forall maximum value encoded,
  checked_index maximum value = Some encoded -> encoded = value /\ value <= maximum.
Proof.
  intros maximum value encoded H; unfold checked_index in H.
  destruct (value <=? maximum) eqn:B; [|discriminate].
  inversion H; subst. split; [reflexivity|now apply Nat.leb_le].
Qed.

Definition checked_optional_index maximum index :=
  match index with None => Some None
  | Some value => option_map (@Some nat) (checked_index maximum value)
  end.
Theorem missing_element_category_is_not_category_zero : forall maximum,
  checked_optional_index maximum None = Some None.
Proof. reflexivity. Qed.

Print Assumptions recorded_conflict_freezes_insertions.
Print Assumptions first_collision_retains_prior_table.
Print Assumptions successful_insertion_reuses_original_checked_table.
Print Assumptions conflict_suppresses_only_label_and_insertion.
Print Assumptions conflict_still_visits_remaining_discovery_phases.
Print Assumptions label_precedes_each_attempted_checked_insertion.
Print Assumptions collection_success_skips_binder_classifier.
Print Assumptions collection_absence_requests_binder_classifier.
Print Assumptions each_rule_starts_with_original_infix_probe.
Print Assumptions existing_conflict_does_not_skip_next_rule.
Print Assumptions callback_failure_stops.
Print Assumptions callback_failure_has_exact_prefix.
Print Assumptions all_ok_preserves_original_program.
Print Assumptions checked_reader_substitution.
Print Assumptions recorded_conflict_cannot_publish_partial_table.
Print Assumptions complete_nonconflicting_result_is_exact_table.
Print Assumptions checked_index_preserves_exact_representable_coordinate.
Print Assumptions checked_index_refuses_unrepresentable_coordinate.
Print Assumptions checked_index_never_wraps.
Print Assumptions missing_element_category_is_not_category_zero.
End CollectionAssemblyProjection.
