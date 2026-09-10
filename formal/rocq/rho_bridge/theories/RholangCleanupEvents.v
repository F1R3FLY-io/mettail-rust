(** Event refinement of the existing normal cleanup worklist.

    The source-derived wrapper annotation in RholangConstructionCleanup is
    refined here into explicit destructor-entry, child-table, scheduling and
    loop-pop events. Clearing recursive fields produces a shell with no child
    Pars; its generated destructor therefore schedules nothing. Source owners
    remain the pinned Par::drop and dismantle_in_place, not a new runtime walk.

    These event traces cover the admitted scalar/append/Fresh construction
    image and normal execution. They do not model panic unwinding, allocator
    internals, ordered-map destruction or unrelated schema families. *)
From Stdlib Require Import List Arith Lia.
From RhoBridge Require Import RholangTargetConstruction RholangDeepConstructionSize
  RholangConstructionCleanup RholangInitialGraphInterpretation RholangInitialGraphMachine.
Import ListNotations.

Inductive CleanupAxis := LoopPops | DestructorEntries | ChildTableCalls | ScheduledPars.
Inductive CleanupEvent := PopPending | EnterDestructor | CallChildTable | ScheduleChildren (count : nat).

Definition cleanup_event_measure (axis : CleanupAxis) (event : CleanupEvent) : nat :=
  match axis, event with
  | LoopPops, PopPending | DestructorEntries, EnterDestructor | ChildTableCalls, CallChildTable => 1
  | ScheduledPars, ScheduleChildren count => count
  | _, _ => 0
  end.
Definition trace_measure axis events := sum_sizes (cleanup_event_measure axis) events.
Definition emptied_value (value : Value) : Value := MakeValue [] (summary_of value).
Definition extraction_events (value : Value) :=
  [CallChildTable; ScheduleChildren (List.length (direct_children value))].
Definition destructor_entry_events (value : Value) := EnterDestructor :: extraction_events value.
Definition loop_iteration_events (value : Value) :=
  PopPending :: (extraction_events value ++ destructor_entry_events (emptied_value value)).

Theorem emptied_shell_has_no_cleanup_work : forall value,
  direct_children (emptied_value value) = [] /\
  CleanupSteps 0 0 (rev (direct_children (emptied_value value))).
Proof. intro value. split; [reflexivity|constructor]. Qed.

Inductive CleanupLoopTrace : list Value -> list CleanupEvent -> Prop :=
| CleanupTraceDone : CleanupLoopTrace [] []
| CleanupTraceNext : forall value rest tail,
    CleanupLoopTrace (rev (direct_children value) ++ rest) tail ->
    CleanupLoopTrace (value :: rest) (loop_iteration_events value ++ tail).

Definition expected_loop_measure axis pending :=
  let mass := forest_mass pending in
  match axis with
  | LoopPops | DestructorEntries => mass
  | ChildTableCalls => 2 * mass
  | ScheduledPars => mass - List.length pending
  end.

Lemma loop_iteration_event_measure : forall axis value,
  trace_measure axis (loop_iteration_events value) =
    match axis with
    | LoopPops | DestructorEntries => 1
    | ChildTableCalls => 2
    | ScheduledPars => List.length (direct_children value)
    end.
Proof.
  intros axis value.
  change (trace_measure axis
    [PopPending; CallChildTable; ScheduleChildren (List.length (direct_children value));
     EnterDestructor; CallChildTable; ScheduleChildren 0] =
    match axis with
    | LoopPops | DestructorEntries => 1
    | ChildTableCalls => 2
    | ScheduledPars => List.length (direct_children value)
    end).
  destruct axis; cbn [trace_measure sum_sizes fold_right cleanup_event_measure]; lia.
Qed.

Lemma loop_event_step_conserves_expected_measure : forall axis value rest,
  trace_measure axis (loop_iteration_events value) +
    expected_loop_measure axis (rev (direct_children value) ++ rest) =
    expected_loop_measure axis (value :: rest).
Proof.
  intros axis value rest.
  pose proof (cleanup_step_consumes_exactly_one_owned_occurrence
    (value :: rest) (rev (direct_children value) ++ rest) eq_refl) as HM.
  pose proof (forest_mass_bounds_pending_length (rev (direct_children value) ++ rest)) as HL.
  rewrite length_app, length_rev in HL.
  rewrite loop_iteration_event_measure.
  unfold expected_loop_measure. rewrite length_app, length_rev. cbn [List.length].
  destruct axis; lia.
Qed.

Theorem cleanup_loop_events_have_exact_counts : forall pending events,
  CleanupLoopTrace pending events -> forall axis,
  trace_measure axis events = expected_loop_measure axis pending.
Proof.
  intros pending events H. induction H as [|value rest tail HT IH]; intro axis;
    [destruct axis; reflexivity|].
  unfold trace_measure at 1. rewrite sum_sizes_app.
  change (trace_measure axis (loop_iteration_events value) + trace_measure axis tail =
    expected_loop_measure axis (value :: rest)).
  rewrite IH. apply loop_event_step_conserves_expected_measure.
Qed.

Theorem every_checked_cleanup_execution_has_an_event_trace : forall count capacity pending,
  CleanupSteps count capacity pending -> exists events, CleanupLoopTrace pending events.
Proof.
  intros count capacity pending H. induction H as [capacity|steps capacity pending next HL HS HT IH].
  - exists []. constructor.
  - destruct pending as [|value rest]; [discriminate|].
    inversion HS; subst next. destruct IH as [events HE].
    exists (loop_iteration_events value ++ events). now constructor.
Qed.

Inductive NormalDropTrace : Value -> list CleanupEvent -> Prop :=
| NormalDropEvents : forall value events,
    CleanupLoopTrace (rev (direct_children value)) events ->
    NormalDropTrace value (destructor_entry_events value ++ events).

Definition expected_root_measure axis value :=
  let descendants := value_owned_count DescendantPars value in
  match axis with
  | LoopPops | ScheduledPars => descendants
  | DestructorEntries => S descendants
  | ChildTableCalls => S (2 * descendants)
  end.

Theorem normal_drop_events_have_exact_counts : forall value events,
  NormalDropTrace value events -> forall axis,
  trace_measure axis events = expected_root_measure axis value.
Proof.
  intros value events H. destruct H as [value events HT]. intro axis.
  unfold trace_measure at 1. rewrite sum_sizes_app.
  change (trace_measure axis (destructor_entry_events value) + trace_measure axis events =
    expected_root_measure axis value).
  rewrite (cleanup_loop_events_have_exact_counts _ _ HT).
  unfold expected_loop_measure, expected_root_measure.
  assert (HM : forest_mass (rev (direct_children value)) = value_owned_count DescendantPars value).
  { unfold forest_mass. rewrite sum_sizes_rev. symmetry.
    apply value_descendants_are_the_direct_child_forest. }
  rewrite HM, length_rev.
  pose proof (forest_mass_bounds_pending_length (direct_children value)) as HL.
  rewrite <- value_descendants_are_the_direct_child_forest in HL.
  destruct axis; cbn [trace_measure destructor_entry_events extraction_events sum_sizes
    fold_right cleanup_event_measure]; lia.
Qed.

Theorem every_value_has_a_normal_drop_event_trace : forall value,
  exists events, NormalDropTrace value events.
Proof.
  intro value. destruct (every_checked_cleanup_execution_has_an_event_trace _ _ _
    (normal_par_drop_has_exact_descendant_worklist value)) as [events HE].
  exists (destructor_entry_events value ++ events). now constructor.
Qed.

(** Ordinary New field-drop glue invokes normal Par destruction separately for
    each body and injection root. It does not merge those roots into a shared
    cleanup loop. The additive counts below do not depend on root order. *)
Inductive SeparateRootDropTrace : list Value -> list CleanupEvent -> Prop :=
| SeparateRootsDone : SeparateRootDropTrace [] []
| SeparateRootsNext : forall value rest first tail,
    NormalDropTrace value first -> SeparateRootDropTrace rest tail ->
    SeparateRootDropTrace (value :: rest) (first ++ tail).

Theorem separate_root_drop_events_are_additive : forall values events,
  SeparateRootDropTrace values events -> forall axis,
  trace_measure axis events = sum_sizes (expected_root_measure axis) values.
Proof.
  intros values events H. induction H as [|value rest first tail HF HT IH]; intro axis; [reflexivity|].
  unfold trace_measure at 1. rewrite sum_sizes_app.
  change (trace_measure axis first + trace_measure axis tail =
    expected_root_measure axis value + sum_sizes (expected_root_measure axis) rest).
  rewrite (normal_drop_events_have_exact_counts _ _ HF), IH. reflexivity.
Qed.

Theorem every_root_forest_has_a_separate_drop_trace : forall values,
  exists events, SeparateRootDropTrace values events.
Proof.
  induction values as [|value rest [tail HT]].
  - exists []. constructor.
  - destruct (every_value_has_a_normal_drop_event_trace value) as [first HF].
    exists (first ++ tail). now constructor.
Qed.

Definition expected_forest_measure axis values :=
  let mass := forest_mass values in
  match axis with
  | LoopPops | ScheduledPars => mass - List.length values
  | DestructorEntries => mass
  | ChildTableCalls => 2 * mass - List.length values
  end.

Theorem separate_root_drop_receipt_has_exact_counts : forall values axis,
  sum_sizes (expected_root_measure axis) values = expected_forest_measure axis values.
Proof.
  induction values as [|value rest IH]; intro axis; [destruct axis; reflexivity|].
  change (expected_root_measure axis value + sum_sizes (expected_root_measure axis) rest =
    expected_forest_measure axis (value :: rest)).
  rewrite IH. unfold expected_root_measure, expected_forest_measure.
  change ((match axis with
    | LoopPops | ScheduledPars => value_owned_count DescendantPars value
    | DestructorEntries => S (value_owned_count DescendantPars value)
    | ChildTableCalls => S (2 * value_owned_count DescendantPars value) end) +
    (match axis with
    | LoopPops | ScheduledPars => forest_mass rest - List.length rest
    | DestructorEntries => forest_mass rest
    | ChildTableCalls => 2 * forest_mass rest - List.length rest end) =
    match axis with
    | LoopPops | ScheduledPars => S (value_owned_count DescendantPars value) + forest_mass rest - S (List.length rest)
    | DestructorEntries => S (value_owned_count DescendantPars value) + forest_mass rest
    | ChildTableCalls => 2 * (S (value_owned_count DescendantPars value) + forest_mass rest) - S (List.length rest)
    end).
  pose proof (forest_mass_bounds_pending_length rest). destruct axis; lia.
Qed.

Definition new_or_leaf_head (head : Head) : Prop :=
  match head with MakeHead kind children =>
    match kind with NewHead _ _ _ => True | _ => children = [] end
  end.
Definition only_new_heads_have_children (value : Value) :=
  Forall new_or_leaf_head (heads_of value).

Lemma embedded_immediate_roots_are_zero : forall children,
  sum_sizes (fun child => embed_count ImmediateNewRoots
    (RholangBoundMetadata.metadata_length child) (value_owned_count ImmediateNewRoots child)) children = 0.
Proof.
  induction children as [|child rest IH]; [reflexivity|].
  change (0 + sum_sizes (fun child => embed_count ImmediateNewRoots
    (RholangBoundMetadata.metadata_length child) (value_owned_count ImmediateNewRoots child)) rest = 0).
  exact IH.
Qed.

Lemma head_immediate_roots_are_exact : forall head,
  new_or_leaf_head head -> head_deep_count ImmediateNewRoots head = List.length (head_children head).
Proof.
  intros [kind children] H. cbn [head_deep_count]. rewrite embedded_immediate_roots_are_zero.
  destruct kind; cbn [new_or_leaf_head] in H; try subst children;
    cbn [head_children head_owned_count fresh_owned_count List.length]; lia.
Qed.

Lemma child_forest_length_is_additive : forall heads,
  List.length (flat_map head_children heads) = sum_sizes (fun head => List.length (head_children head)) heads.
Proof.
  induction heads as [|head rest IH]; [reflexivity|].
  cbn [flat_map]. rewrite length_app, IH. reflexivity.
Qed.

Theorem immediate_new_roots_match_the_child_forest : forall value,
  only_new_heads_have_children value ->
  value_owned_count ImmediateNewRoots value = List.length (direct_children value).
Proof.
  intros [heads summary] H. unfold only_new_heads_have_children in H.
  unfold direct_children. cbn [heads_of value_owned_count] in *.
  rewrite child_forest_length_is_additive. apply sum_sizes_extensional.
  intros head HH. apply head_immediate_roots_are_exact.
  exact (proj1 (Forall_forall _ _) H head HH).
Qed.

Theorem construction_image_has_only_new_child_heads : forall tree,
  only_new_heads_have_children (tree_denotation tree).
Proof.
  induction tree as [scalar|lhs HL rhs HR|descriptor body HB injections].
  - destruct scalar; cbn [only_new_heads_have_children tree_denotation scalar_denotation
      empty boolean text wildcard singleton heads_of new_or_leaf_head]; repeat constructor.
  - change (Forall new_or_leaf_head
      (heads_of (tree_denotation lhs) ++ heads_of (tree_denotation rhs))).
    apply Forall_app. split; assumption.
  - unfold only_new_heads_have_children. cbn [tree_denotation fresh_denotation singleton heads_of].
    repeat constructor.
Qed.

(** Only disposal of append's input owners is counted here, not clone-internal
    work or eventual cleanup of the retained output. In helper order: temporary
    cloned-left heads, temporary moved-right heads, emptied right receiver;
    then the direct adapter's owned left value. *)
Inductive AppendOwnedCleanupTrace : Value -> Value -> list CleanupEvent -> Prop :=
| AppendOwnedEvents : forall lhs rhs left_heads right_heads right_shell left_value,
    SeparateRootDropTrace (direct_children lhs) left_heads ->
    SeparateRootDropTrace (direct_children rhs) right_heads ->
    NormalDropTrace (emptied_value rhs) right_shell ->
    NormalDropTrace lhs left_value ->
    AppendOwnedCleanupTrace lhs rhs (left_heads ++ (right_heads ++ (right_shell ++ left_value))).

Definition expected_append_cleanup_measure axis lhs rhs :=
  let left_descendants := value_owned_count DescendantPars lhs in
  let right_descendants := value_owned_count DescendantPars rhs in
  let left_roots := value_owned_count ImmediateNewRoots lhs in
  let right_roots := value_owned_count ImmediateNewRoots rhs in
  match axis with
  | LoopPops | ScheduledPars => 2 * left_descendants + right_descendants - left_roots - right_roots
  | DestructorEntries => 2 + 2 * left_descendants + right_descendants
  | ChildTableCalls => 2 + 4 * left_descendants + 2 * right_descendants - left_roots - right_roots
  end.

Theorem append_owned_cleanup_events_have_exact_counts : forall lhs rhs events,
  only_new_heads_have_children lhs -> only_new_heads_have_children rhs ->
  AppendOwnedCleanupTrace lhs rhs events -> forall axis,
  trace_measure axis events = expected_append_cleanup_measure axis lhs rhs.
Proof.
  intros lhs rhs events HL HR H. destruct H as [lhs rhs left_heads right_heads right_shell left_value Hleft Hright Hshell Hvalue].
  intro axis. unfold trace_measure at 1. rewrite !sum_sizes_app.
  change (trace_measure axis left_heads + (trace_measure axis right_heads +
    (trace_measure axis right_shell + trace_measure axis left_value)) =
    expected_append_cleanup_measure axis lhs rhs).
  rewrite (separate_root_drop_events_are_additive _ _ Hleft),
    (separate_root_drop_events_are_additive _ _ Hright),
    (normal_drop_events_have_exact_counts _ _ Hshell),
    (normal_drop_events_have_exact_counts _ _ Hvalue),
    !separate_root_drop_receipt_has_exact_counts.
  unfold expected_forest_measure.
  rewrite <- !value_descendants_are_the_direct_child_forest,
    <- (immediate_new_roots_match_the_child_forest lhs HL),
    <- (immediate_new_roots_match_the_child_forest rhs HR).
  pose proof (forest_mass_bounds_pending_length (direct_children lhs)) as Hleft_bound.
  pose proof (forest_mass_bounds_pending_length (direct_children rhs)) as Hright_bound.
  rewrite <- value_descendants_are_the_direct_child_forest,
    <- (immediate_new_roots_match_the_child_forest lhs HL) in Hleft_bound.
  rewrite <- value_descendants_are_the_direct_child_forest,
    <- (immediate_new_roots_match_the_child_forest rhs HR) in Hright_bound.
  unfold expected_root_measure, expected_append_cleanup_measure.
  destruct axis; cbn [emptied_value value_owned_count sum_sizes fold_right]; lia.
Qed.

Theorem every_append_has_an_owned_cleanup_trace : forall lhs rhs,
  exists events, AppendOwnedCleanupTrace lhs rhs events.
Proof.
  intros lhs rhs.
  destruct (every_root_forest_has_a_separate_drop_trace (direct_children lhs)) as [left_heads HL].
  destruct (every_root_forest_has_a_separate_drop_trace (direct_children rhs)) as [right_heads HR].
  destruct (every_value_has_a_normal_drop_event_trace (emptied_value rhs)) as [right_shell HS].
  destruct (every_value_has_a_normal_drop_event_trace lhs) as [left_value HV].
  exists (left_heads ++ (right_heads ++ (right_shell ++ left_value))). now constructor.
Qed.

Corollary constructed_append_cleanup_is_exact : forall lhs rhs events,
  AppendOwnedCleanupTrace (tree_denotation lhs) (tree_denotation rhs) events -> forall axis,
  trace_measure axis events = expected_append_cleanup_measure axis (tree_denotation lhs) (tree_denotation rhs).
Proof.
  intros lhs rhs events H axis. apply append_owned_cleanup_events_have_exact_counts;
    try apply construction_image_has_only_new_child_heads; assumption.
Qed.

Print Assumptions emptied_shell_has_no_cleanup_work.
Print Assumptions cleanup_loop_events_have_exact_counts.
Print Assumptions every_checked_cleanup_execution_has_an_event_trace.
Print Assumptions normal_drop_events_have_exact_counts.
Print Assumptions every_value_has_a_normal_drop_event_trace.
Print Assumptions separate_root_drop_events_are_additive.
Print Assumptions every_root_forest_has_a_separate_drop_trace.
Print Assumptions separate_root_drop_receipt_has_exact_counts.
Print Assumptions immediate_new_roots_match_the_child_forest.
Print Assumptions construction_image_has_only_new_child_heads.
Print Assumptions append_owned_cleanup_events_have_exact_counts.
Print Assumptions every_append_has_an_owned_cleanup_trace.
Print Assumptions constructed_append_cleanup_is_exact.
