(** Consuming construction transitions of the existing two-stack worker.

    Work and its counters have already been popped by the enclosing driver.
    These transitions change only the source-ordered value stack. Underflow
    leaves it unchanged; callback failure consumes its children but never
    appends a substitute result. Such failure is terminal to the owning driver,
    not a promise of rollback of the target's internal allocations or work.

    The pair specialization has the same mathematical suffix as ordered
    extraction; Rust can pop right/left directly without allocating a vector.
    This model does not change source scheduling or interpret source syntax. *)
From Stdlib Require Import List Arith Lia.
From RhoBridge Require Import RholangWorklistStorage RholangConstructionFacts.
Import ListNotations.

Inductive BuildResult (V E : Type) := Built (value : V) | BuildError (error : E).
Arguments Built {V E} _.
Arguments BuildError {V E} _.
Inductive Transition (V E : Type) :=
| Completed (values : list V)
| Underflow (requested available : nat) (unchanged : list V)
| Rejected (error : E) (remaining_prefix : list V).
Arguments Completed {V E} _.
Arguments Underflow {V E} _ _ _.
Arguments Rejected {V E} _ _.

Definition reduce_values {V E} count (build : list V -> BuildResult V E) values
    : Transition V E :=
  match checked_suffix count values with
  | None => Underflow count (length values) values
  | Some (prefix, children) =>
    match build children with
    | Built value => Completed (prefix ++ [value])
    | BuildError error => Rejected error prefix
    end
  end.

Definition reduce_pair {V E} (build : V -> V -> BuildResult V E) values
    : Transition V E :=
  match checked_suffix 2 values with
  | Some (prefix, [lhs; rhs]) =>
    match build lhs rhs with
    | Built value => Completed (prefix ++ [value])
    | BuildError error => Rejected error prefix
    end
  | _ => Underflow 2 (length values) values
  end.

Theorem values_success_preserves_prefix_and_source_order : forall V E
    (build : list V -> BuildResult V E) prefix children value,
  build children = Built value ->
  reduce_values (length children) build (prefix ++ children) = Completed (prefix ++ [value]).
Proof. intros. unfold reduce_values. rewrite suffix_source_order, H. reflexivity. Qed.

Theorem values_failure_consumes_only_children : forall V E
    (build : list V -> BuildResult V E) prefix children error,
  build children = BuildError error ->
  reduce_values (length children) build (prefix ++ children) = Rejected error prefix.
Proof. intros. unfold reduce_values. rewrite suffix_source_order, H. reflexivity. Qed.

Theorem values_underflow_keeps_original_stack : forall V E count
    (build : list V -> BuildResult V E) values,
  length values < count ->
  reduce_values count build values = Underflow count (length values) values.
Proof. intros. unfold reduce_values. rewrite suffix_underflow_rejects by assumption. reflexivity. Qed.

Theorem pair_keeps_left_right_order : forall V E
    (build : V -> V -> BuildResult V E) prefix lhs rhs,
  reduce_pair build (prefix ++ [lhs; rhs]) =
  match build lhs rhs with
  | Built value => Completed (prefix ++ [value])
  | BuildError error => Rejected error prefix
  end.
Proof.
  intros. unfold reduce_pair.
  replace 2 with (length [lhs; rhs]) by reflexivity.
  rewrite suffix_source_order. reflexivity.
Qed.

Theorem pair_empty_rejects : forall V E (build : V -> V -> BuildResult V E),
  reduce_pair build [] = Underflow 2 0 [].
Proof. reflexivity. Qed.

Theorem pair_singleton_rejects : forall V E (build : V -> V -> BuildResult V E) value,
  reduce_pair build [value] = Underflow 2 1 [value].
Proof. reflexivity. Qed.

Definition map_build {V W E} (f : V -> W) (result : BuildResult V E) : BuildResult W E :=
  match result with Built value => Built (f value) | BuildError error => BuildError error end.
Definition map_transition {V W E} (f : V -> W) (transition : Transition V E) : Transition W E :=
  match transition with
  | Completed values => Completed (map f values)
  | Underflow requested available values => Underflow requested available (map f values)
  | Rejected error prefix => Rejected error (map f prefix)
  end.

(** This generic algebra law is instantiated below with the concrete cache
    interpretation. Its callback premise is not an assumption about Rust. *)
Theorem consuming_suffix_commutes : forall V W E (f : V -> W)
    (build : list V -> BuildResult V E) (mapped : list W -> BuildResult W E),
  (forall children, mapped (map f children) = map_build f (build children)) ->
  forall count values,
  reduce_values count mapped (map f values) =
  map_transition f (reduce_values count build values).
Proof.
  intros V W E f build mapped H count values. unfold reduce_values.
  rewrite mapped_suffix_commutes.
  destruct (checked_suffix count values) as [[prefix children]|]; cbn.
  - rewrite H. destruct (build children); cbn; try rewrite map_app; reflexivity.
  - now rewrite length_map.
Qed.

Theorem concrete_append_fold_cache_exact : forall children accumulator,
  fold_left append_fact (map fact_of children) (fact_of accumulator) =
  fact_of (fold_left RholangTargetConstruction.append children accumulator).
Proof.
  induction children as [|child rest IH]; intros; cbn; auto.
  rewrite append_fact_is_exact. apply IH.
Qed.

Definition build_parallel (children : list RholangTargetConstruction.Value)
    : BuildResult RholangTargetConstruction.Value unit :=
  Built (fold_left RholangTargetConstruction.append children RholangTargetConstruction.empty).
Definition build_parallel_fact (children : list ConstructionFact)
    : BuildResult ConstructionFact unit :=
  Built (fold_left append_fact children (fact_of RholangTargetConstruction.empty)).

Theorem actual_parallel_transition_cache_commutes : forall count values,
  reduce_values count build_parallel_fact (map fact_of values) =
  map_transition fact_of (reduce_values count build_parallel values).
Proof.
  apply consuming_suffix_commutes. intro children.
  unfold build_parallel_fact, build_parallel, map_build.
  now rewrite concrete_append_fold_cache_exact.
Qed.

Theorem empty_fold_constructs_one_empty_value : forall prefix,
  reduce_values 0 build_parallel prefix =
  Completed (prefix ++ [RholangTargetConstruction.empty]).
Proof. intros. unfold reduce_values. rewrite suffix_zero. reflexivity. Qed.

Theorem pair_cache_commutes_on_ordered_children : forall prefix lhs rhs,
  reduce_pair (fun left right => @Built _ unit (append_fact left right))
    (map fact_of (prefix ++ [lhs; rhs])) =
  map_transition fact_of
    (reduce_pair (fun left right => @Built _ unit (RholangTargetConstruction.append left right))
      (prefix ++ [lhs; rhs])).
Proof.
  intros. rewrite map_app. cbn [map]. rewrite !pair_keeps_left_right_order.
  cbn [map_transition]. rewrite map_app, append_fact_is_exact. reflexivity.
Qed.

Print Assumptions values_success_preserves_prefix_and_source_order.
Print Assumptions values_failure_consumes_only_children.
Print Assumptions values_underflow_keeps_original_stack.
Print Assumptions pair_keeps_left_right_order.
Print Assumptions pair_empty_rejects.
Print Assumptions pair_singleton_rejects.
Print Assumptions consuming_suffix_commutes.
Print Assumptions concrete_append_fold_cache_exact.
Print Assumptions actual_parallel_transition_cache_commutes.
Print Assumptions empty_fold_constructs_one_empty_value.
Print Assumptions pair_cache_commutes_on_ordered_children.
