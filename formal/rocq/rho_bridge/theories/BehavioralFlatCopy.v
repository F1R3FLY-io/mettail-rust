(** Flat payload recipes and ordinary cleanup credits for the existing
    prattail/src/behavioral_pred/lifecycle.rs reconstruction worker.

    Variable arguments alone substitute. Named domains and string literals
    remain unchanged; enumerated domains preserve argument order. The worker
    supplies its existing shadowing-filtered substitution to these recipes.
    Byte lengths model byte strings. Inspection/comparison admission precedes
    the paid copy represented here; no copied string is needed to inspect its
    selected borrowed length in Rust.

    The cleanup section certifies arithmetic over explicit destructor events.
    Their correspondence to Rust's implicit Drop calls requires source review;
    this is not a compiler-verified destructor proof. It excludes flat payload
    teardown, allocator capacity, and panic recovery. No new worker or evaluator
    is specified. *)
From Stdlib Require Import List String ZArith Arith Lia.
From RhoBridge Require Import RholangInitialGraphResources RholangPreparationReservation.
Import ListNotations.

Module FlatPredicateRecipes.
Inductive Argument :=
| VariableArg (name : string)
| IntegerArg (value : Z)
| StringArg (value : string).
Inductive Domain :=
| NamedDomain (name : string)
| BoundedDomain (bound : nat)
| EnumeratedDomain (arguments : list Argument).
Definition Substitution := option (string * string).

Definition selected_variable_text substitution name :=
  match substitution with
  | None => name
  | Some (old, replacement) =>
    if String.eqb name old then replacement else name
  end.
Definition argument_recipe substitution argument :=
  match argument with
  | VariableArg name => VariableArg (selected_variable_text substitution name)
  | IntegerArg value => IntegerArg value
  | StringArg value => StringArg value
  end.
Definition domain_recipe substitution domain :=
  match domain with
  | NamedDomain name => NamedDomain name
  | BoundedDomain bound => BoundedDomain bound
  | EnumeratedDomain arguments =>
    EnumeratedDomain (map (argument_recipe substitution) arguments)
  end.
Definition argument_bytes argument :=
  match argument with
  | VariableArg text | StringArg text => String.length text
  | IntegerArg _ => 0
  end.
Definition paid_argument cancelled ceiling available substitution argument :=
  let bytes := argument_bytes (argument_recipe substitution argument) in
  preparation_action cancelled ceiling available [1; bytes] [4; bytes]
    (fun _ => Some (argument_recipe substitution argument)).

Theorem paid_argument_success_is_exact :
  forall cancelled ceiling available substitution argument paid result,
  paid_argument cancelled ceiling available substitution argument = Accepted paid result ->
  result = argument_recipe substitution argument.
Proof.
  intros cancelled ceiling available substitution argument paid result H.
  unfold paid_argument in H.
  apply preparation_success_is_the_same_paid_operation in H.
  destruct H as [_ [HR _]]. now inversion HR.
Qed.
Theorem cloning_argument_is_identity :
  forall argument, argument_recipe None argument = argument.
Proof. intros []; reflexivity. Qed.
Theorem cloning_domain_is_identity :
  forall domain, domain_recipe None domain = domain.
Proof.
  intros [name|bound|arguments]; try reflexivity.
  cbn [domain_recipe]. f_equal.
  induction arguments as [|argument rest IH]; cbn; [reflexivity|].
  now rewrite cloning_argument_is_identity, IH.
Qed.
Theorem matching_variable_uses_replacement :
  forall name replacement,
  argument_recipe (Some (name, replacement)) (VariableArg name) = VariableArg replacement.
Proof.
  intros. cbn [argument_recipe selected_variable_text]. now rewrite String.eqb_refl.
Qed.
Theorem string_literal_never_substitutes :
  forall substitution text, argument_recipe substitution (StringArg text) = StringArg text.
Proof. reflexivity. Qed.
Theorem named_domain_never_substitutes :
  forall substitution name, domain_recipe substitution (NamedDomain name) = NamedDomain name.
Proof. reflexivity. Qed.
Theorem enumerated_domain_preserves_argument_order :
  forall substitution prefix suffix,
  domain_recipe substitution (EnumeratedDomain (prefix ++ suffix)) =
  EnumeratedDomain (map (argument_recipe substitution) prefix ++
    map (argument_recipe substitution) suffix).
Proof. intros. cbn [domain_recipe]. now rewrite map_app. Qed.

(** N original nodes, E original child edges, and D edges with non-root
    original parents. Each non-root is drained by its enclosing Drop loop
    before its own implicit Drop drains its replacement Top children.
    Hence D <= E. Per-entry credits sum across independently owned results. *)
Definition temporary_boxes edges repeated := edges + repeated.
Definition cleanup_pushes edges repeated := edges + repeated.
Definition destructor_entries nodes edges repeated := nodes + edges + repeated.
Definition cleanup_dispatches nodes edges repeated := nodes + 2 * edges + 2 * repeated.
Definition cleanup_pop_attempts := cleanup_dispatches.
Definition cleanup_work nodes edges repeated :=
  destructor_entries nodes edges repeated + cleanup_dispatches nodes edges repeated +
  cleanup_pushes edges repeated + cleanup_pop_attempts nodes edges repeated.
Definition cleanup_records nodes edges repeated :=
  destructor_entries nodes edges repeated + cleanup_pushes edges repeated +
  temporary_boxes edges repeated.

Theorem existing_drop_event_counts_have_compositional_credit :
  forall nodes edges repeated,
  repeated <= edges ->
  cleanup_work nodes edges repeated <= 3 * nodes + 12 * edges /\
  cleanup_records nodes edges repeated <= nodes + 6 * edges.
Proof.
  intros. unfold cleanup_work, cleanup_records, destructor_entries,
    cleanup_pop_attempts, cleanup_dispatches, cleanup_pushes, temporary_boxes. lia.
Qed.
Theorem credits_add_over_private_result_forests :
  forall n1 n2 e1 e2,
  3 * (n1 + n2) + 12 * (e1 + e2) =
    (3 * n1 + 12 * e1) + (3 * n2 + 12 * e2) /\
  (n1 + n2) + 6 * (e1 + e2) = (n1 + 6 * e1) + (n2 + 6 * e2).
Proof. intros; split; lia. Qed.

Print Assumptions paid_argument_success_is_exact.
Print Assumptions cloning_argument_is_identity.
Print Assumptions cloning_domain_is_identity.
Print Assumptions matching_variable_uses_replacement.
Print Assumptions string_literal_never_substitutes.
Print Assumptions named_domain_never_substitutes.
Print Assumptions enumerated_domain_preserves_argument_order.
Print Assumptions existing_drop_event_counts_have_compositional_credit.
Print Assumptions credits_add_over_private_result_forests.
End FlatPredicateRecipes.
