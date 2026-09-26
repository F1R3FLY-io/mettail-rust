(** Lossless owned associativity and the existing semantic admission boundary.

    This extends the old Boolean classifier observation without interpreting
    NonAssociative as false. Legacy postfix classification deliberately returned
    Left even for a declared Right; that exact legacy result is preserved.
    The existing postfix binding-power pass does not read associativity. This
    bounded extension admits NonAssociative postfix there. The closed-mixfix
    extension below reuses the original closed-edge routing pair while retaining
    the source associativity for semantic admission; open edges remain refused.

    The semantic worker is Realizer::precedence_valid relocated verbatim except
    for its caller's lazy category-child index projection. Its binary and postfix
    comparisons are the existing JuxtapositionPrecedence and
    UnaryPostfixPrecedence definitions, not a new evaluator. The selected-child
    law below states the required adapter premise explicitly: retained argument
    slots must expose the same ordered child-top observations. It does not prove
    that arbitrary authored syntax has that correspondence. Unsupported rows
    must remain explicit errors, and Rust source review/tests discharge the
    admitted row projection. No recognition/forest completeness claim.
*)
From Stdlib Require Import List Arith Bool.
From RuntimeGrammar Require Import JuxtapositionPrecedence UnaryPostfixPrecedence.
Import ListNotations.

Module OwnedPrecedenceAdmission.

Definition legacy_associativity (right : bool) := if right then Right else Left.
Definition postfix_classifier_associativity assoc :=
  match assoc with NonAssociative => NonAssociative | _ => Left end.
Definition binary_binding_pair assoc power :=
  match assoc with
  | Left => Some (power, S power)
  | Right => Some (S power, power)
  | NonAssociative => None
  end.
Definition postfix_binding_pair (_ : Associativity) power := (S power, 0).

Theorem legacy_binary_pairs_unchanged : forall right power,
  binary_binding_pair (legacy_associativity right) power =
    Some (if right then (S power, power) else (power, S power)).
Proof. intros []; reflexivity. Qed.
Theorem legacy_postfix_descriptor_unchanged : forall right,
  postfix_classifier_associativity (legacy_associativity right) = Left.
Proof. intros []; reflexivity. Qed.
Theorem nonassociative_postfix_is_retained :
  postfix_classifier_associativity NonAssociative = NonAssociative.
Proof. reflexivity. Qed.
Theorem nonassociative_binary_is_not_silently_left : forall power,
  binary_binding_pair NonAssociative power = None /\
  binary_binding_pair Left power <> None.
Proof. intros; split; [reflexivity|discriminate]. Qed.
Theorem original_postfix_assignment_is_reused : forall assoc power,
  postfix_binding_pair assoc power = postfix_binding_pair Left power.
Proof. reflexivity. Qed.
Theorem declared_postfix_strictness_is_original : forall parent child,
  postfix_admission NonAssociative (Some parent) (Some child) = true <-> parent < child.
Proof. apply ranked_nonassociative_postfix_is_exact_strict_comparison. Qed.

Definition selected (tops : list (option nat)) (indices : list nat) :=
  map (fun index => match nth_error tops index with
                   | Some top => top | None => None end) indices.

Theorem corresponding_slots_preserve_all_selected_children :
  forall source owned source_indices owned_indices,
  map (fun index => match nth_error source index with
                   | Some top => top | None => None end) source_indices =
  map (fun index => match nth_error owned index with
                   | Some top => top | None => None end) owned_indices ->
  selected source source_indices = selected owned owned_indices.
Proof. intros; exact H. Qed.

(** The callback remains below BOTH early returns. The returned trace is its
    complete caller-owned observation trace, not an assumption of purity. *)
Section LazyProjection.
Context {Observation Trace : Type}.
Variable project : nat -> Observation * list Trace.
Variable check : nat -> Observation -> bool.
Definition shared_worker (parent : option (option nat)) :=
  match parent with
  | None | Some None => (true, [])
  | Some (Some power) =>
      let '(children, trace) := project power in (check power children, trace)
  end.
Definition original_caller (parent : option (option nat)) :=
  match parent with
  | None => (true, [])
  | Some parent => match parent with
      | None => (true, [])
      | Some power =>
          let '(children, trace) := project power in (check power children, trace)
      end
  end.
Theorem relocation_preserves_result_and_projection_trace : forall parent,
  shared_worker parent = original_caller parent.
Proof. intros [ [power|] |]; reflexivity. Qed.
Theorem missing_parent_does_not_observe_children : shared_worker None = (true, []).
Proof. reflexivity. Qed.
Theorem missing_power_does_not_observe_children : shared_worker (Some None) = (true, []).
Proof. reflexivity. Qed.
End LazyProjection.

(** A closed postfix-mixfix is NOT a plain postfix routing row. Its original
    classifier retains all operand/literal parts and uses the nonpostfix table
    pass with a Left pair. PRepeat has two parts: Nat followed by comma, then
    Nat followed by right brace. Only the last part's following literals are
    closure evidence. Earlier delimiters do not close an open final operand.
    A nullary mixfix uses its separate, nonempty trailing-literal descriptor.

    [last_following] is the existing descriptor observation, not a new scan of
    authored syntax. [None] means there are no operand parts. Rust correspondence
    must establish that the original classifier supplied this descriptor and
    that no fields, level order, checked arithmetic or callbacks are changed.
    Core's associativity is NOT replaced with Left. The final semantic worker
    still uses its original postfix classification and selected child indices.
    These laws make no recognition/forest completeness claim. *)
Definition closed_mixfix (is_mixfix : bool)
    (last_following : option (list nat)) (nullary_literals : list nat) : bool :=
  is_mixfix &&
    match last_following with
    | Some (_ :: _) => true
    | Some [] => false
    | None => match nullary_literals with [] => false | _ :: _ => true end
    end.

Definition closed_mixfix_binding_pair (assoc : Associativity) (closed : bool)
    (power : nat) :=
  match assoc with
  | NonAssociative => if closed then binary_binding_pair Left power else None
  | _ => binary_binding_pair assoc power
  end.

Theorem closed_extension_preserves_legacy_pairs : forall right closed power,
  closed_mixfix_binding_pair (legacy_associativity right) closed power =
  binary_binding_pair (legacy_associativity right) power.
Proof. intros []; reflexivity. Qed.
Theorem binary_row_is_not_closed : forall following literals,
  closed_mixfix false following literals = false.
Proof. reflexivity. Qed.
Theorem final_operand_without_closer_stays_open : forall literals,
  closed_mixfix true (Some []) literals = false.
Proof. reflexivity. Qed.
Theorem final_literal_proves_closed_edge : forall literal rest literals,
  closed_mixfix true (Some (literal :: rest)) literals = true.
Proof. reflexivity. Qed.
Theorem nullary_requires_actual_trailing_literal :
  closed_mixfix true None [] = false /\
  forall literal rest, closed_mixfix true None (literal :: rest) = true.
Proof. split; reflexivity. Qed.
Theorem open_nonassociative_routing_remains_refused : forall power,
  closed_mixfix_binding_pair NonAssociative false power = None.
Proof. reflexivity. Qed.
Theorem closed_nonassociative_reuses_original_pair : forall power,
  closed_mixfix_binding_pair NonAssociative true power =
  binary_binding_pair Left power.
Proof. reflexivity. Qed.

Definition retained_closed_route {Payload : Type} assoc closed power
    (payload : Payload) :=
  option_map (fun pair => (pair, assoc, payload))
    (closed_mixfix_binding_pair assoc closed power).
Theorem closure_retains_source_association_and_complete_payload :
  forall Payload power (payload : Payload),
  retained_closed_route NonAssociative true power payload =
    Some ((power, S power), NonAssociative, payload).
Proof. reflexivity. Qed.
Theorem closed_route_does_not_weaken_semantic_admission : forall power child,
  postfix_admission NonAssociative (Some power) (Some child) = true <->
  power < child.
Proof. apply ranked_nonassociative_postfix_is_exact_strict_comparison. Qed.
Theorem repeat_selects_pattern_not_nat_children : forall pattern lower upper,
  selected [pattern; lower; upper] [0] = [pattern].
Proof. reflexivity. Qed.

Print Assumptions legacy_binary_pairs_unchanged.
Print Assumptions legacy_postfix_descriptor_unchanged.
Print Assumptions nonassociative_postfix_is_retained.
Print Assumptions nonassociative_binary_is_not_silently_left.
Print Assumptions original_postfix_assignment_is_reused.
Print Assumptions declared_postfix_strictness_is_original.
Print Assumptions corresponding_slots_preserve_all_selected_children.
Print Assumptions relocation_preserves_result_and_projection_trace.
Print Assumptions missing_parent_does_not_observe_children.
Print Assumptions missing_power_does_not_observe_children.
Print Assumptions closed_extension_preserves_legacy_pairs.
Print Assumptions binary_row_is_not_closed.
Print Assumptions final_operand_without_closer_stays_open.
Print Assumptions final_literal_proves_closed_edge.
Print Assumptions nullary_requires_actual_trailing_literal.
Print Assumptions open_nonassociative_routing_remains_refused.
Print Assumptions closed_nonassociative_reuses_original_pair.
Print Assumptions closure_retains_source_association_and_complete_payload.
Print Assumptions closed_route_does_not_weaken_semantic_admission.
Print Assumptions repeat_selects_pattern_not_nat_children.
End OwnedPrecedenceAdmission.
