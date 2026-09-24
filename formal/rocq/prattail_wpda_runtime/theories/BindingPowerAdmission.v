(** Checked arithmetic around the existing binding-power assignment loop.

    Source: prattail/src/binding_power.rs::analyze_binding_powers. The existing
    BTreeMap grouping remains unchanged: lexical category order, source order
    within each category. This model receives those ordered groups; it neither
    reconstructs grouping nor replaces classification or Pratt parsing.

    The SAME two-pass worker below takes either exact mathematical addition or
    checked addition. Rust will keep one loop, replacing only its six addition
    sites. The old static API forwards to that checked worker. A failed result
    contains no partial table. Source admission occurs before grouping, cloning,
    and temporary storage; its caller policy prepays the whole supplied domain,
    not a constant-cost token or a reused runtime parse-item budget.

    Rule occurrence payloads are abstract provenance. The original descriptor
    constructors keep their exact copies/defaults; postfix still erases its
    mixfix-only fields. This model checks pair assignment, order, and occurrence
    identity, not arbitrary Clone/Drop effects or physical allocator failure.

    Infix and postfix each maintain their own open-level bit. The two postfix
    gap additions run even when there are no postfix rules. Thus 126 distinct
    infix levels fail at PostfixStart (252+2+2), without imposing a rule-count
    cap: any number of same-level rules remains admissible when its level fits.
*)
From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.
Set Implicit Arguments.

Module BindingPowerAdmission.
Inductive Site := InfixAdvance | InfixSlot | FirstFree | PostfixStart
  | PostfixAdvance | PostfixSlot.
Inductive Failure := AdmissionRejected | Overflow (category_index : nat) (site : Site).
Inductive Result (A : Type) := Complete (value : A) | Refused (failure : Failure).
Arguments Complete {A} _.
Arguments Refused {A} _.
Definition bind {A B} (input : Result A) (next : A -> Result B) :=
  match input with Complete value => next value | Refused failure => Refused failure end.
Definition Refines {A} (checked original : Result A) :=
  forall value, checked = Complete value -> original = Complete value.

Lemma bind_refines : forall A B (checked original : Result A) (f g : A -> Result B),
  Refines checked original -> (forall value, Refines (f value) (g value)) ->
  Refines (bind checked f) (bind original g).
Proof.
  intros A B checked original f g Input Next value H.
  destruct checked as [intermediate|failure]; cbn in H; [|discriminate].
  specialize (Input intermediate eq_refl); rewrite Input; cbn.
  eapply Next; exact H.
Qed.
Lemma refines_identity : forall A (value : Result A), Refines value value.
Proof. intros A value answer H; exact H. Qed.

Definition add (maximum : option nat) category site left right : Result nat :=
  match maximum with
  | None => Complete (left + right)
  | Some limit => if left + right <=? limit then Complete (left + right)
                  else Refused (Overflow category site)
  end.
Theorem checked_add_preserves_exact_sum : forall maximum category site left right,
  Refines (add maximum category site left right) (add None category site left right).
Proof.
  intros [limit|] category site left right value H; cbn in *.
  - destruct (left + right <=? limit); inversion H; reflexivity.
  - exact H.
Qed.
Theorem checked_add_fits : forall limit category site left right,
  left + right <= limit -> add (Some limit) category site left right = Complete (left + right).
Proof. intros; unfold add; apply Nat.leb_le in H; now rewrite H. Qed.
Theorem checked_add_refuses_at_exact_site : forall limit category site left right,
  limit < left + right -> add (Some limit) category site left right = Refused (Overflow category site).
Proof. intros; unfold add; assert ((left + right <=? limit) = false) by (apply Nat.leb_gt; lia); now rewrite H0. Qed.
Theorem checked_add_never_wraps : forall limit category site left right value,
  add (Some limit) category site left right = Complete value -> value = left + right /\ value <= limit.
Proof.
  intros; unfold add in H; destruct (left + right <=? limit) eqn:Fits; [|discriminate].
  inversion H; subst; split; [reflexivity|now apply Nat.leb_le in Fits].
Qed.

Record Rule := { occurrence : nat; postfix : bool; same_level : bool; right_associative : bool }.
Record Operator := { source_rule : Rule; left_bp : nat; right_bp : nat }.
Record State := { level : nat; level_open : bool; operators : list Operator }.

Definition advance maximum category (is_postfix opened : bool) rule precedence :=
  if opened && negb (same_level rule)
  then add maximum category (if is_postfix then PostfixAdvance else InfixAdvance) precedence 2
  else Complete precedence.
Definition assign maximum category (is_postfix : bool) rule precedence :=
  bind (add maximum category (if is_postfix then PostfixSlot else InfixSlot) precedence 1)
    (fun upper => Complete {| source_rule := rule;
      left_bp := if is_postfix then upper else if right_associative rule then upper else precedence;
      right_bp := if is_postfix then 0 else if right_associative rule then precedence else upper |}).

Fixpoint run_pass maximum category is_postfix rules precedence opened : Result State :=
  match rules with
  | [] => Complete {| level := precedence; level_open := opened; operators := [] |}
  | rule :: rest => bind (advance maximum category is_postfix opened rule precedence) (fun next =>
      bind (assign maximum category is_postfix rule next) (fun operator =>
      bind (run_pass maximum category is_postfix rest next true) (fun final =>
      Complete {| level := level final; level_open := level_open final;
                  operators := operator :: operators final |})))
  end.

Definition run_category maximum category rules : Result (list Operator) :=
  bind (run_pass maximum category false (filter (fun r => negb (postfix r)) rules) 2 false) (fun infix =>
  bind (if level_open infix then add maximum category FirstFree (level infix) 2
        else Complete (level infix)) (fun first_free =>
  bind (add maximum category PostfixStart first_free 2) (fun postfix_start =>
  bind (run_pass maximum category true (filter postfix rules) postfix_start false) (fun suffix =>
  Complete (operators infix ++ operators suffix))))).

Fixpoint run_groups maximum index groups : Result (list Operator) := match groups with
| [] => Complete []
| rules :: rest => bind (run_category maximum index rules) (fun current =>
    bind (run_groups maximum (S index) rest) (fun suffix => Complete (current ++ suffix)))
end.
Definition analyze (admitted : bool) maximum groups :=
  if admitted then run_groups maximum 0 groups else Refused AdmissionRejected.

Theorem advance_preserves_original_level : forall maximum category is_postfix opened rule precedence,
  Refines (advance maximum category is_postfix opened rule precedence)
          (advance None category is_postfix opened rule precedence).
Proof. intros; unfold advance; destruct (opened && negb (same_level rule)); [apply checked_add_preserves_exact_sum|apply refines_identity]. Qed.
Theorem assignment_preserves_original_pair_and_payload : forall maximum category is_postfix rule precedence,
  Refines (assign maximum category is_postfix rule precedence)
          (assign None category is_postfix rule precedence).
Proof. intros; unfold assign; apply bind_refines; [apply checked_add_preserves_exact_sum|intros; apply refines_identity]. Qed.
Theorem checked_pass_preserves_original_state_and_order : forall maximum category is_postfix rules precedence opened,
  Refines (run_pass maximum category is_postfix rules precedence opened)
          (run_pass None category is_postfix rules precedence opened).
Proof.
  intros maximum category is_postfix rules; induction rules as [|rule rest IH]; intros;
    cbn -[advance assign bind].
  - apply refines_identity.
  - apply bind_refines; [apply advance_preserves_original_level|intro next].
    apply bind_refines; [apply assignment_preserves_original_pair_and_payload|intro operator].
    apply bind_refines; [apply IH|intro final; apply refines_identity].
Qed.
Theorem checked_category_preserves_both_original_passes : forall maximum category rules,
  Refines (run_category maximum category rules) (run_category None category rules).
Proof.
  intros; unfold run_category.
  apply bind_refines; [apply checked_pass_preserves_original_state_and_order|intro infix].
  apply bind_refines.
  - destruct (level_open infix); [apply checked_add_preserves_exact_sum|apply refines_identity].
  - intro first_free. apply bind_refines; [apply checked_add_preserves_exact_sum|intro postfix_start].
    apply bind_refines; [apply checked_pass_preserves_original_state_and_order|intro suffix; apply refines_identity].
Qed.
Theorem checked_groups_preserve_original_table : forall maximum index groups,
  Refines (run_groups maximum index groups) (run_groups None index groups).
Proof.
  intros maximum index groups; revert index; induction groups as [|rules rest IH]; intros;
    cbn -[run_category bind].
  - apply refines_identity.
  - apply bind_refines; [apply checked_category_preserves_both_original_passes|intro current].
    apply bind_refines; [apply IH|intro suffix; apply refines_identity].
Qed.
Theorem successful_publication_is_exact_original_table : forall admitted maximum groups table,
  analyze admitted maximum groups = Complete table -> run_groups None 0 groups = Complete table.
Proof.
  intros [|] maximum groups table H; cbn in H; [|discriminate].
  eapply checked_groups_preserve_original_table; exact H.
Qed.
Theorem denied_policy_runs_no_assignment : forall maximum groups,
  analyze false maximum groups = Refused AdmissionRejected.
Proof. reflexivity. Qed.
Theorem arithmetic_failure_exposes_no_partial_table : forall maximum groups failure,
  run_groups maximum 0 groups = Refused failure -> analyze true maximum groups = Refused failure.
Proof. intros; exact H. Qed.

Theorem same_marker_does_not_advance : forall maximum category is_postfix opened rule precedence,
  same_level rule = true -> advance maximum category is_postfix opened rule precedence = Complete precedence.
Proof. intros; unfold advance; rewrite H; destruct opened; reflexivity. Qed.
Theorem first_rule_ignores_same_marker : forall maximum category is_postfix rule precedence,
  advance maximum category is_postfix false rule precedence = Complete precedence.
Proof. reflexivity. Qed.
Theorem pair_slots_are_bounded : forall limit category is_postfix rule precedence result,
  assign (Some limit) category is_postfix rule precedence = Complete result ->
  left_bp result <= limit /\ right_bp result <= limit /\ source_rule result = rule.
Proof.
  intros; unfold assign in H.
  destruct (add (Some limit) category (if is_postfix then PostfixSlot else InfixSlot) precedence 1) as [upper|failure] eqn:Add;
    cbn in H; [|discriminate].
  apply checked_add_never_wraps in Add; destruct Add as [Sum Bound].
  inversion H; subst; cbn. destruct is_postfix, (right_associative rule); cbn; repeat split; auto; lia.
Qed.
Theorem same_pair_level_is_associativity_independent : forall category rule precedence,
  assign None category false rule precedence = Complete
    {| source_rule := rule;
       left_bp := if right_associative rule then precedence + 1 else precedence;
       right_bp := if right_associative rule then precedence else precedence + 1 |}.
Proof. reflexivity. Qed.
Theorem postfix_has_no_right_recursive_slot : forall maximum category rule precedence result,
  assign maximum category true rule precedence = Complete result -> right_bp result = 0.
Proof.
  intros; unfold assign in H.
  destruct (add maximum category PostfixSlot precedence 1); cbn in H; inversion H; reflexivity.
Qed.

Definition ordinary_rule : Rule := {| occurrence := 0; postfix := false;
  same_level := false; right_associative := false |}.
Definition same_rule : Rule := {| occurrence := 0; postfix := false;
  same_level := true; right_associative := false |}.
Definition postfix_rule : Rule := {| occurrence := 0; postfix := true;
  same_level := false; right_associative := false |}.
Definition successful {A} (result : Result A) := match result with Complete _ => true | _ => false end.

Example original_125_infix_levels_fit :
  successful (run_category (Some 255) 0 (repeat ordinary_rule 125)) = true.
Proof. vm_compute; reflexivity. Qed.
Example original_126_infix_levels_refuse_even_without_postfix :
  run_category (Some 255) 0 (repeat ordinary_rule 126) = Refused (Overflow 0 PostfixStart).
Proof. vm_compute; reflexivity. Qed.
Example original_127_infix_levels_refuse_first_free :
  run_category (Some 255) 0 (repeat ordinary_rule 127) = Refused (Overflow 0 FirstFree).
Proof. vm_compute; reflexivity. Qed.
Example original_126_postfix_levels_fit_without_infix :
  successful (run_category (Some 255) 0 (repeat postfix_rule 126)) = true.
Proof. vm_compute; reflexivity. Qed.
Example original_127_postfix_levels_refuse_advance :
  run_category (Some 255) 0 (repeat postfix_rule 127) = Refused (Overflow 0 PostfixAdvance).
Proof. vm_compute; reflexivity. Qed.
Example more_than_126_same_level_rules_still_fit :
  successful (run_category (Some 255) 0 (repeat same_rule 500)) = true.
Proof. vm_compute; reflexivity. Qed.
Example postfix_same_never_reuses_infix_level :
  let same_postfix := {| occurrence := 1; postfix := true;
      same_level := true; right_associative := false |} in
  run_category (Some 255) 0 [same_postfix; ordinary_rule] = Complete
    [{| source_rule := ordinary_rule; left_bp := 2; right_bp := 3 |};
     {| source_rule := same_postfix; left_bp := 7; right_bp := 0 |}].
Proof. reflexivity. Qed.

Print Assumptions checked_add_preserves_exact_sum.
Print Assumptions checked_add_refuses_at_exact_site.
Print Assumptions checked_add_never_wraps.
Print Assumptions checked_pass_preserves_original_state_and_order.
Print Assumptions checked_category_preserves_both_original_passes.
Print Assumptions checked_groups_preserve_original_table.
Print Assumptions successful_publication_is_exact_original_table.
Print Assumptions denied_policy_runs_no_assignment.
Print Assumptions arithmetic_failure_exposes_no_partial_table.
Print Assumptions same_marker_does_not_advance.
Print Assumptions first_rule_ignores_same_marker.
Print Assumptions pair_slots_are_bounded.
Print Assumptions same_pair_level_is_associativity_independent.
Print Assumptions postfix_has_no_right_recursive_slot.
Print Assumptions original_125_infix_levels_fit.
Print Assumptions original_126_infix_levels_refuse_even_without_postfix.
Print Assumptions original_127_infix_levels_refuse_first_free.
Print Assumptions original_126_postfix_levels_fit_without_infix.
Print Assumptions original_127_postfix_levels_refuse_advance.
Print Assumptions more_than_126_same_level_rules_still_fit.
Print Assumptions postfix_same_never_reuses_infix_level.
End BindingPowerAdmission.
