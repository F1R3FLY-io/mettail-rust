From Stdlib Require Import Arith Bool List Lia.
From RhoBridge Require Import DeBruijnSubstTRS.
Import ListNotations.
Import DeBruijnSubstTRS.

Module MonikerScopeInstantiation.

Inductive LeafDecision :=
| Keep : nat -> LeafDecision
| Insert : nat -> nat -> LeafDecision
| MissingBinder : LeafDecision.

Definition instantiate_leaf (depth scope index arity : nat) : LeafDecision :=
  match Nat.compare scope depth with
  | Lt => Keep scope
  | Eq => if index <? arity then Insert index depth else MissingBinder
  | Gt => Keep (pred scope)
  end.

Theorem inner_binding_is_unchanged : forall depth scope index arity,
  scope < depth -> instantiate_leaf depth scope index arity = Keep scope.
Proof.
  intros. unfold instantiate_leaf. apply Nat.compare_lt_iff in H. rewrite H. reflexivity.
Qed.

Theorem outer_binding_loses_one_scope : forall depth scope index arity,
  depth < scope -> instantiate_leaf depth scope index arity = Keep (pred scope).
Proof.
  intros. unfold instantiate_leaf. apply Nat.compare_gt_iff in H. rewrite H. reflexivity.
Qed.

Theorem replacement_keeps_index_and_depth : forall depth index arity,
  index < arity -> instantiate_leaf depth depth index arity = Insert index depth.
Proof.
  intros. unfold instantiate_leaf. rewrite Nat.compare_refl.
  apply Nat.ltb_lt in H. rewrite H. reflexivity.
Qed.

Theorem missing_binder_is_rejected : forall depth index arity,
  arity <= index -> instantiate_leaf depth depth index arity = MissingBinder.
Proof.
  intros. unfold instantiate_leaf. rewrite Nat.compare_refl.
  apply Nat.ltb_ge in H. rewrite H. reflexivity.
Qed.

Fixpoint instantiate (depth : nat) (argument body : Obj) : Obj :=
  match body with
  | oBound scope =>
      match Nat.compare scope depth with
      | Lt => oBound scope
      | Eq => oshift_by 0 depth argument
      | Gt => oBound (pred scope)
      end
  | oFree name => oFree name
  | oLam body => oLam (instantiate (S depth) argument body)
  | oNode op children => oNode op (map (instantiate depth argument) children)
  end.

Theorem instantiation_is_debruijn_substitution : forall body depth argument,
  instantiate depth argument body = osubst depth argument body.
Proof.
  induction body using Obj_ind'; intros; simpl.
  - destruct (n ?= depth); try reflexivity. now rewrite oshift_by_is_oshiftk.
  - reflexivity.
  - now rewrite IHbody.
  - f_equal. induction H; simpl; [reflexivity|]. now rewrite H, IHForall.
Qed.

Theorem free_names_are_unchanged : forall name depth argument,
  instantiate depth argument (oFree name) = oFree name.
Proof. reflexivity. Qed.

Theorem binder_increments_scope_depth : forall body depth argument,
  instantiate depth argument (oLam body) = oLam (instantiate (S depth) argument body).
Proof. reflexivity. Qed.

Theorem argument_internal_binding_is_unchanged : forall cutoff amount scope,
  scope < cutoff -> oshift_by cutoff amount (oBound scope) = oBound scope.
Proof. intros. simpl. apply Nat.ltb_lt in H. now rewrite H. Qed.

Theorem argument_external_binding_is_shifted : forall cutoff amount scope,
  cutoff <= scope -> oshift_by cutoff amount (oBound scope) = oBound (scope + amount).
Proof. intros. simpl. apply Nat.ltb_ge in H. now rewrite H. Qed.

Fixpoint old_open (depth marker : nat) (body : Obj) : Obj :=
  match body with
  | oBound scope => if scope =? depth then oFree marker else oBound scope
  | oFree name => oFree name
  | oLam body => oLam (old_open (S depth) marker body)
  | oNode op children => oNode op (map (old_open depth marker) children)
  end.

Fixpoint old_replace (marker : nat) (argument body : Obj) : Obj :=
  match body with
  | oBound scope => oBound scope
  | oFree name => if name =? marker then argument else oFree name
  | oLam body => oLam (old_replace marker argument body)
  | oNode op children => oNode op (map (old_replace marker argument) children)
  end.

Definition old_beta (argument body : Obj) := old_replace 1 argument (old_open 0 1 body).

Theorem old_w1_captures_argument :
  old_beta (oBound 0) (oLam (oBound 1)) = oLam (oBound 0).
Proof. reflexivity. Qed.

Theorem old_w2_keeps_removed_scope :
  old_beta (oFree 0) (oBound 1) = oBound 1.
Proof. reflexivity. Qed.

Theorem corrected_w1_preserves_argument_binding :
  instantiate 0 (oBound 0) (oLam (oBound 1)) = oLam (oBound 1).
Proof. reflexivity. Qed.

Theorem corrected_w2_preserves_body_binding :
  instantiate 0 (oFree 0) (oBound 1) = oBound 0.
Proof. reflexivity. Qed.

End MonikerScopeInstantiation.

Print Assumptions MonikerScopeInstantiation.inner_binding_is_unchanged.
Print Assumptions MonikerScopeInstantiation.outer_binding_loses_one_scope.
Print Assumptions MonikerScopeInstantiation.replacement_keeps_index_and_depth.
Print Assumptions MonikerScopeInstantiation.missing_binder_is_rejected.
Print Assumptions MonikerScopeInstantiation.instantiation_is_debruijn_substitution.
Print Assumptions MonikerScopeInstantiation.free_names_are_unchanged.
Print Assumptions MonikerScopeInstantiation.binder_increments_scope_depth.
Print Assumptions MonikerScopeInstantiation.argument_internal_binding_is_unchanged.
Print Assumptions MonikerScopeInstantiation.argument_external_binding_is_shifted.
Print Assumptions MonikerScopeInstantiation.old_w1_captures_argument.
Print Assumptions MonikerScopeInstantiation.old_w2_keeps_removed_scope.
Print Assumptions MonikerScopeInstantiation.corrected_w1_preserves_argument_binding.
Print Assumptions MonikerScopeInstantiation.corrected_w2_preserves_body_binding.
