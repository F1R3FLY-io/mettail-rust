(** Retaining the already-observed universal grouping close for owned terms.

    Existing source sites: canonical walker structural GroupingMarker
    ConsumeAndPop and GroupingMarker -> CategoryEntry ConsumeAndReplace.
    Both consumed an actual closing delimiter; neither invoked an authored
    action. The static/default path remains exact passthrough. The owned path
    retains a unary structural packing, separate from grammar productions, so
    realization can expose an unranked boundary without relabelling the value.
    Authored PGroup reductions remain ordinary actions and are not this hook.

    This proves boundary erasure, source-gate and semantic/cost preservation,
    not full SPPF/recognition completeness. Rust correspondence must cover both
    close sites, the actual marker position, disjoint structural action tag,
    and the existing realization entry points. There is no token-text inference
    or side table marking an inner symbol shared with ungrouped occurrences.
*)
From Stdlib Require Import List Bool Arith Lia.
From RuntimeGrammar Require Import JuxtapositionPrecedence UnaryPostfixPrecedence.
Import ListNotations.

Module OwnedGroupingBoundary.
Inductive Close := ConsumePop | ConsumeReplace.
Inductive Frame := GroupingMarker | OtherFrame.
Section Boundary.
Context {Payload Weight : Type}.
Record Term := { payload : Payload; top : option nat; weight : Weight }.
Definition grouped term :=
  {| payload := payload term; top := None; weight := weight term |}.
Inductive Forest := Inner (term : Term) | Group (child : Forest).
Fixpoint erase forest := match forest with Inner term => term | Group child => erase child end.
Fixpoint realize forest :=
  match forest with Inner term => term | Group child => grouped (realize child) end.
Definition retain (owned : bool) (frame : Frame) (_ : Close) child :=
  if owned then match frame with GroupingMarker => Group child | OtherFrame => child end
  else child.

Theorem static_path_is_exact_passthrough : forall frame close child,
  retain false frame close child = child.
Proof. reflexivity. Qed.
Theorem no_group_marker_no_boundary : forall enabled close child,
  retain enabled OtherFrame close child = child.
Proof. intros []; reflexivity. Qed.
Theorem both_original_close_paths_retain_same_boundary : forall child,
  retain true GroupingMarker ConsumePop child =
  retain true GroupingMarker ConsumeReplace child.
Proof. reflexivity. Qed.
Theorem structural_erasure_is_identity : forall enabled frame close child,
  erase (retain enabled frame close child) = erase child.
Proof. intros [] [] close child; reflexivity. Qed.
Theorem boundary_keeps_exact_payload_and_weight : forall term,
  payload (grouped term) = payload term /\ weight (grouped term) = weight term.
Proof. intros; split; reflexivity. Qed.
Theorem boundary_does_not_invent_production : forall term, top (grouped term) = None.
Proof. reflexivity. Qed.
Theorem unranked_group_admitted_by_original_postfix_worker : forall assoc parent term,
  postfix_admission assoc parent (top (grouped term)) = true.
Proof. intros; apply unranked_child_remains_admitted. Qed.
End Boundary.

(** A unit local packing does not change the child's semiring cost. *)
Section Cost.
Context {W : Type} (one : W) (times : W -> W -> W).
Hypothesis right_identity : forall child, times child one = child.
Theorem structural_unit_packing_preserves_cost : forall child,
  times child one = child.
Proof. apply right_identity. Qed.
End Cost.

(** The retained close advances beyond the inner symbol's end; therefore the
    outer symbol cannot intern as its own child at the same category/span. *)
Theorem consumed_close_distinguishes_wrapper : forall (category lo child_hi close_hi : nat),
  child_hi < close_hi ->
  (category, lo, child_hi) <> (category, lo, close_hi).
Proof. intros category lo child_hi close_hi Later Equal; inversion Equal; lia. Qed.

(** Both structural hooks use the checked reserved category, not a guessed
    free local-rule index. All real categories must lie strictly below it. *)
Theorem checked_category_domain_separates_structural_actions :
  forall (category rule reserved structural_rule : nat),
  category < reserved -> (category, rule) <> (reserved, structural_rule).
Proof. intros category rule reserved structural_rule Bound Equal; inversion Equal; lia. Qed.
Theorem distinct_structural_rules_remain_distinct : forall (category group hole : nat),
  group <> hole -> (category, group) <> (category, hole).
Proof. intros category group hole Different Equal; inversion Equal; contradiction. Qed.

Print Assumptions static_path_is_exact_passthrough.
Print Assumptions no_group_marker_no_boundary.
Print Assumptions both_original_close_paths_retain_same_boundary.
Print Assumptions structural_erasure_is_identity.
Print Assumptions boundary_keeps_exact_payload_and_weight.
Print Assumptions boundary_does_not_invent_production.
Print Assumptions unranked_group_admitted_by_original_postfix_worker.
Print Assumptions structural_unit_packing_preserves_cost.
Print Assumptions consumed_close_distinguishes_wrapper.
Print Assumptions checked_category_domain_separates_structural_actions.
Print Assumptions distinct_structural_rules_remain_distinct.
End OwnedGroupingBoundary.
