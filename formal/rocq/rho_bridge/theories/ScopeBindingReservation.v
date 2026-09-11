(** Local scope-field accounting for generated checked binding.

    Source: iterative_drop.rs's Binder/MultiBinder arms construct a raw dummy
    scope, replace the old scope, consume it with into_parts_unsafe, and pass
    its body Arc to into_inner. runtime/src/binding.rs reconstructs raw scope
    parts without closing, freshening, or a tuple allocation. Scope has no
    custom Drop; the final replacement-scope event below is flat field glue.

    Reuse the required Arc contract for body wrapping, mem::replace handling,
    replacement Arc construction/release, the original ownership check, and
    an owned-result push. Do not add those operations again. The extra scope
    facts pay output and dummy scope shells, old into_parts dispatch, final
    replacement-scope dispatch, and its actual replacement pattern.

    Single replacement patterns are Binder(FreeVar::fresh(None)): two logical
    Binder wrapper events plus one unnamed FreeVar construction/record. The
    multi replacement is Vec::new(): construction, flat teardown and a header
    record, with no element work. These are source-specific native contracts,
    not proofs of native allocation, freshness generation, or CPU cost.

    Original pattern copy/cleanup is already paid by BinderPatternCopy and is
    excluded here. The consumed original scope has no residual shell glue;
    the original Arc has no extra release pair after into_inner. Parent,
    slots and worklist charges are separate. The existing output algebra
    transfers already-paid child credits unchanged. Body-depth laws remain
    those of the existing binding operation; this model adds no depth policy.

    All fallible copies/takes must finish in paid bare locals before wrapping
    and raw parent reconstruction, with no fallible callback until publication.
    The model does not prove that a Rust emitter follows that ordering. Source
    pinning, the selected-dummy normal/empty-pool premise, and normal-error
    cleanup boundaries are inherited. Unwind, TLS teardown, allocator failure
    and whole-Rust correctness are not claimed. *)
From Stdlib Require Import List Arith Lia.
From Trampoline Require Import WorklistFoldEquivalence.
From RhoBridge Require Import GeneratedDummyCleanupReservation ScalarArcBindingReservation
  GeneratedBindingOutputReservation RholangScopeConstructionRecipe BinderPatternCopy.
Import ListNotations.

Module ScopeBindingReservation.
Module S := ScalarArcBindingReservation.
Module D := GeneratedDummyCleanupReservation.
Module O := GeneratedBindingOutputReservation.
Module R := ScopeConstructionRecipe.
Module P := BinderPatternCopy.
Module W := WorklistFoldEquivalence.

Inductive PatternKind := SinglePattern | MultiPattern.

Definition scope_shell : D.Counts := fun event =>
  D.atom D.NativeWork event + D.atom D.NativeRecord event.

Definition replacement_pattern kind : D.Counts := fun event =>
  match kind with
  | SinglePattern => 3 * D.atom D.NativeWork event + D.atom D.NativeRecord event
  | MultiPattern => 2 * D.atom D.NativeWork event + D.atom D.NativeRecord event
  end.

Theorem single_replacement_matches_unnamed_binder_charge : forall identity,
  D.weighted D.base_work_weight (replacement_pattern SinglePattern) =
    P.binder_work {| P.K.name_identity := identity; P.K.name_pretty := None |} /\
  D.weighted D.record_weight (replacement_pattern SinglePattern) = 1 /\
  D.weighted D.byte_weight (replacement_pattern SinglePattern) = 0.
Proof. intros; repeat split; reflexivity. Qed.

Theorem multi_replacement_matches_empty_pattern_charge :
  D.weighted D.base_work_weight (replacement_pattern MultiPattern) = P.copied_work [] /\
  D.weighted D.record_weight (replacement_pattern MultiPattern) = P.copied_records [] /\
  D.weighted D.byte_weight (replacement_pattern MultiPattern) = P.copied_bytes [].
Proof. repeat split; reflexivity. Qed.

Definition scope_copy mode : D.Counts := fun event =>
  S.wrapper_construction mode event + scope_shell event.

Definition scope_cleanup kind mode : D.Counts := fun event =>
  S.required_cleanup mode event + scope_shell event +
  D.atom D.NativeWork event + D.atom D.NativeWork event + replacement_pattern kind event.

Definition scope_extra kind : D.Counts := fun event =>
  scope_shell event + scope_shell event +
  D.atom D.NativeWork event + D.atom D.NativeWork event + replacement_pattern kind event.

Definition scope_local kind mode : D.Counts := fun event =>
  scope_copy mode event + scope_cleanup kind mode event.

Definition scope_total kind mode receipt : D.Counts := fun event =>
  scope_local kind mode event + S.selected_dummy receipt event.

Theorem scope_local_is_required_plus_extra : forall kind mode event,
  scope_local kind mode event = S.required_local mode event + scope_extra kind event.
Proof.
  intros. unfold scope_local, scope_copy, scope_cleanup, S.required_local, scope_extra.
  lia.
Qed.

Theorem scope_total_is_required_total_plus_extra : forall kind mode receipt event,
  scope_total kind mode receipt event =
    S.required_total mode receipt event + scope_extra kind event.
Proof.
  intros. unfold scope_total, S.required_total.
  rewrite scope_local_is_required_plus_extra. lia.
Qed.

Theorem scope_extra_projection : forall kind,
  D.weighted D.base_work_weight (scope_extra kind) =
    (match kind with SinglePattern => 7 | MultiPattern => 6 end) /\
  D.weighted D.record_weight (scope_extra kind) = 3 /\
  D.weighted D.byte_weight (scope_extra kind) = 0.
Proof. intros []; repeat split; reflexivity. Qed.

Theorem scope_local_projection : forall kind mode,
  D.weighted D.base_work_weight (scope_local kind mode) =
    (match kind, mode with
     | SinglePattern, S.CloneMode => 13 | SinglePattern, S.OpenCloseMode => 14
     | MultiPattern, S.CloneMode => 12 | MultiPattern, S.OpenCloseMode => 13
     end) /\
  D.weighted D.record_weight (scope_local kind mode) =
    (match mode with S.CloneMode => 5 | S.OpenCloseMode => 6 end) /\
  D.weighted D.byte_weight (scope_local kind mode) = 0.
Proof. intros [] []; repeat split; reflexivity. Qed.

Theorem scope_total_projection : forall kind mode receipt,
  D.weighted D.base_work_weight (scope_total kind mode receipt) =
    (match kind, mode with
     | SinglePattern, S.CloneMode => 13 | SinglePattern, S.OpenCloseMode => 14
     | MultiPattern, S.CloneMode => 12 | MultiPattern, S.OpenCloseMode => 13
     end) + D.weighted D.base_work_weight (S.selected_dummy receipt) /\
  D.weighted D.record_weight (scope_total kind mode receipt) =
    (match mode with S.CloneMode => 5 | S.OpenCloseMode => 6 end) +
      D.weighted D.record_weight (S.selected_dummy receipt) /\
  D.weighted D.byte_weight (scope_total kind mode receipt) =
    D.weighted D.byte_weight (S.selected_dummy receipt).
Proof.
  intros kind mode receipt. unfold scope_total. rewrite !S.weighted_add.
  destruct (scope_local_projection kind mode) as [HW [HR HB]].
  rewrite HW, HR, HB. repeat split; lia.
Qed.

Theorem scope_field_instantiates_output_local :
  forall dc dx dg kind mode dummy tag event,
  O.local_credit dc dx dg (fun _ => [dummy])
    (fun _ => scope_copy mode) (fun _ => scope_cleanup kind mode) tag event =
  S.parent_base event + scope_total kind mode (D.receipt dc dx dg dummy) event.
Proof.
  intros. unfold O.local_credit, O.local_root, O.replacements, O.sum_counts,
    O.dummy_receipt, S.parent_base, scope_total, scope_local, S.selected_dummy.
  cbn [fold_right]. lia.
Qed.

Theorem scope_assembly_transfers_existing_child_credits :
  forall dc dx dg kind mode dummy tag children event,
  O.output_credit
    (O.output dc dx dg (fun _ => [dummy])
      (fun _ => scope_copy mode) (fun _ => scope_cleanup kind mode)
      (W.Node tag children)) event =
  S.parent_base event + scope_total kind mode (D.receipt dc dx dg dummy) event +
  O.sum_counts O.output_credit
    (O.outputs dc dx dg (fun _ => [dummy])
      (fun _ => scope_copy mode) (fun _ => scope_cleanup kind mode) children) event.
Proof.
  intros. rewrite O.assembly_transfers_existing_child_credits.
  now rewrite scope_field_instantiates_output_local.
Qed.

(** Raw reconstruction reuses the existing scope-result shape. Unlike
    with_closing/Scope::new, it preserves an already-transformed body without
    invoking close again. Tuple notation describes returned parts only. *)
Definition from_parts {Pattern Body} (pattern : Pattern) (body : Body)
    : R.ScopeResult Pattern Body :=
  {| R.saved_pattern := pattern; R.saved_body := body |}.

Definition parts {Pattern Body} (scope : R.ScopeResult Pattern Body) :=
  (R.saved_pattern scope, R.saved_body scope).

Theorem raw_reconstruction_preserves_both_parts :
  forall Pattern Body (pattern : Pattern) (already_transformed_body : Body),
  parts (from_parts pattern already_transformed_body) =
    (pattern, already_transformed_body).
Proof. reflexivity. Qed.

Definition traced_from_parts {Pattern Body Binder}
    (pattern : Pattern) (body : Body)
    : R.ScopeResult Pattern Body * list (R.RecipeEvent Binder) :=
  (from_parts pattern body, [R.ConstructScope]).

Theorem raw_reconstruction_has_no_closing_dispatch :
  forall Pattern Body Binder (pattern : Pattern) (body : Body),
  @R.closing_depths Binder
    (snd (@traced_from_parts Pattern Body Binder pattern body)) = [].
Proof. reflexivity. Qed.

Print Assumptions single_replacement_matches_unnamed_binder_charge.
Print Assumptions multi_replacement_matches_empty_pattern_charge.
Print Assumptions scope_local_is_required_plus_extra.
Print Assumptions scope_total_is_required_total_plus_extra.
Print Assumptions scope_extra_projection.
Print Assumptions scope_local_projection.
Print Assumptions scope_total_projection.
Print Assumptions scope_field_instantiates_output_local.
Print Assumptions scope_assembly_transfers_existing_child_credits.
Print Assumptions raw_reconstruction_preserves_both_parts.
Print Assumptions raw_reconstruction_has_no_closing_dispatch.
End ScopeBindingReservation.
