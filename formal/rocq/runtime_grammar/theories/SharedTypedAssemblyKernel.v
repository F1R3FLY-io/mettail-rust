(** * One typed assembly kernel for normalization and Dovetail

    Normalization and inverse Dovetail reconstruction are two producers of the
    same checked constructor fields.  Their scheduling differs, but ordinary
    constructor materialization must not.  This module factors validation and
    assembly through one dependent coproduct carrier and proves that replacing
    repeated inline projections by shared eliminators preserves acceptance,
    rejection, and the assembled typed result.

    Concrete generated categories instantiate [Payload].  Optional absence is
    indexed by its declared field position.  The frame view is pure and exact:
    it exposes one bounded buffer slice while retaining the untouched prefix
    and suffix as explicit observations. *)

From Stdlib Require Import List Bool Arith.PeanoNat Lia.
From RuntimeGrammar Require Import TypedCoproductEliminators.
Import ListNotations.
Set Implicit Arguments.

Module SharedTypedAssemblyKernel.
  Import TypedCoproductEliminators.

  Inductive FieldSpec : Type :=
  | RequiredField : nat -> FieldSpec
  | OptionalField : nat -> nat -> FieldSpec.

  Section Kernel.
    Variable Payload : nat -> Type.
    Variable Ast : Type.

    Definition Packed := @PackedValue Payload.
    Definition Field := @PackedField Payload.

    Definition inline_field_valid
        (spec : FieldSpec) (field : Field) : bool :=
      match spec with
      | RequiredField expected =>
          match field with
          | PresentField packed =>
              match inline_project expected packed with
              | Some _ => true
              | None => false
              end
          | @AbsentField _ _ => false
          end
      | OptionalField expected field_index =>
          match inline_optional_project expected field_index field with
          | Some _ => true
          | None => false
          end
      end.

    Definition shared_field_valid
        (spec : FieldSpec) (field : Field) : bool :=
      match spec with
      | RequiredField expected =>
          match field with
          | PresentField packed =>
              match shared_project expected packed with
              | Some _ => true
              | None => false
              end
          | @AbsentField _ _ => false
          end
      | OptionalField expected field_index =>
          match shared_optional_project expected field_index field with
          | Some _ => true
          | None => false
          end
      end.

    Theorem shared_field_validation_refines_inline : forall spec field,
        shared_field_valid spec field = inline_field_valid spec field.
    Proof.
      intros [expected | expected field_index] [packed | actual_index]; cbn.
      - now rewrite shared_project_refines_inline_match.
      - reflexivity.
      - now rewrite shared_project_refines_inline_match.
      - reflexivity.
    Qed.

    Fixpoint fields_valid
        (validator : FieldSpec -> Field -> bool)
        (specs : list FieldSpec) (fields : list Field) : bool :=
      match specs, fields with
      | [], [] => true
      | spec :: spec_rest, field :: field_rest =>
          validator spec field && fields_valid validator spec_rest field_rest
      | _, _ => false
      end.

    Theorem shared_fields_validation_refines_inline : forall specs fields,
        fields_valid shared_field_valid specs fields =
        fields_valid inline_field_valid specs fields.
    Proof.
      induction specs as [|spec spec_rest IH]; intros fields;
        destruct fields as [|field field_rest].
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - cbn. now rewrite shared_field_validation_refines_inline, IH.
    Qed.

    Variable assemble : nat -> nat -> list Field -> option Ast.

    Definition inline_kernel
        (category constructor : nat) (specs : list FieldSpec)
        (fields : list Field) : option Ast :=
      if fields_valid inline_field_valid specs fields
      then assemble category constructor fields
      else None.

    Definition shared_kernel
        (category constructor : nat) (specs : list FieldSpec)
        (fields : list Field) : option Ast :=
      if fields_valid shared_field_valid specs fields
      then assemble category constructor fields
      else None.

    Theorem shared_kernel_refines_inline :
      forall category constructor specs fields,
        shared_kernel category constructor specs fields =
        inline_kernel category constructor specs fields.
    Proof.
      intros. unfold shared_kernel, inline_kernel.
      now rewrite shared_fields_validation_refines_inline.
    Qed.

    Theorem required_wrong_tag_fails_closed :
      forall expected actual (value : Payload actual),
        actual <> expected ->
        shared_field_valid (RequiredField expected)
          (PresentField (@inject Payload actual value)) = false.
    Proof.
      intros expected actual value Hdifferent.
      change
        (match shared_project expected (@inject Payload actual value) with
         | Some _ => true
         | None => false
         end = false).
      now rewrite shared_project_rejects_other_injection.
    Qed.

    Theorem optional_wrong_absence_index_fails_closed :
      forall expected field_index actual_index,
        actual_index <> field_index ->
        shared_field_valid (OptionalField expected field_index)
          (@AbsentField Payload actual_index) = false.
    Proof.
      intros expected field_index actual_index Hdifferent.
      change
        (match shared_optional_project expected field_index
          (@AbsentField Payload actual_index) with
         | Some _ => true
         | None => false
         end = false).
      now rewrite shared_optional_rejects_wrong_absence_index.
    Qed.

    Inductive Producer : Type := Normalization | Dovetail.
    Variable produce : Producer -> nat -> nat -> option (list Field).

    Definition run_producer
        (producer : Producer) (category constructor : nat)
        (specs : list FieldSpec) : option Ast :=
      match produce producer category constructor with
      | Some fields => shared_kernel category constructor specs fields
      | None => None
      end.

    Theorem producers_agree_on_equal_checked_fields :
      forall category constructor specs fields,
        produce Normalization category constructor = Some fields ->
        produce Dovetail category constructor = Some fields ->
        run_producer Normalization category constructor specs =
        run_producer Dovetail category constructor specs.
    Proof.
      intros category constructor specs fields Hnormal Hdovetail.
      unfold run_producer. now rewrite Hnormal, Hdovetail.
    Qed.

    (** A normalization visit records recursive results in random-access slots,
        whereas inverse reconstruction publishes coproduct fields directly.
        The initial implementation mirrored the latter literally by scheduling
        one extra move task after every normalization child.  The fused producer
        delays those injections until its assembly frame runs.  Both producers
        traverse the same already-completed field origins in semantic order. *)
    Inductive FieldOrigin : Type :=
    | RecursiveResult : Field -> FieldOrigin
    | StructuralValue : Field -> FieldOrigin.

    Definition materialize_origin (origin : FieldOrigin) : Field :=
      match origin with
      | RecursiveResult field | StructuralValue field => field
      end.

    Fixpoint staged_publish
        (origins : list FieldOrigin) (published : list Field) : list Field :=
      match origins with
      | [] => published
      | origin :: rest =>
          staged_publish rest (published ++ [materialize_origin origin])
      end.

    Definition staged_fields (origins : list FieldOrigin) : list Field :=
      staged_publish origins [].

    Definition fused_fields (origins : list FieldOrigin) : list Field :=
      map materialize_origin origins.

    Lemma staged_publish_app : forall origins published,
        staged_publish origins published = published ++ fused_fields origins.
    Proof.
      induction origins as [|origin rest IH]; intro published.
      - now rewrite app_nil_r.
      - cbn. rewrite IH. unfold fused_fields in *. cbn.
        now rewrite <- app_assoc.
    Qed.

    Theorem fused_normalization_producer_preserves_field_order : forall origins,
        fused_fields origins = staged_fields origins.
    Proof.
      intro origins. unfold staged_fields.
      rewrite staged_publish_app. reflexivity.
    Qed.

    Definition run_staged_normalization
        (category constructor : nat) (specs : list FieldSpec)
        (origins : list FieldOrigin) : option Ast :=
      shared_kernel category constructor specs (staged_fields origins).

    Definition run_fused_normalization
        (category constructor : nat) (specs : list FieldSpec)
        (origins : list FieldOrigin) : option Ast :=
      shared_kernel category constructor specs (fused_fields origins).

    Theorem fused_normalization_producer_preserves_kernel_result :
      forall category constructor specs origins,
        run_fused_normalization category constructor specs origins =
        run_staged_normalization category constructor specs origins.
    Proof.
      intros. unfold run_fused_normalization, run_staged_normalization.
      now rewrite fused_normalization_producer_preserves_field_order.
    Qed.

    (** The constructor kernel itself returns the statically known category
        payload.  A heterogeneous consumer such as Dovetail injects that
        result into the closed coproduct; normalization, whose category is
        already fixed by its typed task, consumes the payload directly.  The
        formerly shared "inject then immediately project" path is therefore
        an observationally redundant wrapper around the same kernel result. *)
    Definition publish_typed_result
        (category : nat) (result : option (Payload category))
        : option Packed :=
      match result with
      | Some value => Some (@inject Payload category value)
      | None => None
      end.

    Definition observe_published_result
        (category : nat) (result : option (Payload category))
        : option (Payload category) :=
      match @publish_typed_result category result with
      | Some packed => shared_project category packed
      | None => None
      end.

    Theorem typed_result_output_factorization :
      forall category (result : option (Payload category)),
        @observe_published_result category result = result.
    Proof.
      intros category [value |]; [| reflexivity].
      unfold observe_published_result, publish_typed_result.
      now rewrite shared_project_inject.
    Qed.

    (** A completed normalization child was formerly projected into a
        normalization-only typed wrapper and then reinjected into the shared
        coproduct before assembly.  Storing the shared injection directly in
        the random-access result buffer removes that representation round trip
        without changing the value observed by the constructor kernel. *)
    Definition project_then_reinject
        (category : nat) (packed : Packed) : option Packed :=
      match shared_project category packed with
      | Some value => Some (@inject Payload category value)
      | None => None
      end.

    Theorem shared_result_buffer_fusion :
      forall category (value : Payload category),
        @project_then_reinject category (@inject Payload category value) =
        Some (@inject Payload category value).
    Proof.
      intros. unfold project_then_reinject.
      now rewrite shared_project_inject.
    Qed.

    Record FrameView : Type := frame_view {
      untouched_prefix : list Field;
      owned_fields : list Field;
      untouched_suffix : list Field
    }.

    Definition exact_frame_view
        (value_base value_count : nat) (buffer : list Field)
        : option FrameView :=
      if Nat.leb (value_base + value_count) (length buffer)
      then Some (frame_view
        (firstn value_base buffer)
        (firstn value_count (skipn value_base buffer))
        (skipn (value_base + value_count) buffer))
      else None.

    Theorem exact_frame_view_has_declared_count :
      forall value_base value_count buffer view,
        exact_frame_view value_base value_count buffer = Some view ->
        length (owned_fields view) = value_count.
    Proof.
      intros value_base value_count buffer view Hview.
      unfold exact_frame_view in Hview.
      destruct (Nat.leb (value_base + value_count) (length buffer))
        eqn:Hbounds; try discriminate.
      inversion Hview; subst view. cbn.
      apply Nat.leb_le in Hbounds.
      rewrite length_firstn, length_skipn. lia.
    Qed.

    Theorem exact_frame_view_recombines_buffer :
      forall value_base value_count buffer view,
        exact_frame_view value_base value_count buffer = Some view ->
        buffer = untouched_prefix view ++ owned_fields view ++
          untouched_suffix view.
    Proof.
      intros value_base value_count buffer view Hview.
      unfold exact_frame_view in Hview.
      destruct (Nat.leb (value_base + value_count) (length buffer))
        eqn:Hbounds; try discriminate.
      inversion Hview; subst view. cbn.
      rewrite <- (firstn_skipn value_base buffer) at 1. f_equal.
      rewrite <- (firstn_skipn value_count (skipn value_base buffer)) at 1.
      f_equal.
      rewrite skipn_skipn. f_equal. lia.
    Qed.

    Definition shared_kernel_from_buffer
        (category constructor : nat) (specs : list FieldSpec)
        (value_base value_count : nat) (buffer : list Field) : option Ast :=
      match exact_frame_view value_base value_count buffer with
      | Some view => shared_kernel category constructor specs (owned_fields view)
      | None => None
      end.

    Theorem out_of_bounds_frame_fails_closed :
      forall category constructor specs value_base value_count buffer,
        length buffer < value_base + value_count ->
        shared_kernel_from_buffer category constructor specs
          value_base value_count buffer = None.
    Proof.
      intros category constructor specs value_base value_count buffer Hbounds.
      unfold shared_kernel_from_buffer, exact_frame_view.
      destruct (Nat.leb (value_base + value_count) (length buffer))
        eqn:Hleb; [apply Nat.leb_le in Hleb; lia | reflexivity].
    Qed.

  End Kernel.

  Record BinderImage : Type := binder_image {
    binder_name : nat;
    binder_body : nat
  }.

  Definition alpha_observation (binder : BinderImage) : nat :=
    binder_body binder.

  Theorem normalization_and_fresh_dovetail_binders_are_alpha_equal :
    forall original fresh body,
      alpha_observation (binder_image original body) =
      alpha_observation (binder_image fresh body).
  Proof.
    reflexivity.
  Qed.

  Print Assumptions shared_field_validation_refines_inline.
  Print Assumptions shared_fields_validation_refines_inline.
  Print Assumptions shared_kernel_refines_inline.
  Print Assumptions required_wrong_tag_fails_closed.
  Print Assumptions optional_wrong_absence_index_fails_closed.
  Print Assumptions producers_agree_on_equal_checked_fields.
  Print Assumptions fused_normalization_producer_preserves_field_order.
  Print Assumptions fused_normalization_producer_preserves_kernel_result.
  Print Assumptions typed_result_output_factorization.
  Print Assumptions shared_result_buffer_fusion.
  Print Assumptions exact_frame_view_has_declared_count.
  Print Assumptions exact_frame_view_recombines_buffer.
  Print Assumptions out_of_bounds_frame_fails_closed.
  Print Assumptions normalization_and_fresh_dovetail_binders_are_alpha_equal.

End SharedTypedAssemblyKernel.
