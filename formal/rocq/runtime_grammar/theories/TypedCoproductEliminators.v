(** * Shared eliminators for the generated typed reconstruction coproduct

    The generated reconstruction value is a closed dependent coproduct: every
    category and every exact leaf carrier contributes one injection.  Assembly
    previously repeated the same elimination match at every field occurrence.
    A single generated partial eliminator per injection is observationally the
    same match, while its result type still depends on the requested tag.

    This module proves the representation-independent part of that factoring.
    The concrete Rust enum supplies the finite injection family; generated
    methods are instances of [shared_project] and optional methods are
    instances of [shared_optional_project].  A failed projection is pure and
    therefore cannot consume or publish a reconstruction-stack value. *)

From Stdlib Require Import List Arith.PeanoNat Logic.Eqdep_dec.
Import ListNotations.
Set Implicit Arguments.

Module TypedCoproductEliminators.

  Section PayloadFamily.

    Variable Payload : nat -> Type.

    Definition PackedValue : Type := { tag : nat & Payload tag }.

    Definition inject (tag : nat) (value : Payload tag) : PackedValue :=
      existT Payload tag value.

    Definition inline_project
        (expected : nat) (packed : PackedValue) : option (Payload expected) :=
      match packed with
      | existT _ actual value =>
          match Nat.eq_dec actual expected with
          | left equal => Some (eq_rect actual Payload value expected equal)
          | right _ => None
          end
      end.

    (** The shared method has the same closed match as the former inline arm.
        It is named separately so the correspondence theorem is explicit. *)
    Definition shared_project
        (expected : nat) (packed : PackedValue) : option (Payload expected) :=
      match packed with
      | existT _ actual value =>
          match Nat.eq_dec actual expected with
          | left equal => Some (eq_rect actual Payload value expected equal)
          | right _ => None
          end
      end.

    Theorem shared_project_refines_inline_match : forall expected packed,
        shared_project expected packed = inline_project expected packed.
    Proof.
      intros expected [actual value]. reflexivity.
    Qed.

    Theorem shared_project_inject : forall tag (value : Payload tag),
        shared_project tag (@inject tag value) = Some value.
    Proof.
      intros tag value. unfold shared_project, inject.
      destruct (Nat.eq_dec tag tag) as [equal | unequal].
      - pose proof (eq_rect_eq_dec Nat.eq_dec Payload value equal)
          as Htransport.
        now rewrite <- Htransport.
      - now exfalso; apply unequal.
    Qed.

    Theorem shared_project_rejects_other_injection :
      forall expected actual (value : Payload actual),
        actual <> expected ->
        shared_project expected (@inject actual value) = None.
    Proof.
      intros expected actual value Hdifferent.
      unfold shared_project, inject.
      destruct (Nat.eq_dec actual expected) as [equal | unequal].
      - now exfalso; apply Hdifferent.
      - reflexivity.
    Qed.

    Inductive PackedField : Type :=
    | PresentField : PackedValue -> PackedField
    | AbsentField : nat -> PackedField.

    Inductive OptionalPayload (expected : nat) : Type :=
    | PresentPayload : Payload expected -> OptionalPayload expected
    | AbsentPayload : OptionalPayload expected.

    Definition inline_optional_project
        (expected field_index : nat) (field : PackedField)
        : option (OptionalPayload expected) :=
      match field with
      | PresentField packed =>
          match inline_project expected packed with
          | Some value => Some (PresentPayload value)
          | None => None
          end
      | AbsentField actual_index =>
          if Nat.eq_dec actual_index field_index
          then Some (@AbsentPayload expected)
          else None
      end.

    Definition shared_optional_project
        (expected field_index : nat) (field : PackedField)
        : option (OptionalPayload expected) :=
      match field with
      | PresentField packed =>
          match shared_project expected packed with
          | Some value => Some (PresentPayload value)
          | None => None
          end
      | AbsentField actual_index =>
          if Nat.eq_dec actual_index field_index
          then Some (@AbsentPayload expected)
          else None
      end.

    Theorem shared_optional_refines_inline_match :
      forall expected field_index field,
        shared_optional_project expected field_index field =
        inline_optional_project expected field_index field.
    Proof.
      intros expected field_index [packed | actual_index]; cbn.
      - now rewrite shared_project_refines_inline_match.
      - reflexivity.
    Qed.

    Theorem shared_optional_present_round_trip :
      forall tag field_index (value : Payload tag),
        shared_optional_project tag field_index
          (PresentField (@inject tag value)) =
        Some (PresentPayload value).
    Proof.
      intros. change
        (match shared_project tag (@inject tag value) with
         | Some projected => Some (PresentPayload projected)
         | None => None
         end = Some (PresentPayload value)).
      now rewrite shared_project_inject.
    Qed.

    Theorem shared_optional_absent_round_trip : forall tag field_index,
        shared_optional_project tag field_index (AbsentField field_index) =
        Some (@AbsentPayload tag).
    Proof.
      intros. cbn. destruct (Nat.eq_dec field_index field_index).
      - reflexivity.
      - now exfalso; apply n.
    Qed.

    Theorem shared_optional_rejects_wrong_absence_index :
      forall tag field_index actual_index,
        actual_index <> field_index ->
        shared_optional_project tag field_index (AbsentField actual_index) = None.
    Proof.
      intros tag field_index actual_index Hdifferent. cbn.
      destruct (Nat.eq_dec actual_index field_index) as [equal | unequal].
      - now exfalso; apply Hdifferent.
      - reflexivity.
    Qed.

    Theorem shared_optional_rejects_other_injection :
      forall expected actual field_index (value : Payload actual),
        actual <> expected ->
        shared_optional_project expected field_index
          (PresentField (@inject actual value)) = None.
    Proof.
      intros. change
        (match shared_project expected (@inject actual value) with
         | Some projected => Some (PresentPayload projected)
         | None => None
         end = None).
      now rewrite shared_project_rejects_other_injection.
    Qed.

    (** A Rust [Vec::pop] removes the last element.  The model uses a top-first
        stack so that successful projection returns the exact untouched tail;
        failure returns no successor state at all. *)
    Definition pop_shared
        (expected : nat) (stack : list PackedValue)
        : option (Payload expected * list PackedValue) :=
      match stack with
      | [] => None
      | packed :: rest =>
          match shared_project expected packed with
          | Some value => Some (value, rest)
          | None => None
          end
      end.

    Definition pop_inline
        (expected : nat) (stack : list PackedValue)
        : option (Payload expected * list PackedValue) :=
      match stack with
      | [] => None
      | packed :: rest =>
          match inline_project expected packed with
          | Some value => Some (value, rest)
          | None => None
          end
      end.

    Theorem pop_shared_refines_inline : forall expected stack,
        pop_shared expected stack = pop_inline expected stack.
    Proof.
      intros expected [|packed rest]; [reflexivity |]. cbn.
      now rewrite shared_project_refines_inline_match.
    Qed.

    Theorem pop_shared_success_preserves_exact_tail :
      forall expected stack value rest,
        pop_shared expected stack = Some (value, rest) ->
        exists packed, stack = packed :: rest.
    Proof.
      intros expected [|packed tail] value rest Hpop; cbn in Hpop;
        [discriminate |].
      destruct (shared_project expected packed); try discriminate.
      inversion Hpop; subst. now exists packed.
    Qed.

    Theorem pop_shared_rejects_mismatched_top_without_successor :
      forall expected actual (value : Payload actual) rest,
        actual <> expected ->
        pop_shared expected (@inject actual value :: rest) = None.
    Proof.
      intros. change
        (match shared_project expected (@inject actual value) with
         | Some projected => Some (projected, rest)
         | None => None
         end = None).
      now rewrite shared_project_rejects_other_injection.
    Qed.

  End PayloadFamily.

  Print Assumptions shared_project_refines_inline_match.
  Print Assumptions shared_project_inject.
  Print Assumptions shared_project_rejects_other_injection.
  Print Assumptions shared_optional_refines_inline_match.
  Print Assumptions shared_optional_present_round_trip.
  Print Assumptions shared_optional_absent_round_trip.
  Print Assumptions shared_optional_rejects_wrong_absence_index.
  Print Assumptions shared_optional_rejects_other_injection.
  Print Assumptions pop_shared_refines_inline.
  Print Assumptions pop_shared_success_preserves_exact_tail.
  Print Assumptions pop_shared_rejects_mismatched_top_without_successor.

End TypedCoproductEliminators.
