(** * Exact elimination of dead generated match fallbacks

    A generator that emits exactly one arm for every constructor has already
    constructed the total eliminator for that datatype.  Adding a wildcard
    arm is semantically dead and asks the Rust compiler to diagnose and retain
    unreachable syntax.  This model makes the required precondition explicit:
    the constructor census is duplicate-free and covers the queried variant.

    Empty generated case tables are separate.  A source expression shaped like
    [Some(match key { _ => return None })] returns [None] before [Some] can be
    constructed.  Its exact normal form is therefore the direct absence
    result, not a fabricated value and not an unreachable wrapper. *)

From Stdlib Require Import List.
Import ListNotations.
Set Implicit Arguments.

Module ExhaustiveGeneratedMatch.

  Section Dispatch.
    Context {Variant Result : Type}.
    Variable variant_eq_dec : forall left right : Variant, {left = right} + {left <> right}.

    Fixpoint lookup
        (variant : Variant) (arms : list (Variant * Result)) : option Result :=
      match arms with
      | [] => None
      | (candidate, result) :: rest =>
          if variant_eq_dec variant candidate
          then Some result
          else lookup variant rest
      end.

    Lemma lookup_generated_arms :
      forall constructors action variant,
        NoDup constructors ->
        In variant constructors ->
        lookup variant (map (fun constructor => (constructor, action constructor)) constructors) =
        Some (action variant).
    Proof.
      intros constructors; induction constructors as [|constructor rest IH];
        intros action variant Hnodup Hin.
      - inversion Hin.
      - inversion Hnodup as [|? ? Hnotin Hrest]; subst.
        simpl in Hin. destruct Hin as [Heq | Hin].
        + subst constructor. simpl.
          destruct (variant_eq_dec variant variant); [reflexivity | contradiction].
        + simpl. destruct (variant_eq_dec variant constructor) as [Heq | Hneq].
          * subst constructor. exfalso. apply Hnotin. exact Hin.
          * apply IH; assumption.
    Qed.

    Definition generated_with_fallback
        (constructors : list Variant)
        (action : Variant -> Result)
        (fallback : Result)
        (variant : Variant) : Result :=
      match lookup variant
        (map (fun constructor => (constructor, action constructor)) constructors) with
      | Some result => result
      | None => fallback
      end.

    Definition generated_exhaustive
        (action : Variant -> Result) (variant : Variant) : Result :=
      action variant.

    Theorem exhaustive_fallback_elimination_preserves_dispatch :
      forall constructors action fallback variant,
        NoDup constructors ->
        In variant constructors ->
        generated_with_fallback constructors action fallback variant =
        generated_exhaustive action variant.
    Proof.
      intros constructors action fallback variant Hnodup Hin.
      unfold generated_with_fallback, generated_exhaustive.
      rewrite lookup_generated_arms; [reflexivity | exact Hnodup | exact Hin].
    Qed.

  End Dispatch.

  (** A small control-flow model for generated Rust expressions.  [Early]
      corresponds to [return] from the surrounding function; [Continue]
      corresponds to an ordinary expression value. *)
  Inductive Flow (A : Type) : Type :=
  | Early : option A -> Flow A
  | Continue : A -> Flow A.

  Arguments Early {A} _.
  Arguments Continue {A} _.

  Definition wrap_some {A : Type} (flow : Flow A) : Flow A :=
    match flow with
    | Early result => Early result
    | Continue value => Early (Some value)
    end.

  Definition empty_case_table {A : Type} : Flow A := Early None.

  Theorem empty_case_wrapper_is_direct_absence :
    forall A,
      wrap_some (@empty_case_table A) = Early None.
  Proof.
    reflexivity.
  Qed.

  (** For a single-constructor generated destructure, matching cannot fail.
      The fallback branch of [let PATTERN = value else ...] is therefore dead. *)
  Inductive Singleton (A : Type) : Type := only : A -> Singleton A.

  Definition destructure_with_fallback {A B : Type}
      (value : Singleton A) (body : A -> B) (fallback : B) : B :=
    match value with
    | only payload => body payload
    end.

  Definition destructure_exact {A B : Type}
      (value : Singleton A) (body : A -> B) : B :=
    match value with
    | only payload => body payload
    end.

  Theorem irrefutable_fallback_elimination_preserves_result :
    forall (A B : Type) (value : Singleton A) (body : A -> B) (fallback : B),
      destructure_with_fallback value body fallback =
      destructure_exact value body.
  Proof.
    intros A B value body fallback. destruct value. reflexivity.
  Qed.

  (** Constructor coverage is not, by itself, pattern-space coverage.  An arm
      may name the only outer constructor while accepting only part of that
      constructor's payload.  The generated variable-inference arm is exactly
      this shape: it accepts [Free] variables and must fall through for [Bound]
      variables. *)
  Section PatternSpace.
    Context {Value Result : Type}.

    Definition pattern_total (arms : Value -> option Result) : Prop :=
      forall value, exists result, arms value = Some result.

    Definition pattern_dispatch
        (arms : Value -> option Result) (fallback : Result) (value : Value) : Result :=
      match arms value with
      | Some result => result
      | None => fallback
      end.

    Theorem total_pattern_fallback_elimination :
      forall (arms : Value -> option Result) fallback value result,
        arms value = Some result ->
        pattern_dispatch arms fallback value = result.
    Proof.
      intros arms fallback value result Hcovered.
      unfold pattern_dispatch. rewrite Hcovered. reflexivity.
    Qed.
  End PatternSpace.

  Inductive VarPayload : Type := Free | Bound.
  Inductive OneConstructor : Type := VarCtor : VarPayload -> OneConstructor.

  Definition free_only_arm (value : OneConstructor) : option bool :=
    match value with
    | VarCtor Free => Some true
    | VarCtor Bound => None
    end.

  Theorem singleton_constructor_label_does_not_imply_pattern_total :
    ~ pattern_total free_only_arm.
  Proof.
    intro Htotal.
    destruct (Htotal (VarCtor Bound)) as [result Hresult].
    discriminate Hresult.
  Qed.

  Theorem partial_variable_arm_requires_bound_fallback :
    pattern_dispatch free_only_arm false (VarCtor Bound) = false.
  Proof.
    reflexivity.
  Qed.

  Print Assumptions exhaustive_fallback_elimination_preserves_dispatch.
  Print Assumptions empty_case_wrapper_is_direct_absence.
  Print Assumptions irrefutable_fallback_elimination_preserves_result.
  Print Assumptions total_pattern_fallback_elimination.
  Print Assumptions singleton_constructor_label_does_not_imply_pattern_total.
  Print Assumptions partial_variable_arm_requires_bound_fallback.

End ExhaustiveGeneratedMatch.
