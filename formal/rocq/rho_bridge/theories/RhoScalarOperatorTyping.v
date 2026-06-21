(*
 * RhoScalarOperatorTyping: type-sensitive classifier for scalar Rho lowering.
 *
 * Rust bridge:
 *   rholang-codegen/src/lower.rs
 *
 * The lowerer may not choose a Rholang expression from the surface token alone.
 * Calculator has both `Int "+" Int -> Int` and `Str "+" Str -> Str`; the former
 * is Rholang integer `EPlus`, while the latter is Rholang string `EPlusPlus`.
 * This model proves the shape of that classifier and the fail-closed behavior
 * for combinations without an exact Rholang scalar expression.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.

Import ListNotations.

Section RhoScalarOperatorTyping.

  Inductive ScalarTy : Type :=
  | TInt
  | TBool
  | TStr.

  Inductive NativeKind : Type :=
  | NInt8
  | NInt16
  | NInt32
  | NInt64
  | NUInt32
  | NFloat64
  | NBool
  | NStr
  | NBigInt
  | NBigRat
  | NFixed
  | NOther.

  Record CategoryDecl : Type := {
    category_name_id : nat;
    category_native_kind : option NativeKind
  }.

  Definition native_kind_scalar (kind : NativeKind) : option ScalarTy :=
    match kind with
    | NInt8 | NInt16 | NInt32 | NInt64 => Some TInt
    | NBool => Some TBool
    | NStr => Some TStr
    | NUInt32 | NFloat64 | NBigInt | NBigRat | NFixed | NOther => None
    end.

  Definition category_decl_scalar (decl : CategoryDecl) : option ScalarTy :=
    match category_native_kind decl with
    | Some kind => native_kind_scalar kind
    | None => None
    end.

  Inductive SurfaceBinOp : Type :=
  | SPlus
  | SMinus
  | SMult
  | SDiv
  | SMod
  | SEq
  | SNeq
  | SLt
  | SGt
  | SLte
  | SGte
  | SAnd
  | SOr
  | SConcat.

  Inductive RhoBinOp : Type :=
  | RAdd
  | RSub
  | RMul
  | RDiv
  | RMod
  | REq
  | RNeq
  | RLt
  | RGt
  | RLte
  | RGte
  | RAnd
  | ROr
  | RConcat.

  Inductive SurfaceUnOp : Type :=
  | SNot
  | SNeg.

  Inductive RhoUnOp : Type :=
  | RNot
  | RNeg.

  Inductive ScalarContractShape : Type :=
  | AbiUnaryPrefix : ScalarTy -> ScalarTy -> ScalarContractShape
  | AbiBinaryInfix : ScalarTy -> ScalarTy -> ScalarTy -> ScalarContractShape.

  Record ScalarContractAbi : Type := {
    abi_label_id : nat;
    abi_shape : ScalarContractShape;
    abi_formal_count : nat;
    abi_return_channel_position : nat
  }.

  Definition unary_contract_abi
      (label : nat)
      (arg result : ScalarTy) : ScalarContractAbi :=
    {| abi_label_id := label;
       abi_shape := AbiUnaryPrefix arg result;
       abi_formal_count := 2;
       abi_return_channel_position := 1 |}.

  Definition binary_contract_abi
      (label : nat)
      (lhs rhs result : ScalarTy) : ScalarContractAbi :=
    {| abi_label_id := label;
       abi_shape := AbiBinaryInfix lhs rhs result;
       abi_formal_count := 3;
       abi_return_channel_position := 2 |}.

  Definition scalar_contract_operand_types
      (shape : ScalarContractShape) : list ScalarTy :=
    match shape with
    | AbiUnaryPrefix arg _ => [arg]
    | AbiBinaryInfix lhs rhs _ => [lhs; rhs]
    end.

  Definition scalar_contract_result_type
      (shape : ScalarContractShape) : ScalarTy :=
    match shape with
    | AbiUnaryPrefix _ result => result
    | AbiBinaryInfix _ _ result => result
    end.

  Record ScalarInvocationPlan : Type := {
    plan_label_id : nat;
    plan_operand_types : list ScalarTy;
    plan_result_type : ScalarTy
  }.

  Definition invocation_plan_from_abi
      (abi : ScalarContractAbi) : ScalarInvocationPlan :=
    {| plan_label_id := abi_label_id abi;
       plan_operand_types := scalar_contract_operand_types (abi_shape abi);
       plan_result_type := scalar_contract_result_type (abi_shape abi) |}.

  Definition typed_binop
      (op : SurfaceBinOp)
      (lhs rhs result : ScalarTy) : option RhoBinOp :=
    match lhs, rhs with
    | TInt, TInt =>
        match op, result with
        | SPlus, TInt => Some RAdd
        | SMinus, TInt => Some RSub
        | SMult, TInt => Some RMul
        | SDiv, TInt => Some RDiv
        | SMod, TInt => Some RMod
        | SEq, TBool => Some REq
        | SNeq, TBool => Some RNeq
        | SLt, TBool => Some RLt
        | SGt, TBool => Some RGt
        | SLte, TBool => Some RLte
        | SGte, TBool => Some RGte
        | _, _ => None
        end
    | TBool, TBool =>
        match op, result with
        | SEq, TBool => Some REq
        | SNeq, TBool => Some RNeq
        | SLt, TBool => Some RLt
        | SGt, TBool => Some RGt
        | SLte, TBool => Some RLte
        | SGte, TBool => Some RGte
        | SAnd, TBool => Some RAnd
        | SOr, TBool => Some ROr
        | _, _ => None
        end
    | TStr, TStr =>
        match op, result with
        | SPlus, TStr => Some RConcat
        | SConcat, TStr => Some RConcat
        | SEq, TBool => Some REq
        | SNeq, TBool => Some RNeq
        | SLt, TBool => Some RLt
        | SGt, TBool => Some RGt
        | SLte, TBool => Some RLte
        | SGte, TBool => Some RGte
        | _, _ => None
        end
    | _, _ => None
    end.

  Definition typed_unop
      (op : SurfaceUnOp)
      (arg result : ScalarTy) : option RhoUnOp :=
    match op, arg, result with
    | SNot, TBool, TBool => Some RNot
    | SNeg, TInt, TInt => Some RNeg
    | _, _, _ => None
    end.

  Definition typed_binop_abi
      (label : nat)
      (op : SurfaceBinOp)
      (lhs rhs result : ScalarTy) : option ScalarContractAbi :=
    match typed_binop op lhs rhs result with
    | Some _ => Some (binary_contract_abi label lhs rhs result)
    | None => None
    end.

  Definition typed_unop_abi
      (label : nat)
      (op : SurfaceUnOp)
      (arg result : ScalarTy) : option ScalarContractAbi :=
    match typed_unop op arg result with
    | Some _ => Some (unary_contract_abi label arg result)
    | None => None
    end.

  Definition typed_binop_from_categories
      (op : SurfaceBinOp)
      (lhs rhs result : CategoryDecl) : option RhoBinOp :=
    match category_decl_scalar lhs,
          category_decl_scalar rhs,
          category_decl_scalar result with
    | Some lhs_ty, Some rhs_ty, Some result_ty =>
        typed_binop op lhs_ty rhs_ty result_ty
    | _, _, _ => None
    end.

  Theorem category_name_does_not_affect_native_scalar : forall name1 name2 kind,
    category_decl_scalar
      {| category_name_id := name1; category_native_kind := Some kind |}
    =
    category_decl_scalar
      {| category_name_id := name2; category_native_kind := Some kind |}.
  Proof. reflexivity. Qed.

  Theorem scalar_named_structural_category_rejected : forall name,
    category_decl_scalar
      {| category_name_id := name; category_native_kind := None |} = None.
  Proof. reflexivity. Qed.

  Theorem renamed_native_categories_lower_identically : forall op name1 name2 name3 name4 name5 name6 kind_l kind_r kind_result,
    typed_binop_from_categories
      op
      {| category_name_id := name1; category_native_kind := Some kind_l |}
      {| category_name_id := name2; category_native_kind := Some kind_r |}
      {| category_name_id := name3; category_native_kind := Some kind_result |}
    =
    typed_binop_from_categories
      op
      {| category_name_id := name4; category_native_kind := Some kind_l |}
      {| category_name_id := name5; category_native_kind := Some kind_r |}
      {| category_name_id := name6; category_native_kind := Some kind_result |}.
  Proof. reflexivity. Qed.

  Theorem category_based_lowering_requires_native_payloads : forall op lhs rhs result rho,
    typed_binop_from_categories op lhs rhs result = Some rho ->
    exists lhs_ty rhs_ty result_ty,
      category_decl_scalar lhs = Some lhs_ty /\
      category_decl_scalar rhs = Some rhs_ty /\
      category_decl_scalar result = Some result_ty /\
      typed_binop op lhs_ty rhs_ty result_ty = Some rho.
  Proof.
    intros op lhs rhs result rho Hlower.
    unfold typed_binop_from_categories in Hlower.
    destruct (category_decl_scalar lhs) as [lhs_ty |] eqn:Hlhs; try discriminate.
    destruct (category_decl_scalar rhs) as [rhs_ty |] eqn:Hrhs; try discriminate.
    destruct (category_decl_scalar result) as [result_ty |] eqn:Hresult; try discriminate.
    exists lhs_ty, rhs_ty, result_ty. repeat split; assumption.
  Qed.

  Theorem typed_binop_abi_success_matches_typed_operator :
    forall label op lhs rhs result abi,
      typed_binop_abi label op lhs rhs result = Some abi ->
      abi = binary_contract_abi label lhs rhs result /\
      exists rho, typed_binop op lhs rhs result = Some rho.
  Proof.
    intros label op lhs rhs result abi Habi.
    unfold typed_binop_abi in Habi.
    destruct (typed_binop op lhs rhs result) as [rho |] eqn:Htyped; try discriminate.
    inversion Habi; subst. split; [reflexivity | exists rho; reflexivity].
  Qed.

  Theorem typed_unop_abi_success_matches_typed_operator :
    forall label op arg result abi,
      typed_unop_abi label op arg result = Some abi ->
      abi = unary_contract_abi label arg result /\
      exists rho, typed_unop op arg result = Some rho.
  Proof.
    intros label op arg result abi Habi.
    unfold typed_unop_abi in Habi.
    destruct (typed_unop op arg result) as [rho |] eqn:Htyped; try discriminate.
    inversion Habi; subst. split; [reflexivity | exists rho; reflexivity].
  Qed.

  Theorem binary_contract_abi_operands_first_return_last :
    forall label lhs rhs result,
      abi_formal_count (binary_contract_abi label lhs rhs result) = 3 /\
      abi_return_channel_position (binary_contract_abi label lhs rhs result) = 2.
  Proof. repeat split; reflexivity. Qed.

  Theorem unary_contract_abi_operand_first_return_last :
    forall label arg result,
      abi_formal_count (unary_contract_abi label arg result) = 2 /\
      abi_return_channel_position (unary_contract_abi label arg result) = 1.
  Proof. repeat split; reflexivity. Qed.

  Theorem invocation_plan_from_binary_abi_preserves_signature :
    forall label lhs rhs result,
      invocation_plan_from_abi (binary_contract_abi label lhs rhs result) =
      {| plan_label_id := label;
         plan_operand_types := [lhs; rhs];
         plan_result_type := result |}.
  Proof. reflexivity. Qed.

  Theorem invocation_plan_from_unary_abi_preserves_signature :
    forall label arg result,
      invocation_plan_from_abi (unary_contract_abi label arg result) =
      {| plan_label_id := label;
         plan_operand_types := [arg];
         plan_result_type := result |}.
  Proof. reflexivity. Qed.

  Theorem typed_binop_invocation_plan_preserves_typed_signature :
    forall label op lhs rhs result abi,
      typed_binop_abi label op lhs rhs result = Some abi ->
      invocation_plan_from_abi abi =
      {| plan_label_id := label;
         plan_operand_types := [lhs; rhs];
         plan_result_type := result |}.
  Proof.
    intros label op lhs rhs result abi Habi.
    apply typed_binop_abi_success_matches_typed_operator in Habi.
    destruct Habi as [Habi _]. subst abi. reflexivity.
  Qed.

  Theorem typed_unop_invocation_plan_preserves_typed_signature :
    forall label op arg result abi,
      typed_unop_abi label op arg result = Some abi ->
      invocation_plan_from_abi abi =
      {| plan_label_id := label;
         plan_operand_types := [arg];
         plan_result_type := result |}.
  Proof.
    intros label op arg result abi Habi.
    apply typed_unop_abi_success_matches_typed_operator in Habi.
    destruct Habi as [Habi _]. subst abi. reflexivity.
  Qed.

  Theorem unsupported_native_kinds_are_not_scalars :
    native_kind_scalar NUInt32 = None /\
    native_kind_scalar NFloat64 = None /\
    native_kind_scalar NBigInt = None /\
    native_kind_scalar NBigRat = None /\
    native_kind_scalar NFixed = None /\
    native_kind_scalar NOther = None.
  Proof. repeat split; reflexivity. Qed.

  Theorem int_plus_lowers_to_integer_add :
    typed_binop SPlus TInt TInt TInt = Some RAdd.
  Proof. reflexivity. Qed.

  Theorem string_plus_lowers_to_concat :
    typed_binop SPlus TStr TStr TStr = Some RConcat.
  Proof. reflexivity. Qed.

  Theorem string_concat_lowers_to_concat :
    typed_binop SConcat TStr TStr TStr = Some RConcat.
  Proof. reflexivity. Qed.

  Theorem string_plus_abi_records_string_signature :
    forall label,
      typed_binop_abi label SPlus TStr TStr TStr =
      Some (binary_contract_abi label TStr TStr TStr).
  Proof. reflexivity. Qed.

  Theorem string_plus_not_integer_add :
    typed_binop SPlus TStr TStr TStr <> Some RAdd.
  Proof. discriminate. Qed.

  Theorem bool_not_lowers_to_not :
    typed_unop SNot TBool TBool = Some RNot.
  Proof. reflexivity. Qed.

  Theorem int_neg_lowers_to_neg :
    typed_unop SNeg TInt TInt = Some RNeg.
  Proof. reflexivity. Qed.

  Theorem bool_not_abi_records_bool_signature :
    forall label,
      typed_unop_abi label SNot TBool TBool =
      Some (unary_contract_abi label TBool TBool).
  Proof. reflexivity. Qed.

  Theorem int_neg_abi_records_int_signature :
    forall label,
      typed_unop_abi label SNeg TInt TInt =
      Some (unary_contract_abi label TInt TInt).
  Proof. reflexivity. Qed.

  Theorem bool_plus_rejected :
    typed_binop SPlus TBool TBool TBool = None.
  Proof. reflexivity. Qed.

  Theorem bool_neg_rejected :
    typed_unop SNeg TBool TBool = None.
  Proof. reflexivity. Qed.

  Theorem int_not_rejected :
    typed_unop SNot TInt TInt = None.
  Proof. reflexivity. Qed.

  Theorem mixed_operand_types_rejected :
    forall op result,
      typed_binop op TInt TStr result = None /\
      typed_binop op TStr TInt result = None /\
      typed_binop op TBool TInt result = None.
  Proof.
    intros op result. destruct op; destruct result; simpl; repeat split; reflexivity.
  Qed.

  Theorem comparison_result_must_be_bool :
    forall op ty result rho,
      (op = SEq \/ op = SNeq \/ op = SLt \/ op = SGt \/ op = SLte \/ op = SGte) ->
      typed_binop op ty ty result = Some rho ->
      result = TBool.
  Proof.
    intros op ty result rho Hop Hlower.
    destruct Hop as [-> | [-> | [-> | [-> | [-> | ->]]]]];
      destruct ty; destruct result; simpl in Hlower; try discriminate; reflexivity.
  Qed.

  Theorem successful_lowering_uses_equal_operand_types :
    forall op lhs rhs result rho,
      typed_binop op lhs rhs result = Some rho ->
      lhs = rhs.
  Proof.
    intros op lhs rhs result rho Hlower.
    destruct lhs; destruct rhs; destruct op; destruct result;
      simpl in Hlower; try discriminate; reflexivity.
  Qed.

  Theorem plus_success_cases :
    forall lhs rhs result rho,
      typed_binop SPlus lhs rhs result = Some rho ->
      (lhs = TInt /\ rhs = TInt /\ result = TInt /\ rho = RAdd) \/
      (lhs = TStr /\ rhs = TStr /\ result = TStr /\ rho = RConcat).
  Proof.
    intros lhs rhs result rho Hlower.
    destruct lhs; destruct rhs; destruct result; simpl in Hlower;
      try discriminate; inversion Hlower; subst; auto.
  Qed.

End RhoScalarOperatorTyping.
