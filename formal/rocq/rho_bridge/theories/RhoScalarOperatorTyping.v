(*
 * RhoScalarOperatorTyping: type-sensitive classifier for scalar Rho lowering.
 *
 * Rust bridge:
 *   mettail-rho-codegen/src/lower.rs
 *
 * The lowerer may not choose a Rholang expression from the surface token alone.
 * Calculator has both `Int "+" Int -> Int` and `Str "+" Str -> Str`; the former
 * is Rholang integer `EPlus`, while the latter is Rholang string `EPlusPlus`.
 * This model proves the shape of that classifier and the fail-closed behavior
 * for combinations without an exact Rholang scalar expression.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

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

  Theorem string_plus_not_integer_add :
    typed_binop SPlus TStr TStr TStr <> Some RAdd.
  Proof. discriminate. Qed.

  Theorem bool_plus_rejected :
    typed_binop SPlus TBool TBool TBool = None.
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
