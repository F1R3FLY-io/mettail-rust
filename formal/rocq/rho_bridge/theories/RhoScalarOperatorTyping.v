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
