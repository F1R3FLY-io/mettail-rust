(*
 * RhoAstSendBoundary: generated dynamic calls and ambiguity witnesses cross
 * the Rho runtime boundary as AST sends, never as source text.
 *
 * Rust image:
 *   - `mettail-rho-codegen::RhoAstSend` constructs normalized `rhoapi::Par`
 *     sends for scalar-contract calls, structured runtime payloads, and
 *     ambiguity witness facts.
 *   - `RhoAstSend::text_annotation` is a reader/debug annotation only.
 *   - `mettail-rho-runtime` injects the `Par` value and can observe grouped
 *     witness tuples from receive-less channels.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Section RhoAstSendBoundary.

  Definition Atom : Type := nat.

  Inductive AstLiteral : Type :=
    | LitInt : nat -> AstLiteral
    | LitBool : bool -> AstLiteral
    | LitString : Atom -> AstLiteral
    | LitBytes : Atom -> AstLiteral
    | LitPrivateName : Atom -> AstLiteral
    | LitList : list AstLiteral -> AstLiteral
    | LitTuple : list AstLiteral -> AstLiteral
    | LitSet : list AstLiteral -> AstLiteral
    | LitMap : list (AstLiteral * AstLiteral) -> AstLiteral
    | LitBag : list (AstLiteral * nat) -> AstLiteral
    | LitQuotedChannel : Atom -> AstLiteral.

  Inductive ScalarTy : Type :=
    | TInt
    | TBool
    | TStr.

  Inductive ScalarObservation : Type :=
    | ObserveInts
    | ObserveBools
    | ObserveStrings.

  Record AstSend : Type := {
    send_channel : Atom;
    send_payloads : list AstLiteral
  }.

  Record ScalarCallAbi : Type := {
    scalar_abi_label : Atom;
    scalar_abi_operands : list ScalarTy;
    scalar_abi_result : ScalarTy
  }.

  Inductive DynamicInputArtifact : Type :=
    | AstSendArtifact : AstSend -> DynamicInputArtifact
    | SourceTextInput : list nat -> DynamicInputArtifact.

  Definition dynamic_input_is_source_text
      (artifact : DynamicInputArtifact) : bool :=
    match artifact with
    | SourceTextInput _ => true
    | AstSendArtifact _ => false
    end.

  Definition current_dynamic_input_accepts
      (artifact : DynamicInputArtifact) : bool :=
    match artifact with
    | AstSendArtifact send =>
        negb (Nat.eqb (send_channel send) 0)
    | SourceTextInput _ => false
    end.

  Definition contract_call
      (operation return_channel : Atom)
      (arguments : list AstLiteral) : DynamicInputArtifact :=
    AstSendArtifact {|
      send_channel := operation;
      send_payloads := arguments ++ [LitQuotedChannel return_channel]
    |}.

  Definition scalar_observation_for (ty : ScalarTy) : ScalarObservation :=
    match ty with
    | TInt => ObserveInts
    | TBool => ObserveBools
    | TStr => ObserveStrings
    end.

  Definition scalar_ty_eqb (lhs rhs : ScalarTy) : bool :=
    match lhs, rhs with
    | TInt, TInt | TBool, TBool | TStr, TStr => true
    | _, _ => false
    end.

  Definition literal_scalar_type (literal : AstLiteral) : option ScalarTy :=
    match literal with
    | LitInt _ => Some TInt
    | LitBool _ => Some TBool
    | LitString _ => Some TStr
    | LitBytes _
    | LitPrivateName _
    | LitList _
    | LitTuple _
    | LitSet _
    | LitMap _
    | LitBag _
    | LitQuotedChannel _ => None
    end.

  Definition scalar_literal_matches
      (literal : AstLiteral)
      (expected : ScalarTy) : bool :=
    match literal_scalar_type literal with
    | Some actual => scalar_ty_eqb actual expected
    | None => false
    end.

  Fixpoint scalar_literals_match
      (arguments : list AstLiteral)
      (expected : list ScalarTy) : bool :=
    match arguments, expected with
    | [], [] => true
    | argument :: arguments', expected_ty :: expected' =>
        scalar_literal_matches argument expected_ty
        && scalar_literals_match arguments' expected'
    | _, _ => false
    end.

  Definition checked_scalar_contract_invocation
      (abi : ScalarCallAbi)
      (arguments : list AstLiteral)
      (return_channel : Atom)
      : option (DynamicInputArtifact * ScalarObservation) :=
    if Nat.eqb (length arguments) (length (scalar_abi_operands abi))
    then
      if scalar_literals_match arguments (scalar_abi_operands abi)
      then Some
        (contract_call (scalar_abi_label abi) return_channel arguments,
         scalar_observation_for (scalar_abi_result abi))
      else None
    else None.

  Definition ambiguity_witness
      (witness_channel key payload : Atom) : DynamicInputArtifact :=
    AstSendArtifact {|
      send_channel := witness_channel;
      send_payloads := [LitString key; LitString payload]
    |}.

  Definition observed_witness_tuple
      (artifact : DynamicInputArtifact) : option (Atom * Atom) :=
    match artifact with
    | AstSendArtifact send =>
        match send_payloads send with
        | [LitString key; LitString payload] => Some (key, payload)
        | _ => None
        end
    | SourceTextInput _ => None
    end.

  Definition send_payloads_of
      (artifact : DynamicInputArtifact) : option (list AstLiteral) :=
    match artifact with
    | AstSendArtifact send => Some (send_payloads send)
    | SourceTextInput _ => None
    end.

  Theorem source_text_dynamic_input_rejected : forall bytes,
    current_dynamic_input_accepts (SourceTextInput bytes) = false.
  Proof. intros bytes. reflexivity. Qed.

  Theorem accepted_dynamic_input_not_source_text : forall artifact,
    current_dynamic_input_accepts artifact = true ->
    dynamic_input_is_source_text artifact = false.
  Proof.
    intros [send | bytes] Haccept; simpl in *.
    - reflexivity.
    - discriminate Haccept.
  Qed.

  Theorem contract_call_is_ast_not_source_text :
    forall operation return_channel arguments,
      dynamic_input_is_source_text
        (contract_call operation return_channel arguments) = false.
  Proof. intros operation return_channel arguments. reflexivity. Qed.

  Theorem contract_call_preserves_argument_payloads :
    forall operation return_channel arguments,
      send_payloads_of (contract_call operation return_channel arguments) =
        Some (arguments ++ [LitQuotedChannel return_channel]).
  Proof. intros operation return_channel arguments. reflexivity. Qed.

  Theorem scalar_ty_eqb_refl :
    forall ty, scalar_ty_eqb ty ty = true.
  Proof. intros []; reflexivity. Qed.

  Theorem scalar_string_literal_does_not_match_int : forall atom,
    scalar_literal_matches (LitString atom) TInt = false.
  Proof. intros atom. reflexivity. Qed.

  Theorem non_scalar_literal_does_not_match_scalar : forall values ty,
    scalar_literal_matches (LitList values) ty = false.
  Proof. intros values ty. destruct ty; reflexivity. Qed.

  Theorem checked_scalar_invocation_preserves_payloads :
    forall abi arguments return_channel artifact observation,
      checked_scalar_contract_invocation abi arguments return_channel =
        Some (artifact, observation) ->
      send_payloads_of artifact =
        Some (arguments ++ [LitQuotedChannel return_channel]).
  Proof.
    intros abi arguments return_channel artifact observation Hchecked.
    unfold checked_scalar_contract_invocation in Hchecked.
    destruct (Nat.eqb (length arguments) (length (scalar_abi_operands abi)));
      try discriminate.
    destruct (scalar_literals_match arguments (scalar_abi_operands abi));
      try discriminate.
    inversion Hchecked; subst. reflexivity.
  Qed.

  Theorem checked_scalar_invocation_observation_follows_result :
    forall abi arguments return_channel artifact observation,
      checked_scalar_contract_invocation abi arguments return_channel =
        Some (artifact, observation) ->
      observation = scalar_observation_for (scalar_abi_result abi).
  Proof.
    intros abi arguments return_channel artifact observation Hchecked.
    unfold checked_scalar_contract_invocation in Hchecked.
    destruct (Nat.eqb (length arguments) (length (scalar_abi_operands abi)));
      try discriminate.
    destruct (scalar_literals_match arguments (scalar_abi_operands abi));
      try discriminate.
    inversion Hchecked; subst. reflexivity.
  Qed.

  Theorem checked_scalar_invocation_rejects_arity_mismatch :
    forall abi arguments return_channel,
      length arguments <> length (scalar_abi_operands abi) ->
      checked_scalar_contract_invocation abi arguments return_channel = None.
  Proof.
    intros abi arguments return_channel Hneq.
    unfold checked_scalar_contract_invocation.
    apply Nat.eqb_neq in Hneq. rewrite Hneq. reflexivity.
  Qed.

  Theorem checked_string_result_invocation_observes_strings :
    forall label arguments return_channel artifact observation,
      checked_scalar_contract_invocation
        {| scalar_abi_label := label;
           scalar_abi_operands := [TStr; TStr];
           scalar_abi_result := TStr |}
        arguments
        return_channel =
        Some (artifact, observation) ->
      observation = ObserveStrings.
  Proof.
    intros label arguments return_channel artifact observation Hchecked.
    apply checked_scalar_invocation_observation_follows_result in Hchecked.
    exact Hchecked.
  Qed.

  Theorem structured_contract_call_preserves_list_payload :
    forall operation return_channel payloads,
      send_payloads_of
        (contract_call operation return_channel [LitList payloads]) =
        Some [LitList payloads; LitQuotedChannel return_channel].
  Proof. intros operation return_channel payloads. reflexivity. Qed.

  Theorem structured_contract_call_preserves_map_payload :
    forall operation return_channel entries,
      send_payloads_of
        (contract_call operation return_channel [LitMap entries]) =
        Some [LitMap entries; LitQuotedChannel return_channel].
  Proof. intros operation return_channel entries. reflexivity. Qed.

  Theorem structured_contract_call_preserves_bag_payload :
    forall operation return_channel entries,
      send_payloads_of
        (contract_call operation return_channel [LitBag entries]) =
        Some [LitBag entries; LitQuotedChannel return_channel].
  Proof. intros operation return_channel entries. reflexivity. Qed.

  Theorem accepted_contract_call_requires_nonempty_operation :
    forall operation return_channel arguments,
      current_dynamic_input_accepts
        (contract_call operation return_channel arguments) = true ->
      operation <> 0.
  Proof.
    intros operation return_channel arguments Haccept Heq.
    unfold current_dynamic_input_accepts, contract_call in Haccept.
    simpl in Haccept. subst operation. simpl in Haccept.
    discriminate Haccept.
  Qed.

  Theorem ambiguity_witness_is_ast_not_source_text :
    forall witness_channel key payload,
      dynamic_input_is_source_text
        (ambiguity_witness witness_channel key payload) = false.
  Proof. intros witness_channel key payload. reflexivity. Qed.

  Theorem ambiguity_witness_observes_exact_tuple :
    forall witness_channel key payload,
      observed_witness_tuple
        (ambiguity_witness witness_channel key payload) = Some (key, payload).
  Proof. intros witness_channel key payload. reflexivity. Qed.

  Theorem accepted_ambiguity_witness_requires_nonempty_channel :
    forall witness_channel key payload,
      current_dynamic_input_accepts
        (ambiguity_witness witness_channel key payload) = true ->
      witness_channel <> 0.
  Proof.
    intros witness_channel key payload Haccept Heq.
    unfold current_dynamic_input_accepts, ambiguity_witness in Haccept.
    simpl in Haccept. subst witness_channel. simpl in Haccept.
    discriminate Haccept.
  Qed.

End RhoAstSendBoundary.
