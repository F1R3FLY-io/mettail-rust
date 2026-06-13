(*
 * RhoAstSendBoundary: generated dynamic calls and ambiguity witnesses cross
 * the Rho runtime boundary as AST sends, never as source text.
 *
 * Rust image:
 *   - `mettail-rho-codegen::RhoAstSend` constructs normalized `rhoapi::Par`
 *     sends for scalar-contract calls and ambiguity witness facts.
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
    | LitQuotedChannel : Atom -> AstLiteral.

  Record AstSend : Type := {
    send_channel : Atom;
    send_payloads : list AstLiteral
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
