(*
 * RhoParWellFormedness: normalized-Par obligations for generated Rho backend
 * artifacts.
 *
 * The generated backend no longer uses Rholang source text as the execution
 * boundary. It constructs `models::rhoapi::Par` directly and injects that value
 * into `RhoRuntime::inj`. This file models the scalar-contract shape emitted by
 * `rholang-codegen::lower_language_def`:
 *
 *   contract @"Label"(@a1, ..., @an, ret) = { ret!(expr(a1, ..., an)) }
 *
 * after host normalization, a contract is a persistent `Receive` with one bind,
 * `n+1` free patterns, one body send, one result datum, return channel
 * de-Bruijn index 0 (the newest binding), and metadata (`locally_free` /
 * `connective_used`) consistent with those bindings.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

Section RhoParWellFormedness.

  Record ContractAst : Type := {
    source_is_ground_string : bool;
    persistent_receive : bool;
    peek_receive : bool;
    condition_absent : bool;
    receive_metadata_clean : bool;
    source_metadata_clean : bool;
    pattern_metadata_clean : bool;
    body_metadata_clean : bool;
    return_channel_metadata_clean : bool;
    result_metadata_clean : bool;
    operand_metadata_clean : bool;
    bind_count : nat;
    free_count : nat;
    pattern_count : nat;
    body_send_count : nat;
    body_data_count : nat;
    return_channel_index : nat
  }.

  Definition contract_well_formed (c : ContractAst) : bool :=
    source_is_ground_string c
    && persistent_receive c
    && negb (peek_receive c)
    && condition_absent c
    && receive_metadata_clean c
    && source_metadata_clean c
    && pattern_metadata_clean c
    && body_metadata_clean c
    && return_channel_metadata_clean c
    && result_metadata_clean c
    && operand_metadata_clean c
    && Nat.eqb (bind_count c) (free_count c)
    && Nat.eqb (pattern_count c) (free_count c)
    && Nat.ltb 0 (bind_count c)
    && Nat.eqb (body_send_count c) 1
    && Nat.eqb (body_data_count c) 1
    && Nat.eqb (return_channel_index c) 0.

  Definition program_well_formed (contracts : list ContractAst) : bool :=
    forallb contract_well_formed contracts.

  Inductive RhoArtifact : Type :=
  | NormalizedAstArtifact : list ContractAst -> RhoArtifact.

  Record ValidatedArtifact : Type := {
    validated_contracts : list ContractAst
  }.

  Definition validate_artifact (artifact : RhoArtifact) : option ValidatedArtifact :=
    match artifact with
    | NormalizedAstArtifact contracts =>
        if program_well_formed contracts
        then Some {| validated_contracts := contracts |}
        else None
    end.

  Theorem validate_artifact_sound : forall artifact validated,
    validate_artifact artifact = Some validated ->
    program_well_formed (validated_contracts validated) = true.
  Proof.
    intros [contracts] validated Hvalidate.
    unfold validate_artifact in Hvalidate.
    destruct (program_well_formed contracts) eqn:Hwf.
    - inversion Hvalidate. subst. simpl. exact Hwf.
    - discriminate Hvalidate.
  Qed.

  Theorem validate_artifact_rejects_invalid : forall contracts,
    program_well_formed contracts = false ->
    validate_artifact (NormalizedAstArtifact contracts) = None.
  Proof.
    intros contracts Hinvalid. unfold validate_artifact.
    destruct (program_well_formed contracts) eqn:Hwf.
    - discriminate Hinvalid.
    - reflexivity.
  Qed.

  Theorem validate_artifact_complete : forall contracts,
    program_well_formed contracts = true ->
    exists validated,
      validate_artifact (NormalizedAstArtifact contracts) = Some validated
      /\ validated_contracts validated = contracts.
  Proof.
    intros contracts Hvalid. unfold validate_artifact.
    destruct (program_well_formed contracts) eqn:Hwf.
    - exists {| validated_contracts := contracts |}.
      split; reflexivity.
    - discriminate Hvalid.
  Qed.

  Definition scalar_contract (operand_count : nat) : ContractAst :=
    {|
      source_is_ground_string := true;
      persistent_receive := true;
      peek_receive := false;
      condition_absent := true;
      receive_metadata_clean := true;
      source_metadata_clean := true;
      pattern_metadata_clean := true;
      body_metadata_clean := true;
      return_channel_metadata_clean := true;
      result_metadata_clean := true;
      operand_metadata_clean := true;
      bind_count := S operand_count;
      free_count := S operand_count;
      pattern_count := S operand_count;
      body_send_count := 1;
      body_data_count := 1;
      return_channel_index := 0
    |}.

  Theorem scalar_contract_well_formed : forall operand_count,
    contract_well_formed (scalar_contract operand_count) = true.
  Proof.
    intros operand_count. unfold contract_well_formed, scalar_contract. simpl.
    repeat rewrite Nat.eqb_refl. simpl.
    destruct operand_count; reflexivity.
  Qed.

  Theorem program_well_formed_iff_all_contracts : forall contracts,
    program_well_formed contracts = true
    <-> forall c, In c contracts -> contract_well_formed c = true.
  Proof.
    intros contracts. unfold program_well_formed.
    rewrite forallb_forall. reflexivity.
  Qed.

  Theorem lowered_scalar_program_well_formed : forall arities,
    program_well_formed (map scalar_contract arities) = true.
  Proof.
    intros arities. apply forallb_forall.
    intros c Hin. apply in_map_iff in Hin.
    destruct Hin as [arity [Heq _]]. subst.
    apply scalar_contract_well_formed.
  Qed.

  Theorem lowered_scalar_program_validates : forall arities,
    exists validated,
      validate_artifact (NormalizedAstArtifact (map scalar_contract arities)) = Some validated
      /\ validated_contracts validated = map scalar_contract arities.
  Proof.
    intros arities. apply validate_artifact_complete.
    apply lowered_scalar_program_well_formed.
  Qed.

  Theorem scalar_contract_return_channel_zero : forall operand_count,
    return_channel_index (scalar_contract operand_count) = 0.
  Proof. reflexivity. Qed.

  Theorem scalar_contract_bind_counts_match : forall operand_count,
    bind_count (scalar_contract operand_count) = free_count (scalar_contract operand_count)
    /\ pattern_count (scalar_contract operand_count) = free_count (scalar_contract operand_count).
  Proof.
    intros operand_count. split; reflexivity.
  Qed.

  Theorem scalar_contract_positive_bind_count : forall operand_count,
    0 < bind_count (scalar_contract operand_count).
  Proof.
    intros operand_count. simpl. lia.
  Qed.

  Theorem scalar_contract_metadata_clean : forall operand_count,
    receive_metadata_clean (scalar_contract operand_count) = true
    /\ source_metadata_clean (scalar_contract operand_count) = true
    /\ pattern_metadata_clean (scalar_contract operand_count) = true
    /\ body_metadata_clean (scalar_contract operand_count) = true
    /\ return_channel_metadata_clean (scalar_contract operand_count) = true
    /\ result_metadata_clean (scalar_contract operand_count) = true
    /\ operand_metadata_clean (scalar_contract operand_count) = true.
  Proof.
    intros operand_count. repeat split.
  Qed.

End RhoParWellFormedness.
