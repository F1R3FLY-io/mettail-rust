(*
 * RhoRuntimeBackendReportBridge: conversion from planned Rho observation
 * reports to the generic runtime backend report preserves the observation
 * boundary and never fabricates an Ascent-shaped result.
 *
 * Rust image:
 *   - `RhoObservationReport<T>::try_into_runtime_backend_report` maps typed Rho
 *     values into `RuntimeObservationValue`.
 *   - The resulting `RuntimeBackendReport` has backend `RhoMachine`, artifact
 *     `RhoNormalizedAst`, exactly one channel observation, the same read-order
 *     values after payload mapping, and copied evidence references.
 *   - Closed Rho ground payloads preserve scalar and structured collection
 *     shape when they are read as generic runtime observation values.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool List.
From RhoBridge Require Import RhoObservationReportBoundary.

Import ListNotations.

Section RhoRuntimeBackendReportBridge.

  Inductive RuntimeBackend : Type :=
  | Ascent
  | Dovetail
  | RhoMachine.

  Inductive RuntimeArtifact : Type :=
  | AscentFixpoint
  | DovetailRunReport
  | RhoNormalizedAst
  | RhoBytecode.

  Inductive RhoPayload : Type :=
  | RhoInt : nat -> RhoPayload
  | RhoBool : bool -> RhoPayload
  | RhoText : nat -> RhoPayload
  | RhoBytes : nat -> RhoPayload
  | RhoPrivateName : nat -> RhoPayload
  | RhoList : list RhoPayload -> RhoPayload
  | RhoTuple : list RhoPayload -> RhoPayload
  | RhoSet : list RhoPayload -> RhoPayload
  | RhoMap : list (RhoPayload * RhoPayload) -> RhoPayload
  | RhoBag : list (RhoPayload * nat) -> RhoPayload.

  Inductive RuntimeObservationValue : Type :=
  | RuntimeFact : nat -> RuntimeObservationValue
  | RuntimeInt : nat -> RuntimeObservationValue
  | RuntimeBool : bool -> RuntimeObservationValue
  | RuntimeText : nat -> RuntimeObservationValue
  | RuntimeBytes : nat -> RuntimeObservationValue
  | RuntimePrivateName : nat -> RuntimeObservationValue
  | RuntimeList : list RuntimeObservationValue -> RuntimeObservationValue
  | RuntimeTuple : list RuntimeObservationValue -> RuntimeObservationValue
  | RuntimeSet : list RuntimeObservationValue -> RuntimeObservationValue
  | RuntimeMap : list (RuntimeObservationValue * RuntimeObservationValue) ->
      RuntimeObservationValue
  | RuntimeBag : list (RuntimeObservationValue * nat) ->
      RuntimeObservationValue.

  Definition fact_to_runtime_value (fact : nat) : RuntimeObservationValue :=
    RuntimeFact fact.

  Inductive payload_maps_to : RhoPayload -> RuntimeObservationValue -> Prop :=
  | PayloadMapsInt : forall value,
      payload_maps_to (RhoInt value) (RuntimeInt value)
  | PayloadMapsBool : forall value,
      payload_maps_to (RhoBool value) (RuntimeBool value)
  | PayloadMapsText : forall value,
      payload_maps_to (RhoText value) (RuntimeText value)
  | PayloadMapsBytes : forall value,
      payload_maps_to (RhoBytes value) (RuntimeBytes value)
  | PayloadMapsPrivateName : forall value,
      payload_maps_to (RhoPrivateName value) (RuntimePrivateName value)
  | PayloadMapsListNil :
      payload_maps_to (RhoList []) (RuntimeList [])
  | PayloadMapsListCons :
      forall rho_head rho_tail runtime_head runtime_tail,
        payload_maps_to rho_head runtime_head ->
        payload_maps_to (RhoList rho_tail) (RuntimeList runtime_tail) ->
        payload_maps_to
          (RhoList (rho_head :: rho_tail))
          (RuntimeList (runtime_head :: runtime_tail))
  | PayloadMapsTupleNil :
      payload_maps_to (RhoTuple []) (RuntimeTuple [])
  | PayloadMapsTupleCons :
      forall rho_head rho_tail runtime_head runtime_tail,
        payload_maps_to rho_head runtime_head ->
        payload_maps_to (RhoTuple rho_tail) (RuntimeTuple runtime_tail) ->
        payload_maps_to
          (RhoTuple (rho_head :: rho_tail))
          (RuntimeTuple (runtime_head :: runtime_tail))
  | PayloadMapsSetNil :
      payload_maps_to (RhoSet []) (RuntimeSet [])
  | PayloadMapsSetCons :
      forall rho_head rho_tail runtime_head runtime_tail,
        payload_maps_to rho_head runtime_head ->
        payload_maps_to (RhoSet rho_tail) (RuntimeSet runtime_tail) ->
        payload_maps_to
          (RhoSet (rho_head :: rho_tail))
          (RuntimeSet (runtime_head :: runtime_tail))
  | PayloadMapsMapNil :
      payload_maps_to (RhoMap []) (RuntimeMap [])
  | PayloadMapsMapCons :
      forall rho_key rho_value rho_tail runtime_key runtime_value runtime_tail,
        payload_maps_to rho_key runtime_key ->
        payload_maps_to rho_value runtime_value ->
        payload_maps_to (RhoMap rho_tail) (RuntimeMap runtime_tail) ->
        payload_maps_to
          (RhoMap ((rho_key, rho_value) :: rho_tail))
          (RuntimeMap ((runtime_key, runtime_value) :: runtime_tail))
  | PayloadMapsBagNil :
      payload_maps_to (RhoBag []) (RuntimeBag [])
  | PayloadMapsBagCons :
      forall rho_value rho_tail runtime_value runtime_tail count,
        payload_maps_to rho_value runtime_value ->
        payload_maps_to (RhoBag rho_tail) (RuntimeBag runtime_tail) ->
        payload_maps_to
          (RhoBag ((rho_value, count) :: rho_tail))
          (RuntimeBag ((runtime_value, count) :: runtime_tail)).

  Lemma fact_to_runtime_value_map_length : forall values,
    length (map fact_to_runtime_value values) = length values.
  Proof.
    induction values as [| value rest IH]; simpl; [reflexivity | rewrite IH; reflexivity].
  Qed.

  Inductive RuntimeOutput : Type :=
  | AscentOutput
  | ObservationOutput : nat -> list RuntimeObservationValue -> RuntimeOutput.

  Record RuntimeBackendReport : Type := {
    runtime_backend : RuntimeBackend;
    runtime_artifact : RuntimeArtifact;
    runtime_output : RuntimeOutput;
    runtime_evidence_refs : list nat
  }.

  Definition rho_report_to_runtime_report
      (evidence_refs : list nat)
      (r : ObservationReport) : RuntimeBackendReport :=
    {|
      runtime_backend := RhoMachine;
      runtime_artifact := RhoNormalizedAst;
      runtime_output :=
        ObservationOutput
          (observation_channel r)
          (map fact_to_runtime_value (observation_values r));
      runtime_evidence_refs := evidence_refs
    |}.

  Definition runtime_report_is_ascent_output
      (r : RuntimeBackendReport) : bool :=
    match runtime_output r with
    | AscentOutput => true
    | ObservationOutput _ _ => false
    end.

  Definition runtime_report_observed_count
      (r : RuntimeBackendReport) : nat :=
    match runtime_output r with
    | AscentOutput => 0
    | ObservationOutput _ values => length values
    end.

  Theorem rho_runtime_report_backend_is_rho : forall evidence_refs report,
    runtime_backend (rho_report_to_runtime_report evidence_refs report) =
      RhoMachine.
  Proof. intros evidence_refs report. reflexivity. Qed.

  Theorem rho_runtime_report_artifact_is_normalized_ast :
    forall evidence_refs report,
      runtime_artifact (rho_report_to_runtime_report evidence_refs report) =
        RhoNormalizedAst.
  Proof. intros evidence_refs report. reflexivity. Qed.

  Theorem rho_runtime_report_is_not_ascent_output :
    forall evidence_refs report,
      runtime_report_is_ascent_output
        (rho_report_to_runtime_report evidence_refs report) = false.
  Proof. intros evidence_refs report. reflexivity. Qed.

  Theorem rho_runtime_report_preserves_channel : forall evidence_refs report,
    runtime_output (rho_report_to_runtime_report evidence_refs report) =
      ObservationOutput (observation_channel report)
                        (map fact_to_runtime_value (observation_values report)).
  Proof. intros evidence_refs report. reflexivity. Qed.

  Theorem rho_runtime_report_preserves_values : forall evidence_refs report,
    match runtime_output (rho_report_to_runtime_report evidence_refs report) with
    | AscentOutput => False
    | ObservationOutput _ values =>
        values = map fact_to_runtime_value (observation_values report)
    end.
  Proof. intros evidence_refs report. reflexivity. Qed.

  Theorem rho_runtime_report_preserves_observed_count :
    forall evidence_refs report,
      runtime_report_observed_count
        (rho_report_to_runtime_report evidence_refs report) =
      length (observation_values report).
  Proof.
    intros evidence_refs report.
    destruct report as [entry channel values]. simpl.
    apply fact_to_runtime_value_map_length.
  Qed.

  Theorem runtime_payload_mapping_preserves_bool : forall value,
    payload_maps_to (RhoBool value) (RuntimeBool value).
  Proof. intros value. constructor. Qed.

  Theorem runtime_payload_mapping_preserves_int : forall value,
    payload_maps_to (RhoInt value) (RuntimeInt value).
  Proof. intros value. constructor. Qed.

  Theorem runtime_payload_mapping_preserves_text : forall value,
    payload_maps_to (RhoText value) (RuntimeText value).
  Proof. intros value. constructor. Qed.

  Theorem runtime_payload_mapping_preserves_list_pair :
    forall rho_left rho_right runtime_left runtime_right,
      payload_maps_to rho_left runtime_left ->
      payload_maps_to rho_right runtime_right ->
      payload_maps_to
        (RhoList [rho_left; rho_right])
        (RuntimeList [runtime_left; runtime_right]).
  Proof.
    intros rho_left rho_right runtime_left runtime_right Hleft Hright.
    apply PayloadMapsListCons; [exact Hleft |].
    apply PayloadMapsListCons; [exact Hright |].
    apply PayloadMapsListNil.
  Qed.

  Theorem runtime_payload_mapping_preserves_map_singleton :
    forall rho_key rho_value runtime_key runtime_value,
      payload_maps_to rho_key runtime_key ->
      payload_maps_to rho_value runtime_value ->
      payload_maps_to
        (RhoMap [(rho_key, rho_value)])
        (RuntimeMap [(runtime_key, runtime_value)]).
  Proof.
    intros rho_key rho_value runtime_key runtime_value Hkey Hvalue.
    apply PayloadMapsMapCons; [exact Hkey | exact Hvalue |].
    apply PayloadMapsMapNil.
  Qed.

  Theorem runtime_payload_mapping_preserves_bag_singleton :
    forall rho_value runtime_value count,
      payload_maps_to rho_value runtime_value ->
      payload_maps_to
        (RhoBag [(rho_value, count)])
        (RuntimeBag [(runtime_value, count)]).
  Proof.
    intros rho_value runtime_value count Hvalue.
    apply PayloadMapsBagCons; [exact Hvalue |].
    apply PayloadMapsBagNil.
  Qed.

  Theorem rho_runtime_report_preserves_evidence_refs :
    forall evidence_refs report,
      runtime_evidence_refs
        (rho_report_to_runtime_report evidence_refs report) = evidence_refs.
  Proof. intros evidence_refs report. reflexivity. Qed.

End RhoRuntimeBackendReportBridge.
