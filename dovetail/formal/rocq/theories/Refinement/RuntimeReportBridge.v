(*
 * RuntimeReportBridge: Dovetail's substrate-neutral runtime report preserves
 * the checked extraction boundary.
 *
 * The Rust artifact is `dovetail::report::DovetailRunReport`: a list of root
 * exact keys in extractor order, a deduplicated list of exact term keys, and
 * the terminal ExtractionCompleteness copied from extraction. This model proves
 * the properties a runtime/Rho adapter is allowed to rely on.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.

From Dovetail.Extraction Require Import CycleCutBoundary.

Import ListNotations.

Arguments extraction_value {A} _.
Arguments extraction_completeness {A} _.

Section RuntimeReportBridge.

  Inductive Derivation : Type :=
    | DNode : nat -> list Derivation -> Derivation.

  Definition d_key (d : Derivation) : nat :=
    match d with
    | DNode key _ => key
    end.

  Definition d_children (d : Derivation) : list Derivation :=
    match d with
    | DNode _ children => children
    end.

  Fixpoint derivation_keys (d : Derivation) : list nat :=
    d_key d :: flat_map derivation_keys (d_children d).

  Definition root_keys (ds : list Derivation) : list nat :=
    map d_key ds.

  Definition forest_keys (ds : list Derivation) : list nat :=
    flat_map derivation_keys ds.

  Record RuntimeReport : Type := {
    runtime_report_roots : list nat;
    runtime_report_terms : list nat;
    runtime_report_completeness : CompletenessStatus
  }.

  Definition report_is_complete (r : RuntimeReport) : bool :=
    match runtime_report_completeness r with
    | Complete => true
    | BoundedByCycleCut => false
    end.

  Definition report_from_extraction
    (e : Extraction (list Derivation)) : RuntimeReport :=
    {|
      runtime_report_roots := root_keys (extraction_value e);
      runtime_report_terms := nodup Nat.eq_dec (forest_keys (extraction_value e));
      runtime_report_completeness := extraction_completeness e
    |}.

  Lemma root_key_in_derivation_keys : forall d,
    In (d_key d) (derivation_keys d).
  Proof.
    intros [key children]. simpl. left. reflexivity.
  Qed.

  Theorem report_roots_preserve_extractor_order : forall e,
    runtime_report_roots (report_from_extraction e) =
      root_keys (extraction_value e).
  Proof. intros e. reflexivity. Qed.

  Theorem report_completeness_matches_extraction : forall e,
    runtime_report_completeness (report_from_extraction e) =
      extraction_completeness e.
  Proof. intros e. reflexivity. Qed.

  Theorem report_terms_are_deduplicated_exact_keys : forall e,
    NoDup (runtime_report_terms (report_from_extraction e)).
  Proof.
    intros e. simpl. apply NoDup_nodup.
  Qed.

  Theorem report_term_keys_come_from_extraction : forall e key,
    In key (runtime_report_terms (report_from_extraction e)) ->
    In key (forest_keys (extraction_value e)).
  Proof.
    intros e key Hin. simpl in Hin.
    rewrite nodup_In in Hin.
    exact Hin.
  Qed.

  Theorem report_root_keys_have_term_records : forall e key,
    In key (runtime_report_roots (report_from_extraction e)) ->
    In key (runtime_report_terms (report_from_extraction e)).
  Proof.
    intros [ds status] key Hin. simpl in *.
    rewrite nodup_In.
    unfold root_keys in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [d [Hkey HinD]].
    unfold forest_keys.
    apply in_flat_map.
    exists d. split.
    - exact HinD.
    - rewrite <- Hkey. apply root_key_in_derivation_keys.
  Qed.

  Theorem bounded_extraction_report_is_not_complete : forall e,
    extraction_completeness e = BoundedByCycleCut ->
    report_is_complete (report_from_extraction e) = false /\
    runtime_report_completeness (report_from_extraction e) <> Complete.
  Proof.
    intros [ds status] Hbounded. simpl in *.
    rewrite Hbounded. split.
    - reflexivity.
    - discriminate.
  Qed.

  Theorem complete_report_originates_in_complete_extraction : forall e,
    report_is_complete (report_from_extraction e) = true ->
    extraction_completeness e = Complete.
  Proof.
    intros [ds status] Hcomplete. simpl in *.
    destruct status.
    - reflexivity.
    - discriminate.
  Qed.

End RuntimeReportBridge.
