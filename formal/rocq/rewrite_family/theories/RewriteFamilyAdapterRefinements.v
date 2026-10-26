From Stdlib Require Import List Bool PeanoNat Lia.
Require Import TermParamReaderProjection RewriteFamilyNames.
Import ListNotations.
Import TermParamReaderProjection.TermParamReaderProjection.
Import RewriteFamilyNames.RewriteFamilyNames.

Module RewriteFamilyAdapterRefinements.

Fixpoint materialize (step : Work -> Step) fuel work : option (list Leaf) :=
  match fuel with
  | 0 => None
  | S remaining =>
      match step work with
      | Done => Some []
      | Continue rest _ => materialize step remaining rest
      | Yield leaf rest _ => option_map (cons leaf) (materialize step remaining rest)
      | InvalidReader => None
      end
  end.

Fixpoint iterator_nth (step : Work -> Step) fuel work index : option Leaf :=
  match fuel with
  | 0 => None
  | S remaining =>
      match step work with
      | Done | InvalidReader => None
      | Continue rest _ => iterator_nth step remaining rest index
      | Yield leaf rest _ =>
          match index with
          | 0 => Some leaf
          | S next => iterator_nth step remaining rest next
          end
      end
  end.

Theorem materialization_preserves_every_indexed_leaf :
  forall fuel step work leaves index,
  materialize step fuel work = Some leaves ->
  nth_error leaves index = iterator_nth step fuel work index.
Proof.
  induction fuel as [|fuel IH]; intros step work leaves index Hdone;
    simpl in Hdone; [discriminate|].
  simpl. destruct (step work) as [|rest trace|leaf rest trace|]; try discriminate.
  - inversion Hdone; subst. destruct index; reflexivity.
  - now apply IH.
  - destruct (materialize step fuel rest) as [tail|] eqn:Htail;
      inversion Hdone; subst. destruct index; simpl; [reflexivity|].
    now apply IH.
Qed.

Theorem materialized_reader_roster_is_the_original_roster : forall fuel store work,
  materialize (reader_step (view_reader (project_store store))) fuel work =
  materialize (source_step store) fuel work.
Proof.
  induction fuel as [|fuel IH]; intros store work; simpl; [reflexivity|].
  rewrite original_step_correspondence.
  destruct (source_step store work); simpl; try reflexivity; now rewrite IH.
Qed.

Theorem cached_reader_access_retains_original_payload_and_optional_flag :
  forall fuel store work leaves index leaf,
  materialize (reader_step (view_reader (project_store store))) fuel work = Some leaves ->
  nth_error leaves index = Some leaf ->
  iterator_nth (source_step store) fuel work index = Some leaf.
Proof.
  intros fuel store work leaves index leaf Hdone Hleaf.
  rewrite materialized_reader_roster_is_the_original_roster in Hdone.
  rewrite <- (materialization_preserves_every_indexed_leaf fuel (source_step store)
    work leaves index Hdone). exact Hleaf.
Qed.

Theorem materialized_roster_preserves_arity_and_out_of_range :
  forall fuel step work leaves index,
  materialize step fuel work = Some leaves ->
  iterator_nth step fuel work index = None <-> length leaves <= index.
Proof.
  intros fuel step work leaves index Hdone.
  rewrite <- (materialization_preserves_every_indexed_leaf fuel step work leaves index Hdone).
  apply nth_error_None.
Qed.

Section Diagnostics.

Context {Location : Type}.
Variable spelling : nat -> nat.
Variable binder_location : nat -> Location.
Variable binder_index : nat -> nat.

Record OldAmbiguity := old_ambiguity {
  old_binder_location : Location;
  old_external_location : Location
}.

Record DetailedAmbiguity := detailed_ambiguity {
  detail_binder_location : Location;
  detail_external_location : Location;
  detail_binder_index : nat
}.

Definition erase_ambiguity detail :=
  old_ambiguity (detail_binder_location detail) (detail_external_location detail).

Definition matching_external external identity :=
  find (fun entry : nat * Location => Nat.eqb (spelling identity) (fst entry)) external.

Fixpoint old_ambiguity_scan identities external pending : option OldAmbiguity :=
  match pending with
  | [] => None
  | identity :: rest =>
      if spelling_is_unique spelling identities identity then
        old_ambiguity_scan identities external rest
      else match matching_external external identity with
      | Some (_, site) => Some (old_ambiguity (binder_location identity) site)
      | None => old_ambiguity_scan identities external rest
      end
  end.

Fixpoint detailed_ambiguity_scan identities external pending : option DetailedAmbiguity :=
  match pending with
  | [] => None
  | identity :: rest =>
      if spelling_is_unique spelling identities identity then
        detailed_ambiguity_scan identities external rest
      else match matching_external external identity with
      | Some (_, site) => Some (detailed_ambiguity
          (binder_location identity) site (binder_index identity))
      | None => detailed_ambiguity_scan identities external rest
      end
  end.

Theorem diagnostic_metadata_erasure_preserves_the_original_scan :
  forall pending identities external,
  option_map erase_ambiguity (detailed_ambiguity_scan identities external pending) =
    old_ambiguity_scan identities external pending.
Proof.
  induction pending as [|identity rest IH]; intros identities external; simpl; [reflexivity|].
  destruct (spelling_is_unique spelling identities identity); [apply IH|].
  destruct (matching_external external identity) as [[name site]|]; [reflexivity|apply IH].
Qed.

Definition old_outcome {A} (success : A) identities external pending :=
  match old_ambiguity_scan identities external pending with
  | Some failure => inr failure
  | None => inl success
  end.

Definition detailed_outcome {A} (success : A) identities external pending :=
  match detailed_ambiguity_scan identities external pending with
  | Some failure => inr failure
  | None => inl success
  end.

Definition erase_outcome {A} (outcome : A + DetailedAmbiguity) : A + OldAmbiguity :=
  match outcome with
  | inl success => inl success
  | inr failure => inr (erase_ambiguity failure)
  end.

Theorem diagnostic_metadata_preserves_success_and_refusal :
  forall (A : Type) (success : A) identities external pending,
  erase_outcome (detailed_outcome success identities external pending) =
    old_outcome success identities external pending.
Proof.
  intros. unfold detailed_outcome, old_outcome.
  rewrite <- diagnostic_metadata_erasure_preserves_the_original_scan.
  destruct (detailed_ambiguity_scan identities external pending); reflexivity.
Qed.

Lemma detailed_ambiguity_has_an_original_witness :
  forall pending identities external detail,
  detailed_ambiguity_scan identities external pending = Some detail ->
  exists identity name,
    In identity pending /\
    spelling_is_unique spelling identities identity = false /\
    In (name, detail_external_location detail) external /\
    spelling identity = name /\
    detail_binder_location detail = binder_location identity /\
    detail_binder_index detail = binder_index identity.
Proof.
  induction pending as [|identity rest IH]; intros identities external detail Hfound;
    simpl in Hfound; [discriminate|].
  destruct (spelling_is_unique spelling identities identity) eqn:Hunique.
  - destruct (IH _ _ _ Hfound) as [found [name [Hin Hrest]]].
    exists found, name. split; [right; exact Hin|exact Hrest].
  - destruct (matching_external external identity) as [[name site]|] eqn:Hmatch.
    + inversion Hfound; subst. unfold matching_external in Hmatch.
      apply find_some in Hmatch. destruct Hmatch as [Hin Hname].
      simpl in Hname. apply Nat.eqb_eq in Hname.
      exists identity, name. simpl. repeat split; auto.
    + destruct (IH _ _ _ Hfound) as [found [name [Hin Hrest]]].
      exists found, name. split; [right; exact Hin|exact Hrest].
Qed.

Theorem reported_index_resolves_the_offending_name_and_external_site :
  forall identities external detail (binder_names : Location -> list nat),
  (forall identity, In identity identities ->
    nth_error (binder_names (binder_location identity)) (binder_index identity) =
      Some (spelling identity)) ->
  detailed_ambiguity_scan identities external identities = Some detail ->
  exists name,
    nth_error (binder_names (detail_binder_location detail))
      (detail_binder_index detail) = Some name /\
    In (name, detail_external_location detail) external.
Proof.
  intros identities external detail binder_names Hpositions Hfound.
  destruct (detailed_ambiguity_has_an_original_witness _ _ _ _ Hfound) as
    [identity [name [Hin [Hunique [Hexternal [Hname [Hsite Hindex]]]]]]].
  exists name. split; [|exact Hexternal].
  rewrite Hsite, Hindex, <- Hname. now apply Hpositions.
Qed.

Theorem reported_ambiguity_is_refused_by_the_existing_name_contract :
  forall identities external detail,
  detailed_ambiguity_scan identities external identities = Some detail ->
  external_names_are_clear spelling identities (map fst external) = false.
Proof.
  intros identities external detail Hfound.
  destruct (detailed_ambiguity_has_an_original_witness _ _ _ _ Hfound) as
    [identity [name [Hin [Hunique [Hexternal [Hname Hrest]]]]]].
  destruct (external_names_are_clear spelling identities (map fst external)) eqn:Hclear;
    [|reflexivity].
  unfold external_names_are_clear in Hclear.
  apply forallb_forall with (x := identity) in Hclear; [|exact Hin].
  rewrite Hunique in Hclear. simpl in Hclear.
  assert (Hinname : In (spelling identity) (map fst external)).
  { rewrite Hname. apply in_map_iff. exists (name, detail_external_location detail). auto. }
  assert (Hexists : existsb (Nat.eqb (spelling identity)) (map fst external) = true).
  { apply existsb_exists. exists (spelling identity). split; [exact Hinname|apply Nat.eqb_refl]. }
  rewrite Hexists in Hclear. discriminate.
Qed.

End Diagnostics.
End RewriteFamilyAdapterRefinements.

Print Assumptions RewriteFamilyAdapterRefinements.materialization_preserves_every_indexed_leaf.
Print Assumptions RewriteFamilyAdapterRefinements.materialized_reader_roster_is_the_original_roster.
Print Assumptions RewriteFamilyAdapterRefinements.cached_reader_access_retains_original_payload_and_optional_flag.
Print Assumptions RewriteFamilyAdapterRefinements.materialized_roster_preserves_arity_and_out_of_range.
Print Assumptions RewriteFamilyAdapterRefinements.diagnostic_metadata_erasure_preserves_the_original_scan.
Print Assumptions RewriteFamilyAdapterRefinements.diagnostic_metadata_preserves_success_and_refusal.
Print Assumptions RewriteFamilyAdapterRefinements.reported_index_resolves_the_offending_name_and_external_site.
Print Assumptions RewriteFamilyAdapterRefinements.reported_ambiguity_is_refused_by_the_existing_name_contract.
