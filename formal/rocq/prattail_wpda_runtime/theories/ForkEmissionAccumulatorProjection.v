(** Exact source relocation of fork_emission.rs's descriptor accumulator.

    This boundary moves ForkEmissionOrdinalRow, the two-map model, new,
    record_site2_row, counts and readbacks. The macro wrapper delegates these
    methods and consumes the owned maps through into_parts. It retains the
    original into_tokens/emitted_value bodies and all emitter call sites.
    No derived ordinal becomes election-active.

    Source ledger, original record_site2_row:
    (1) Query ambiguous FIRST. If present, append the new bucket@ordinal even
        when it duplicates an earlier observation, then return.
    (2) Otherwise query the derived map. A DIFFERING ordinal removes that row
        and inserts [first-derived-tag@old-ordinal; new-tag@new-ordinal]. The
        just-matched row is still present at remove/expect: no intervening
        mutation or callback exists. remove_with_value below states this fact.
    (3) An equal ordinal changes NOTHING, including the first bucket tag.
        Equal-position duplicate tags are not saved for a later conflict.
    (4) An absent row is inserted with the supplied ordinal and owned tag.
    Ambiguity is permanent; neither map is reconstructed from grammar syntax.

    Stdlib's proved ordered finite map is an observation model for BTreeMap:
    tuple-key lookup/add/remove/cardinality and sorted iteration are retained,
    not Rust's tree shape, allocator, balancing, capacity or timing. The two
    maps remain separate. census_keys is sorted derived keys FOLLOWED BY sorted
    ambiguous keys, not a sorted union. into_parts moves both complete maps,
    preserving order of every ambiguous tag vector. Map values preserve all
    original row fields; TagObservation retains both exact format arguments.
    Applying the SAME original formatter yields the original bucket@ordinal
    strings. Formatting internals, String allocation/Drop, Rust extraction and
    borrow checking are outside this theorem.

    Keys/ordinals are naturals representing source u16 values (no arithmetic
    occurs in record_site2_row); source entry values are restricted to u16.
    Counts are mathematical cardinalities. The census capacity addition is
    represented by its domain predicate, not by new runtime admission. No
    allocation success or panic behavior outside that domain is asserted.

    The wrappers share the CONCRETE original recording transition below, not
    an unspecified parser with an assumed equivalence. Finite sequences retain
    complete maps/readbacks. Imported ordered-map laws discharge membership,
    removal and sortedness obligations. ConstructorElectionEvidence's ordinal-
    word theorems concern downstream ranking, not this accumulator, so they
    are intentionally not used to claim accumulator correctness or activation.
    The only election claim here is the unchanged, model-independent interface
    0|2 -> 0, 1|3 -> 1, otherwise u16::MAX (binder TAKE/SKIP constants 0/1).
*)
From Stdlib Require Import List String Bool Arith Lia Sorting.Sorted.
From Stdlib Require Import FSets.FMapAVL FSets.FMapFacts Structures.OrderedTypeEx.
Import ListNotations.
Set Implicit Arguments.

Module ForkEmissionAccumulatorProjection.
Module Key := PairOrderedType Nat_as_OT Nat_as_OT.
Module Maps := FMapAVL.Make Key.
Module Facts := WFacts_fun Key Maps.

Record Row := { emission_ordinal : nat; bucket_tag : string }.
Record TagObservation := { observed_tag : string; observed_ordinal : nat }.
Record Observation := {
  observed_key : Key.t; incoming_ordinal : nat; incoming_tag : string
}.
Definition tag_observation tag ordinal :=
 {| observed_tag := tag; observed_ordinal := ordinal |}.
Definition incoming_tag_observation observation :=
  tag_observation (incoming_tag observation) (incoming_ordinal observation).
Definition row_tag_observation row := tag_observation (bucket_tag row) (emission_ordinal row).
Record Accumulator := {
  site2_rows : Maps.t Row;
  ambiguous_multi_bucket : Maps.t (list TagObservation)
}.
Definition accumulator rows ambiguous :=
 {| site2_rows := rows; ambiguous_multi_bucket := ambiguous |}.
Definition new := accumulator (Maps.empty Row) (Maps.empty (list TagObservation)).

(** The source remove returns its old value. Under the preceding get result,
    this operation's expect succeeds and returns precisely that same row. *)
Definition remove_with_value {A} key (rows : Maps.t A) :=
  (Maps.find key rows, Maps.remove key rows).
Theorem just_matched_row_is_present_at_remove : forall key rows row,
  Maps.find key rows = Some row ->
  @remove_with_value Row key rows = (Some row, Maps.remove key rows).
Proof. intros; unfold remove_with_value; now rewrite H. Qed.

Definition record_site2_row observation state :=
  let key := observed_key observation in
  let ordinal := incoming_ordinal observation in
  let tag := incoming_tag_observation observation in
  match Maps.find key (ambiguous_multi_bucket state) with
  | Some tags => accumulator (site2_rows state)
      (Maps.add key (tags ++ [tag])%list (ambiguous_multi_bucket state))
  | None => match Maps.find key (site2_rows state) with
      | Some existing => if Nat.eqb (emission_ordinal existing) ordinal then state
        else accumulator (Maps.remove key (site2_rows state))
          (Maps.add key [row_tag_observation existing; tag] (ambiguous_multi_bucket state))
      | None => accumulator
          (Maps.add key {| emission_ordinal := ordinal; bucket_tag := incoming_tag observation |}
            (site2_rows state)) (ambiguous_multi_bucket state)
      end end.

Definition site2_row_count state := Maps.cardinal (site2_rows state).
Definition ambiguous_rule_count state := Maps.cardinal (ambiguous_multi_bucket state).
Definition site2_ordinal state key := option_map emission_ordinal (Maps.find key (site2_rows state)).
Definition is_ambiguous_multi_bucket state key := Maps.mem key (ambiguous_multi_bucket state).
Definition census_keys state :=
  (List.map fst (Maps.elements (site2_rows state)) ++
   List.map fst (Maps.elements (ambiguous_multi_bucket state)))%list.
Definition into_parts state := (site2_rows state, ambiguous_multi_bucket state).
Definition census_capacity_domain usize_max state :=
  site2_row_count state + ambiguous_rule_count state <= usize_max.
Definition ordered_readback state :=
  (Maps.elements (site2_rows state), Maps.elements (ambiguous_multi_bucket state)).
Definition rendered_ambiguities (render : TagObservation -> string) state :=
  List.map (fun entry => (fst entry, List.map render (snd entry)))
    (Maps.elements (ambiguous_multi_bucket state)).

Record OriginalState := { original_accumulator : Accumulator }.
Record SharedState := { shared_accumulator : Accumulator }.
Record MacroWrapper := { descriptor : SharedState }.
Definition relocate state :=
 {| descriptor := {| shared_accumulator := original_accumulator state |} |}.
Definition original_record observation state :=
 {| original_accumulator := record_site2_row observation (original_accumulator state) |}.
Definition wrapper_record observation state :=
 {| descriptor := {| shared_accumulator :=
      record_site2_row observation (shared_accumulator (descriptor state)) |} |}.
Definition wrapper_into_parts state := into_parts (shared_accumulator (descriptor state)).
Fixpoint original_record_sequence observations state := match observations with
| [] => state
| observation :: rest => original_record_sequence rest (original_record observation state) end.
Fixpoint wrapper_record_sequence observations state := match observations with
| [] => state
| observation :: rest => wrapper_record_sequence rest (wrapper_record observation state) end.
Theorem exact_recording_step_relocation : forall observation state,
  wrapper_record observation (relocate state) = relocate (original_record observation state).
Proof. reflexivity. Qed.
Theorem finite_recording_preserves_complete_accumulator : forall observations state,
  wrapper_record_sequence observations (relocate state) =
  relocate (original_record_sequence observations state).
Proof.
  induction observations as [|observation rest IH]; intros; [reflexivity|].
  cbn [wrapper_record_sequence original_record_sequence].
  rewrite exact_recording_step_relocation; apply IH.
Qed.
Theorem into_parts_moves_both_maps_without_reconstruction : forall state,
  wrapper_into_parts (relocate state) =
  (site2_rows (original_accumulator state), ambiguous_multi_bucket (original_accumulator state)).
Proof. reflexivity. Qed.
Theorem finite_recording_preserves_ordered_readback : forall observations state,
  ordered_readback (shared_accumulator (descriptor
    (wrapper_record_sequence observations (relocate state)))) =
  ordered_readback (original_accumulator (original_record_sequence observations state)).
Proof. intros; rewrite finite_recording_preserves_complete_accumulator; reflexivity. Qed.
Theorem finite_recording_preserves_formatted_diagnostics : forall observations state render,
  rendered_ambiguities render (shared_accumulator (descriptor
    (wrapper_record_sequence observations (relocate state)))) =
  rendered_ambiguities render (original_accumulator (original_record_sequence observations state)).
Proof. intros; rewrite finite_recording_preserves_complete_accumulator; reflexivity. Qed.

Theorem equal_ordinal_retains_first_tag_and_every_field : forall observation state existing,
  Maps.find (observed_key observation) (ambiguous_multi_bucket state) = None ->
  Maps.find (observed_key observation) (site2_rows state) = Some existing ->
  emission_ordinal existing = incoming_ordinal observation ->
  record_site2_row observation state = state.
Proof. intros; unfold record_site2_row; rewrite H, H0, H1, Nat.eqb_refl; reflexivity. Qed.
Theorem first_conflict_keeps_first_and_conflicting_tags_only : forall observation state existing,
  Maps.find (observed_key observation) (ambiguous_multi_bucket state) = None ->
  Maps.find (observed_key observation) (site2_rows state) = Some existing ->
  emission_ordinal existing <> incoming_ordinal observation ->
  record_site2_row observation state =
  accumulator (Maps.remove (observed_key observation) (site2_rows state))
    (Maps.add (observed_key observation)
      [row_tag_observation existing; incoming_tag_observation observation]
      (ambiguous_multi_bucket state)).
Proof.
  intros; unfold record_site2_row; rewrite H,H0.
  apply Nat.eqb_neq in H1; now rewrite H1.
Qed.
Theorem already_ambiguous_appends_without_deduplication : forall observation state tags,
  Maps.find (observed_key observation) (ambiguous_multi_bucket state) = Some tags ->
  record_site2_row observation state = accumulator (site2_rows state)
    (Maps.add (observed_key observation) (tags ++ [incoming_tag_observation observation])%list
      (ambiguous_multi_bucket state)).
Proof. intros; unfold record_site2_row; now rewrite H. Qed.

Lemma key_equality_is_tuple_equality : forall left right,
  Key.eq left right -> left = right.
Proof. intros [lc lr] [rc rr] [Hc Hr]; cbn in Hc,Hr; subst; reflexivity. Qed.
Definition disjoint state := forall key,
  Maps.find key (site2_rows state) = None \/
  Maps.find key (ambiguous_multi_bucket state) = None.
Theorem new_has_disjoint_maps : disjoint new.
Proof. intros key; left; apply Facts.empty_o. Qed.

Lemma append_ambiguity_preserves_disjointness : forall state key tags,
  disjoint state -> Maps.find key (site2_rows state) = None ->
  disjoint (accumulator (site2_rows state) (Maps.add key tags (ambiguous_multi_bucket state))).
Proof.
  intros state key tags Hdisjoint Hnone query; cbn [accumulator site2_rows ambiguous_multi_bucket].
  destruct (Key.eq_dec key query) as [Heq|Hneq].
  - apply key_equality_is_tuple_equality in Heq; subst; auto.
  - rewrite Facts.add_neq_o by assumption; apply Hdisjoint.
Qed.
Lemma move_to_ambiguity_preserves_disjointness : forall state key tags,
  disjoint state -> disjoint (accumulator (Maps.remove key (site2_rows state))
    (Maps.add key tags (ambiguous_multi_bucket state))).
Proof.
  intros state key tags Hdisjoint query; cbn [accumulator site2_rows ambiguous_multi_bucket].
  destruct (Key.eq_dec key query) as [Heq|Hneq].
  - left; apply Facts.remove_eq_o; assumption.
  - rewrite Facts.remove_neq_o, Facts.add_neq_o by assumption; apply Hdisjoint.
Qed.
Lemma insert_derived_preserves_disjointness : forall state key row,
  disjoint state -> Maps.find key (ambiguous_multi_bucket state) = None ->
  disjoint (accumulator (Maps.add key row (site2_rows state)) (ambiguous_multi_bucket state)).
Proof.
  intros state key row Hdisjoint Hnone query; cbn [accumulator site2_rows ambiguous_multi_bucket].
  destruct (Key.eq_dec key query) as [Heq|Hneq].
  - apply key_equality_is_tuple_equality in Heq; subst; auto.
  - rewrite Facts.add_neq_o by assumption; apply Hdisjoint.
Qed.
Theorem recording_preserves_disjoint_maps : forall observation state,
  disjoint state -> disjoint (record_site2_row observation state).
Proof.
  intros observation state Hdisjoint; unfold record_site2_row.
  destruct (Maps.find (observed_key observation) (ambiguous_multi_bucket state)) as [tags|] eqn:Hamb.
  - apply append_ambiguity_preserves_disjointness; [assumption|].
    destruct (Hdisjoint (observed_key observation)); [assumption|congruence].
  - destruct (Maps.find (observed_key observation) (site2_rows state)) as [existing|].
    + destruct (Nat.eqb (emission_ordinal existing) (incoming_ordinal observation));
        [assumption|apply move_to_ambiguity_preserves_disjointness; assumption].
    + apply insert_derived_preserves_disjointness; assumption.
Qed.
Theorem finite_recording_preserves_disjoint_maps : forall observations state,
  disjoint (original_accumulator state) ->
  disjoint (original_accumulator (original_record_sequence observations state)).
Proof.
  induction observations as [|observation rest IH]; intros state H; [assumption|].
  cbn [original_record_sequence]; apply IH; apply recording_preserves_disjoint_maps; assumption.
Qed.
Theorem recording_never_removes_ambiguity : forall observation state key tags,
  Maps.find key (ambiguous_multi_bucket state) = Some tags ->
  exists after, Maps.find key (ambiguous_multi_bucket (record_site2_row observation state)) = Some after.
Proof.
  intros observation state key tags H; unfold record_site2_row.
  destruct (Maps.find (observed_key observation) (ambiguous_multi_bucket state)) as [previous|].
  - cbn [accumulator ambiguous_multi_bucket]; rewrite Facts.add_o.
    destruct (Key.eq_dec (observed_key observation) key); eauto.
  - destruct (Maps.find (observed_key observation) (site2_rows state)) as [existing|].
    + destruct (Nat.eqb (emission_ordinal existing) (incoming_ordinal observation)); [eauto|].
      cbn [accumulator ambiguous_multi_bucket]; rewrite Facts.add_o.
      destruct (Key.eq_dec (observed_key observation) key); eauto.
    + cbn [accumulator ambiguous_multi_bucket]; eauto.
Qed.
Theorem ambiguity_is_permanent_over_finite_recording : forall observations state key tags,
  Maps.find key (ambiguous_multi_bucket (original_accumulator state)) = Some tags ->
  exists after, Maps.find key (ambiguous_multi_bucket
    (original_accumulator (original_record_sequence observations state))) = Some after.
Proof.
  induction observations as [|observation rest IH]; intros state key tags H; [eauto|].
  cbn [original_record_sequence]. apply recording_never_removes_ambiguity with (observation := observation) in H.
  destruct H as [after Hafter]; eapply IH; exact Hafter.
Qed.

Theorem derived_readback_is_key_sorted : forall state,
  Sorted (fun left right => Key.lt (fst left) (fst right)) (Maps.elements (site2_rows state)).
Proof. intros; apply Maps.elements_3. Qed.
Theorem ambiguous_readback_is_key_sorted : forall state,
  Sorted (fun left right => Key.lt (fst left) (fst right)) (Maps.elements (ambiguous_multi_bucket state)).
Proof. intros; apply Maps.elements_3. Qed.
Theorem counts_equal_ordered_readback_lengths : forall state,
  site2_row_count state = List.length (Maps.elements (site2_rows state)) /\
  ambiguous_rule_count state = List.length (Maps.elements (ambiguous_multi_bucket state)).
Proof. intros; split; apply Maps.cardinal_1. Qed.
Theorem census_is_derived_then_ambiguous_not_a_merged_sort : forall state,
  census_keys state = (List.map fst (fst (ordered_readback state)) ++
    List.map fst (snd (ordered_readback state)))%list.
Proof. reflexivity. Qed.

Definition emitted_value (_ : Accumulator) site (_ : Key.t) :=
  match site with 0 | 2 => 0 | 1 | 3 => 1 | _ => 65535 end.
Theorem recording_cannot_activate_derived_ordinals : forall observations state site key,
  emitted_value (original_accumulator (original_record_sequence observations state)) site key =
  emitted_value (original_accumulator state) site key.
Proof. reflexivity. Qed.
Theorem election_interface_remains_trait_default : forall state site key,
  emitted_value state site key = match site with 0 | 2 => 0 | 1 | 3 => 1 | _ => 65535 end.
Proof. reflexivity. Qed.

Print Assumptions just_matched_row_is_present_at_remove.
Print Assumptions finite_recording_preserves_complete_accumulator.
Print Assumptions into_parts_moves_both_maps_without_reconstruction.
Print Assumptions finite_recording_preserves_ordered_readback.
Print Assumptions finite_recording_preserves_formatted_diagnostics.
Print Assumptions equal_ordinal_retains_first_tag_and_every_field.
Print Assumptions first_conflict_keeps_first_and_conflicting_tags_only.
Print Assumptions already_ambiguous_appends_without_deduplication.
Print Assumptions finite_recording_preserves_disjoint_maps.
Print Assumptions ambiguity_is_permanent_over_finite_recording.
Print Assumptions derived_readback_is_key_sorted.
Print Assumptions ambiguous_readback_is_key_sorted.
Print Assumptions counts_equal_ordered_readback_lengths.
Print Assumptions census_is_derived_then_ambiguous_not_a_merged_sort.
Print Assumptions recording_cannot_activate_derived_ordinals.
Print Assumptions election_interface_remains_trait_default.

End ForkEmissionAccumulatorProjection.
