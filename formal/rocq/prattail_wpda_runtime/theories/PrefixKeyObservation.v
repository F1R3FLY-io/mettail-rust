(** Key-observation interface for the consumed prefix context.

    Reuses the existing FIRST retain_first, unified insert_at_key/insert_sequence,
    and patterned_has_ident workers. No new deduplicator, map algorithm, FIRST
    analysis, or runtime parser is introduced.

    A renaming is injective on the original observable key domain; the global
    injection below is a sufficient interface witness. The concrete neutral
    vocabulary must supply such a witness (or restrict this statement to its
    reachable keys), preserve the original pair-key constructor including the
    empty default guard, and supply the original Ident substring observation.
    These are explicit theorem premises, NOT axioms or an assertion that arbitrary
    semantic token equality preserves Rust quotation equality.

    Key is the existing model's string-pair carrier. It is an extensional name
    for keys in this proof, not a requirement to render or parse Rust tokens at
    runtime. Static ToString behavior stays unchanged. Finite typed constructors
    require separate constructor-to-macro correspondence tests.

    The map relation compares lookup at renamed keys and the separate
    first-insertion roster. It deliberately says NOTHING about sorted map
    enumeration, tree representation, or comparison order. Production consumes
    unified_order. Payloads remain opaque and complete: guard Option, provenance,
    and descriptor multiplicity are not quotiented by key equality.

    Ident is independent of deduplication: Some(empty guard) may collide with
    None as a key but must still suppress the unguarded Ident observation.
    The inherited symbolic FormatPattern trace denotes that observation site;
    a neutral flag does not promise to execute a formatter.

    Source-to-Rust correspondence, allocation/failure policy, payload conversion,
    effectful ToString behavior, and whole-parser correctness remain outside
    this key-interface theorem.
*)
From Stdlib Require Import List String Bool.
From PrattailWpdaRuntime Require Import UnifiedPrefixDescriptorProjection
  OriginalFirstSetProjection OriginalIdentSummaryProjection.
Import ListNotations.
Set Implicit Arguments.

Module PrefixKeyObservation.
Module U := UnifiedPrefixDescriptorProjection.UnifiedPrefixDescriptorProjection.
Module F := OriginalFirstSetProjection.OriginalFirstSetProjection.
Module I := OriginalIdentSummaryProjection.OriginalIdentSummaryProjection.
Definition Key := U.BucketKey.t.

Lemma ordered_key_equality : forall a b : Key, U.BucketKey.eq a b <-> a = b.
Proof.
  intros [a1 a2] [b1 b2].
  change ((a1 = b1 /\ a2 = b2) <-> (a1,a2) = (b1,b2)); split.
  - intros [H1 H2]; now subst.
  - intros H; inversion H; auto.
Qed.

Lemma key_eqb_true : forall a b : Key, F.key_eqb a b = true <-> a = b.
Proof.
  intros [a1 a2] [b1 b2]; unfold F.key_eqb; cbn.
  rewrite Bool.andb_true_iff, !String.eqb_eq; split.
  - intros [H1 H2]; now subst.
  - intros H; inversion H; auto.
Qed.

Lemma key_eqb_refl : forall key : Key, F.key_eqb key key = true.
Proof. intros; apply key_eqb_true; reflexivity. Qed.

Section Renaming.
Variable rename : Key -> Key.

Definition ReflectsEquality :=
  forall left right, rename left = rename right -> left = right.

Theorem renamed_comparison : ReflectsEquality -> forall left right,
  F.key_eqb (rename left) (rename right) = F.key_eqb left right.
Proof.
  intros reflects left right.
  destruct (F.key_eqb left right) eqn:Hsame.
  - apply key_eqb_true in Hsame; subst; apply key_eqb_refl.
  - destruct (F.key_eqb (rename left) (rename right)) eqn:Hrenamed; auto.
    apply key_eqb_true in Hrenamed; apply reflects in Hrenamed; subst.
    rewrite key_eqb_refl in Hsame; discriminate.
Qed.

Theorem renamed_membership : ReflectsEquality -> forall seen key,
  existsb (F.key_eqb (rename key)) (map rename seen) =
  existsb (F.key_eqb key) seen.
Proof.
  intros reflects seen; induction seen as [|head rest IH]; intros key; cbn.
  - reflexivity.
  - rewrite renamed_comparison by exact reflects; now rewrite IH.
Qed.

Section FirstRows.
Context {Rule Literal Pattern State : Type}.
Variables original neutral : @F.Callbacks Rule Literal Pattern State.

Definition RowKeyCorrespondence :=
  forall row, F.row_key neutral row = rename (F.row_key original row).

Theorem stable_first_payload_dedup : ReflectsEquality -> RowKeyCorrespondence ->
  forall input seen,
  F.retain_first neutral (map rename seen) input =
  F.retain_first original seen input.
Proof.
  intros reflects corresponds input; induction input as [|row rest IH]; intros seen.
  - reflexivity.
  - cbn [F.retain_first].
    rewrite corresponds, renamed_membership by exact reflects.
    destruct (existsb (F.key_eqb (F.row_key original row)) seen).
    + apply IH.
    + f_equal.
      specialize (IH (seen ++ [F.row_key original row])%list).
      rewrite map_app in IH; exact IH.
Qed.

Theorem duplicate_key_preserves_complete_first_row :
  ReflectsEquality -> RowKeyCorrespondence -> forall first second,
  F.row_key original first = F.row_key original second ->
  F.retain_first neutral [] [first; second] = [first].
Proof.
  intros reflects corresponds first second same.
  change (F.retain_first neutral (map rename []) [first;second] = [first]).
  rewrite stable_first_payload_dedup by assumption.
  now apply F.duplicate_formatter_key_keeps_first_complete_payload.
Qed.
End FirstRows.

Section Buckets.
Context {Payload Descriptor : Type}.
Definition Related (original neutral : @U.BucketState Payload Descriptor) :=
  (forall query, U.BucketMaps.find (rename query) (U.buckets neutral) =
                 U.BucketMaps.find query (U.buckets original)) /\
  U.first_key_order neutral = map rename (U.first_key_order original).

Theorem empty_states_related :
  Related (U.bucket_state (U.BucketMaps.empty _) [])
          (U.bucket_state (U.BucketMaps.empty _) []).
Proof.
  split; cbn.
  - intro query; reflexivity.
  - reflexivity.
Qed.

Lemma related_membership : forall original neutral,
  Related original neutral -> forall query,
  U.BucketMaps.mem (rename query) (U.buckets neutral) =
  U.BucketMaps.mem query (U.buckets original).
Proof.
  intros original neutral [lookup order] query.
  rewrite !U.BucketFacts.mem_find_b, lookup; reflexivity.
Qed.

Theorem insertion_preserves_lookup_payloads_and_order : ReflectsEquality ->
  forall original neutral key (insertion : @U.Insertion Payload Descriptor),
  Related original neutral ->
  Related (fst (U.insert_at_key key insertion original))
          (fst (U.insert_at_key (rename key) insertion neutral)).
Proof.
  intros reflects original neutral key insertion relation.
  destruct relation as [lookup order]; split.
  - intro query.
    destruct (U.BucketKey.eq_dec key query) as [equal | unequal].
    + apply ordered_key_equality in equal; subst query.
      destruct (U.BucketMaps.find key (U.buckets original)) as [old|] eqn:prior.
      * rewrite (@U.existing_bucket_preserves_first_payload_and_appends
          Payload Descriptor (rename key) insertion neutral old)
          by (rewrite lookup; exact prior).
        rewrite (@U.existing_bucket_preserves_first_payload_and_appends
          Payload Descriptor key insertion original old) by exact prior.
        reflexivity.
      * rewrite U.absent_entry_constructs_original_payload
          by (rewrite lookup; exact prior).
        rewrite U.absent_entry_constructs_original_payload by exact prior.
        reflexivity.
    + assert (different : ~ U.BucketKey.eq (rename key) (rename query)).
      { intro same; apply unequal; apply ordered_key_equality.
        apply reflects; now apply ordered_key_equality in same. }
      rewrite U.other_bucket_entries_are_unchanged by exact different.
      rewrite U.other_bucket_entries_are_unchanged by exact unequal.
      apply lookup.
  - assert (membership : U.BucketMaps.mem (rename key) (U.buckets neutral) =
                         U.BucketMaps.mem key (U.buckets original)).
    { apply related_membership; split; assumption. }
    destruct (U.BucketMaps.mem key (U.buckets original)) eqn:present.
    + rewrite U.existing_key_does_not_append_order by exact membership.
      rewrite U.existing_key_does_not_append_order by exact present.
      exact order.
    + rewrite U.absent_key_appends_exactly_once by exact membership.
      rewrite U.absent_key_appends_exactly_once by exact present.
      rewrite order, map_app; reflexivity.
Qed.

Theorem renamed_finite_insertions : ReflectsEquality ->
  forall (key_of : @U.Insertion Payload Descriptor -> Key) insertions original neutral,
  Related original neutral ->
  Related
    (fst (U.insert_sequence insertions original
      (fun insertion state => U.insert_at_key (key_of insertion) insertion state)))
    (fst (U.insert_sequence insertions neutral
      (fun insertion state => U.insert_at_key (rename (key_of insertion)) insertion state))).
Proof.
  intros reflects key_of insertions; induction insertions as [|insertion rest IH];
    intros original neutral relation.
  - exact relation.
  - cbn [U.insert_sequence].
    assert (next : Related
      (fst (U.insert_at_key (key_of insertion) insertion original))
      (fst (U.insert_at_key (rename (key_of insertion)) insertion neutral))).
    { apply insertion_preserves_lookup_payloads_and_order; assumption. }
    destruct (U.insert_at_key (key_of insertion) insertion original) as [left levents] eqn:Hl.
    destruct (U.insert_at_key (rename (key_of insertion)) insertion neutral) as [right revents] eqn:Hr.
    try rewrite Hl, Hr in next; cbn in next.
    specialize (IH left right next).
    destruct (U.insert_sequence rest left
      (fun item state => U.insert_at_key (key_of item) item state)).
    destruct (U.insert_sequence rest right
      (fun item state => U.insert_at_key (rename (key_of item)) item state)).
    exact IH.
Qed.

(** Existing append/first-payload laws apply unchanged to either key spelling. *)
Definition retained_first_payload_law := @U.existing_bucket_preserves_first_payload_and_appends.
Definition retained_new_payload_law := @U.absent_entry_constructs_original_payload.
Definition retained_order_law := @U.absent_key_appends_exactly_once.
End Buckets.
End Renaming.

Theorem default_empty_guard_equivalence : forall Payload (format : Payload -> string) pattern empty,
  format empty = EmptyString ->
  U.original_key format pattern None = U.original_key format pattern (Some empty).
Proof. intros; now apply U.empty_guard_collision_keeps_distinct_input_payloads. Qed.

Section IdentObservation.
Context {Rule Literal Pattern State : Type}.
Variables original neutral : @F.Callbacks Rule Literal Pattern State.
Variables original_contains neutral_contains : string -> bool.

Definition IdentCorrespondence :=
  forall pattern, neutral_contains (F.format neutral pattern) =
                  original_contains (F.format original pattern).

Theorem ident_observation_correspondence : IdentCorrespondence -> forall pairs events,
  I.patterned_has_ident neutral neutral_contains pairs events =
  I.patterned_has_ident original original_contains pairs events.
Proof.
  intros corresponds pairs; induction pairs as [|[pattern guard] rest IH]; intro events.
  - reflexivity.
  - destruct guard; cbn [I.patterned_has_ident].
    + apply IH.
    + rewrite corresponds.
      destruct (original_contains (F.format original pattern)); [reflexivity | apply IH].
Qed.

Theorem present_guard_suppresses_ident_observation : forall pattern guard rest events,
  I.patterned_has_ident neutral neutral_contains ((pattern,Some guard)::rest) events =
  I.patterned_has_ident neutral neutral_contains rest events.
Proof. reflexivity. Qed.
End IdentObservation.

Print Assumptions renamed_comparison.
Print Assumptions renamed_membership.
Print Assumptions stable_first_payload_dedup.
Print Assumptions duplicate_key_preserves_complete_first_row.
Print Assumptions empty_states_related.
Print Assumptions insertion_preserves_lookup_payloads_and_order.
Print Assumptions renamed_finite_insertions.
Print Assumptions default_empty_guard_equivalence.
Print Assumptions ident_observation_correspondence.
Print Assumptions present_guard_suppresses_ident_observation.
End PrefixKeyObservation.
