From Stdlib Require Import List PeanoNat.
Import ListNotations.

Definition HoleId := nat.
Definition CategoryId := nat.
Definition GuestChunk := nat.
Definition HostValue := nat.

Inductive TemplatePiece : Type :=
| TextPiece : GuestChunk -> TemplatePiece
| HolePiece : HoleId -> TemplatePiece.

Inductive ElaboratedPiece : Type :=
| GuestText : GuestChunk -> ElaboratedPiece
| StructuralGraft : HoleId -> HostValue -> ElaboratedPiece.

Definition HoleEnvironment := HoleId -> HostValue.

Fixpoint elaborate
    (environment : HoleEnvironment) (template : list TemplatePiece)
    : list ElaboratedPiece :=
  match template with
  | [] => []
  | TextPiece text :: rest => GuestText text :: elaborate environment rest
  | HolePiece id :: rest =>
      StructuralGraft id (environment id) :: elaborate environment rest
  end.

Fixpoint template_text (template : list TemplatePiece) : list GuestChunk :=
  match template with
  | [] => []
  | TextPiece text :: rest => text :: template_text rest
  | HolePiece _ :: rest => template_text rest
  end.

Fixpoint elaborated_text (term : list ElaboratedPiece) : list GuestChunk :=
  match term with
  | [] => []
  | GuestText text :: rest => text :: elaborated_text rest
  | StructuralGraft _ _ :: rest => elaborated_text rest
  end.

(** Structural elaboration cannot add, remove, split, join, or reinterpret a
    guest-text chunk. Hole values appear only as graft nodes. *)
Theorem structural_elaboration_has_no_text_injection :
  forall environment template,
    elaborated_text (elaborate environment template) = template_text template.
Proof.
  intros environment template.
  induction template as [|piece rest IH]; simpl; [reflexivity|].
  destruct piece; simpl; rewrite IH; reflexivity.
Qed.

Record HoleOccurrence : Type := {
  occurrence_hole : HoleId;
  occurrence_category : CategoryId
}.

Definition category_consistent (occurrences : list HoleOccurrence) : Prop :=
  forall left right,
    In left occurrences ->
    In right occurrences ->
    occurrence_hole left = occurrence_hole right ->
    occurrence_category left = occurrence_category right.

Definition inferred_category
    (occurrences : list HoleOccurrence) (id : HoleId) (category : CategoryId)
    : Prop :=
  exists occurrence,
    In occurrence occurrences /\
    occurrence_hole occurrence = id /\
    occurrence_category occurrence = category.

(** Once all occurrences of a repeated hole agree, inference is functional.
    A parser may retain several syntactic derivations, but it cannot assign two
    different categories to the same telescope entry. *)
Theorem repeated_hole_inference_is_unique :
  forall occurrences id left_category right_category,
    category_consistent occurrences ->
    inferred_category occurrences id left_category ->
    inferred_category occurrences id right_category ->
    left_category = right_category.
Proof.
  intros occurrences id left_category right_category Hconsistent Hleft Hright.
  destruct Hleft as [left [Hinleft [Hleftid Hleftcategory]]].
  destruct Hright as [right [Hinright [Hrightid Hrightcategory]]].
  subst left_category right_category.
  apply (Hconsistent left right Hinleft Hinright).
  now rewrite Hleftid, Hrightid.
Qed.

Definition DeclaredCategory := HoleId -> option CategoryId.

Definition respects_declarations
    (declarations : DeclaredCategory) (occurrences : list HoleOccurrence) : Prop :=
  forall occurrence declared,
    In occurrence occurrences ->
    declarations (occurrence_hole occurrence) = Some declared ->
    occurrence_category occurrence = declared.

(** An explicit [${x:Cat}] declaration pins every occurrence; contextual
    inference cannot silently widen or replace the declared category. *)
Theorem declared_category_is_preserved :
  forall declarations occurrences id declared inferred,
    respects_declarations declarations occurrences ->
    declarations id = Some declared ->
    inferred_category occurrences id inferred ->
    inferred = declared.
Proof.
  intros declarations occurrences id declared inferred Hrespects Hdeclared Hinferred.
  destruct Hinferred as [occurrence [Hin [Hid Hcategory]]].
  subst inferred.
  apply (Hrespects occurrence declared Hin).
  now rewrite Hid.
Qed.

Section SymbolicTemplateCache.
  Context {LanguageCommitment HostCommitment SymbolicParse : Type}.
  Variable parse_symbolic :
    LanguageCommitment -> HostCommitment -> list TemplatePiece -> SymbolicParse.

  Record SymbolicCacheEntry : Type := {
    cached_language_commitment : LanguageCommitment;
    cached_host_commitment : HostCommitment;
    cached_template : list TemplatePiece;
    cached_parse : SymbolicParse
  }.

  Definition cache_entry_sound (entry : SymbolicCacheEntry) : Prop :=
    cached_parse entry =
      parse_symbolic
        (cached_language_commitment entry)
        (cached_host_commitment entry)
        (cached_template entry).

  Definition cache_hit
      (entry : SymbolicCacheEntry)
      (language_commitment : LanguageCommitment)
      (host_commitment : HostCommitment)
      (template : list TemplatePiece) : Prop :=
    cached_language_commitment entry = language_commitment /\
    cached_host_commitment entry = host_commitment /\
    cached_template entry = template.

  Theorem sound_cache_hit_is_uncached_parse :
    forall entry language_commitment host_commitment template,
      cache_entry_sound entry ->
      cache_hit entry language_commitment host_commitment template ->
      cached_parse entry =
        parse_symbolic language_commitment host_commitment template.
  Proof.
    intros entry language_commitment host_commitment template
      Hsound [Hlanguage [Hhost Htemplate]].
    unfold cache_entry_sound in Hsound.
    now rewrite <- Hlanguage, <- Hhost, <- Htemplate.
  Qed.

  Variable graft : SymbolicParse -> HoleEnvironment -> HostValue.

  (** Fills are intentionally absent from the cache key and value.  They are
      grafted only after a sound symbolic hit, so changing a run-time binding
      cannot change or poison the cached guest parse. *)
  Theorem symbolic_cache_commutes_with_structural_grafting :
    forall entry language_commitment host_commitment template environment,
      cache_entry_sound entry ->
      cache_hit entry language_commitment host_commitment template ->
      graft (cached_parse entry) environment =
      graft
        (parse_symbolic language_commitment host_commitment template)
        environment.
  Proof.
    intros entry language_commitment host_commitment template environment
      Hsound Hhit.
    rewrite (sound_cache_hit_is_uncached_parse
      entry language_commitment host_commitment template Hsound Hhit).
    reflexivity.
  Qed.

  Theorem different_language_commitment_cannot_hit :
    forall entry language_commitment host_commitment template,
      cached_language_commitment entry <> language_commitment ->
      ~ cache_hit entry language_commitment host_commitment template.
  Proof.
    intros entry language_commitment host_commitment template
      Hdifferent [Hequal _].
    contradiction.
  Qed.

  (** A host commitment identifies deterministic token decoding and native
      evaluation behavior.  Stateful or uncommitted hosts therefore cannot
      obtain a cache hit through language identity alone. *)
  Theorem different_host_commitment_cannot_hit :
    forall entry language_commitment host_commitment template,
      cached_host_commitment entry <> host_commitment ->
      ~ cache_hit entry language_commitment host_commitment template.
  Proof.
    intros entry language_commitment host_commitment template
      Hdifferent [_ [Hequal _]].
    contradiction.
  Qed.
End SymbolicTemplateCache.

Section SymbolicTemplateSingleFlight.
  Context {Owner : Type}.
  Variable owner_eq_dec : forall left right : Owner, {left = right} + {left <> right}.

  Inductive CacheFlightState : Type :=
  | FlightIdle
  | FlightRunning (owner : Owner).

  Inductive CacheFlightDecision : Type :=
  | BecomeOwner
  | WaitForOwner
  | RejectReentrantCycle.

  Definition decide_cache_flight
      (requester : Owner) (state : CacheFlightState) : CacheFlightDecision :=
    match state with
    | FlightIdle => BecomeOwner
    | FlightRunning owner =>
        if owner_eq_dec requester owner
        then RejectReentrantCycle
        else WaitForOwner
    end.

  (** The iterative dispatcher never blocks a worker on a flight it already
      owns.  Same-key re-entry is rejected as a non-contracting cycle instead
      of recursing or deadlocking. *)
  Theorem running_owner_reentry_is_rejected :
    forall owner,
      decide_cache_flight owner (FlightRunning owner) = RejectReentrantCycle.
  Proof.
    intros owner. unfold decide_cache_flight.
    destruct (owner_eq_dec owner owner); [reflexivity|contradiction].
  Qed.

  Theorem distinct_owner_waits :
    forall requester owner,
      requester <> owner ->
      decide_cache_flight requester (FlightRunning owner) = WaitForOwner.
  Proof.
    intros requester owner Hdifferent. unfold decide_cache_flight.
    destruct (owner_eq_dec requester owner); [contradiction|reflexivity].
  Qed.

  Theorem only_idle_flight_elects_an_owner :
    forall requester state,
      decide_cache_flight requester state = BecomeOwner ->
      state = FlightIdle.
  Proof.
    intros requester state Hdecision.
    destruct state as [|owner]; [reflexivity|].
    unfold decide_cache_flight in Hdecision.
    destruct (owner_eq_dec requester owner); discriminate.
  Qed.
End SymbolicTemplateSingleFlight.

Print Assumptions structural_elaboration_has_no_text_injection.
Print Assumptions repeated_hole_inference_is_unique.
Print Assumptions declared_category_is_preserved.
Print Assumptions sound_cache_hit_is_uncached_parse.
Print Assumptions symbolic_cache_commutes_with_structural_grafting.
Print Assumptions different_language_commitment_cannot_hit.
Print Assumptions different_host_commitment_cannot_hit.
Print Assumptions running_owner_reentry_is_rejected.
Print Assumptions distinct_owner_waits.
Print Assumptions only_idle_flight_elects_an_owner.
