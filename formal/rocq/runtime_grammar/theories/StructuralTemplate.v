From Stdlib Require Import List PeanoNat Lia.
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

(** The host parser records an explicit scoped reference and result category.
    Neither component is optional in the staged FLT boundary.  Resolution is a
    function of the current lexical environment; source spellings and registry
    names therefore cannot add another route. *)
Section ExplicitScopedRoute.
  Context {Reference Handle : Type}.

  Record TemplateHeader : Type := {
    header_reference : Reference;
    header_category : CategoryId
  }.

  Definition ScopedEnvironment := Reference -> option Handle.

  Definition resolve_header
      (environment : ScopedEnvironment) (header : TemplateHeader)
      : option (Handle * CategoryId) :=
    match environment (header_reference header) with
    | Some handle => Some (handle, header_category header)
    | None => None
    end.

  Theorem explicit_scoped_route_is_functional :
    forall environment header left right,
      resolve_header environment header = Some left ->
      resolve_header environment header = Some right ->
      left = right.
  Proof.
    intros environment header left right Hleft Hright.
    congruence.
  Qed.
End ExplicitScopedRoute.

(** URI literals and FLT templates share a backtick byte but not a lexical
    opener or a parser use site.  The concrete lexer recognizes an FLT opener
    as [reference:Category`] in one maximal-munch token.  Both identifiers are
    nonempty, so that token is strictly longer than the competing leading
    identifier.  A bare [`body`] remains a URI token; [reference`body`] is
    consequently an identifier followed by a URI token and is not an FLT.

    The model below records the accepted-token extents rather than the bytes of
    a particular identifier alphabet.  This is the information the generated
    maximal-munch lexer and modal parser consume. *)
Section UriFltLexicalOwnership.
  Inductive HeaderToken : Type :=
  | HeaderIdentifier
  | HeaderUriLiteral
  | HeaderFltOpen
  | HeaderGuestChunk
  | HeaderFltClose.

  Inductive HeaderSurface : Type :=
  | QualifiedFltSurface
      (reference_bytes category_bytes body_bytes : nat)
  | UnqualifiedBacktickSurface
      (reference_bytes body_bytes : nat)
  | BareUriSurface
      (body_bytes : nat).

  Inductive HeaderUseSite : Type :=
  | TemplateProcSite
  | BinderUriSite.

  Definition qualified_open_extent
      (reference_bytes category_bytes : nat) : nat :=
    reference_bytes + 1 + category_bytes + 1.

  Definition body_tokens (body_bytes : nat) : list HeaderToken :=
    if Nat.eqb body_bytes 0
    then [HeaderFltClose]
    else [HeaderGuestChunk; HeaderFltClose].

  Definition lex_header (surface : HeaderSurface)
      : option (list HeaderToken) :=
    match surface with
    | QualifiedFltSurface reference_bytes category_bytes body_bytes =>
        if andb (Nat.ltb 0 reference_bytes) (Nat.ltb 0 category_bytes)
        then Some (HeaderFltOpen :: body_tokens body_bytes)
        else None
    | UnqualifiedBacktickSurface reference_bytes body_bytes =>
        if andb (Nat.ltb 0 reference_bytes) (Nat.ltb 0 body_bytes)
        then Some [HeaderIdentifier; HeaderUriLiteral]
        else None
    | BareUriSurface body_bytes =>
        if Nat.ltb 0 body_bytes
        then Some [HeaderUriLiteral]
        else None
    end.

  Definition enters_guest_mode (tokens : list HeaderToken) : bool :=
    match tokens with
    | HeaderFltOpen :: _ => true
    | _ => false
    end.

  Definition accepted_at
      (site : HeaderUseSite) (tokens : list HeaderToken) : bool :=
    match site, tokens with
    | TemplateProcSite, HeaderFltOpen :: _ => true
    | BinderUriSite, [HeaderUriLiteral] => true
    | _, _ => false
    end.

  (** The colon, nonempty category, and delimiter make the FLT opener longer
      than its identifier prefix.  Maximal munch therefore selects the modal
      opener without a priority convention or parser feedback. *)
  Theorem qualified_flt_opener_strictly_extends_identifier :
    forall reference_bytes category_bytes,
      0 < reference_bytes ->
      0 < category_bytes ->
      reference_bytes <
        qualified_open_extent reference_bytes category_bytes.
  Proof.
    intros reference_bytes category_bytes Hreference Hcategory.
    unfold qualified_open_extent; lia.
  Qed.

  Theorem qualified_flt_enters_guest_mode :
    forall reference_bytes category_bytes body_bytes tokens,
      0 < reference_bytes ->
      0 < category_bytes ->
      lex_header
        (QualifiedFltSurface reference_bytes category_bytes body_bytes) =
        Some tokens ->
      enters_guest_mode tokens = true.
  Proof.
    intros reference_bytes category_bytes body_bytes tokens
      Hreference Hcategory Hlex.
    unfold lex_header in Hlex.
    apply Nat.ltb_lt in Hreference.
    apply Nat.ltb_lt in Hcategory.
    rewrite Hreference, Hcategory in Hlex; simpl in Hlex.
    inversion Hlex; reflexivity.
  Qed.

  Theorem qualified_flt_is_accepted_only_at_template_site :
    forall reference_bytes category_bytes body_bytes tokens,
      0 < reference_bytes ->
      0 < category_bytes ->
      lex_header
        (QualifiedFltSurface reference_bytes category_bytes body_bytes) =
        Some tokens ->
      accepted_at TemplateProcSite tokens = true /\
      accepted_at BinderUriSite tokens = false.
  Proof.
    intros reference_bytes category_bytes body_bytes tokens
      Hreference Hcategory Hlex.
    unfold lex_header in Hlex.
    apply Nat.ltb_lt in Hreference.
    apply Nat.ltb_lt in Hcategory.
    rewrite Hreference, Hcategory in Hlex; simpl in Hlex.
    inversion Hlex; split; reflexivity.
  Qed.

  Theorem unqualified_backtick_never_enters_guest_mode :
    forall reference_bytes body_bytes tokens,
      lex_header (UnqualifiedBacktickSurface reference_bytes body_bytes) =
        Some tokens ->
      enters_guest_mode tokens = false.
  Proof.
    intros reference_bytes body_bytes tokens Hlex.
    unfold lex_header in Hlex.
    destruct (andb (Nat.ltb 0 reference_bytes) (Nat.ltb 0 body_bytes))
      eqn:Hvalid; discriminate Hlex || (inversion Hlex; reflexivity).
  Qed.

  Theorem unqualified_backtick_is_not_an_flt_or_binder_uri :
    forall reference_bytes body_bytes tokens,
      lex_header (UnqualifiedBacktickSurface reference_bytes body_bytes) =
        Some tokens ->
      accepted_at TemplateProcSite tokens = false /\
      accepted_at BinderUriSite tokens = false.
  Proof.
    intros reference_bytes body_bytes tokens Hlex.
    unfold lex_header in Hlex.
    destruct (andb (Nat.ltb 0 reference_bytes) (Nat.ltb 0 body_bytes))
      eqn:Hvalid; discriminate Hlex || (inversion Hlex; split; reflexivity).
  Qed.

  Theorem bare_uri_remains_binder_owned :
    forall body_bytes tokens,
      lex_header (BareUriSurface body_bytes) = Some tokens ->
      accepted_at BinderUriSite tokens = true /\
      accepted_at TemplateProcSite tokens = false /\
      enters_guest_mode tokens = false.
  Proof.
    intros body_bytes tokens Hlex.
    unfold lex_header in Hlex.
    destruct (Nat.ltb 0 body_bytes) eqn:Hbody;
      discriminate Hlex || (inversion Hlex; repeat split; reflexivity).
  Qed.
End UriFltLexicalOwnership.

(** Polarity belongs to the use site, not to untrusted guest text.  The host
    stages the same structural capture as either a positive construction or a
    negative pattern, and the two cases are disjoint by construction. *)
Inductive TemplatePolarity : Type :=
| PositiveConstruction
| NegativePattern.

Theorem construction_and_pattern_polarities_are_disjoint :
  PositiveConstruction <> NegativePattern.
Proof.
  discriminate.
Qed.

(** Provenance is a half-open byte range in the original host source.  It is
    diagnostic metadata only: erasing ranges recovers exactly the semantic
    Text/Hole sequence. *)
Record SourceRange : Type := {
  range_start : nat;
  range_end : nat
}.

Definition range_valid (range : SourceRange) : Prop :=
  range_start range <= range_end range.

Record LocatedPiece : Type := {
  located_piece : TemplatePiece;
  piece_range : SourceRange
}.

Fixpoint erase_locations (pieces : list LocatedPiece) : list TemplatePiece :=
  match pieces with
  | [] => []
  | piece :: rest => located_piece piece :: erase_locations rest
  end.

Fixpoint located_text (pieces : list LocatedPiece) : list GuestChunk :=
  match pieces with
  | [] => []
  | piece :: rest =>
      match located_piece piece with
      | TextPiece text => text :: located_text rest
      | HolePiece _ => located_text rest
      end
  end.

Theorem provenance_erasure_preserves_guest_text :
  forall pieces,
    template_text (erase_locations pieces) = located_text pieces.
Proof.
  intro pieces; induction pieces as [|piece rest IH]; simpl; [reflexivity|].
  destruct (located_piece piece); simpl; rewrite IH; reflexivity.
Qed.

(** [ranges_tile_from cursor pieces finish] states that every piece range is
    valid, ranges are adjacent and source ordered, and together they cover the
    captured body without overlap or gaps. *)
Fixpoint ranges_tile_from
    (cursor : nat) (pieces : list LocatedPiece) (finish : nat) : Prop :=
  match pieces with
  | [] => cursor = finish
  | piece :: rest =>
      range_start (piece_range piece) = cursor /\
      range_start (piece_range piece) <= range_end (piece_range piece) /\
      ranges_tile_from (range_end (piece_range piece)) rest finish
  end.

Theorem tiled_ranges_are_valid :
  forall cursor pieces finish,
    ranges_tile_from cursor pieces finish ->
    Forall (fun piece => range_valid (piece_range piece)) pieces.
Proof.
  intros cursor pieces; revert cursor.
  induction pieces as [|piece rest IH]; intros cursor finish Htiles.
  - constructor.
  - simpl in Htiles.
    destruct Htiles as [_ [Hvalid Hrest]].
    constructor.
    + exact Hvalid.
    + apply (IH (range_end (piece_range piece)) finish Hrest).
Qed.

(** The lexer receives an explicit work schedule.  Every text piece starts one
    fresh recognizer run; every hole is a typed lattice terminal between runs.
    Mapping scheduled work back to pieces is the identity, so no scheduler step
    can join text across a hole or reinterpret a hole as source. *)
Inductive LexicalWork : Type :=
| RestartRecognizer : GuestChunk -> LexicalWork
| InjectHoleTerminal : HoleId -> LexicalWork.

Fixpoint lexical_schedule (template : list TemplatePiece) : list LexicalWork :=
  match template with
  | [] => []
  | TextPiece text :: rest =>
      RestartRecognizer text :: lexical_schedule rest
  | HolePiece id :: rest =>
      InjectHoleTerminal id :: lexical_schedule rest
  end.

Definition scheduled_piece (work : LexicalWork) : TemplatePiece :=
  match work with
  | RestartRecognizer text => TextPiece text
  | InjectHoleTerminal id => HolePiece id
  end.

Theorem recognizer_restart_schedule_is_exact :
  forall template,
    map scheduled_piece (lexical_schedule template) = template.
Proof.
  intro template; induction template as [|piece rest IH]; simpl; [reflexivity|].
  destruct piece; simpl; rewrite IH; reflexivity.
Qed.

(** A telescope is indexed in first-occurrence order.  [canonical_from base]
    avoids display-name lookup: the declaration at numeric position [i] has
    stable identifier [base + i]. *)
Record HoleDeclaration : Type := {
  declaration_hole : HoleId;
  declaration_category : option CategoryId
}.

Fixpoint canonical_from
    (next : HoleId) (telescope : list HoleDeclaration) : Prop :=
  match telescope with
  | [] => True
  | declaration :: rest =>
      declaration_hole declaration = next /\
      canonical_from (S next) rest
  end.

Definition canonical_telescope := canonical_from 0.

Theorem canonical_telescope_lookup_is_stable :
  forall base telescope index declaration,
    canonical_from base telescope ->
    nth_error telescope index = Some declaration ->
    declaration_hole declaration = base + index.
Proof.
  intros base telescope; revert base.
  induction telescope as [|head rest IH]; intros base index declaration Hcanonical Hlookup.
  - destruct index; discriminate.
  - simpl in Hcanonical; destruct Hcanonical as [Hhead Hrest].
    destruct index as [|index].
    + simpl in Hlookup; inversion Hlookup; subst; lia.
    + simpl in Hlookup.
      specialize (IH (S base) index declaration Hrest Hlookup).
      lia.
Qed.

Fixpoint hole_occurrence_count (pieces : list TemplatePiece) : nat :=
  match pieces with
  | [] => 0
  | TextPiece _ :: rest => hole_occurrence_count rest
  | HolePiece _ :: rest => S (hole_occurrence_count rest)
  end.

(** Effective limits are supplied by the trusted host and may be tightened by
    an installed language.  They are not fields from guest source. *)
Record TemplateBounds : Type := {
  max_source_bytes : nat;
  max_piece_count : nat;
  max_hole_declarations : nat;
  max_hole_occurrences : nat
}.

Definition within_template_bounds
    (bounds : TemplateBounds)
    (source_bytes : nat)
    (telescope : list HoleDeclaration)
    (pieces : list TemplatePiece) : Prop :=
  source_bytes <= max_source_bytes bounds /\
  length pieces <= max_piece_count bounds /\
  length telescope <= max_hole_declarations bounds /\
  hole_occurrence_count pieces <= max_hole_occurrences bounds.

Definition bounds_tighter (tight loose : TemplateBounds) : Prop :=
  max_source_bytes tight <= max_source_bytes loose /\
  max_piece_count tight <= max_piece_count loose /\
  max_hole_declarations tight <= max_hole_declarations loose /\
  max_hole_occurrences tight <= max_hole_occurrences loose.

Theorem tightening_bounds_cannot_add_an_admission :
  forall tight loose source_bytes telescope pieces,
    bounds_tighter tight loose ->
    within_template_bounds tight source_bytes telescope pieces ->
    within_template_bounds loose source_bytes telescope pieces.
Proof.
  intros tight loose source_bytes telescope pieces
    [Hsource [Hpieces [Hholes Hoccurrences]]]
    [Asource [Apieces [Aholes Aoccurrences]]].
  repeat split; lia.
Qed.

Theorem rejection_by_loose_bounds_is_preserved_by_tightening :
  forall tight loose source_bytes telescope pieces,
    bounds_tighter tight loose ->
    ~ within_template_bounds loose source_bytes telescope pieces ->
    ~ within_template_bounds tight source_bytes telescope pieces.
Proof.
  intros tight loose source_bytes telescope pieces Htight Hreject Hadmit.
  apply Hreject.
  exact (tightening_bounds_cannot_add_an_admission
    tight loose source_bytes telescope pieces Htight Hadmit).
Qed.

(** An ambiguity-lattice node lies on the global maximal-munch chain only
    when its parent already lies on that chain and the selected edge is the
    parent's longest accept.  Looking only at the current edge is unsound: a
    locally longest continuation of a secondary opener remains secondary. *)
Definition extend_primary_chain
    (parent_is_primary edge_is_longest : bool) : bool :=
  andb parent_is_primary edge_is_longest.

Fixpoint is_primary_edge_path (edge_choices : list bool) : bool :=
  match edge_choices with
  | [] => true
  | choice :: rest => andb choice (is_primary_edge_path rest)
  end.

Theorem primary_chain_extension_is_exact :
  forall prefix edge,
    extend_primary_chain (is_primary_edge_path prefix) edge =
    is_primary_edge_path (prefix ++ [edge]).
Proof.
  induction prefix as [|choice rest IH]; intros edge; simpl.
  - now destruct edge.
  - rewrite <- IH. now destruct choice.
Qed.

Theorem locally_longest_edge_cannot_promote_a_secondary_parent :
  forall edge_is_longest,
    extend_primary_chain false edge_is_longest = false.
Proof.
  intros edge_is_longest. reflexivity.
Qed.

(** Minimal witness for the fence-opener regression: the first edge selects
    a shorter identifier alternative; the next edge is locally longest, but
    the two-edge path is not globally primary. *)
Example local_only_primary_classification_is_unsound :
  is_primary_edge_path [false; true] = false /\
  hd false (rev [false; true]) = true.
Proof.
  split; reflexivity.
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
Print Assumptions explicit_scoped_route_is_functional.
Print Assumptions qualified_flt_opener_strictly_extends_identifier.
Print Assumptions qualified_flt_enters_guest_mode.
Print Assumptions qualified_flt_is_accepted_only_at_template_site.
Print Assumptions unqualified_backtick_never_enters_guest_mode.
Print Assumptions unqualified_backtick_is_not_an_flt_or_binder_uri.
Print Assumptions bare_uri_remains_binder_owned.
Print Assumptions construction_and_pattern_polarities_are_disjoint.
Print Assumptions provenance_erasure_preserves_guest_text.
Print Assumptions tiled_ranges_are_valid.
Print Assumptions recognizer_restart_schedule_is_exact.
Print Assumptions canonical_telescope_lookup_is_stable.
Print Assumptions tightening_bounds_cannot_add_an_admission.
Print Assumptions rejection_by_loose_bounds_is_preserved_by_tightening.
Print Assumptions primary_chain_extension_is_exact.
Print Assumptions locally_longest_edge_cannot_promote_a_secondary_parent.
Print Assumptions local_only_primary_classification_is_unsound.
Print Assumptions sound_cache_hit_is_uncached_parse.
Print Assumptions symbolic_cache_commutes_with_structural_grafting.
Print Assumptions different_language_commitment_cannot_hit.
Print Assumptions different_host_commitment_cannot_hit.
Print Assumptions running_owner_reentry_is_rejected.
Print Assumptions distinct_owner_waits.
Print Assumptions only_idle_flight_elects_an_owner.
