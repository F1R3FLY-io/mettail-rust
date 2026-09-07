(** * Incremental enrollment of the installed constructor roster

    The installed LanguageCore/image pair already supplies the source-aligned
    signatures. This model closes the finite-index glue: inserting each image
    constructor exactly once, refusing either key collision and the reserved
    reflection namespace, establishes the existing head codec's complete-entry
    inverse premise. The lists specify finite map observations, not a proposed
    linear-scan implementation. Rust uses reserved maps and dense reverse slots;
    neither hash iteration nor numeric equality across namespaces supplies IDs.

    A separate grammar-constructor map accepts repeated productions with the
    same label but refuses aliases, matching the existing dynamic reflector.
    Source/image validation, hashing complexity and allocator RSS are not proved
    here. Logical reservations use ReflectedHeadEnrollment's existing laws. *)

From Stdlib Require Import Lists.List Arith.PeanoNat Strings.String Bool.Bool Lia.
From RuntimeGrammar Require Import InstalledFltHeadCodec.
Import ListNotations.

Module InstalledFltBindingEnrollment.
Module Head := InstalledFltHeadCodec.InstalledFltHeadCodec.

(** Fixed logical slot payloads use 32-bit declaration coordinates. This is a
    resource schedule, not a wire encoding or physical Rust layout. Empty
    optional slots and temporary lookup tables are charged too. *)
Inductive IndexSlotKind := OptionalCoordinate | CoordinatePair | ForwardBinding.

Definition index_slot_bytes kind :=
  match kind with OptionalCoordinate => 5 | CoordinatePair => 8 | ForwardBinding => 12 end.

Definition index_payload_bytes categories sorts productions constructors :=
  categories * index_slot_bytes OptionalCoordinate +
  sorts * index_slot_bytes OptionalCoordinate +
  categories * index_slot_bytes CoordinatePair +
  productions * index_slot_bytes CoordinatePair +
  constructors * index_slot_bytes CoordinatePair +
  constructors * index_slot_bytes ForwardBinding.

Theorem complete_index_payload_schedule : forall categories sorts productions constructors,
  index_payload_bytes categories sorts productions constructors =
  13 * categories + 5 * sorts + 8 * productions + 20 * constructors.
Proof. intros. unfold index_payload_bytes, index_slot_bytes. lia. Qed.

Definition forward_matches (first second : Head.ConstructorBinding) :=
  Nat.eqb (Head.semantic_result first) (Head.semantic_result second) &&
  String.eqb (Head.reflected_label first) (Head.reflected_label second).

Definition reverse_matches (first second : Head.ConstructorBinding) :=
  Nat.eqb (Head.semantic_constructor first) (Head.semantic_constructor second).

Lemma forward_matches_symmetric : forall first second,
  forward_matches first second = forward_matches second first.
Proof. intros. unfold forward_matches. now rewrite Nat.eqb_sym, String.eqb_sym. Qed.

Lemma reverse_matches_symmetric : forall first second,
  reverse_matches first second = reverse_matches second first.
Proof. intros. unfold reverse_matches. apply Nat.eqb_sym. Qed.

Definition fresh entry table :=
  forallb (fun old => negb (forward_matches old entry || reverse_matches old entry)) table.

Lemma fresh_member : forall entry table old,
  fresh entry table = true -> In old table ->
  forward_matches old entry = false /\ reverse_matches old entry = false.
Proof.
  intros entry table old Hfresh Hin. unfold fresh in Hfresh.
  apply forallb_forall with (x := old) in Hfresh; [|exact Hin].
  apply negb_true_iff in Hfresh. now apply orb_false_iff in Hfresh.
Qed.

Lemma filter_empty : forall (matches : Head.ConstructorBinding -> bool) table,
  (forall old, In old table -> matches old = false) -> filter matches table = [].
Proof.
  intros matches table. induction table as [|old tail IH]; intros H; [reflexivity|].
  cbn. rewrite (H old (or_introl eq_refl)). apply IH.
  intros member Hin. apply H. now right.
Qed.

Lemma same_binding_self : forall entry, Head.same_binding (Some entry) entry = true.
Proof.
  intros entry. unfold Head.same_binding.
  destruct (Head.binding_eq_dec entry entry); [reflexivity|contradiction].
Qed.

Theorem fresh_enrollment_preserves_exact_inverses : forall entry table,
  Head.check_bindings table = true -> fresh entry table = true ->
  Head.check_bindings (entry :: table) = true.
Proof.
  intros entry table Hchecked Hfresh. unfold Head.check_bindings.
  apply forallb_forall. intros member [Hequal|Hin].
  - subst member. unfold Head.reflected_lookup, Head.semantic_lookup, Head.lookup_unique.
    cbn. rewrite !Nat.eqb_refl, String.eqb_refl. cbn.
    assert (Hforward : filter (fun old =>
      Nat.eqb (Head.semantic_result old) (Head.semantic_result entry) &&
      String.eqb (Head.reflected_label old) (Head.reflected_label entry)) table = []).
    { apply filter_empty. intros old Hin. exact (proj1 (fresh_member entry table old Hfresh Hin)). }
    assert (Hreverse : filter (fun old =>
      Nat.eqb (Head.semantic_constructor old) (Head.semantic_constructor entry)) table = []).
    { apply filter_empty. intros old Hin. exact (proj2 (fresh_member entry table old Hfresh Hin)). }
    rewrite Hforward, Hreverse. rewrite same_binding_self. reflexivity.
  - destruct (Head.checked_entry_has_exact_inverses table member Hchecked Hin)
      as [Hforward Hreverse].
    destruct (fresh_member entry table member Hfresh Hin) as [Fforward Freverse].
    rewrite forward_matches_symmetric in Fforward.
    rewrite reverse_matches_symmetric in Freverse.
    unfold forward_matches in Fforward. unfold reverse_matches in Freverse.
    unfold Head.reflected_lookup, Head.semantic_lookup, Head.lookup_unique in *.
    cbn. rewrite Fforward, Freverse, Hforward, Hreverse, same_binding_self. reflexivity.
Qed.

Definition enroll entry table :=
  if negb (Head.reserved_reflection_label (Head.reflected_label entry)) && fresh entry table
  then Some (entry :: table) else None.

Theorem enrolled_roster_satisfies_existing_wire_contract : forall entry table output,
  Head.check_wire_bindings table = true -> enroll entry table = Some output ->
  Head.check_wire_bindings output = true.
Proof.
  intros entry table output Htable Henroll. unfold enroll in Henroll.
  destruct (negb (Head.reserved_reflection_label (Head.reflected_label entry)) &&
    fresh entry table) eqn:Hguard; try discriminate.
  inversion Henroll; subst output. apply andb_true_iff in Hguard.
  destruct Hguard as [Hlabel Hfresh]. unfold Head.check_wire_bindings in *.
  apply andb_true_iff in Htable. destruct Htable as [Hchecked Hlabels].
  rewrite (fresh_enrollment_preserves_exact_inverses entry table Hchecked Hfresh).
  cbn. rewrite Hlabel, Hlabels. reflexivity.
Qed.

Fixpoint enroll_roster entries table :=
  match entries with
  | [] => Some table
  | entry :: tail =>
      match enroll entry table with
      | Some next => enroll_roster tail next
      | None => None
      end
  end.

Theorem whole_roster_retains_every_exact_entry : forall entries table output,
  enroll_roster entries table = Some output -> output = rev entries ++ table.
Proof.
  induction entries as [|entry tail IH]; intros table output H; cbn in H.
  - inversion H. reflexivity.
  - unfold enroll in H.
    destruct (negb (Head.reserved_reflection_label (Head.reflected_label entry)) &&
      fresh entry table); try discriminate.
    apply IH in H. rewrite H. cbn. now rewrite <- app_assoc.
Qed.

Theorem whole_roster_establishes_head_codec_premise : forall entries table output,
  Head.check_wire_bindings table = true -> enroll_roster entries table = Some output ->
  Head.check_wire_bindings output = true.
Proof.
  induction entries as [|entry tail IH]; intros table output Hchecked H; cbn in H.
  - inversion H; subst. exact Hchecked.
  - destruct (enroll entry table) as [next|] eqn:Enext; try discriminate.
    eapply IH; [|exact H].
    eapply enrolled_roster_satisfies_existing_wire_contract; eauto.
Qed.

(** The grammar-label map is keyed by Grammar ConstructorId, independently of
    semantic IDs. Repeated productions may have the same identity and label.
    A different label never overwrites the previously recorded identity. *)
Definition enroll_grammar_label (existing : option string) (label : string) :=
  match existing with
  | None => Some label
  | Some previous => if String.eqb previous label then Some previous else None
  end.

Theorem repeated_production_preserves_the_same_label : forall label,
  enroll_grammar_label (Some label) label = Some label.
Proof. intros. unfold enroll_grammar_label. now rewrite String.eqb_refl. Qed.

Theorem successful_grammar_enrollment_never_overwrites_identity : forall previous label result,
  enroll_grammar_label (Some previous) label = Some result ->
  previous = label /\ result = previous.
Proof.
  intros previous label result H. unfold enroll_grammar_label in H.
  destruct (String.eqb previous label) eqn:E; try discriminate.
  apply String.eqb_eq in E. inversion H; subst. auto.
Qed.

(** Names join the two independently indexed namespaces. The carrier is an
    uninterpreted admitted descriptor: retaining it proves neither that every
    carrier is supported by this adapter nor that a token implies a carrier. *)
Inductive AdmittedSortShape := SyntaxShape (literal : option nat) | NonSyntaxShape.
Record SortBinding := sort_binding {
  bound_category : nat;
  bound_sort : nat;
  bound_literal : option nat
}.

Definition join_named_sort category category_name sort sort_name shape :=
  match shape with
  | SyntaxShape literal =>
      if String.eqb category_name sort_name
      then Some (sort_binding category sort literal) else None
  | NonSyntaxShape => None
  end.

Theorem named_join_retains_both_coordinates_and_exact_carrier :
  forall category category_name sort sort_name shape output,
    join_named_sort category category_name sort sort_name shape = Some output ->
    category_name = sort_name /\ bound_category output = category /\
    bound_sort output = sort /\ shape = SyntaxShape (bound_literal output).
Proof.
  intros category category_name sort sort_name [literal|] output H; cbn in H;
    try discriminate.
  destruct (String.eqb category_name sort_name) eqn:E; try discriminate.
  apply String.eqb_eq in E. inversion H; subst. auto.
Qed.

Theorem nonsyntax_sort_is_not_fabricated_as_syntax : forall category name sort other,
  join_named_sort category name sort other NonSyntaxShape = None.
Proof. reflexivity. Qed.

(** The image's already-admitted grammar pair, domain and codomain remain one
    signature. Assembly checks the named join and recorded grammar-label slot
    against that exact signature before enrollment. *)
Record AdmittedSignature := signature {
  image_constructor : nat;
  image_domain : list nat;
  image_result : nat;
  image_category : nat;
  image_grammar_constructor : nat
}.

Definition assembled_binding sig label :=
  Head.binding (image_category sig) (image_grammar_constructor sig) label
    (image_constructor sig) (image_result sig) (image_domain sig).

Definition assemble_entry sig joined source_label recorded_label :=
  if Nat.eqb (bound_category joined) (image_category sig) &&
     Nat.eqb (bound_sort joined) (image_result sig) &&
     String.eqb recorded_label source_label
  then Some (assembled_binding sig source_label) else None.

Theorem assembly_uses_same_join_label_and_complete_signature :
  forall sig joined source_label recorded_label entry,
    assemble_entry sig joined source_label recorded_label = Some entry ->
    bound_category joined = image_category sig /\
    bound_sort joined = image_result sig /\ recorded_label = source_label /\
    entry = assembled_binding sig source_label.
Proof.
  intros sig joined source_label recorded_label entry H. unfold assemble_entry in H.
  destruct (Nat.eqb (bound_category joined) (image_category sig) &&
    Nat.eqb (bound_sort joined) (image_result sig) &&
    String.eqb recorded_label source_label) eqn:E; try discriminate.
  apply andb_true_iff in E. destruct E as [Ecoords Elabel].
  apply andb_true_iff in Ecoords. destruct Ecoords as [Ecategory Esort].
  apply Nat.eqb_eq in Ecategory, Esort. apply String.eqb_eq in Elabel.
  inversion H; subst. auto.
Qed.

Definition assemble_and_enroll sig joined source_label recorded_label table :=
  match assemble_entry sig joined source_label recorded_label with
  | Some entry => enroll entry table
  | None => None
  end.

Theorem published_entry_connects_signature_to_checked_roster :
  forall sig joined source_label recorded_label table output,
    Head.check_wire_bindings table = true ->
    assemble_and_enroll sig joined source_label recorded_label table = Some output ->
    bound_category joined = image_category sig /\
    bound_sort joined = image_result sig /\ recorded_label = source_label /\
    output = assembled_binding sig source_label :: table /\
    Head.check_wire_bindings output = true.
Proof.
  intros sig joined source_label recorded_label table output Hchecked H.
  unfold assemble_and_enroll in H.
  destruct (assemble_entry sig joined source_label recorded_label) as [entry|] eqn:E;
    try discriminate.
  pose proof (enrolled_roster_satisfies_existing_wire_contract entry table output Hchecked H)
    as Hwire.
  apply assembly_uses_same_join_label_and_complete_signature in E.
  destruct E as [Ecategory [Esort [Elabel Eentry]]]. subst entry.
  unfold enroll in H. destruct (negb _ && fresh _ _); try discriminate.
  inversion H; subst. auto.
Qed.

Example repeated_semantic_constructor_is_refused :
  let entry := Head.binding 13 41 "Pair"%string 7 19 [2; 3; 2] in
  enroll_roster [entry; entry] [] = None.
Proof. reflexivity. Qed.

Example different_grammar_alias_is_refused :
  enroll_grammar_label (Some "First"%string) "Second"%string = None.
Proof. reflexivity. Qed.

Example valid_roster_preserves_distinct_namespaces :
  let entry := Head.binding 13 41 "Pair"%string 7 19 [2; 3; 2] in
  enroll_roster [entry] [] = Some [entry] /\ Head.check_wire_bindings [entry] = true.
Proof. split; reflexivity. Qed.

End InstalledFltBindingEnrollment.

Print Assumptions InstalledFltBindingEnrollment.fresh_enrollment_preserves_exact_inverses.
Print Assumptions InstalledFltBindingEnrollment.enrolled_roster_satisfies_existing_wire_contract.
Print Assumptions InstalledFltBindingEnrollment.whole_roster_retains_every_exact_entry.
Print Assumptions InstalledFltBindingEnrollment.whole_roster_establishes_head_codec_premise.
Print Assumptions InstalledFltBindingEnrollment.repeated_production_preserves_the_same_label.
Print Assumptions InstalledFltBindingEnrollment.successful_grammar_enrollment_never_overwrites_identity.
Print Assumptions InstalledFltBindingEnrollment.named_join_retains_both_coordinates_and_exact_carrier.
Print Assumptions InstalledFltBindingEnrollment.nonsyntax_sort_is_not_fabricated_as_syntax.
Print Assumptions InstalledFltBindingEnrollment.assembly_uses_same_join_label_and_complete_signature.
Print Assumptions InstalledFltBindingEnrollment.published_entry_connects_signature_to_checked_roster.
Print Assumptions InstalledFltBindingEnrollment.complete_index_payload_schedule.
