(** * Checked constructor identity at the installed FLT boundary

    A grammar constructor/category identifier and a semantic constructor/sort
    identifier inhabit different namespaces.  An installed image supplies the
    correspondence, not equality of their numeric representations.  This model
    checks a finite correspondence table in both directions before using it.
    Repeated or conflicting bindings are refused, never resolved by selecting
    the first candidate.

    [lookup_unique] specifies the observable contract of the production
    checked maps, not a proposed linear-scan implementation.  The admitted
    table's source/image provenance is supplied by existing installation
    validation.  This file proves the table's own reverse-uniqueness check and
    the positional constructor-head codec; it does not certify source/image
    validation, arbitrary protobuf messages, native payloads, or a complete
    tree walk.  Native payload laws are in [NativeReflectionCodec].

    Child references are flat arena coordinates.  The ordered argument plan
    pairs each occurrence with its expected sort.  Visiting those children,
    checking their sorts and categories, remapping coordinates, enforcing one
    shared work budget, and publishing a whole result are separate obligations.
    In particular, successful head conversion does not admit its descendants. *)

From Stdlib Require Import List Arith.PeanoNat Strings.Ascii Strings.String Bool.Bool.
Import ListNotations.

Module InstalledFltHeadCodec.

Record ConstructorBinding := binding {
  grammar_category : nat;
  grammar_constructor : nat;
  reflected_label : string;
  semantic_constructor : nat;
  semantic_result : nat;
  semantic_domain : list nat
}.

Definition binding_eq_dec : forall first second : ConstructorBinding,
  {first = second} + {first <> second}.
Proof.
  decide equality; try apply string_dec; try apply Nat.eq_dec.
  apply list_eq_dec. apply Nat.eq_dec.
Defined.

Definition lookup_unique (matches : ConstructorBinding -> bool)
    (table : list ConstructorBinding) : option ConstructorBinding :=
  match filter matches table with
  | [entry] => Some entry
  | _ => None
  end.

Lemma unique_lookup_sound : forall matches table entry,
  lookup_unique matches table = Some entry ->
  In entry table /\ matches entry = true.
Proof.
  intros matches table entry H. unfold lookup_unique in H.
  destruct (filter matches table) as [|first [|second rest]] eqn:E;
    try discriminate.
  inversion H; subst first. apply filter_In.
  rewrite E. now left.
Qed.

Theorem multiple_candidates_refused : forall matches table first second rest,
  filter matches table = first :: second :: rest ->
  lookup_unique matches table = None.
Proof. intros matches table first second rest H. unfold lookup_unique. now rewrite H. Qed.

Definition reflected_lookup table sort label :=
  lookup_unique (fun entry =>
    Nat.eqb (semantic_result entry) sort &&
    String.eqb (reflected_label entry) label) table.

Definition semantic_lookup table constructor :=
  lookup_unique (fun entry => Nat.eqb (semantic_constructor entry) constructor) table.

Definition same_binding (found : option ConstructorBinding) (expected : ConstructorBinding) :=
  match found with
  | Some actual => if binding_eq_dec actual expected then true else false
  | None => false
  end.

Lemma same_binding_true : forall found expected,
  same_binding found expected = true -> found = Some expected.
Proof.
  intros [actual|] expected H; cbn in H; try discriminate.
  destruct (binding_eq_dec actual expected); [now subst|discriminate].
Qed.

Definition check_bindings (table : list ConstructorBinding) : bool :=
  forallb (fun entry =>
    same_binding (reflected_lookup table (semantic_result entry) (reflected_label entry)) entry
    && same_binding (semantic_lookup table (semantic_constructor entry)) entry) table.

Theorem checked_entry_has_exact_inverses : forall table entry,
  check_bindings table = true -> In entry table ->
  reflected_lookup table (semantic_result entry) (reflected_label entry) = Some entry /\
  semantic_lookup table (semantic_constructor entry) = Some entry.
Proof.
  intros table entry Hchecked Hmember.
  unfold check_bindings in Hchecked. apply forallb_forall with (x := entry) in Hchecked;
    [|exact Hmember].
  apply andb_true_iff in Hchecked. destruct Hchecked as [Hfirst Hsecond].
  split; now apply same_binding_true.
Qed.

Lemma reflected_lookup_sound : forall table sort label entry,
  reflected_lookup table sort label = Some entry ->
  In entry table /\ semantic_result entry = sort /\ reflected_label entry = label.
Proof.
  intros table sort label entry H. apply unique_lookup_sound in H.
  destruct H as [Hmember Hkeys]. apply andb_true_iff in Hkeys.
  destruct Hkeys as [Hsort Hlabel]. apply Nat.eqb_eq in Hsort.
  apply String.eqb_eq in Hlabel. auto.
Qed.

Lemma semantic_lookup_sound : forall table constructor entry,
  semantic_lookup table constructor = Some entry ->
  In entry table /\ semantic_constructor entry = constructor.
Proof.
  intros table constructor entry H. apply unique_lookup_sound in H.
  destruct H as [Hmember Hkey]. apply Nat.eqb_eq in Hkey. auto.
Qed.

Definition project_constructor table sort label (children : list nat) :=
  match reflected_lookup table sort label with
  | Some entry =>
      if Nat.eqb (List.length (semantic_domain entry)) (List.length children)
      then Some (semantic_constructor entry, children) else None
  | None => None
  end.

Definition restore_constructor table sort constructor (children : list nat) :=
  match semantic_lookup table constructor with
  | Some entry =>
      if Nat.eqb (semantic_result entry) sort &&
        Nat.eqb (List.length (semantic_domain entry)) (List.length children)
      then Some (reflected_label entry, children) else None
  | None => None
  end.

Theorem restore_projected_constructor : forall table sort label children constructor output,
  check_bindings table = true ->
  project_constructor table sort label children = Some (constructor, output) ->
  restore_constructor table sort constructor output = Some (label, children).
Proof.
  intros table sort label children constructor output Hchecked Hproject.
  unfold project_constructor in Hproject.
  destruct (reflected_lookup table sort label) as [entry|] eqn:E; try discriminate.
  destruct (Nat.eqb (List.length (semantic_domain entry)) (List.length children)) eqn:Earity;
    try discriminate.
  inversion Hproject; subst constructor output.
  apply reflected_lookup_sound in E. destruct E as [Hmember [Hsort Hlabel]].
  destruct (checked_entry_has_exact_inverses table entry Hchecked Hmember) as [_ Hreverse].
  unfold restore_constructor. rewrite Hreverse, Hsort, Nat.eqb_refl, Earity, Hlabel.
  reflexivity.
Qed.

Theorem project_restored_constructor : forall table sort constructor children label output,
  check_bindings table = true ->
  restore_constructor table sort constructor children = Some (label, output) ->
  project_constructor table sort label output = Some (constructor, children).
Proof.
  intros table sort constructor children label output Hchecked Hrestore.
  unfold restore_constructor in Hrestore.
  destruct (semantic_lookup table constructor) as [entry|] eqn:E; try discriminate.
  destruct (Nat.eqb (semantic_result entry) sort &&
    Nat.eqb (List.length (semantic_domain entry)) (List.length children)) eqn:Echecks;
    try discriminate.
  inversion Hrestore; subst label output.
  apply andb_true_iff in Echecks. destruct Echecks as [Esort Earity].
  apply Nat.eqb_eq in Esort.
  apply semantic_lookup_sound in E. destruct E as [Hmember Hconstructor].
  destruct (checked_entry_has_exact_inverses table entry Hchecked Hmember) as [Hreverse _].
  unfold project_constructor. rewrite <- Esort, Hreverse, Earity, Hconstructor.
  reflexivity.
Qed.

Theorem projection_retains_every_child : forall table sort label children constructor output,
  project_constructor table sort label children = Some (constructor, output) -> output = children.
Proof.
  intros table sort label children constructor output H. unfold project_constructor in H.
  destruct (reflected_lookup table sort label) as [entry|]; try discriminate.
  destruct (Nat.eqb (List.length (semantic_domain entry)) (List.length children));
    inversion H. reflexivity.
Qed.

(** A zip is safe only after the arity check; an unchecked zip would silently
    truncate one side.  The plan's two projections prove exact ordered lists,
    not merely equal lengths or equal sets of references. *)
Definition argument_plan (domain children : list nat) : option (list (nat * nat)) :=
  if Nat.eqb (List.length domain) (List.length children)
  then Some (combine domain children) else None.

Lemma combine_exact_projections : forall (domain children : list nat),
  List.length domain = List.length children ->
  map fst (combine domain children) = domain /\ map snd (combine domain children) = children.
Proof.
  induction domain as [|sort rest IH]; intros [|child tail] H; try discriminate.
  - split; reflexivity.
  - cbn in H. injection H as H.
    destruct (IH tail H) as [Hsorts Hchildren]. cbn.
    rewrite Hsorts, Hchildren. split; reflexivity.
Qed.

Theorem argument_plan_preserves_order_sorts_and_multiplicity : forall domain children plan,
  argument_plan domain children = Some plan ->
  map fst plan = domain /\ map snd plan = children.
Proof.
  intros domain children plan H. unfold argument_plan in H.
  destruct (Nat.eqb (List.length domain) (List.length children)) eqn:E; try discriminate.
  inversion H; subst plan. apply combine_exact_projections. now apply Nat.eqb_eq.
Qed.

(** Resolve the binding and obtain the argument plan in one operation.  This
    rules out substituting a different, merely equal-length domain vector. *)
Definition resolve_constructor_plan table sort label children :=
  match reflected_lookup table sort label with
  | Some entry =>
      match argument_plan (semantic_domain entry) children with
      | Some plan => Some (entry, plan)
      | None => None
      end
  | None => None
  end.

Theorem resolved_plan_uses_the_same_exact_binding : forall table sort label children entry plan,
  resolve_constructor_plan table sort label children = Some (entry, plan) ->
  In entry table /\ semantic_result entry = sort /\ reflected_label entry = label /\
  map fst plan = semantic_domain entry /\ map snd plan = children.
Proof.
  intros table sort label children entry plan H. unfold resolve_constructor_plan in H.
  destruct (reflected_lookup table sort label) as [found|] eqn:Ebinding; try discriminate.
  destruct (argument_plan (semantic_domain found) children) as [actual|] eqn:Eplan;
    try discriminate.
  inversion H; subst found actual.
  apply reflected_lookup_sound in Ebinding.
  apply argument_plan_preserves_order_sorts_and_multiplicity in Eplan.
  destruct Ebinding as [Hmember [Hsort Hlabel]], Eplan as [Hdomain Hchildren].
  auto.
Qed.

Example permuted_identity_binding :
  let entry := binding 13 41 "Pair"%string 7 19 [2; 3; 2] in
  check_bindings [entry] = true /\
  project_constructor [entry] 19 "Pair"%string [91; 14; 91] = Some (7, [91; 14; 91]) /\
  restore_constructor [entry] 19 7 [91; 14; 91] = Some ("Pair"%string, [91; 14; 91]).
Proof. repeat split; reflexivity. Qed.

Example conflicting_reverse_binding_refused :
  check_bindings [binding 0 0 "First"%string 7 3 []; binding 0 1 "Second"%string 7 3 []] = false.
Proof. reflexivity. Qed.

Example conflicting_reflected_binding_refused :
  check_bindings [binding 0 0 "Same"%string 7 3 []; binding 0 1 "Same"%string 8 3 []] = false.
Proof. reflexivity. Qed.

Example extra_argument_refused : argument_plan [2; 3] [5; 6; 7] = None.
Proof. reflexivity. Qed.

Example missing_argument_refused : argument_plan [2; 3] [5] = None.
Proof. reflexivity. Qed.

(** The existing reflector reserves the entire caret-prefixed namespace, as
    expressed by [ast::validation::is_reserved_reflect_label].  Runtime source
    validation alone does not establish that restriction.  A binding consumed
    by this reflector therefore needs this additional representability check;
    it is not a new restriction on the abstract GrammarCore data model. *)
Definition reserved_reflection_label (label : string) : bool :=
  match label with
  | String "^"%char _ => true
  | _ => false
  end.

Definition check_wire_bindings (table : list ConstructorBinding) : bool :=
  check_bindings table &&
    forallb (fun entry => negb (reserved_reflection_label (reflected_label entry))) table.

Theorem wire_bindings_have_checked_inverses : forall table,
  check_wire_bindings table = true -> check_bindings table = true.
Proof.
  intros table H. unfold check_wire_bindings in H. apply andb_true_iff in H. tauto.
Qed.

Theorem wire_binding_has_unreserved_constructor_label : forall table entry,
  check_wire_bindings table = true -> In entry table ->
  reserved_reflection_label (reflected_label entry) = false.
Proof.
  intros table entry H Hmember. unfold check_wire_bindings in H.
  apply andb_true_iff in H. destruct H as [_ Hlabels].
  apply forallb_forall with (x := entry) in Hlabels; [|exact Hmember].
  now apply negb_true_iff in Hlabels.
Qed.

Theorem resolved_constructor_cannot_be_a_reserved_head : forall table sort label entry tail,
  check_wire_bindings table = true -> reflected_lookup table sort label = Some entry ->
  label <> String "^"%char tail.
Proof.
  intros table sort label entry tail Hchecked Hlookup Hequal.
  apply reflected_lookup_sound in Hlookup. destruct Hlookup as [Hmember [_ Hlabel]].
  pose proof (wire_binding_has_unreserved_constructor_label table entry Hchecked Hmember) as H.
  rewrite Hlabel, Hequal in H. discriminate.
Qed.

Theorem native_payload_labels_are_reserved : forall suffix,
  reserved_reflection_label ("^dynamic-text:" ++ suffix)%string = true /\
  reserved_reflection_label ("^dynamic-integer:" ++ suffix)%string = true /\
  reserved_reflection_label ("^dynamic-boolean:" ++ suffix)%string = true.
Proof. intros. repeat split; reflexivity. Qed.

Example signature_binding_alone_does_not_establish_representability :
  let entry := binding 0 0 "^dynamic-text:61"%string 0 0 [] in
  check_bindings [entry] = true /\ check_wire_bindings [entry] = false.
Proof. split; reflexivity. Qed.

End InstalledFltHeadCodec.

Print Assumptions InstalledFltHeadCodec.checked_entry_has_exact_inverses.
Print Assumptions InstalledFltHeadCodec.restore_projected_constructor.
Print Assumptions InstalledFltHeadCodec.project_restored_constructor.
Print Assumptions InstalledFltHeadCodec.resolved_plan_uses_the_same_exact_binding.
Print Assumptions InstalledFltHeadCodec.resolved_constructor_cannot_be_a_reserved_head.
