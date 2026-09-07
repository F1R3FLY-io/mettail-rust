(** * Structural FLT term conversion, before backend arena allocation

    These are reference conversions over finite occurrence witnesses, using
    the existing [SelectedOccurrencePlan] tree rather than a new evaluator.
    A witness is proof data only; production traverses borrowed terms with an
    explicit work stack.  Constructor labels and native payloads are different
    cases, and every node is checked under its parent's exact declared sort.

    [text_valid] is a supplied byte predicate.  Both directions apply the same
    predicate to identical bytes, so the laws hold for any such predicate; the
    Rust instantiation uses UTF-8 validation.  No correctness axiom about a
    UTF-8 implementation is needed for byte preservation.  Likewise an exact
    owner string checks structural identity, not capability authority.

    The theorems concern these structural observations, not arbitrary Par or
    protobuf bytes.  Framing inspection, borrowed-source unfolding, bounded
    iterative execution and egraph coordinate realization must refine this
    reference conversion before the production adapter is complete. *)

From Stdlib Require Import List Strings.String Arith.PeanoNat ZArith Bool.Bool.
From RuntimeGrammar Require Import NativeReflectionCodec InstalledFltHeadCodec.
From PrattailWpdaRuntime Require Import SelectedOccurrencePlan.
Import ListNotations.

Module InstalledFltTermCodec.
Module Payload := NativeReflectionCodec.NativeReflectionCodec.
Module Head := InstalledFltHeadCodec.InstalledFltHeadCodec.

Inductive NativeKind := TextKind | IntegerKind | BooleanKind.

Definition native_kind_eq_dec : forall first second : NativeKind,
  {first = second} + {first <> second}.
Proof. decide equality. Defined.

Inductive NativeValue :=
| TextValue (bytes : string)
| IntegerValue (value : Z)
| BooleanValue (value : bool).

Inductive ReflectedNative :=
| TextPayload (hexadecimal : string)
| IntegerPayload (decimal : string)
| BooleanPayload (text : string).

Definition native_kind value :=
  match value with
  | TextValue _ => TextKind
  | IntegerValue _ => IntegerKind
  | BooleanValue _ => BooleanKind
  end.

Section NativeCodec.
Variable text_valid : string -> bool.

Definition encode_native value : option ReflectedNative :=
  match value with
  | TextValue bytes =>
      if text_valid bytes then Some (TextPayload (Payload.encode_hex bytes)) else None
  | IntegerValue value =>
      if Payload.in_i128 value then Some (IntegerPayload (Payload.encode_integer value)) else None
  | BooleanValue value => Some (BooleanPayload (Payload.encode_boolean value))
  end.

Definition decode_native payload : option NativeValue :=
  match payload with
  | TextPayload text =>
      match Payload.decode_hex text with
      | Some bytes => if text_valid bytes then Some (TextValue bytes) else None
      | None => None
      end
  | IntegerPayload text => option_map IntegerValue (Payload.decode_integer text)
  | BooleanPayload text => option_map BooleanValue (Payload.decode_boolean text)
  end.

Lemma native_decode_encode : forall value payload,
  encode_native value = Some payload -> decode_native payload = Some value.
Proof.
  intros [bytes|value|value] payload H; cbn [encode_native] in H.
  - destruct (text_valid bytes) eqn:E; try discriminate.
    inversion H; subst. cbn [decode_native]. rewrite Payload.decode_encoded_bytes, E. reflexivity.
  - destruct (Payload.in_i128 value) eqn:E; try discriminate.
    inversion H; subst. cbn [decode_native].
    rewrite (Payload.decode_encoded_integer value E). reflexivity.
  - inversion H; subst. cbn [decode_native]. rewrite Payload.decode_encoded_boolean. reflexivity.
Qed.

Lemma native_encode_decode : forall payload value,
  decode_native payload = Some value -> encode_native value = Some payload.
Proof.
  intros [text|text|text] value H; cbn [decode_native] in H.
  - destruct (Payload.decode_hex text) as [bytes|] eqn:E; try discriminate.
    destruct (text_valid bytes) eqn:Evalid; try discriminate.
    inversion H; subst. cbn [encode_native].
    rewrite Evalid, (Payload.encode_decoded_bytes text bytes E). reflexivity.
  - destruct (Payload.decode_integer text) as [integer|] eqn:E; try discriminate.
    inversion H; subst. cbn [encode_native].
    destruct (Payload.encode_decoded_integer text integer E) as [Etext Ebound].
    rewrite Ebound, Etext. reflexivity.
  - destruct (Payload.decode_boolean text) as [boolean|] eqn:E; try discriminate.
    inversion H; subst. cbn [encode_native].
    rewrite (Payload.encode_decoded_boolean text boolean E). reflexivity.
Qed.
End NativeCodec.

Record ReflectedLeaf := reflected_leaf {
  leaf_owner : string;
  leaf_payload : ReflectedNative
}.

Definition ReflectedTerm := @selected_tree ReflectedLeaf (string * string).
Definition ReflectedChildren := @selected_children ReflectedLeaf (string * string).
Definition SemanticTerm := @selected_tree (nat * NativeValue) (nat * nat).
Definition SemanticChildren := @selected_children (nat * NativeValue) (nat * nat).

Section InstalledCodec.
Variable table : list Head.ConstructorBinding.
Variable owner : string.
Variable carriers : nat -> option NativeKind.
Variable text_valid : string -> bool.

Definition carrier_admits sort value :=
  match carriers sort with
  | Some kind => if native_kind_eq_dec kind (native_kind value) then true else false
  | None => false
  end.

Definition project_leaf expected leaf : option (nat * NativeValue) :=
  if String.eqb (leaf_owner leaf) owner then
    match decode_native text_valid (leaf_payload leaf) with
    | Some value => if carrier_admits expected value then Some (expected, value) else None
    | None => None
    end
  else None.

Definition restore_leaf expected (leaf : nat * NativeValue) : option ReflectedLeaf :=
  let '(sort, value) := leaf in
  if Nat.eqb sort expected && carrier_admits expected value then
    option_map (reflected_leaf owner) (encode_native text_valid value)
  else None.

Lemma restore_projected_leaf : forall expected leaf output,
  project_leaf expected leaf = Some output -> restore_leaf expected output = Some leaf.
Proof.
  intros expected [actual payload] output H. unfold project_leaf in H; cbn in H.
  destruct (String.eqb actual owner) eqn:Eowner; try discriminate.
  destruct (decode_native text_valid payload) as [value|] eqn:Epayload; try discriminate.
  destruct (carrier_admits expected value) eqn:Ecarrier; try discriminate.
  inversion H; subst output. unfold restore_leaf.
  rewrite Nat.eqb_refl, Ecarrier. cbn.
  rewrite (native_encode_decode text_valid payload value Epayload).
  apply String.eqb_eq in Eowner. subst actual. reflexivity.
Qed.

Lemma project_restored_leaf : forall expected leaf output,
  restore_leaf expected leaf = Some output -> project_leaf expected output = Some leaf.
Proof.
  intros expected [sort value] output H. unfold restore_leaf in H.
  destruct (Nat.eqb sort expected && carrier_admits expected value) eqn:Echecks; try discriminate.
  destruct (encode_native text_valid value) as [payload|] eqn:Epayload; try discriminate.
  inversion H; subst output.
  apply andb_true_iff in Echecks. destruct Echecks as [Esort Ecarrier].
  apply Nat.eqb_eq in Esort. subst sort.
  unfold project_leaf; cbn. rewrite String.eqb_refl.
  rewrite (native_decode_encode text_valid value payload Epayload), Ecarrier. reflexivity.
Qed.

Fixpoint project_tree expected (tree : ReflectedTerm) : option SemanticTerm :=
  match tree with
  | SelectedLeaf leaf => option_map SelectedLeaf (project_leaf expected leaf)
  | SelectedBranch (actual, label) children =>
      if String.eqb actual owner then
        match Head.reflected_lookup table expected label with
        | Some entry =>
            option_map (SelectedBranch (expected, Head.semantic_constructor entry))
              (project_children (Head.semantic_domain entry) children)
        | None => None
        end
      else None
  end
with project_children domain (children : ReflectedChildren) : option SemanticChildren :=
  match domain, children with
  | nil, NoChildren => Some NoChildren
  | sort :: sorts, MoreChildren child rest =>
      match project_tree sort child, project_children sorts rest with
      | Some first, Some later => Some (MoreChildren first later)
      | _, _ => None
      end
  | _, _ => None
  end.

Fixpoint restore_tree expected (tree : SemanticTerm) : option ReflectedTerm :=
  match tree with
  | SelectedLeaf leaf => option_map SelectedLeaf (restore_leaf expected leaf)
  | SelectedBranch (sort, constructor) children =>
      if Nat.eqb sort expected then
        match Head.semantic_lookup table constructor with
        | Some entry =>
            if Nat.eqb (Head.semantic_result entry) expected then
              option_map (SelectedBranch (owner, Head.reflected_label entry))
                (restore_children (Head.semantic_domain entry) children)
            else None
        | None => None
        end
      else None
  end
with restore_children domain (children : SemanticChildren) : option ReflectedChildren :=
  match domain, children with
  | nil, NoChildren => Some NoChildren
  | sort :: sorts, MoreChildren child rest =>
      match restore_tree sort child, restore_children sorts rest with
      | Some first, Some later => Some (MoreChildren first later)
      | _, _ => None
      end
  | _, _ => None
  end.

Theorem projected_occurrences_restore_exactly : Head.check_bindings table = true ->
  (forall tree expected output,
    project_tree expected tree = Some output -> restore_tree expected output = Some tree) /\
  (forall children domain output,
    project_children domain children = Some output -> restore_children domain output = Some children).
Proof.
  intro Hchecked. apply selected_mutual.
  - intros leaf expected output H. cbn [project_tree] in H.
    destruct (project_leaf expected leaf) as [value|] eqn:E; try discriminate.
    inversion H; subst output. cbn [restore_tree].
    rewrite (restore_projected_leaf expected leaf value E). reflexivity.
  - intros [actual label] children IH expected output H. cbn [project_tree] in H.
    destruct (String.eqb actual owner) eqn:Eowner; try discriminate.
    destruct (Head.reflected_lookup table expected label) as [entry|] eqn:Ebinding;
      try discriminate.
    destruct (project_children (Head.semantic_domain entry) children) as [values|] eqn:Echildren;
      try discriminate.
    inversion H; subst output. cbn [restore_tree]. rewrite Nat.eqb_refl.
    pose proof (Head.reflected_lookup_sound table expected label entry Ebinding)
      as [Hmember [Hsort Hlabel]].
    destruct (Head.checked_entry_has_exact_inverses table entry Hchecked Hmember) as [_ Ereverse].
    rewrite Ereverse, Hsort, Nat.eqb_refl, (IH _ _ Echildren), Hlabel.
    apply String.eqb_eq in Eowner. subst actual. reflexivity.
  - intros [|sort sorts] output H; cbn [project_children] in H; try discriminate.
    inversion H; reflexivity.
  - intros tree IHtree rest IHrest [|sort sorts] output H; cbn [project_children] in H;
      try discriminate.
    destruct (project_tree sort tree) as [value|] eqn:Etree; try discriminate.
    destruct (project_children sorts rest) as [values|] eqn:Erest; try discriminate.
    inversion H; subst output. cbn [restore_children].
    rewrite (IHtree _ _ Etree), (IHrest _ _ Erest). reflexivity.
Qed.

Theorem restored_occurrences_project_exactly : Head.check_bindings table = true ->
  (forall tree expected output,
    restore_tree expected tree = Some output -> project_tree expected output = Some tree) /\
  (forall children domain output,
    restore_children domain children = Some output -> project_children domain output = Some children).
Proof.
  intro Hchecked. apply selected_mutual.
  - intros leaf expected output H. cbn [restore_tree] in H.
    destruct (restore_leaf expected leaf) as [value|] eqn:E; try discriminate.
    inversion H; subst output. cbn [project_tree].
    rewrite (project_restored_leaf expected leaf value E). reflexivity.
  - intros [sort constructor] children IH expected output H. cbn [restore_tree] in H.
    destruct (Nat.eqb sort expected) eqn:Esort; try discriminate.
    destruct (Head.semantic_lookup table constructor) as [entry|] eqn:Ebinding; try discriminate.
    destruct (Nat.eqb (Head.semantic_result entry) expected) eqn:Eresult; try discriminate.
    destruct (restore_children (Head.semantic_domain entry) children) as [values|] eqn:Echildren;
      try discriminate.
    inversion H; subst output. cbn [project_tree]. rewrite String.eqb_refl.
    pose proof (Head.semantic_lookup_sound table constructor entry Ebinding)
      as [Hmember Hconstructor].
    destruct (Head.checked_entry_has_exact_inverses table entry Hchecked Hmember) as [Ereverse _].
    apply Nat.eqb_eq in Esort. apply Nat.eqb_eq in Eresult.
    rewrite <- Eresult, Ereverse, (IH _ _ Echildren), Hconstructor, Eresult, <- Esort.
    reflexivity.
  - intros [|sort sorts] output H; cbn [restore_children] in H; try discriminate.
    inversion H; reflexivity.
  - intros tree IHtree rest IHrest [|sort sorts] output H; cbn [restore_children] in H;
      try discriminate.
    destruct (restore_tree sort tree) as [value|] eqn:Etree; try discriminate.
    destruct (restore_children sorts rest) as [values|] eqn:Erest; try discriminate.
    inversion H; subst output. cbn [project_children].
    rewrite (IHtree _ _ Etree), (IHrest _ _ Erest). reflexivity.
Qed.

Corollary projection_does_not_identify_distinct_structural_terms :
  forall first second expected output,
  Head.check_bindings table = true ->
  project_tree expected first = Some output ->
  project_tree expected second = Some output -> first = second.
Proof.
  intros first second expected output Hchecked Hfirst Hsecond.
  pose proof (proj1 (projected_occurrences_restore_exactly Hchecked)
    first expected output Hfirst) as Efirst.
  pose proof (proj1 (projected_occurrences_restore_exactly Hchecked)
    second expected output Hsecond) as Esecond.
  rewrite Efirst in Esecond. now inversion Esecond.
Qed.
End InstalledCodec.

(** Concrete witnesses use deliberately unrelated grammar and semantic IDs.
    Both a native Boolean and an ordinary constructor inhabit sort 3 without
    being identified.  The byte predicate accepts the ASCII text in this test;
    the general theorem above is independent of that predicate's choice. *)
Definition mixed_bindings :=
  [Head.binding 13 41 "Apply"%string 7 19 [2; 4; 3; 3];
   Head.binding 14 55 "TrueCtor"%string 8 3 []].

Definition mixed_carriers sort :=
  match sort with
  | 2 => Some TextKind
  | 3 => Some BooleanKind
  | 4 => Some IntegerKind
  | _ => None
  end.

Definition mixed_tail : ReflectedChildren :=
  MoreChildren (SelectedLeaf (reflected_leaf "owner"%string (IntegerPayload "-3"%string)))
    (MoreChildren (SelectedLeaf (reflected_leaf "owner"%string (BooleanPayload "true"%string)))
      (MoreChildren (SelectedBranch ("owner"%string, "TrueCtor"%string) NoChildren) NoChildren)).

Definition mixed_input : ReflectedTerm :=
  SelectedBranch ("owner"%string, "Apply"%string)
    (MoreChildren (SelectedLeaf (reflected_leaf "owner"%string (TextPayload "41"%string))) mixed_tail).

Definition mixed_output : SemanticTerm :=
  SelectedBranch (19, 7)
    (MoreChildren (SelectedLeaf (2, TextValue "A"%string))
      (MoreChildren (SelectedLeaf (4, IntegerValue (-3)%Z))
        (MoreChildren (SelectedLeaf (3, BooleanValue true))
          (MoreChildren (SelectedBranch (3, 8) NoChildren) NoChildren)))).

Example mixed_binding_check_succeeds : Head.check_bindings mixed_bindings = true.
Proof. reflexivity. Qed.

Example mixed_native_constructor_projection :
  project_tree mixed_bindings "owner"%string mixed_carriers (fun _ => true) 19 mixed_input =
    Some mixed_output.
Proof. reflexivity. Qed.

Example mixed_native_constructor_restoration :
  restore_tree mixed_bindings "owner"%string mixed_carriers (fun _ => true) 19 mixed_output =
    Some mixed_input.
Proof. reflexivity. Qed.

Example equal_arity_wrong_child_sort_refused :
  project_tree mixed_bindings "owner"%string mixed_carriers (fun _ => true) 19
    (SelectedBranch ("owner"%string, "Apply"%string)
      (MoreChildren (SelectedLeaf (reflected_leaf "owner"%string
        (BooleanPayload "true"%string))) mixed_tail)) = None.
Proof. reflexivity. Qed.

Example foreign_owner_leaf_refused :
  project_tree mixed_bindings "owner"%string mixed_carriers (fun _ => true) 3
    (SelectedLeaf (reflected_leaf "foreign"%string (BooleanPayload "true"%string))) = None.
Proof. reflexivity. Qed.

End InstalledFltTermCodec.

Print Assumptions InstalledFltTermCodec.projected_occurrences_restore_exactly.
Print Assumptions InstalledFltTermCodec.restored_occurrences_project_exactly.
Print Assumptions InstalledFltTermCodec.projection_does_not_identify_distinct_structural_terms.
