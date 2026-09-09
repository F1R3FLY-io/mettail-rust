(** Structural recipes for the existing installed-FLT request encoders in
    rholang-runtime/src/language_install.rs. These equations compose the
    existing target constructors, not another runtime encoder or evaluator.
    Source owners retain template validation, lexical resolution, work/resource
    checks, parser routing, provider authority and reply publication.

    Source hole IDs are u32. This model checks that range before reusing the
    signed integer constructor. Text stays literal structural data. Wire lists
    use ordinary child-derived metadata, never DDL's closed-list policy. *)

From Stdlib Require Import List String Bool PeanoNat ZArith Lia.
From RhoBridge Require Import RholangTargetConstruction RholangConstructionProtocol.
From RhoBridge Require RholangFltTransport.
Import ListNotations.
Module Foreign := RholangFltTransport.

Definition optional_category (category : option string) : Value :=
  match category with None => empty | Some category => text category end.

Definition checked_hole_integer (id : nat) : ConstructionResult :=
  if (Z.of_nat id <=? 4294967295)%Z then integer (Z.of_nat id)
  else ConstructionRejected IntegerOutOfRange.

Definition piece_recipe (piece : Foreign.PiecePayload) : ConstructionResult :=
  match piece with
  | Foreign.ExactGuestText payload => Constructed (list_value [text "text"; text payload])
  | Foreign.TelescopeHole id =>
    match checked_hole_integer id with
    | Constructed value => Constructed (list_value [text "hole"; value])
    | ConstructionRejected error => ConstructionRejected error
    end
  end.

Definition hole_recipe (hole : Foreign.NamedHole) : ConstructionResult :=
  match checked_hole_integer (Foreign.hole_id hole) with
  | Constructed value => Constructed (list_value
      [value; text (Foreign.hole_name hole); optional_category (Foreign.hole_category hole)])
  | ConstructionRejected error => ConstructionRejected error
  end.

(** Mathematical sequencing of fallible constructor results. The production
    refinement uses its existing explicit worklist and bounded output vectors;
    it must not recursively materialize this reference list on the host stack. *)
Fixpoint collect_recipe_values (results : list ConstructionResult) : ChildrenResult :=
  match results with
  | [] => ChildrenResolved []
  | ConstructionRejected error :: _ => ChildrenRejected error
  | Constructed value :: rest =>
    match collect_recipe_values rest with
    | ChildrenResolved values => ChildrenResolved (value :: values)
    | ChildrenRejected error => ChildrenRejected error
    end
  end.

Definition template_list_recipes (capture : Foreign.CapturedTemplate) : ChildrenResult :=
  match collect_recipe_values (map piece_recipe
    (map Foreign.piece_payload (Foreign.captured_pieces capture))) with
  | ChildrenRejected error => ChildrenRejected error
  | ChildrenResolved pieces =>
    match collect_recipe_values (map hole_recipe
      (map Foreign.hole_declaration (Foreign.captured_holes capture))) with
    | ChildrenRejected error => ChildrenRejected error
    | ChildrenResolved holes => ChildrenResolved [list_value pieces; list_value holes]
    end
  end.

(** Ordered inputs to the existing map constructor, not a new node sorter.
    Rust's wire_map delegates to ParMap, whose sorter canonicalizes BOTH keys
    and values. This neutral equation does not assert arbitrary host inputs
    are unchanged by that canonicalization. The current FLT source producer
    supplies BoundVar fills; fixed-point/string-key-order correspondence for
    those leaves and general canonical target emission remain adapter laws. *)
Definition fill_map (fills : list (string * Value)) : Value :=
  map_value (map (fun pair => (text (fst pair), snd pair)) fills).

Definition construct_fields (handle pieces holes : Value) (category : string)
    (fills : list (string * Value)) (reply : Value) : list Value :=
  [text "mettail-language-flt-construct/1"; handle; pieces; holes;
   text category; fill_map fills; reply].
Definition pattern_fields (handle pieces holes : Value) (category : string)
    (reply : Value) : list Value :=
  [text "mettail-language-flt-pattern/1"; handle; pieces; holes; text category; reply].

Definition construct_request_recipe (handle : Value) (capture : Foreign.CapturedTemplate)
    (fills : list (string * Value)) (reply : Value) : ConstructionResult :=
  if ordered_injection_keys (map fst fills) then
    match template_list_recipes capture with
    | ChildrenRejected error => ConstructionRejected error
    | ChildrenResolved [pieces; holes] => Constructed
        (list_value (construct_fields handle pieces holes (Foreign.root_category capture) fills reply))
    | ChildrenResolved _ => ConstructionRejected ChildArityMismatch
    end
  else ConstructionRejected InvalidBinderLayout.

Definition pattern_request_recipe (handle : Value) (capture : Foreign.CapturedTemplate)
    (reply : Value) : ConstructionResult :=
  match template_list_recipes capture with
  | ChildrenRejected error => ConstructionRejected error
  | ChildrenResolved [pieces; holes] => Constructed
      (list_value (pattern_fields handle pieces holes (Foreign.root_category capture) reply))
  | ChildrenResolved _ => ConstructionRejected ChildArityMismatch
  end.

Theorem optional_category_preserves_absence :
  optional_category None <> optional_category (Some EmptyString).
Proof. discriminate. Qed.

Theorem text_piece_preserves_literal_payload : forall payload,
  piece_recipe (Foreign.ExactGuestText payload) =
    Constructed (list_value [text "text"; text payload]).
Proof. reflexivity. Qed.

Theorem hole_integer_reuses_checked_constructor : forall id value,
  checked_hole_integer id = Constructed value ->
  (Z.of_nat id <= 4294967295)%Z /\ integer (Z.of_nat id) = Constructed value.
Proof.
  intros id value H; unfold checked_hole_integer in H.
  destruct (Z.of_nat id <=? 4294967295)%Z eqn:E; try discriminate.
  split; [now apply Z.leb_le|exact H].
Qed.

Theorem oversized_hole_id_rejects : forall id,
  (4294967295 < Z.of_nat id)%Z ->
  checked_hole_integer id = ConstructionRejected IntegerOutOfRange.
Proof. intros; unfold checked_hole_integer. apply Z.leb_gt in H; now rewrite H. Qed.

Theorem collection_preserves_each_constructor_result : forall results values,
  collect_recipe_values results = ChildrenResolved values ->
  results = map Constructed values.
Proof.
  induction results as [|result rest IH]; intros values H.
  - inversion H; reflexivity.
  - destruct result; cbn in H; try discriminate.
    destruct (collect_recipe_values rest) eqn:E; try discriminate.
    inversion H; subst. cbn; now rewrite (IH _ eq_refl).
Qed.

Theorem template_success_retains_exact_component_rosters : forall capture lists,
  template_list_recipes capture = ChildrenResolved lists ->
  exists pieces holes,
    lists = [list_value pieces; list_value holes] /\
    map piece_recipe (map Foreign.piece_payload (Foreign.captured_pieces capture)) =
      map Constructed pieces /\
    map hole_recipe (map Foreign.hole_declaration (Foreign.captured_holes capture)) =
      map Constructed holes /\
    List.length pieces = List.length (Foreign.captured_pieces capture) /\
    List.length holes = List.length (Foreign.captured_holes capture).
Proof.
  intros capture lists H; unfold template_list_recipes in H.
  destruct (collect_recipe_values (map piece_recipe
    (map Foreign.piece_payload (Foreign.captured_pieces capture)))) as [pieces|error] eqn:P;
    try discriminate.
  destruct (collect_recipe_values (map hole_recipe
    (map Foreign.hole_declaration (Foreign.captured_holes capture)))) as [holes|error] eqn:D;
    try discriminate.
  inversion H; subst.
  apply collection_preserves_each_constructor_result in P.
  apply collection_preserves_each_constructor_result in D.
  pose proof (f_equal (@List.length ConstructionResult) P) as LP.
  pose proof (f_equal (@List.length ConstructionResult) D) as LD.
  repeat rewrite length_map in LP, LD.
  exists pieces, holes; repeat split; auto.
Qed.

Theorem repeated_piece_results_remain_repeated : forall piece value,
  piece_recipe piece = Constructed value ->
  collect_recipe_values (map piece_recipe [piece; piece]) = ChildrenResolved [value; value].
Proof. intros; cbn [map]; rewrite H; reflexivity. Qed.

Theorem first_failed_component_is_not_an_empty_value : forall error rest,
  collect_recipe_values (ConstructionRejected error :: rest) = ChildrenRejected error.
Proof. reflexivity. Qed.

Theorem construction_fields_keep_exact_service_roles : forall handle pieces holes category fills reply,
  List.length (construct_fields handle pieces holes category fills reply) = 7 /\
  nth_error (construct_fields handle pieces holes category fills reply) 1 = Some handle /\
  nth_error (construct_fields handle pieces holes category fills reply) 2 = Some pieces /\
  nth_error (construct_fields handle pieces holes category fills reply) 3 = Some holes /\
  nth_error (construct_fields handle pieces holes category fills reply) 4 = Some (text category) /\
  nth_error (construct_fields handle pieces holes category fills reply) 5 = Some (fill_map fills) /\
  nth_error (construct_fields handle pieces holes category fills reply) 6 = Some reply.
Proof. intros; repeat split; reflexivity. Qed.

Theorem pattern_fields_keep_exact_service_roles : forall handle pieces holes category reply,
  List.length (pattern_fields handle pieces holes category reply) = 6 /\
  nth_error (pattern_fields handle pieces holes category reply) 1 = Some handle /\
  nth_error (pattern_fields handle pieces holes category reply) 2 = Some pieces /\
  nth_error (pattern_fields handle pieces holes category reply) 3 = Some holes /\
  nth_error (pattern_fields handle pieces holes category reply) 4 = Some (text category) /\
  nth_error (pattern_fields handle pieces holes category reply) 5 = Some reply.
Proof. intros; repeat split; reflexivity. Qed.

Theorem construct_recipe_uses_existing_list_operation :
  forall handle capture fills reply pieces holes,
  ordered_injection_keys (map fst fills) = true ->
  template_list_recipes capture = ChildrenResolved [pieces; holes] ->
  construct_request_recipe handle capture fills reply =
    interpret ListOp (construct_fields handle pieces holes (Foreign.root_category capture) fills reply).
Proof. intros; unfold construct_request_recipe; now rewrite H, H0. Qed.

Theorem pattern_recipe_uses_existing_list_operation : forall handle capture reply pieces holes,
  template_list_recipes capture = ChildrenResolved [pieces; holes] ->
  pattern_request_recipe handle capture reply =
    interpret ListOp (pattern_fields handle pieces holes (Foreign.root_category capture) reply).
Proof. intros; unfold pattern_request_recipe; now rewrite H. Qed.

Theorem successful_construction_fills_have_unique_ordered_keys : forall handle capture fills reply value,
  construct_request_recipe handle capture fills reply = Constructed value ->
  ordered_injection_keys (map fst fills) = true /\ NoDup (map fst fills).
Proof.
  intros; unfold construct_request_recipe in H.
  destruct (ordered_injection_keys (map fst fills)) eqn:E; try discriminate.
  split; [reflexivity|now apply injection_key_check_excludes_duplicates].
Qed.

(** The existing wire helpers fold metadata from the left. The algebra's
    right fold has the same exact bit-vector result, not merely the same set
    of free indices. In particular trailing false entries are not trimmed. *)
Lemma union_bits_associative : forall first second third,
  union_bits (union_bits first second) third = union_bits first (union_bits second third).
Proof.
  induction first as [|a first IH]; intros [|b second] [|c third]; cbn;
    try reflexivity. now rewrite IH, orb_assoc.
Qed.

Lemma join_summary_associative : forall first second third,
  join_summary (join_summary first second) third = join_summary first (join_summary second third).
Proof.
  intros [a x] [b y] [c z]; unfold join_summary; cbn.
  now rewrite union_bits_associative, orb_assoc.
Qed.

Lemma join_summary_right_identity : forall summary,
  join_summary summary closed_summary = summary.
Proof.
  intros [bits flag]; unfold join_summary, closed_summary; cbn.
  assert (union_bits bits [] = bits) as E by (destruct bits; reflexivity).
  rewrite E, orb_false_r; reflexivity.
Qed.

Theorem wire_metadata_left_fold_matches_algebra : forall children initial,
  fold_left (fun summary child => join_summary summary (summary_of child)) children initial =
    join_summary initial (children_summary children).
Proof.
  induction children as [|child rest IH]; intros initial; cbn.
  - symmetry; apply join_summary_right_identity.
  - rewrite IH; apply join_summary_associative.
Qed.

Corollary wire_list_metadata_uses_every_child : forall children,
  fold_left (fun summary child => join_summary summary (summary_of child)) children closed_summary =
    summary_of (list_value children).
Proof.
  intros; rewrite wire_metadata_left_fold_matches_algebra.
  change (join_summary closed_summary (children_summary children) = children_summary children).
  destruct (children_summary children) as [bits flag]. reflexivity.
Qed.

Theorem wire_map_metadata_left_fold_matches_algebra : forall pairs initial,
  fold_left (fun summary pair => join_summary summary
    (join_summary (summary_of (fst pair)) (summary_of (snd pair)))) pairs initial =
    join_summary initial (children_summary (pair_children pairs)).
Proof.
  induction pairs as [|[key value] rest IH]; intros initial.
  - cbn; symmetry; apply join_summary_right_identity.
  - cbn [fold_left pair_children flat_map app fst snd children_summary].
    rewrite IH. now repeat rewrite join_summary_associative.
Qed.

Theorem fill_map_retains_exact_pairs_and_metadata : forall fills,
  heads_of (fill_map fills) = [MakeHead MapHead
    (pair_children (map (fun pair => (text (fst pair), snd pair)) fills))] /\
  summary_of (fill_map fills) = children_summary
    (pair_children (map (fun pair => (text (fst pair), snd pair)) fills)).
Proof. intros; split; reflexivity. Qed.

Print Assumptions optional_category_preserves_absence.
Print Assumptions text_piece_preserves_literal_payload.
Print Assumptions hole_integer_reuses_checked_constructor.
Print Assumptions oversized_hole_id_rejects.
Print Assumptions collection_preserves_each_constructor_result.
Print Assumptions template_success_retains_exact_component_rosters.
Print Assumptions repeated_piece_results_remain_repeated.
Print Assumptions first_failed_component_is_not_an_empty_value.
Print Assumptions construction_fields_keep_exact_service_roles.
Print Assumptions pattern_fields_keep_exact_service_roles.
Print Assumptions construct_recipe_uses_existing_list_operation.
Print Assumptions pattern_recipe_uses_existing_list_operation.
Print Assumptions successful_construction_fills_have_unique_ordered_keys.
Print Assumptions union_bits_associative.
Print Assumptions join_summary_associative.
Print Assumptions join_summary_right_identity.
Print Assumptions wire_metadata_left_fold_matches_algebra.
Print Assumptions wire_list_metadata_uses_every_child.
Print Assumptions wire_map_metadata_left_fold_matches_algebra.
Print Assumptions fill_map_retains_exact_pairs_and_metadata.
