From Stdlib Require Import Bool List String Arith.PeanoNat Lia.
Import ListNotations.

(** A prefix route is indexed by the requested category, the *lexed token*
    that opens it, and the grammatical route identity. No character-level or
    opener/closer shape is assumed: ["("], ["["], and ["{|"] are merely
    different token strings. The runtime action and semiring weight attached
    to a route are intentionally opaque here; source correspondence must show
    that emission reuses each original action and weight unchanged. *)
Record Route := route {
  result_category : nat;
  opening_token : string;
  grammatical_route : nat;
  action_identity : nat;
  weight_identity : nat
}.

Definition eligible (category : nat) (opener : string) (candidate : Route) : bool :=
  Nat.eqb (result_category candidate) category &&
  String.eqb (opening_token candidate) opener.

Definition same_route (left right : Route) : bool :=
  Nat.eqb (result_category left) (result_category right) &&
  String.eqb (opening_token left) (opening_token right) &&
  Nat.eqb (grammatical_route left) (grammatical_route right).

(** A special collection projection and an ordinary cross-category projection
    can name the same grammatical route while carrying different continuation
    actions. In that exact case the special action is the authoritative one;
    all other ordinary branches are retained in source order. Grouping,
    binders, and collection constructors have distinct route identities. *)
Definition shadowed_by_special (special : list Route) (candidate : Route) : bool :=
  existsb (fun route => same_route route candidate) special.

Definition prepare_opener (category : nat) (opener : string)
    (special ordinary : list Route) : list Route :=
  filter (eligible category opener) special ++
  filter
    (fun candidate => eligible category opener candidate &&
                      negb (shadowed_by_special special candidate))
    ordinary.

Lemma same_route_reflexive : forall candidate,
  same_route candidate candidate = true.
Proof.
  intros [category opener identity action weight]; unfold same_route; simpl.
  repeat rewrite Nat.eqb_refl; rewrite String.eqb_refl; reflexivity.
Qed.

Lemma same_route_preserves_eligibility :
  forall category opener left right,
    same_route left right = true ->
    eligible category opener right = true ->
    eligible category opener left = true.
Proof.
  intros category opener [left_category left_opener left_id left_action left_weight]
    [right_category right_opener right_id right_action right_weight] same admitted.
  unfold same_route, eligible in *; simpl in *.
  repeat rewrite andb_true_iff in same.
  destruct same as [[same_category same_opener] _].
  apply Nat.eqb_eq in same_category.
  apply String.eqb_eq in same_opener.
  subst left_category left_opener.
  exact admitted.
Qed.

(** The emitter may choose a specialized continuation for an equivalent
    collection projection, but cannot manufacture an unlisted route. Since a
    retained route is the original record, its action and weight identities
    are preserved without a reconstruction argument. *)
Theorem every_emitted_route_has_an_original :
  forall category opener special ordinary emitted,
    In emitted (prepare_opener category opener special ordinary) ->
    (In emitted special \/ In emitted ordinary) /\
    eligible category opener emitted = true.
Proof.
  intros category opener special ordinary emitted present.
  unfold prepare_opener in present.
  apply in_app_or in present.
  destruct present as [present | present].
  - apply filter_In in present as [origin admitted].
    split; [left; exact origin | exact admitted].
  - apply filter_In in present as [origin admitted].
    apply andb_true_iff in admitted as [eligible_now _].
    split; [right; exact origin | exact eligible_now].
Qed.

Theorem special_routes_keep_their_declaration_order :
  forall category opener special ordinary,
    firstn (List.length (filter (eligible category opener) special))
      (prepare_opener category opener special ordinary) =
    filter (eligible category opener) special.
Proof.
  intros; unfold prepare_opener.
  rewrite firstn_app.
  rewrite firstn_all, Nat.sub_diag.
  simpl; rewrite app_nil_r; reflexivity.
Qed.

(** Filtering may remove an ordinary projection superseded by its specialized
    continuation, but it cannot reorder the surviving ordinary routes. *)
Inductive in_order_subsequence {A : Type} : list A -> list A -> Prop :=
| subsequence_empty : forall source, in_order_subsequence [] source
| subsequence_keep : forall x kept source,
    in_order_subsequence kept source ->
    in_order_subsequence (x :: kept) (x :: source)
| subsequence_drop : forall x kept source,
    in_order_subsequence kept source ->
    in_order_subsequence kept (x :: source).

Lemma filter_keeps_relative_order : forall (A : Type) (predicate : A -> bool) source,
  in_order_subsequence (filter predicate source) source.
Proof.
  intros A predicate source; induction source as [| head tail induction_hypothesis].
  - constructor.
  - simpl; destruct (predicate head) eqn:accepted.
    + constructor; exact induction_hypothesis.
    + apply subsequence_drop; exact induction_hypothesis.
Qed.

Theorem retained_ordinary_routes_keep_their_declaration_order :
  forall category opener special ordinary,
    in_order_subsequence
      (filter
         (fun candidate => eligible category opener candidate &&
                           negb (shadowed_by_special special candidate))
         ordinary)
      ordinary.
Proof.
  intros; apply filter_keeps_relative_order.
Qed.

Theorem every_special_route_is_preserved :
  forall category opener special ordinary candidate,
    In candidate special -> eligible category opener candidate = true ->
    In candidate (prepare_opener category opener special ordinary).
Proof.
  intros category opener special ordinary candidate declared admitted.
  unfold prepare_opener; apply in_or_app; left.
  apply filter_In; split; assumption.
Qed.

Theorem every_ordinary_route_has_a_retained_equivalent :
  forall category opener special ordinary candidate,
    In candidate ordinary -> eligible category opener candidate = true ->
    exists kept,
      In kept (prepare_opener category opener special ordinary) /\
      same_route kept candidate = true.
Proof.
  intros category opener special ordinary candidate declared admitted.
  destruct (shadowed_by_special special candidate) eqn:shadowed.
  - unfold shadowed_by_special in shadowed.
    apply existsb_exists in shadowed as [kept [special_member equivalent]].
    exists kept; split; [|exact equivalent].
    apply every_special_route_is_preserved; auto.
    eapply same_route_preserves_eligibility; eauto.
  - exists candidate; split.
    + unfold prepare_opener; apply in_or_app; right.
      apply filter_In; split; auto.
      rewrite admitted, shadowed; reflexivity.
    + apply same_route_reflexive.
Qed.

Theorem ordinary_route_is_removed_only_for_an_existing_special_equivalent :
  forall category opener special candidate,
    eligible category opener candidate = true ->
    ~ In candidate
        (filter
          (fun route => eligible category opener route &&
                        negb (shadowed_by_special special route))
          [candidate]) ->
    exists kept, In kept special /\ same_route kept candidate = true.
Proof.
  intros category opener special candidate admitted missing.
  destruct (shadowed_by_special special candidate) eqn:shadowed.
  - unfold shadowed_by_special in shadowed.
    apply existsb_exists in shadowed as [kept [present same]].
    exists kept; split; assumption.
  - exfalso; apply missing.
    apply filter_In; split; [simpl; auto|].
    rewrite admitted, shadowed; reflexivity.
Qed.

(** Collection-projection specialization is justified by an actual declared
    source collection route with the same *lexer token*. The close delimiter
    and the spelling of the complete delimiter are irrelevant to admission. *)
Definition source_has_collection_opener
    (source_category : nat) (opener : string) (collections : list Route) : bool :=
  existsb (eligible source_category opener) collections.

Theorem source_projection_is_specialized_iff_a_source_route_exists :
  forall source_category opener collections,
    source_has_collection_opener source_category opener collections = true <->
    exists route,
      In route collections /\ eligible source_category opener route = true.
Proof.
  intros source_category opener collections.
  unfold source_has_collection_opener.
  apply existsb_exists.
Qed.

(** The owned and generated engines must dispatch the *same* admitted route
    list. A singleton retains its direct action; a collision is one flat fork
    over numbered original routes, never a fork of forks. The numbering is
    performed only after specialization removes exact duplicate routes. *)
Fixpoint number_routes (base : nat) (routes : list Route) : list (nat * Route) :=
  match routes with
  | [] => []
  | candidate :: rest => (base, candidate) :: number_routes (S base) rest
  end.

Inductive PrefixDispatch :=
| NoPrefixRoute
| SingletonPrefixRoute (candidate : Route)
| FlatPrefixFork (branches : list (nat * Route)).

Definition dispatch_routes (routes : list Route) : PrefixDispatch :=
  match routes with
  | [] => NoPrefixRoute
  | [candidate] => SingletonPrefixRoute candidate
  | _ :: _ :: _ => FlatPrefixFork (number_routes 0 routes)
  end.

Definition dispatched_originals (dispatch : PrefixDispatch) : list Route :=
  match dispatch with
  | NoPrefixRoute => []
  | SingletonPrefixRoute candidate => [candidate]
  | FlatPrefixFork branches => map snd branches
  end.

Lemma numbered_routes_preserve_originals :
  forall base routes, map snd (number_routes base routes) = routes.
Proof.
  intros base routes; revert base.
  induction routes as [| candidate rest IH]; intros base; simpl.
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

Theorem flat_dispatch_conserves_exactly_the_admitted_routes :
  forall routes, dispatched_originals (dispatch_routes routes) = routes.
Proof.
  intros [| first [| second rest]]; simpl; try reflexivity.
  rewrite numbered_routes_preserve_originals; reflexivity.
Qed.

Lemma numbered_routes_preserve_position :
  forall routes base position,
    nth_error (number_routes base routes) position =
    option_map (fun candidate => (base + position, candidate))
      (nth_error routes position).
Proof.
  induction routes as [| candidate rest IH]; intros base position.
  - destruct position; reflexivity.
  - destruct position as [| position].
    + simpl; rewrite Nat.add_0_r; reflexivity.
    + simpl; rewrite (IH (S base) position).
      replace (S base + position) with (base + S position) by lia.
      reflexivity.
Qed.

(** A branch's action and weight remain those of the original route at that
    ordinal: [number_routes] pairs the index with the original record rather
    than rebuilding a route from a token or delimiter spelling. *)
Theorem flat_fork_preserves_action_weight_and_ordinal :
  forall routes position candidate,
    nth_error routes position = Some candidate ->
    nth_error (number_routes 0 routes) position = Some (position, candidate).
Proof.
  intros routes position candidate found.
  rewrite numbered_routes_preserve_position, found.
  simpl; reflexivity.
Qed.

(** The routing index is published only after its logical route-slot charge
    succeeds. Refusal does not publish a truncated fork. The Rust constructor
    additionally charges map and key slots before their allocations. *)
Definition checked_dispatch (available_slots : nat) (routes : list Route) :
    option PrefixDispatch :=
  if Nat.leb (List.length routes) available_slots
  then Some (dispatch_routes routes)
  else None.

Theorem admitted_dispatch_preserves_all_routes :
  forall available_slots routes admitted,
    checked_dispatch available_slots routes = Some admitted ->
    dispatched_originals admitted = routes.
Proof.
  intros available_slots routes admitted checked.
  unfold checked_dispatch in checked.
  destruct (Nat.leb (List.length routes) available_slots) eqn:fits;
    try discriminate.
  inversion checked; subst; apply flat_dispatch_conserves_exactly_the_admitted_routes.
Qed.

Theorem insufficient_route_capacity_refuses_before_publication :
  forall available_slots routes,
    available_slots < List.length routes ->
    checked_dispatch available_slots routes = None.
Proof.
  intros available_slots routes insufficient.
  unfold checked_dispatch.
  apply Nat.leb_gt in insufficient.
  rewrite insufficient; reflexivity.
Qed.

Inductive grouped_name_depth : nat -> nat -> Prop :=
| grouped_name_atom : grouped_name_depth 0 0
| grouped_name_transparent : forall brackets constructors,
    grouped_name_depth brackets constructors ->
    grouped_name_depth (S brackets) constructors
| grouped_name_explicit : forall brackets constructors,
    grouped_name_depth brackets constructors ->
    grouped_name_depth (S brackets) (S constructors).

Definition grouped_name_readings (brackets : nat) : list nat := seq 0 (S brackets).

Theorem grouped_name_depth_sound : forall brackets constructors,
  grouped_name_depth brackets constructors -> constructors <= brackets.
Proof.
  intros brackets constructors derivation; induction derivation; lia.
Qed.

Theorem grouped_name_depth_complete : forall brackets constructors,
  constructors <= brackets -> grouped_name_depth brackets constructors.
Proof.
  induction brackets as [| brackets IH]; intros constructors bounded.
  - assert (constructors = 0) by lia; subst; constructor.
  - destruct constructors as [| constructors].
    + apply grouped_name_transparent; apply IH; lia.
    + apply grouped_name_explicit; apply IH; lia.
Qed.

Theorem grouped_name_readings_exact : forall brackets constructors,
  In constructors (grouped_name_readings brackets) <->
  grouped_name_depth brackets constructors.
Proof.
  intros brackets constructors; unfold grouped_name_readings; rewrite in_seq.
  split.
  - intros bounded; apply grouped_name_depth_complete; lia.
  - intros derivation; apply grouped_name_depth_sound in derivation; lia.
Qed.

Theorem grouped_name_readings_count : forall brackets,
  List.length (grouped_name_readings brackets) = S brackets.
Proof.
  intros; unfold grouped_name_readings; apply length_seq.
Qed.

Theorem grouped_name_readings_unique : forall brackets,
  NoDup (grouped_name_readings brackets).
Proof.
  intros; unfold grouped_name_readings; apply seq_NoDup.
Qed.

Theorem all_explicit_groups_are_retained : forall brackets,
  In brackets (grouped_name_readings brackets).
Proof.
  intros; apply grouped_name_readings_exact; apply grouped_name_depth_complete; lia.
Qed.

Definition measured_special_name_depths : list nat := [0; 1].
Definition measured_ordinary_name_depths : list nat := [0; 1; 2].

Theorem measured_union_retains_all_two_group_forms :
  measured_ordinary_name_depths = grouped_name_readings 2 /\
  (forall constructors, In constructors measured_special_name_depths ->
    In constructors measured_ordinary_name_depths).
Proof.
  split; [reflexivity|].
  intros constructors present; simpl in *; intuition.
Qed.

Theorem source_category_overlap_does_not_justify_removal :
  grouped_name_depth 2 2 /\
  In 2 measured_ordinary_name_depths /\
  ~ In 2 measured_special_name_depths.
Proof.
  split.
  - apply grouped_name_depth_complete; lia.
  - simpl; intuition lia.
Qed.

Print Assumptions grouped_name_depth_sound.
Print Assumptions grouped_name_depth_complete.
Print Assumptions grouped_name_readings_exact.
Print Assumptions grouped_name_readings_count.
Print Assumptions grouped_name_readings_unique.
Print Assumptions all_explicit_groups_are_retained.
Print Assumptions measured_union_retains_all_two_group_forms.
Print Assumptions source_category_overlap_does_not_justify_removal.

Definition nil_send_variants : list nat := [0; 1; 2].

Definition grouped_send_combinations (brackets : nat) : list (nat * (nat * nat)) :=
  list_prod (grouped_name_readings brackets)
    (list_prod nil_send_variants nil_send_variants).

Theorem grouped_send_combinations_exact : forall brackets constructors left right,
  In (constructors, (left, right)) (grouped_send_combinations brackets) <->
  grouped_name_depth brackets constructors /\ left < 3 /\ right < 3.
Proof.
  intros; unfold grouped_send_combinations.
  rewrite !in_prod_iff, grouped_name_readings_exact.
  unfold nil_send_variants; simpl; intuition lia.
Qed.

Theorem grouped_send_combinations_count : forall brackets,
  List.length (grouped_send_combinations brackets) = S brackets * 9.
Proof.
  intros; unfold grouped_send_combinations.
  rewrite !length_prod, grouped_name_readings_count; reflexivity.
Qed.

Theorem single_group_divided_send_has_eighteen_forms :
  List.length (grouped_send_combinations 1) = 18.
Proof. reflexivity. Qed.

Print Assumptions grouped_send_combinations_exact.
Print Assumptions grouped_send_combinations_count.
Print Assumptions single_group_divided_send_has_eighteen_forms.
