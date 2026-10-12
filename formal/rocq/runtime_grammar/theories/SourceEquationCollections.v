(** * Coordinating the source equation section with existing collections

    This file is a composition model, not a second production normalizer.
    The equation phase reuses SourceEquationSection; the collection phase
    describes the existing canonical collection constructor by its exact
    child-key observations.  Bag sorting, Set deduplication, and keyed-map
    sorting reuse CanonicalSemanticArena.  Map and BOTH valued PathMap modes
    refuse duplicate keys.  No overwrite or PathMap-set deduplication policy
    is introduced here.

    A collection pass may change ancestor syntax and expose a new equation
    redex.  Its occurrences do not increase, but sorting need not decrease
    occurrences.  Consequently only cycles containing a genuine equation
    contraction may continue.  Their occurrence measure strictly decreases.
    The finite-cell/class bound for each raw equation phase remains separate:
    collection reconstruction may change child vectors or Set arity.

    Successful finite coordination yields membership in the combined existing
    quotient, collection canonicality, and equation irreducibility.  It does
    NOT prove uniqueness for a new combined quotient, physical engine
    completeness, or totality on every well-typed rich term.  The final
    counterexample shows why mutable Map keys obstruct that totality.

    Local refinement boundaries are the source-owned operator/mode classifier,
    exact child-key identity, the existing equation-phase observations, and
    the existing collection constructor observations.  The optional domain
    completion theorem states its two local closure/availability obligations
    explicitly; it does not assume a completed combined section theorem.
*)

From Stdlib Require Import List PeanoNat Lia Arith.Wf_nat Sorting.Permutation.
From RuntimeGrammar Require Import SourceEquationSection CanonicalSemanticArena.
Import ListNotations.

Module SourceEquationCollections.
Module E := SourceEquationSection.
Module C := CanonicalSemanticArena.
Import E.K.

Definition Term := E.Term.

(** Collection labels and pair/mode labels are resolved source-image labels,
    not constructor spellings.  List and other positional operators remain
    unclassified.  A PathMap's three mode markers remain distinct even when
    the collection is empty. *)
Inductive CollectionKind :=
| BagKind
| SetKind
| MapKind (pair : nat)
| PathMapKind (pair neutral_marker set_marker map_marker : nat).

Record Profile := {
  collection_kind : nat -> option CollectionKind;
  collection_roles_separate : forall operator kind,
    collection_kind operator = Some kind -> 5 <= operator;
  pathmap_markers_separate : forall operator pair neutral set map,
    collection_kind operator = Some (PathMapKind pair neutral set map) ->
    neutral <> set /\ neutral <> map /\ set <> map
}.

Definition marker operator : Term := LogicApplication operator [].
Definition pair_term operator (entry : Term * Term) : Term :=
  LogicApplication operator [fst entry; snd entry].
Definition pair_terms operator entries := map (pair_term operator) entries.

Lemma map_injective_on_lists : forall (A B : Type) (f : A -> B),
  (forall x y, f x = f y -> x = y) ->
  forall xs ys, map f xs = map f ys -> xs = ys.
Proof.
  intros A B f Injective xs. induction xs as [|x xs IH]; intros [|y ys] Equal;
    simpl in Equal; try discriminate; [reflexivity|].
  injection Equal as Head Tail. f_equal; [now apply Injective|now apply IH].
Qed.

Lemma map_reflects_permutation : forall (A B : Type) (f : A -> B),
  (forall x y, f x = f y -> x = y) ->
  forall xs ys, Permutation (map f xs) (map f ys) -> Permutation xs ys.
Proof.
  intros A B f Injective xs ys P.
  destruct (@Permutation_map_inv A B f (map f xs) ys P) as [zs [Equal Perm]].
  assert (xs = zs) by (eapply map_injective_on_lists; eauto).
  subst zs. now apply Permutation_sym.
Qed.

Lemma child_occurrences_permutation : forall xs ys,
  Permutation xs ys -> E.child_occurrences xs = E.child_occurrences ys.
Proof.
  intros xs ys P. induction P; simpl in *; lia.
Qed.

Lemma child_occurrences_nodup : forall children,
  E.child_occurrences (nodup E.term_eq_dec children) <= E.child_occurrences children.
Proof.
  induction children as [|child children IH]; simpl; [lia|].
  destruct (in_dec E.term_eq_dec child children); simpl; lia.
Qed.

Lemma repeated_entry_is_not_unique : forall (A : Type) (entry : A),
  ~ NoDup [entry; entry].
Proof.
  intros A entry Unique. inversion Unique as [|head tail Fresh UniqueTail]; subst.
  apply Fresh. now left.
Qed.

Section ExactCollectionObservations.
  Variable exact_key : Term -> nat.
  Hypothesis exact_key_reflects : forall x y, exact_key x = exact_key y -> x = y.

  Definition keys children := map exact_key children.
  Definition entry_code (entry : Term * Term) :=
    (exact_key (fst entry), exact_key (snd entry)).
  Definition entry_codes entries := map entry_code entries.
  Definition entry_keys (entries : list (Term * Term)) :=
    map (fun entry => exact_key (fst entry)) entries.

  Lemma entry_code_reflects : forall x y, entry_code x = entry_code y -> x = y.
  Proof.
    intros [x xv] [y yv] Equal. unfold entry_code in Equal; simpl in Equal.
    injection Equal as Key Value. f_equal; now apply exact_key_reflects.
  Qed.

  Lemma entry_keys_are_code_keys : forall entries,
    entry_keys entries = map fst (entry_codes entries).
  Proof. intros. unfold entry_keys, entry_codes. rewrite map_map. reflexivity. Qed.

  (** These are precise observations at ONE existing constructor call, not
      assumptions that a whole output denotes a source step.  Refusal has no
      successful observation.  For keyed carriers even identical duplicate
      entries are refused. *)
  Definition BagObservation before after :=
    keys after = C.canonical_bag (keys before).
  Definition SetObservation before after :=
    keys after = C.canonical_set (keys before).
  Definition MapObservation before after :=
    NoDup (entry_keys before) /\
    entry_codes after = C.canonical_map (entry_codes before).
  Definition PathSetObservation before after :=
    NoDup (keys before) /\ BagObservation before after.

  Lemma bag_observation_preserves_multiplicity : forall before after,
    BagObservation before after -> Permutation before after.
  Proof.
    intros before after Observation.
    apply (map_reflects_permutation Term nat exact_key exact_key_reflects).
    unfold BagObservation, keys in Observation. rewrite Observation.
    apply C.canonical_bag_preserves_multiplicity.
  Qed.

  Lemma exact_key_membership : forall child children,
    In (exact_key child) (keys children) <-> In child children.
  Proof.
    intros child children. unfold keys. split.
    - intros Member. apply in_map_iff in Member.
      destruct Member as [found [Equal Member]].
      apply exact_key_reflects in Equal. now subst found.
    - apply in_map.
  Qed.

  Lemma set_observation_preserves_membership : forall before after,
    SetObservation before after -> forall child, In child before <-> In child after.
  Proof.
    intros before after Observation child.
    rewrite <- !exact_key_membership. unfold SetObservation in Observation.
    rewrite Observation. symmetry. apply C.canonical_set_preserves_membership.
  Qed.

  Lemma set_observation_is_dedup_permutation : forall before after,
    SetObservation before after -> Permutation (nodup E.term_eq_dec before) after.
  Proof.
    intros before after Observation. apply NoDup_Permutation.
    - apply NoDup_nodup.
    - apply (@NoDup_map_inv Term nat exact_key after).
      change (NoDup (keys after)). rewrite Observation.
      apply C.canonical_set_has_unique_elements.
    - intros child. rewrite nodup_In.
      now apply set_observation_preserves_membership.
  Qed.

  Lemma map_observation_preserves_entries : forall before after,
    MapObservation before after -> Permutation before after.
  Proof.
    intros before after [_ Observation].
    apply (map_reflects_permutation (Term * Term) (nat * nat)
      entry_code entry_code_reflects).
    unfold entry_codes in Observation. rewrite Observation.
    apply C.canonical_map_preserves_entries.
  Qed.

  Lemma map_observation_preserves_key_uniqueness : forall before after,
    MapObservation before after -> NoDup (entry_keys after).
  Proof.
    intros before after [Unique Observation].
    rewrite entry_keys_are_code_keys in *. rewrite Observation.
    now apply C.canonical_map_preserves_unique_keys.
  Qed.

  Lemma pathset_observation_preserves_key_uniqueness : forall before after,
    PathSetObservation before after -> NoDup (keys after).
  Proof.
    intros before after [Unique Observation].
    unfold BagObservation in Observation. rewrite Observation.
    eapply Permutation_NoDup; [apply C.canonical_bag_preserves_multiplicity|exact Unique].
  Qed.

  Theorem maps_refuse_duplicate_keys : forall before after,
    ~ NoDup (entry_keys before) -> ~ MapObservation before after.
  Proof. intros before after Duplicate [Unique _]. contradiction. Qed.

  Theorem pathmap_set_refuses_duplicate_keys : forall before after,
    ~ NoDup (keys before) -> ~ PathSetObservation before after.
  Proof. intros before after Duplicate [Unique _]. contradiction. Qed.

  Variable profile : Profile.

  Inductive CanonicalRoot : Term -> Term -> Prop :=
  | canonical_bag : forall operator before after,
      collection_kind profile operator = Some BagKind ->
      BagObservation before after ->
      CanonicalRoot (LogicApplication operator before) (LogicApplication operator after)
  | canonical_set : forall operator before after,
      collection_kind profile operator = Some SetKind ->
      SetObservation before after ->
      CanonicalRoot (LogicApplication operator before) (LogicApplication operator after)
  | canonical_map : forall operator pair before after,
      collection_kind profile operator = Some (MapKind pair) ->
      MapObservation before after ->
      CanonicalRoot (LogicApplication operator (pair_terms pair before))
        (LogicApplication operator (pair_terms pair after))
  | canonical_path_empty : forall operator pair neutral set map,
      collection_kind profile operator = Some (PathMapKind pair neutral set map) ->
      CanonicalRoot (LogicApplication operator [marker neutral])
        (LogicApplication operator [marker neutral])
  | canonical_path_set : forall operator pair neutral set map before after,
      collection_kind profile operator = Some (PathMapKind pair neutral set map) ->
      PathSetObservation before after ->
      CanonicalRoot (LogicApplication operator (marker set :: before))
        (LogicApplication operator (marker set :: after))
  | canonical_path_map : forall operator pair neutral set map before after,
      collection_kind profile operator = Some (PathMapKind pair neutral set map) ->
      MapObservation before after ->
      CanonicalRoot (LogicApplication operator (marker map :: pair_terms pair before))
        (LogicApplication operator (marker map :: pair_terms pair after)).

  (** This is the existing collection equality, independently of canonical
      order: multiplicity for Bags, extensional membership for Sets, and
      entry permutation WITHOUT key erasure for Maps.  PathMap modes never
      change.  The surrounding raw syntax can contain an invalid map; this
      equality does not turn it into an admitted typed carrier. *)
  Inductive CollectionEquality : Term -> Term -> Prop :=
  | equality_bag : forall operator before after,
      collection_kind profile operator = Some BagKind -> Permutation before after ->
      CollectionEquality (LogicApplication operator before) (LogicApplication operator after)
  | equality_set : forall operator before after,
      collection_kind profile operator = Some SetKind ->
      (forall child, In child before <-> In child after) ->
      CollectionEquality (LogicApplication operator before) (LogicApplication operator after)
  | equality_map : forall operator pair before after,
      collection_kind profile operator = Some (MapKind pair) -> Permutation before after ->
      CollectionEquality (LogicApplication operator (pair_terms pair before))
        (LogicApplication operator (pair_terms pair after))
  | equality_path_empty : forall operator pair neutral set map,
      collection_kind profile operator = Some (PathMapKind pair neutral set map) ->
      CollectionEquality (LogicApplication operator [marker neutral])
        (LogicApplication operator [marker neutral])
  | equality_path_set : forall operator pair neutral set map before after,
      collection_kind profile operator = Some (PathMapKind pair neutral set map) ->
      Permutation before after ->
      CollectionEquality (LogicApplication operator (marker set :: before))
        (LogicApplication operator (marker set :: after))
  | equality_path_map : forall operator pair neutral set map before after,
      collection_kind profile operator = Some (PathMapKind pair neutral set map) ->
      Permutation before after ->
      CollectionEquality (LogicApplication operator (marker map :: pair_terms pair before))
        (LogicApplication operator (marker map :: pair_terms pair after)).

  Theorem canonical_root_is_existing_collection_equality : forall before after,
    CanonicalRoot before after -> CollectionEquality before after.
  Proof.
    intros before after Observation. destruct Observation.
    - eapply equality_bag; eauto using bag_observation_preserves_multiplicity.
    - eapply equality_set; eauto using set_observation_preserves_membership.
    - eapply equality_map; eauto using map_observation_preserves_entries.
    - eapply equality_path_empty; eauto.
    - destruct H0 as [_ Sorted]. eapply equality_path_set;
        eauto using bag_observation_preserves_multiplicity.
    - eapply equality_path_map; eauto using map_observation_preserves_entries.
  Qed.

  Theorem canonical_root_does_not_increase_occurrences : forall before after,
    CanonicalRoot before after -> E.occurrences after <= E.occurrences before.
  Proof.
    intros before after Observation. destruct Observation.
    - pose proof (bag_observation_preserves_multiplicity _ _ H0) as P.
      pose proof (child_occurrences_permutation _ _ P).
      change (S (E.child_occurrences after) <= S (E.child_occurrences before)). lia.
    - pose proof (set_observation_is_dedup_permutation _ _ H0) as P.
      pose proof (child_occurrences_permutation _ _ P).
      pose proof (child_occurrences_nodup before).
      change (S (E.child_occurrences after) <= S (E.child_occurrences before)). lia.
    - pose proof (map_observation_preserves_entries _ _ H0) as P.
      pose proof (child_occurrences_permutation _ _ (Permutation_map (pair_term pair) P)).
      change (S (E.child_occurrences (pair_terms pair after)) <=
        S (E.child_occurrences (pair_terms pair before))). unfold pair_terms. lia.
    - reflexivity.
    - destruct H0 as [_ Sorted].
      pose proof (bag_observation_preserves_multiplicity _ _ Sorted) as P.
      pose proof (child_occurrences_permutation _ _ P).
      change (S (E.occurrences (marker set) + E.child_occurrences after) <=
        S (E.occurrences (marker set) + E.child_occurrences before)). lia.
    - pose proof (map_observation_preserves_entries _ _ H0) as P.
      pose proof (child_occurrences_permutation _ _ (Permutation_map (pair_term pair) P)).
      change (S (E.occurrences (marker map) + E.child_occurrences (pair_terms pair after)) <=
        S (E.occurrences (marker map) + E.child_occurrences (pair_terms pair before))).
      unfold pair_terms. lia.
  Qed.

  Inductive CanonicalStep : Term -> Term -> Prop :=
  | canonical_at_root : forall x y, CanonicalRoot x y -> CanonicalStep x y
  | canonical_in_context : forall operator before after x y,
      CanonicalStep x y ->
      CanonicalStep (LogicApplication operator (before ++ x :: after))
        (LogicApplication operator (before ++ y :: after)).

  Inductive CanonicalReaches : Term -> Term -> Prop :=
  | canonical_refl : forall x, CanonicalReaches x x
  | canonical_next : forall x y z,
      CanonicalStep x y -> CanonicalReaches y z -> CanonicalReaches x z.

  Theorem canonical_steps_do_not_increase_occurrences : forall x y,
    CanonicalStep x y -> E.occurrences y <= E.occurrences x.
  Proof.
    intros x y Step. induction Step.
    - now apply canonical_root_does_not_increase_occurrences.
    - rewrite !E.occurrences_context. lia.
  Qed.

  Lemma canonical_pass_measure : forall x y,
    CanonicalReaches x y -> E.occurrences y <= E.occurrences x.
  Proof.
    intros x y Run. induction Run; [lia|].
    pose proof (canonical_steps_do_not_increase_occurrences _ _ H). lia.
  Qed.

  Inductive CombinedCongruence : Term -> Term -> Prop :=
  | combined_refl : forall x, CombinedCongruence x x
  | combined_sym : forall x y, CombinedCongruence x y -> CombinedCongruence y x
  | combined_trans : forall x y z,
      CombinedCongruence x y -> CombinedCongruence y z -> CombinedCongruence x z
  | combined_equations : forall x y, E.Congruence x y -> CombinedCongruence x y
  | combined_collections : forall x y,
      CollectionEquality x y -> CombinedCongruence x y
  | combined_context : forall operator before after x y,
      CombinedCongruence x y ->
      CombinedCongruence (LogicApplication operator (before ++ x :: after))
        (LogicApplication operator (before ++ y :: after)).

  Lemma canonical_step_is_sound : forall x y,
    CanonicalStep x y -> CombinedCongruence x y.
  Proof.
    intros x y Step. induction Step.
    - apply combined_collections. now apply canonical_root_is_existing_collection_equality.
    - now apply combined_context.
  Qed.

  Lemma canonical_pass_is_sound : forall x y,
    CanonicalReaches x y -> CombinedCongruence x y.
  Proof.
    intros x y Run. induction Run; eauto using combined_refl, combined_trans,
      canonical_step_is_sound.
  Qed.

  Definition KeySorted children := C.SSorted Nat.leb (keys children).
  Definition MapCanonical entries :=
    C.SSorted C.entry_leb (entry_codes entries) /\ NoDup (entry_keys entries).

  Definition LocallyCanonical operator children : Prop :=
    match collection_kind profile operator with
    | None => True
    | Some BagKind => KeySorted children
    | Some SetKind => KeySorted children /\ NoDup (keys children)
    | Some (MapKind pair_operator) => exists entries,
        children = pair_terms pair_operator entries /\ MapCanonical entries
    | Some (PathMapKind pair_operator neutral set map) =>
        children = [marker neutral] \/
        (exists entries, children = marker set :: entries /\
          KeySorted entries /\ NoDup (keys entries)) \/
        (exists entries, children = marker map :: pair_terms pair_operator entries /\
          MapCanonical entries)
    end.

  Inductive CollectionCanonical : Term -> Prop :=
  | collection_variable : forall variable, CollectionCanonical (LogicVariable variable)
  | collection_application : forall operator children,
      LocallyCanonical operator children -> Forall CollectionCanonical children ->
      CollectionCanonical (LogicApplication operator children).

  (** A completed constructor traversal is a finite sequence of LOCAL
      canonical observations plus the final carrier check.  Merely performing
      one root sort is not such a pass. *)
  Definition CollectionPass before after :=
    CanonicalReaches before after /\ CollectionCanonical after.

  Definition EquationResult before after :=
    E.Congruence before after /\ E.Irreducible after.

  Lemma equation_result_is_existing_normal_form : forall before after,
    EquationResult before after -> after = E.normalize before.
  Proof. intros before after [Sound Normal]. now apply E.accepted_equivalent_irreducible_output_is_the_section. Qed.

  Lemma equation_result_is_reachable : forall before after,
    EquationResult before after -> E.Reaches before after.
  Proof.
    intros before after Result. rewrite (equation_result_is_existing_normal_form _ _ Result).
    apply E.reference_normalization_is_reachable.
  Qed.

  Lemma reference_equation_result : forall input, EquationResult input (E.normalize input).
  Proof.
    intros. split.
    - apply E.reaches_in_congruence, E.reference_normalization_is_reachable.
    - apply E.normal_is_irreducible, E.reference_normalization_is_normal.
  Qed.

  Lemma equation_reaches_decreases_unless_equal : forall before after,
    E.Reaches before after -> before = after \/ E.occurrences after < E.occurrences before.
  Proof.
    intros before after Run. induction Run.
    - now left.
    - right. now apply E.every_contextual_collapse_strictly_decreases_occurrences.
    - destruct IHRun1 as [Equal|First]; destruct IHRun2 as [Equal2|Second];
        try (left; congruence); right; subst; lia.
  Qed.

  (** The first pass is allowed to contain no equation contraction.  A later
      cycle is justified ONLY by an equation redex in the current canonical
      term.  Nontrivial collection sorting by itself is not progress. *)
  Definition InitialPass before after := exists raw,
    EquationResult before raw /\ CollectionPass raw after.
  Definition ContinuedCycle before after :=
    ~ E.Irreducible before /\ InitialPass before after.

  Theorem every_continued_cycle_strictly_decreases_occurrences : forall before after,
    ContinuedCycle before after -> E.occurrences after < E.occurrences before.
  Proof.
    intros before after [Reducible [raw [Equation [Canonical _]]]].
    pose proof (equation_reaches_decreases_unless_equal _ _
      (equation_result_is_reachable _ _ Equation)) as Decrease.
    pose proof (canonical_pass_measure _ _ Canonical) as Nonexpanding.
    destruct Decrease as [Same|Strict]; [subst raw; destruct Equation; contradiction|lia].
  Qed.

  Theorem continued_coordination_terminates :
    well_founded (fun after before => ContinuedCycle before after).
  Proof.
    apply (well_founded_lt_compat Term E.occurrences).
    intros after before Cycle. now apply every_continued_cycle_strictly_decreases_occurrences.
  Qed.

  Lemma initial_pass_is_sound : forall before after,
    InitialPass before after -> CombinedCongruence before after.
  Proof.
    intros before after [raw [[Equation _] [Canonical _]]].
    eapply combined_trans with (y := raw).
    - apply combined_equations. exact Equation.
    - apply canonical_pass_is_sound. exact Canonical.
  Qed.

  Inductive Coordination : nat -> Term -> Term -> Prop :=
  | coordination_done : forall output,
      CollectionCanonical output -> E.Irreducible output -> Coordination 0 output output
  | coordination_continue : forall count before middle output,
      ContinuedCycle before middle -> Coordination count middle output ->
      Coordination (S count) before output.

  Theorem continued_cycles_are_bounded_by_unfolded_occurrences : forall count before output,
    Coordination count before output -> count + E.occurrences output <= E.occurrences before.
  Proof.
    intros count before output Run. induction Run; [lia|].
    pose proof (every_continued_cycle_strictly_decreases_occurrences _ _ H). lia.
  Qed.

  Lemma coordination_is_sound_and_jointly_normal : forall count before output,
    Coordination count before output ->
    CombinedCongruence before output /\ CollectionCanonical output /\ E.Irreducible output.
  Proof.
    intros count before output Run. induction Run.
    - split; [apply combined_refl|auto].
    - destruct IHRun as [Sound [Canonical Irreducible]]. split; [|auto].
      destruct H as [_ Pass]. eapply combined_trans with (y := middle).
      + apply initial_pass_is_sound. exact Pass.
      + exact Sound.
  Qed.

  Theorem accepted_coordination_is_sound_and_jointly_normal :
    forall input ready output count,
    InitialPass input ready -> Coordination count ready output ->
    CombinedCongruence input output /\ CollectionCanonical output /\
    E.Irreducible output /\ count + E.occurrences output <= E.occurrences input.
  Proof.
    intros input ready output count First Run.
    pose proof (coordination_is_sound_and_jointly_normal _ _ _ Run) as [Sound [Canonical Normal]].
    pose proof (continued_cycles_are_bounded_by_unfolded_occurrences _ _ _ Run) as Bound.
    destruct First as [raw [Equation [Collection Ready]]].
    pose proof (equation_reaches_decreases_unless_equal _ _
      (equation_result_is_reachable _ _ Equation)) as Decrease.
    pose proof (canonical_pass_measure _ _ Collection) as Nonexpanding.
    split.
    - eapply combined_trans with (y := ready); [|exact Sound]. apply initial_pass_is_sound.
      exists raw. split; [exact Equation|]. split; assumption.
    - repeat split; try assumption. destruct Decrease; subst; lia.
  Qed.

  (** These are two DIFFERENT bounds.  Collection reconstruction can allocate
      different structural cells; the raw phase's old cell table must not be
      reused as a bound on all reconstructed graphs. *)
  Theorem cycle_and_raw_phase_have_separate_finite_bounds :
    forall before after cells classes labels final_labels merges,
    ContinuedCycle before after ->
    E.EnumeratesCarrierClasses cells classes labels ->
    E.SuccessfulMergeChain merges labels final_labels ->
    E.occurrences after < E.occurrences before /\
    merges + length final_labels <= length cells.
  Proof.
    intros before after cells classes labels final_labels merges Cycle Classes Merges.
    split.
    - now apply every_continued_cycle_strictly_decreases_occurrences.
    - eapply E.successful_merges_are_bounded_by_the_initial_carrier; eauto.
  Qed.

  (** This conditional mathematical existence result is NOT a totality claim
      about every valid installed theory.  The domain must survive raw
      equations, and every term remaining in it must admit a successful
      existing collection pass that remains in the domain.  In particular,
      keyed collisions cannot be hidden in the latter field.  Physical fuel,
      allocation, extraction, and cancellation are additional API limits. *)
  Record DomainClosure (domain : Term -> Prop) : Prop := {
    equations_preserve_domain : forall before after,
      domain before -> E.Reaches before after -> domain after;
    collection_pass_available_in_domain : forall before,
      domain before -> exists after, CollectionPass before after /\ domain after
  }.

  Theorem closed_domain_canonical_terms_have_completion : forall domain,
    DomainClosure domain -> forall input,
    domain input -> CollectionCanonical input ->
    exists count output, Coordination count input output.
  Proof.
    intros domain Closure.
    refine (@well_founded_induction Term
      (fun after before => ContinuedCycle before after)
      continued_coordination_terminates
      (fun input => domain input -> CollectionCanonical input ->
        exists count output, Coordination count input output) _).
    intros input IH Domain Canonical.
    destruct (E.term_eq_dec input (E.normalize input)) as [Fixed|Changed].
    - exists 0, input. apply coordination_done; [exact Canonical|].
      rewrite Fixed. apply E.normal_is_irreducible, E.reference_normalization_is_normal.
    - assert (Reducible : ~ E.Irreducible input).
      { intros Normal. apply Changed. symmetry.
        apply E.normal_terms_are_reference_fixed_points, E.irreducible_is_normal. exact Normal. }
      assert (RawDomain : domain (E.normalize input)).
      { eapply (equations_preserve_domain domain Closure);
          [exact Domain|apply E.reference_normalization_is_reachable]. }
      destruct (collection_pass_available_in_domain domain Closure _ RawDomain)
        as [ready [Pass ReadyDomain]].
      assert (Cycle : ContinuedCycle input ready).
      { split; [exact Reducible|]. exists (E.normalize input).
        split; [apply reference_equation_result|exact Pass]. }
      destruct (IH ready Cycle ReadyDomain (proj2 Pass)) as [count [output Run]].
      exists (S count), output. now apply coordination_continue with (middle := ready).
  Qed.

  Theorem closed_domain_has_accepted_completion : forall domain,
    DomainClosure domain -> forall input, domain input ->
    exists ready count output, InitialPass input ready /\ Coordination count ready output.
  Proof.
    intros domain Closure input Domain.
    assert (RawDomain : domain (E.normalize input)).
    { eapply (equations_preserve_domain domain Closure);
        [exact Domain|apply E.reference_normalization_is_reachable]. }
    destruct (collection_pass_available_in_domain domain Closure _ RawDomain)
      as [ready [Pass ReadyDomain]].
    destruct (closed_domain_canonical_terms_have_completion domain Closure ready ReadyDomain
      (proj2 Pass)) as [count [output Run]].
    exists ready, count, output. split; [|exact Run]. exists (E.normalize input).
    split; [apply reference_equation_result|exact Pass].
  Qed.
End ExactCollectionObservations.

(** Stability is an injectivity condition on the ACTUAL keys of a retained
    keyed carrier.  It is stronger than preservation of key sort, and does
    not follow from merely checking that all equations have the ten schemas.
    Identity on an equation-inert key domain is one sufficient instance. *)
Definition StableKeys (interpret : Term -> Term) (keys : list Term) :=
  forall first second, In first keys -> In second keys ->
    interpret first = interpret second -> first = second.

Theorem stable_keys_preserve_uniqueness : forall interpret keys,
  StableKeys interpret keys -> NoDup keys -> NoDup (map interpret keys).
Proof.
  intros interpret keys Stable Unique. revert Stable.
  induction Unique as [|head tail Fresh Unique IH]; intros Stable; simpl.
  - constructor.
  - constructor.
    + intros Member. apply in_map_iff in Member. destruct Member as [found [Equal InTail]].
      apply Fresh. assert (head = found).
      { apply Stable; [now left|now right|symmetry; exact Equal]. }
      now subst found.
    + apply IH. intros first second First Second Equal.
      apply Stable; [now right|now right|exact Equal].
Qed.

Theorem unchanged_keys_are_stable : forall interpret keys,
  (forall key, In key keys -> interpret key = key) -> StableKeys interpret keys.
Proof. intros interpret keys Fixed first second First Second Equal.
  rewrite (Fixed first First), (Fixed second Second) in Equal. exact Equal. Qed.

Theorem equation_irreducible_keys_are_stable : forall keys,
  (forall key, In key keys -> E.Irreducible key) -> StableKeys E.normalize keys.
Proof.
  intros keys Irreducible. apply unchanged_keys_are_stable. intros key Member.
  apply E.normal_terms_are_reference_fixed_points, E.irreducible_is_normal.
  now apply Irreducible.
Qed.

(** Concrete obstruction: these are distinct, well-shaped keys before the
    equation phase and the SAME key afterward.  Values are immaterial, so
    even two identical values do not justify changing existing Map policy. *)
Definition collision_atom : Term := LogicApplication 5 [].
Definition collision_redex : Term := E.alternative E.zero collision_atom.

Lemma collision_keys_are_distinct : collision_atom <> collision_redex.
Proof. unfold collision_atom, collision_redex, E.alternative. discriminate. Qed.

Lemma collision_keys_normalize_equal :
  E.normalize collision_atom = collision_atom /\
  E.normalize collision_redex = collision_atom.
Proof.
  split; [reflexivity|]. unfold collision_redex. rewrite E.normalize_alternative, E.normalize_zero.
  apply E.smart_alternative_zero_left.
Qed.

Theorem distinct_admitted_keys_can_collapse :
  NoDup [collision_atom; collision_redex] /\
  ~ NoDup (map E.normalize [collision_atom; collision_redex]) /\
  ~ StableKeys E.normalize [collision_atom; collision_redex].
Proof.
  destruct collision_keys_normalize_equal as [Atom Redex]. split.
  - constructor.
    + simpl. intros [Equal|Impossible]; [apply collision_keys_are_distinct; symmetry; exact Equal|contradiction].
    + constructor; [simpl; tauto|constructor].
  - split.
    + change (~ NoDup [E.normalize collision_atom; E.normalize collision_redex]).
      rewrite Atom, Redex. apply repeated_entry_is_not_unique.
    + intros Stable. apply collision_keys_are_distinct.
      apply Stable; [now left|right; now left|now rewrite Atom, Redex].
Qed.

Theorem no_collection_observation_can_hide_collapsed_map_keys :
  forall exact_key after first_value second_value,
  ~ MapObservation exact_key
    [(collision_atom, first_value); (collision_atom, second_value)] after.
Proof.
  intros exact_key after first_value second_value [Unique _].
  change (NoDup [exact_key collision_atom; exact_key collision_atom]) in Unique.
  exact (repeated_entry_is_not_unique nat (exact_key collision_atom) Unique).
Qed.

(** A raw equation-normal tree need not remain equation-normal when an
    existing Set constructor removes duplicate normalized members.  This
    example concerns an intermediate raw tree, not initial Set admission. *)
Definition example_single_set : Term := LogicApplication 6 [collision_atom].
Definition example_duplicate_set : Term := LogicApplication 6 [collision_atom; collision_atom].
Definition example_before_collections := E.alternative example_duplicate_set example_single_set.
Definition example_after_collections := E.alternative example_single_set example_single_set.

Lemma existing_set_canonicalizer_removes_a_duplicate : forall key,
  C.canonical_set [key; key] = [key].
Proof.
  intros key. apply C.sorted_nodup_membership_unique.
  - apply C.canonical_keys_sorted.
  - apply C.canonical_set_has_unique_elements.
  - constructor; constructor.
  - constructor; [simpl; tauto|constructor].
  - intros candidate. rewrite C.canonical_set_preserves_membership. simpl. tauto.
Qed.

Theorem collection_canonicalization_can_expose_an_equation_redex :
  forall exact_key profile,
  collection_kind profile 6 = Some SetKind ->
  E.Irreducible example_before_collections /\
  CanonicalStep exact_key profile example_before_collections example_after_collections /\
  ~ E.Irreducible example_after_collections.
Proof.
  intros exact_key profile SetRole. split.
  - assert (Fixed : E.normalize example_before_collections = example_before_collections)
      by reflexivity.
    rewrite <- Fixed. apply E.normal_is_irreducible, E.reference_normalization_is_normal.
  - split.
    + change (CanonicalStep exact_key profile
        (LogicApplication 2 ([] ++ example_duplicate_set :: [example_single_set]))
        (LogicApplication 2 ([] ++ example_single_set :: [example_single_set]))).
      apply canonical_in_context, canonical_at_root.
      apply canonical_set; [exact SetRole|].
      change ([exact_key collision_atom] =
        C.canonical_set [exact_key collision_atom; exact_key collision_atom]).
      symmetry. apply existing_set_canonicalizer_removes_a_duplicate.
    + intros Irreducible. apply (Irreducible example_single_set).
      apply E.step_root, E.alternative_idempotent.
Qed.

Print Assumptions canonical_root_is_existing_collection_equality.
Print Assumptions canonical_root_does_not_increase_occurrences.
Print Assumptions maps_refuse_duplicate_keys.
Print Assumptions pathmap_set_refuses_duplicate_keys.
Print Assumptions every_continued_cycle_strictly_decreases_occurrences.
Print Assumptions continued_coordination_terminates.
Print Assumptions accepted_coordination_is_sound_and_jointly_normal.
Print Assumptions cycle_and_raw_phase_have_separate_finite_bounds.
Print Assumptions closed_domain_has_accepted_completion.
Print Assumptions stable_keys_preserve_uniqueness.
Print Assumptions distinct_admitted_keys_can_collapse.
Print Assumptions no_collection_observation_can_hide_collapsed_map_keys.
Print Assumptions collection_canonicalization_can_expose_an_equation_redex.

End SourceEquationCollections.
