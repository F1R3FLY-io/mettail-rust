(** * Uniqueness for successful equation/collection coordination

    This proof-only observation is not an alternative runtime normalizer.
    It reuses the ten-schema smart node and the existing generic collection
    sort.  Maps are observed as multisets of WHOLE entries, including their
    values.  The observation is total even on raw trees whose keys collide;
    this does not publish those trees or introduce a collision policy.

    Reflection is restricted to CollectionCanonical, equation-irreducible
    outputs.  Their existing sorted, unique-key representation determines
    exact Map order.  Thus successful results are unique without assuming
    that every rich input admits a successful canonicalization.  The keyed
    domain-closure and physical engine obligations of the imported model
    remain separate.

    No extra opcode-disjointness assumption is used.  Collection roles are
    separate from the five equation roles by the existing Profile field.
    All zero-arity markers are fixed by the structural observation, even
    for profiles more permissive than the authenticated typed image.
*)

From Stdlib Require Import List PeanoNat Lia Sorting.Permutation.
From RuntimeGrammar Require Import SourceEquationCollections.
Import ListNotations.

Module SourceEquationCollectionUniqueness.
Module X := SourceEquationCollections.
Module E := X.E.
Module C := X.C.
Import E.K.
Definition Term := E.Term.

(** These two order facts extend, rather than replace, the existing generic
    sort.  The first retains Bag multiplicity.  The second retains complete
    Map entries while using the existing unique key order. *)
Lemma nat_sorted_permutation_unique : forall xs ys,
  C.SSorted Nat.leb xs -> C.SSorted Nat.leb ys ->
  Permutation xs ys -> xs = ys.
Proof.
  intros xs. induction xs as [|x xs IH]; intros ys Left Right Perm.
  - symmetry. now apply Permutation_nil.
  - destruct ys as [|y ys]; [apply Permutation_sym, Permutation_nil in Perm; discriminate|].
    assert (XY : x <= y).
    { eapply C.sorted_head_minimum; [exact Left|].
      eapply Permutation_in; [apply Permutation_sym; exact Perm|now left]. }
    assert (YX : y <= x).
    { eapply C.sorted_head_minimum; [exact Right|].
      eapply Permutation_in; [exact Perm|now left]. }
    assert (x = y) by lia. subst y. f_equal. apply IH.
    + inversion Left; assumption.
    + inversion Right; assumption.
    + now apply Permutation_cons_inv in Perm.
Qed.

Lemma unique_keys_identify_members : forall (A : Type) (key : A -> nat) xs,
  NoDup (map key xs) -> forall x y,
  In x xs -> In y xs -> key x = key y -> x = y.
Proof.
  intros A key xs. induction xs as [|a xs IH]; intros Unique x y Xmem Ymem Equal;
    [contradiction|].
  inversion Unique as [|? ? Fresh Tail]; subst.
  destruct Xmem as [<-|Xmem]; destruct Ymem as [<-|Ymem]; auto.
  - exfalso. apply Fresh. rewrite Equal. now apply in_map.
  - exfalso. apply Fresh. rewrite <- Equal. now apply in_map.
Qed.

Lemma sorted_unique_key_permutation : forall (A : Type) (key : A -> nat) xs ys,
  C.SSorted Nat.leb (map key xs) -> C.SSorted Nat.leb (map key ys) ->
  NoDup (map key xs) -> Permutation xs ys -> xs = ys.
Proof.
  intros A key xs. induction xs as [|x xs IH]; intros ys Left Right Unique Perm.
  - symmetry. now apply Permutation_nil.
  - destruct ys as [|y ys]; [apply Permutation_sym, Permutation_nil in Perm; discriminate|].
    assert (Codes : map key (x :: xs) = map key (y :: ys)).
    { eapply nat_sorted_permutation_unique; eauto using Permutation_map. }
    injection Codes as Head Tail.
    assert (Equal : x = y).
    { eapply unique_keys_identify_members; [exact Unique|now left| |exact Head].
      eapply Permutation_in; [apply Permutation_sym; exact Perm|now left]. }
    subst y. f_equal. apply IH.
    + inversion Left; assumption.
    + inversion Right; assumption.
    + inversion Unique; assumption.
    + now apply Permutation_cons_inv in Perm.
Qed.

Lemma sorted_map_projection : forall (A B : Type) (f : A -> B)
  (left : A -> A -> bool) (right : B -> B -> bool),
  (forall x y, left x y = right (f x) (f y)) ->
  forall xs, C.SSorted left xs -> C.SSorted right (map f xs).
Proof.
  intros A B f left right Correspond xs Sorted. induction Sorted; simpl.
  - constructor.
  - constructor; [|assumption]. rewrite Forall_forall in *.
    intros y Member. apply in_map_iff in Member as [x [<- Member]].
    rewrite <- Correspond. now apply H.
Qed.

Section Observation.
  Variable exact_key : Term -> nat.
  Hypothesis exact_key_reflects : forall x y, exact_key x = exact_key y -> x = y.
  Variable profile : X.Profile.

  Definition term_leb x y := Nat.leb (exact_key x) (exact_key y).
  Definition ordered terms := C.sort term_leb terms.
  Definition extensional terms := ordered (nodup E.term_eq_dec terms).

  Lemma term_leb_total : forall x y, term_leb x y = true \/ term_leb y x = true.
  Proof. intros. apply C.nat_leb_total. Qed.
  Lemma term_leb_trans : forall x y z,
    term_leb x y = true -> term_leb y z = true -> term_leb x z = true.
  Proof. intros. eapply C.nat_leb_trans; eauto. Qed.

  Lemma ordered_permutation : forall terms, Permutation terms (ordered terms).
  Proof. intros. apply C.sort_permutation. Qed.
  Lemma ordered_key_sorted : forall terms, X.KeySorted exact_key (ordered terms).
  Proof.
    intros. unfold X.KeySorted, X.keys.
    eapply sorted_map_projection with (left := term_leb); [reflexivity|].
    apply C.sort_sorted; [apply term_leb_total|apply term_leb_trans].
  Qed.
  Lemma key_sorted_permutation_unique : forall xs ys,
    X.KeySorted exact_key xs -> X.KeySorted exact_key ys ->
    Permutation xs ys -> xs = ys.
  Proof.
    intros xs ys Left Right Perm. apply (X.map_injective_on_lists Term nat exact_key exact_key_reflects).
    eapply nat_sorted_permutation_unique; eauto using Permutation_map.
  Qed.
  Lemma ordered_extensional : forall xs ys,
    Permutation xs ys -> ordered xs = ordered ys.
  Proof.
    intros xs ys Perm. apply key_sorted_permutation_unique;
      try apply ordered_key_sorted.
    eapply Permutation_trans; [apply Permutation_sym, ordered_permutation|].
    eapply Permutation_trans; [exact Perm|apply ordered_permutation].
  Qed.
  Lemma ordered_reflects_permutation : forall xs ys,
    ordered xs = ordered ys -> Permutation xs ys.
  Proof.
    intros xs ys Equal. eapply Permutation_trans; [apply ordered_permutation|].
    rewrite Equal. apply Permutation_sym, ordered_permutation.
  Qed.
  Lemma extensional_membership : forall terms term,
    In term (extensional terms) <-> In term terms.
  Proof.
    intros terms term. unfold extensional.
    split; intros Member.
    - apply (proj1 (nodup_In E.term_eq_dec terms term)). eapply Permutation_in;
        [apply Permutation_sym, ordered_permutation|exact Member].
    - eapply Permutation_in; [apply ordered_permutation|].
      now apply (proj2 (nodup_In E.term_eq_dec terms term)).
  Qed.
  Lemma extensional_extensional : forall xs ys,
    (forall term, In term xs <-> In term ys) -> extensional xs = extensional ys.
  Proof.
    intros xs ys Members. apply ordered_extensional, NoDup_Permutation;
      try apply NoDup_nodup.
    intros term. rewrite !nodup_In. apply Members.
  Qed.
  Lemma extensional_reflects_membership : forall xs ys,
    extensional xs = extensional ys -> forall term, In term xs <-> In term ys.
  Proof.
    intros xs ys Equal term.
    rewrite <- (extensional_membership xs term), <- (extensional_membership ys term).
    now rewrite Equal.
  Qed.

  Lemma map_canonical_permutation_unique : forall xs ys,
    X.MapCanonical exact_key xs -> X.MapCanonical exact_key ys ->
    Permutation xs ys -> xs = ys.
  Proof.
    intros xs ys [Left Unique] [Right _] Perm.
    apply (sorted_unique_key_permutation (Term * Term)
      (fun entry => exact_key (fst entry))); try assumption.
    - change (C.SSorted Nat.leb (X.entry_keys exact_key xs)).
      rewrite X.entry_keys_are_code_keys.
      eapply sorted_map_projection; [reflexivity|exact Left].
    - change (C.SSorted Nat.leb (X.entry_keys exact_key ys)).
      rewrite X.entry_keys_are_code_keys.
      eapply sorted_map_projection; [reflexivity|exact Right].
  Qed.

  (** This structural fold changes only the observation order of collections.
      Map observation sorts complete entry TERMS, not keys.  PathMap retains
      the first child (the exact mode marker) and every following entry. *)
  Definition collection_children operator children :=
    match X.collection_kind profile operator with
    | None => children
    | Some X.BagKind => ordered children
    | Some X.SetKind => extensional children
    | Some (X.MapKind _) => ordered children
    | Some (X.PathMapKind _ _ _ _) =>
        match children with [] => [] | mode :: entries => mode :: ordered entries end
    end.

  Fixpoint structural (term : Term) : Term :=
    match term with
    | LogicVariable variable => LogicVariable variable
    | LogicApplication operator children =>
        LogicApplication operator (collection_children operator (map structural children))
    end.

  Definition observed_node operator children :=
    match X.collection_kind profile operator with
    | None => E.smart_node operator children
    | Some _ => LogicApplication operator (collection_children operator children)
    end.

  Fixpoint observe (term : Term) : Term :=
    match term with
    | LogicVariable variable => LogicVariable variable
    | LogicApplication operator children => observed_node operator (map observe children)
    end.

  Lemma equation_roles_are_positional : forall operator,
    operator < 5 -> X.collection_kind profile operator = None.
  Proof.
    intros operator Small. destruct (X.collection_kind profile operator) eqn:Kind; [|reflexivity].
    pose proof (X.collection_roles_separate profile operator c Kind). lia.
  Qed.
  Lemma collection_children_empty : forall operator, collection_children operator [] = [].
  Proof. intros. unfold collection_children. destruct (X.collection_kind profile operator) as [[| |pair|pair n s m]|]; reflexivity. Qed.
  Lemma structural_marker : forall operator, structural (X.marker operator) = X.marker operator.
  Proof. intros. change (LogicApplication operator (collection_children operator []) = X.marker operator).
    now rewrite collection_children_empty. Qed.

  (** Local reflection needs injectivity only between actual children being
      compared.  It does not assume global faithfulness of the observation. *)
  Lemma mapped_lists_reflect : forall (f : Term -> Term) xs ys,
    (forall x y, In x xs -> In y ys -> f x = f y -> x = y) ->
    map f xs = map f ys -> xs = ys.
  Proof.
    intros f xs. induction xs as [|x xs IH]; intros [|y ys] Reflect Equal;
      simpl in Equal; try discriminate; [reflexivity|].
    injection Equal as Head Tail. f_equal.
    - apply Reflect; [now left|now left|exact Head].
    - apply IH; [|exact Tail]. intros a b A B Equal.
      apply Reflect; [now right|now right|exact Equal].
  Qed.
  Lemma mapped_permutations_reflect : forall (f : Term -> Term) xs ys,
    (forall x y, In x xs -> In y ys -> f x = f y -> x = y) ->
    Permutation (map f xs) (map f ys) -> Permutation xs ys.
  Proof.
    intros f xs ys Reflect Perm.
    destruct (@Permutation_map_inv Term Term f (map f xs) ys Perm)
      as [zs [Equal Reorder]].
    assert (xs = zs).
    { eapply mapped_lists_reflect; [|exact Equal]. intros x y Xmem Ymem.
      apply Reflect; [exact Xmem|]. eapply Permutation_in;
        [apply Permutation_sym; exact Reorder|exact Ymem]. }
    subst zs. now apply Permutation_sym.
  Qed.
  Lemma mapped_memberships_reflect : forall (f : Term -> Term) xs ys,
    (forall x y, In x xs -> In y ys -> f x = f y -> x = y) ->
    (forall term, In term (map f xs) <-> In term (map f ys)) ->
    forall term, In term xs <-> In term ys.
  Proof.
    intros f xs ys Reflect Members term. split; intros Member.
    - assert (In (f term) (map f ys)) by (apply Members; now apply in_map).
      apply in_map_iff in H as [found [Equal Found]].
      assert (term = found) by (apply Reflect; auto). now subst.
    - assert (In (f term) (map f xs)) by (apply Members; now apply in_map).
      apply in_map_iff in H as [found [Equal Found]].
      assert (found = term) by (apply Reflect; auto). now subst.
  Qed.

  Lemma sorted_memberships_unique : forall xs ys,
    X.KeySorted exact_key xs -> NoDup (X.keys exact_key xs) ->
    X.KeySorted exact_key ys -> NoDup (X.keys exact_key ys) ->
    (forall term, In term xs <-> In term ys) -> xs = ys.
  Proof.
    intros xs ys Left LU Right RU Members.
    apply (X.map_injective_on_lists Term nat exact_key exact_key_reflects).
    apply C.sorted_nodup_membership_unique; try assumption.
    intros code. unfold X.keys. repeat rewrite in_map_iff. split;
      intros [term [Equal Member]]; exists term; split; auto; now apply Members.
  Qed.

  Lemma pair_term_injective : forall pair x y, X.pair_term pair x = X.pair_term pair y -> x = y.
  Proof. intros pair [x xv] [y yv] Equal. unfold X.pair_term in Equal; simpl in Equal.
    injection Equal. intros. congruence. Qed.

  Lemma canonical_pair_vectors_unique : forall pair xs ys,
    X.MapCanonical exact_key xs -> X.MapCanonical exact_key ys ->
    Permutation (X.pair_terms pair xs) (X.pair_terms pair ys) ->
    X.pair_terms pair xs = X.pair_terms pair ys.
  Proof.
    intros pair xs ys Left Right Perm. f_equal.
    apply map_canonical_permutation_unique; try assumption.
    eapply X.map_reflects_permutation; [apply pair_term_injective|exact Perm].
  Qed.

  Lemma collection_children_reflect : forall operator xs ys,
    X.LocallyCanonical exact_key profile operator xs ->
    X.LocallyCanonical exact_key profile operator ys ->
    (forall x y, In x xs -> In y ys -> structural x = structural y -> x = y) ->
    collection_children operator (map structural xs) =
      collection_children operator (map structural ys) -> xs = ys.
  Proof.
    intros operator xs ys Left Right Reflect Equal.
    unfold X.LocallyCanonical in Left, Right. unfold collection_children in Equal.
    destruct (X.collection_kind profile operator) as [kind|] eqn:Kind.
    2: { eapply mapped_lists_reflect; eauto. }
    destruct kind as [| |pair|pair neutral set map_marker].
    - apply key_sorted_permutation_unique; try assumption.
      eapply mapped_permutations_reflect; [exact Reflect|].
      now apply ordered_reflects_permutation.
    - destruct Left as [Left LU], Right as [Right RU].
      apply sorted_memberships_unique; try assumption.
      eapply mapped_memberships_reflect; [exact Reflect|].
      now apply extensional_reflects_membership.
    - destruct Left as [left [L LC]], Right as [right [R RC]]. subst xs; subst ys.
      apply canonical_pair_vectors_unique; try assumption.
      eapply mapped_permutations_reflect; [exact Reflect|].
      now apply ordered_reflects_permutation.
    - pose proof (X.pathmap_markers_separate profile operator pair neutral set map_marker Kind)
        as [NS [NM SM]].
      destruct Left as [L|[[left [L [LS LU]]]|[left [L LC]]]];
      destruct Right as [R|[[right [R [RS RU]]]|[right [R RC]]]];
      subst xs; subst ys; simpl map in Equal;
      rewrite ?structural_marker, ?collection_children_empty in Equal; simpl in Equal.
      + reflexivity.
      + injection Equal as Modes Tail. unfold X.marker in Modes. congruence.
      + injection Equal as Modes Tail. unfold X.marker in Modes. congruence.
      + injection Equal as Modes Tail. unfold X.marker in Modes. congruence.
      + injection Equal as Tail. f_equal.
        apply key_sorted_permutation_unique; try assumption.
        eapply mapped_permutations_reflect.
        * intros x y Xmem Ymem Same. apply Reflect; [now right|now right|exact Same].
        * apply ordered_reflects_permutation. exact Tail.
      + injection Equal as Modes Tail. unfold X.marker in Modes. congruence.
      + injection Equal as Modes Tail. unfold X.marker in Modes. congruence.
      + injection Equal as Modes Tail. unfold X.marker in Modes. congruence.
      + injection Equal as Tail. f_equal.
        apply canonical_pair_vectors_unique; try assumption.
        eapply mapped_permutations_reflect.
        * intros x y Xmem Ymem Same. apply Reflect; [now right|now right|exact Same].
        * apply ordered_reflects_permutation. exact Tail.
  Qed.

  Theorem structural_reflects_canonical_terms : forall left right,
    X.CollectionCanonical exact_key profile left ->
    X.CollectionCanonical exact_key profile right ->
    structural left = structural right -> left = right.
  Proof.
    apply (E.term_induction (fun left => forall right,
      X.CollectionCanonical exact_key profile left ->
      X.CollectionCanonical exact_key profile right ->
      structural left = structural right -> left = right)).
    - intros variable [other|operator children] Left Right Equal;
        simpl in Equal; [now injection Equal|discriminate].
    - intros operator children IH [variable|other rest] Left Right Equal;
        simpl in Equal; [discriminate|].
      injection Equal as Operators Children. subst other. f_equal.
      inversion Left as [|? ? LocalLeft CanonLeft]; subst.
      inversion Right as [|? ? LocalRight CanonRight]; subst.
      eapply collection_children_reflect; [exact LocalLeft|exact LocalRight| |exact Children].
      intros x y Xmem Ymem Obs.
      rewrite Forall_forall in IH, CanonLeft, CanonRight.
      apply (IH x Xmem y); auto.
  Qed.

  Lemma structural_zero : structural E.zero = E.zero.
  Proof. apply structural_marker. Qed.
  Lemma structural_unit : structural E.unit = E.unit.
  Proof. apply structural_marker. Qed.
  Lemma structural_closure : forall term,
    structural (E.closure term) = E.closure (structural term).
  Proof.
    intros. change (LogicApplication 4 (collection_children 4 [structural term]) =
      E.closure (structural term)).
    unfold collection_children. rewrite equation_roles_are_positional by lia. reflexivity.
  Qed.

  Lemma structural_reflects_zero : forall term, structural term = E.zero -> term = E.zero.
  Proof.
    intros [variable|operator children] Equal; [discriminate|].
    simpl in Equal. unfold E.zero in Equal. injection Equal as Op Children. subst operator.
    unfold collection_children in Children.
    rewrite equation_roles_are_positional in Children by lia.
    destruct children; [reflexivity|discriminate].
  Qed.
  Lemma structural_reflects_unit : forall term, structural term = E.unit -> term = E.unit.
  Proof.
    intros [variable|operator children] Equal; [discriminate|].
    simpl in Equal. unfold E.unit in Equal. injection Equal as Op Children. subst operator.
    unfold collection_children in Children.
    rewrite equation_roles_are_positional in Children by lia.
    destruct children; [reflexivity|discriminate].
  Qed.
  Lemma structural_reflects_closure : forall term child,
    structural term = E.closure child -> exists original, term = E.closure original.
  Proof.
    intros [variable|operator children] child Equal; [discriminate|].
    simpl in Equal. unfold E.closure in Equal. injection Equal as Op Children. subst operator.
    unfold collection_children in Children.
    rewrite equation_roles_are_positional in Children by lia.
    destruct children as [|first [|second rest]]; try discriminate.
    exists first. reflexivity.
  Qed.

  Lemma structural_smart_node : forall operator children,
    Forall (X.CollectionCanonical exact_key profile) children ->
    (forall output, ~ E.RootStep (LogicApplication operator children) output) ->
    E.smart_node operator (map structural children) = LogicApplication operator (map structural children).
  Proof.
    intros operator children Canonical NoRoot.
    destruct operator as [|[|[|[|[|operator]]]]]; try reflexivity.
    - destruct children as [|a [|b [|c rest]]]; try reflexivity.
      simpl map. change (E.smart_alternative (structural a) (structural b) =
        E.alternative (structural a) (structural b)).
      unfold E.smart_alternative.
      destruct (E.term_eq_dec (structural a) E.zero) as [Z|Z].
      { apply structural_reflects_zero in Z. subst a. exfalso. apply (NoRoot b). constructor. }
      destruct (E.term_eq_dec (structural b) E.zero) as [Z'|Z'].
      { apply structural_reflects_zero in Z'. subst b. exfalso. apply (NoRoot a). constructor. }
      destruct (E.term_eq_dec (structural a) (structural b)) as [Same|Different]; [|reflexivity].
      assert (a = b).
      { apply structural_reflects_canonical_terms; try assumption;
          rewrite Forall_forall in Canonical; apply Canonical; simpl; auto. }
      subst b. exfalso. apply (NoRoot a). constructor.
    - destruct children as [|a [|b [|c rest]]]; try reflexivity.
      simpl map. change (E.smart_product (structural a) (structural b) =
        E.product (structural a) (structural b)).
      unfold E.smart_product.
      destruct (E.term_eq_dec (structural a) E.zero) as [Z|Z].
      { apply structural_reflects_zero in Z. subst a. exfalso. apply (NoRoot E.zero). constructor. }
      destruct (E.term_eq_dec (structural b) E.zero) as [Z'|Z'].
      { apply structural_reflects_zero in Z'. subst b. exfalso. apply (NoRoot E.zero). constructor. }
      destruct (E.term_eq_dec (structural a) E.unit) as [U|U].
      { apply structural_reflects_unit in U. subst a. exfalso. apply (NoRoot b). constructor. }
      destruct (E.term_eq_dec (structural b) E.unit) as [U'|U']; [|reflexivity].
      apply structural_reflects_unit in U'. subst b. exfalso. apply (NoRoot a). constructor.
    - destruct children as [|a [|b rest]]; try reflexivity.
      simpl map. change (E.smart_closure (structural a) = E.closure (structural a)).
      unfold E.smart_closure.
      destruct (E.term_eq_dec (structural a) E.zero) as [Z|Z].
      { apply structural_reflects_zero in Z. subst a. exfalso. apply (NoRoot E.unit). constructor. }
      destruct (E.term_eq_dec (structural a) E.unit) as [U|U].
      { apply structural_reflects_unit in U. subst a. exfalso. apply (NoRoot E.unit). constructor. }
      destruct (E.closure_child (structural a)) as [child|] eqn:Closed; [|reflexivity].
      apply E.closure_child_sound in Closed.
      apply structural_reflects_closure in Closed as [original Same]. subst a.
      exfalso. apply (NoRoot (E.closure original)). constructor.
  Qed.

  Theorem jointly_normal_observation_is_structural : forall term,
    X.CollectionCanonical exact_key profile term -> E.Normal term ->
    observe term = structural term.
  Proof.
    apply (E.term_induction (fun term =>
      X.CollectionCanonical exact_key profile term -> E.Normal term ->
      observe term = structural term)).
    - reflexivity.
    - intros operator children IH Canonical Normal.
      inversion Canonical as [|? ? Local Children]; subst.
      inversion Normal as [|? ? Normals NoRoot]; subst.
      assert (Equal : map observe children = map structural children).
      { apply map_ext_in. intros term Member. rewrite Forall_forall in IH, Children, Normals.
        apply (IH term Member); auto. }
      change (observed_node operator (map observe children) =
        LogicApplication operator (collection_children operator (map structural children))).
      rewrite Equal. unfold observed_node.
      destruct (X.collection_kind profile operator) eqn:Kind; [reflexivity|].
      unfold collection_children. rewrite Kind. now apply structural_smart_node.
  Qed.

  Theorem observation_reflects_jointly_normal_terms : forall left right,
    X.CollectionCanonical exact_key profile left -> E.Irreducible left ->
    X.CollectionCanonical exact_key profile right -> E.Irreducible right ->
    observe left = observe right -> left = right.
  Proof.
    intros left right LC LN RC RN Equal.
    rewrite !jointly_normal_observation_is_structural in Equal;
      try assumption; try now apply E.irreducible_is_normal.
    eapply structural_reflects_canonical_terms; eauto.
  Qed.

  Lemma observe_zero : observe E.zero = E.zero.
  Proof.
    change (observed_node 0 [] = E.zero). unfold observed_node.
    rewrite equation_roles_are_positional by lia. reflexivity.
  Qed.
  Lemma observe_unit : observe E.unit = E.unit.
  Proof.
    change (observed_node 1 [] = E.unit). unfold observed_node.
    rewrite equation_roles_are_positional by lia. reflexivity.
  Qed.
  Lemma observe_alternative : forall a b,
    observe (E.alternative a b) = E.smart_alternative (observe a) (observe b).
  Proof.
    intros. change (observed_node 2 [observe a; observe b] =
      E.smart_alternative (observe a) (observe b)). unfold observed_node.
    rewrite equation_roles_are_positional by lia. reflexivity.
  Qed.
  Lemma observe_product : forall a b,
    observe (E.product a b) = E.smart_product (observe a) (observe b).
  Proof.
    intros. change (observed_node 3 [observe a; observe b] =
      E.smart_product (observe a) (observe b)). unfold observed_node.
    rewrite equation_roles_are_positional by lia. reflexivity.
  Qed.
  Lemma observe_closure : forall a,
    observe (E.closure a) = E.smart_closure (observe a).
  Proof.
    intros. change (observed_node 4 [observe a] = E.smart_closure (observe a)). unfold observed_node.
    rewrite equation_roles_are_positional by lia. reflexivity.
  Qed.

  Lemma equation_root_preserves_observation : forall left right,
    E.RootStep left right -> observe left = observe right.
  Proof.
    intros left right Step. destruct Step;
      rewrite ?observe_alternative, ?observe_product, ?observe_closure,
        ?observe_zero, ?observe_unit;
      auto using E.smart_alternative_zero_left, E.smart_alternative_zero_right,
        E.smart_alternative_idempotent, E.smart_product_zero_left,
        E.smart_product_zero_right, E.smart_product_unit_left, E.smart_product_unit_right,
        E.smart_closure_zero, E.smart_closure_unit, E.smart_closure_idempotent.
  Qed.
  Lemma context_preserves_observation : forall operator before after left right,
    observe left = observe right ->
    observe (LogicApplication operator (before ++ left :: after)) =
      observe (LogicApplication operator (before ++ right :: after)).
  Proof.
    intros operator before after left right Equal. simpl. rewrite !map_app. simpl.
    now rewrite Equal.
  Qed.
  Lemma equations_preserve_observation : forall left right,
    E.Congruence left right -> observe left = observe right.
  Proof.
    intros left right Equal. induction Equal; eauto using
      equation_root_preserves_observation, context_preserves_observation; congruence.
  Qed.

  Lemma collections_preserve_observation : forall left right,
    X.CollectionEquality profile left right -> observe left = observe right.
  Proof.
    intros left right Equal. destruct Equal;
      cbn [observe];
      unfold observed_node, collection_children; rewrite H.
    - f_equal. apply ordered_extensional. now apply Permutation_map.
    - f_equal. apply extensional_extensional. intros term.
      repeat rewrite in_map_iff. split; intros [child [Equal Member]];
        exists child; split; auto; now apply H0.
    - f_equal. apply ordered_extensional. apply Permutation_map.
      unfold X.pair_terms. now apply Permutation_map.
    - reflexivity.
    - simpl. f_equal. f_equal. apply ordered_extensional. now apply Permutation_map.
    - simpl. f_equal. f_equal. apply ordered_extensional. apply Permutation_map.
      unfold X.pair_terms. now apply Permutation_map.
  Qed.

  Theorem combined_congruence_preserves_observation : forall left right,
    X.CombinedCongruence profile left right -> observe left = observe right.
  Proof.
    intros left right Equal. induction Equal; eauto using
      equations_preserve_observation, collections_preserve_observation,
      context_preserves_observation; congruence.
  Qed.

  Theorem combined_joint_normal_forms_are_unique : forall left right,
    X.CombinedCongruence profile left right ->
    X.CollectionCanonical exact_key profile left -> E.Irreducible left ->
    X.CollectionCanonical exact_key profile right -> E.Irreducible right -> left = right.
  Proof.
    intros left right Equal LC LN RC RN.
    apply observation_reflects_jointly_normal_terms; try assumption.
    now apply combined_congruence_preserves_observation.
  Qed.

  Theorem successful_runs_agree : forall input ready_left ready_right left right nl nr,
    X.InitialPass exact_key profile input ready_left ->
    X.Coordination exact_key profile nl ready_left left ->
    X.InitialPass exact_key profile input ready_right ->
    X.Coordination exact_key profile nr ready_right right -> left = right.
  Proof.
    intros input ready_left ready_right left right nl nr FirstL RunL FirstR RunR.
    pose proof (X.accepted_coordination_is_sound_and_jointly_normal
      exact_key exact_key_reflects profile _ _ _ _ FirstL RunL)
      as [SoundL [CanonL [NormalL BoundL]]].
    pose proof (X.accepted_coordination_is_sound_and_jointly_normal
      exact_key exact_key_reflects profile _ _ _ _ FirstR RunR)
      as [SoundR [CanonR [NormalR BoundR]]].
    apply combined_joint_normal_forms_are_unique; try assumption.
    eapply X.combined_trans; [apply X.combined_sym; exact SoundL|exact SoundR].
  Qed.

  Theorem successful_rerun_is_idempotent : forall input ready output count rerun_ready rerun n,
    X.InitialPass exact_key profile input ready ->
    X.Coordination exact_key profile count ready output ->
    X.InitialPass exact_key profile output rerun_ready ->
    X.Coordination exact_key profile n rerun_ready rerun -> rerun = output.
  Proof.
    intros input ready output count rerun_ready rerun n First Run Next Rerun.
    pose proof (X.accepted_coordination_is_sound_and_jointly_normal
      exact_key exact_key_reflects profile _ _ _ _ First Run)
      as [Sound [Canon [Normal Bound]]].
    pose proof (X.accepted_coordination_is_sound_and_jointly_normal
      exact_key exact_key_reflects profile _ _ _ _ Next Rerun)
      as [RerunSound [RerunCanon [RerunNormal RerunBound]]].
    apply combined_joint_normal_forms_are_unique; try assumption.
    now apply X.combined_sym.
  Qed.
End Observation.

Print Assumptions nat_sorted_permutation_unique.
Print Assumptions sorted_unique_key_permutation.
Print Assumptions structural_reflects_canonical_terms.
Print Assumptions jointly_normal_observation_is_structural.
Print Assumptions observation_reflects_jointly_normal_terms.
Print Assumptions combined_congruence_preserves_observation.
Print Assumptions combined_joint_normal_forms_are_unique.
Print Assumptions successful_runs_agree.
Print Assumptions successful_rerun_is_idempotent.

End SourceEquationCollectionUniqueness.
