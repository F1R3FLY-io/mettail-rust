From Stdlib Require Import List Bool PeanoNat.
Import ListNotations.

Module RewriteFamilyContext.

Inductive Syntax :=
| Atom (name : nat)
| Unary (tag : nat) (element : Syntax)
| Binary (tag : nat) (left right : Syntax)
| Arrow (domain codomain : Syntax)
| Rewrite (result : Syntax)
| Invalid.

Fixpoint ordinary value :=
  match value with
  | Atom _ => true
  | Unary _ element => ordinary element
  | Binary _ lhs rhs | Arrow lhs rhs => ordinary lhs && ordinary rhs
  | Rewrite _ | Invalid => false
  end.

Inductive FamilyShape : Syntax -> list Syntax -> Syntax -> Prop :=
| FamilyEnd : forall result, ordinary result = true ->
    FamilyShape (Rewrite result) [] result
| FamilyArrow : forall domain tail domains result,
    ordinary domain = true -> FamilyShape tail domains result ->
    FamilyShape (Arrow domain tail) (domain :: domains) result.

Fixpoint read_family value : option (list Syntax * Syntax) :=
  match value with
  | Rewrite result => if ordinary result then Some ([], result) else None
  | Arrow domain tail =>
      if ordinary domain then
        match read_family tail with
        | Some (domains, result) => Some (domain :: domains, result)
        | None => None
        end
      else None
  | _ => None
  end.

Fixpoint scan_family value reverse_domains : option (list Syntax * Syntax) :=
  match value with
  | Rewrite result =>
      if ordinary result then Some (rev reverse_domains, result) else None
  | Arrow domain tail =>
      if ordinary domain then scan_family tail (domain :: reverse_domains) else None
  | _ => None
  end.

Theorem family_decoder_matches_the_independent_shape : forall value domains result,
  read_family value = Some (domains, result) <-> FamilyShape value domains result.
Proof.
  intros value. induction value; intros domains result; simpl;
    try (split; [discriminate|intros H; inversion H]).
  - destruct (ordinary value1) eqn:Hdomain.
    + destruct (read_family value2) as [[tail ending]|] eqn:Htail.
      * split.
        -- intros H. inversion H; subst. constructor; [exact Hdomain|].
           now apply IHvalue2.
        -- intros H. inversion H; subst. apply IHvalue2 in H5.
           inversion H5. reflexivity.
      * split; [discriminate|]. intros H. inversion H; subst.
        apply IHvalue2 in H5. discriminate.
    + split; [discriminate|]. intros H. inversion H; subst. congruence.
  - destruct (ordinary value) eqn:Hresult.
    + split.
      * intros H. inversion H; subst. now constructor.
      * intros H. inversion H; subst. reflexivity.
    + split; [discriminate|]. intros H. inversion H; subst. congruence.
Qed.

Theorem family_shape_preserves_complete_domain_and_result_types :
  forall value domains result, FamilyShape value domains result ->
  Forall (fun domain => ordinary domain = true) domains /\ ordinary result = true.
Proof.
  intros value domains result H. induction H; simpl.
  - split; [constructor|assumption].
  - destruct IHFamilyShape. split; [now constructor|assumption].
Qed.

Theorem family_shapes_are_disjoint_from_ordinary_types :
  forall value domains result, FamilyShape value domains result -> ordinary value = false.
Proof.
  intros value domains result H. induction H; simpl; [reflexivity|].
  now rewrite H, IHFamilyShape.
Qed.

Theorem codomain_scan_preserves_the_ordered_domain_roster :
  forall value reverse_domains,
  scan_family value reverse_domains =
    option_map (fun pair => (rev reverse_domains ++ fst pair, snd pair)) (read_family value).
Proof.
  intros value. induction value; intros reverse_domains; simpl; try reflexivity.
  - destruct (ordinary value1); simpl; [|reflexivity].
    rewrite IHvalue2. destruct (read_family value2) as [[domains result]|];
      simpl; [|reflexivity]. now rewrite <- app_assoc.
  - destruct (ordinary value); simpl; [|reflexivity]. now rewrite app_nil_r.
Qed.

Definition assemble domains result := fold_right Arrow (Rewrite result) domains.

Theorem encoded_family_context_round_trips : forall domains result,
  Forall (fun domain => ordinary domain = true) domains -> ordinary result = true ->
  scan_family (assemble domains result) [] = Some (domains, result).
Proof.
  intros domains result Hdomains Hresult.
  rewrite codomain_scan_preserves_the_ordered_domain_roster.
  assert (Hshape : FamilyShape (assemble domains result) domains result).
  { induction Hdomains; unfold assemble in *; simpl; now constructor. }
  apply family_decoder_matches_the_independent_shape in Hshape.
  now rewrite Hshape.
Qed.

Inductive ContextType := Ordinary (value : Syntax) | Family (domains : list Syntax) (result : Syntax).

Definition decode_context (allow_family : bool) value :=
  if ordinary value then Some (Ordinary value)
  else if allow_family then
    option_map (fun pair => Family (fst pair) (snd pair)) (scan_family value [])
  else None.

Theorem ordinary_contexts_keep_the_exact_legacy_value : forall allow_family value,
  ordinary value = true -> decode_context allow_family value = Some (Ordinary value).
Proof. intros. unfold decode_context. now rewrite H. Qed.

Theorem ordinary_context_admission_is_exact : forall allow_family value decoded,
  decode_context allow_family value = Some (Ordinary decoded) <->
  ordinary value = true /\ decoded = value.
Proof.
  intros. unfold decode_context. destruct (ordinary value) eqn:Hordinary.
  - split; intros H; [inversion H; auto|destruct H; now subst].
  - destruct allow_family; simpl.
    + destruct (scan_family value []) as [[domains result]|]; simpl;
        split; intros H; [discriminate|destruct H; discriminate|discriminate|destruct H; discriminate].
    + split; intros H; [discriminate|destruct H; discriminate].
Qed.

Theorem family_context_admission_is_exact : forall allow_family value domains result,
  decode_context allow_family value = Some (Family domains result) <->
  allow_family = true /\ FamilyShape value domains result.
Proof.
  intros allow_family value domains result. split.
  - unfold decode_context. destruct (ordinary value) eqn:Hordinary; [discriminate|].
    destruct allow_family; [|discriminate].
    rewrite codomain_scan_preserves_the_ordered_domain_roster.
    destruct (read_family value) as [[found ending]|] eqn:Hfound; simpl; [|discriminate].
    intros H. inversion H; subst. split; [reflexivity|].
    now apply family_decoder_matches_the_independent_shape.
  - intros [Hallow Hshape]. subst. unfold decode_context.
    rewrite (family_shapes_are_disjoint_from_ordinary_types _ _ _ Hshape).
    rewrite codomain_scan_preserves_the_ordered_domain_roster.
    apply family_decoder_matches_the_independent_shape in Hshape.
    now rewrite Hshape.
Qed.

Theorem equation_and_intrinsic_contexts_cannot_admit_families :
  forall value domains result, decode_context false value <> Some (Family domains result).
Proof.
  intros value domains result H. apply family_context_admission_is_exact in H.
  destruct H. discriminate.
Qed.

Theorem nested_rewrite_in_a_domain_is_refused : forall domain tail result,
  scan_family (Arrow (Rewrite domain) tail) [] = None /\
  scan_family (Rewrite (Rewrite result)) [] = None.
Proof. intros. split; reflexivity. Qed.

End RewriteFamilyContext.

Print Assumptions RewriteFamilyContext.family_decoder_matches_the_independent_shape.
Print Assumptions RewriteFamilyContext.family_shape_preserves_complete_domain_and_result_types.
Print Assumptions RewriteFamilyContext.family_shapes_are_disjoint_from_ordinary_types.
Print Assumptions RewriteFamilyContext.codomain_scan_preserves_the_ordered_domain_roster.
Print Assumptions RewriteFamilyContext.encoded_family_context_round_trips.
Print Assumptions RewriteFamilyContext.ordinary_contexts_keep_the_exact_legacy_value.
Print Assumptions RewriteFamilyContext.ordinary_context_admission_is_exact.
Print Assumptions RewriteFamilyContext.family_context_admission_is_exact.
Print Assumptions RewriteFamilyContext.equation_and_intrinsic_contexts_cannot_admit_families.
Print Assumptions RewriteFamilyContext.nested_rewrite_in_a_domain_is_refused.
