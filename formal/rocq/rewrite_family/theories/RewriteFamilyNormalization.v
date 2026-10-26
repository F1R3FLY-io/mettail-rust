From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.

Module RewriteFamilyNormalization.

Record Binding := binding {
  binder_identity : nat;
  binder_category : nat
}.

Definition binding_eqb (left right : Binding) :=
  Nat.eqb (binder_identity left) (binder_identity right) &&
  Nat.eqb (binder_category left) (binder_category right).

Lemma binding_eqb_spec : forall left right,
  binding_eqb left right = true <-> left = right.
Proof.
  intros [li lc] [ri rc]. unfold binding_eqb. simpl.
  rewrite andb_true_iff, !Nat.eqb_eq. split.
  - intros [-> ->]. reflexivity.
  - intros H. inversion H. auto.
Qed.

Definition binding_member (item : Binding) (scope : list Binding) :=
  existsb (binding_eqb item) scope.

Lemma binding_member_spec : forall item scope,
  binding_member item scope = true <-> In item scope.
Proof.
  intros item scope. unfold binding_member. rewrite existsb_exists. split.
  - intros [other [Hin Heq]]. apply binding_eqb_spec in Heq. now subst other.
  - intros Hin. exists item. split; [assumption|apply binding_eqb_spec; reflexivity].
Qed.

Fixpoint distinct_ids (scope : list Binding) :=
  match scope with
  | [] => true
  | item :: rest =>
      negb (existsb (Nat.eqb (binder_identity item)) (map binder_identity rest)) &&
      distinct_ids rest
  end.

Lemma distinct_ids_spec : forall scope,
  distinct_ids scope = true <-> NoDup (map binder_identity scope).
Proof.
  induction scope as [|item rest IH]; simpl.
  - split; intros; constructor.
  - rewrite andb_true_iff, negb_true_iff, IH.
    assert (Hmember : existsb (Nat.eqb (binder_identity item))
      (map binder_identity rest) = true <->
      In (binder_identity item) (map binder_identity rest)).
    { rewrite existsb_exists. split.
      - intros [other [Hin Heq]]. apply Nat.eqb_eq in Heq. now subst other.
      - intros Hin. exists (binder_identity item). now rewrite Nat.eqb_refl. }
    split.
    + intros [Hfalse Hnodup]. constructor; [|assumption].
      intros Hin. apply Hmember in Hin. congruence.
    + intros Hnodup. inversion Hnodup as [|? ? Hnot Hrest]. split; [|assumption].
      destruct (existsb _ _) eqn:Hfound; [|reflexivity].
      exfalso. apply Hnot. apply Hmember. reflexivity.
Qed.

Record Family := family {
  family_domains : list nat;
  family_result : nat
}.

Definition family_check declared descriptor ambient introduced arguments :=
  forallb (fun category => existsb (Nat.eqb category) declared)
    (family_result descriptor :: family_domains descriptor) &&
  (if list_eq_dec Nat.eq_dec (map binder_category arguments)
      (family_domains descriptor) then true else false) &&
  distinct_ids arguments &&
  forallb (fun item => binding_member item (ambient ++ introduced)) arguments &&
  forallb (fun item => binding_member item arguments) introduced &&
  distinct_ids (ambient ++ introduced).

Definition FamilyWellTyped declared descriptor ambient introduced arguments :=
  (forall category, In category
      (family_result descriptor :: family_domains descriptor) -> In category declared) /\
  map binder_category arguments = family_domains descriptor /\
  NoDup (map binder_identity arguments) /\
  (forall item, In item arguments -> In item (ambient ++ introduced)) /\
  (forall item, In item introduced -> In item arguments) /\
  NoDup (map binder_identity (ambient ++ introduced)).

Lemma category_member_spec : forall category declared,
  existsb (Nat.eqb category) declared = true <-> In category declared.
Proof.
  intros category declared. rewrite existsb_exists. split.
  - intros [other [Hin Heq]]. apply Nat.eqb_eq in Heq. now subst other.
  - intros Hin. exists category. now rewrite Nat.eqb_refl.
Qed.

Theorem family_check_is_exact : forall declared descriptor ambient introduced arguments,
  family_check declared descriptor ambient introduced arguments = true <->
  FamilyWellTyped declared descriptor ambient introduced arguments.
Proof.
  intros. unfold family_check, FamilyWellTyped.
  rewrite !andb_true_iff, !forallb_forall, !distinct_ids_spec.
  assert (Hdomains : (if list_eq_dec Nat.eq_dec (map binder_category arguments)
    (family_domains descriptor) then true else false) = true <->
    map binder_category arguments = family_domains descriptor).
  { destruct (list_eq_dec Nat.eq_dec _ _); intuition discriminate. }
  rewrite Hdomains. setoid_rewrite binding_member_spec.
  setoid_rewrite category_member_spec. tauto.
Qed.

Theorem accepted_family_has_exact_arity : forall declared descriptor ambient introduced arguments,
  family_check declared descriptor ambient introduced arguments = true ->
  length arguments = length (family_domains descriptor).
Proof.
  intros. apply family_check_is_exact in H. destruct H as [_ [Hdomains _]].
  rewrite <- Hdomains, length_map. reflexivity.
Qed.

Theorem accepted_family_has_no_escaped_argument :
  forall declared descriptor ambient introduced arguments item,
  family_check declared descriptor ambient introduced arguments = true ->
  In item arguments -> In item (ambient ++ introduced).
Proof.
  intros. apply family_check_is_exact in H.
  destruct H as [_ [_ [_ [Hscope _]]]]. now apply Hscope.
Qed.

Theorem accepted_family_covers_each_introduced_binder :
  forall declared descriptor ambient introduced arguments item,
  family_check declared descriptor ambient introduced arguments = true ->
  In item introduced -> In item arguments.
Proof.
  intros. apply family_check_is_exact in H.
  destruct H as [_ [_ [_ [_ [Hcoverage _]]]]]. now apply Hcoverage.
Qed.

Theorem accepted_family_has_distinct_lexical_occurrences :
  forall declared descriptor ambient introduced arguments,
  family_check declared descriptor ambient introduced arguments = true ->
  NoDup (map binder_identity (ambient ++ introduced)).
Proof.
  intros. apply family_check_is_exact in H. unfold FamilyWellTyped in H. tauto.
Qed.

Lemma member_bounded_by_maximum : forall items item,
  In item items -> item <= fold_right Nat.max 0 items.
Proof.
  induction items as [|head rest IH]; intros item Hin; simpl in *.
  - contradiction.
  - destruct Hin as [->|Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Definition next_identity scope := S (fold_right Nat.max 0 (map binder_identity scope)).

Theorem generated_identity_is_fresh : forall scope,
  ~ In (next_identity scope) (map binder_identity scope).
Proof.
  intros scope Hin. apply member_bounded_by_maximum in Hin.
  unfold next_identity in Hin. lia.
Qed.

Theorem scope_extension_preserves_distinct_identities : forall scope category,
  NoDup (map binder_identity scope) ->
  NoDup (map binder_identity (binding (next_identity scope) category :: scope)).
Proof. intros. simpl. constructor; [apply generated_identity_is_fresh|assumption]. Qed.

Theorem duplicate_lexical_occurrence_is_refused :
  family_check [0] (family [0] 0) [] [binding 0 0; binding 0 0] [binding 0 0] = false.
Proof. reflexivity. Qed.

Record NamedBinding := named_binding {
  binder_spelling : nat;
  resolved_binding : Binding
}.

Fixpoint resolve_lexical spelling scope :=
  match scope with
  | [] => None
  | item :: rest =>
      if Nat.eqb spelling (binder_spelling item)
      then Some (resolved_binding item)
      else resolve_lexical spelling rest
  end.

Theorem nearest_lexical_binder_wins : forall spelling identity category scope,
  resolve_lexical spelling (named_binding spelling (binding identity category) :: scope) =
  Some (binding identity category).
Proof. intros. simpl. now rewrite Nat.eqb_refl. Qed.

Theorem shadowed_binders_keep_distinct_identities :
  forall spelling inner outer category scope,
  inner <> outer ->
  resolve_lexical spelling
    (named_binding spelling (binding inner category) ::
     named_binding spelling (binding outer category) :: scope) <>
  Some (binding outer category).
Proof.
  intros. rewrite nearest_lexical_binder_wins. intros Heq. inversion Heq. contradiction.
Qed.

Inductive Value :=
| Atom (literal : nat)
| Bound (reference : Binding)
| Node (constructor : nat) (children : list Value)
| Bind (binders : list Binding) (body : Value).

Inductive Context :=
| Hole
| NodeContext (constructor : nat) (before : list Value) (inside : Context) (after : list Value)
| BinderContext (binders : list Binding) (inside : Context).

Fixpoint introduced_scope context :=
  match context with
  | Hole => []
  | NodeContext _ _ inside _ => introduced_scope inside
  | BinderContext binders inside => binders ++ introduced_scope inside
  end.

Fixpoint plug context endpoint :=
  match context with
  | Hole => endpoint
  | NodeContext constructor before inside after =>
      Node constructor (before ++ plug inside endpoint :: after)
  | BinderContext binders inside => Bind binders (plug inside endpoint)
  end.

Inductive CorePattern :=
| Meta (name : nat)
| NodePattern (constructor : nat) (before : list Value) (inside : CorePattern) (after : list Value)
| BinderPattern (binders : list Binding) (inside : CorePattern).

Fixpoint normalize context variable :=
  match context with
  | Hole => Meta variable
  | NodeContext constructor before inside after =>
      NodePattern constructor before (normalize inside variable) after
  | BinderContext binders inside => BinderPattern binders (normalize inside variable)
  end.

Definition Environment := nat -> option Value.

Inductive Matches (environment : Environment) : CorePattern -> Value -> Prop :=
| matches_meta : forall name value,
    environment name = Some value -> Matches environment (Meta name) value
| matches_node : forall constructor before inside after child,
    Matches environment inside child ->
    Matches environment (NodePattern constructor before inside after)
      (Node constructor (before ++ child :: after))
| matches_binder : forall binders inside child,
    Matches environment inside child ->
    Matches environment (BinderPattern binders inside) (Bind binders child).

Fixpoint reconstruct pattern (environment : Environment) :=
  match pattern with
  | Meta variable => environment variable
  | NodePattern constructor before inside after =>
      match reconstruct inside environment with
      | Some child => Some (Node constructor (before ++ child :: after))
      | None => None
      end
  | BinderPattern binders inside =>
      match reconstruct inside environment with
      | Some child => Some (Bind binders child)
      | None => None
      end
  end.

Theorem normalized_matching_extracts_exact_endpoint : forall context variable environment value,
  Matches environment (normalize context variable) value <->
  exists endpoint, environment variable = Some endpoint /\ value = plug context endpoint.
Proof.
  induction context as [|constructor before inside IH after|binders inside IH];
    intros variable environment value; simpl.
  - split.
    + intros H. inversion H. subst. eauto.
    + intros [endpoint [Hlookup ->]]. now constructor.
  - split.
    + intros H. inversion H. subst.
      match goal with Hchild : Matches _ (normalize _ _) _ |- _ =>
        apply IH in Hchild; destruct Hchild as [endpoint [Hlookup ->]] end.
      eauto.
    + intros [endpoint [Hlookup ->]]. constructor. apply IH. eauto.
  - split.
    + intros H. inversion H. subst.
      match goal with Hchild : Matches _ (normalize _ _) _ |- _ =>
        apply IH in Hchild; destruct Hchild as [endpoint [Hlookup ->]] end.
      eauto.
    + intros [endpoint [Hlookup ->]]. constructor. apply IH. eauto.
Qed.

Theorem normalized_reconstruction_preserves_context : forall context variable environment,
  reconstruct (normalize context variable) environment =
  option_map (plug context) (environment variable).
Proof.
  induction context as [|constructor before inside IH after|binders inside IH];
    intros; simpl.
  - destruct (environment variable); reflexivity.
  - rewrite IH. destruct (environment variable); reflexivity.
  - rewrite IH. destruct (environment variable); reflexivity.
Qed.

Definition write_binding (environment : Environment) name value : Environment :=
  fun candidate => if Nat.eqb candidate name then Some value else environment candidate.

Theorem write_binding_reads_exact_value : forall environment name value,
  write_binding environment name value name = Some value.
Proof. intros. unfold write_binding. now rewrite Nat.eqb_refl. Qed.

Theorem fresh_extension_preserves_other_bindings : forall environment name value other,
  other <> name -> write_binding environment name value other = environment other.
Proof. intros. unfold write_binding. apply Nat.eqb_neq in H. now rewrite H. Qed.

Definition SourceStep
    (step : list Binding -> nat -> Value -> Value -> Prop)
    ambient descriptor context input output :=
  exists source target,
    step (ambient ++ introduced_scope context) (family_result descriptor) source target /\
    input = plug context source /\ output = plug context target.

Inductive PremiseExecution
    (step : list Binding -> nat -> Value -> Value -> Prop)
    (scope : list Binding) (category source_name target_name : nat) :
    Environment -> Environment -> Prop :=
| execute_transition : forall initial source target,
    initial source_name = Some source ->
    initial target_name = None ->
    step scope category source target ->
    PremiseExecution step scope category source_name target_name initial
      (write_binding initial target_name target).

Definition CoreStep step ambient descriptor context source_name target_name
    (prior : Environment) input output :=
  exists matched final,
    Matches matched (normalize context source_name) input /\
    (forall other, other <> source_name -> matched other = prior other) /\
    PremiseExecution step (ambient ++ introduced_scope context)
      (family_result descriptor) source_name target_name matched final /\
    reconstruct (normalize context target_name) final = Some output.

Theorem explicit_family_step_iff_existing_premise :
  forall step ambient descriptor context source_name target_name prior input output,
  source_name <> target_name -> prior source_name = None -> prior target_name = None ->
  (SourceStep step ambient descriptor context input output <->
   CoreStep step ambient descriptor context source_name target_name prior input output).
Proof.
  intros step ambient descriptor context source_name target_name prior input output
    Hdistinct Hsourcefresh Hfresh. split.
  - intros [source [target [Hstep [-> ->]]]].
    exists (write_binding prior source_name source).
    exists (write_binding (write_binding prior source_name source) target_name target).
    split.
    + apply normalized_matching_extracts_exact_endpoint.
      exists source. split; [apply write_binding_reads_exact_value|reflexivity].
    + split.
      * intros. now apply fresh_extension_preserves_other_bindings.
      * split.
        -- econstructor.
           ++ apply write_binding_reads_exact_value.
           ++ rewrite fresh_extension_preserves_other_bindings; congruence.
           ++ exact Hstep.
        -- rewrite normalized_reconstruction_preserves_context,
             write_binding_reads_exact_value. reflexivity.
  - intros [matched [final [Hmatch [_ [Hpremise Hreconstruct]]]]].
    apply normalized_matching_extracts_exact_endpoint in Hmatch.
    destruct Hmatch as [source [Hlookup Hinput]].
    inversion Hpremise; subst.
    match goal with Hother : matched source_name = Some _ |- _ =>
      rewrite Hlookup in Hother; inversion Hother; subst end.
    rewrite normalized_reconstruction_preserves_context,
      write_binding_reads_exact_value in Hreconstruct.
    inversion Hreconstruct. subst. unfold SourceStep. eauto.
Qed.

Theorem transition_premise_preserves_metavariable_bindings :
  forall step scope category source_name target_name initial final other,
  PremiseExecution step scope category source_name target_name initial final ->
  other <> target_name -> final other = initial other.
Proof.
  intros. inversion H. subst. now apply fresh_extension_preserves_other_bindings.
Qed.

Theorem bound_target_refuses_transition :
  forall step scope category source_name target_name initial final existing,
  initial target_name = Some existing ->
  ~ PremiseExecution step scope category source_name target_name initial final.
Proof. intros. intros Hrun. inversion Hrun. congruence. Qed.

Theorem generated_pair_preserves_prior_environment :
  forall prior source_name source target_name target other,
  other <> source_name -> other <> target_name ->
  write_binding (write_binding prior source_name source) target_name target other = prior other.
Proof.
  intros. rewrite fresh_extension_preserves_other_bindings by assumption.
  now apply fresh_extension_preserves_other_bindings.
Qed.

Inductive Sort :=
| Category (name : nat)
| Arrow (domains : list nat) (codomain : Sort).

Definition Signature := nat -> option (list Sort * Sort).
Definition LiteralTypes := nat -> option Sort.

Inductive TypedValue (signature : Signature) (literal_types : LiteralTypes) :
    list Binding -> Value -> Sort -> Prop :=
| typed_atom : forall scope literal sort,
    literal_types literal = Some sort ->
    TypedValue signature literal_types scope (Atom literal) sort
| typed_bound : forall scope reference,
    In reference scope ->
    TypedValue signature literal_types scope (Bound reference)
      (Category (binder_category reference))
| typed_node : forall scope constructor children arguments result,
    signature constructor = Some (arguments, result) ->
    Forall2 (TypedValue signature literal_types scope) children arguments ->
    TypedValue signature literal_types scope (Node constructor children) result
| typed_binder : forall scope binders body result,
    NoDup (map binder_identity (scope ++ binders)) ->
    TypedValue signature literal_types (scope ++ binders) body result ->
    TypedValue signature literal_types scope (Bind binders body)
      (Arrow (map binder_category binders) result).

Inductive TypedContext (signature : Signature) (literal_types : LiteralTypes) :
    list Binding -> Sort -> Context -> Sort -> Prop :=
| typed_hole : forall scope hole_sort,
    TypedContext signature literal_types scope hole_sort Hole hole_sort
| typed_node_context :
    forall scope hole_sort constructor before inside after before_sorts inside_sort after_sorts result,
    signature constructor = Some (before_sorts ++ inside_sort :: after_sorts, result) ->
    Forall2 (TypedValue signature literal_types scope) before before_sorts ->
    Forall2 (TypedValue signature literal_types scope) after after_sorts ->
    TypedContext signature literal_types scope hole_sort inside inside_sort ->
    TypedContext signature literal_types scope hole_sort
      (NodeContext constructor before inside after) result
| typed_binder_context : forall scope hole_sort binders inside result,
    NoDup (map binder_identity (scope ++ binders)) ->
    TypedContext signature literal_types (scope ++ binders) hole_sort inside result ->
    TypedContext signature literal_types scope hole_sort (BinderContext binders inside)
      (Arrow (map binder_category binders) result).

Theorem typed_context_plugging_preserves_endpoint_type :
  forall signature literal_types scope hole_sort context result endpoint,
  TypedContext signature literal_types scope hole_sort context result ->
  TypedValue signature literal_types (scope ++ introduced_scope context) endpoint hole_sort ->
  TypedValue signature literal_types scope (plug context endpoint) result.
Proof.
  intros signature literal_types scope hole_sort context result endpoint Hcontext.
  induction Hcontext; intros Hendpoint; simpl in *.
  - now rewrite app_nil_r in Hendpoint.
  - eapply typed_node; [eassumption|].
    apply Forall2_app; [eassumption|]. constructor; [now apply IHHcontext|assumption].
  - apply typed_binder; [assumption|]. apply IHHcontext.
    now rewrite <- app_assoc.
Qed.

Theorem typed_bound_reference_is_in_scope :
  forall signature literal_types scope reference sort,
  TypedValue signature literal_types scope (Bound reference) sort -> In reference scope.
Proof. intros. inversion H. assumption. Qed.

Theorem typed_constructor_has_exact_arity :
  forall signature literal_types scope constructor children sort arguments,
  TypedValue signature literal_types scope (Node constructor children) sort ->
  signature constructor = Some (arguments, sort) -> length children = length arguments.
Proof.
  intros. inversion H. subst.
  match goal with Hsig : signature constructor = Some _ |- _ =>
    rewrite H0 in Hsig; inversion Hsig; subst end.
  clear H H0 H4. induction H6; simpl; congruence.
Qed.

Definition OpenStep signature literal_types
    (step : list Binding -> nat -> Value -> Value -> Prop)
    scope category source target :=
  TypedValue signature literal_types scope source (Category category) /\
  step scope category source target /\
  TypedValue signature literal_types scope target (Category category).

Definition AdmittedFamily declared signature literal_types ambient descriptor arguments
    context result :=
  family_check declared descriptor ambient (introduced_scope context) arguments = true /\
  TypedContext signature literal_types ambient (Category (family_result descriptor)) context result.

Theorem checked_family_execution_preserves_parent_types :
  forall declared signature literal_types ambient descriptor arguments context result step input output,
  AdmittedFamily declared signature literal_types ambient descriptor arguments context result ->
  SourceStep (OpenStep signature literal_types step) ambient descriptor context input output ->
  TypedValue signature literal_types ambient input result /\
  TypedValue signature literal_types ambient output result.
Proof.
  intros declared signature literal_types ambient descriptor arguments context result step input output
    [Hcheck Hcontext] [source [target [[Hsource [Hstep Htarget]] [-> ->]]]].
  split; eapply typed_context_plugging_preserves_endpoint_type; eassumption.
Qed.

Theorem checked_family_matching_and_reconstruction_are_equivalent :
  forall declared signature literal_types ambient descriptor arguments context result step
    source_name target_name prior input output,
  AdmittedFamily declared signature literal_types ambient descriptor arguments context result ->
  source_name <> target_name -> prior source_name = None -> prior target_name = None ->
  (SourceStep (OpenStep signature literal_types step) ambient descriptor context input output <->
   CoreStep (OpenStep signature literal_types step) ambient descriptor context
     source_name target_name prior input output) /\
  FamilyWellTyped declared descriptor ambient (introduced_scope context) arguments.
Proof.
  intros declared signature literal_types ambient descriptor arguments context result step
    source_name target_name prior input output [Hcheck Hcontext] Hdistinct Hsource Htarget.
  split.
  - now apply explicit_family_step_iff_existing_premise.
  - now apply family_check_is_exact.
Qed.

Definition rename_binding rename item :=
  binding (rename (binder_identity item)) (binder_category item).

Fixpoint rename_value rename value :=
  match value with
  | Atom literal => Atom literal
  | Bound reference => Bound (rename_binding rename reference)
  | Node constructor children => Node constructor (map (rename_value rename) children)
  | Bind binders body => Bind (map (rename_binding rename) binders) (rename_value rename body)
  end.

Fixpoint rename_context rename context :=
  match context with
  | Hole => Hole
  | NodeContext constructor before inside after =>
      NodeContext constructor (map (rename_value rename) before)
        (rename_context rename inside) (map (rename_value rename) after)
  | BinderContext binders inside =>
      BinderContext (map (rename_binding rename) binders) (rename_context rename inside)
  end.

Fixpoint rename_core_pattern rename pattern :=
  match pattern with
  | Meta name => Meta name
  | NodePattern constructor before inside after =>
      NodePattern constructor (map (rename_value rename) before)
        (rename_core_pattern rename inside) (map (rename_value rename) after)
  | BinderPattern binders inside =>
      BinderPattern (map (rename_binding rename) binders) (rename_core_pattern rename inside)
  end.

Theorem lexical_renaming_commutes_with_plugging : forall context rename endpoint,
  rename_value rename (plug context endpoint) =
  plug (rename_context rename context) (rename_value rename endpoint).
Proof.
  induction context; intros; simpl; [reflexivity| |].
  - rewrite map_app. simpl. now rewrite IHcontext.
  - now rewrite IHcontext.
Qed.

Theorem lexical_renaming_commutes_with_normalization : forall context rename variable,
  rename_core_pattern rename (normalize context variable) =
  normalize (rename_context rename context) variable.
Proof. induction context; intros; simpl; [reflexivity|now rewrite IHcontext|now rewrite IHcontext]. Qed.

Theorem lexical_renaming_preserves_scope_order : forall context rename,
  introduced_scope (rename_context rename context) =
  map (rename_binding rename) (introduced_scope context).
Proof. induction context; intros; simpl; [reflexivity|apply IHcontext|now rewrite map_app, IHcontext]. Qed.

End RewriteFamilyNormalization.

Print Assumptions RewriteFamilyNormalization.family_check_is_exact.
Print Assumptions RewriteFamilyNormalization.accepted_family_has_exact_arity.
Print Assumptions RewriteFamilyNormalization.accepted_family_has_no_escaped_argument.
Print Assumptions RewriteFamilyNormalization.accepted_family_covers_each_introduced_binder.
Print Assumptions RewriteFamilyNormalization.nearest_lexical_binder_wins.
Print Assumptions RewriteFamilyNormalization.shadowed_binders_keep_distinct_identities.
Print Assumptions RewriteFamilyNormalization.normalized_matching_extracts_exact_endpoint.
Print Assumptions RewriteFamilyNormalization.normalized_reconstruction_preserves_context.
Print Assumptions RewriteFamilyNormalization.explicit_family_step_iff_existing_premise.
Print Assumptions RewriteFamilyNormalization.transition_premise_preserves_metavariable_bindings.
Print Assumptions RewriteFamilyNormalization.bound_target_refuses_transition.
Print Assumptions RewriteFamilyNormalization.generated_pair_preserves_prior_environment.
Print Assumptions RewriteFamilyNormalization.accepted_family_has_distinct_lexical_occurrences.
Print Assumptions RewriteFamilyNormalization.generated_identity_is_fresh.
Print Assumptions RewriteFamilyNormalization.scope_extension_preserves_distinct_identities.
Print Assumptions RewriteFamilyNormalization.duplicate_lexical_occurrence_is_refused.
Print Assumptions RewriteFamilyNormalization.typed_context_plugging_preserves_endpoint_type.
Print Assumptions RewriteFamilyNormalization.typed_bound_reference_is_in_scope.
Print Assumptions RewriteFamilyNormalization.typed_constructor_has_exact_arity.
Print Assumptions RewriteFamilyNormalization.checked_family_execution_preserves_parent_types.
Print Assumptions RewriteFamilyNormalization.checked_family_matching_and_reconstruction_are_equivalent.
Print Assumptions RewriteFamilyNormalization.lexical_renaming_commutes_with_plugging.
Print Assumptions RewriteFamilyNormalization.lexical_renaming_commutes_with_normalization.
Print Assumptions RewriteFamilyNormalization.lexical_renaming_preserves_scope_order.
Print Assumptions RewriteFamilyNormalization.write_binding_reads_exact_value.
Print Assumptions RewriteFamilyNormalization.fresh_extension_preserves_other_bindings.
