From Stdlib Require Import List Bool PeanoNat.
From RuntimeGrammar Require Import SemanticTransitionKernel.
Import ListNotations.
Module K := SemanticTransitionKernel.SemanticTransitionKernel.

Definition root_key (activation variable : nat) : K.ScopedVariable :=
  {| K.scoped_activation := activation; K.scoped_local := variable |}.

Definition runtime_lookup key history := K.lookup_scoped key (rev history).

Fixpoint chronological_lookup key (history : K.ScopedSubstitution)
    : option K.LogicTerm :=
  match history with
  | [] => None
  | (candidate, value) :: rest =>
      match chronological_lookup key rest with
      | Some later => Some later
      | None => if K.scoped_variable_eqb key candidate then Some value else None
      end
  end.

Lemma lookup_append : forall key left right,
  K.lookup_scoped key (left ++ right) =
  match K.lookup_scoped key left with
  | Some value => Some value
  | None => K.lookup_scoped key right
  end.
Proof.
  intros key left; induction left as [|[candidate value] rest IH]; intros right;
    simpl; auto.
  destruct (K.scoped_variable_eqb key candidate); auto.
Qed.

Theorem reverse_lookup_has_last_binding_precedence : forall key history,
  runtime_lookup key history = chronological_lookup key history.
Proof.
  intros key history; induction history as [|[candidate value] rest IH]; auto.
  unfold runtime_lookup in *; simpl.
  rewrite lookup_append, IH.
  destruct (chronological_lookup key rest); simpl; auto.
Qed.

Theorem latest_exact_scoped_binding_wins : forall key history value,
  runtime_lookup key (history ++ [(key, value)]) = Some value.
Proof.
  intros. unfold runtime_lookup. rewrite rev_app_distr. simpl.
  rewrite (proj2 (K.scoped_variable_eqb_spec key key) eq_refl). reflexivity.
Qed.

Theorem different_activation_cannot_alias_root : forall root local variable other,
  root <> local -> root_key root variable <> root_key local other.
Proof.
  intros root local variable other Hneq Heq.
  inversion Heq. contradiction.
Qed.

Theorem local_append_preserves_every_root_lookup : forall history locals root,
  Forall (fun binding => K.scoped_activation (fst binding) <> root) locals ->
  forall variable,
  runtime_lookup (root_key root variable) (history ++ locals) =
  runtime_lookup (root_key root variable) history.
Proof.
  intros history locals root Hlocals. revert history.
  induction Hlocals as [|[key value] rest Hkey Hrest IH]; intros history variable.
  - now rewrite app_nil_r.
  - replace (history ++ (key,value) :: rest)
      with ((history ++ [(key,value)]) ++ rest) by (rewrite <- app_assoc; reflexivity).
    rewrite IH.
    unfold runtime_lookup. rewrite rev_app_distr. simpl.
    destruct (K.scoped_variable_eqb (root_key root variable) key) eqn:Heq; auto.
    apply K.scoped_variable_eqb_spec in Heq.
    rewrite <- Heq in Hkey. simpl in Hkey. contradiction.
Qed.

Inductive Outcome (A : Type) :=
| Success (value : A)
| Failure (error : nat).
Arguments Success {A} _.
Arguments Failure {A} _.

Definition Grounding := nat -> K.LogicTerm -> Outcome K.LogicTerm.

Fixpoint project (ground : Grounding) (root : nat)
    (history : K.ScopedSubstitution) (variables : list nat)
    : Outcome (list (nat * K.LogicTerm)) :=
  match variables with
  | [] => Success []
  | variable :: rest =>
      match runtime_lookup (root_key root variable) history with
      | None => project ground root history rest
      | Some raw =>
          match ground variable raw with
          | Failure reason => Failure reason
          | Success value =>
              match project ground root history rest with
              | Failure reason => Failure reason
              | Success tail => Success ((variable,value) :: tail)
              end
          end
      end
  end.

Inductive RootProjection (ground : Grounding) (root : nat)
    (history : K.ScopedSubstitution) :
    list nat -> list (nat * K.LogicTerm) -> Prop :=
| projection_empty : RootProjection ground root history [] []
| projection_absent : forall variable rest output,
    chronological_lookup (root_key root variable) history = None ->
    RootProjection ground root history rest output ->
    RootProjection ground root history (variable :: rest) output
| projection_present : forall variable rest raw value output,
    chronological_lookup (root_key root variable) history = Some raw ->
    ground variable raw = Success value ->
    RootProjection ground root history rest output ->
    RootProjection ground root history (variable :: rest) ((variable,value) :: output).

Theorem projection_exactly_matches_root_binding_specification :
  forall ground root history variables output,
  project ground root history variables = Success output <->
  RootProjection ground root history variables output.
Proof.
  intros ground root history variables output. split.
  - revert output. induction variables as [|variable rest IH]; intros output H;
      simpl in H.
    + inversion H; constructor.
    + rewrite reverse_lookup_has_last_binding_precedence in H.
      destruct (chronological_lookup (root_key root variable) history) as [raw|] eqn:Hlookup.
      * destruct (ground variable raw) as [value|reason] eqn:Hground; try discriminate.
        destruct (project ground root history rest) as [tail|reason] eqn:Htail;
          try discriminate.
        inversion H; subst. eapply projection_present.
        -- exact Hlookup.
        -- exact Hground.
        -- apply IH. reflexivity.
      * apply projection_absent; auto.
  - intro H. induction H; simpl; auto;
      rewrite reverse_lookup_has_last_binding_precedence, H; auto.
    now rewrite H0, IHRootProjection.
Qed.

Theorem projection_preserves_exact_grounded_values :
  forall ground root history variables output,
  project ground root history variables = Success output ->
  forall variable value,
  In (variable,value) output <->
  In variable variables /\ exists raw,
    chronological_lookup (root_key root variable) history = Some raw /\
    ground variable raw = Success value.
Proof.
  intros ground root history variables output Hproject.
  apply projection_exactly_matches_root_binding_specification in Hproject.
  induction Hproject as [|id rest output Hlookup Htail IH|
      id rest raw result output Hlookup Hground Htail IH]; intros variable value; simpl.
  - tauto.
  - rewrite IH. split.
    + intros [Hin Hvalue]. auto.
    + intros [[Heq|Hin] [raw [Hraw Hvalue]]].
      * subst. rewrite Hlookup in Hraw. discriminate.
      * eauto.
  - rewrite IH. split.
    + intros [Heq|[Hin Hvalue]].
      * inversion Heq; subst. split; [auto|]. eauto.
      * auto.
    + intros [[Heq|Hin] [actual [Hraw Hvalue]]].
      * subst. rewrite Hlookup in Hraw. inversion Hraw; subst.
        rewrite Hground in Hvalue. inversion Hvalue; auto.
      * right; eauto.
Qed.

Definition root_is_bound root history variable : bool :=
  match chronological_lookup (root_key root variable) history with
  | Some _ => true
  | None => false
  end.

Theorem successful_projection_preserves_roster_order :
  forall ground root history variables output,
  project ground root history variables = Success output ->
  map fst output = filter (root_is_bound root history) variables.
Proof.
  intros ground root history variables output Hproject.
  apply projection_exactly_matches_root_binding_specification in Hproject.
  induction Hproject; simpl; auto; unfold root_is_bound at 1;
    rewrite H; simpl; congruence.
Qed.

Theorem absent_root_binding_is_omitted :
  forall ground root history variables output variable,
  project ground root history variables = Success output ->
  chronological_lookup (root_key root variable) history = None ->
  ~ In variable (map fst output).
Proof.
  intros ground root history variables output variable Hproject Hnone Hin.
  rewrite (successful_projection_preserves_roster_order _ _ _ _ _ Hproject) in Hin.
  apply filter_In in Hin. destruct Hin as [_ Hbound].
  unfold root_is_bound in Hbound. rewrite Hnone in Hbound. discriminate.
Qed.

Theorem undeclared_root_binding_is_omitted :
  forall ground root history variables output variable,
  project ground root history variables = Success output ->
  ~ In variable variables -> ~ In variable (map fst output).
Proof.
  intros ground root history variables output variable Hproject Hmissing Hin.
  rewrite (successful_projection_preserves_roster_order _ _ _ _ _ Hproject) in Hin.
  apply filter_In in Hin. tauto.
Qed.

Theorem unique_roster_has_no_projected_alias :
  forall ground root history variables output,
  NoDup variables -> project ground root history variables = Success output ->
  NoDup (map fst output).
Proof.
  intros ground root history variables output Hunique Hproject.
  rewrite (successful_projection_preserves_roster_order _ _ _ _ _ Hproject).
  now apply NoDup_filter.
Qed.

Theorem local_only_history_publishes_no_bindings :
  forall ground root history variables,
  Forall (fun binding => K.scoped_activation (fst binding) <> root) history ->
  project ground root history variables = Success [].
Proof.
  intros ground root history variables Hlocal. induction variables as [|variable rest IH]; auto.
  simpl. pose proof (local_append_preserves_every_root_lookup [] history root Hlocal variable) as Hlookup.
  simpl in Hlookup. rewrite Hlookup. exact IH.
Qed.

Theorem local_bindings_preserve_projection_with_stable_grounding :
  forall ground root history locals variables,
  Forall (fun binding => K.scoped_activation (fst binding) <> root) locals ->
  project ground root (history ++ locals) variables = project ground root history variables.
Proof.
  intros ground root history locals variables Hlocals.
  induction variables as [|variable rest IH]; auto. simpl.
  rewrite (local_append_preserves_every_root_lookup history locals root Hlocals variable).
  destruct (runtime_lookup (root_key root variable) history) as [raw|]; auto.
  destruct (ground variable raw); now rewrite ?IH.
Qed.

Record Declaration := {
  declaration_id : nat;
  declaration_role : nat
}.

Definition project_declarations ground root history declarations :=
  project ground root history (map declaration_id declarations).

Theorem declaration_roles_do_not_change_visibility :
  forall ground root history left right,
  map declaration_id left = map declaration_id right ->
  project_declarations ground root history left =
  project_declarations ground root history right.
Proof.
  intros. unfold project_declarations. now rewrite H.
Qed.

Theorem present_root_binder_survives_projection :
  forall ground root history variable role raw value,
  runtime_lookup (root_key root variable) history = Some raw ->
  ground variable raw = Success value ->
  project_declarations ground root history
    [{| declaration_id := variable; declaration_role := role |}] =
  Success [(variable,value)].
Proof.
  intros. unfold project_declarations. simpl. now rewrite H, H0.
Qed.

Theorem head_grounding_failure_returns_exact_error :
  forall ground root history variable rest raw error,
  runtime_lookup (root_key root variable) history = Some raw ->
  ground variable raw = Failure error ->
  project ground root history (variable :: rest) = Failure error.
Proof.
  intros. simpl. now rewrite H, H0.
Qed.

Theorem later_grounding_failure_discards_projected_prefix :
  forall ground root history variable rest raw value error,
  runtime_lookup (root_key root variable) history = Some raw ->
  ground variable raw = Success value ->
  project ground root history rest = Failure error ->
  project ground root history (variable :: rest) = Failure error.
Proof.
  intros. simpl. now rewrite H, H0, H1.
Qed.

Theorem failed_projection_cannot_publish_any_prefix :
  forall ground root history variables error,
  project ground root history variables = Failure error ->
  forall output, project ground root history variables <> Success output.
Proof.
  intros ground root history variables error Herror output Hsuccess.
  rewrite Herror in Hsuccess. discriminate.
Qed.

Print Assumptions reverse_lookup_has_last_binding_precedence.
Print Assumptions latest_exact_scoped_binding_wins.
Print Assumptions different_activation_cannot_alias_root.
Print Assumptions local_append_preserves_every_root_lookup.
Print Assumptions projection_exactly_matches_root_binding_specification.
Print Assumptions projection_preserves_exact_grounded_values.
Print Assumptions successful_projection_preserves_roster_order.
Print Assumptions absent_root_binding_is_omitted.
Print Assumptions undeclared_root_binding_is_omitted.
Print Assumptions unique_roster_has_no_projected_alias.
Print Assumptions local_only_history_publishes_no_bindings.
Print Assumptions local_bindings_preserve_projection_with_stable_grounding.
Print Assumptions declaration_roles_do_not_change_visibility.
Print Assumptions present_root_binder_survives_projection.
Print Assumptions head_grounding_failure_returns_exact_error.
Print Assumptions later_grounding_failure_discards_projected_prefix.
Print Assumptions failed_projection_cannot_publish_any_prefix.
