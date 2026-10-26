From Stdlib Require Import List Bool PeanoNat Lia.
From RuntimeGrammar Require Import CheckedCostImage SemanticTransitionKernel.
Import ListNotations.

Module Cost := CheckedCostImage.CheckedCostImage.
Module Kernel := SemanticTransitionKernel.SemanticTransitionKernel.

Record SourceGradeDeclaration := {
  source_rewrite_name : nat;
  source_grade_root : nat
}.

Record CostProgramView := {
  program_manifest : Kernel.TransitionRuleManifest;
  program_source_index : nat;
  program_source_name : nat;
  program_grade_arena : list (nat * Cost.GradeExpr)
}.

Record CostRowReference := {
  row_program : nat;
  row_grade_root : nat
}.

Definition source_row_identity_matches equations index source program row : bool :=
  match Kernel.transition_rule_origin (program_manifest program) with
  | Kernel.EquationOrigin => false
  | Kernel.RewriteOrigin =>
      Nat.eqb (Kernel.transition_rule_id (program_manifest program)) (2 * equations + index) &&
      Nat.eqb (program_source_index program) index &&
      Nat.eqb (program_source_name program) (source_rewrite_name source) &&
      Nat.eqb (row_program row) (Kernel.transition_rule_id (program_manifest program)) &&
      Nat.eqb (row_grade_root row) (source_grade_root source)
  end.

Definition admit_source_row equations index grade_sort source program row
    : option Cost.CostRule :=
  if source_row_identity_matches equations index source program row then
    match nth_error (program_grade_arena program) (row_grade_root row) with
    | Some (sort, expression) =>
        if Nat.eqb sort grade_sort then
          Some {| Cost.cost_rule_id := row_program row;
                  Cost.cost_rule_grade := expression |}
        else None
    | None => None
    end
  else None.

Theorem admitted_row_retains_exact_source_identity :
  forall equations index grade_sort source program row compiled,
    admit_source_row equations index grade_sort source program row = Some compiled ->
    Kernel.transition_rule_origin (program_manifest program) = Kernel.RewriteOrigin /\
    Kernel.transition_rule_id (program_manifest program) = 2 * equations + index /\
    program_source_index program = index /\
    program_source_name program = source_rewrite_name source /\
    row_program row = Kernel.transition_rule_id (program_manifest program) /\
    row_grade_root row = source_grade_root source /\
    exists expression,
      nth_error (program_grade_arena program) (source_grade_root source) =
        Some (grade_sort, expression) /\
      compiled = {| Cost.cost_rule_id := row_program row;
                    Cost.cost_rule_grade := expression |}.
Proof.
  intros equations index grade_sort source program row compiled Hadmit.
  unfold admit_source_row in Hadmit.
  destruct (source_row_identity_matches equations index source program row)
    eqn:Hidentity; [| discriminate].
  destruct (nth_error (program_grade_arena program) (row_grade_root row))
    as [[sort expression]|] eqn:Hterm; [| discriminate].
  destruct (Nat.eqb sort grade_sort) eqn:Hsort; [| discriminate].
  apply Nat.eqb_eq in Hsort. subst sort.
  inversion Hadmit; subst compiled.
  unfold source_row_identity_matches in Hidentity.
  destruct (Kernel.transition_rule_origin (program_manifest program))
    eqn:Horigin; [discriminate |].
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  end.
  repeat match goal with
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  end.
  repeat split; try assumption; try reflexivity.
  exists expression. split; [| reflexivity]. congruence.
Qed.

Theorem equation_program_cannot_have_an_admitted_cost_row :
  forall equations index grade_sort source program row,
    Kernel.transition_rule_origin (program_manifest program) = Kernel.EquationOrigin ->
    admit_source_row equations index grade_sort source program row = None.
Proof.
  intros equations index grade_sort source program row Horigin.
  unfold admit_source_row, source_row_identity_matches. now rewrite Horigin.
Qed.

Theorem a_different_declared_root_is_refused :
  forall equations index grade_sort source program row,
    row_grade_root row <> source_grade_root source ->
    admit_source_row equations index grade_sort source program row = None.
Proof.
  intros equations index grade_sort source program row Hdifferent.
  destruct (admit_source_row equations index grade_sort source program row)
    as [compiled|] eqn:Hadmit; [| reflexivity].
  pose proof (admitted_row_retains_exact_source_identity _ _ _ _ _ _ _ Hadmit)
    as [_ [_ [_ [_ [_ [Hroot _]]]]]]. contradiction.
Qed.

Theorem an_equation_prefix_id_cannot_name_a_cost_row :
  forall equations index grade_sort source program row compiled,
    admit_source_row equations index grade_sort source program row = Some compiled ->
    ~ row_program row < 2 * equations.
Proof.
  intros equations index grade_sort source program row compiled Hadmit.
  pose proof (admitted_row_retains_exact_source_identity _ _ _ _ _ _ _ Hadmit)
    as [_ [Hposition [_ [_ [Hprogram _]]]]]. lia.
Qed.

Lemma cost_lookup_retains_requested_identity : forall rules id row,
  Cost.find_cost_rule id rules = Some row -> Cost.cost_rule_id row = id.
Proof.
  induction rules as [|head tail IH]; intros id row Hfind; [discriminate |].
  simpl in Hfind. destruct (Nat.eqb (Cost.cost_rule_id head) id) eqn:Hid.
  - inversion Hfind; subst row. now apply Nat.eqb_eq.
  - now apply IH.
Qed.

Theorem admitted_source_row_composes_with_existing_grade_publication :
  forall equations index grade_sort source program row compiled image matched receipt,
    admit_source_row equations index grade_sort source program row = Some compiled ->
    Cost.find_cost_rule (Cost.match_rule matched) (Cost.cost_rules image) = Some compiled ->
    Cost.cost_grade_sort image = grade_sort ->
    Cost.publish_grade image matched = Some receipt ->
    Kernel.transition_rule_origin (program_manifest program) = Kernel.RewriteOrigin /\
    row_grade_root row = source_grade_root source /\
    Cost.receipt_rule receipt = 2 * equations + index /\
    Cost.receipt_output receipt = Cost.match_output matched /\
    Cost.receipt_sort receipt = grade_sort /\
    exists expression,
      nth_error (program_grade_arena program) (source_grade_root source) =
        Some (grade_sort, expression) /\
      Cost.evaluate_grade (Cost.match_bindings matched) expression =
        Some (Cost.receipt_grade receipt).
Proof.
  intros equations index grade_sort source program row compiled image matched receipt
    Hadmit Hlookup Hsort Hpublish.
  destruct (admitted_row_retains_exact_source_identity _ _ _ _ _ _ _ Hadmit)
    as [Horigin [Hposition [_ [_ [Hprogram [Hroot [expression [Hterm Hcompiled]]]]]]]].
  pose proof (cost_lookup_retains_requested_identity _ _ _ Hlookup) as Hmatched.
  destruct (Cost.published_grade_is_exactly_the_matched_rule_grade _ _ _ Hpublish)
    as [_ [_ [_ [_ [_ [_ [_ [_ [Houtput [Hreceipt_sort [selected [Hselected [Hgrade Hreceipt]]]]]]]]]]]]].
  rewrite Hlookup in Hselected. inversion Hselected; subst selected.
  rewrite Hcompiled in Hmatched, Hgrade. simpl in Hmatched, Hgrade.
  split; [exact Horigin |]. split; [exact Hroot |]. split.
  - congruence.
  - split; [exact Houtput |]. split; [congruence |]. exists expression. auto.
Qed.

Definition source_roster_position_matches equations grade_sort sources programs rows index : bool :=
  match nth_error sources index,
        nth_error programs (2 * equations + index),
        nth_error rows index with
  | Some source, Some program, Some row =>
      match admit_source_row equations index grade_sort source program row with
      | Some _ => true
      | None => false
      end
  | _, _, _ => false
  end.

Definition admit_source_roster equations grade_sort sources programs rows : bool :=
  Nat.eqb (length rows) (length sources) &&
  Nat.eqb (length programs) (2 * equations + length sources) &&
  forallb (source_roster_position_matches equations grade_sort sources programs rows)
    (seq 0 (length sources)).

Theorem admitted_roster_has_exact_counts :
  forall equations grade_sort sources programs rows,
    admit_source_roster equations grade_sort sources programs rows = true ->
    length rows = length sources /\
    length programs = 2 * equations + length sources.
Proof.
  intros equations grade_sort sources programs rows H.
  unfold admit_source_roster in H.
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [Hrows Hprograms].
  apply Nat.eqb_eq in Hrows. apply Nat.eqb_eq in Hprograms. auto.
Qed.

Theorem admitted_roster_covers_every_source_position :
  forall equations grade_sort sources programs rows index,
    admit_source_roster equations grade_sort sources programs rows = true ->
    index < length sources ->
    exists source program row compiled,
      nth_error sources index = Some source /\
      nth_error programs (2 * equations + index) = Some program /\
      nth_error rows index = Some row /\
      admit_source_row equations index grade_sort source program row = Some compiled.
Proof.
  intros equations grade_sort sources programs rows index H Hin.
  unfold admit_source_roster in H.
  apply andb_true_iff in H as [_ H].
  rewrite forallb_forall in H.
  assert (Hposition : In index (seq 0 (length sources))) by (apply in_seq; lia).
  specialize (H index Hposition).
  unfold source_roster_position_matches in H.
  destruct (nth_error sources index) as [source|] eqn:Hsource; [| discriminate].
  destruct (nth_error programs (2 * equations + index)) as [program|]
    eqn:Hprogram; [| discriminate].
  destruct (nth_error rows index) as [row|] eqn:Hrow; [| discriminate].
  destruct (admit_source_row equations index grade_sort source program row)
    as [compiled|] eqn:Hadmit; [| discriminate].
  exists source, program, row, compiled. auto.
Qed.

Theorem admitted_roster_has_no_extra_rows :
  forall equations grade_sort sources programs rows index row,
    admit_source_roster equations grade_sort sources programs rows = true ->
    nth_error rows index = Some row -> index < length sources.
Proof.
  intros equations grade_sort sources programs rows index row H Hrow.
  destruct (admitted_roster_has_exact_counts _ _ _ _ _ H) as [Hlength _].
  rewrite <- Hlength. apply nth_error_Some. rewrite Hrow. discriminate.
Qed.

Theorem admitted_roster_retains_source_order :
  forall equations grade_sort sources programs rows index row,
    admit_source_roster equations grade_sort sources programs rows = true ->
    nth_error rows index = Some row -> row_program row = 2 * equations + index.
Proof.
  intros equations grade_sort sources programs rows index row H Hrow.
  pose proof (admitted_roster_has_no_extra_rows _ _ _ _ _ _ _ H Hrow) as Hin.
  destruct (admitted_roster_covers_every_source_position _ _ _ _ _ _ H Hin)
    as [source [program [found [compiled [_ [_ [Hfound Hadmit]]]]]]].
  rewrite Hrow in Hfound. inversion Hfound; subst found.
  destruct (admitted_row_retains_exact_source_identity _ _ _ _ _ _ _ Hadmit)
    as [_ [Hposition [_ [_ [Hprogram _]]]]]. congruence.
Qed.

Theorem admitted_roster_cannot_duplicate_a_program :
  forall equations grade_sort sources programs rows i j left right,
    admit_source_roster equations grade_sort sources programs rows = true ->
    nth_error rows i = Some left -> nth_error rows j = Some right ->
    row_program left = row_program right -> i = j.
Proof.
  intros equations grade_sort sources programs rows i j left right H Hleft Hright Heq.
  pose proof (admitted_roster_retains_source_order _ _ _ _ _ _ _ H Hleft).
  pose proof (admitted_roster_retains_source_order _ _ _ _ _ _ _ H Hright).
  lia.
Qed.

Theorem admitted_roster_excludes_equation_prefix_ids :
  forall equations grade_sort sources programs rows index row,
    admit_source_roster equations grade_sort sources programs rows = true ->
    nth_error rows index = Some row -> ~ row_program row < 2 * equations.
Proof.
  intros equations grade_sort sources programs rows index row H Hrow.
  pose proof (admitted_roster_retains_source_order _ _ _ _ _ _ _ H Hrow). lia.
Qed.

Theorem mismatched_roster_count_is_refused :
  forall equations grade_sort sources programs rows,
    length rows <> length sources ->
    admit_source_roster equations grade_sort sources programs rows = false.
Proof.
  intros equations grade_sort sources programs rows Hlength.
  destruct (admit_source_roster equations grade_sort sources programs rows) eqn:H;
    [| reflexivity].
  destruct (admitted_roster_has_exact_counts _ _ _ _ _ H). contradiction.
Qed.

Definition example_source := {| source_rewrite_name := 8; source_grade_root := 0 |}.
Definition example_program :=
  {| program_manifest :=
       {| Kernel.transition_rule_id := 2;
          Kernel.transition_rule_origin := Kernel.RewriteOrigin;
          Kernel.transition_rule_source_sort := 0;
          Kernel.transition_rule_target_sort := 0;
          Kernel.transition_rule_executable := true |};
     program_source_index := 0;
     program_source_name := 8;
     program_grade_arena := [(1, Cost.GradeUnit);
       (1, Cost.GradeProduct Cost.GradeUnit Cost.GradeUnit)] |}.

Example exact_root_is_admitted :
  admit_source_row 1 0 1 example_source example_program
    {| row_program := 2; row_grade_root := 0 |} =
  Some {| Cost.cost_rule_id := 2; Cost.cost_rule_grade := Cost.GradeUnit |}.
Proof. reflexivity. Qed.

Example equal_evaluation_does_not_authorize_another_root :
  Cost.evaluate_grade [] Cost.GradeUnit =
    Cost.evaluate_grade [] (Cost.GradeProduct Cost.GradeUnit Cost.GradeUnit) /\
  admit_source_row 1 0 1 example_source example_program
    {| row_program := 2; row_grade_root := 1 |} = None.
Proof. split; reflexivity. Qed.

Example either_equation_direction_id_is_refused :
  admit_source_row 1 0 1 example_source example_program
    {| row_program := 0; row_grade_root := 0 |} = None /\
  admit_source_row 1 0 1 example_source example_program
    {| row_program := 1; row_grade_root := 0 |} = None.
Proof. split; reflexivity. Qed.

Print Assumptions admitted_row_retains_exact_source_identity.
Print Assumptions equation_program_cannot_have_an_admitted_cost_row.
Print Assumptions a_different_declared_root_is_refused.
Print Assumptions an_equation_prefix_id_cannot_name_a_cost_row.
Print Assumptions admitted_source_row_composes_with_existing_grade_publication.
Print Assumptions exact_root_is_admitted.
Print Assumptions equal_evaluation_does_not_authorize_another_root.
Print Assumptions either_equation_direction_id_is_refused.
Print Assumptions admitted_roster_has_exact_counts.
Print Assumptions admitted_roster_covers_every_source_position.
Print Assumptions admitted_roster_has_no_extra_rows.
Print Assumptions admitted_roster_retains_source_order.
Print Assumptions admitted_roster_cannot_duplicate_a_program.
Print Assumptions admitted_roster_excludes_equation_prefix_ids.
Print Assumptions mismatched_roster_count_is_refused.
