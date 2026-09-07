(*
 * A selected candidate is an occurrence tree: sharing a forest node does not
 * identify two positions in this tree. The ranked family engine supplies its
 * selected leaves. This model proves that compiling the tree to a flat
 * postorder program and executing it on an explicit value stack preserves
 * exactly its declarative assembly, including partial constructor actions.
 *
 * Labels may describe collection, optional, or grammar-rule assembly. Values
 * may include ordered semiring weights; the assembler owns those operations.
 * No ranking, bounded-family completeness, or Rust heap refinement is assumed
 * or claimed by this local reconstruction theorem.
 *)
From Stdlib Require Import List Arith Lia.
Import ListNotations.
Set Implicit Arguments.

Section OccurrenceProgram.
  Context {Value Label : Type}.
  Variable assemble : Label -> list Value -> option Value.

  Inductive selected_tree : Type :=
  | SelectedLeaf : Value -> selected_tree
  | SelectedBranch : Label -> selected_children -> selected_tree
  with selected_children : Type :=
  | NoChildren : selected_children
  | MoreChildren : selected_tree -> selected_children -> selected_children.

  Scheme selected_tree_mut := Induction for selected_tree Sort Prop
    with selected_children_mut := Induction for selected_children Sort Prop.
  Combined Scheme selected_mutual from selected_tree_mut, selected_children_mut.

  Fixpoint child_count (children : selected_children) : nat :=
    match children with
    | NoChildren => 0
    | MoreChildren _ rest => S (child_count rest)
    end.

  Fixpoint denote_tree (tree : selected_tree) : option Value :=
    match tree with
    | SelectedLeaf value => Some value
    | SelectedBranch label children =>
        match denote_children children with
        | Some values => assemble label values
        | None => None
        end
    end
  with denote_children (children : selected_children) : option (list Value) :=
    match children with
    | NoChildren => Some []
    | MoreChildren tree rest =>
        match denote_tree tree, denote_children rest with
        | Some value, Some values => Some (value :: values)
        | _, _ => None
        end
    end.

  Inductive instruction :=
  | PushSelected : Value -> instruction
  | AssembleSelected : Label -> nat -> instruction.

  Fixpoint compile_tree (tree : selected_tree) : list instruction :=
    match tree with
    | SelectedLeaf value => [PushSelected value]
    | SelectedBranch label children =>
        compile_children children ++ [AssembleSelected label (child_count children)]
    end
  with compile_children (children : selected_children) : list instruction :=
    match children with
    | NoChildren => []
    | MoreChildren tree rest => compile_tree tree ++ compile_children rest
    end.

  (* Stack top is the list head; reversing only the selected suffix gives the
     action its children in source order. Rust may keep its Vec top at the end
     and use split_off, with no reverse copy. Neither requires call recursion. *)
  Definition execute_instruction (op : instruction) (stack : list Value)
    : option (list Value) :=
    match op with
    | PushSelected value => Some (value :: stack)
    | AssembleSelected label count =>
        if count <=? length stack then
          match assemble label (rev (firstn count stack)) with
          | Some value => Some (value :: skipn count stack)
          | None => None
          end
        else None
    end.

  Fixpoint execute (program : list instruction) (stack : list Value)
    : option (list Value) :=
    match program with
    | [] => Some stack
    | op :: rest =>
        match execute_instruction op stack with
        | Some next => execute rest next
        | None => None
        end
    end.

  Lemma execute_append : forall first rest stack,
    execute (first ++ rest) stack =
    match execute first stack with
    | Some middle => execute rest middle
    | None => None
    end.
  Proof.
    induction first as [|op first IH]; intros rest stack; cbn; [reflexivity |].
    destruct (execute_instruction op stack); cbn; [apply IH | reflexivity].
  Qed.

  Lemma child_values_have_exact_arity : forall children values,
    denote_children children = Some values -> length values = child_count children.
  Proof.
    induction children as [|tree rest IH]; intros values H; cbn in H.
    - inversion H. reflexivity.
    - destruct (denote_tree tree) as [value|]; [|discriminate].
      destruct (denote_children rest) as [tail|] eqn:Htail; [|discriminate].
      inversion H; subst. cbn. f_equal. now apply IH.
  Qed.

  Lemma assemble_restores_stack : forall label values stack,
    execute_instruction (AssembleSelected label (length values)) (rev values ++ stack) =
    option_map (fun value => value :: stack) (assemble label values).
  Proof.
    intros label values stack. unfold execute_instruction.
    assert (Hbound : (length values <=? length (rev values ++ stack)) = true).
    { apply Nat.leb_le. rewrite length_app, length_rev. lia. }
    rewrite Hbound.
    replace (length values) with (length (rev values)) by apply length_rev.
    rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite skipn_app, skipn_all, Nat.sub_diag, skipn_O. cbn.
    rewrite rev_involutive. destruct (assemble label values); reflexivity.
  Qed.

  Theorem compiled_occurrences_refine_declarative_assembly :
    (forall tree stack,
      execute (compile_tree tree) stack =
      option_map (fun value => value :: stack) (denote_tree tree)) /\
    (forall children stack,
      execute (compile_children children) stack =
      option_map (fun values => rev values ++ stack) (denote_children children)).
  Proof.
    apply selected_mutual.
    - intros value stack. reflexivity.
    - intros label children IH stack. cbn. rewrite execute_append, IH.
      destruct (denote_children children) as [values|] eqn:Hvalues; cbn; [|reflexivity].
      rewrite <- (@child_values_have_exact_arity children values Hvalues).
      change (match execute_instruction (AssembleSelected label (length values))
        (rev values ++ stack) with Some next => Some next | None => None end =
        option_map (fun value => value :: stack) (assemble label values)).
      rewrite assemble_restores_stack.
      destruct (assemble label values); reflexivity.
    - intro stack. reflexivity.
    - intros tree IHtree rest IHrest stack. cbn.
      rewrite execute_append, IHtree.
      destruct (denote_tree tree) as [value|]; cbn; [|reflexivity].
      rewrite IHrest. destruct (denote_children rest) as [values|]; cbn; [|reflexivity].
      f_equal. rewrite <- app_assoc. reflexivity.
  Qed.

  Corollary completed_program_returns_exact_selected_value : forall tree value,
    execute (compile_tree tree) [] = Some [value] <-> denote_tree tree = Some value.
  Proof.
    intros tree value.
    rewrite (proj1 compiled_occurrences_refine_declarative_assembly).
    destruct (denote_tree tree) as [result|]; cbn; split; intro H;
      inversion H; reflexivity.
  Qed.

  Corollary partial_actions_fail_at_the_same_candidate : forall tree,
    execute (compile_tree tree) [] = None <-> denote_tree tree = None.
  Proof.
    intro tree. rewrite (proj1 compiled_occurrences_refine_declarative_assembly).
    destruct (denote_tree tree); cbn; split; intro H; try discriminate; reflexivity.
  Qed.
End OccurrenceProgram.

Print Assumptions compiled_occurrences_refine_declarative_assembly.
Print Assumptions completed_program_returns_exact_selected_value.
Print Assumptions partial_actions_fail_at_the_same_candidate.

(* A candidate's Weight key can be evaluated before invoking any partial
   constructor. Successful assembly must have exactly that precomputed weight;
   failure rejects this candidate, not a different coordinate. This statement
   deliberately says nothing about Election's separate provenance product or
   whether a heap comparator is monotone. No commutation or reassociation is
   used: the two interpretations perform the identical ordered operations. *)
Section WeightProjection.
  Context {Value Label Weight : Type}.
  Variable one : Weight.
  Variable times : Weight -> Weight -> Weight.
  Variable action : Label -> list Value -> option Value.

  (* Collection assembly has no local packing factor. An actual packing
     carries Some weight even when that weight equals the numeric identity.
     The distinction is structural, never inferred by inspecting a weight. *)
  Definition append_local_factor (children : Weight) (local : option Weight) : Weight :=
    match local with Some weight => times children weight | None => children end.

  Definition assemble_weight (label : Label * option Weight) (children : list Weight)
    : option Weight := Some (append_local_factor (fold_left times children one) (snd label)).

  Definition assemble_weighted (label : Label * option Weight)
    (children : list (Value * Weight)) : option (Value * Weight) :=
    match action (fst label) (map fst children) with
    | Some value =>
        Some (value, append_local_factor (fold_left times (map snd children) one) (snd label))
    | None => None
    end.

  Fixpoint project_tree_weight
    (tree : @selected_tree (Value * Weight) (Label * option Weight))
    : @selected_tree Weight (Label * option Weight) :=
    match tree with
    | SelectedLeaf value => SelectedLeaf (snd value)
    | SelectedBranch label children =>
        SelectedBranch label (project_children_weight children)
    end
  with project_children_weight
    (children : @selected_children (Value * Weight) (Label * option Weight))
    : @selected_children Weight (Label * option Weight) :=
    match children with
    | NoChildren => NoChildren
    | MoreChildren tree rest =>
        MoreChildren (project_tree_weight tree) (project_children_weight rest)
    end.

  Theorem successful_assembly_preserves_precomputed_weight :
    (forall tree value,
      denote_tree assemble_weighted tree = Some value ->
      denote_tree assemble_weight (project_tree_weight tree) = Some (snd value)) /\
    (forall children values,
      denote_children assemble_weighted children = Some values ->
      denote_children assemble_weight (project_children_weight children) =
        Some (map snd values)).
  Proof.
    apply selected_mutual.
    - intros value result H. inversion H. reflexivity.
    - intros label children IH result H.
      change (match denote_children assemble_weighted children with
        | Some values => assemble_weighted label values | None => None end =
        Some result) in H.
      change (match denote_children assemble_weight (project_children_weight children) with
        | Some values => assemble_weight label values | None => None end =
        Some (snd result)).
      destruct (denote_children assemble_weighted children) as [values|] eqn:E;
        [|discriminate].
      rewrite (IH values eq_refl). unfold assemble_weighted in H.
      destruct (action (fst label) (map fst values)); [|discriminate].
      inversion H. reflexivity.
    - intros values H. inversion H. reflexivity.
    - intros tree IHtree rest IHrest values H.
      change (match denote_tree assemble_weighted tree,
        denote_children assemble_weighted rest with
        | Some value, Some tail => Some (value :: tail) | _, _ => None end =
        Some values) in H.
      change (match denote_tree assemble_weight (project_tree_weight tree),
        denote_children assemble_weight (project_children_weight rest) with
        | Some value, Some tail => Some (value :: tail) | _, _ => None end =
        Some (map snd values)).
      destruct (denote_tree assemble_weighted tree) as [value|] eqn:Et;
        [|discriminate].
      destruct (denote_children assemble_weighted rest) as [tail|] eqn:Er;
        [|discriminate].
      rewrite (IHtree value eq_refl), (IHrest tail eq_refl).
      inversion H. reflexivity.
  Qed.

  Corollary successful_postorder_program_has_precomputed_weight : forall tree value,
    execute assemble_weighted (compile_tree tree) [] = Some [value] ->
    execute assemble_weight (compile_tree (project_tree_weight tree)) [] =
      Some [snd value].
  Proof.
    intros tree value H.
    apply completed_program_returns_exact_selected_value in H.
    apply completed_program_returns_exact_selected_value.
    now apply (proj1 successful_assembly_preserves_precomputed_weight tree value).
  Qed.
End WeightProjection.

(* Free words expose factor ordering: arithmetic commutative weights would
   fail to distinguish L A B Optional R Parent from several incorrect folds. *)
Example nested_optional_weight_word_is_source_order :
  let leaf n := @SelectedLeaf (unit * list nat) (unit * option (list nat)) (tt, [n]) in
  let optional := SelectedBranch (tt, Some [4])
    (MoreChildren (leaf 2) (MoreChildren (leaf 3) NoChildren)) in
  let tree := SelectedBranch (tt, Some [6])
    (MoreChildren (leaf 1)
      (MoreChildren optional (MoreChildren (leaf 5) NoChildren))) in
  denote_tree (assemble_weighted [] (@app nat) (fun _ _ => Some tt)) tree =
    Some (tt, [1; 2; 3; 4; 5; 6]).
Proof. reflexivity. Qed.

Print Assumptions successful_assembly_preserves_precomputed_weight.
Print Assumptions successful_postorder_program_has_precomputed_weight.
Print Assumptions nested_optional_weight_word_is_source_order.

(* Election has a different ordered product from action Weight. Its
   structural containers transport optional factors and independent metadata.
   None is absence, not Some one. This matters for the legacy rank carrier,
   whose primary-zero is_one shortcut does not satisfy right identity for
   decorated values. No semiring identity or associativity premise is used. *)
Section ElectionFactorPresence.
  Context {Weight Event : Type}.
  Variable times : Weight -> Weight -> Weight.

  Definition combine_present_factors (left right : option Weight) : option Weight :=
    match left, right with
    | _, None => left
    | None, Some weight => Some weight
    | Some a, Some b => Some (times a b)
    end.

  Record rank_contribution := {
    rank_factor : option Weight;
    rank_lag : nat;
    rank_events : list Event
  }.

  Definition no_rank_contribution : rank_contribution :=
    {| rank_factor := None; rank_lag := 0; rank_events := [] |}.

  Definition absorb_contribution (left right : rank_contribution) : rank_contribution :=
    {| rank_factor := combine_present_factors (rank_factor left) (rank_factor right);
       rank_lag := rank_lag left + rank_lag right;
       rank_events := rank_events left ++ rank_events right |}.

  Theorem absent_container_is_an_exact_noop : forall rank,
    absorb_contribution rank no_rank_contribution = rank.
  Proof.
    intros [factor lag events]. unfold absorb_contribution, no_rank_contribution; cbn.
    rewrite Nat.add_0_r, app_nil_r. now destruct factor.
  Qed.

  Theorem event_only_leaf_preserves_weight : forall rank events,
    absorb_contribution rank
      {| rank_factor := None; rank_lag := 0; rank_events := events |} =
      {| rank_factor := rank_factor rank; rank_lag := rank_lag rank;
         rank_events := rank_events rank ++ events |}.
  Proof.
    intros [factor lag prior] events. unfold absorb_contribution; cbn.
    rewrite Nat.add_0_r. now destruct factor.
  Qed.

  Theorem present_factor_is_never_silently_omitted : forall left right lag events,
    rank_factor (absorb_contribution
      {| rank_factor := Some left; rank_lag := lag; rank_events := events |}
      {| rank_factor := Some right; rank_lag := 0; rank_events := [] |}) =
      Some (times left right).
  Proof. reflexivity. Qed.

  Theorem contribution_loop_preserves_ordered_present_factors : forall children seed,
    rank_factor (fold_left absorb_contribution children seed) =
      fold_left combine_present_factors (map rank_factor children) (rank_factor seed).
  Proof.
    induction children as [|child rest IH]; intro seed; cbn; [reflexivity|].
    rewrite IH. reflexivity.
  Qed.

  Theorem contribution_loop_preserves_event_occurrences : forall children seed,
    rank_events (fold_left absorb_contribution children seed) =
      rank_events seed ++ flat_map rank_events children.
  Proof.
    induction children as [|child rest IH]; intro seed; cbn.
    - now rewrite app_nil_r.
    - rewrite IH. cbn. now rewrite app_assoc.
  Qed.
End ElectionFactorPresence.

(* Exact primary-zero slice of LexicographicWeight::times: max open length,
   right operand's provenance due to the primary-only identity shortcut. *)
Definition zero_primary_rank_times (left right : nat * nat) : nat * nat :=
  (Nat.max (fst left) (fst right), snd right).

Example synthetic_identity_erases_zero_primary_provenance :
  zero_primary_rank_times (5, 1) (0, 65535) = (5, 65535) /\
  zero_primary_rank_times (5, 1) (0, 65535) <> (5, 1).
Proof. split; [reflexivity|discriminate]. Qed.

Example collection_has_no_synthetic_weight_tail :
  @assemble_weight unit (nat * nat) (0, 65535) zero_primary_rank_times
    (tt, None) [(5, 1)] = Some (5, 1).
Proof. reflexivity. Qed.

Print Assumptions absent_container_is_an_exact_noop.
Print Assumptions event_only_leaf_preserves_weight.
Print Assumptions present_factor_is_never_silently_omitted.
Print Assumptions contribution_loop_preserves_ordered_present_factors.
Print Assumptions contribution_loop_preserves_event_occurrences.
Print Assumptions collection_has_no_synthetic_weight_tail.

(* Operational bridge for the compiler itself. VisitTree/VisitChildren are
   suspended traversal frames; Emit postpones a parent until all its children
   have emitted. The Rust implementation can store forest IDs in these frames
   and append into a Vec instead of building a recursive owned tree. A separate
   forest-selection invariant must establish which occurrence each ID denotes. *)
Section IterativeCompiler.
  Context {Value Label : Type}.

  Inductive compile_task :=
  | VisitTree : @selected_tree Value Label -> compile_task
  | VisitChildren : @selected_children Value Label -> compile_task
  | Emit : @instruction Value Label -> compile_task.

  Definition task_meaning (task : compile_task) : list instruction :=
    match task with
    | VisitTree tree => compile_tree tree
    | VisitChildren children => compile_children children
    | Emit op => [op]
    end.

  Definition work_meaning (work : list compile_task) := flat_map task_meaning work.

  Fixpoint tree_work (tree : @selected_tree Value Label) : nat :=
    match tree with
    | SelectedLeaf _ => 1
    | SelectedBranch _ children => S (S (children_work children))
    end
  with children_work (children : @selected_children Value Label) : nat :=
    match children with
    | NoChildren => 1
    | MoreChildren tree rest => S (tree_work tree + children_work rest)
    end.

  Definition task_work (task : compile_task) : nat :=
    match task with
    | VisitTree tree => tree_work tree
    | VisitChildren children => children_work children
    | Emit _ => 1
    end.

  Definition remaining_work (work : list compile_task) : nat :=
    fold_right (fun task total => task_work task + total) 0 work.

  Definition advance_compiler (work : list compile_task) (emitted : list instruction)
    : option (list compile_task * list instruction) :=
    match work with
    | [] => None
    | VisitTree (SelectedLeaf value) :: rest =>
        Some (rest, PushSelected value :: emitted)
    | VisitTree (SelectedBranch label children) :: rest =>
        Some (VisitChildren children :: Emit (AssembleSelected label (child_count children)) :: rest,
          emitted)
    | VisitChildren NoChildren :: rest => Some (rest, emitted)
    | VisitChildren (MoreChildren tree children) :: rest =>
        Some (VisitTree tree :: VisitChildren children :: rest, emitted)
    | Emit op :: rest => Some (rest, op :: emitted)
    end.

  Lemma compiler_transition_refines_postorder : forall work emitted next output,
    advance_compiler work emitted = Some (next, output) ->
    rev output ++ work_meaning next = rev emitted ++ work_meaning work /\
    remaining_work next < remaining_work work.
  Proof.
    intros work emitted next output H.
    destruct work as [|task rest]; [discriminate |].
    destruct task as [tree|children|op].
    - destruct tree; inversion H; subst; unfold work_meaning, remaining_work;
        cbn [task_meaning task_work tree_work flat_map fold_right rev compile_tree];
        repeat rewrite <- app_assoc; cbn; split; (reflexivity || lia).
    - destruct children; inversion H; subst;
        unfold work_meaning, remaining_work;
        cbn [task_meaning task_work children_work flat_map fold_right compile_children];
        repeat rewrite <- app_assoc; cbn; split; (reflexivity || lia).
    - inversion H; subst; unfold work_meaning, remaining_work;
        cbn [task_meaning task_work flat_map fold_right rev];
        rewrite <- app_assoc; cbn; split; (reflexivity || lia).
  Qed.

  Lemma unfinished_compiler_has_a_transition : forall work emitted,
    work <> [] -> exists next output,
      advance_compiler work emitted = Some (next, output).
  Proof.
    intros work emitted H. destruct work as [|task rest]; [contradiction |].
    destruct task as [tree|children|op];
      [destruct tree | destruct children |]; eexists; eexists; reflexivity.
  Qed.

  Lemma unfinished_compiler_has_positive_work : forall work,
    work <> [] -> 0 < remaining_work work.
  Proof.
    intros work H. destruct work as [|task rest]; [contradiction |].
    destruct task as [tree|children|op];
      [destruct tree | destruct children |];
      unfold remaining_work; cbn [fold_right task_work tree_work children_work]; lia.
  Qed.

  Fixpoint run_compiler (fuel : nat) (work : list compile_task) (emitted : list instruction)
    : option (list instruction) :=
    match work with
    | [] => Some (rev emitted)
    | _ => match fuel with
      | 0 => None
      | S fuel' => match advance_compiler work emitted with
        | Some (next, output) => run_compiler fuel' next output
        | None => None
        end
      end
    end.

  Theorem sufficient_work_returns_exact_postorder : forall fuel work emitted,
    remaining_work work <= fuel ->
    run_compiler fuel work emitted = Some (rev emitted ++ work_meaning work).
  Proof.
    induction fuel as [|fuel IH]; intros work emitted Hbound.
    - destruct work as [|task rest].
      + cbn. now rewrite app_nil_r.
      + pose proof (unfinished_compiler_has_positive_work (work := task :: rest)
          ltac:(discriminate)). lia.
    - destruct work as [|task rest].
      + cbn. now rewrite app_nil_r.
      + destruct (unfinished_compiler_has_a_transition (work := task :: rest) emitted
          ltac:(discriminate)) as [next [output Hstep]].
        pose proof (@compiler_transition_refines_postorder
          (task :: rest) emitted next output Hstep) as [Hmeaning Hless].
        change (match advance_compiler (task :: rest) emitted with
          | Some (next, output) => run_compiler fuel next output
          | None => None end = Some (rev emitted ++ work_meaning (task :: rest))).
        rewrite Hstep, IH by lia. now rewrite Hmeaning.
  Qed.

  Corollary iterative_compilation_preserves_selected_program : forall tree,
    run_compiler (tree_work tree) [VisitTree tree] [] = Some (compile_tree tree).
  Proof.
    intro tree. rewrite sufficient_work_returns_exact_postorder.
    - unfold work_meaning. cbn [flat_map task_meaning]. now rewrite app_nil_r.
    - unfold remaining_work. cbn [fold_right task_work]. lia.
  Qed.

  Corollary iterative_compilation_preserves_partial_assembly :
    forall (assemble : Label -> list Value -> option Value) tree value,
    (match run_compiler (tree_work tree) [VisitTree tree] [] with
    | Some program => execute assemble program [] | None => None end = Some [value]) <->
    denote_tree assemble tree = Some value.
  Proof.
    intros assemble tree value. rewrite iterative_compilation_preserves_selected_program.
    apply completed_program_returns_exact_selected_value.
  Qed.
End IterativeCompiler.

Print Assumptions compiler_transition_refines_postorder.
Print Assumptions sufficient_work_returns_exact_postorder.
Print Assumptions iterative_compilation_preserves_partial_assembly.

(* Election event transport is deliberately distinct from the ordered Weight
   product. The existing rank protocol stages direct-child events, then the
   owning rule's events, then structural Scan events in child order. A child's
   second component stores its delayed Scan word (SKIP or TAKE + inner events).
   Separating that word must not delete, duplicate or move it across phases. *)
Section ElectionEventTransport.
  Context {Event : Type}.

  Definition absorb_event_words
    (acc child : list Event * list Event) : list Event * list Event :=
    (fst acc ++ fst child, snd acc ++ snd child).

  Lemma staged_event_accumulator_refines_source_order : forall children immediate delayed,
    fold_left absorb_event_words children (immediate, delayed) =
      (immediate ++ flat_map fst children, delayed ++ flat_map snd children).
  Proof.
    induction children as [|[direct scan] rest IH]; intros immediate delayed.
    - cbn. now rewrite !app_nil_r.
    - change (fold_left absorb_event_words rest (immediate ++ direct, delayed ++ scan) =
        (immediate ++ (direct ++ flat_map fst rest), delayed ++ (scan ++ flat_map snd rest))).
      rewrite IH. now rewrite !app_assoc.
  Qed.

  Definition staged_election_events
    (children : list (list Event * list Event)) (owner : list Event) : list Event :=
    let words := fold_left absorb_event_words children ([], []) in
    fst words ++ owner ++ snd words.

  Theorem staged_election_keeps_owner_and_scan_order : forall children owner,
    staged_election_events children owner =
      flat_map fst children ++ owner ++ flat_map snd children.
  Proof.
    intros children owner. unfold staged_election_events.
    rewrite staged_event_accumulator_refines_source_order. reflexivity.
  Qed.

  Corollary staged_election_preserves_every_event_occurrence :
    forall (event_eq : forall a b : Event, {a = b} + {a <> b}) children owner event,
    count_occ event_eq (staged_election_events children owner) event =
      count_occ event_eq (flat_map fst children) event +
      count_occ event_eq owner event + count_occ event_eq (flat_map snd children) event.
  Proof.
    intros event_eq children owner event.
    rewrite staged_election_keeps_owner_and_scan_order, !count_occ_app. lia.
  Qed.
End ElectionEventTransport.

Example equal_position_skip_then_take_keeps_owner_phase :
  staged_election_events [([], [1]); ([], [0])] [77] = [77; 1; 0].
Proof. reflexivity. Qed.

Example absorbing_take_before_owner_and_skip_is_not_preservation :
  [0; 77; 1] <> staged_election_events [([], [1]); ([], [0])] [77].
Proof. discriminate. Qed.

Print Assumptions staged_election_keeps_owner_and_scan_order.
Print Assumptions staged_election_preserves_every_event_occurrence.
