(** * Tagged normalization frames over one explicit worklist

    The generated normalizer historically gives every constructor its own
    assembly-task variant.  The compact machine retains typed visit tasks and
    represents ordinary assembly by one checked tag containing the category,
    constructor, destination slot, and exact value-buffer range.  Beta,
    multi-beta, cancellation, native-fold, and owned-source revisit steps are
    classified separately: factoring ordinary construction cannot turn one of
    those semantic transitions into a constructor assembly.

    This model proves representation equivalence independently of a concrete
    generated language.  The Rust generator reflects the finite constructor
    census and supplies the same visit, ordinary-assembly, and special-step
    functions to both representations.  All pending work remains a list (the
    model of the heap-backed Rust [Vec]); no native call-stack recursion is
    introduced by the factoring.

    The last section (added 2026-10-20) models how the fused visit of an AC
    bag constructor sizes its frame, and how the tagged assembly of the same
    constructor checks that frame.  Before 2026-10-20 the frame counted every
    occurrence of an element, but the visit and the assembly see one stored
    entry per distinct element, so a bag with a repeated element failed the
    assembly check ([fused_bag_check_before_fails_on_a_repeated_element]). *)

From Stdlib Require Import List Arith.PeanoNat Lia.
Import ListNotations.
Set Implicit Arguments.

Module TaggedNormalizationMachine.

  Inductive SpecialKind : Type :=
  | Beta
  | MultiBeta
  | Cancellation
  | NativeFold
  | OwnedSourceRevisit.

  Record AssemblyTag (Category Constructor : Type) : Type := assembly_tag {
    tag_category : Category;
    tag_constructor : Constructor
  }.

  Record Frame : Type := frame {
    (** Abstract identity of the already-live typed source node.  Rust keeps
        this as the existing category-typed raw pointer; the refactor neither
        erases nor extends its lifetime. *)
    frame_source_id : nat;
    frame_result_slot : nat;
    frame_value_base : nat;
    frame_value_count : nat
  }.

  Definition frame_in_bounds {Value : Type}
      (frm : Frame) (values : list Value) : Prop :=
    frame_value_base frm + frame_value_count frm <= length values.

  Definition frame_values {Value : Type}
      (frm : Frame) (values : list Value) : list Value :=
    firstn (frame_value_count frm)
      (skipn (frame_value_base frm) values).

  Theorem frame_values_have_exact_length :
    forall (Value : Type) (frm : Frame) (values : list Value),
      frame_in_bounds frm values ->
      length (frame_values frm values) = frame_value_count frm.
  Proof.
    intros Value [source_id result_slot value_base value_count] values Hbounds.
    unfold frame_values, frame_in_bounds in *. cbn in *.
    rewrite length_firstn, length_skipn. lia.
  Qed.

  Definition frame_prefix {Value : Type}
      (frm : Frame) (values : list Value) : list Value :=
    firstn (frame_value_base frm) values.

  Definition frame_suffix {Value : Type}
      (frm : Frame) (values : list Value) : list Value :=
    skipn (frame_value_base frm + frame_value_count frm) values.

  Theorem frame_partition_recombines :
    forall (Value : Type) (frm : Frame) (values : list Value),
      frame_in_bounds frm values ->
      values =
        frame_prefix frm values ++ frame_values frm values ++
          frame_suffix frm values.
  Proof.
    intros Value [source_id result_slot value_base value_count] values Hbounds.
    unfold frame_prefix, frame_values, frame_suffix, frame_in_bounds in *.
    cbn in *.
    rewrite <- (firstn_skipn value_base values) at 1.
    f_equal.
    rewrite <- (firstn_skipn value_count (skipn value_base values)) at 1.
    f_equal.
    rewrite skipn_skipn. f_equal. lia.
  Qed.

  Section Tasks.
    Context {Category Constructor Visit Value Source : Type}.

    Inductive OldTask : Type :=
    | OldVisit : Visit -> OldTask
    | OldConstructorAssembly : Category -> Constructor -> Frame -> OldTask
    | OldSpecial : SpecialKind -> Category -> Constructor -> Frame -> OldTask.

    Inductive NewTask : Type :=
    | NewVisit : Visit -> NewTask
    | NewTaggedAssembly : AssemblyTag Category Constructor -> Frame -> NewTask
    | NewSpecial : SpecialKind -> Category -> Constructor -> Frame -> NewTask.

    Definition encode_task (task : OldTask) : NewTask :=
      match task with
      | OldVisit visit => NewVisit visit
      | OldConstructorAssembly category constructor frm =>
          NewTaggedAssembly (assembly_tag category constructor) frm
      | OldSpecial kind category constructor frm =>
          NewSpecial kind category constructor frm
      end.

    Definition decode_task (task : NewTask) : OldTask :=
      match task with
      | NewVisit visit => OldVisit visit
      | NewTaggedAssembly tag frm =>
          OldConstructorAssembly
            (tag_category tag) (tag_constructor tag) frm
      | NewSpecial kind category constructor frm =>
          OldSpecial kind category constructor frm
      end.

    Theorem decode_encode_task : forall task,
        decode_task (encode_task task) = task.
    Proof.
      intros task. destruct task; reflexivity.
    Qed.

    Theorem encode_decode_task : forall task,
        encode_task (decode_task task) = task.
    Proof.
      intros task.
      destruct task as [visit | [category constructor] frm |
        kind category constructor frm]; reflexivity.
    Qed.

    Inductive TaskClass : Type :=
    | VisitClass
    | OrdinaryClass
    | SpecialClass : SpecialKind -> TaskClass.

    Definition old_task_class (task : OldTask) : TaskClass :=
      match task with
      | OldVisit _ => VisitClass
      | OldConstructorAssembly _ _ _ => OrdinaryClass
      | OldSpecial kind _ _ _ => SpecialClass kind
      end.

    Definition new_task_class (task : NewTask) : TaskClass :=
      match task with
      | NewVisit _ => VisitClass
      | NewTaggedAssembly _ _ => OrdinaryClass
      | NewSpecial kind _ _ _ => SpecialClass kind
      end.

    Theorem task_class_preserved : forall task,
        new_task_class (encode_task task) = old_task_class task.
    Proof.
      intros task. destruct task; reflexivity.
    Qed.

    Theorem ordinary_never_becomes_special :
      forall category constructor frm kind,
        new_task_class
          (encode_task (OldConstructorAssembly category constructor frm)) <>
        SpecialClass kind.
    Proof.
      intros. discriminate.
    Qed.

    Record OldState : Type := old_state {
      old_tasks : list OldTask;
      old_values : list Value;
      old_sources : list Source
    }.

    Record NewState : Type := new_state {
      new_tasks : list NewTask;
      new_values : list Value;
      new_sources : list Source
    }.

    Definition encode_state (state : OldState) : NewState :=
      new_state
        (map encode_task (old_tasks state))
        (old_values state)
        (old_sources state).

    Variable visit_plan : Visit -> list OldTask.
    Variable ordinary_assembly :
      Category -> Constructor -> Frame -> list Value -> option (list Value).
    Variable special_transition :
      SpecialKind -> Category -> Constructor -> Frame ->
      list Value -> list Source -> option (list OldTask * list Value * list Source).

    Definition old_step (state : OldState) : option OldState :=
      match old_tasks state with
      | [] => None
      | task :: rest =>
          match task with
          | OldVisit visit =>
              Some (old_state
                (visit_plan visit ++ rest)
                (old_values state)
                (old_sources state))
          | OldConstructorAssembly category constructor frm =>
              match ordinary_assembly
                category constructor frm (old_values state) with
              | Some values => Some (old_state rest values (old_sources state))
              | None => None
              end
          | OldSpecial kind category constructor frm =>
              match special_transition kind category constructor frm
                (old_values state) (old_sources state) with
              | Some (planned, values, sources) =>
                  Some (old_state (planned ++ rest) values sources)
              | None => None
              end
          end
      end.

    Definition new_step (state : NewState) : option NewState :=
      match new_tasks state with
      | [] => None
      | task :: rest =>
          match task with
          | NewVisit visit =>
              Some (new_state
                (map encode_task (visit_plan visit) ++ rest)
                (new_values state)
                (new_sources state))
          | NewTaggedAssembly tag frm =>
              match ordinary_assembly
                (tag_category tag) (tag_constructor tag) frm
                (new_values state) with
              | Some values => Some (new_state rest values (new_sources state))
              | None => None
              end
          | NewSpecial kind category constructor frm =>
              match special_transition kind category constructor frm
                (new_values state) (new_sources state) with
              | Some (planned, values, sources) =>
                  Some (new_state
                    (map encode_task planned ++ rest) values sources)
              | None => None
              end
          end
      end.

    Theorem one_step_preserved : forall state,
        new_step (encode_state state) = option_map encode_state (old_step state).
    Proof.
      intros [tasks values sources]. destruct tasks as [|task rest].
      - reflexivity.
      - destruct task as [visit | category constructor frm |
          kind category constructor frm].
        + unfold new_step, old_step, encode_state. cbn. now rewrite map_app.
        + unfold new_step, old_step, encode_state. cbn.
          destruct (ordinary_assembly category constructor frm values);
            reflexivity.
        + unfold new_step, old_step, encode_state. cbn.
          destruct (special_transition kind category constructor frm values sources)
            as [[[planned next_values] next_sources] |] eqn:Hspecial;
            cbn; [now rewrite map_app | reflexivity].
    Qed.

    Theorem failure_preserved : forall state,
        old_step state = None <-> new_step (encode_state state) = None.
    Proof.
      intro state. rewrite one_step_preserved.
      destruct (old_step state); split; intro H; try discriminate; reflexivity.
    Qed.

    Fixpoint old_run (fuel : nat) (state : OldState) : option OldState :=
      match fuel with
      | 0 => None
      | S remaining =>
          match old_tasks state with
          | [] => Some state
          | _ :: _ =>
              match old_step state with
              | Some next => old_run remaining next
              | None => None
              end
          end
      end.

    Fixpoint new_run (fuel : nat) (state : NewState) : option NewState :=
      match fuel with
      | 0 => None
      | S remaining =>
          match new_tasks state with
          | [] => Some state
          | _ :: _ =>
              match new_step state with
              | Some next => new_run remaining next
              | None => None
              end
          end
      end.

    Theorem finite_run_preserved : forall fuel state,
        new_run fuel (encode_state state) =
        option_map encode_state (old_run fuel state).
    Proof.
      induction fuel as [|fuel IH]; intros [tasks values sources];
        [reflexivity |].
      destruct tasks as [|task rest]; [reflexivity |].
      cbn [new_run old_run encode_state].
      rewrite one_step_preserved.
      destruct (old_step (old_state (task :: rest) values sources)) as [next |];
        [apply IH | reflexivity].
    Qed.

    Theorem successful_results_and_sources_preserved :
      forall fuel state final_state,
        old_run fuel state = Some final_state ->
        exists compact_final,
          new_run fuel (encode_state state) = Some compact_final /\
          new_values compact_final = old_values final_state /\
          new_sources compact_final = old_sources final_state.
    Proof.
      intros fuel state final_state Hrun.
      exists (encode_state final_state). split.
      - now rewrite finite_run_preserved, Hrun.
      - now split.
    Qed.

  End Tasks.

  (** ** Fused AC bag frames (added 2026-10-20)

      Rust: the [AcBag] arm of [generate_fused_collection_visit_arm] in
      [macros/src/gen/term_ops/normalize.rs] emits the visit.  The tagged
      assembly of the same constructor (the [__result_cursor] loop that the
      generated [norm_assemble_<cat>] runs) consumes the frame.

      A [HashBag] stores one entry for each distinct element, with a positive
      multiplicity.  [HashBag::len] is the total multiplicity
      ([runtime/src/hashbag.rs], [total_count]).  [HashBag::distinct_len] and
      [HashBag::iter] both see one item for each stored entry.

      The visit reserves [value_count] result slots from [value_base], and it
      pushes one child visit for each entry: the [i]-th entry goes to slot
      [value_base + i].  The assembly walks the same entries, takes one result
      for each entry, and then requires that its cursor ends at
      [value_base + value_count].  A bag is modeled by the multiplicities of
      its stored entries, in iteration order. *)

  Definition Bag : Type := list nat.

  (** [HashBag::len]. *)
  Definition bag_total (bag : Bag) : nat := fold_right Nat.add 0 bag.

  (** [HashBag::distinct_len]: one item for each stored entry. *)
  Definition bag_distinct (bag : Bag) : nat := length bag.

  Definition positive_multiplicities (bag : Bag) : Prop :=
    Forall (fun multiplicity => 0 < multiplicity) bag.

  Definition no_repeated_element (bag : Bag) : Prop :=
    Forall (fun multiplicity => multiplicity = 1) bag.

  (** The slot of each child visit:
      [for (__fused_index, ..) in collection.iter().enumerate()]. *)
  Definition fused_bag_visit_slots (value_base : nat) (bag : Bag) : list nat :=
    seq value_base (length bag).

  (** The assembly cursor after its loop: one step for each entry. *)
  Definition fused_bag_cursor (value_base : nat) (bag : Bag) : nat :=
    value_base + length bag.

  (** [assert_eq!(__result_cursor, value_end)], where
      [value_end = value_base + value_count]. *)
  Definition fused_bag_check (value_base value_count : nat) (bag : Bag) : bool :=
    Nat.eqb (fused_bag_cursor value_base bag) (value_base + value_count).

  (** Before 2026-10-20: [value_count = collection.len()]. *)
  Definition fused_bag_value_count_before (bag : Bag) : nat := bag_total bag.

  (** After 2026-10-20: [value_count = collection.distinct_len()]. *)
  Definition fused_bag_value_count (bag : Bag) : nat := bag_distinct bag.

  Lemma bag_total_bounds_length : forall bag,
      positive_multiplicities bag -> length bag <= bag_total bag.
  Proof.
    unfold bag_total.
    induction bag as [|multiplicity rest IH]; intros Hpositive; cbn; [lia |].
    inversion Hpositive as [|? ? Hhead Htail]; subst.
    specialize (IH Htail). lia.
  Qed.

  Lemma bag_total_is_length_iff : forall bag,
      positive_multiplicities bag ->
      (bag_total bag = length bag <-> no_repeated_element bag).
  Proof.
    induction bag as [|multiplicity rest IH]; intros Hpositive.
    - split; intros _; [constructor | reflexivity].
    - inversion Hpositive as [|? ? Hhead Htail]; subst.
      pose proof (bag_total_bounds_length Htail) as Hbound.
      change (bag_total (multiplicity :: rest)) with (multiplicity + bag_total rest).
      change (length (multiplicity :: rest)) with (S (length rest)).
      split.
      + intros Heq.
        assert (multiplicity = 1) as Hone by lia.
        assert (bag_total rest = length rest) as Hrest by lia.
        constructor; [exact Hone | exact (proj1 (IH Htail) Hrest)].
      + intros Hnone. inversion Hnone as [|? ? Hone Hrest]; subst.
        pose proof (proj2 (IH Htail) Hrest) as Hlength. lia.
  Qed.

  (** The check before 2026-10-20 holds exactly when no element repeats. *)
  Theorem fused_bag_check_before_holds_only_without_repeats :
    forall value_base bag,
      positive_multiplicities bag ->
      (fused_bag_check value_base (fused_bag_value_count_before bag) bag = true <->
       no_repeated_element bag).
  Proof.
    intros value_base bag Hpositive.
    unfold fused_bag_check, fused_bag_cursor, fused_bag_value_count_before.
    rewrite Nat.eqb_eq, <- (bag_total_is_length_iff Hpositive).
    split; intros; lia.
  Qed.

  (** Counterexample: [par{0|0}] is one entry with multiplicity 2. *)
  Theorem fused_bag_check_before_fails_on_a_repeated_element :
    forall value_base,
      fused_bag_check value_base (fused_bag_value_count_before [2]) [2] = false.
  Proof.
    intros value_base. unfold fused_bag_check, fused_bag_cursor,
      fused_bag_value_count_before, bag_total.
    apply Nat.eqb_neq. cbn [length fold_right]. lia.
  Qed.

  (** The same frame reserves a slot that no child visit fills, so the
      slot stays [None]. *)
  Theorem fused_bag_slots_before_leave_a_reserved_slot_unvisited :
    forall value_base,
      value_base + 1 < value_base + fused_bag_value_count_before [2] /\
      ~ In (value_base + 1) (fused_bag_visit_slots value_base [2]).
  Proof.
    intros value_base. split.
    - unfold fused_bag_value_count_before, bag_total. cbn [fold_right]. lia.
    - unfold fused_bag_visit_slots. cbn [length seq In]. intros [Heq | []]. lia.
  Qed.

  (** The corrected frame passes the check for every bag. *)
  Theorem fused_bag_check_holds : forall value_base bag,
      fused_bag_check value_base (fused_bag_value_count bag) bag = true.
  Proof.
    intros value_base bag.
    unfold fused_bag_check, fused_bag_cursor, fused_bag_value_count, bag_distinct.
    apply Nat.eqb_refl.
  Qed.

  (** The child visits fill exactly the reserved slots, each one once. *)
  Theorem fused_bag_visits_fill_exactly_the_reserved_slots :
    forall value_base bag,
      fused_bag_visit_slots value_base bag =
        seq value_base (fused_bag_value_count bag) /\
      NoDup (fused_bag_visit_slots value_base bag).
  Proof.
    intros value_base bag. split; [reflexivity |].
    apply seq_NoDup.
  Qed.

  (** Positive control: without a repeated element the corrected frame is
      the frame before 2026-10-20. *)
  Theorem fused_bag_value_count_unchanged_without_repeats : forall bag,
      positive_multiplicities bag -> no_repeated_element bag ->
      fused_bag_value_count bag = fused_bag_value_count_before bag.
  Proof.
    intros bag Hpositive Hnone.
    unfold fused_bag_value_count, fused_bag_value_count_before, bag_distinct.
    symmetry. exact (proj2 (bag_total_is_length_iff Hpositive) Hnone).
  Qed.

  (** The shared assembly receives each entry's result repeated by its
      multiplicity ([for _ in 1..__multiplicity { values.push(..) }] and one
      more push), so it sees the total multiplicity of the bag. *)
  Definition fused_bag_shared_values {Value : Type}
      (results : list Value) (bag : Bag) : list Value :=
    flat_map (fun entry => repeat (fst entry) (snd entry)) (combine results bag).

  Theorem fused_bag_shared_values_have_the_total_multiplicity :
    forall (Value : Type) (results : list Value) bag,
      length results = length bag ->
      length (fused_bag_shared_values results bag) = bag_total bag.
  Proof.
    intros Value results. induction results as [|result rest IH];
      intros [|multiplicity bag] Hlength; cbn in *; try discriminate; [reflexivity |].
    unfold fused_bag_shared_values in *. cbn.
    rewrite length_app, repeat_length. f_equal. apply IH. lia.
  Qed.

  Print Assumptions frame_values_have_exact_length.
  Print Assumptions frame_partition_recombines.
  Print Assumptions decode_encode_task.
  Print Assumptions encode_decode_task.
  Print Assumptions task_class_preserved.
  Print Assumptions ordinary_never_becomes_special.
  Print Assumptions one_step_preserved.
  Print Assumptions failure_preserved.
  Print Assumptions finite_run_preserved.
  Print Assumptions successful_results_and_sources_preserved.
  Print Assumptions fused_bag_check_before_holds_only_without_repeats.
  Print Assumptions fused_bag_check_before_fails_on_a_repeated_element.
  Print Assumptions fused_bag_slots_before_leave_a_reserved_slot_unvisited.
  Print Assumptions fused_bag_check_holds.
  Print Assumptions fused_bag_visits_fill_exactly_the_reserved_slots.
  Print Assumptions fused_bag_value_count_unchanged_without_repeats.
  Print Assumptions fused_bag_shared_values_have_the_total_multiplicity.

End TaggedNormalizationMachine.
