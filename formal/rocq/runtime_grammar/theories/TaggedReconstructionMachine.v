(** * Checked tagged reconstruction machine

    Generated typed reconstruction is a bounded pushdown machine over a flat
    Dovetail derivation spine.  A stable operator discriminant selects one
    immutable constructor descriptor.  The descriptor first validates the
    complete local node shape, then publishes an ordered producer plan and one
    assembly frame.  No failed validation may mutate either the pending-task
    stack or the value stack.

    The concrete Rust task store is a [Vec] used last-in, first-out.  A plan in
    semantic execution order is therefore appended in reverse.  Optional
    absence is an ordinary producer task: emitting its value during parent
    scheduling would reorder it with respect to deferred sibling visits.

    This module is intentionally independent of a generated language's size.
    It proves the dense-table, shape, scheduling, frame-ownership, and bounded
    transition laws once; generated Rust tables are reflected instances of
    these definitions. *)

From Stdlib Require Import List ListDec Bool Arith.PeanoNat Lia.
Import ListNotations.
Set Implicit Arguments.

Module TaggedReconstructionMachine.

  Definition Ref : Type := nat.

  Inductive VisitMode : Type :=
  | Required
  | Optional : nat -> VisitMode.

  Inductive Projection : Type :=
  | TokenProjection
  | SequenceProjection : nat -> Projection
  | WithheldProjection : nat -> Projection.

  Inductive BinderKind : Type :=
  | SingleBinder
  | MultiBinder : nat -> BinderKind.

  Inductive CollectionKind : Type :=
  | SequenceCollection
  | BagCollection
  | SetCollection
  | MapCollection.

  Inductive PairRole : Type :=
  | CollectionPair : CollectionKind -> nat -> PairRole
  | PathMapPair : nat -> PairRole
  | NativePathMapPair : nat -> nat -> PairRole.

  Inductive PathRole : Type :=
  | TypedPathMap : nat -> PathRole
  | NativePathMap : nat -> nat -> PathRole.

  Inductive FieldPlan : Type :=
  | CategoryField : nat -> VisitMode -> FieldPlan
  | ProjectedField : Projection -> VisitMode -> FieldPlan.

  Inductive AssemblyKind : Type :=
  | TypedConstructor
  | AcConstructor : CollectionKind -> AssemblyKind
  | BinderConstructor : BinderKind -> AssemblyKind
  | PathMapConstructor : PathRole -> AssemblyKind.

  Inductive ConstructorPlan : Type :=
  | RejectPlan
  | DirectLeafPlan
  | NullaryPlan
  | FixedPlan : list FieldPlan -> ConstructorPlan
  | VariadicPlan : nat -> CollectionKind -> ConstructorPlan
  | PairVariadicPlan : PairRole -> ConstructorPlan
  | OrderedSequencePlan : nat -> ConstructorPlan
  | BinderPlan : list FieldPlan -> nat -> BinderKind -> ConstructorPlan
  | PathMapPlan : nat -> ConstructorPlan
  | NativeZipperPlan : nat -> nat -> ConstructorPlan.

  Record Descriptor : Type := descriptor {
    descriptor_category : nat;
    descriptor_constructor : nat;
    descriptor_discriminant : nat;
    descriptor_plan : ConstructorPlan
  }.

  Inductive SentinelIdentity : Type :=
  | FieldNoneSentinel
  | BinderAritySentinel
  | TokenSentinel
  | SequenceSentinel : nat -> SentinelIdentity
  | WithheldSentinel : nat -> SentinelIdentity
  | PairSentinel : PairRole -> SentinelIdentity
  | PathModeSentinel : PathRole -> SentinelIdentity
  | BytesSentinel.

  Inductive DispatchSlot : Type :=
  | ConstructorSlot : Descriptor -> DispatchSlot
  | SentinelSlot : nat -> SentinelIdentity -> DispatchSlot.

  Definition slot_discriminant (slot : DispatchSlot) : nat :=
    match slot with
    | ConstructorSlot value => descriptor_discriminant value
    | SentinelSlot discriminant _ => discriminant
    end.

  Definition descriptor_key (value : Descriptor) : nat * nat :=
    (descriptor_category value, descriptor_constructor value).

  Fixpoint constructor_descriptors (table : list DispatchSlot)
      : list Descriptor :=
    match table with
    | [] => []
    | ConstructorSlot value :: rest =>
        value :: constructor_descriptors rest
    | SentinelSlot _ _ :: rest => constructor_descriptors rest
    end.

  Fixpoint indexed_from (next : nat) (table : list DispatchSlot) : Prop :=
    match table with
    | [] => True
    | slot :: rest =>
        slot_discriminant slot = next /\ indexed_from (S next) rest
    end.

  Definition ValidDenseTable (table : list DispatchSlot) : Prop :=
    indexed_from 0 table /\
    NoDup (map descriptor_key (constructor_descriptors table)).

  Fixpoint indexed_from_dec (next : nat) (table : list DispatchSlot)
      : {indexed_from next table} + {~ indexed_from next table}.
  Proof.
    destruct table as [|slot rest].
    - left. exact I.
    - destruct (Nat.eq_dec (slot_discriminant slot) next) as [Hequal | Hunequal].
      + destruct (indexed_from_dec (S next) rest) as [Hrest | Hrest].
        * left. now split.
        * right. intros [_ Hcontra]. now apply Hrest.
      + right. intros [Hcontra _]. now apply Hunequal.
  Defined.

  Definition descriptor_key_eq_dec :
      forall left right : nat * nat, {left = right} + {left <> right}.
  Proof.
    decide equality; apply Nat.eq_dec.
  Defined.

  Definition valid_dense_table_dec (table : list DispatchSlot)
      : {ValidDenseTable table} + {~ ValidDenseTable table}.
  Proof.
    unfold ValidDenseTable.
    destruct (indexed_from_dec 0 table) as [Hindexed | Hindexed].
    - destruct (NoDup_dec descriptor_key_eq_dec
        (map descriptor_key (constructor_descriptors table)))
        as [Hunique | Hunique].
      + left. now split.
      + right. intros [_ Hcontra]. now apply Hunique.
    - right. intros [Hcontra _]. now apply Hindexed.
  Defined.

  Definition validate_dense_table (table : list DispatchSlot) : bool :=
    if valid_dense_table_dec table then true else false.

  Theorem validate_dense_table_reflects_validity : forall table,
      validate_dense_table table = true <-> ValidDenseTable table.
  Proof.
    intros table. unfold validate_dense_table.
    destruct (valid_dense_table_dec table) as [Hvalid | Hinvalid].
    - split; [intros; exact Hvalid | intros; reflexivity].
    - split; [intros H; discriminate | intros H; now exfalso].
  Qed.

  Lemma indexed_from_nth_error :
    forall table base index slot,
      indexed_from base table ->
      nth_error table index = Some slot ->
      slot_discriminant slot = base + index.
  Proof.
    intros table. induction table as [|head rest IH];
      intros base index slot Hindexed Hnth; [destruct index; discriminate |].
    destruct Hindexed as [Hhead Hrest]. destruct index as [|index].
    - cbn in Hnth. inversion Hnth; subst. cbn. lia.
    - cbn in Hnth. specialize (IH (S base) index slot Hrest Hnth).
      lia.
  Qed.

  Lemma nth_constructor_in_descriptors :
    forall table index value,
      nth_error table index = Some (ConstructorSlot value) ->
      In value (constructor_descriptors table).
  Proof.
    intros table. induction table as [|head rest IH];
      intros index value Hnth; [destruct index; discriminate |].
    destruct index as [|index].
    - cbn in Hnth. inversion Hnth; subst head. cbn. now left.
    - cbn in Hnth. destruct head; cbn; [right |]; now apply IH with index.
  Qed.

  Definition descriptor_matches
      (category constructor : nat) (value : Descriptor) : bool :=
    Nat.eqb category (descriptor_category value) &&
      Nat.eqb constructor (descriptor_constructor value).

  Fixpoint pair_lookup
      (category constructor : nat) (values : list Descriptor)
      : option Descriptor :=
    match values with
    | [] => None
    | value :: rest =>
        if descriptor_matches category constructor value
        then Some value
        else pair_lookup category constructor rest
    end.

  Lemma descriptor_matches_refl : forall value,
      descriptor_matches
        (descriptor_category value) (descriptor_constructor value) value = true.
  Proof.
    intros []. unfold descriptor_matches. cbn.
    now rewrite !Nat.eqb_refl.
  Qed.

  Lemma descriptor_matches_equalities : forall category constructor value,
      descriptor_matches category constructor value = true ->
      category = descriptor_category value /\
      constructor = descriptor_constructor value.
  Proof.
    intros category constructor value Hmatch.
    unfold descriptor_matches in Hmatch.
    apply andb_true_iff in Hmatch as [Hcategory Hconstructor].
    now rewrite !Nat.eqb_eq in *.
  Qed.

  Lemma pair_lookup_complete : forall values value,
      NoDup (map descriptor_key values) ->
      In value values ->
      pair_lookup
        (descriptor_category value) (descriptor_constructor value) values =
        Some value.
  Proof.
    intros values. induction values as [|head rest IH];
      intros value Hunique Hin; [inversion Hin |].
    inversion Hunique as [|head_key rest_keys Hfresh Hrest]; subst.
    destruct Hin as [Hequal | Hin].
    - subst head. cbn. now rewrite descriptor_matches_refl.
    - cbn.
      destruct (descriptor_matches
        (descriptor_category value) (descriptor_constructor value) head)
        eqn:Hmatches.
      + apply descriptor_matches_equalities in Hmatches
          as [Hcategory Hconstructor].
        exfalso. apply Hfresh.
        assert (Hkey : descriptor_key head = descriptor_key value).
        { unfold descriptor_key. cbn. now rewrite <- Hcategory, <- Hconstructor. }
        rewrite Hkey. now apply in_map.
      + now apply IH.
  Qed.

  Definition dense_lookup
      (expected_category discriminant : nat) (table : list DispatchSlot)
      : option Descriptor :=
    match nth_error table discriminant with
    | Some (ConstructorSlot value) =>
        if Nat.eqb expected_category (descriptor_category value) &&
           Nat.eqb discriminant (descriptor_discriminant value)
        then Some value
        else None
    | _ => None
    end.

  Theorem dense_lookup_refines_pair_lookup :
    forall table expected discriminant value,
      ValidDenseTable table ->
      dense_lookup expected discriminant table = Some value ->
      descriptor_category value = expected /\
      descriptor_discriminant value = discriminant /\
      pair_lookup expected (descriptor_constructor value)
        (constructor_descriptors table) = Some value.
  Proof.
    intros table expected discriminant value [Hindexed Hunique] Hlookup.
    unfold dense_lookup in Hlookup.
    destruct (nth_error table discriminant) as [slot |] eqn:Hnth;
      try discriminate.
    destruct slot as [found | sentinel identity]; try discriminate.
    destruct (Nat.eqb expected (descriptor_category found) &&
      Nat.eqb discriminant (descriptor_discriminant found)) eqn:Hchecks;
      try discriminate.
    inversion Hlookup; subst found.
    apply andb_true_iff in Hchecks as [Hcategory Hdisc].
    apply Nat.eqb_eq in Hcategory, Hdisc.
    split; [symmetry; assumption |]. split; [symmetry; assumption |].
    rewrite Hcategory. apply pair_lookup_complete; [assumption |].
    now apply nth_constructor_in_descriptors with discriminant.
  Qed.

  (** The exact spine identities read by local shape validation.  Ordinary
      category nodes may themselves have children; every backend-only sentinel
      is required to be a leaf. *)
  Inductive SpineIdentity : Type :=
  | CategoryIdentity : nat -> SpineIdentity
  | FieldNoneIdentity : nat -> SpineIdentity
  | BinderArityIdentity : nat -> SpineIdentity
  | ProjectionIdentity : Projection -> SpineIdentity
  | PairIdentity : PairRole -> SpineIdentity
  | PathModeIdentity : PathRole -> nat -> SpineIdentity
  | BytesIdentity : SpineIdentity.

  Record SpineNode : Type := spine_node {
    spine_identity : SpineIdentity;
    spine_children : list Ref
  }.

  Definition is_leaf (node : SpineNode) : bool :=
    Nat.eqb (length (spine_children node)) 0.

  Definition projection_eqb (left right : Projection) : bool :=
    match left, right with
    | TokenProjection, TokenProjection => true
    | SequenceProjection left_category, SequenceProjection right_category
    | WithheldProjection left_category, WithheldProjection right_category =>
        Nat.eqb left_category right_category
    | _, _ => false
    end.

  Definition pair_role_eqb (left right : PairRole) : bool :=
    match left, right with
    | CollectionPair left_kind left_category,
        CollectionPair right_kind right_category =>
        let kind_eq :=
          match left_kind, right_kind with
          | SequenceCollection, SequenceCollection
          | BagCollection, BagCollection
          | SetCollection, SetCollection
          | MapCollection, MapCollection => true
          | _, _ => false
          end in
        kind_eq && Nat.eqb left_category right_category
    | PathMapPair left_category, PathMapPair right_category =>
        Nat.eqb left_category right_category
    | NativePathMapPair left_key left_value,
        NativePathMapPair right_key right_value =>
        Nat.eqb left_key right_key && Nat.eqb left_value right_value
    | _, _ => false
    end.

  Definition path_role_eqb (left right : PathRole) : bool :=
    match left, right with
    | TypedPathMap left_category, TypedPathMap right_category =>
        Nat.eqb left_category right_category
    | NativePathMap left_key left_value, NativePathMap right_key right_value =>
        Nat.eqb left_key right_key && Nat.eqb left_value right_value
    | _, _ => false
    end.

  Definition validate_required_field
      (plan : FieldPlan) (node : SpineNode) : bool :=
    match plan, spine_identity node with
    | CategoryField expected Required, CategoryIdentity actual =>
        Nat.eqb expected actual
    | ProjectedField expected Required, ProjectionIdentity actual =>
        projection_eqb expected actual && is_leaf node
    | _, _ => false
    end.

  Definition validate_field (plan : FieldPlan) (node : SpineNode) : bool :=
    match plan with
    | CategoryField expected (Optional index) =>
        match spine_identity node with
        | FieldNoneIdentity actual => Nat.eqb index actual && is_leaf node
        | _ => validate_required_field (CategoryField expected Required) node
        end
    | ProjectedField expected (Optional index) =>
        match spine_identity node with
        | FieldNoneIdentity actual => Nat.eqb index actual && is_leaf node
        | _ => validate_required_field (ProjectedField expected Required) node
        end
    | _ => validate_required_field plan node
    end.

  Fixpoint validate_fields
      (plans : list FieldPlan) (nodes : list SpineNode) : bool :=
    match plans, nodes with
    | [], [] => true
    | plan :: plan_rest, node :: node_rest =>
        validate_field plan node && validate_fields plan_rest node_rest
    | _, _ => false
    end.

  Lemma validate_fields_exact_arity : forall plans nodes,
      validate_fields plans nodes = true -> length plans = length nodes.
  Proof.
    intros plans. induction plans as [|plan rest IH];
      intros nodes Hvalid; destruct nodes as [|node nodes]; cbn in Hvalid;
      try discriminate; auto.
    apply andb_true_iff in Hvalid as [_ Hrest]. cbn. f_equal.
    now apply IH.
  Qed.

  Definition validate_leaf_identity (node : SpineNode) : bool :=
    match spine_identity node with
    | CategoryIdentity _ => is_leaf node
    | _ => false
    end.

  Definition validate_binder_marker
      (kind : BinderKind) (node : SpineNode) : bool :=
    match kind, spine_identity node with
    | SingleBinder, BinderArityIdentity arity =>
        Nat.eqb arity 1 && is_leaf node
    | MultiBinder maximum, BinderArityIdentity arity =>
        Nat.leb arity maximum && is_leaf node
    | _, _ => false
    end.

  Definition validate_pair (role : PairRole) (node : SpineNode) : bool :=
    match spine_identity node with
    | PairIdentity actual =>
        pair_role_eqb role actual && Nat.eqb (length (spine_children node)) 2
    | _ => false
    end.

  Fixpoint all_category_nodes (category : nat) (nodes : list SpineNode) : bool :=
    match nodes with
    | [] => true
    | node :: rest =>
        match spine_identity node with
        | CategoryIdentity actual =>
            Nat.eqb category actual && all_category_nodes category rest
        | _ => false
        end
    end.

  Fixpoint all_pairs (role : PairRole) (nodes : list SpineNode) : bool :=
    match nodes with
    | [] => true
    | node :: rest => validate_pair role node && all_pairs role rest
    end.

  Definition validate_path_entries
      (role : PathRole) (mode : nat) (entries : list SpineNode) : bool :=
    match role, mode with
    | TypedPathMap element, 0 => Nat.eqb (length entries) 0
    | TypedPathMap element, 1 => all_category_nodes element entries
    | TypedPathMap element, 2 => all_pairs (PathMapPair element) entries
    | NativePathMap key value, 0 => Nat.eqb (length entries) 0
    | NativePathMap key value, 1 => all_category_nodes key entries
    | NativePathMap key value, 2 =>
        all_pairs (NativePathMapPair key value) entries
    | _, _ => false
    end.

  Definition validate_path_mode
      (role : PathRole) (node : SpineNode) : option nat :=
    match spine_identity node with
    | PathModeIdentity actual mode =>
        if path_role_eqb role actual && Nat.leb mode 2 && is_leaf node
        then Some mode
        else None
    | _ => None
    end.

  Definition split_last {A : Type} (values : list A) : option (list A * A) :=
    match rev values with
    | [] => None
    | last :: reverse_prefix => Some (rev reverse_prefix, last)
    end.

  Definition validate_shape
      (plan : ConstructorPlan) (children : list SpineNode) : bool :=
    match plan with
    | RejectPlan => false
    | DirectLeafPlan | NullaryPlan => Nat.eqb (length children) 0
    | FixedPlan fields => validate_fields fields children
    | VariadicPlan element _ => all_category_nodes element children
    | PairVariadicPlan role => all_pairs role children
    | OrderedSequencePlan element =>
        match children with
        | [node] => validate_required_field
            (ProjectedField (SequenceProjection element) Required) node
        | _ => false
        end
    | BinderPlan fields body kind =>
        if Nat.eqb (length children) (length fields + 2) then
          match firstn (length fields) children,
                nth_error children (length fields),
                nth_error children (S (length fields)) with
          | prefix, Some marker, Some body_node =>
              validate_fields fields prefix &&
              validate_binder_marker kind marker &&
              match spine_identity body_node with
              | CategoryIdentity actual => Nat.eqb body actual
              | _ => false
              end
          | _, _, _ => false
          end
        else false
    | PathMapPlan element =>
        match children with
        | [] => false
        | mode_node :: entries =>
            match validate_path_mode (TypedPathMap element) mode_node with
            | Some mode => validate_path_entries (TypedPathMap element) mode entries
            | None => false
            end
        end
    | NativeZipperPlan key value =>
        match children with
        | [] => false
        | mode_node :: rest =>
            match split_last rest with
            | Some (entries, focus) =>
                match validate_path_mode (NativePathMap key value) mode_node,
                      spine_identity focus with
                | Some mode, BytesIdentity =>
                    validate_path_entries (NativePathMap key value) mode entries &&
                    is_leaf focus
                | _, _ => false
                end
            | None => false
            end
        end
    end.

  Theorem fixed_shape_rejects_every_arity_mismatch :
    forall fields children,
      length fields <> length children ->
      validate_shape (FixedPlan fields) children = false.
  Proof.
    intros fields children Hmismatch. cbn.
    destruct (validate_fields fields children) eqn:Hvalid; [|reflexivity].
    exfalso. apply Hmismatch. now apply validate_fields_exact_arity.
  Qed.

  Theorem leaf_and_nullary_shapes_reject_children :
    forall children,
      children <> [] ->
      validate_shape DirectLeafPlan children = false /\
      validate_shape NullaryPlan children = false.
  Proof.
    intros children Hnonempty. destruct children as [|child rest];
      [contradiction |]. cbn. auto.
  Qed.

  Lemma binder_shape_exact_arity : forall fields body kind children,
      validate_shape (BinderPlan fields body kind) children = true ->
      length children = length fields + 2.
  Proof.
    intros fields body kind children Hvalid. cbn in Hvalid.
    destruct (Nat.eqb (length children) (length fields + 2)) eqn:Hexact;
      try discriminate.
    now apply Nat.eqb_eq in Hexact.
  Qed.

  Inductive ProducerTask : Type :=
  | Visit : nat -> VisitMode -> Ref -> ProducerTask
  | DecodeProjection : Projection -> VisitMode -> Ref -> ProducerTask
  | DecodeBinder : BinderKind -> Ref -> ProducerTask
  | DecodeBytes : Ref -> ProducerTask
  | ExpandPair : PairRole -> Ref -> ProducerTask
  | PlanPathMapTask : PathRole -> Ref -> list Ref -> option Ref -> nat -> ProducerTask
  | EmitAbsent : nat -> ProducerTask.

  Record Frame : Type := frame {
    frame_category : nat;
    frame_constructor : nat;
    frame_value_base : nat;
    frame_input_count : nat;
    frame_assembly_kind : AssemblyKind
  }.

  Inductive Task : Type :=
  | Produce : ProducerTask -> Task
  | AssembleFrame : Frame -> Task.

  Definition append_plan_lifo (old plan : list Task) : list Task :=
    old ++ rev plan.

  Definition pop_order (stored : list Task) : list Task := rev stored.

  Theorem lifo_append_executes_plan_before_old_work : forall old plan,
      pop_order (append_plan_lifo old plan) = plan ++ pop_order old.
  Proof.
    intros old plan. unfold pop_order, append_plan_lifo.
    now rewrite rev_app_distr, rev_involutive.
  Qed.

  Inductive ProducedValue : Type :=
  | ProducedCategory : nat -> ProducedValue
  | ProducedProjection : Projection -> ProducedValue
  | ProducedBinder : BinderKind -> ProducedValue
  | ProducedBytes : ProducedValue
  | ProducedPair : PairRole -> ProducedValue
  | ProducedPathMap : PathRole -> ProducedValue
  | ProducedAbsent : nat -> ProducedValue.

  Definition producer_output (task : ProducerTask) : ProducedValue :=
    match task with
    | Visit category _ _ => ProducedCategory category
    | DecodeProjection projection _ _ => ProducedProjection projection
    | DecodeBinder kind _ => ProducedBinder kind
    | DecodeBytes _ => ProducedBytes
    | ExpandPair role _ => ProducedPair role
    | PlanPathMapTask role _ _ _ _ => ProducedPathMap role
    | EmitAbsent index => ProducedAbsent index
    end.

  Fixpoint producer_trace (tasks : list Task) : list ProducedValue :=
    match tasks with
    | [] => []
    | Produce producer :: rest =>
        producer_output producer :: producer_trace rest
    | AssembleFrame _ :: rest => producer_trace rest
    end.

  Lemma producer_trace_app : forall left right,
      producer_trace (left ++ right) =
      producer_trace left ++ producer_trace right.
  Proof.
    intros left. induction left as [|task rest IH]; intros right; cbn.
    - reflexivity.
    - destruct task; cbn; now rewrite IH.
  Qed.

  Theorem optional_absence_is_position_preserving :
    producer_trace
      [Produce (Visit 7 Required 41); Produce (EmitAbsent 1)] =
      [ProducedCategory 7; ProducedAbsent 1].
  Proof.
    reflexivity.
  Qed.

  Example immediate_optional_emission_reverses_mixed_values :
    [ProducedAbsent 1; ProducedCategory 7] <>
    [ProducedCategory 7; ProducedAbsent 1].
  Proof.
    discriminate.
  Qed.

  Definition schedule_transaction
      (plan : ConstructorPlan) (children : list SpineNode)
      (tasks : list Task) (published : list Task)
      : option (list Task) :=
    if validate_shape plan children
    then Some (append_plan_lifo tasks published)
    else None.

  Theorem invalid_shape_publishes_no_tasks :
    forall plan children tasks published,
      validate_shape plan children = false ->
      schedule_transaction plan children tasks published = None.
  Proof.
    intros. unfold schedule_transaction. now rewrite H.
  Qed.

  (** Assembly owns exactly the value suffix beginning at [frame_value_base].
      A successful frame preserves the prefix and replaces all inputs by one
      result. *)
  Definition assemble_values
      (current : list nat) (current_frame : Frame) (result : nat)
      : option (list nat) :=
    if Nat.eqb (length current)
        (frame_value_base current_frame + frame_input_count current_frame)
    then Some (firstn (frame_value_base current_frame) current ++ [result])
    else None.

  Theorem successful_assembly_has_exact_net_height :
    forall current current_frame result output,
      assemble_values current current_frame result = Some output ->
      length current =
        frame_value_base current_frame + frame_input_count current_frame /\
      length output = S (frame_value_base current_frame).
  Proof.
    intros current current_frame result output Hassemble.
    unfold assemble_values in Hassemble.
    destruct (Nat.eqb (length current)
      (frame_value_base current_frame + frame_input_count current_frame))
      eqn:Hexact; try discriminate.
    apply Nat.eqb_eq in Hexact. inversion Hassemble; subst output.
    split; [assumption |]. rewrite length_app. cbn.
    rewrite length_firstn, Hexact. rewrite Nat.min_l; lia.
  Qed.

  Theorem successful_assembly_preserves_prefix :
    forall current current_frame result output,
      assemble_values current current_frame result = Some output ->
      firstn (frame_value_base current_frame) output =
      firstn (frame_value_base current_frame) current.
  Proof.
    intros current current_frame result output Hassemble.
    unfold assemble_values in Hassemble.
    destruct (Nat.eqb (length current)
      (frame_value_base current_frame + frame_input_count current_frame))
      eqn:Hexact; try discriminate.
    apply Nat.eqb_eq in Hexact. inversion Hassemble; subst output.
    assert (Hbase : frame_value_base current_frame <= length current) by
      (rewrite Hexact; lia).
    rewrite firstn_app, firstn_firstn, Nat.min_id.
    rewrite length_firstn, Nat.min_l by exact Hbase.
    rewrite Nat.sub_diag. cbn. now rewrite app_nil_r.
  Qed.

  Definition checked_path_value_count
      (mode entry_count focus_count limit : nat) : option nat :=
    let multiplier := if Nat.eqb mode 2 then 2 else 1 in
    if Nat.leb mode 2 then
      let total := focus_count + 1 + multiplier * entry_count in
      if Nat.leb total limit then Some total else None
    else None.

  Theorem checked_path_value_count_respects_limit :
    forall mode entries focus limit total,
      checked_path_value_count mode entries focus limit = Some total ->
      mode <= 2 /\ total <= limit.
  Proof.
    intros mode entries focus limit total Hcount.
    unfold checked_path_value_count in Hcount.
    destruct (Nat.eqb mode 2);
      destruct (Nat.leb mode 2) eqn:Hmode; try discriminate;
      destruct (Nat.leb _ limit) eqn:Hlimit; try discriminate;
      inversion Hcount; subst total;
      apply Nat.leb_le in Hmode, Hlimit; auto.
  Qed.

  Definition transition_node_reads (task : Task) : nat :=
    match task with
    | AssembleFrame _ => 0
    | Produce (EmitAbsent _) => 0
    | Produce _ => 1
    end.

  Theorem every_transition_decodes_at_most_one_arena_node : forall task,
      transition_node_reads task <= 1.
  Proof.
    intros [producer | current_frame]; cbn; [destruct producer |]; cbn; lia.
  Qed.

  (** A source-neutral spine field relation used to compose this machine with
      the generated canonical semantic adapter. *)
  Inductive CanonicalSpineField : Type :=
  | CanonicalChild : nat -> Ref -> CanonicalSpineField
  | CanonicalOptional : nat -> nat -> option Ref -> CanonicalSpineField
  | CanonicalProjection : Projection -> nat -> option Ref -> CanonicalSpineField
  | CanonicalBinder : BinderKind -> nat -> nat -> Ref -> CanonicalSpineField
  | CanonicalPairField : PairRole -> Ref -> Ref -> CanonicalSpineField
  | CanonicalPathMode : PathRole -> nat -> CanonicalSpineField
  | CanonicalBytes : Ref -> CanonicalSpineField.

  Inductive EncodedSpineField : Type :=
  | EncodedReference : nat -> Ref -> EncodedSpineField
  | EncodedNone : nat -> EncodedSpineField
  | EncodedProjection : Projection -> Ref -> EncodedSpineField
  | EncodedBinder : BinderKind -> nat -> nat -> Ref -> EncodedSpineField
  | EncodedPair : PairRole -> Ref -> Ref -> EncodedSpineField
  | EncodedMode : PathRole -> nat -> EncodedSpineField
  | EncodedBytes : Ref -> EncodedSpineField.

  Definition spine_encode (field : CanonicalSpineField) : EncodedSpineField :=
    match field with
    | CanonicalChild category reference => EncodedReference category reference
    | CanonicalOptional category index (Some reference) =>
        EncodedReference category reference
    | CanonicalOptional _ index None => EncodedNone index
    | CanonicalProjection projection index (Some reference) =>
        EncodedProjection projection reference
    | CanonicalProjection _ index None => EncodedNone index
    | CanonicalBinder kind domain arity body =>
        EncodedBinder kind domain arity body
    | CanonicalPairField role key value => EncodedPair role key value
    | CanonicalPathMode role mode => EncodedMode role mode
    | CanonicalBytes reference => EncodedBytes reference
    end.

  Definition spine_decode
      (expected : CanonicalSpineField) (encoded : EncodedSpineField)
      : option CanonicalSpineField :=
    match expected, encoded with
    | CanonicalChild category _, EncodedReference actual reference =>
        if Nat.eqb category actual
        then Some (CanonicalChild category reference)
        else None
    | CanonicalOptional category index _, EncodedReference actual reference =>
        if Nat.eqb category actual
        then Some (CanonicalOptional category index (Some reference))
        else None
    | CanonicalOptional category index _, EncodedNone actual =>
        if Nat.eqb index actual
        then Some (CanonicalOptional category index None)
        else None
    | CanonicalProjection projection index _, EncodedProjection actual reference =>
        if projection_eqb projection actual
        then Some (CanonicalProjection projection index (Some reference))
        else None
    | CanonicalProjection projection index _, EncodedNone actual =>
        if Nat.eqb index actual
        then Some (CanonicalProjection projection index None)
        else None
    | CanonicalBinder kind domain _ _, EncodedBinder actual_kind actual_domain arity body =>
        let kind_eq :=
          match kind, actual_kind with
          | SingleBinder, SingleBinder => true
          | MultiBinder left_bound, MultiBinder right_bound =>
              Nat.eqb left_bound right_bound
          | _, _ => false
          end in
        if kind_eq && Nat.eqb domain actual_domain
        then Some (CanonicalBinder kind domain arity body)
        else None
    | CanonicalPairField role _ _, EncodedPair actual key value =>
        if pair_role_eqb role actual
        then Some (CanonicalPairField role key value)
        else None
    | CanonicalPathMode role _, EncodedMode actual mode =>
        if path_role_eqb role actual
        then Some (CanonicalPathMode role mode)
        else None
    | CanonicalBytes _, EncodedBytes reference =>
        Some (CanonicalBytes reference)
    | _, _ => None
    end.

  Theorem spine_decode_encode : forall field,
      spine_decode field (spine_encode field) = Some field.
  Proof.
    intros [category reference
      | category index optional_reference
      | projection index optional_reference
      | kind domain arity body
      | role key value
      | role mode
      | reference].
    - cbn. now rewrite Nat.eqb_refl.
    - destruct optional_reference; cbn; now rewrite Nat.eqb_refl.
    - destruct optional_reference;
        destruct projection; cbn; now rewrite ?Nat.eqb_refl.
    - destruct kind; cbn; now rewrite ?Nat.eqb_refl.
    - destruct role as
        [collection_kind category | category | key_category value_category].
      + destruct collection_kind; cbn; now rewrite ?Nat.eqb_refl.
      + cbn. now rewrite Nat.eqb_refl.
      + cbn. now rewrite !Nat.eqb_refl.
    - destruct role; cbn; now rewrite ?Nat.eqb_refl.
    - reflexivity.
  Qed.

  (** The declared body category is independent of the enclosing constructor
      category.  Routing the body through the enclosing category is correct
      only when those categories happen to coincide. *)
  Definition binder_body_route_valid
      (declared_body scheduled_body : nat) : bool :=
    Nat.eqb declared_body scheduled_body.

  Theorem declared_binder_body_route_is_valid : forall category,
      binder_body_route_valid category category = true.
  Proof.
    intros. apply Nat.eqb_refl.
  Qed.

  Example enclosing_category_is_not_a_valid_cross_category_body_route :
    binder_body_route_valid 3 8 = false.
  Proof.
    reflexivity.
  Qed.

  Print Assumptions validate_dense_table_reflects_validity.
  Print Assumptions dense_lookup_refines_pair_lookup.
  Print Assumptions fixed_shape_rejects_every_arity_mismatch.
  Print Assumptions leaf_and_nullary_shapes_reject_children.
  Print Assumptions binder_shape_exact_arity.
  Print Assumptions lifo_append_executes_plan_before_old_work.
  Print Assumptions optional_absence_is_position_preserving.
  Print Assumptions invalid_shape_publishes_no_tasks.
  Print Assumptions successful_assembly_has_exact_net_height.
  Print Assumptions successful_assembly_preserves_prefix.
  Print Assumptions checked_path_value_count_respects_limit.
  Print Assumptions every_transition_decodes_at_most_one_arena_node.
  Print Assumptions spine_decode_encode.
  Print Assumptions declared_binder_body_route_is_valid.

End TaggedReconstructionMachine.
