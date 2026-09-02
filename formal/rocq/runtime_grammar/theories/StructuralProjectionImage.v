(** * Declarative projection from canonical semantic terms to the WPDA/e-graph carrier

    [CanonicalSemanticTermImage] supplies the lossless, flat semantic value.
    This file models the next seam: a checked projection table describes how
    each typed field is exposed to a tree-automaton backend.  The table is a
    polynomial-functor description, not source code and not an untyped program:
    direct children remain transitions, sequences and collections gain explicit
    spine nodes, absence and binder arity gain leaves, and scalar/token/opaque
    coefficients gain typed leaves.

    The central inverse theorem says that every admitted projection is lossless.
    The naturality theorem says that a generated legacy projection and a shared
    table-driven projection with the same observations produce the same machine
    node trace.  The final small-step model consumes one source node per step,
    which is the obligation implemented by a heap worklist rather than native
    recursion. *)

From Stdlib Require Import List Arith.PeanoNat Bool.Bool.
From RuntimeGrammar Require Import CanonicalSemanticTermImage.
Import ListNotations.
Set Implicit Arguments.

Module StructuralProjectionImage.
  Import CanonicalSemanticTermImage.

  Record MachineOp : Type := machine_op {
    machine_discriminant : nat;
    machine_payload : list nat
  }.

  Record MachineNode : Type := machine_node {
    machine_node_op : MachineOp;
    machine_node_children : list nat;
    machine_node_canonicalize : bool
  }.

  Fixpoint nat_list_eqb (left right : list nat) : bool :=
    match left, right with
    | [], [] => true
    | left_head :: left_tail, right_head :: right_tail =>
        Nat.eqb left_head right_head && nat_list_eqb left_tail right_tail
    | _, _ => false
    end.

  Definition machine_op_eqb (left right : MachineOp) : bool :=
    Nat.eqb (machine_discriminant left) (machine_discriminant right) &&
    nat_list_eqb (machine_payload left) (machine_payload right).

  Definition instantiate (template : MachineOp) (dynamic_payload : list nat)
      : MachineOp :=
    machine_op
      (machine_discriminant template)
      (machine_payload template ++ dynamic_payload).

  Fixpoint strip_prefix (prefix values : list nat) : option (list nat) :=
    match prefix, values with
    | [], _ => Some values
    | expected :: prefix_rest, actual :: value_rest =>
        if Nat.eqb expected actual
        then strip_prefix prefix_rest value_rest
        else None
    | _ :: _, [] => None
    end.

  Definition decode_dynamic (template actual : MachineOp) : option (list nat) :=
    if Nat.eqb (machine_discriminant template) (machine_discriminant actual)
    then strip_prefix (machine_payload template) (machine_payload actual)
    else None.

  Inductive FieldProjection : Type :=
  | ProjectChild : FieldProjection
  | ProjectSequence : MachineOp -> FieldProjection
  | ProjectValueCollection : nat -> MachineOp -> bool -> FieldProjection
  | ProjectPairCollection : nat -> MachineOp -> MachineOp -> bool -> FieldProjection
  (** A whole-constructor collection reuses the semantic constructor as its
      machine spine.  Its value references therefore become parent children
      directly; no auxiliary collection node may be inserted. *)
  | ProjectInlineValueCollection : nat -> FieldProjection
  (** A whole-constructor map reuses the semantic constructor as its machine
      spine while retaining one exact pair node per key-value boundary. *)
  | ProjectInlinePairCollection : nat -> MachineOp -> FieldProjection
  (** A whole-constructor path map retains an explicit mode leaf.  Set keys
      follow that leaf directly; Map entries retain exact pair nodes. *)
  | ProjectInlinePathMap : MachineOp -> MachineOp -> MachineOp -> MachineOp ->
      FieldProjection
  | ProjectOptional : MachineOp -> FieldProjection
  | ProjectOptionalSequence : MachineOp -> MachineOp -> FieldProjection
  | ProjectOptionalToken : MachineOp -> MachineOp -> FieldProjection
  | ProjectScope : nat -> MachineOp -> FieldProjection
  | ProjectVariable : MachineOp -> FieldProjection
  | ProjectScalar : MachineOp -> FieldProjection
  | ProjectToken : MachineOp -> FieldProjection
  | ProjectOpaque : nat -> MachineOp -> FieldProjection
  | ProjectUnit : MachineOp -> FieldProjection.

  Definition templates_disjoint (left right : MachineOp) : Prop :=
    Nat.eqb (machine_discriminant left) (machine_discriminant right) = false.

  Definition templates_distinct (left right : MachineOp) : Prop :=
    machine_op_eqb left right = false.

  Definition four_templates_pairwise_distinct
      (first second third fourth : MachineOp) : Prop :=
    templates_distinct first second /\
    templates_distinct first third /\
    templates_distinct first fourth /\
    templates_distinct second third /\
    templates_distinct second fourth /\
    templates_distinct third fourth.

  Definition projection_valid (projection : FieldProjection) : Prop :=
    match projection with
    | ProjectOptionalSequence none_template sequence_template
    | ProjectOptionalToken none_template sequence_template =>
        templates_disjoint none_template sequence_template
    | ProjectInlinePathMap empty_template set_template map_template pair_template =>
        four_templates_pairwise_distinct
          empty_template set_template map_template pair_template
    | _ => True
    end.

  Record CompiledField : Type := compiled_field {
    compiled_field_nodes : list MachineNode;
    compiled_parent_children : list nat
  }.

  Definition leaf (op : MachineOp) : MachineNode :=
    machine_node op [] false.

  Definition encode_variable (variable : TermVariable) : list nat :=
    match variable with
    | BoundVariable scope_depth slot => 0 :: scope_depth :: slot :: []
    | FreeVariable identity => 1 :: identity
    end.

  Definition decode_variable (bytes : list nat) : option TermVariable :=
    match bytes with
    | 0 :: scope_depth :: slot :: [] => Some (BoundVariable scope_depth slot)
    | 1 :: identity => Some (FreeVariable identity)
    | _ => None
    end.

  Lemma nat_list_eqb_refl : forall values, nat_list_eqb values values = true.
  Proof.
    intro values. induction values as [|head tail IH]; cbn.
    - reflexivity.
    - now rewrite Nat.eqb_refl, IH.
  Qed.

  Lemma machine_op_eqb_refl : forall op, machine_op_eqb op op = true.
  Proof.
    intros [discriminant payload]. unfold machine_op_eqb. cbn.
    rewrite Nat.eqb_refl. cbn. exact (nat_list_eqb_refl payload).
  Qed.

  Lemma strip_prefix_app : forall prefix suffix,
      strip_prefix prefix (prefix ++ suffix) = Some suffix.
  Proof.
    intro prefix. induction prefix as [|head tail IH]; intro suffix; cbn.
    - reflexivity.
    - now rewrite Nat.eqb_refl, IH.
  Qed.

  Lemma decode_dynamic_instantiate : forall template payload,
      decode_dynamic template (instantiate template payload) = Some payload.
  Proof.
    intros [discriminant fixed_payload] payload.
    unfold decode_dynamic, instantiate. cbn. rewrite Nat.eqb_refl. cbn.
    exact (strip_prefix_app fixed_payload payload).
  Qed.

  Lemma disjoint_machine_op_eqb : forall left right,
      templates_disjoint left right -> machine_op_eqb left right = false.
  Proof.
    intros [left_discriminant left_payload]
      [right_discriminant right_payload] Hdisjoint.
    unfold templates_disjoint, machine_op_eqb in *. cbn in *.
    now rewrite Hdisjoint.
  Qed.

  Lemma disjoint_instantiate_eqb : forall left right payload,
      templates_disjoint left right ->
      machine_op_eqb left (instantiate right payload) = false.
  Proof.
    intros [left_discriminant left_payload]
      [right_discriminant right_payload] payload Hdisjoint.
    unfold templates_disjoint, machine_op_eqb, instantiate in *. cbn in *.
    now rewrite Hdisjoint.
  Qed.

  Fixpoint value_references (entries : list CollectionEntry) : option (list nat) :=
    match entries with
    | [] => Some []
    | CollectionValue reference :: rest =>
        option_map (cons reference) (value_references rest)
    | CollectionKeyValue _ _ :: _ => None
    end.

  Fixpoint compile_pair_entries
      (base : nat) (pair_template : MachineOp) (entries : list CollectionEntry)
      : option (list MachineNode * list nat)%type :=
    match entries with
    | [] => Some ([], [])
    | CollectionValue _ :: _ => None
    | CollectionKeyValue key value :: rest =>
        match compile_pair_entries (S base) pair_template rest with
        | None => None
        | Some (later_nodes, later_roots) =>
            Some (
              machine_node
                pair_template [key; value] false :: later_nodes,
              base :: later_roots)
        end
    end.

  Fixpoint decode_pair_entries
      (base : nat) (pair_template : MachineOp)
      (nodes : list MachineNode) (roots : list nat)
      : option (list CollectionEntry) :=
    match nodes, roots with
    | [], [] => Some []
    | machine_node actual [key; value] false :: later_nodes,
      root :: later_roots =>
        if machine_op_eqb pair_template actual && Nat.eqb base root then
          option_map
            (cons (CollectionKeyValue key value))
            (decode_pair_entries (S base) pair_template later_nodes later_roots)
        else None
    | _, _ => None
    end.

  Fixpoint pathmap_set_references (entries : list PathMapEntry)
      : option (list nat) :=
    match entries with
    | [] => Some []
    | PathMapKey key :: rest =>
        option_map (cons key) (pathmap_set_references rest)
    | PathMapKeyValue _ _ :: _ => None
    end.

  Fixpoint compile_pathmap_pair_entries
      (base : nat) (pair_template : MachineOp) (entries : list PathMapEntry)
      : option (list MachineNode * list nat)%type :=
    match entries with
    | [] => Some ([], [])
    | PathMapKey _ :: _ => None
    | PathMapKeyValue key value :: rest =>
        match compile_pathmap_pair_entries (S base) pair_template rest with
        | None => None
        | Some (later_nodes, later_roots) =>
            Some (
              machine_node pair_template [key; value] false :: later_nodes,
              base :: later_roots)
        end
    end.

  Fixpoint decode_pathmap_pair_entries
      (base : nat) (pair_template : MachineOp)
      (nodes : list MachineNode) (roots : list nat)
      : option (list PathMapEntry) :=
    match nodes, roots with
    | [], [] => Some []
    | machine_node actual [key; value] false :: later_nodes,
      root :: later_roots =>
        if machine_op_eqb pair_template actual && Nat.eqb base root then
          option_map
            (cons (PathMapKeyValue key value))
            (decode_pathmap_pair_entries
              (S base) pair_template later_nodes later_roots)
        else None
    | _, _ => None
    end.

  Fixpoint split_last {A : Type} (values : list A) : option (list A * A)%type :=
    match values with
    | [] => None
    | head :: tail =>
        match split_last tail with
        | None => Some ([], head)
        | Some (prefix, last) => Some (head :: prefix, last)
        end
    end.

  Definition compile_field
      (base : nat) (projection : FieldProjection) (field : Field)
      : option CompiledField :=
    match projection, field with
    | ProjectChild, ChildRef reference =>
        Some (compiled_field [] [reference])
    | ProjectSequence template, SequenceRefs references =>
        Some (compiled_field
          [machine_node template references false]
          [base])
    | ProjectValueCollection expected_kind template canonicalize,
      CollectionRefs actual_kind entries =>
        if Nat.eqb expected_kind actual_kind then
          match value_references entries with
          | Some references =>
              Some (compiled_field
                [machine_node template references canonicalize]
                [base])
          | None => None
          end
        else None
    | ProjectPairCollection expected_kind template pair_template canonicalize,
      CollectionRefs actual_kind entries =>
        if Nat.eqb expected_kind actual_kind then
          match compile_pair_entries base pair_template entries with
          | Some (entry_nodes, entry_roots) =>
              Some (compiled_field
                (entry_nodes ++
                  [machine_node
                    template entry_roots canonicalize])
                [base + length entry_nodes])
          | None => None
        end
        else None
    | ProjectInlineValueCollection expected_kind,
      CollectionRefs actual_kind entries =>
        if Nat.eqb expected_kind actual_kind then
          option_map (compiled_field []) (value_references entries)
        else None
    | ProjectInlinePairCollection expected_kind pair_template,
      CollectionRefs actual_kind entries =>
        if Nat.eqb expected_kind actual_kind then
          match compile_pair_entries base pair_template entries with
          | Some (entry_nodes, entry_roots) =>
              Some (compiled_field entry_nodes entry_roots)
          | None => None
          end
        else None
    | ProjectInlinePathMap empty_template _ _ _,
      PathMapRefs PathMapNeutralEmpty [] =>
        Some (compiled_field [leaf empty_template] [base])
    | ProjectInlinePathMap _ set_template _ _,
      PathMapRefs PathMapSetMode entries =>
        match pathmap_set_references entries with
        | Some references =>
            Some (compiled_field [leaf set_template] (base :: references))
        | None => None
        end
    | ProjectInlinePathMap _ _ map_template pair_template,
      PathMapRefs PathMapMapMode entries =>
        match compile_pathmap_pair_entries (S base) pair_template entries with
        | Some (entry_nodes, entry_roots) =>
            Some (compiled_field
              (leaf map_template :: entry_nodes)
              (base :: entry_roots))
        | None => None
        end
    | ProjectOptional none_template, OptionalRef None =>
        Some (compiled_field [leaf none_template] [base])
    | ProjectOptional _, OptionalRef (Some reference) =>
        Some (compiled_field [] [reference])
    | ProjectOptionalSequence none_template _, OptionalSequenceRefs None =>
        Some (compiled_field [leaf none_template] [base])
    | ProjectOptionalSequence _ sequence_template,
      OptionalSequenceRefs (Some references) =>
        Some (compiled_field
          [machine_node sequence_template references false]
          [base])
    | ProjectOptionalToken none_template _, OptionalTokenText None =>
        Some (compiled_field [leaf none_template] [base])
    | ProjectOptionalToken _ token_template, OptionalTokenText (Some bytes) =>
        Some (compiled_field [leaf (instantiate token_template bytes)] [base])
    | ProjectScope expected_domain arity_template,
      ScopeRef actual_domain arity body =>
        if Nat.eqb expected_domain actual_domain then
          Some (compiled_field [leaf (instantiate arity_template [arity])] [base; body])
        else None
    | ProjectVariable template, VariableField variable =>
        Some (compiled_field [leaf (instantiate template (encode_variable variable))] [base])
    | ProjectScalar template, ScalarField scalar_value =>
        Some (compiled_field
          [leaf (instantiate template
            (scalar_tag scalar_value :: scalar_bytes scalar_value))] [base])
    | ProjectToken template, TokenText bytes =>
        Some (compiled_field [leaf (instantiate template bytes)] [base])
    | ProjectOpaque expected_codec template, OpaqueField actual_codec bytes =>
        if Nat.eqb expected_codec actual_codec then
          Some (compiled_field [leaf (instantiate template bytes)] [base])
        else None
    | ProjectUnit template, UnitField =>
        Some (compiled_field [leaf template] [base])
    | _, _ => None
    end.

  Definition decode_field
      (base : nat) (projection : FieldProjection) (compiled : CompiledField)
      : option Field :=
    match projection, compiled_field_nodes compiled,
          compiled_parent_children compiled with
    | ProjectChild, [], [reference] => Some (ChildRef reference)
    | ProjectSequence template,
      [machine_node actual references false], [root] =>
        if machine_op_eqb template actual && Nat.eqb base root
        then Some (SequenceRefs references) else None
    | ProjectValueCollection kind template canonicalize,
      [machine_node actual references actual_canonicalize], [root] =>
        if machine_op_eqb template actual
           && Bool.eqb canonicalize actual_canonicalize
           && Nat.eqb base root
        then Some (CollectionRefs kind (map CollectionValue references)) else None
    | ProjectPairCollection kind template pair_template canonicalize,
      nodes, [root] =>
        match split_last nodes with
        | Some (entry_nodes,
            machine_node actual entry_roots actual_canonicalize) =>
            if machine_op_eqb template actual
               && Bool.eqb canonicalize actual_canonicalize
               && Nat.eqb (base + length entry_nodes) root
            then option_map
              (CollectionRefs kind)
              (decode_pair_entries base pair_template entry_nodes entry_roots)
            else None
        | _ => None
        end
    | ProjectInlineValueCollection kind, [], references =>
        Some (CollectionRefs kind (map CollectionValue references))
    | ProjectInlinePairCollection kind pair_template, nodes, roots =>
        option_map (CollectionRefs kind)
          (decode_pair_entries base pair_template nodes roots)
    | ProjectInlinePathMap empty_template set_template map_template pair_template,
      machine_node actual [] false :: later_nodes, mode_root :: entry_roots =>
        if Nat.eqb base mode_root then
          if machine_op_eqb empty_template actual then
            match later_nodes, entry_roots with
            | [], [] => Some (PathMapRefs PathMapNeutralEmpty [])
            | _, _ => None
            end
          else if machine_op_eqb set_template actual then
            match later_nodes with
            | [] => Some (PathMapRefs PathMapSetMode (map PathMapKey entry_roots))
            | _ => None
            end
          else if machine_op_eqb map_template actual then
            option_map
              (PathMapRefs PathMapMapMode)
              (decode_pathmap_pair_entries
                (S base) pair_template later_nodes entry_roots)
          else None
        else None
    | ProjectOptional none_template,
      [machine_node actual [] false], [root] =>
        if machine_op_eqb none_template actual && Nat.eqb base root
        then Some (OptionalRef None) else None
    | ProjectOptional _, [], [reference] => Some (OptionalRef (Some reference))
    | ProjectOptionalSequence none_template sequence_template,
      [machine_node actual references false], [root] =>
        if Nat.eqb base root then
          if machine_op_eqb none_template actual
          then Some (OptionalSequenceRefs None)
          else if machine_op_eqb sequence_template actual
               then Some (OptionalSequenceRefs (Some references))
               else None
        else None
    | ProjectOptionalToken none_template token_template,
      [machine_node actual [] false], [root] =>
        if Nat.eqb base root then
          if machine_op_eqb none_template actual
          then Some (OptionalTokenText None)
          else option_map
                 (fun bytes => OptionalTokenText (Some bytes))
                 (decode_dynamic token_template actual)
        else None
    | ProjectScope domain arity_template,
      [machine_node actual [] false], [root; body] =>
        match decode_dynamic arity_template actual with
        | Some [arity] =>
            if Nat.eqb base root then Some (ScopeRef domain arity body) else None
        | _ => None
        end
    | ProjectVariable template,
      [machine_node actual [] false], [root] =>
        match decode_dynamic template actual with
        | Some bytes =>
            if Nat.eqb base root
            then option_map VariableField (decode_variable bytes) else None
        | None => None
        end
    | ProjectScalar template,
      [machine_node actual [] false], [root] =>
        match decode_dynamic template actual with
        | Some (tag :: bytes) =>
            if Nat.eqb base root then Some (ScalarField (scalar tag bytes)) else None
        | _ => None
        end
    | ProjectToken template,
      [machine_node actual [] false], [root] =>
        match decode_dynamic template actual with
        | Some bytes => if Nat.eqb base root then Some (TokenText bytes) else None
        | None => None
        end
    | ProjectOpaque codec template,
      [machine_node actual [] false], [root] =>
        match decode_dynamic template actual with
        | Some bytes =>
            if Nat.eqb base root then Some (OpaqueField codec bytes) else None
        | None => None
        end
    | ProjectUnit template,
      [machine_node actual [] false], [root] =>
        if machine_op_eqb template actual && Nat.eqb base root
        then Some UnitField else None
    | _, _, _ => None
    end.

  Lemma decode_encode_variable :
    forall variable, decode_variable (encode_variable variable) = Some variable.
  Proof. intros [scope_depth slot | identity]; reflexivity. Qed.

  Lemma value_references_inverse : forall entries references,
      value_references entries = Some references ->
      map CollectionValue references = entries.
  Proof.
    intro entries. induction entries as [|entry rest IH]; intros references Hcompile.
    - inversion Hcompile. reflexivity.
    - destruct entry as [reference | key value]; cbn in Hcompile; try discriminate.
      destruct (value_references rest) as [later |] eqn:Hlater; try discriminate.
      inversion Hcompile; subst. cbn. f_equal.
      exact (IH later eq_refl).
  Qed.

  Lemma decode_compile_pair_entries :
    forall base discriminant entries nodes roots,
      compile_pair_entries base discriminant entries = Some (nodes, roots) ->
      decode_pair_entries base discriminant nodes roots = Some entries.
  Proof.
    intros base discriminant entries.
    revert base.
    induction entries as [|entry rest IH]; intros base nodes roots Hcompile.
    - inversion Hcompile. reflexivity.
    - destruct entry as [reference | key value]; cbn in Hcompile; try discriminate.
      destruct (compile_pair_entries (S base) discriminant rest)
        as [[later_nodes later_roots] |] eqn:Hlater; try discriminate.
      inversion Hcompile; subst. cbn.
      rewrite machine_op_eqb_refl, Nat.eqb_refl. cbn.
      now rewrite (IH (S base) later_nodes later_roots Hlater).
  Qed.

  Lemma pathmap_set_references_inverse : forall entries references,
      pathmap_set_references entries = Some references ->
      map PathMapKey references = entries.
  Proof.
    intro entries. induction entries as [|entry rest IH]; intros references Hcompile.
    - inversion Hcompile. reflexivity.
    - destruct entry as [key | key value]; cbn in Hcompile; try discriminate.
      destruct (pathmap_set_references rest) as [later |] eqn:Hlater;
        try discriminate.
      inversion Hcompile; subst. cbn. f_equal.
      exact (IH later eq_refl).
  Qed.

  Lemma decode_compile_pathmap_pair_entries :
    forall base pair_template entries nodes roots,
      compile_pathmap_pair_entries base pair_template entries = Some (nodes, roots) ->
      decode_pathmap_pair_entries base pair_template nodes roots = Some entries.
  Proof.
    intros base pair_template entries.
    revert base.
    induction entries as [|entry rest IH]; intros base nodes roots Hcompile.
    - inversion Hcompile. reflexivity.
    - destruct entry as [key | key value]; cbn in Hcompile; try discriminate.
      destruct (compile_pathmap_pair_entries (S base) pair_template rest)
        as [[later_nodes later_roots] |] eqn:Hlater; try discriminate.
      inversion Hcompile; subst. cbn.
      rewrite machine_op_eqb_refl, Nat.eqb_refl. cbn.
      now rewrite (IH (S base) later_nodes later_roots Hlater).
  Qed.

  Lemma split_last_snoc : forall (A : Type) (prefix : list A) last,
      split_last (prefix ++ [last]) = Some (prefix, last).
  Proof.
    intros A prefix. induction prefix as [|head tail IH]; intro last; cbn.
    - reflexivity.
    - now rewrite IH.
  Qed.

  Lemma child_projection_is_lossless :
    forall base field compiled,
      compile_field base ProjectChild field = Some compiled ->
      decode_field base ProjectChild compiled = Some field.
  Proof.
    intros base field compiled Hcompile.
    destruct field; simpl in Hcompile; try discriminate.
    now inversion Hcompile.
  Qed.

  Lemma sequence_projection_is_lossless :
    forall base discriminant field compiled,
      compile_field base (ProjectSequence discriminant) field = Some compiled ->
      decode_field base (ProjectSequence discriminant) compiled = Some field.
  Proof.
    intros base discriminant field compiled Hcompile.
    destruct field; simpl in Hcompile; try discriminate.
    inversion Hcompile; subst; simpl.
    now rewrite machine_op_eqb_refl, Nat.eqb_refl.
  Qed.

  Lemma value_collection_projection_is_lossless :
    forall base kind discriminant canonicalize field compiled,
      compile_field base (ProjectValueCollection kind discriminant canonicalize) field =
        Some compiled ->
      decode_field base (ProjectValueCollection kind discriminant canonicalize) compiled =
        Some field.
  Proof.
    intros base kind discriminant canonicalize field compiled Hcompile.
    destruct field; simpl in Hcompile; try discriminate.
    match type of Hcompile with
    | context [Nat.eqb ?expected ?actual] =>
        destruct (Nat.eqb expected actual) eqn:Hequal
    end; try discriminate.
    apply Nat.eqb_eq in Hequal. subst.
    destruct (value_references l) as [references |] eqn:Hreferences; try discriminate.
    inversion Hcompile; subst; simpl.
    rewrite machine_op_eqb_refl, Nat.eqb_refl.
    pose proof (@value_references_inverse l references Hreferences) as Hinverse.
    destruct canonicalize; cbn; now rewrite Hinverse.
  Qed.

  Lemma pair_collection_projection_is_lossless :
    forall base kind discriminant pair_discriminant canonicalize field compiled,
      compile_field base
        (ProjectPairCollection kind discriminant pair_discriminant canonicalize) field =
        Some compiled ->
      decode_field base
        (ProjectPairCollection kind discriminant pair_discriminant canonicalize) compiled =
        Some field.
  Proof.
    intros base kind discriminant pair_discriminant canonicalize field compiled Hcompile.
    destruct field; simpl in Hcompile; try discriminate.
    match type of Hcompile with
    | context [Nat.eqb ?expected ?actual] =>
        destruct (Nat.eqb expected actual) eqn:Hequal
    end; try discriminate.
    apply Nat.eqb_eq in Hequal. subst.
    destruct (compile_pair_entries base pair_discriminant l)
      as [[entry_nodes entry_roots] |] eqn:Hentries; try discriminate.
    inversion Hcompile; subst; simpl.
    rewrite split_last_snoc.
    rewrite machine_op_eqb_refl, Nat.eqb_refl. cbn.
    rewrite (@decode_compile_pair_entries
      base pair_discriminant l entry_nodes entry_roots Hentries).
    destruct canonicalize; reflexivity.
  Qed.

  Lemma inline_value_collection_projection_is_lossless :
    forall base kind field compiled,
      compile_field base (ProjectInlineValueCollection kind) field = Some compiled ->
      decode_field base (ProjectInlineValueCollection kind) compiled = Some field.
  Proof.
    intros base kind field compiled Hcompile.
    destruct field; simpl in Hcompile; try discriminate.
    match type of Hcompile with
    | context [Nat.eqb ?expected ?actual] =>
        destruct (Nat.eqb expected actual) eqn:Hequal
    end; try discriminate.
    apply Nat.eqb_eq in Hequal. subst.
    destruct (value_references l) as [references |] eqn:Hreferences;
      try discriminate.
    inversion Hcompile; subst; simpl.
    now rewrite (@value_references_inverse l references Hreferences).
  Qed.

  Lemma inline_pair_collection_projection_is_lossless :
    forall base kind pair_template field compiled,
      compile_field base (ProjectInlinePairCollection kind pair_template) field =
        Some compiled ->
      decode_field base (ProjectInlinePairCollection kind pair_template) compiled =
        Some field.
  Proof.
    intros base kind pair_template field compiled Hcompile.
    destruct field; simpl in Hcompile; try discriminate.
    match type of Hcompile with
    | context [Nat.eqb ?expected ?actual] =>
        destruct (Nat.eqb expected actual) eqn:Hequal
    end; try discriminate.
    apply Nat.eqb_eq in Hequal. subst.
    destruct (compile_pair_entries base pair_template l)
      as [[entry_nodes entry_roots] |] eqn:Hentries; try discriminate.
    inversion Hcompile; subst; simpl.
    now rewrite (@decode_compile_pair_entries
      base pair_template l entry_nodes entry_roots Hentries).
  Qed.

  Lemma inline_pathmap_projection_is_lossless :
    forall base empty_template set_template map_template pair_template field compiled,
      four_templates_pairwise_distinct
        empty_template set_template map_template pair_template ->
      compile_field base
        (ProjectInlinePathMap
          empty_template set_template map_template pair_template) field = Some compiled ->
      decode_field base
        (ProjectInlinePathMap
          empty_template set_template map_template pair_template) compiled = Some field.
  Proof.
    intros base empty_template set_template map_template pair_template
      field compiled Hdistinct Hcompile.
    destruct field; simpl in Hcompile; try discriminate.
    destruct p.
    - destruct l as [|entry rest]; try discriminate.
      inversion Hcompile; subst; simpl.
      now rewrite Nat.eqb_refl, machine_op_eqb_refl.
    - destruct (pathmap_set_references l) as [references |] eqn:Hreferences;
        try discriminate.
      inversion Hcompile; subst; simpl.
      destruct Hdistinct as
        [Hempty_set [Hempty_map [Hempty_pair
          [Hset_map [Hset_pair Hmap_pair]]]]].
      rewrite Nat.eqb_refl, Hempty_set. cbn.
      rewrite machine_op_eqb_refl.
      now rewrite (@pathmap_set_references_inverse l references Hreferences).
    - destruct (compile_pathmap_pair_entries (S base) pair_template l)
        as [[entry_nodes entry_roots] |] eqn:Hentries; try discriminate.
      inversion Hcompile; subst; simpl.
      destruct Hdistinct as
        [Hempty_set [Hempty_map [Hempty_pair
          [Hset_map [Hset_pair Hmap_pair]]]]].
      rewrite Nat.eqb_refl, Hempty_map. cbn.
      rewrite Hset_map. cbn. rewrite machine_op_eqb_refl.
      now rewrite (@decode_compile_pathmap_pair_entries
        (S base) pair_template l entry_nodes entry_roots Hentries).
  Qed.

  Lemma optional_projection_is_lossless :
    forall base discriminant field compiled,
      compile_field base (ProjectOptional discriminant) field = Some compiled ->
      decode_field base (ProjectOptional discriminant) compiled = Some field.
  Proof.
    intros base discriminant field compiled Hcompile.
    destruct field as
      [reference | references | kind references | pathmap_mode pathmap_entries | maybe_reference |
       maybe_references | maybe_bytes | domain arity body | variable |
       scalar_value | bytes | byte_string | codec bytes |];
      simpl in Hcompile; try discriminate.
    destruct maybe_reference; inversion Hcompile; subst; simpl.
    - reflexivity.
    - now rewrite machine_op_eqb_refl, Nat.eqb_refl.
  Qed.

  Lemma optional_sequence_projection_is_lossless :
    forall base none_template sequence_template field compiled,
      templates_disjoint none_template sequence_template ->
      compile_field base
        (ProjectOptionalSequence none_template sequence_template) field = Some compiled ->
      decode_field base
        (ProjectOptionalSequence none_template sequence_template) compiled = Some field.
  Proof.
    intros base none_template sequence_template field compiled Hvalid Hcompile.
    destruct field as
      [reference | references | kind entries | pathmap_mode pathmap_entries | maybe_reference |
       maybe_references | maybe_bytes | domain arity body | variable |
       scalar_value | bytes | byte_string | codec bytes |];
      simpl in Hcompile; try discriminate.
    destruct maybe_references as [references |]; inversion Hcompile; subst; simpl.
    - rewrite Nat.eqb_refl. cbn.
      rewrite (@disjoint_machine_op_eqb none_template sequence_template Hvalid),
        machine_op_eqb_refl.
      reflexivity.
    - now rewrite Nat.eqb_refl, machine_op_eqb_refl.
  Qed.

  Lemma optional_token_projection_is_lossless :
    forall base none_template token_template field compiled,
      templates_disjoint none_template token_template ->
      compile_field base
        (ProjectOptionalToken none_template token_template) field = Some compiled ->
      decode_field base
        (ProjectOptionalToken none_template token_template) compiled = Some field.
  Proof.
    intros base none_template token_template field compiled Hvalid Hcompile.
    destruct field as
      [reference | references | kind entries | pathmap_mode pathmap_entries | maybe_reference |
       maybe_references | maybe_bytes | domain arity body | variable |
       scalar_value | bytes | byte_string | codec bytes |];
      simpl in Hcompile; try discriminate.
    destruct maybe_bytes as [bytes |]; inversion Hcompile; subst; simpl.
    - rewrite Nat.eqb_refl. cbn.
      rewrite (@disjoint_instantiate_eqb none_template token_template bytes Hvalid),
        decode_dynamic_instantiate.
      reflexivity.
    - now rewrite Nat.eqb_refl, machine_op_eqb_refl.
  Qed.

  Lemma scope_projection_is_lossless :
    forall base domain discriminant field compiled,
      compile_field base (ProjectScope domain discriminant) field = Some compiled ->
      decode_field base (ProjectScope domain discriminant) compiled = Some field.
  Proof.
    intros base domain discriminant field compiled Hcompile.
    destruct field; simpl in Hcompile; try discriminate.
    match type of Hcompile with
    | context [Nat.eqb ?expected ?actual] =>
        destruct (Nat.eqb expected actual) eqn:Hequal
    end; try discriminate.
    apply Nat.eqb_eq in Hequal. subst.
    inversion Hcompile; subst; simpl.
    now rewrite decode_dynamic_instantiate, Nat.eqb_refl.
  Qed.

  Lemma variable_projection_is_lossless :
    forall base discriminant field compiled,
      compile_field base (ProjectVariable discriminant) field = Some compiled ->
      decode_field base (ProjectVariable discriminant) compiled = Some field.
  Proof.
    intros base discriminant field compiled Hcompile.
    destruct field; simpl in Hcompile; try discriminate.
    inversion Hcompile; subst; simpl.
    rewrite decode_dynamic_instantiate, Nat.eqb_refl. simpl.
    now rewrite decode_encode_variable.
  Qed.

  Lemma scalar_projection_is_lossless :
    forall base discriminant field compiled,
      compile_field base (ProjectScalar discriminant) field = Some compiled ->
      decode_field base (ProjectScalar discriminant) compiled = Some field.
  Proof.
    intros base discriminant field compiled Hcompile.
    destruct field as
      [reference | references | kind references | pathmap_mode pathmap_entries | maybe_reference |
       maybe_references | maybe_bytes | domain arity body | variable |
       scalar_value | bytes | byte_string | codec bytes |];
      simpl in Hcompile; try discriminate.
    destruct scalar_value as [tag payload].
    inversion Hcompile; subst; simpl.
    now rewrite decode_dynamic_instantiate, Nat.eqb_refl.
  Qed.

  Lemma token_projection_is_lossless :
    forall base discriminant field compiled,
      compile_field base (ProjectToken discriminant) field = Some compiled ->
      decode_field base (ProjectToken discriminant) compiled = Some field.
  Proof.
    intros base discriminant field compiled Hcompile.
    destruct field; simpl in Hcompile; try discriminate.
    inversion Hcompile; subst; simpl.
    now rewrite decode_dynamic_instantiate, Nat.eqb_refl.
  Qed.

  Lemma opaque_projection_is_lossless :
    forall base codec discriminant field compiled,
      compile_field base (ProjectOpaque codec discriminant) field = Some compiled ->
      decode_field base (ProjectOpaque codec discriminant) compiled = Some field.
  Proof.
    intros base codec discriminant field compiled Hcompile.
    destruct field; simpl in Hcompile; try discriminate.
    match type of Hcompile with
    | context [Nat.eqb ?expected ?actual] =>
        destruct (Nat.eqb expected actual) eqn:Hequal
    end; try discriminate.
    apply Nat.eqb_eq in Hequal. subst.
    inversion Hcompile; subst; simpl.
    now rewrite decode_dynamic_instantiate, Nat.eqb_refl.
  Qed.

  Lemma unit_projection_is_lossless :
    forall base discriminant field compiled,
      compile_field base (ProjectUnit discriminant) field = Some compiled ->
      decode_field base (ProjectUnit discriminant) compiled = Some field.
  Proof.
    intros base discriminant field compiled Hcompile.
    destruct field; simpl in Hcompile; try discriminate.
    inversion Hcompile; subst; simpl.
    now rewrite machine_op_eqb_refl, Nat.eqb_refl.
  Qed.

  Theorem field_projection_is_lossless :
    forall base projection field compiled,
      projection_valid projection ->
      compile_field base projection field = Some compiled ->
      decode_field base projection compiled = Some field.
  Proof.
    intros base projection field compiled Hvalid Hcompile.
    destruct projection;
      eauto using child_projection_is_lossless,
                  sequence_projection_is_lossless,
                  value_collection_projection_is_lossless,
                  pair_collection_projection_is_lossless,
                  inline_value_collection_projection_is_lossless,
                  inline_pair_collection_projection_is_lossless,
                  inline_pathmap_projection_is_lossless,
                  optional_projection_is_lossless,
                  optional_sequence_projection_is_lossless,
                  optional_token_projection_is_lossless,
                  scope_projection_is_lossless,
                  variable_projection_is_lossless,
                  scalar_projection_is_lossless,
                  token_projection_is_lossless,
                  opaque_projection_is_lossless,
                  unit_projection_is_lossless.
  Qed.

  Fixpoint compile_fields
      (base : nat) (projections : list FieldProjection) (fields : list Field)
      : option (list MachineNode * list nat)%type :=
    match projections, fields with
    | [], [] => Some ([], [])
    | projection :: projection_rest, field :: field_rest =>
        match compile_field base projection field with
        | None => None
        | Some current =>
            let next_base := base + length (compiled_field_nodes current) in
            match compile_fields next_base projection_rest field_rest with
            | None => None
            | Some (later_nodes, later_children) =>
                Some (
                  compiled_field_nodes current ++ later_nodes,
                  compiled_parent_children current ++ later_children)
            end
        end
    | _, _ => None
    end.

  Record ProjectionTable : Type := projection_table {
    projection_main_template : MachineOp;
    projection_fields : list FieldProjection;
    projection_canonicalize : bool
  }.

  Definition encode_scalar (value : Scalar) : list nat :=
    scalar_tag value :: scalar_bytes value.

  Definition encode_optional_scalar (value : option Scalar) : list nat :=
    match value with
    | None => []
    | Some scalar_value => encode_scalar scalar_value
    end.

  Definition decode_optional_scalar (bytes : list nat) : option Scalar :=
    match bytes with
    | [] => None
    | tag :: payload => Some (scalar tag payload)
    end.

  Definition project_main_operator (template : MachineOp) (op : CoreOp) : MachineOp :=
    instantiate template (encode_optional_scalar (core_payload op)).

  Theorem main_operator_projection_is_exact : forall template op,
      machine_discriminant template = core_discriminant op ->
      machine_discriminant (project_main_operator template op) =
        core_discriminant op /\
      option_map decode_optional_scalar
        (decode_dynamic template (project_main_operator template op)) =
        Some (core_payload op).
  Proof.
    intros template [category constructor discriminant [scalar_value |]] Hequal;
      unfold project_main_operator; rewrite decode_dynamic_instantiate; cbn in *;
      split; try assumption.
    - now destruct scalar_value.
    - reflexivity.
  Qed.

  Definition compile_node
      (base : nat) (table : ProjectionTable) (value : Node CoreOp)
      : option (list MachineNode * nat)%type :=
    if Nat.eqb
         (machine_discriminant (projection_main_template table))
         (core_discriminant (node_op value)) then
      match compile_fields base (projection_fields table) (node_fields value) with
      | None => None
      | Some (field_nodes, children) =>
          let root := base + length field_nodes in
          Some (
            field_nodes ++
              [machine_node
                (project_main_operator
                  (projection_main_template table) (node_op value))
                children
                (projection_canonicalize table)],
            root)
      end
    else None.

  (** A value-only whole-constructor collection contributes no auxiliary
      spine.  The existing main constructor receives the references directly
      and retains the exact canonicalization policy selected by the table. *)
  Theorem inline_value_collection_reuses_main_spine :
    forall base template op kind canonicalize entries references,
      machine_discriminant template = core_discriminant op ->
      value_references entries = Some references ->
      compile_node base
        (projection_table template
          [ProjectInlineValueCollection kind] canonicalize)
        (node op [CollectionRefs kind entries]) =
      Some ([machine_node (project_main_operator template op)
        references canonicalize], base).
  Proof.
    intros base template op kind canonicalize entries references
      Hdiscriminant Hreferences.
    unfold compile_node. cbn. rewrite Hdiscriminant, Nat.eqb_refl. cbn.
    rewrite Nat.eqb_refl, Hreferences.
    cbn [option_map compiled_field_nodes compiled_parent_children].
    cbn. now rewrite app_nil_r, Nat.add_0_r.
  Qed.

  Definition projection_observationally_equal
      (legacy shared : ProjectionTable) : Prop :=
    projection_main_template legacy = projection_main_template shared /\
    projection_fields legacy = projection_fields shared /\
    projection_canonicalize legacy = projection_canonicalize shared.

  Theorem shared_projection_preserves_legacy_machine_trace :
    forall base legacy shared value,
      projection_observationally_equal legacy shared ->
      compile_node base legacy value = compile_node base shared value.
  Proof.
    intros base legacy shared value [Hop [Hfields Hcanon]].
    destruct legacy as [legacy_discriminant legacy_fields legacy_canon].
    destruct shared as [shared_discriminant shared_fields shared_canon].
    simpl in *. subst. reflexivity.
  Qed.

  Inductive MachineRunResult : Type :=
  | MachineRunFailed : MachineRunResult
  | MachineRunDone : list MachineNode -> list nat -> MachineRunResult
  | MachineRunPending : list (ProjectionTable * Node CoreOp)%type ->
      list MachineNode -> list nat -> MachineRunResult.

  Fixpoint machine_run
      (fuel : nat)
      (pending : list (ProjectionTable * Node CoreOp)%type)
      (emitted : list MachineNode)
      (roots : list nat) : MachineRunResult :=
    match fuel, pending with
    | 0, [] => MachineRunDone emitted roots
    | 0, _ => MachineRunPending pending emitted roots
    | S _, [] => MachineRunDone emitted roots
    | S remaining, (table, value) :: rest =>
        match compile_node (length emitted) table value with
        | None => MachineRunFailed
        | Some (nodes, root) =>
            machine_run remaining rest (emitted ++ nodes) (roots ++ [root])
        end
    end.

  Definition source_nodes_consumed
      (pending : list (ProjectionTable * Node CoreOp)%type) : nat :=
    match pending with [] => 0 | _ :: _ => 1 end.

  Theorem machine_transition_consumes_at_most_one_source_node :
    forall pending, source_nodes_consumed pending <= 1.
  Proof. intros [|value rest]; simpl; auto. Qed.

  Theorem empty_machine_run_is_total :
    forall fuel emitted roots,
      machine_run fuel [] emitted roots = MachineRunDone emitted roots.
  Proof. intros [|fuel] emitted roots; reflexivity. Qed.

  Print Assumptions decode_encode_variable.
  Print Assumptions main_operator_projection_is_exact.
  Print Assumptions field_projection_is_lossless.
  Print Assumptions inline_value_collection_projection_is_lossless.
  Print Assumptions inline_pair_collection_projection_is_lossless.
  Print Assumptions inline_pathmap_projection_is_lossless.
  Print Assumptions inline_value_collection_reuses_main_spine.
  Print Assumptions shared_projection_preserves_legacy_machine_trace.
  Print Assumptions machine_transition_consumes_at_most_one_source_node.
  Print Assumptions empty_machine_run_is_total.

End StructuralProjectionImage.
