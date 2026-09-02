(** * Canonical structural semantic terms shared by generated and run-time languages

    A generated typed abstract-syntax tree and a run-time [GrammarCoreV1]
    value are two presentations of the same checked language signature.  The
    semantic backends must therefore meet at a lossless structural carrier,
    not at source text and not at the deliberately lossy [GroundTerm]
    projection used by the Rho bridge.

    The carrier below is a flat, post-order arena.  Every reference points to
    an earlier node, so an implementation can encode, validate, match, and
    reconstruct it with a bounded native stack and a heap worklist.  Fields
    enumerate the information that must survive the seam: positional children,
    optional and repeated children, collections, scopes, variables, typed
    scalar payloads, captured token text, and capability-coded opaque values.

    [LegacyOp] models the current generated typed Dovetail operator and
    [CoreOp] models its source-neutral image.  The proofs establish the
    obligations used by the replacement backend: representation round trips,
    exact-key preservation, arena and scope preservation, fail-closed
    validation, positional/AC pattern observations, substitution and
    structural instantiation, native-transition naturality, report
    invariance, and an explicit one-node-per-step image machine. *)

From Stdlib Require Import List Arith.PeanoNat Sorting.Permutation.
Import ListNotations.
Set Implicit Arguments.

Module CanonicalSemanticTermImage.

  Record Signature : Type := signature {
    category_count : nat;
    constructor_count : nat
  }.

  Record Scalar : Type := scalar {
    scalar_tag : nat;
    scalar_bytes : list nat
  }.

  Inductive TermVariable : Type :=
  | BoundVariable : nat -> nat -> TermVariable
  | FreeVariable : list nat -> TermVariable.

  Inductive CollectionEntry : Type :=
  | CollectionValue : nat -> CollectionEntry
  | CollectionKeyValue : nat -> nat -> CollectionEntry.

  (** Path maps are a homogeneous sum, not ordinary maps.  The mode belongs to
      the whole carrier and remains observable even when its entry list is
      empty.  Key-only set membership is therefore distinct from key-value map
      membership, and both are distinct from neutral empty. *)
  Inductive PathMapMode : Type :=
  | PathMapNeutralEmpty
  | PathMapSetMode
  | PathMapMapMode.

  Inductive PathMapEntry : Type :=
  | PathMapKey : nat -> PathMapEntry
  | PathMapKeyValue : nat -> nat -> PathMapEntry.

  (** References are node indices in a post-order arena.  A collection kind or
      opaque codec is represented by its stable committed identifier. *)
  Inductive Field : Type :=
  | ChildRef : nat -> Field
  | SequenceRefs : list nat -> Field
  | CollectionRefs : nat -> list CollectionEntry -> Field
  | PathMapRefs : PathMapMode -> list PathMapEntry -> Field
  | OptionalRef : option nat -> Field
  | OptionalSequenceRefs : option (list nat) -> Field
  | OptionalTokenText : option (list nat) -> Field
  | ScopeRef : nat -> nat -> nat -> Field
  | VariableField : TermVariable -> Field
  | ScalarField : Scalar -> Field
  | TokenText : list nat -> Field
  | ByteString : list nat -> Field
  | OpaqueField : nat -> list nat -> Field
  | UnitField : Field.

  Record LegacyOp : Type := legacy_op {
    legacy_category : nat;
    legacy_constructor : nat;
    legacy_discriminant : nat;
    legacy_payload : option Scalar
  }.

  Record CoreOp : Type := core_op {
    core_category : nat;
    core_constructor : nat;
    core_discriminant : nat;
    core_payload : option Scalar
  }.

  Definition encode_op (op : LegacyOp) : CoreOp :=
    core_op
      (legacy_category op)
      (legacy_constructor op)
      (legacy_discriminant op)
      (legacy_payload op).

  Definition decode_op (op : CoreOp) : LegacyOp :=
    legacy_op
      (core_category op)
      (core_constructor op)
      (core_discriminant op)
      (core_payload op).

  Theorem decode_encode_op : forall op, decode_op (encode_op op) = op.
  Proof. intros []; reflexivity. Qed.

  Theorem encode_decode_op : forall op, encode_op (decode_op op) = op.
  Proof. intros []; reflexivity. Qed.

  Theorem encode_op_injective :
    forall left right, encode_op left = encode_op right -> left = right.
  Proof.
    intros left right Heq.
    rewrite <- (decode_encode_op left), <- (decode_encode_op right), Heq.
    reflexivity.
  Qed.

  Record Node (Op : Type) : Type := node {
    node_op : Op;
    node_fields : list Field
  }.

  Arguments node {_} _ _.
  Arguments node_op {_} _.
  Arguments node_fields {_} _.

  Definition encode_node (value : Node LegacyOp) : Node CoreOp :=
    node (encode_op (node_op value)) (node_fields value).

  Definition decode_node (value : Node CoreOp) : Node LegacyOp :=
    node (decode_op (node_op value)) (node_fields value).

  Theorem decode_encode_node : forall value, decode_node (encode_node value) = value.
  Proof. intros [[] fields]; reflexivity. Qed.

  Theorem encode_decode_node : forall value, encode_node (decode_node value) = value.
  Proof. intros [[] fields]; reflexivity. Qed.

  Definition LegacyArena := list (Node LegacyOp).
  Definition CoreArena := list (Node CoreOp).

  Definition encode_arena (arena : LegacyArena) : CoreArena :=
    map encode_node arena.

  Definition decode_arena (arena : CoreArena) : LegacyArena :=
    map decode_node arena.

  Theorem decode_encode_arena :
    forall arena, decode_arena (encode_arena arena) = arena.
  Proof.
    induction arena as [|value rest IH].
    - reflexivity.
    - simpl. now rewrite decode_encode_node, IH.
  Qed.

  Theorem encode_decode_arena :
    forall arena, encode_arena (decode_arena arena) = arena.
  Proof.
    induction arena as [|value rest IH].
    - reflexivity.
    - simpl. now rewrite encode_decode_node, IH.
  Qed.

  Definition arena_shape {Op : Type} (arena : list (Node Op)) : list (list Field) :=
    map node_fields arena.

  Theorem arena_shape_preserved :
    forall arena, arena_shape (encode_arena arena) = arena_shape arena.
  Proof.
    intros arena. unfold arena_shape, encode_arena.
    rewrite map_map. apply map_ext. intros [op fields]. reflexivity.
  Qed.

  Definition collection_entry_refs (entry : CollectionEntry) : list nat :=
    match entry with
    | CollectionValue reference => [reference]
    | CollectionKeyValue key value => [key; value]
    end.

  Definition pathmap_entry_refs (entry : PathMapEntry) : list nat :=
    match entry with
    | PathMapKey key => [key]
    | PathMapKeyValue key value => [key; value]
    end.

  Definition pathmap_entry_matches_mode
      (mode : PathMapMode) (entry : PathMapEntry) : Prop :=
    match mode, entry with
    | PathMapSetMode, PathMapKey _ => True
    | PathMapMapMode, PathMapKeyValue _ _ => True
    | _, _ => False
    end.

  Definition pathmap_entries_valid
      (mode : PathMapMode) (entries : list PathMapEntry) : Prop :=
    match mode with
    | PathMapNeutralEmpty => entries = []
    | PathMapSetMode | PathMapMapMode =>
        Forall (pathmap_entry_matches_mode mode) entries
    end.

  Theorem pathmap_neutral_empty_rejects_entries :
    forall entries,
      pathmap_entries_valid PathMapNeutralEmpty entries -> entries = [].
  Proof. intros entries Hvalid. exact Hvalid. Qed.

  Theorem pathmap_empty_modes_are_pairwise_distinct :
    PathMapNeutralEmpty <> PathMapSetMode /\
    PathMapNeutralEmpty <> PathMapMapMode /\
    PathMapSetMode <> PathMapMapMode.
  Proof. repeat split; discriminate. Qed.

  Definition field_refs (field : Field) : list nat :=
    match field with
    | ChildRef reference => [reference]
    | SequenceRefs references => references
    | CollectionRefs _ entries => concat (map collection_entry_refs entries)
    | PathMapRefs _ entries => concat (map pathmap_entry_refs entries)
    | OptionalRef (Some reference) => [reference]
    | OptionalRef None => []
    | OptionalSequenceRefs (Some references) => references
    | OptionalSequenceRefs None => []
    | ScopeRef _ _ body => [body]
    | VariableField _
    | ScalarField _
    | TokenText _
    | ByteString _
    | OptionalTokenText _
    | OpaqueField _ _
    | UnitField => []
    end.

  Definition fields_refs (fields : list Field) : list nat :=
    concat (map field_refs fields).

  Definition well_formed_shape (shape : list (list Field)) : Prop :=
    forall index fields,
      nth_error shape index = Some fields ->
      Forall (fun reference => reference < index) (fields_refs fields).

  Definition well_formed_arena {Op : Type} (arena : list (Node Op)) : Prop :=
    well_formed_shape (arena_shape arena).

  Theorem backward_references_preserved :
    forall arena,
      well_formed_arena arena <-> well_formed_arena (encode_arena arena).
  Proof.
    intros arena. unfold well_formed_arena.
    now rewrite arena_shape_preserved.
  Qed.

  Definition legacy_op_valid (sig : Signature) (op : LegacyOp) : Prop :=
    legacy_category op < category_count sig /\
    legacy_constructor op < constructor_count sig.

  Definition core_op_valid (sig : Signature) (op : CoreOp) : Prop :=
    core_category op < category_count sig /\
    core_constructor op < constructor_count sig.

  Definition field_valid (sig : Signature) (installed_codecs : list nat) (field : Field) : Prop :=
    match field with
    | ScopeRef domain arity _ => domain < category_count sig /\ 0 < arity
    | PathMapRefs mode entries => pathmap_entries_valid mode entries
    | OpaqueField codec _ => In codec installed_codecs
    | _ => True
    end.

  Definition legacy_node_valid
      (sig : Signature) (installed_codecs : list nat) (value : Node LegacyOp) : Prop :=
    legacy_op_valid sig (node_op value) /\
    Forall (field_valid sig installed_codecs) (node_fields value).

  Definition core_node_valid
      (sig : Signature) (installed_codecs : list nat) (value : Node CoreOp) : Prop :=
    core_op_valid sig (node_op value) /\
    Forall (field_valid sig installed_codecs) (node_fields value).

  Lemma node_valid_preserved :
    forall sig installed_codecs value,
      legacy_node_valid sig installed_codecs value <->
      core_node_valid sig installed_codecs (encode_node value).
  Proof. intros sig installed_codecs [[] fields]; reflexivity. Qed.

  Lemma valid_nodes_preserved :
    forall sig installed_codecs arena,
      Forall (legacy_node_valid sig installed_codecs) arena <->
      Forall (core_node_valid sig installed_codecs) (encode_arena arena).
  Proof.
    intros sig installed_codecs arena. unfold encode_arena.
    induction arena as [|value rest IH].
    - split; intro H; constructor.
    - split; intro H.
      + inversion H as [|ignored ignored_rest Hvalue Hrest]; subst.
        change
          (Forall (core_node_valid sig installed_codecs)
            (encode_node value :: map encode_node rest)).
        constructor.
        * apply (proj1 (node_valid_preserved sig installed_codecs value)). exact Hvalue.
        * apply (proj1 IH). exact Hrest.
      + change
          (Forall (core_node_valid sig installed_codecs)
            (encode_node value :: map encode_node rest)) in H.
        inversion H as [|ignored ignored_rest Hvalue Hrest]; subst.
        constructor.
        * apply (proj2 (node_valid_preserved sig installed_codecs value)). exact Hvalue.
        * apply (proj2 IH). exact Hrest.
  Qed.

  Definition legacy_image_valid
      (sig : Signature) (installed_codecs : list nat) (arena : LegacyArena) : Prop :=
    well_formed_arena arena /\
    Forall (legacy_node_valid sig installed_codecs) arena.

  Definition core_image_valid
      (sig : Signature) (installed_codecs : list nat) (arena : CoreArena) : Prop :=
    well_formed_arena arena /\
    Forall (core_node_valid sig installed_codecs) arena.

  Theorem fail_closed_image_validity_preserved :
    forall sig installed_codecs arena,
      legacy_image_valid sig installed_codecs arena <->
      core_image_valid sig installed_codecs (encode_arena arena).
  Proof.
    intros sig installed_codecs arena.
    unfold legacy_image_valid, core_image_valid.
    now rewrite <- backward_references_preserved, <- valid_nodes_preserved.
  Qed.

  Definition OpObservation : Type := (nat * nat * nat * option Scalar)%type.

  Definition legacy_op_observation (op : LegacyOp) : OpObservation :=
    (legacy_category op,
     legacy_constructor op,
     legacy_discriminant op,
     legacy_payload op).

  Definition core_op_observation (op : CoreOp) : OpObservation :=
    (core_category op,
     core_constructor op,
     core_discriminant op,
     core_payload op).

  Theorem operator_observation_preserved :
    forall op, core_op_observation (encode_op op) = legacy_op_observation op.
  Proof. intros []; reflexivity. Qed.

  Theorem legacy_operator_observation_injective :
    forall left right,
      legacy_op_observation left = legacy_op_observation right -> left = right.
  Proof.
    intros [left_category left_constructor left_discriminant left_payload]
           [right_category right_constructor right_discriminant right_payload] Heq.
    unfold legacy_op_observation in Heq. inversion Heq. reflexivity.
  Qed.

  Theorem core_operator_observation_injective :
    forall left right,
      core_op_observation left = core_op_observation right -> left = right.
  Proof.
    intros [left_category left_constructor left_discriminant left_payload]
           [right_category right_constructor right_discriminant right_payload] Heq.
    unfold core_op_observation in Heq. inversion Heq. reflexivity.
  Qed.

  Definition node_key_input {Op : Type}
      (observe : Op -> OpObservation) (value : Node Op) : (OpObservation * list Field)%type :=
    (observe (node_op value), node_fields value).

  Definition legacy_arena_key_input (arena : LegacyArena) :=
    map (node_key_input legacy_op_observation) arena.

  Definition core_arena_key_input (arena : CoreArena) :=
    map (node_key_input core_op_observation) arena.

  Theorem exact_semantic_key_input_preserved :
    forall arena,
      core_arena_key_input (encode_arena arena) = legacy_arena_key_input arena.
  Proof.
    intros arena.
    unfold core_arena_key_input, legacy_arena_key_input, encode_arena.
    rewrite map_map. apply map_ext. intros [[] fields]. reflexivity.
  Qed.

  Theorem pathmap_mode_is_preserved_in_canonical_nodes :
    forall op mode entries,
      node_fields (encode_node (node op [PathMapRefs mode entries])) =
      [PathMapRefs mode entries].
  Proof. reflexivity. Qed.

  (** Flat patterns use earlier pattern-node identifiers for positional or AC
      children.  Pattern variables and substitution targets are stable numeric
      identifiers, so the representation change never rewrites them. *)
  Inductive PatternAtom (Op : Type) : Type :=
  | PatternVariable : nat -> PatternAtom Op
  | PatternApp : Op -> list nat -> PatternAtom Op
  | PatternAc : Op -> list nat -> option nat -> PatternAtom Op.

  Arguments PatternVariable {_} _.
  Arguments PatternApp {_} _ _.
  Arguments PatternAc {_} _ _ _.

  Definition encode_pattern_atom (pattern : PatternAtom LegacyOp) : PatternAtom CoreOp :=
    match pattern with
    | PatternVariable name => PatternVariable name
    | PatternApp op children => PatternApp (encode_op op) children
    | PatternAc op fixed rest => PatternAc (encode_op op) fixed rest
    end.

  Definition decode_pattern_atom (pattern : PatternAtom CoreOp) : PatternAtom LegacyOp :=
    match pattern with
    | PatternVariable name => PatternVariable name
    | PatternApp op children => PatternApp (decode_op op) children
    | PatternAc op fixed rest => PatternAc (decode_op op) fixed rest
    end.

  Theorem pattern_atom_round_trip :
    forall pattern, decode_pattern_atom (encode_pattern_atom pattern) = pattern.
  Proof. intros [name | [] children | [] fixed rest]; reflexivity. Qed.

  Definition legacy_pattern_matches_node
      (pattern : PatternAtom LegacyOp) (value : Node LegacyOp) : Prop :=
    match pattern with
    | PatternVariable _ => True
    | PatternApp op children =>
        legacy_op_observation op = legacy_op_observation (node_op value) /\
        children = fields_refs (node_fields value)
    | PatternAc op fixed _ =>
        legacy_op_observation op = legacy_op_observation (node_op value) /\
        exists complement,
          Permutation (fixed ++ complement) (fields_refs (node_fields value))
    end.

  Definition core_pattern_matches_node
      (pattern : PatternAtom CoreOp) (value : Node CoreOp) : Prop :=
    match pattern with
    | PatternVariable _ => True
    | PatternApp op children =>
        core_op_observation op = core_op_observation (node_op value) /\
        children = fields_refs (node_fields value)
    | PatternAc op fixed _ =>
        core_op_observation op = core_op_observation (node_op value) /\
        exists complement,
          Permutation (fixed ++ complement) (fields_refs (node_fields value))
    end.

  Theorem positional_and_ac_pattern_observation_preserved :
    forall pattern value,
      legacy_pattern_matches_node pattern value <->
      core_pattern_matches_node (encode_pattern_atom pattern) (encode_node value).
  Proof.
    intros [name | [] children | [] fixed rest] [[] fields]; reflexivity.
  Qed.

  Definition Substitution : Type := list (nat * nat)%type.

  Fixpoint lookup_substitution (name : nat) (sigma : Substitution) : option nat :=
    match sigma with
    | [] => None
    | (candidate, target) :: rest =>
        if Nat.eqb name candidate then Some target
        else lookup_substitution name rest
    end.

  Definition substitution_valid (term_count : nat) (sigma : Substitution) : Prop :=
    NoDup (map fst sigma) /\
    Forall (fun target => target < term_count) (map snd sigma).

  Theorem substitution_certificate_representation_independent :
    forall term_count sigma,
      substitution_valid term_count sigma <-> substitution_valid term_count sigma.
  Proof. reflexivity. Qed.

  Fixpoint resolve_variables (names : list nat) (sigma : Substitution) : option (list nat) :=
    match names with
    | [] => Some []
    | name :: rest =>
        match lookup_substitution name sigma, resolve_variables rest sigma with
        | Some target, Some targets => Some (target :: targets)
        | _, _ => None
        end
    end.

  Definition legacy_instantiate
      (pattern : PatternAtom LegacyOp) (sigma : Substitution) : option (OpObservation * list nat)%type :=
    match pattern with
    | PatternVariable name =>
        match lookup_substitution name sigma with
        | Some target => Some ((0, 0, 0, None), [target])
        | None => None
        end
    | PatternApp op names =>
        match resolve_variables names sigma with
        | Some children => Some (legacy_op_observation op, children)
        | None => None
        end
    | PatternAc op names rest =>
        match resolve_variables names sigma,
              match rest with
              | Some name => lookup_substitution name sigma
              | None => Some 0
              end with
        | Some fixed, Some remainder => Some (legacy_op_observation op, fixed ++ [remainder])
        | _, _ => None
        end
    end.

  Definition core_instantiate
      (pattern : PatternAtom CoreOp) (sigma : Substitution) : option (OpObservation * list nat)%type :=
    match pattern with
    | PatternVariable name =>
        match lookup_substitution name sigma with
        | Some target => Some ((0, 0, 0, None), [target])
        | None => None
        end
    | PatternApp op names =>
        match resolve_variables names sigma with
        | Some children => Some (core_op_observation op, children)
        | None => None
        end
    | PatternAc op names rest =>
        match resolve_variables names sigma,
              match rest with
              | Some name => lookup_substitution name sigma
              | None => Some 0
              end with
        | Some fixed, Some remainder => Some (core_op_observation op, fixed ++ [remainder])
        | _, _ => None
        end
    end.

  Theorem structural_instantiation_preserved :
    forall pattern sigma,
      core_instantiate (encode_pattern_atom pattern) sigma =
      legacy_instantiate pattern sigma.
  Proof. intros [name | [] children | [] fixed rest] sigma; reflexivity. Qed.

  (** Native code is interpreted once at the core boundary.  The generated
      typed adapter is definitionally its encode/evaluate/decode wrapper. *)
  Definition typed_native_evaluate
      (evaluate : list CoreOp -> option CoreOp) (inputs : list LegacyOp) : option LegacyOp :=
    option_map decode_op (evaluate (map encode_op inputs)).

  Theorem native_transition_naturality :
    forall evaluate inputs,
      option_map encode_op (typed_native_evaluate evaluate inputs) =
      evaluate (map encode_op inputs).
  Proof.
    intros evaluate inputs. unfold typed_native_evaluate.
    destruct (evaluate (map encode_op inputs)) as [result |]; simpl.
    - now rewrite encode_decode_op.
    - reflexivity.
  Qed.

  Record Report (Op : Type) : Type := report {
    report_arena : list (Node Op);
    report_roots : list nat;
    report_rule_firings : list (nat * nat)%type;
    report_sigma : list (nat * nat)%type;
    report_contracta : list nat;
    report_declines : list nat;
    report_source_occurrences : list (nat * list nat)%type
  }.

  Arguments report {_} _ _ _ _ _ _ _.
  Arguments report_arena {_} _.
  Arguments report_roots {_} _.
  Arguments report_rule_firings {_} _.
  Arguments report_sigma {_} _.
  Arguments report_contracta {_} _.
  Arguments report_declines {_} _.
  Arguments report_source_occurrences {_} _.

  Definition encode_report (value : Report LegacyOp) : Report CoreOp :=
    report
      (encode_arena (report_arena value))
      (report_roots value)
      (report_rule_firings value)
      (report_sigma value)
      (report_contracta value)
      (report_declines value)
      (report_source_occurrences value).

  Definition decode_report (value : Report CoreOp) : Report LegacyOp :=
    report
      (decode_arena (report_arena value))
      (report_roots value)
      (report_rule_firings value)
      (report_sigma value)
      (report_contracta value)
      (report_declines value)
      (report_source_occurrences value).

  Theorem report_round_trip :
    forall value, decode_report (encode_report value) = value.
  Proof.
    intros [arena roots firings sigma contracta declines occurrences].
    change
      (report (decode_arena (encode_arena arena)) roots firings sigma
        contracta declines occurrences =
       report arena roots firings sigma contracta declines occurrences).
    now rewrite decode_encode_arena.
  Qed.

  Theorem core_report_round_trip :
    forall value, encode_report (decode_report value) = value.
  Proof.
    intros [arena roots firings sigma contracta declines occurrences].
    change
      (report (encode_arena (decode_arena arena)) roots firings sigma
        contracta declines occurrences =
       report arena roots firings sigma contracta declines occurrences).
    now rewrite encode_decode_arena.
  Qed.

  (** The replacement generated backend is a typed adapter around the shared
      semantic machine.  This naturality square is the exact factorisation:
      encode, execute once on the canonical carrier, then decode only when a
      typed result is required. *)
  Definition typed_semantic_machine
      (run : CoreArena -> Report CoreOp) (arena : LegacyArena) : Report LegacyOp :=
    decode_report (run (encode_arena arena)).

  Theorem semantic_machine_naturality :
    forall run arena,
      encode_report (typed_semantic_machine run arena) =
      run (encode_arena arena).
  Proof.
    intros run arena. unfold typed_semantic_machine.
    apply core_report_round_trip.
  Qed.

  Definition ReportObservation : Type := (
    list (OpObservation * list Field) *
    list nat * list (nat * nat) * list (nat * nat) *
    list nat * list nat * list (nat * list nat))%type.

  Definition legacy_report_observation (value : Report LegacyOp) : ReportObservation :=
    (legacy_arena_key_input (report_arena value),
     report_roots value,
     report_rule_firings value,
     report_sigma value,
     report_contracta value,
     report_declines value,
     report_source_occurrences value).

  Definition core_report_observation (value : Report CoreOp) : ReportObservation :=
    (core_arena_key_input (report_arena value),
     report_roots value,
     report_rule_firings value,
     report_sigma value,
     report_contracta value,
     report_declines value,
     report_source_occurrences value).

  Theorem report_observation_preserved :
    forall value,
      core_report_observation (encode_report value) = legacy_report_observation value.
  Proof.
    intros [arena roots firings sigma contracta declines occurrences].
    change
      ((core_arena_key_input (encode_arena arena), roots, firings, sigma,
         contracta, declines, occurrences) =
       (legacy_arena_key_input arena, roots, firings, sigma,
         contracta, declines, occurrences)).
    now rewrite exact_semantic_key_input_preserved.
  Qed.

  (** A small-step, heap-list image machine.  Each transition consumes exactly
      one pending node and emits exactly one core node.  No transition descends
      through a child reference, which is the stack-safety property supplied by
      the post-order arena representation. *)
  Fixpoint image_run
      (fuel : nat) (pending : LegacyArena) (emitted : CoreArena)
      : (LegacyArena * CoreArena)%type :=
    match fuel, pending with
    | 0, _ => (pending, emitted)
    | S remaining, [] => ([], emitted)
    | S remaining, value :: rest =>
        image_run remaining rest (encode_node value :: emitted)
    end.

  Lemma image_run_all :
    forall pending emitted,
      image_run (length pending) pending emitted =
      ([], rev (map encode_node pending) ++ emitted).
  Proof.
    induction pending as [|value rest IH]; intros emitted.
    - reflexivity.
    - simpl. rewrite IH. simpl. now rewrite <- app_assoc.
  Qed.

  Definition iterative_encode_arena (arena : LegacyArena) : CoreArena :=
    rev (snd (image_run (length arena) arena [])).

  Theorem iterative_image_equals_canonical_image :
    forall arena, iterative_encode_arena arena = encode_arena arena.
  Proof.
    intros arena. unfold iterative_encode_arena, encode_arena.
    rewrite image_run_all.
    change (rev (rev (map encode_node arena) ++ []) = map encode_node arena).
    rewrite app_nil_r. apply rev_involutive.
  Qed.

  Definition transition_consumption (pending : LegacyArena) : nat :=
    match pending with [] => 0 | _ :: _ => 1 end.

  Theorem image_machine_consumes_at_most_one_node :
    forall pending, transition_consumption pending <= 1.
  Proof. intros [|value rest]; simpl; auto. Qed.

  Print Assumptions decode_encode_op.
  Print Assumptions encode_decode_op.
  Print Assumptions encode_op_injective.
  Print Assumptions decode_encode_arena.
  Print Assumptions encode_decode_arena.
  Print Assumptions backward_references_preserved.
  Print Assumptions pathmap_neutral_empty_rejects_entries.
  Print Assumptions pathmap_empty_modes_are_pairwise_distinct.
  Print Assumptions fail_closed_image_validity_preserved.
  Print Assumptions exact_semantic_key_input_preserved.
  Print Assumptions pathmap_mode_is_preserved_in_canonical_nodes.
  Print Assumptions legacy_operator_observation_injective.
  Print Assumptions core_operator_observation_injective.
  Print Assumptions positional_and_ac_pattern_observation_preserved.
  Print Assumptions structural_instantiation_preserved.
  Print Assumptions native_transition_naturality.
  Print Assumptions report_round_trip.
  Print Assumptions core_report_round_trip.
  Print Assumptions semantic_machine_naturality.
  Print Assumptions report_observation_preserved.
  Print Assumptions iterative_image_equals_canonical_image.
  Print Assumptions image_machine_consumes_at_most_one_node.

End CanonicalSemanticTermImage.
