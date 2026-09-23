(** Original NativeKind ownership/last-segment projection boundary.

    Source: ast/src/language/model.rs, NativeKind and its complete impl.
    Production intent is to MOVE the original 20-variant enum, constant methods,
    ordered lattice tables and FIFO promotion worker to grammar-core unchanged.
    Only from_syn_type is split: the AST extension trait extracts the original
    Type::Path/last Ident spelling, then the core method executes the SAME
    ordered string match and BigInt suffix fallback. No syn enters core.

    Reuse the exact named variant vocabulary already checked by
    NativeFirstDescriptorProjection; all_kinds below follows Rust declaration
    order (the abstract inductive declaration's order is not a wire encoding).
    The string branch roster is the finite denotation of the original Rust
    literal match, not a new production lookup table. Case-sensitive suffix
    matching is over the same byte spelling, with the ASCII suffix BigInt.

    Proofs cover shallow source observation, all constant rows, and every finite
    execution of the ORIGINAL seen-vector/FIFO worker. The worker's fuel below
    counts proof-observed queue pops only: it is not a production admission,
    termination, allocation, or resource policy. Exhaustive computation then
    shows all 20 current source graphs finish within 20 pops with exact ordered
    outputs. No numeric-losslessness theorem, transitive-edge redesign, carrier
    inference, canonical-schema alias policy, decoder, or ABI claim is made.

    API boundary: once the enum belongs to core, AST cannot add an inherent
    foreign-type method. NativeKindFromSynType must be in caller scope to retain
    NativeKind::from_syn_type syntax. Syn-free inherent methods and AST's enum
    reexport keep their existing types; workspace callsites need only the local
    extension-trait import. External users of that method need the same import.
*)
From Stdlib Require Import List String Bool Arith.
From PrattailWpdaRuntime Require Import NativeFirstDescriptorProjection.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Set Implicit Arguments.

Module NativeKindProjection.
Module N := NativeFirstDescriptorProjection.NativeFirstDescriptorProjection.
Definition Kind := N.NativeKind.

Definition all_kinds : list Kind :=
  [N.Int8; N.Int16; N.Int32; N.Int64; N.Int128; N.Isize; N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64; N.BoolKind; N.Str; N.CanonicalBigInt; N.CanonicalBigRat; N.CanonicalFixedPoint; N.Other].

(** Exact literal-match priority before the sole suffix arm. *)
Definition known_segments : list (string * Kind) := [
  ("i8", N.Int8);
  ("i16", N.Int16);
  ("i32", N.Int32);
  ("i64", N.Int64);
  ("i128", N.Int128);
  ("isize", N.Isize);
  ("u8", N.UInt8);
  ("u16", N.UInt16);
  ("u32", N.UInt32);
  ("u64", N.UInt64);
  ("u128", N.UInt128);
  ("usize", N.Usize);
  ("f32", N.Float32);
  ("f64", N.Float64);
  ("bool", N.BoolKind);
  ("str", N.Str);
  ("String", N.Str);
  ("CanonicalBigRat", N.CanonicalBigRat);
  ("CanonicalFixedPoint", N.CanonicalFixedPoint)
].
Definition ends_bigint name :=
  String.eqb (String.substring (String.length name - 6) 6 name) "BigInt".
Definition original_segment_match name : Kind :=
  match find (fun entry => String.eqb name (fst entry)) known_segments with
  | Some entry => snd entry
  | None => if ends_bigint name then N.CanonicalBigInt else N.Other end.

Record Segment := { ident_spelling : string; unobserved_arguments : nat }.
Inductive SourceType :=
| SourcePath (unobserved_qself : option nat) (unobserved_leading_colon : bool)
             (segments : list Segment)
| SourceNonPath (unobserved_tag_and_payload : nat).
Fixpoint last_observation {A} (values : list A) : option A := match values with
| [] => None | value :: rest => match rest with
  | [] => Some value | _ => last_observation rest end end.

(** Original Type::Path gate and last-segment observation, with the unchanged
    string-match body represented by original_segment_match above. *)
Definition source_from_syn_type ty : Kind := match ty with
| SourceNonPath _ => N.Other
| SourcePath _ _ segments => match last_observation segments with
  | None => N.Other | Some segment => original_segment_match (ident_spelling segment) end end.

Definition projected_last_segment ty : option string := match ty with
| SourceNonPath _ => None
| SourcePath _ _ segments => last_observation (map ident_spelling segments) end.
Definition core_from_last_path_segment := original_segment_match.
Definition ast_extension ty : Kind := match projected_last_segment ty with
| None => N.Other | Some name => core_from_last_path_segment name end.

Lemma last_observation_map : forall A B (f : A -> B) values,
  last_observation (map f values) = option_map f (last_observation values).
Proof.
  intros A B f values; induction values as [|value rest IH]; [reflexivity|].
  destruct rest as [|next rest]; [reflexivity|]. cbn in *. exact IH.
Qed.

Theorem original_syn_adapter_projection : forall ty,
  ast_extension ty = source_from_syn_type ty.
Proof.
  intros [qself colon segments|other]; [|reflexivity].
  unfold ast_extension, projected_last_segment, source_from_syn_type.
  rewrite last_observation_map.
  destruct (last_observation segments); reflexivity.
Qed.

Theorem path_prefix_arguments_and_qself_are_unobserved : forall qself colon segments,
  source_from_syn_type (SourcePath qself colon segments) =
  source_from_syn_type (SourcePath None false
    (map (fun segment => {| ident_spelling := ident_spelling segment;
                           unobserved_arguments := 0 |}) segments)).
Proof.
  intros. unfold source_from_syn_type. rewrite last_observation_map.
  destruct (last_observation segments); reflexivity.
Qed.

Theorem non_path_and_empty_path_remain_other : forall payload qself colon,
  ast_extension (SourceNonPath payload) = N.Other /\
  ast_extension (SourcePath qself colon []) = N.Other.
Proof. intros; split; reflexivity. Qed.

Lemma original_known_match_roster : map (fun entry => original_segment_match (fst entry)) known_segments =
  map snd known_segments.
Proof. vm_compute; reflexivity. Qed.

Example original_suffix_and_raw_identifier_boundaries :
  map original_segment_match
    ["BigInt"; "UserBigInt"; "CanonicalBigRatBigInt"; "r#BigInt"; "r#String";
     "BigRat"; "UserCanonicalBigRat"; "UserCanonicalFixedPoint"; "bigint"; "BigInteger"] =
  [N.CanonicalBigInt; N.CanonicalBigInt; N.CanonicalBigInt; N.CanonicalBigInt;
   N.Other; N.Other; N.Other; N.Other; N.Other; N.Other].
Proof. vm_compute; reflexivity. Qed.

Definition is_integer kind := match kind with
| N.Int8 | N.Int16 | N.Int32 | N.Int64 | N.Int128 | N.Isize
| N.UInt8 | N.UInt16 | N.UInt32 | N.UInt64 | N.UInt128 | N.Usize
| N.CanonicalBigInt => true | _ => false end.
Definition standard_token_variant kind : option string := match kind with
| N.Float32 | N.Float64 => Some "Float" | N.BoolKind => Some "Boolean" | N.Str => Some "StringLit"
| N.CanonicalBigInt | N.CanonicalBigRat | N.CanonicalFixedPoint => None
| N.Int8 | N.Int16 | N.Int32 | N.Int64 | N.Int128 | N.Isize
| N.UInt8 | N.UInt16 | N.UInt32 | N.UInt64 | N.UInt128 | N.Usize => Some "Integer"
| N.Other => None end.

(** Exact ordered tables, including original isize/usize policy. These are
    source facts, not a derivation from bit widths or host pointer size. *)
Definition lossless_targets kind : list Kind := match kind with
| N.Int8 => [N.Int16; N.Int32; N.Int64; N.Int128; N.CanonicalBigInt; N.CanonicalBigRat]
| N.Int16 => [N.Int32; N.Int64; N.Int128; N.CanonicalBigInt; N.CanonicalBigRat]
| N.Int32 => [N.Int64; N.Int128; N.CanonicalBigInt; N.CanonicalBigRat]
| N.Int64 => [N.Int128; N.CanonicalBigInt; N.CanonicalBigRat]
| N.Int128 => [N.CanonicalBigInt; N.CanonicalBigRat]
| N.Isize => [N.Int128; N.CanonicalBigInt; N.CanonicalBigRat]
| N.UInt8 => [N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Int16; N.Int32; N.Int64; N.Int128; N.CanonicalBigInt; N.CanonicalBigRat]
| N.UInt16 => [N.UInt32; N.UInt64; N.UInt128; N.Int32; N.Int64; N.Int128; N.CanonicalBigInt; N.CanonicalBigRat]
| N.UInt32 => [N.UInt64; N.UInt128; N.Int64; N.Int128; N.CanonicalBigInt; N.CanonicalBigRat]
| N.UInt64 => [N.UInt128; N.Int128; N.CanonicalBigInt; N.CanonicalBigRat]
| N.UInt128 => [N.CanonicalBigInt; N.CanonicalBigRat]
| N.Usize => [N.UInt128; N.Int128; N.CanonicalBigInt; N.CanonicalBigRat]
| N.Float32 => [N.Float64; N.CanonicalBigRat]
| N.Float64 => [N.CanonicalBigRat]
| N.BoolKind => [N.Int8; N.Int16; N.Int32; N.Int64; N.Int128; N.Isize; N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.CanonicalBigInt; N.CanonicalBigRat]
| N.Str => []
| N.CanonicalBigInt => [N.CanonicalBigRat]
| N.CanonicalBigRat => []
| N.CanonicalFixedPoint => [N.CanonicalBigRat]
| N.Other => []
end.
Definition lossy_targets kind : list Kind := match kind with
| N.Int8 => [N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64]
| N.Int16 => [N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64]
| N.Int32 => [N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64]
| N.Int64 => [N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64]
| N.Int128 => [N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64]
| N.Isize => [N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64]
| N.UInt8 => [N.Float32; N.Float64]
| N.UInt16 => [N.Float32; N.Float64]
| N.UInt32 => [N.Float32; N.Float64]
| N.UInt64 => [N.Float32; N.Float64]
| N.UInt128 => [N.Float32; N.Float64]
| N.Usize => [N.Float32; N.Float64]
| N.Float32 => [N.Int8; N.Int16; N.Int32; N.Int64; N.Int128; N.Isize; N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.CanonicalFixedPoint]
| N.Float64 => [N.Int8; N.Int16; N.Int32; N.Int64; N.Int128; N.Isize; N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.CanonicalFixedPoint]
| N.BoolKind => [N.Float32; N.Float64]
| N.Str => []
| N.CanonicalBigInt => [N.Int8; N.Int16; N.Int32; N.Int64; N.Int128; N.Isize; N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64]
| N.CanonicalBigRat => [N.CanonicalBigInt; N.Int8; N.Int16; N.Int32; N.Int64; N.Int128; N.Isize; N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64; N.CanonicalFixedPoint]
| N.CanonicalFixedPoint => [N.Int8; N.Int16; N.Int32; N.Int64; N.Int128; N.Isize; N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64; N.CanonicalBigInt]
| N.Other => []
end.

Definition frozen_integer_flags :=
  [true; true; true; true; true; true; true; true; true; true; true; true;
   false; false; false; false; true; false; false; false].
Definition frozen_token_variants : list (option string) :=
  [Some "Integer"; Some "Integer"; Some "Integer"; Some "Integer"; Some "Integer"; Some "Integer";
   Some "Integer"; Some "Integer"; Some "Integer"; Some "Integer"; Some "Integer"; Some "Integer";
   Some "Float"; Some "Float"; Some "Boolean"; Some "StringLit"; None; None; None; None].
Definition frozen_lossless_rows : list (list Kind) := [
  [N.Int16; N.Int32; N.Int64; N.Int128; N.CanonicalBigInt; N.CanonicalBigRat];
  [N.Int32; N.Int64; N.Int128; N.CanonicalBigInt; N.CanonicalBigRat];
  [N.Int64; N.Int128; N.CanonicalBigInt; N.CanonicalBigRat];
  [N.Int128; N.CanonicalBigInt; N.CanonicalBigRat];
  [N.CanonicalBigInt; N.CanonicalBigRat];
  [N.Int128; N.CanonicalBigInt; N.CanonicalBigRat];
  [N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Int16; N.Int32; N.Int64; N.Int128; N.CanonicalBigInt; N.CanonicalBigRat];
  [N.UInt32; N.UInt64; N.UInt128; N.Int32; N.Int64; N.Int128; N.CanonicalBigInt; N.CanonicalBigRat];
  [N.UInt64; N.UInt128; N.Int64; N.Int128; N.CanonicalBigInt; N.CanonicalBigRat];
  [N.UInt128; N.Int128; N.CanonicalBigInt; N.CanonicalBigRat];
  [N.CanonicalBigInt; N.CanonicalBigRat];
  [N.UInt128; N.Int128; N.CanonicalBigInt; N.CanonicalBigRat];
  [N.Float64; N.CanonicalBigRat];
  [N.CanonicalBigRat];
  [N.Int8; N.Int16; N.Int32; N.Int64; N.Int128; N.Isize; N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.CanonicalBigInt; N.CanonicalBigRat];
  [];
  [N.CanonicalBigRat];
  [];
  [N.CanonicalBigRat];
  []
].
Definition frozen_lossy_rows : list (list Kind) := [
  [N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64];
  [N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64];
  [N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64];
  [N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64];
  [N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64];
  [N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64];
  [N.Float32; N.Float64];
  [N.Float32; N.Float64];
  [N.Float32; N.Float64];
  [N.Float32; N.Float64];
  [N.Float32; N.Float64];
  [N.Float32; N.Float64];
  [N.Int8; N.Int16; N.Int32; N.Int64; N.Int128; N.Isize; N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.CanonicalFixedPoint];
  [N.Int8; N.Int16; N.Int32; N.Int64; N.Int128; N.Isize; N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.CanonicalFixedPoint];
  [N.Float32; N.Float64];
  [];
  [N.Int8; N.Int16; N.Int32; N.Int64; N.Int128; N.Isize; N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64];
  [N.CanonicalBigInt; N.Int8; N.Int16; N.Int32; N.Int64; N.Int128; N.Isize; N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64; N.CanonicalFixedPoint];
  [N.Int8; N.Int16; N.Int32; N.Int64; N.Int128; N.Isize; N.UInt8; N.UInt16; N.UInt32; N.UInt64; N.UInt128; N.Usize; N.Float32; N.Float64; N.CanonicalBigInt];
  []
].

Lemma twenty_original_variant_cases : List.length all_kinds = 20.
Proof. reflexivity. Qed.
Lemma every_original_kind_is_enumerated : forall kind, In kind all_kinds.
Proof. intros kind; destruct kind; cbn; tauto. Qed.
Lemma integer_and_token_method_goldens :
  map is_integer all_kinds = frozen_integer_flags /\
  map standard_token_variant all_kinds = frozen_token_variants.
Proof. split; reflexivity. Qed.
Lemma ordered_lattice_table_goldens :
  map lossless_targets all_kinds = frozen_lossless_rows /\
  map lossy_targets all_kinds = frozen_lossy_rows.
Proof. split; reflexivity. Qed.

Definition kind_eq_dec : forall lhs rhs : Kind, {lhs = rhs} + {lhs <> rhs}.
Proof. decide equality. Defined.
Definition already_seen kind seen := if in_dec kind_eq_dec kind seen then true else false.
Definition saturating_successor distance := Nat.min 255 (S distance).
Inductive PromotionEvent :=
| Pop (kind : Kind) (distance : nat)
| TestSeen (kind : Kind) (answer : bool)
| AppendSeen (kind : Kind)
| Distance (previous next : nat)
| AppendOutput (kind : Kind) (distance : nat)
| PushQueue (kind : Kind) (distance : nat).
Record State := {
  seen : list Kind;
  output : list (Kind * nat);
  queue : list (Kind * nat);
  events : list PromotionEvent
}.
Definition state s o q e := {| seen := s; output := o; queue := q; events := e |}.
Definition initial source := state [source] [] [(source, 0)] [].

(** The original inner for loop: seen test, seen.push, saturating_add, out.push,
    queue.push_back. No sorting, edge coalescing, or new enqueue algorithm. *)
Fixpoint scan_targets distance targets st := match targets with
| [] => st
| target :: rest =>
  let present := already_seen target (seen st) in
  let checked := events st ++ [TestSeen target present] in
  if present then scan_targets distance rest (state (seen st) (output st) (queue st) checked)
  else let next := saturating_successor distance in
    scan_targets distance rest
      (state (seen st ++ [target]) (output st ++ [(target, next)]) (queue st ++ [(target, next)])
        (checked ++ [AppendSeen target; Distance distance next;
                     AppendOutput target next; PushQueue target next]))
end.

Inductive Run := Finished (st : State) | FinitePrefix (st : State).
(** fuel indexes finite observations only; exhaustion is NOT a Rust outcome. *)
Fixpoint run fuel (edges : Kind -> list Kind) st := match queue st with
| [] => Finished st
| (kind, distance) :: rest => match fuel with
  | 0 => FinitePrefix st
  | S fuel' =>
    let popped := state (seen st) (output st) rest (events st ++ [Pop kind distance]) in
    run fuel' edges (scan_targets distance (edges kind) popped)
  end end.

Theorem finite_promotion_execution_substitution : forall fuel old_edges new_edges st,
  (forall kind, old_edges kind = new_edges kind) ->
  run fuel old_edges st = run fuel new_edges st.
Proof.
  induction fuel as [|fuel IH]; intros old_edges new_edges st law;
    cbn; destruct (queue st) as [|[kind distance] rest]; try reflexivity.
  rewrite (law kind). apply IH. exact law.
Qed.

Definition emitted_promotions result := match result with
| Finished st => Some (output st) | FinitePrefix _ => None end.

(** Strong concrete correspondence for EVERY current source kind. No new
    production fast path is justified or installed by this finite table fact. *)
Theorem all_twenty_original_promotion_outputs : forall kind,
  emitted_promotions (run 20 lossless_targets (initial kind)) =
    Some (map (fun target => (target, 1)) (lossless_targets kind)).
Proof. intros kind; destruct kind; vm_compute; reflexivity. Qed.

Lemma original_promotion_finishes_in_finite_observation : forall kind,
  exists st, run 20 lossless_targets (initial kind) = Finished st.
Proof. intros kind; destruct kind; eexists; vm_compute; reflexivity. Qed.

Example saturation_is_preserved_for_general_finite_states :
  output (scan_targets 255 [N.Int16] (state [N.Int8] [] [] [])) = [(N.Int16, 255)].
Proof. vm_compute; reflexivity. Qed.

Example duplicate_edge_is_tested_but_not_enqueued_twice :
  let st := scan_targets 0 [N.Int16; N.Int16] (state [N.Int8] [] [] []) in
  (seen st, output st, queue st, events st) =
  ([N.Int8; N.Int16], [(N.Int16, 1)], [(N.Int16, 1)],
   [TestSeen N.Int16 false; AppendSeen N.Int16; Distance 0 1;
    AppendOutput N.Int16 1; PushQueue N.Int16 1; TestSeen N.Int16 true]).
Proof. vm_compute; reflexivity. Qed.

Lemma source_initially_seen : forall source,
  seen (initial source) = [source] /\ queue (initial source) = [(source, 0)].
Proof. intros; split; reflexivity. Qed.

Print Assumptions last_observation_map.
Print Assumptions original_syn_adapter_projection.
Print Assumptions path_prefix_arguments_and_qself_are_unobserved.
Print Assumptions non_path_and_empty_path_remain_other.
Print Assumptions original_known_match_roster.
Print Assumptions original_suffix_and_raw_identifier_boundaries.
Print Assumptions twenty_original_variant_cases.
Print Assumptions every_original_kind_is_enumerated.
Print Assumptions integer_and_token_method_goldens.
Print Assumptions ordered_lattice_table_goldens.
Print Assumptions finite_promotion_execution_substitution.
Print Assumptions all_twenty_original_promotion_outputs.
Print Assumptions original_promotion_finishes_in_finite_observation.
Print Assumptions saturation_is_preserved_for_general_finite_states.
Print Assumptions duplicate_edge_is_tested_but_not_enqueued_twice.
Print Assumptions source_initially_seen.
End NativeKindProjection.
