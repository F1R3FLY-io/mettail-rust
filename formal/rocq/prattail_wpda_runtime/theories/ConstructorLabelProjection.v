(** Original constructor-label selection and lazy observation boundary.

    Sources: macros/src/gen/mod.rs::generate_var_label/generate_literal_label;
    macros/src/gen/native/mod.rs::NativeType, native_type_to_string and
    is_byte_vector. Move the original richer 25-variant NativeType, including
    Other(String), and its exact string classifier/predicates to grammar-core.
    This is NOT NativeKind and must not be collapsed into its 20 variants.
    Keep native_type_to_string/is_byte_vector as unchanged syn observations;
    the macro extension trait retains from_syn_type at its original callsites.

    The literal worker calls byte-vector observation FIRST, calls NativeType
    classification only on false, tests is_integer before matching other kinds,
    and invokes the existing constructor only for the selected spelling.
    The two Other spelling tests retain their order and case sensitivity.
    Callbacks are stateful below; the constructor may reject. The observation
    callbacks are total, as are the original shallow probes on finite syn data.
    This model does not certify allocation failure, panic unwinding, arbitrary
    Rust-type equivalence, decoder/value parity, or serialized metadata.

    Var naming retains the original Rust chars().next().unwrap_or('V'), Unicode
    to_uppercase().collect::<String>(), then format_ident!("{}Var", prefix).
    Unicode scalars and uppercase are abstract parameters, NOT ASCII byte
    operations or a newly derived Unicode table. The Rust implementation must
    retain those exact standard-library calls; arbitrary Ident validation and
    span construction stay in the original constructor callback.

    SyntheticRuleProjection already proves ordered recipes/materialization.
    The final lemmas instantiate only its native/Var label boundary, not a new
    synthesis driver or permission to evaluate any callback eagerly.
*)
From Stdlib Require Import List String Bool Arith.
From PrattailWpdaRuntime Require Import NativeKindProjection SyntheticRuleProjection.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Set Implicit Arguments.

Module ConstructorLabelProjection.
Module K := NativeKindProjection.NativeKindProjection.
Module S := SyntheticRuleProjection.SyntheticRuleProjection.

Inductive NativeType :=
| Int8 | Int16 | Int32 | Int64 | Int128 | Isize
| UInt8 | UInt16 | UInt32 | UInt64 | UInt128 | Usize
| Float32 | Float64 | BoolType | Str
| CanonicalBigInt | CanonicalBigRat | CanonicalFixedPoint
| VecCollection | HashBagCollection | HashSetCollection
| HashMapLitCollection | HashMapCollection | Other (spelling : string).

(** Finite denotation of the unchanged literal-match arms, in source order.
    This is not a proposed production lookup table. *)
Definition known_names : list (string * NativeType) :=
  [("i8", Int8); ("i16", Int16); ("i32", Int32); ("i64", Int64);
   ("i128", Int128); ("isize", Isize); ("u8", UInt8); ("u16", UInt16);
   ("u32", UInt32); ("u64", UInt64); ("u128", UInt128); ("usize", Usize);
   ("f32", Float32); ("f64", Float64); ("bool", BoolType);
   ("str", Str); ("String", Str); ("CanonicalBigRat", CanonicalBigRat);
   ("CanonicalFixedPoint", CanonicalFixedPoint); ("Vec", VecCollection);
   ("HashBag", HashBagCollection); ("HashSet", HashSetCollection);
   ("HashMapLit", HashMapLitCollection); ("HashMap", HashMapCollection)].
Definition original_from_type_str spelling :=
  match find (fun entry => String.eqb spelling (fst entry)) known_names with
  | Some entry => snd entry
  | None => if K.ends_bigint spelling then CanonicalBigInt else Other spelling
  end.
Definition shared_from_type_str := original_from_type_str.
Definition original_is_integer native := match native with
  | Int8 | Int16 | Int32 | Int64 | Int128 | Isize
  | UInt8 | UInt16 | UInt32 | UInt64 | UInt128 | Usize
  | CanonicalBigInt => true | _ => false end.
Definition original_is_float native := match native with
  | Float32 | Float64 => true | _ => false end.
Definition original_is_string native := match native with Str => true | _ => false end.
Definition original_is_collection native := match native with
  | VecCollection | HashBagCollection | HashSetCollection
  | HashMapLitCollection | HashMapCollection => true | _ => false end.

(** The unchanged syn adapter observes exactly last-segment spelling; absent
    segments and every non-Path shape use the original "unknown" spelling.
    It does not unwrap references, Arc, or any generic argument. *)
Definition original_type_spelling source :=
  match source with
  | K.SourceNonPath _ => "unknown"
  | K.SourcePath _ _ segments => match K.last_observation segments with
    | None => "unknown" | Some segment => K.ident_spelling segment end
  end.
Definition original_from_syn_type source :=
  original_from_type_str (original_type_spelling source).
Definition shared_syn_adapter source :=
  shared_from_type_str (original_type_spelling source).
Theorem syn_adapter_reuses_exact_classifier : forall source,
  shared_syn_adapter source = original_from_syn_type source.
Proof. reflexivity. Qed.
Theorem exact_name_rows :
  map (fun row => original_from_type_str (fst row)) known_names = map snd known_names.
Proof. vm_compute; reflexivity. Qed.
Theorem richer_kinds_and_opaque_spelling_are_not_collapsed :
  original_from_type_str "Vec" = VecCollection /\
  original_from_type_str "HashSet" = HashSetCollection /\
  original_from_type_str "HashSetLit" = Other "HashSetLit" /\
  original_from_type_str "PathMapLit" = Other "PathMapLit" /\
  original_from_type_str "Arc" = Other "Arc" /\
  original_from_type_str "UserBigInt" = CanonicalBigInt /\
  original_from_type_str "BigRat" = Other "BigRat" /\
  original_from_type_str "Fixed" = Other "Fixed".
Proof. vm_compute; repeat split; reflexivity. Qed.
Theorem unknown_source_shapes_keep_original_fallback : forall tag,
  original_from_syn_type (K.SourceNonPath tag) = Other "unknown" /\
  original_from_syn_type (K.SourcePath None false []) = Other "unknown".
Proof. intros; split; reflexivity. Qed.

Inductive Event := ByteProbe | NativeClassification | IntegerProbe
| OtherSetProbe | OtherPathmapProbe | Construct (spelling : string).

(** The original trailing match, INCLUDING its redundant integer arms. *)
Definition original_kind_match native : string * list Event :=
  match native with
  | Float32 | Float64 => ("FloatLit", [])
  | BoolType => ("BoolLit", []) | Str => ("StringLit", [])
  | CanonicalBigRat => ("RatLit", [])
  | CanonicalFixedPoint => ("FixedLit", [])
  | VecCollection => ("ListLit", [])
  | HashBagCollection | HashSetCollection => ("BagLit", [])
  | HashMapLitCollection | HashMapCollection => ("MapLit", [])
  | Other spelling =>
      if String.eqb spelling "HashSetLit" then ("SetLit", [OtherSetProbe])
      else if String.eqb spelling "PathMapLit" then
        ("PathmapLit", [OtherSetProbe; OtherPathmapProbe])
      else ("Lit", [OtherSetProbe; OtherPathmapProbe])
  | Int8 | Int16 | Int32 | Int64 | Int128 | Isize
  | UInt8 | UInt16 | UInt32 | UInt64 | UInt128 | Usize
  | CanonicalBigInt => ("NumLit", [])
  end.
Definition shared_nonbyte_selection native :=
  if original_is_integer native then ("NumLit", [IntegerProbe])
  else let '(label, probes) := original_kind_match native in
       (label, IntegerProbe :: probes).
Definition selected_label (byte : bool) native :=
  if byte then "BytesLit" else fst (shared_nonbyte_selection native).
Theorem byte_selection_does_not_depend_on_native : forall first second,
  selected_label true first = selected_label true second.
Proof. reflexivity. Qed.
Theorem collection_and_wrapper_labels_remain_distinct :
  selected_label false VecCollection = "ListLit" /\
  selected_label false HashBagCollection = "BagLit" /\
  selected_label false HashSetCollection = "BagLit" /\
  selected_label false HashMapLitCollection = "MapLit" /\
  selected_label false HashMapCollection = "MapLit" /\
  selected_label false (Other "HashSetLit") = "SetLit" /\
  selected_label false (Other "PathMapLit") = "PathmapLit" /\
  selected_label false (Other "std::HashSetLit") = "Lit".
Proof. vm_compute; repeat split; reflexivity. Qed.
Theorem wrapper_probes_short_circuit_in_original_order :
  shared_nonbyte_selection (Other "HashSetLit") =
    ("SetLit", [IntegerProbe; OtherSetProbe]) /\
  shared_nonbyte_selection (Other "PathMapLit") =
    ("PathmapLit", [IntegerProbe; OtherSetProbe; OtherPathmapProbe]) /\
  shared_nonbyte_selection (Other "Unknown") =
    ("Lit", [IntegerProbe; OtherSetProbe; OtherPathmapProbe]).
Proof. vm_compute; repeat split; reflexivity. Qed.

Section LazyCallbacks.
Context {State Label Error : Type}.
Variable byte_probe : State -> bool * State.
Variable classify : State -> NativeType * State.
Variable construct : string -> State -> (Label + Error) * State.
Definition invoke prefix spelling state :=
  let '(result, next) := construct spelling state in
  (result, next, prefix ++ [Construct spelling]).
Definition original_literal state :=
  let '(byte, after_byte) := byte_probe state in
  if byte then invoke [ByteProbe] "BytesLit" after_byte
  else let '(native, after_native) := classify after_byte in
       if original_is_integer native then
         invoke [ByteProbe; NativeClassification; IntegerProbe] "NumLit" after_native
       else let '(label, probes) := original_kind_match native in
         invoke ([ByteProbe; NativeClassification; IntegerProbe] ++ probes) label after_native.
Definition shared_literal state :=
  let '(byte, after_byte) := byte_probe state in
  if byte then invoke [ByteProbe] "BytesLit" after_byte
  else let '(native, after_native) := classify after_byte in
       let '(label, probes) := shared_nonbyte_selection native in
       invoke ([ByteProbe; NativeClassification] ++ probes) label after_native.
Theorem exact_lazy_literal_callback_schedule : forall state,
  shared_literal state = original_literal state.
Proof.
  intros state; unfold shared_literal, original_literal.
  destruct (byte_probe state) as [byte next]; destruct byte; [reflexivity|].
  destruct (classify next) as [native ready].
  unfold shared_nonbyte_selection; destruct (original_is_integer native); [reflexivity|].
  destruct (original_kind_match native); reflexivity.
Qed.
Theorem byte_success_suppresses_native_classification : forall state after_byte,
  byte_probe state = (true, after_byte) ->
  shared_literal state = invoke [ByteProbe] "BytesLit" after_byte.
Proof. intros; unfold shared_literal; rewrite H; reflexivity. Qed.
Theorem constructor_failure_keeps_exact_first_attempt : forall state after_byte error failed,
  byte_probe state = (true, after_byte) ->
  construct "BytesLit" after_byte = (inr error, failed) ->
  shared_literal state = (inr error, failed, [ByteProbe; Construct "BytesLit"]).
Proof. intros; unfold shared_literal; rewrite H; unfold invoke; rewrite H0; reflexivity. Qed.
Theorem selected_constructor_invoked_once : forall prefix spelling state result next,
  construct spelling state = (result, next) ->
  invoke prefix spelling state = (result, next, prefix ++ [Construct spelling]).
Proof. intros; unfold invoke; now rewrite H. Qed.
End LazyCallbacks.

Section UnicodeVar.
Context {Character Label Error State : Type}.
Variable fallback_V : Character.
Variable uppercase : Character -> string.
Variable construct_var : string -> State -> (Label + Error) * State.
Definition first_character characters :=
  match characters with [] => fallback_V | first :: _ => first end.
Definition original_var characters state :=
  construct_var (uppercase (first_character characters)) state.
Definition shared_var characters state :=
  let first := match characters with [] => fallback_V | first :: _ => first end in
  let prefix := uppercase first in construct_var prefix state.
Definition var_spelling characters := (uppercase (first_character characters) ++ "Var")%string.
Theorem var_retains_exact_unicode_operation_and_constructor : forall characters state,
  shared_var characters state = original_var characters state.
Proof. intros; destruct characters; reflexivity. Qed.
Theorem only_first_scalar_contributes : forall first suffix other,
  var_spelling (first :: suffix) = var_spelling (first :: other).
Proof. reflexivity. Qed.
Theorem uppercase_expansion_is_not_truncated : forall first suffix expanded,
  uppercase first = expanded -> var_spelling (first :: suffix) = (expanded ++ "Var")%string.
Proof. intros; unfold var_spelling, first_character; now rewrite H. Qed.
Theorem empty_name_retains_original_V_fallback :
  var_spelling [] = (uppercase fallback_V ++ "Var")%string.
Proof. reflexivity. Qed.
Theorem var_failure_preserved : forall characters state error failed,
  original_var characters state = (inr error, failed) ->
  shared_var characters state = (inr error, failed).
Proof. intros; rewrite var_retains_exact_unicode_operation_and_constructor; exact H. Qed.
End UnicodeVar.

Theorem original_native_recipe_label_boundary : forall home byte native,
  S.materialize_recipe (S.recipe_native home (selected_label byte native)) =
  S.raw_native home (selected_label byte native).
Proof. intros; apply S.materialize_native. Qed.
Theorem original_var_recipe_label_boundary : forall home spelling,
  S.materialize_recipe (S.recipe_var home spelling) = S.raw_var home spelling.
Proof. intros; apply S.materialize_var. Qed.

Print Assumptions syn_adapter_reuses_exact_classifier.
Print Assumptions exact_name_rows.
Print Assumptions richer_kinds_and_opaque_spelling_are_not_collapsed.
Print Assumptions unknown_source_shapes_keep_original_fallback.
Print Assumptions byte_selection_does_not_depend_on_native.
Print Assumptions collection_and_wrapper_labels_remain_distinct.
Print Assumptions wrapper_probes_short_circuit_in_original_order.
Print Assumptions exact_lazy_literal_callback_schedule.
Print Assumptions byte_success_suppresses_native_classification.
Print Assumptions constructor_failure_keeps_exact_first_attempt.
Print Assumptions selected_constructor_invoked_once.
Print Assumptions var_retains_exact_unicode_operation_and_constructor.
Print Assumptions only_first_scalar_contributes.
Print Assumptions uppercase_expansion_is_not_truncated.
Print Assumptions empty_name_retains_original_V_fallback.
Print Assumptions var_failure_preserved.
Print Assumptions original_native_recipe_label_boundary.
Print Assumptions original_var_recipe_label_boundary.
End ConstructorLabelProjection.
