(** The authored-Rewrites to canonical-rule boundary for the Regex application.

    The representations below mirror the subset of RhoValue and
    theory_compile.rs exercised by the 50 interleaved Data rewrite records.
    Map field order is irrelevant in Rust's BTreeMap; list order is not. This
    model does not assert that the generated parser or Rust compiler implements
    these functions. Those are separate executable refinement obligations.
    In particular, current canonical.rs emits ["premises": []] for a direct
    authored rewrite whereas the Data records omit the field when empty.
    Exact record equality requires the emitter to adopt that omission or a
    shared schema normalization before comparison. *)

From Stdlib Require Import String List Bool ZArith PeanoNat.
From RuntimeGrammar Require Import SemanticIntrinsics SemanticIntrinsicSchema.
Import ListNotations SemanticIntrinsics.SemanticIntrinsics.
Open Scope string_scope.

Module AuthoredRegexRewrites.

Inductive Value :=
| VNil | VBool (b : bool) | VInteger (n : Z) | VString (s : string)
| VList (items : list Value) | VMap (fields : list (string * Value)).

Inductive Sort :=
| SortName (name : string)
| SortVec (element : Sort)
| SortBag (element : Sort)
| SortSet (element : Sort)
| SortMap (key element : Sort)
| SortPathMap (key element : Sort)
| SortArrow (domain codomain : Sort).

Fixpoint sort_value (sort : Sort) : Value :=
  match sort with
  | SortName name => VString name
  | SortVec element => VList [VString "vec"; sort_value element]
  | SortBag element => VList [VString "bag"; sort_value element]
  | SortSet element => VList [VString "set"; sort_value element]
  | SortMap key element => VList [VString "map"; sort_value key; sort_value element]
  | SortPathMap key element =>
      VList [VString "pathmap"; sort_value key; sort_value element]
  | SortArrow domain codomain =>
      VList [VString "arrow"; sort_value domain; sort_value codomain]
  end.

Fixpoint sort_key (sort : Sort) : string :=
  match sort with
  | SortName name => name
  | SortVec element => "List(" ++ sort_key element ++ ")"
  | SortBag element => "HashBag(" ++ sort_key element ++ ")"
  | SortSet element => "Set(" ++ sort_key element ++ ")"
  | SortMap key element =>
      "Map(" ++ sort_key key ++ "," ++ sort_key element ++ ")"
  | SortPathMap key element =>
      "PathMap(" ++ sort_key key ++ "," ++ sort_key element ++ ")"
  | SortArrow domain codomain =>
      "[" ++ sort_key domain ++ " -> " ++ sort_key codomain ++ "]"
  end.

Inductive Literal :=
| NativeBool (b : bool)
| NativeString (s : string)
| NativeI128 (n : Z).

Definition literal_value (literal : Literal) : Value :=
  match literal with
  | NativeBool b => VList [VString "lit"; VString "bool"; VBool b]
  | NativeString s => VList [VString "lit"; VString "str"; VString s]
  | NativeI128 n => VList [VString "lit"; VString "i128"; VInteger n]
  end.

(** RhoValue::Integer is signed 128-bit; Z itself is not bounded. The
    authoring admission gate must establish this condition before encoding. *)
Definition native_i128_admitted (n : Z) : bool :=
  Z.leb (- (2 ^ 127))%Z n && Z.ltb n (2 ^ 127)%Z.

Definition literal_admitted (literal : Literal) : bool :=
  match literal with NativeI128 n => native_i128_admitted n | _ => true end.

Theorem admitted_i128_is_signed_128_bit :
  forall n,
    literal_admitted (NativeI128 n) = true ->
    (- (2 ^ 127) <= n < 2 ^ 127)%Z.
Proof.
  intros n H. unfold literal_admitted, native_i128_admitted in H.
  apply andb_true_iff in H. destruct H as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. split; assumption.
Qed.

Inductive Pattern :=
| PatternVariable (name : string)
| PatternConstructor (name : string) (arguments : list Pattern)
| LiteralPattern (literal : Literal)
| TypedCollection (element : Sort) (items : list Pattern)
    (remainder : option string).

Fixpoint pattern_value (pattern : Pattern) : Value :=
  match pattern with
  | PatternVariable name => VString name
  | PatternConstructor name arguments =>
      VList (VString name :: map pattern_value arguments)
  | LiteralPattern literal => literal_value literal
  | TypedCollection element items remainder =>
      VList [VString "coll_typed"; sort_value element;
             VList (map pattern_value items);
             match remainder with None => VNil | Some name => VString name end]
  end.

Definition typed_binding (binding : string * Sort) : Value :=
  VList [VString "typed"; VString (fst binding); sort_value (snd binding)].

Record Intrinsic := {
  intrinsic_op : string;
  intrinsic_inputs : list string;
  intrinsic_outputs : list (string * Sort)
}.

Definition intrinsic_shape (i : Intrinsic) : RawShape :=
  {| raw_opcode := intrinsic_op i;
     raw_inputs := intrinsic_inputs i;
     raw_outputs := map (fun output => (fst output, sort_key (snd output)))
                        (intrinsic_outputs i) |}.

Definition intrinsic_value (i : Intrinsic) : Value :=
  VList [VString "intrinsic";
    VMap [("op", VString (intrinsic_op i));
          ("inputs", VList (map VString (intrinsic_inputs i)));
          ("outputs", VList (map typed_binding (intrinsic_outputs i))) ]].

Inductive Premise :=
| Transition (source target : string)
| IntrinsicPremise (intrinsic : Intrinsic).

Definition premise_value (premise : Premise) : Value :=
  match premise with
  | Transition source target =>
      VList [VString "~>"; VString source; VString target]
  | IntrinsicPremise intrinsic => intrinsic_value intrinsic
  end.

Record Rule := {
  rule_name : string;
  rule_context : list (string * Sort);
  rule_left : Pattern;
  rule_premises : list Premise;
  rule_right : Pattern
}.

Definition rule_fields (rule : Rule) : list (string * Value) :=
  ([("name", VString (rule_name rule))] ++
  (match rule_context rule with
   | [] => []
   | context => [("context", VList (map typed_binding context))]
   end) ++
  [("left", pattern_value (rule_left rule))] ++
  (match rule_premises rule with
   | [] => []
   | premises => [("premises", VList (map premise_value premises))]
   end) ++
  [("right", pattern_value (rule_right rule))])%list.

Definition omit_empty_premises (fields : list (string * Value)) :=
  filter (fun entry =>
    if String.eqb (fst entry) "premises" then
      match snd entry with VList [] => false | _ => true end
    else true) fields.

Definition current_direct_emitter_fields (rule : Rule) : list (string * Value) :=
  [("name", VString (rule_name rule)); ("premises", VList []);
   ("left", pattern_value (rule_left rule));
   ("right", pattern_value (rule_right rule))].

Theorem empty_direct_rule_needs_premise_normalization :
  forall rule,
    rule_context rule = [] -> rule_premises rule = [] ->
    omit_empty_premises (current_direct_emitter_fields rule) =
      rule_fields rule.
Proof.
  intros [name context left premises right] Hcontext Hpremises.
  cbn in Hcontext, Hpremises. subst context premises. reflexivity.
Qed.

Definition rule_value (rule : Rule) : Value := VMap (rule_fields rule).

Definition field (key : string) (fields : list (string * Value)) : option Value :=
  option_map snd (find (fun entry => String.eqb (fst entry) key) fields).

Theorem native_literal_payloads_remain_native :
  forall b s n,
    pattern_value (LiteralPattern (NativeBool b)) =
      VList [VString "lit"; VString "bool"; VBool b] /\
    pattern_value (LiteralPattern (NativeString s)) =
      VList [VString "lit"; VString "str"; VString s] /\
    pattern_value (LiteralPattern (NativeI128 n)) =
      VList [VString "lit"; VString "i128"; VInteger n].
Proof. intros; repeat split; reflexivity. Qed.

Theorem typed_collection_preserves_element_and_item_order :
  forall element items remainder,
    pattern_value (TypedCollection element items remainder) =
      VList [VString "coll_typed"; sort_value element;
             VList (map pattern_value items);
             match remainder with None => VNil | Some name => VString name end].
Proof. reflexivity. Qed.

Theorem intrinsic_preserves_ordered_inputs_and_typed_outputs :
  forall i,
    intrinsic_value i =
      VList [VString "intrinsic";
        VMap [("op", VString (intrinsic_op i));
              ("inputs", VList (map VString (intrinsic_inputs i)));
              ("outputs", VList (map typed_binding (intrinsic_outputs i))) ]].
Proof. reflexivity. Qed.

Definition Environment := list (string * Sort).
Definition available (environment : Environment) (name : string) : bool :=
  existsb (fun binding => String.eqb (fst binding) name) environment.
Definition fresh_outputs (environment : Environment)
    (outputs : list (string * Sort)) : bool :=
  let names := map fst outputs in
  forallb (fun name => negb (available environment name) &&
                       Nat.eqb (count_occ String.string_dec names name) 1) names.

Definition admit_intrinsic (declared : Sort -> bool)
    (environment : Environment) (i : Intrinsic) : option Environment :=
  match decode_shape (intrinsic_shape i) with
  | None => None
  | Some _ =>
      if forallb (available environment) (intrinsic_inputs i) &&
         fresh_outputs environment (intrinsic_outputs i) &&
         forallb (fun output => declared (snd output)) (intrinsic_outputs i)
      then Some (environment ++ intrinsic_outputs i)%list
      else None
  end.

Definition admit_transition (environment : Environment)
    (source target : string) : option Environment :=
  match find (fun binding => String.eqb (fst binding) source) environment with
  | None => None
  | Some binding =>
      if negb (available environment target)
      then Some (environment ++ [(target, snd binding)])%list else None
  end.

Fixpoint admit_premises (declared : Sort -> bool)
    (environment : Environment) (premises : list Premise)
    : option Environment :=
  match premises with
  | [] => Some environment
  | Transition source target :: tail =>
      match admit_transition environment source target with
      | Some next => admit_premises declared next tail | None => None end
  | IntrinsicPremise i :: tail =>
      match admit_intrinsic declared environment i with
      | Some next => admit_premises declared next tail | None => None end
  end.

Theorem admitted_intrinsic_has_exact_schema_and_context :
  forall declared environment i result,
    admit_intrinsic declared environment i = Some result ->
    (exists shape, decode_shape (intrinsic_shape i) = Some shape) /\
    forallb (available environment) (intrinsic_inputs i) = true /\
    fresh_outputs environment (intrinsic_outputs i) = true /\
    forallb (fun output => declared (snd output)) (intrinsic_outputs i) = true /\
    result = (environment ++ intrinsic_outputs i)%list.
Proof.
  intros declared environment i result H.
  unfold admit_intrinsic in H.
  destruct (decode_shape (intrinsic_shape i)) as [shape|] eqn:Hshape;
    [|discriminate].
  destruct (forallb (available environment) (intrinsic_inputs i)) eqn:Hinputs;
    [|discriminate].
  destruct (fresh_outputs environment (intrinsic_outputs i)) eqn:Hfresh;
    [|discriminate].
  destruct (forallb (fun output => declared (snd output))
                    (intrinsic_outputs i)) eqn:Hsort; [|discriminate].
  inversion H; subst. repeat split; eauto.
Qed.

Theorem unavailable_intrinsic_input_is_rejected :
  forall declared environment i name,
    In name (intrinsic_inputs i) -> available environment name = false ->
    admit_intrinsic declared environment i = None.
Proof.
  intros declared environment i name Hin Hmissing.
  unfold admit_intrinsic.
  destruct (decode_shape (intrinsic_shape i)); [|reflexivity].
  destruct (forallb (available environment) (intrinsic_inputs i)) eqn:Hinputs;
    [|reflexivity].
  pose proof (proj1 (forallb_forall (available environment)
                    (intrinsic_inputs i)) Hinputs name Hin) as Hgot.
  congruence.
Qed.

Theorem nonfresh_intrinsic_output_is_rejected :
  forall declared environment i output,
    In output (intrinsic_outputs i) ->
    available environment (fst output) = true ->
    admit_intrinsic declared environment i = None.
Proof.
  intros declared environment i output Hin Hbound.
  unfold admit_intrinsic.
  destruct (decode_shape (intrinsic_shape i)); [|reflexivity].
  destruct (forallb (available environment) (intrinsic_inputs i));
    [|reflexivity].
  destruct (fresh_outputs environment (intrinsic_outputs i)) eqn:Hfresh;
    [|reflexivity].
  unfold fresh_outputs in Hfresh.
  pose proof (proj1 (forallb_forall
                    (fun name => negb (available environment name) &&
                                 Nat.eqb (count_occ String.string_dec
                                   (map fst (intrinsic_outputs i)) name) 1)
                    (map fst (intrinsic_outputs i))) Hfresh
                    (fst output) (in_map fst _ _ Hin)) as Hgot.
  cbn beta in Hgot. rewrite Hbound in Hgot. discriminate.
Qed.

Theorem undeclared_intrinsic_output_sort_is_rejected :
  forall declared environment i output,
    In output (intrinsic_outputs i) ->
    declared (snd output) = false ->
    admit_intrinsic declared environment i = None.
Proof.
  intros declared environment i output Hin Hunknown.
  unfold admit_intrinsic.
  destruct (decode_shape (intrinsic_shape i)); [|reflexivity].
  destruct (forallb (available environment) (intrinsic_inputs i));
    [|reflexivity].
  destruct (fresh_outputs environment (intrinsic_outputs i));
    [|reflexivity].
  destruct (forallb (fun item => declared (snd item))
                    (intrinsic_outputs i)) eqn:Hsort; [|reflexivity].
  pose proof (proj1 (forallb_forall
                    (fun item => declared (snd item))
                    (intrinsic_outputs i)) Hsort output Hin) as Hgot.
  congruence.
Qed.

Theorem admitted_intrinsic_has_existing_opcode_and_arities :
  forall declared environment i result,
    admit_intrinsic declared environment i = Some result ->
    exists opcode,
      decode_opcode (intrinsic_op i) = Some opcode /\
      length (intrinsic_inputs i) = length (intrinsic_domain opcode) /\
      length (intrinsic_outputs i) = length (intrinsic_codomain opcode).
Proof.
  intros declared environment i result Hadmit.
  destruct (admitted_intrinsic_has_exact_schema_and_context _ _ _ _ Hadmit)
    as [[shape Hshape] _].
  destruct (decoded_shape_has_exact_existing_arities _ _ Hshape) as [Hin Hout].
  unfold decode_shape in Hshape.
  cbn [intrinsic_shape raw_opcode raw_inputs raw_outputs] in Hshape.
  destruct (decode_opcode (intrinsic_op i)) as [opcode|] eqn:Hop;
    [|discriminate].
  destruct (shape_fields_valid opcode (intrinsic_inputs i)
              (map (fun output => (fst output, sort_key (snd output)))
                   (intrinsic_outputs i))) eqn:Hvalid; [|discriminate].
  inversion Hshape; subst shape. cbn in Hin, Hout.
  exists opcode. split; [reflexivity|].
  split; [exact Hin|]. now rewrite map_length in Hout.
Qed.

Theorem intrinsic_premises_are_checked_in_source_order :
  forall declared environment i tail result,
    admit_premises declared environment (IntrinsicPremise i :: tail) = Some result ->
    exists next,
      admit_intrinsic declared environment i = Some next /\
      admit_premises declared next tail = Some result.
Proof.
  intros declared environment i tail result H.
  simpl in H. destruct (admit_intrinsic declared environment i) as [next|]
    eqn:Hnext; [|discriminate].
  now exists next.
Qed.

Inductive SourceEntry := Authored (rule : Rule) | Existing (value : Value).

Definition translate_entry (entry : SourceEntry) : Value :=
  match entry with Authored rule => rule_value rule | Existing value => value end.

Definition translate_source (source : list SourceEntry) : list Value :=
  map translate_entry source.

Theorem translation_preserves_every_source_position :
  forall source index entry,
    nth_error source index = Some entry ->
    nth_error (translate_source source) index = Some (translate_entry entry).
Proof.
  intros source index entry H.
  unfold translate_source. now rewrite nth_error_map, H.
Qed.

Theorem translation_preserves_interleaving :
  forall before rule middle existing after,
    translate_source
      ((before ++ Authored rule :: middle ++ Existing existing :: after)%list) =
    (translate_source before ++ [rule_value rule] ++
     translate_source middle ++ [existing] ++ translate_source after)%list.
Proof.
  intros. unfold translate_source.
  repeat rewrite map_app. simpl.
  repeat rewrite map_app. simpl.
  repeat rewrite app_assoc. reflexivity.
Qed.

(** Exact source-order names of the 50 Data records currently interleaved with
    authored Rewrites in regex_gslt_application.rho. The migration requires
    each corresponding authored Rule to retain its complete fields; names
    alone are only an order/count witness, never an admission certificate. *)
Definition regex_data_rule_names : list string :=
  ["FullSurfaceDone"; "FullReadEnd"; "FullFinished"; "FullAdvance";
   "SearchSurfaceDone"; "PrefixReadEnd"; "PrefixFinished";
   "PrefixAdvance"; "SearchFound"; "SearchPrefixMiss";
   "SearchFinished"; "SearchAdvance"; "ReplaceInitialize";
   "RenderEmpty"; "RenderRightDone"; "JoinTextPieces";
   "ReplaceRenderDone"; "ReplaceFirstSplice"; "ReplaceAllSplice";
   "ReplaceAllPositive"; "ReplaceAllEmpty"; "ReplaceAllFinalEmpty";
   "ReplaceAllAdvanceEmpty"; "ReplaceJoinDone"; "ReplaceJoinEmptyDone";
   "SmartAltCompare"; "SmartAltSame"; "SmartAltDifferent";
   "DerivativeCompare"; "DerivativeSame"; "DerivativeDifferent";
   "ElaborateScalarStart"; "ElaborateScalarRead";
   "ElaborateScalarAdmitted"; "DerivativeScalarStart";
   "DerivativeScalarRead"; "DerivativeScalarAdmitted";
   "RepeatInitialize"; "RepeatAdmitBounds"; "RepeatCheckLower";
   "RepeatReachedLower"; "RepeatBelowLower";
   "RepeatCheckRequiredUpper"; "RepeatReversedBounds";
   "RepeatAppendRequired"; "RepeatIncrementRequired";
   "RepeatCheckOptionalUpper"; "RepeatReachedUpper";
   "RepeatBelowUpper"; "RepeatIncrementOptional"].

Example regex_data_has_fifty_rules : length regex_data_rule_names = 50.
Proof. reflexivity. Qed.

Definition authored_names (rules : list Rule) : list string :=
  map rule_name rules.

Theorem ordered_fifty_rule_translation :
  forall rules,
    authored_names rules = regex_data_rule_names ->
    length (translate_source (map Authored rules)) = 50 /\
    forall index rule,
      nth_error rules index = Some rule ->
      nth_error (translate_source (map Authored rules)) index =
        Some (rule_value rule).
Proof.
  intros rules Hnames. split.
  - unfold translate_source, authored_names in *.
    repeat rewrite map_length. rewrite <- (map_length rule_name rules).
    rewrite Hnames. exact regex_data_has_fifty_rules.
  - intros index rule Hrule.
    change (nth_error (translate_source (map Authored rules)) index =
              Some (translate_entry (Authored rule))).
    apply translation_preserves_every_source_position.
    now rewrite nth_error_map, Hrule.
Qed.

Print Assumptions native_literal_payloads_remain_native.
Print Assumptions empty_direct_rule_needs_premise_normalization.
Print Assumptions admitted_i128_is_signed_128_bit.
Print Assumptions typed_collection_preserves_element_and_item_order.
Print Assumptions intrinsic_preserves_ordered_inputs_and_typed_outputs.
Print Assumptions admitted_intrinsic_has_exact_schema_and_context.
Print Assumptions admitted_intrinsic_has_existing_opcode_and_arities.
Print Assumptions intrinsic_premises_are_checked_in_source_order.
Print Assumptions translation_preserves_every_source_position.
Print Assumptions translation_preserves_interleaving.
Print Assumptions ordered_fifty_rule_translation.

End AuthoredRegexRewrites.
