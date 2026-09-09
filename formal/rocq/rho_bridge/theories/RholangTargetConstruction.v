(** Concrete structural construction algebra for the neutral Rholang target.

    This is a specification, not a second runtime evaluator. Values retain
    ordered semantic heads and children. No operation evaluates a method,
    performs COMM, parses source, grants a capability, or chooses funding.
    The recursive mathematical carrier is not the proposed Rust storage:
    Rust uses checked references and the existing explicit worklist.

    Metadata equations mirror the admitted lowerer's named policies. Their
    representation correspondence to node bytes is a later emitter obligation.
    In particular, DDL and receive metadata are NOT ordinary child unions.

    This first algebra checkpoint is incomplete as an admission interface:
    fresh and receive below check local cardinalities only. They consume
    already scope-resolved descriptors; they do not establish URI permutation,
    uniqueness, machine-width limits, remainder validity, or scope ownership.
    RholangConstructionProtocol supplies checked dispatch and the admitted
    fresh/receive layouts over this algebra. Full session publication and
    source-producer correspondence remain separate obligations before a
    runtime target can be justified.
    The named theorems assert only the explicit equations and premises shown. *)

From Stdlib Require Import List String Bool PeanoNat ZArith Lia.
Import ListNotations.

Record Summary := { free_bits : list bool; uses_connective : bool }.
Definition closed_summary : Summary :=
  {| free_bits := []; uses_connective := false |}.

Fixpoint union_bits (left right : list bool) : list bool :=
  match left, right with
  | [], _ => right
  | _, [] => left
  | x :: xs, y :: ys => orb x y :: union_bits xs ys
  end.

Definition join_summary (left right : Summary) : Summary :=
  {| free_bits := union_bits (free_bits left) (free_bits right);
     uses_connective := orb (uses_connective left) (uses_connective right) |}.

(** Ordinary union preserves representation length. Scope removal instead
    rebuilds the surviving set bits, dropping trailing false entries. This
    models the admitted 0/1-byte image, not arbitrary hostile byte values. *)
Fixpoint trim_bits (bits : list bool) : list bool :=
  match bits with
  | [] => []
  | bit :: rest =>
    match bit, trim_bits rest with
    | false, [] => []
    | _, suffix => bit :: suffix
    end
  end.
Definition shift_bits (width : nat) (bits : list bool) : list bool :=
  trim_bits (skipn width bits).

Definition shifted_summary (width : nat) (body : Summary) : Summary :=
  {| free_bits := shift_bits width (free_bits body);
     uses_connective := uses_connective body |}.

Definition with_connective (flag : bool) (summary : Summary) : Summary :=
  {| free_bits := free_bits summary; uses_connective := flag |}.

Inductive UnaryOperator := BooleanNot | NumericNegate.
Inductive BinaryOperator :=
| Equal | NotEqual | Less | Greater | LessEqual | GreaterEqual
| BooleanAnd | BooleanOr | Add | Concat | Subtract | Multiply | Divide | Modulo.
Inductive PatternOperator := PatternAnd | PatternOr | PatternNot.
Inductive CaptureSlot := OrdinarySlot (identity : nat)
  | GuestSlot (name : string).

Record BindShape := {
  pattern_count : nat;
  free_count : nat;
  remainder_index : option nat
}.

(** A reference to closed opaque NAME data retained by the caller's adapter.
    It is not a raw process, serialized capability, lexical index or authority
    claim. Only the matching owner can supply the referenced name at emission. *)
Record HostNameSlot := { host_name_owner : nat; host_name_index : nat }.

Inductive HeadKind :=
| IntegerHead (integer : Z)
| BooleanHead (boolean : bool)
| TextHead (text : string)
| HostNameHead (slot : HostNameSlot)
| BoundHead (index : nat)
| CaptureHead (index : nat)
| WildcardHead
| PatternReferenceHead (index depth : nat)
| UnaryHead (operator : UnaryOperator)
| BinaryHead (operator : BinaryOperator)
| ListHead
| MapHead
| MethodHead (name : string)
| SendHead (persistent : bool)
| NewHead (width : nat) (uris injection_keys : list string)
| ReceiveHead (binds : list BindShape) (slots : list CaptureSlot)
    (persistent has_condition : bool)
| MatchHead
| PatternHead (operator : PatternOperator).

Inductive Value :=
| MakeValue (heads : list Head) (summary : Summary)
with Head :=
| MakeHead (kind : HeadKind) (ordered_children : list Value).

Definition heads_of (value : Value) : list Head :=
  match value with MakeValue heads _ => heads end.
Definition summary_of (value : Value) : Summary :=
  match value with MakeValue _ summary => summary end.

Definition empty : Value := MakeValue [] closed_summary.
Definition singleton (kind : HeadKind) (children : list Value)
    (summary : Summary) : Value :=
  MakeValue [MakeHead kind children] summary.
Definition text (s : string) : Value := singleton (TextHead s) [] closed_summary.
Definition boolean (b : bool) : Value := singleton (BooleanHead b) [] closed_summary.
Definition host_name (slot : HostNameSlot) : Value :=
  singleton (HostNameHead slot) [] closed_summary.

Definition append (left right : Value) : Value :=
  MakeValue (heads_of left ++ heads_of right)
    (join_summary (summary_of left) (summary_of right)).

Fixpoint children_summary (children : list Value) : Summary :=
  match children with
  | [] => closed_summary
  | child :: rest => join_summary (summary_of child) (children_summary rest)
  end.

Definition ordinary (kind : HeadKind) (children : list Value) : Value :=
  singleton kind children (children_summary children).

(** Observe the constructed value, including append-composed heads. This is
    deliberately NOT a source-node-kind predicate or arbitrary Par validator. *)
Definition single_string (value : Value) : bool :=
  match heads_of value with
  | [MakeHead (TextHead _) []] => true
  | _ => false
  end.

Definition addition_operator (left right : Value) : BinaryOperator :=
  if single_string left && single_string right then Concat else Add.
Definition addition (left right : Value) : Value :=
  ordinary (BinaryHead (addition_operator left right)) [left; right].

Definition unary (op : UnaryOperator) (operand : Value) : Value :=
  singleton (UnaryHead op) [operand] (summary_of operand).
Definition binary (op : BinaryOperator) (left right : Value) : Value :=
  singleton (BinaryHead op) [left; right]
    (join_summary (summary_of left) (summary_of right)).
Definition implication (antecedent consequent : Value) : Value :=
  binary BooleanOr (unary BooleanNot antecedent) consequent.

Definition list_value (children : list Value) : Value := ordinary ListHead children.
Definition pair_children (pairs : list (Value * Value)) : list Value :=
  flat_map (fun pair => [fst pair; snd pair]) pairs.
Definition map_value (pairs : list (Value * Value)) : Value :=
  ordinary MapHead (pair_children pairs).
Definition method (name : string) (receiver : Value) (arguments : list Value) : Value :=
  ordinary (MethodHead name) (receiver :: arguments).
Definition send (persistent : bool) (channel : Value) (payloads : list Value) : Value :=
  ordinary (SendHead persistent) (channel :: payloads).

(** The wire-list metadata policy is an explicit existing construction, not
    an assertion that arbitrary embedded processes are semantically closed. *)
Definition ddl_node (tag : string) (children : list Value) : Value :=
  singleton ListHead (text tag :: children) closed_summary.

Definition matches_value (target pattern : Value) : Value :=
  singleton MatchHead [target; pattern]
    (with_connective false (join_summary (summary_of target) (summary_of pattern))).
Definition statically_false_match (lowered_target : Value) : Value :=
  singleton (BooleanHead false) [] (with_connective false (summary_of lowered_target)).
Definition pattern_node (op : PatternOperator) (children : list Value) : Value :=
  singleton (PatternHead op) children (with_connective true (children_summary children)).
Definition pattern_implication (antecedent consequent : Value) : Value :=
  pattern_node PatternOr [pattern_node PatternNot [antecedent]; consequent].

Definition bound_summary (index : nat) : Summary :=
  {| free_bits := repeat false index ++ [true]; uses_connective := false |}.

Inductive ConstructionError :=
| IndexOutOfScope | IntegerOutOfRange | ChildArityMismatch
| InvalidBinderLayout | TargetIndexOutOfRange | MissingReference (index : nat).
Inductive ConstructionResult :=
| Constructed (value : Value)
| ConstructionRejected (error : ConstructionError).

Definition bound (scope index : nat) : ConstructionResult :=
  if index <? scope then Constructed (singleton (BoundHead index) [] (bound_summary index))
  else ConstructionRejected IndexOutOfScope.
Definition capture (width index : nat) : ConstructionResult :=
  if index <? width then Constructed
    (singleton (CaptureHead index) [] (with_connective true closed_summary))
  else ConstructionRejected IndexOutOfScope.
Definition wildcard (connective : bool) : Value :=
  singleton WildcardHead [] (with_connective connective closed_summary).
Definition pattern_reference (scope index depth : nat) : ConstructionResult :=
  if index <? scope then Constructed
    (singleton (PatternReferenceHead index depth) []
      (with_connective true (bound_summary index)))
  else ConstructionRejected IndexOutOfScope.

(** This admitted GInt branch is signed 64-bit. The existing GBigInt branch
    and the guest Nat carrier have different ranges. This check never truncates
    a source integer or claims to cover every Rholang numeric representation. *)
Definition integer (value : Z) : ConstructionResult :=
  if ((-9223372036854775808 <=? value) && (value <=? 9223372036854775807))%Z
  then Constructed (singleton (IntegerHead value) [] closed_summary)
  else ConstructionRejected IntegerOutOfRange.

Definition fresh (width : nat) (uris : list string) (body : Value) : ConstructionResult :=
  if List.length uris <=? width then Constructed
    (singleton (NewHead width uris []) [body] (shifted_summary width (summary_of body)))
  else ConstructionRejected InvalidBinderLayout.

(** Injection entries are children, not opaque embedded host processes. Their
    keys retain ordered-map association. The New summary is derived from its
    body only, as in the existing normalizer. Key ordering and supported closed
    injection-value validation are separate checked adapter obligations. *)
Definition fresh_with_injections (width : nat) (uris keys : list string)
    (body : Value) (injections : list Value) : ConstructionResult :=
  if Nat.eqb (List.length keys) (List.length injections) then
    if List.length uris <=? width then Constructed
      (singleton (NewHead width uris keys) (body :: injections)
        (shifted_summary width (summary_of body)))
    else ConstructionRejected InvalidBinderLayout
  else ConstructionRejected ChildArityMismatch.

Theorem empty_injections_specialize_fresh : forall width uris body,
  fresh_with_injections width uris [] body [] = fresh width uris body.
Proof. reflexivity. Qed.

Theorem injected_fresh_preserves_all_entries : forall width uris keys body injections value,
  fresh_with_injections width uris keys body injections = Constructed value ->
  List.length keys = List.length injections /\ List.length uris <= width /\
  heads_of value = [MakeHead (NewHead width uris keys) (body :: injections)] /\
  summary_of value = shifted_summary width (summary_of body).
Proof.
  intros width uris keys body injections value H; unfold fresh_with_injections in H.
  destruct (Nat.eqb (List.length keys) (List.length injections)) eqn:K; try discriminate.
  destruct (List.length uris <=? width) eqn:U; try discriminate.
  inversion H; subst. apply Nat.eqb_eq in K; apply Nat.leb_le in U.
  repeat split; auto.
Qed.

Theorem host_name_has_closed_nonstring_observation : forall slot,
  summary_of (host_name slot) = closed_summary /\ single_string (host_name slot) = false.
Proof. split; reflexivity. Qed.

Theorem host_name_retains_exact_slot : forall slot,
  heads_of (host_name slot) = [MakeHead (HostNameHead slot) []].
Proof. reflexivity. Qed.

Print Assumptions empty_injections_specialize_fresh.
Print Assumptions injected_fresh_preserves_all_entries.
Print Assumptions host_name_has_closed_nonstring_observation.
Print Assumptions host_name_retains_exact_slot.

Record BindValue := {
  bind_source : Value;
  bind_patterns : list Value;
  bind_free_count : nat;
  bind_remainder : option nat
}.
Definition bind_shape (b : BindValue) : BindShape :=
  {| pattern_count := List.length (bind_patterns b);
     free_count := bind_free_count b; remainder_index := bind_remainder b |}.
Definition bind_children (b : BindValue) : list Value := bind_source b :: bind_patterns b.
Definition bind_width (binds : list BindValue) : nat :=
  fold_right (fun b width => bind_free_count b + width) 0 binds.
Definition option_values (condition : option Value) : list Value :=
  match condition with None => [] | Some value => [value] end.
Definition receive_children (binds : list BindValue) (body : Value)
    (condition : option Value) : list Value :=
  flat_map bind_children binds ++ body :: option_values condition.

Definition receive_summary (binds : list BindValue) (body : Value)
    (condition : option Value) : Summary :=
  let sources := children_summary (map bind_source binds) in
  let width := bind_width binds in
  let source_body := union_bits (free_bits sources)
    (shift_bits width (free_bits (summary_of body))) in
  {| free_bits := match condition with
     | None => source_body
     | Some guard => union_bits source_body (shift_bits width (free_bits (summary_of guard)))
     end;
     uses_connective := uses_connective sources || uses_connective (summary_of body) |}.

Definition receive (binds : list BindValue) (slots : list CaptureSlot)
    (persistent : bool) (body : Value) (condition : option Value) : ConstructionResult :=
  if Nat.eqb (bind_width binds) (List.length slots) then
    Constructed (singleton
      (ReceiveHead (map bind_shape binds) slots persistent
        (match condition with None => false | Some _ => true end))
      (receive_children binds body condition) (receive_summary binds body condition))
  else ConstructionRejected InvalidBinderLayout.

(** Checked references return no default value. Ordered duplicate references
    remain ordered duplicates. The implementation must use its explicit work
    stack; this finite list specification states the result to preserve. *)
Fixpoint resolve_children (arena : list Value) (references : list nat)
    : option (list Value) :=
  match references with
  | [] => Some []
  | index :: rest =>
    match nth_error arena index, resolve_children arena rest with
    | Some value, Some values => Some (value :: values)
    | _, _ => None
    end
  end.

Definition checked_binary (op : BinaryOperator) (children : list Value)
    : ConstructionResult :=
  match children with
  | [lhs; rhs] => Constructed (binary op lhs rhs)
  | _ => ConstructionRejected ChildArityMismatch
  end.

Definition slot_index (width formal : nat) : option nat :=
  if formal <? width then Some (width - S formal) else None.

Record Origin := { occurrence_id : nat; diagnostic_span : option (nat * nat) }.
Record PendingContext := {
  provider_slots : list nat;
  capture_slots : list CaptureSlot;
  guard_roots : list nat;
  requested_discharge : bool;
  pending_obligations : list nat
}.
Record Artifact := {
  semantic_values : list Value;
  semantic_root : nat;
  occurrence_values : list (nat * Origin);
  pending_context : PendingContext
}.
Definition erase_origins (artifact : Artifact) :=
  (semantic_values artifact, semantic_root artifact,
   map fst (occurrence_values artifact), pending_context artifact).

Lemma union_bits_empty_right : forall bits, union_bits bits [] = bits.
Proof. intros [|bit bits]; reflexivity. Qed.

Lemma join_closed_left : forall summary, join_summary closed_summary summary = summary.
Proof. intros [bits flag]; reflexivity. Qed.
Lemma join_closed_right : forall summary, join_summary summary closed_summary = summary.
Proof. intros [bits flag]; unfold join_summary; cbn.
  rewrite union_bits_empty_right, orb_false_r. reflexivity. Qed.

Theorem append_empty_left : forall value, append empty value = value.
Proof. intros [heads summary]; unfold append; cbn. now rewrite join_closed_left. Qed.
Theorem append_empty_right : forall value, append value empty = value.
Proof. intros [heads summary]; unfold append; cbn.
  now rewrite app_nil_r, join_closed_right. Qed.
Theorem append_preserves_head_order : forall left right,
  heads_of (append left right) = heads_of left ++ heads_of right.
Proof. reflexivity. Qed.
Theorem append_preserves_head_multiplicity : forall left right,
  List.length (heads_of (append left right)) =
  List.length (heads_of left) + List.length (heads_of right).
Proof. intros; apply length_app. Qed.

Theorem empty_then_text_is_single : forall s, single_string (append empty (text s)) = true.
Proof. intros; rewrite append_empty_left; reflexivity. Qed.
Theorem two_text_heads_are_not_single : forall a b,
  single_string (append (text a) (text b)) = false.
Proof. reflexivity. Qed.
Theorem append_aware_addition_selects_concat : forall a b,
  addition_operator (append empty (text a)) (text b) = Concat.
Proof. intros; rewrite append_empty_left; reflexivity. Qed.
Theorem multiple_heads_select_add : forall a b c,
  addition_operator (append (text a) (text b)) (text c) = Add.
Proof. reflexivity. Qed.

Theorem binary_retains_order_and_summary : forall op left right,
  heads_of (binary op left right) = [MakeHead (BinaryHead op) [left; right]] /\
  summary_of (binary op left right) = join_summary (summary_of left) (summary_of right).
Proof. intros; split; reflexivity. Qed.
Theorem unary_retains_summary : forall op operand,
  summary_of (unary op operand) = summary_of operand.
Proof. reflexivity. Qed.
Theorem implication_negates_only_antecedent : forall left right,
  heads_of (implication left right) =
    [MakeHead (BinaryHead BooleanOr) [unary BooleanNot left; right]].
Proof. reflexivity. Qed.
Theorem list_retains_all_children : forall children,
  heads_of (list_value children) = [MakeHead ListHead children].
Proof. reflexivity. Qed.
Theorem map_retains_pairs_in_order : forall key value rest,
  pair_children ((key, value) :: rest) = key :: value :: pair_children rest.
Proof. reflexivity. Qed.
Theorem method_retains_receiver_first : forall name receiver args,
  heads_of (method name receiver args) = [MakeHead (MethodHead name) (receiver :: args)].
Proof. reflexivity. Qed.
Theorem send_retains_channel_payloads_and_persistence : forall persistent channel payloads,
  heads_of (send persistent channel payloads) =
    [MakeHead (SendHead persistent) (channel :: payloads)] /\
  summary_of (send persistent channel payloads) = children_summary (channel :: payloads).
Proof. intros; split; reflexivity. Qed.
Theorem list_summary_covers_every_child : forall children,
  summary_of (list_value children) = children_summary children.
Proof. reflexivity. Qed.
Theorem map_summary_covers_both_slots : forall pairs,
  summary_of (map_value pairs) = children_summary (pair_children pairs).
Proof. reflexivity. Qed.
Theorem method_summary_covers_receiver_and_arguments : forall name receiver args,
  summary_of (method name receiver args) = children_summary (receiver :: args).
Proof. reflexivity. Qed.
Theorem ddl_policy_retains_children_not_union : forall tag children,
  heads_of (ddl_node tag children) = [MakeHead ListHead (text tag :: children)] /\
  summary_of (ddl_node tag children) = closed_summary.
Proof. intros; split; reflexivity. Qed.
Theorem matching_retains_free_information : forall target pattern,
  free_bits (summary_of (matches_value target pattern)) =
    union_bits (free_bits (summary_of target)) (free_bits (summary_of pattern)) /\
  uses_connective (summary_of (matches_value target pattern)) = false.
Proof. intros; split; reflexivity. Qed.
Theorem false_match_retains_target_information : forall target,
  free_bits (summary_of (statically_false_match target)) = free_bits (summary_of target).
Proof. reflexivity. Qed.
Theorem spatial_connective_not_boolean_expression : forall op children,
  heads_of (pattern_node op children) = [MakeHead (PatternHead op) children] /\
  uses_connective (summary_of (pattern_node op children)) = true.
Proof. intros; split; reflexivity. Qed.
Theorem pattern_implication_retains_consequent : forall antecedent consequent,
  heads_of (pattern_implication antecedent consequent) =
    [MakeHead (PatternHead PatternOr)
      [pattern_node PatternNot [antecedent]; consequent]].
Proof. reflexivity. Qed.

Theorem fresh_success_retains_body_and_local_layout : forall width uris body value,
  fresh width uris body = Constructed value ->
  List.length uris <= width /\
  heads_of value = [MakeHead (NewHead width uris []) [body]] /\
  summary_of value = shifted_summary width (summary_of body).
Proof.
  intros width uris body value H; unfold fresh in H.
  destruct (List.length uris <=? width) eqn:E; try discriminate.
  inversion H; subst. apply Nat.leb_le in E. repeat split; auto.
Qed.
Theorem excessive_uri_count_rejected : forall width uris body,
  width < List.length uris -> fresh width uris body = ConstructionRejected InvalidBinderLayout.
Proof. intros width uris body H; unfold fresh.
  apply Nat.leb_gt in H; now rewrite H. Qed.
Theorem capture_success_is_not_bound_reference : forall width index value,
  capture width index = Constructed value ->
  index < width /\ heads_of value = [MakeHead (CaptureHead index) []] /\
  summary_of value = with_connective true closed_summary.
Proof. intros width index value H; unfold capture in H.
  destruct (index <? width) eqn:E; try discriminate.
  inversion H; subst. apply Nat.ltb_lt in E. repeat split; auto. Qed.
Theorem wildcard_preserves_explicit_policy : forall flag,
  summary_of (wildcard flag) = with_connective flag closed_summary.
Proof. reflexivity. Qed.
Theorem pattern_reference_retains_depth : forall scope index depth value,
  pattern_reference scope index depth = Constructed value ->
  index < scope /\
  heads_of value = [MakeHead (PatternReferenceHead index depth) []] /\
  summary_of value = with_connective true (bound_summary index).
Proof. intros scope index depth value H; unfold pattern_reference in H.
  destruct (index <? scope) eqn:E; try discriminate.
  inversion H; subst. apply Nat.ltb_lt in E. repeat split; auto. Qed.

Theorem out_of_scope_never_empty : forall scope index,
  scope <= index -> bound scope index = ConstructionRejected IndexOutOfScope.
Proof. intros scope index H; unfold bound.
  apply Nat.ltb_ge in H. now rewrite H. Qed.
Theorem bound_success_has_actual_index : forall scope index value,
  bound scope index = Constructed value ->
  index < scope /\ heads_of value = [MakeHead (BoundHead index) []] /\
  free_bits (summary_of value) = repeat false index ++ [true].
Proof. intros scope index value H; unfold bound in H.
  destruct (index <? scope) eqn:E; try discriminate.
  inversion H; subst. apply Nat.ltb_lt in E. repeat split; auto. Qed.
Theorem binary_rejects_wrong_arity : forall op children,
  List.length children <> 2 -> checked_binary op children = ConstructionRejected ChildArityMismatch.
Proof. intros op [|a [|b [|c rest]]] H; cbn in *; try reflexivity; contradiction. Qed.
Theorem checked_binary_preserves_exact_operands : forall op left right,
  checked_binary op [left; right] = Constructed (binary op left right).
Proof. reflexivity. Qed.
Theorem slot_success_is_in_range : forall width formal index,
  slot_index width formal = Some index -> formal < width /\ index < width.
Proof. intros width formal index H; unfold slot_index in H.
  destruct (formal <? width) eqn:E; try discriminate.
  inversion H; subst. apply Nat.ltb_lt in E; lia. Qed.
Theorem slot_out_of_range_rejected : forall width formal,
  width <= formal -> slot_index width formal = None.
Proof. intros width formal H; unfold slot_index.
  apply Nat.ltb_ge in H; now rewrite H. Qed.
Theorem formal_slot_order_is_reversed : forall width first second,
  first < second -> second < width ->
  exists first_index second_index,
    slot_index width first = Some first_index /\
    slot_index width second = Some second_index /\ second_index < first_index.
Proof.
  intros width first second Horder Hbound.
  assert (Hfirst : (first <? width) = true) by (apply Nat.ltb_lt; lia).
  assert (Hsecond : (second <? width) = true) by (apply Nat.ltb_lt; lia).
  exists (width - S first), (width - S second).
  unfold slot_index. rewrite Hfirst, Hsecond. repeat split; auto; lia.
Qed.
Theorem shifted_outer_index_cannot_alias_local_slot : forall width formal local outer,
  slot_index width formal = Some local -> local <> outer + width.
Proof. intros width formal local outer H.
  apply slot_success_is_in_range in H. lia. Qed.

Theorem receive_preserves_roles : forall binds slots persistent body condition value,
  receive binds slots persistent body condition = Constructed value ->
  bind_width binds = List.length slots /\
  heads_of value = [MakeHead
    (ReceiveHead (map bind_shape binds) slots persistent
      (match condition with None => false | Some _ => true end))
    (flat_map bind_children binds ++ body :: option_values condition)].
Proof. intros binds slots persistent body condition value H; unfold receive in H.
  destruct (Nat.eqb (bind_width binds) (List.length slots)) eqn:E; try discriminate.
  inversion H; subst. apply Nat.eqb_eq in E. split; auto. Qed.
Theorem receive_connectives_exclude_pattern_and_condition : forall binds body condition,
  uses_connective (receive_summary binds body condition) =
    uses_connective (children_summary (map bind_source binds)) || uses_connective (summary_of body).
Proof. reflexivity. Qed.
Theorem receive_free_information_includes_condition : forall binds body condition,
  free_bits (receive_summary binds body (Some condition)) =
    union_bits
      (union_bits (free_bits (children_summary (map bind_source binds)))
        (shift_bits (bind_width binds) (free_bits (summary_of body))))
      (shift_bits (bind_width binds) (free_bits (summary_of condition))).
Proof. reflexivity. Qed.

Theorem trim_preserves_every_bit : forall bits index,
  nth index (trim_bits bits) false = nth index bits false.
Proof.
  induction bits as [|bit rest IH]; intros index.
  - destruct index; reflexivity.
  - cbn [trim_bits]. destruct (trim_bits rest) as [|next suffix] eqn:E.
    + destruct bit, index; cbn; try reflexivity.
      * specialize (IH index). destruct index; exact IH.
      * specialize (IH index). destruct index; exact IH.
    + destruct bit, index; cbn; try reflexivity;
        specialize (IH index); exact IH.
Qed.

Theorem shift_preserves_surviving_indices : forall width bits index,
  nth index (shift_bits width bits) false = nth (width + index) bits false.
Proof.
  intros width bits index; unfold shift_bits; rewrite trim_preserves_every_bit.
  revert bits; induction width as [|width IH]; intros [|bit rest]; cbn;
    try reflexivity; try apply IH.
  destruct index; reflexivity.
Qed.

Theorem ordinary_union_retains_trailing_false : union_bits [true; false] [] = [true; false].
Proof. reflexivity. Qed.
Theorem scope_removal_trims_trailing_false : shift_bits 1 [true; false] = [].
Proof. reflexivity. Qed.

Example signed_integer_maximum_is_preserved :
  integer 9223372036854775807 =
    Constructed (singleton (IntegerHead 9223372036854775807) [] closed_summary).
Proof. reflexivity. Qed.
Example signed_integer_overflow_is_rejected :
  integer 9223372036854775808 = ConstructionRejected IntegerOutOfRange.
Proof. reflexivity. Qed.
Example signed_integer_minimum_is_preserved :
  integer (-9223372036854775808) =
    Constructed (singleton (IntegerHead (-9223372036854775808)) [] closed_summary).
Proof. reflexivity. Qed.
Example signed_integer_underflow_is_rejected :
  integer (-9223372036854775809) = ConstructionRejected IntegerOutOfRange.
Proof. reflexivity. Qed.

Theorem checked_reference_order : forall arena refs values,
  resolve_children arena refs = Some values ->
  Forall2 (fun index value => nth_error arena index = Some value) refs values.
Proof. intros arena refs; induction refs as [|index rest IH]; intros values H; cbn in H.
  - inversion H; constructor.
  - destruct (nth_error arena index) eqn:E; try discriminate.
    destruct (resolve_children arena rest) eqn:R; try discriminate.
    inversion H; subst. constructor; auto. Qed.
Theorem missing_reference_rejects : forall arena index rest,
  nth_error arena index = None -> resolve_children arena (index :: rest) = None.
Proof. intros; cbn; now rewrite H. Qed.
Theorem duplicate_reference_not_deduplicated : forall arena index value,
  nth_error arena index = Some value ->
  resolve_children arena [index; index] = Some [value; value].
Proof. intros; cbn; now rewrite H. Qed.

Theorem origin_changes_preserve_structure_and_obligations :
  forall values root occurrences first second context,
  erase_origins {| semantic_values := values; semantic_root := root;
    occurrence_values := map (fun index => (index, first index)) occurrences;
    pending_context := context |} =
  erase_origins {| semantic_values := values; semantic_root := root;
    occurrence_values := map (fun index => (index, second index)) occurrences;
    pending_context := context |}.
Proof. intros; unfold erase_origins; cbn; rewrite !map_map; reflexivity. Qed.

Print Assumptions append_empty_left.
Print Assumptions append_empty_right.
Print Assumptions append_preserves_head_order.
Print Assumptions append_preserves_head_multiplicity.
Print Assumptions empty_then_text_is_single.
Print Assumptions two_text_heads_are_not_single.
Print Assumptions append_aware_addition_selects_concat.
Print Assumptions multiple_heads_select_add.
Print Assumptions binary_retains_order_and_summary.
Print Assumptions unary_retains_summary.
Print Assumptions implication_negates_only_antecedent.
Print Assumptions list_retains_all_children.
Print Assumptions map_retains_pairs_in_order.
Print Assumptions method_retains_receiver_first.
Print Assumptions send_retains_channel_payloads_and_persistence.
Print Assumptions list_summary_covers_every_child.
Print Assumptions map_summary_covers_both_slots.
Print Assumptions method_summary_covers_receiver_and_arguments.
Print Assumptions ddl_policy_retains_children_not_union.
Print Assumptions matching_retains_free_information.
Print Assumptions false_match_retains_target_information.
Print Assumptions spatial_connective_not_boolean_expression.
Print Assumptions pattern_implication_retains_consequent.
Print Assumptions fresh_success_retains_body_and_local_layout.
Print Assumptions excessive_uri_count_rejected.
Print Assumptions capture_success_is_not_bound_reference.
Print Assumptions wildcard_preserves_explicit_policy.
Print Assumptions pattern_reference_retains_depth.
Print Assumptions out_of_scope_never_empty.
Print Assumptions bound_success_has_actual_index.
Print Assumptions binary_rejects_wrong_arity.
Print Assumptions checked_binary_preserves_exact_operands.
Print Assumptions slot_success_is_in_range.
Print Assumptions slot_out_of_range_rejected.
Print Assumptions formal_slot_order_is_reversed.
Print Assumptions shifted_outer_index_cannot_alias_local_slot.
Print Assumptions receive_preserves_roles.
Print Assumptions receive_connectives_exclude_pattern_and_condition.
Print Assumptions receive_free_information_includes_condition.
Print Assumptions trim_preserves_every_bit.
Print Assumptions shift_preserves_surviving_indices.
Print Assumptions ordinary_union_retains_trailing_false.
Print Assumptions scope_removal_trims_trailing_false.
Print Assumptions signed_integer_maximum_is_preserved.
Print Assumptions signed_integer_overflow_is_rejected.
Print Assumptions signed_integer_minimum_is_preserved.
Print Assumptions signed_integer_underflow_is_rejected.
Print Assumptions checked_reference_order.
Print Assumptions missing_reference_rejects.
Print Assumptions duplicate_reference_not_deduplicated.
Print Assumptions origin_changes_preserve_structure_and_obligations.
