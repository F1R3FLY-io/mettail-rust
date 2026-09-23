(** Exact relocation of ORIGINAL prefix.rs descriptor construction:
    PrefixArmDescriptor, UnifiedDescriptor, atomic_arm_descriptors, and
    same_category_led_left_bp. The existing atomic classifier is NOT repeated.
    Its Descriptor vocabulary and the existing FIRST quotation requests are
    imported. Literal payloads, native resolution, and quotation are opaque
    original callbacks; the native call must retain HomeCategory, not FirstSet.

    The old atomic row builder selects one of six quotation sites, delegates
    patterned rows once, or returns no rows for the five excluded variants.
    The shared row builder makes those same requests. Callback state and the
    exact ordered rows (including duplicate rows and absent/present guards)
    are retained when unchanged category/rule indices are attached.

    Generic unified descriptors have exactly the original nine constructors.
    Payload substitution changes only token payloads inside Atomic; all index,
    flag, category-name, guest-kind, and nested-opener fields remain structural.
    This is a representation law, not a new descriptor computation or parser.

    The led lookup still reads the rule-label spelling once and finds the FIRST
    operator whose label/result/source strings pass the original three &&
    predicates. It does not consult rule category or operator classification
    flags, terminal text, right binding power, or mixfix metadata.

    Natural indices below stand for existing representable u16/u8 values. No
    index truncation policy, grammar validity, native evaluator, token-equality,
    downstream pruning, bucket driver, transition-body, allocation, Drop/unwind,
    or whole-parser completeness claim is made. The callback functions are the
    same original operations in both runs, not arbitrary newly certified code.
*)
From Stdlib Require Import List String Bool Arith.
From PrattailWpdaRuntime Require Import OriginalFirstSetProjection NativeFirstDescriptorProjection.
Import ListNotations.
Set Implicit Arguments.

Module AtomicPrefixDescriptorProjection.
Module A := AtomicClassifierProjection.AtomicClassifierProjection.
Module F := OriginalFirstSetProjection.OriginalFirstSetProjection.
Module N := NativeFirstDescriptorProjection.NativeFirstDescriptorProjection.

Section Rows.
Context {LiteralPayload Pattern State : Type}.
Inductive Event := QuoteCall (site : F.Predicate)
  | PatternedCall (payload : LiteralPayload) (context : N.Context).
Record Callbacks := {
  quote : F.Predicate -> State -> (Pattern * option Pattern) * State;
  patterned : LiteralPayload -> N.Context -> State -> list (Pattern * option Pattern) * State
}.
Record Rows := { pairs : list (Pattern * option Pattern); row_state : State; trace : list Event }.

(** Original match body. The six singleton branches are intentionally explicit. *)
Definition source_rows (callbacks : Callbacks) (shape : @A.Descriptor LiteralPayload) state :=
  match shape with
  | A.LiteralInteger => let '(row_pair,next) := quote callbacks F.Integer state in
      {| pairs := [row_pair]; row_state := next; trace := [QuoteCall F.Integer] |}
  | A.LiteralBoolean => let '(row_pair,next) := quote callbacks F.Boolean state in
      {| pairs := [row_pair]; row_state := next; trace := [QuoteCall F.Boolean] |}
  | A.LiteralString => let '(row_pair,next) := quote callbacks F.StringToken state in
      {| pairs := [row_pair]; row_state := next; trace := [QuoteCall F.StringToken] |}
  | A.LiteralFloat => let '(row_pair,next) := quote callbacks F.Float state in
      {| pairs := [row_pair]; row_state := next; trace := [QuoteCall F.Float] |}
  | A.LiteralPatterned payload =>
      let '(rows,next) := patterned callbacks payload N.HomeCategory state in
      {| pairs := rows; row_state := next; trace := [PatternedCall payload N.HomeCategory] |}
  | A.TerminalKeyword text _ => let '(row_pair,next) := quote callbacks (F.Fixed text) state in
      {| pairs := [row_pair]; row_state := next; trace := [QuoteCall (F.Fixed text)] |}
  | A.VarRule _ => let '(row_pair,next) := quote callbacks F.Ident state in
      {| pairs := [row_pair]; row_state := next; trace := [QuoteCall F.Ident] |}
  | A.CrossCatProjection _ _ | A.CrossCatPrefixUnary _ _ _ | A.PrefixOperator _ _
  | A.NullaryLiteralRun _ _ _ | A.NonAtomic =>
      {| pairs := []; row_state := state; trace := [] |}
  end.

Definition singleton_quote (callbacks : Callbacks) site state :=
  let '(row_pair,next) := quote callbacks site state in
  {| pairs := [row_pair]; row_state := next; trace := [QuoteCall site] |}.
Definition shared_rows (callbacks : Callbacks) (shape : @A.Descriptor LiteralPayload) state :=
  match shape with
  | A.LiteralInteger => singleton_quote callbacks F.Integer state
  | A.LiteralBoolean => singleton_quote callbacks F.Boolean state
  | A.LiteralString => singleton_quote callbacks F.StringToken state
  | A.LiteralFloat => singleton_quote callbacks F.Float state
  | A.LiteralPatterned payload =>
      let '(rows,next) := patterned callbacks payload N.HomeCategory state in
      {| pairs := rows; row_state := next; trace := [PatternedCall payload N.HomeCategory] |}
  | A.TerminalKeyword text _ => singleton_quote callbacks (F.Fixed text) state
  | A.VarRule _ => singleton_quote callbacks F.Ident state
  | A.CrossCatProjection _ _ | A.CrossCatPrefixUnary _ _ _ | A.PrefixOperator _ _
  | A.NullaryLiteralRun _ _ _ | A.NonAtomic =>
      {| pairs := []; row_state := state; trace := [] |}
  end.
Theorem original_callback_rows_and_trace : forall callbacks shape state,
  shared_rows callbacks shape state = source_rows callbacks shape state.
Proof. intros; destruct shape; reflexivity. Qed.

Definition excluded (shape : @A.Descriptor LiteralPayload) := match shape with
| A.CrossCatProjection _ _ | A.CrossCatPrefixUnary _ _ _ | A.PrefixOperator _ _
| A.NullaryLiteralRun _ _ _ | A.NonAtomic => true | _ => false end.
Theorem excluded_variants_do_no_callback_work : forall callbacks shape state,
  excluded shape = true ->
  shared_rows callbacks shape state = {| pairs := []; row_state := state; trace := [] |}.
Proof. intros; destruct shape; cbn in H; try discriminate; reflexivity. Qed.
Theorem patterned_uses_home_once : forall callbacks payload state rows next,
  patterned callbacks payload N.HomeCategory state = (rows,next) ->
  shared_rows callbacks (A.LiteralPatterned payload) state =
  {| pairs := rows; row_state := next; trace := [PatternedCall payload N.HomeCategory] |}.
Proof. intros; cbn; rewrite H; reflexivity. Qed.
End Rows.

Record AtomicRow (P : Type) := {
  pattern : P; guard : option P; rule_index : nat; category_index : nat
}.
Definition attach {P} category rule (pair : P * option P) :=
 {| pattern := fst pair; guard := snd pair; rule_index := rule; category_index := category |}.
Definition attach_rows {P} category rule (rows : list (P * option P)) :=
  map (attach category rule) rows.
Definition detach {P} (row : AtomicRow P) := (pattern row, guard row).

Theorem attachment_preserves_length : forall P category rule (rows : list (P * option P)),
  List.length (attach_rows category rule rows) = List.length rows.
Proof. intros; apply length_map. Qed.
Theorem attachment_preserves_order_guards_and_duplicates : forall P category rule (rows : list (P * option P)),
  map detach (attach_rows category rule rows) = rows.
Proof. intros; induction rows as [|[p g] rest IH]; [reflexivity|].
  change ((p,g) :: map detach (attach_rows category rule rest) = (p,g) :: rest).
  rewrite IH; reflexivity. Qed.
Theorem attachment_preserves_indices : forall P category rule (rows : list (P * option P)) row,
  In row (attach_rows category rule rows) ->
  rule_index row = rule /\ category_index row = category.
Proof. intros; apply in_map_iff in H; destruct H as [[p g] [E _]]; subst row; cbn; auto. Qed.
Theorem original_descriptor_rows : forall L P S (callbacks : @Callbacks L P S) shape state category rule,
  attach_rows category rule (pairs (shared_rows callbacks shape state)) =
  attach_rows category rule (pairs (source_rows callbacks shape state)).
Proof. intros; rewrite original_callback_rows_and_trace; reflexivity. Qed.

(** Same nine payload constructors, not new dispatch instructions. *)
Inductive Unified (P : Type) :=
| CrossCatLhs (source : nat) (sigil : bool)
| Atomic (row : AtomicRow P)
| BinderPrefix (rule body : nat)
| LeadingCategory (rule source : nat)
| LeadingTokenKindCapture (rule body : nat) (kind : string)
| LeadingGuestBody (rule body : nat) (open : string) (nested : list string) (close : string)
| CrossCatPrefixUnary (rule source operand_bp : nat)
| CrossCatProjection (rule source : nat)
| NullaryLiteralRun (rule : nat).
Arguments CrossCatLhs {P}.
Arguments Atomic {P}.
Arguments BinderPrefix {P}.
Arguments LeadingCategory {P}.
Arguments LeadingTokenKindCapture {P}.
Arguments LeadingGuestBody {P}.
Arguments CrossCatPrefixUnary {P}.
Arguments CrossCatProjection {P}.
Arguments NullaryLiteralRun {P}.

Definition map_atomic {P Q} (f : P -> Q) (row : AtomicRow P) :=
 {| pattern := f (pattern row); guard := option_map f (guard row);
    rule_index := rule_index row; category_index := category_index row |}.
Definition map_unified {P Q} (f : P -> Q) (descriptor : Unified P) : Unified Q :=
  match descriptor with
  | CrossCatLhs source sigil => CrossCatLhs source sigil
  | Atomic row => Atomic (map_atomic f row)
  | BinderPrefix rule body => BinderPrefix rule body
  | LeadingCategory rule source => LeadingCategory rule source
  | LeadingTokenKindCapture rule body kind => LeadingTokenKindCapture rule body kind
  | LeadingGuestBody rule body open nested close => LeadingGuestBody rule body open nested close
  | CrossCatPrefixUnary rule source bp => CrossCatPrefixUnary rule source bp
  | CrossCatProjection rule source => CrossCatProjection rule source
  | NullaryLiteralRun rule => NullaryLiteralRun rule
  end.
Theorem descriptor_identity : forall P (descriptor : Unified P),
  map_unified (fun value => value) descriptor = descriptor.
Proof. intros; destruct descriptor; try reflexivity.
  destruct row as [p [g|] r c]; reflexivity. Qed.
Theorem descriptor_composition : forall P Q R (f : P -> Q) (g : Q -> R) descriptor,
  map_unified g (map_unified f descriptor) = map_unified (fun value => g (f value)) descriptor.
Proof. intros; destruct descriptor; try reflexivity.
  destruct row as [p [extra|] r c]; reflexivity. Qed.
Theorem guest_fields_are_not_token_payloads : forall P Q (f : P -> Q) rule body open nested close,
  map_unified f (LeadingGuestBody rule body open nested close) =
  LeadingGuestBody rule body open nested close.
Proof. reflexivity. Qed.

(** Original same-category table predicate and first-match traversal. *)
Record SourceRule := { label_spelling : string; label_identity : nat; ignored_rule_category : string }.
Record Operator := { label : string; result : string; category : string;
  left_bp : nat; ignored_payload : nat }.
Inductive LedEvent := LabelSpelling | OperatorLabel (index : nat)
  | OperatorResult (index : nat) | OperatorCategory (index : nat) | OperatorLeftBp (index : nat).
Definition matches_row target_label target_result index row :=
  if String.eqb (label row) target_label then
    if String.eqb (result row) target_result then
      (String.eqb (category row) (result row),
       [OperatorLabel index; OperatorResult index; OperatorCategory index])
    else (false,[OperatorLabel index; OperatorResult index])
  else (false,[OperatorLabel index]).
Fixpoint find_left_bp target_label target_result index rows := match rows with
| [] => (None,[])
| row :: rest => let '(found,events) := matches_row target_label target_result index row in
    if found then (Some (left_bp row), List.app events [OperatorLeftBp index])
    else let '(answer,more) := find_left_bp target_label target_result (S index) rest in
      (answer,List.app events more) end.
Definition source_led rule target rows :=
  let '(answer,events) := find_left_bp (label_spelling rule) target 0 rows in
  (answer,LabelSpelling :: events).
Definition shared_led target_label target rows := find_left_bp target_label target 0 rows.
Theorem led_label_projection_preserves_first_result_and_trace : forall rule target rows,
  source_led rule target rows =
  let '(answer,events) := shared_led (label_spelling rule) target rows in
  (answer,LabelSpelling :: events).
Proof. reflexivity. Qed.
Theorem matching_row_hides_the_entire_suffix : forall target_label target_result index row rest events,
  matches_row target_label target_result index row = (true,events) ->
  find_left_bp target_label target_result index (row :: rest) =
  (Some (left_bp row),List.app events [OperatorLeftBp index]).
Proof. intros; cbn; rewrite H; reflexivity. Qed.
Theorem mismatched_label_skips_later_fields : forall target_label target_result index row,
  String.eqb (label row) target_label = false ->
  matches_row target_label target_result index row = (false,[OperatorLabel index]).
Proof. intros; unfold matches_row; rewrite H; reflexivity. Qed.

Print Assumptions original_callback_rows_and_trace.
Print Assumptions excluded_variants_do_no_callback_work.
Print Assumptions patterned_uses_home_once.
Print Assumptions attachment_preserves_length.
Print Assumptions attachment_preserves_order_guards_and_duplicates.
Print Assumptions attachment_preserves_indices.
Print Assumptions original_descriptor_rows.
Print Assumptions descriptor_identity.
Print Assumptions descriptor_composition.
Print Assumptions guest_fields_are_not_token_payloads.
Print Assumptions led_label_projection_preserves_first_result_and_trace.
Print Assumptions matching_row_hides_the_entire_suffix.
Print Assumptions mismatched_label_skips_later_fields.
End AtomicPrefixDescriptorProjection.
