(** Exact descriptor derivation boundary for parikh_tables.rs (task 8512).
    The complete original file was read before writing this model.

    This is source/accessor substitution for the ORIGINAL algorithms, not a
    replacement Parikh analysis. In particular, suffixes OR every returned
    mask, without testing the returned nullable flag. Nullable rounds update
    the category map IN PLACE, and .any/.all short-circuit in source order.
    Must rounds likewise update in place; empty categories become zero.
    Every production-must call builds parameters BEFORE inspecting syntax.
    Table construction instead skips absent/empty syntax BEFORE parameters.
    Optional parameters are ignored, not recursively flattened. Abstraction
    and MultiAbstraction contribute only their body's arrow-to-Base category.

    Handles below denote original borrowed rule/parameter/type/expression
    occurrences. Stores are shallow field observations, not reconstructed ASTs.
    Name strings denote exact existing to_string results. Source and accessor
    parameter/expression implementations are separate; ordered fold and round
    congruences lift their proved correspondence to the original driver.

    Observations expose rule/parameter/type/expression reads and classifier
    calls, plus category-row indexing and map-update order. They do not claim
    allocation, clone/drop, formatting, or arbitrary callback equivalence.
    Infix classification is the existing normalized classifier, an explicit
    callback boundary; its invocation order is modeled, not reimplemented.

    Masks use binary naturals for u128 bit operations, on the original domain
    of bits 0..127 and masks below 2^128. Rule/category casts reuse the exact
    modulo-u16 model; positions cast modulo256. Slice indices fit usize.
    Missing per_cat rows are faults; fuel exhaustion is a suspended round
    prefix, NEVER a successful fixed point. No all-input termination, abstract
    lattice correctness, dynamic admission, or Rust extraction is asserted.

    ParikhObligationGate is imported as the existing downstream semantic
    boundary. Its must_consume_sound/top_frame_refutation_sound require the
    defining must properties; they DO NOT prove these concrete fixpoint loops.
    This file proves relocation equality, and does not silently supply those
    semantic premises. CategoryCensusProjection supplies the already checked
    exact category/rule cast operation.
*)
From Stdlib Require Import List String Bool Arith NArith Lia.
From PrattailWpdaRuntime Require Import ParikhObligationGate CategoryCensusProjection.
Import ListNotations.
Set Implicit Arguments.

Module ParikhDescriptorProjection.
Module C := CategoryCensusProjection.CategoryCensusProjection.
(* ParikhObligationGate exports a semantic relation named S. *)
Local Notation S := Datatypes.S.
Definition Mask := N.
Definition NameMap (A : Type) := list (string * A).
Fixpoint get {A} (name : string) (entries : NameMap A) : option A := match entries with
| [] => None | (key, value) :: rest => if String.eqb name key then Some value else get name rest end.
Definition default {A} (fallback : A) value := match value with Some x => x | None => fallback end.
Definition put {A} name (value : A) (entries : NameMap A) := (name, value) :: entries.

Inductive SourceType := SBase (name : string) | SArrow (domain codomain : nat) | SOtherType (tag : nat).
Inductive TypeView := VBase (name : string) | VArrow (domain codomain : nat) | VOtherType (tag : nat).
Inductive SourceParam := SSimple (name : string) (ty : nat)
| SAbstraction (binder body : string) (ty : nat)
| SMultiAbstraction (binder body : string) (ty : nat)
| SGuard (name : string) | SOptional (children : list nat).
Inductive ParamView := VSimple (name : string) (ty : nat)
| VAbstraction (binder body : string) (ty : nat)
| VMultiAbstraction (binder body : string) (ty : nat)
| VGuard (name : string) | VOptional (children : list nat).
Inductive Op := Opt | Sep | MapOp | Zip | VarOp.
Inductive SourceExpr := SLiteral (text : string)
| STokenKind (name : string) (other_fields : nat)
| SGuestBody (open : string) (other_fields : nat)
| SParam (name : string) | SOp (op : Op) (other_fields : nat).
Inductive ExprView := VLiteral (text : string)
| VTokenKind (name : string) (other_fields : nat)
| VGuestBody (open : string) (other_fields : nat)
| VParam (name : string) | VOp (op : Op) (other_fields : nat).
Record SourceRule := { source_params : option (list nat); source_syntax : option (list nat) }.
Record InfixInfo := { cross_category : bool; operand_category : string;
  result_category : string; terminal : string }.
Record Source := {
  source_type : nat -> SourceType; source_param : nat -> SourceParam;
  source_expr : nat -> SourceExpr; source_rule : nat -> SourceRule;
  original_classify : nat -> option InfixInfo
}.
Record Reader := {
  read_type : nat -> TypeView; read_param : nat -> ParamView;
  read_expr : nat -> ExprView; read_params : nat -> option (list nat);
  read_syntax : nat -> option (list nat); classify : nat -> option InfixInfo
}.
Definition project_type ty := match ty with
| SBase name => VBase name | SArrow d c => VArrow d c | SOtherType tag => VOtherType tag end.
Definition project_param p := match p with
| SSimple n t => VSimple n t | SAbstraction b n t => VAbstraction b n t
| SMultiAbstraction b n t => VMultiAbstraction b n t | SGuard n => VGuard n
| SOptional children => VOptional children end.
Definition project_expr e := match e with
| SLiteral t => VLiteral t | STokenKind n o => VTokenKind n o
| SGuestBody n o => VGuestBody n o | SParam n => VParam n | SOp op o => VOp op o end.
Definition project s :=
 {| read_type := fun h => project_type (source_type s h);
    read_param := fun h => project_param (source_param s h);
    read_expr := fun h => project_expr (source_expr s h);
    read_params := fun h => source_params (source_rule s h);
    read_syntax := fun h => source_syntax (source_rule s h);
    classify := original_classify s |}.

Inductive Observation := ReadParams (rule : nat) | ReadSyntax (rule : nat)
| ReadParam (param : nat) | ReadType (ty : nat) | ReadExpr (expr : nat)
| Classify (rule : nat) | NullableRow (index : nat) | MustRow (index : nat)
| SetNullable (category : string) | SetMust (category : string) (mask : Mask).
Definition observed {A} (value : A) (trace : list Observation) := (value, trace).
Definition prefix {A} trace (answer : A * list Observation) :=
  (fst answer, (trace ++ snd answer)%list).

Definition source_base s h := (match source_type s h with SBase n => Some n | _ => None end, [ReadType h]).
Definition shared_base a h := (match read_type a h with VBase n => Some n | _ => None end, [ReadType h]).
Definition source_codomain s h := match source_type s h with
| SArrow _ c => prefix [ReadType h] (source_base s c)
| _ => (None, [ReadType h]) end.
Definition shared_codomain a h := match read_type a h with
| VArrow _ c => prefix [ReadType h] (shared_base a c)
| _ => (None, [ReadType h]) end.
Lemma base_substitution : forall s h, shared_base (project s) h = source_base s h.
Proof. intros; unfold shared_base, source_base; cbn; destruct (source_type s h); reflexivity. Qed.
Lemma codomain_substitution : forall s h, shared_codomain (project s) h = source_codomain s h.
Proof.
  intros; unfold shared_codomain, source_codomain; cbn [project read_type].
  destruct (source_type s h); cbn [project_type]; try reflexivity.
  rewrite base_substitution; reflexivity.
Qed.
Definition named_category (name : string) (answer : option string * list Observation) :=
  (option_map (fun cat => (name, cat)) (fst answer), snd answer).
Definition source_parameter s h := prefix [ReadParam h]
  (match source_param s h with
  | SSimple name ty => named_category name (source_base s ty)
  | SAbstraction _ body ty | SMultiAbstraction _ body ty => named_category body (source_codomain s ty)
  | SGuard _ | SOptional _ => (None, []) end).
Definition shared_parameter a h := prefix [ReadParam h]
  (match read_param a h with
  | VSimple name ty => named_category name (shared_base a ty)
  | VAbstraction _ body ty | VMultiAbstraction _ body ty => named_category body (shared_codomain a ty)
  | VGuard _ | VOptional _ => (None, []) end).
Theorem parameter_substitution : forall s h,
  shared_parameter (project s) h = source_parameter s h.
Proof.
  intros; unfold shared_parameter, source_parameter; cbn [project read_param].
  destruct (source_param s h); cbn [project_param]; try rewrite base_substitution;
    try rewrite codomain_substitution; reflexivity.
Qed.

Fixpoint parameter_scan (callback : nat -> option (string * string) * list Observation)
    (handles : list nat) entries : NameMap string * list Observation :=
  match handles with
  | [] => (entries, [])
  | h :: rest => let '(entry, trace) := callback h in
      prefix trace (parameter_scan callback rest
        (match entry with Some (name, cat) => put name cat entries | None => entries end)) end.
Definition parameters params_field parameter_callback rule := prefix [ReadParams rule]
  (match params_field rule with
  | None => ([], []) | Some handles => parameter_scan parameter_callback handles [] end).
Definition source_parameters s := parameters (fun r => source_params (source_rule s r)) (source_parameter s).
Definition shared_parameters a := parameters (read_params a) (shared_parameter a).
Lemma parameter_scan_substitution : forall source_callback shared_callback,
  (forall h, shared_callback h = source_callback h) -> forall handles entries,
  parameter_scan shared_callback handles entries = parameter_scan source_callback handles entries.
Proof.
  intros source_callback shared_callback H handles; induction handles; intros entries; cbn; [reflexivity|].
  rewrite H; destruct (source_callback a) as [entry trace]. rewrite IHhandles; reflexivity.
Qed.
Theorem parameter_map_substitution : forall s rule,
  shared_parameters (project s) rule = source_parameters s rule.
Proof.
  intros; unfold shared_parameters, source_parameters, parameters; cbn.
  destruct (source_params (source_rule s rule)); [|reflexivity].
  rewrite (parameter_scan_substitution (source_parameter s) (shared_parameter (project s))
    (parameter_substitution s)); reflexivity.
Qed.

Record Alphabet := { trigger_bits : NameMap nat; coarse_bit : nat }.
Definition singleton bit : Mask := N.shiftl 1 (N.of_nat bit).
Definition class_of alpha text := default (coarse_bit alpha) (get text (trigger_bits alpha)).
Definition mask_of alpha text := singleton (class_of alpha text).
Definition top alpha : Mask :=
  if Nat.leb 128 (S (coarse_bit alpha)) then N.pred (singleton 128)
  else N.pred (singleton (S (coarse_bit alpha))).
Definition parameter_obligation name params must nullable : bool * Mask :=
  match get name params with
  | None => (true, 0%N)
  | Some cat => (default false (get cat nullable), default 0%N (get cat must)) end.
Definition source_expression s h params must nullable alpha :=
  (match source_expr s h with
  | SLiteral text | STokenKind text _ | SGuestBody text _ => (false, mask_of alpha text)
  | SParam name => parameter_obligation name params must nullable
  | SOp _ _ => (true, 0%N) end, [ReadExpr h]).
Definition shared_expression a h params must nullable alpha :=
  (match read_expr a h with
  | VLiteral text | VTokenKind text _ | VGuestBody text _ => (false, mask_of alpha text)
  | VParam name => parameter_obligation name params must nullable
  | VOp _ _ => (true, 0%N) end, [ReadExpr h]).
Theorem expression_substitution : forall s h params must nullable alpha,
  shared_expression (project s) h params must nullable alpha =
  source_expression s h params must nullable alpha.
Proof. intros; unfold shared_expression, source_expression; cbn; destruct (source_expr s h); reflexivity. Qed.

(** The accumulator and unconditional OR are the source loop, including on
    abstract environments with nullable=true and a nonzero category mask. *)
Fixpoint suffix_scan (callback : nat -> (bool * Mask) * list Observation)
    handles (acc : Mask) : Mask * list Observation := match handles with
| [] => (acc, [])
| h :: rest => let '(answer, trace) := callback h in
    prefix trace (suffix_scan callback rest (N.lor acc (snd answer))) end.
Fixpoint all_nullable (callback : nat -> (bool * Mask) * list Observation)
    handles : bool * list Observation := match handles with
| [] => (true, [])
| h :: rest => let '(answer, trace) := callback h in
    if fst answer then prefix trace (all_nullable callback rest) else (false, trace) end.
Lemma suffix_scan_substitution : forall source_callback shared_callback,
  (forall h, shared_callback h = source_callback h) -> forall handles acc,
  suffix_scan shared_callback handles acc = suffix_scan source_callback handles acc.
Proof.
  intros old new H handles; induction handles; intros acc; cbn; [reflexivity|].
  rewrite H; destruct (old a) as [answer trace]; rewrite IHhandles; reflexivity.
Qed.
Lemma all_nullable_substitution : forall source_callback shared_callback,
  (forall h, shared_callback h = source_callback h) -> forall handles,
  all_nullable shared_callback handles = all_nullable source_callback handles.
Proof.
  intros old new H handles; induction handles; cbn; [reflexivity|].
  rewrite H; destruct (old a) as [[nul mask] trace]; cbn.
  destruct nul; [rewrite IHhandles|]; reflexivity.
Qed.
Definition ParamCallback := nat -> NameMap string * list Observation.
Definition ExprCallback := nat -> NameMap string -> NameMap Mask -> NameMap bool -> Alphabet ->
  (bool * Mask) * list Observation.
Definition production_must syntax_field (parameter_callback : ParamCallback)
    (expression_callback : ExprCallback) rule must nullable alpha :=
  let '(params, trace) := parameter_callback rule in
  prefix (trace ++ [ReadSyntax rule])%list
    (match syntax_field rule with
    | Some (head :: rest) => suffix_scan
        (fun h => expression_callback h params must nullable alpha) (head :: rest) 0%N
    | _ => (singleton (coarse_bit alpha), []) end).
Definition production_nullable syntax_field (parameter_callback : ParamCallback)
    (expression_callback : ExprCallback) rule nullable alpha :=
  let '(params, trace) := parameter_callback rule in
  prefix (trace ++ [ReadSyntax rule])%list
    (match syntax_field rule with
    | Some (head :: rest) => all_nullable
        (fun h => expression_callback h params [] nullable alpha) (head :: rest)
    | _ => (false, []) end).
Definition source_must s := production_must
  (fun r => source_syntax (source_rule s r)) (source_parameters s) (source_expression s).
Definition shared_must a := production_must (read_syntax a) (shared_parameters a) (shared_expression a).
Definition source_nullable s := production_nullable
  (fun r => source_syntax (source_rule s r)) (source_parameters s) (source_expression s).
Definition shared_nullable a := production_nullable (read_syntax a) (shared_parameters a) (shared_expression a).
Theorem production_must_substitution : forall s rule must nullable alpha,
  shared_must (project s) rule must nullable alpha = source_must s rule must nullable alpha.
Proof.
  intros; unfold shared_must, source_must, production_must.
  rewrite parameter_map_substitution.
  destruct (source_parameters s rule) as [params trace]; cbn [project read_syntax].
  destruct (source_syntax (source_rule s rule)) as [[|h rest]|]; try reflexivity.
  f_equal. apply suffix_scan_substitution. intros; apply expression_substitution.
Qed.
Theorem production_nullable_substitution : forall s rule nullable alpha,
  shared_nullable (project s) rule nullable alpha = source_nullable s rule nullable alpha.
Proof.
  intros; unfold shared_nullable, source_nullable, production_nullable.
  rewrite parameter_map_substitution.
  destruct (source_parameters s rule) as [params trace]; cbn [project read_syntax].
  destruct (source_syntax (source_rule s rule)) as [[|h rest]|]; try reflexivity.
  f_equal. apply all_nullable_substitution. intros; apply expression_substitution.
Qed.

(** Concrete .any and intersection loops. The parameter callback is executed
    anew for EACH visited rule in EACH round, as in the original code. *)
Fixpoint any_rule (callback : nat -> bool * list Observation) rules : bool * list Observation := match rules with
| [] => (false, [])
| rule :: rest => let '(nul, trace) := callback rule in
    if nul then (true, trace) else prefix trace (any_rule callback rest) end.
Fixpoint intersect_rules (callback : nat -> Mask * list Observation)
    rules (acc : Mask) : Mask * list Observation := match rules with
| [] => (acc, [])
| rule :: rest => let '(mask, trace) := callback rule in
    prefix trace (intersect_rules callback rest (N.land acc mask)) end.
Lemma any_rule_substitution : forall old new,
  (forall rule, new rule = old rule) -> forall rules, any_rule new rules = any_rule old rules.
Proof.
  intros old new H rules; induction rules; cbn; [reflexivity|].
  rewrite H; destruct (old a) as [nul trace]; destruct nul; [|rewrite IHrules]; reflexivity.
Qed.
Lemma intersect_rules_substitution : forall old new,
  (forall rule, new rule = old rule) -> forall rules acc,
  intersect_rules new rules acc = intersect_rules old rules acc.
Proof.
  intros old new H rules; induction rules; intros acc; cbn; [reflexivity|].
  rewrite H; destruct (old a) as [mask trace]; rewrite IHrules; reflexivity.
Qed.

Record AnalysisState := {
  nullables : NameMap bool; obligations : NameMap Mask; analysis_trace : list Observation
}.
Definition state nullable must trace := {| nullables := nullable; obligations := must; analysis_trace := trace |}.
Inductive RoundOutcome := RoundDone (changed : bool) (final : AnalysisState)
| MissingRow (index : nat) (partial : AnalysisState).
Fixpoint nullable_round callback rows cats index changed st := match cats with
| [] => RoundDone changed st
| cat :: rest =>
    let visited := state (nullables st) (obligations st)
      (analysis_trace st ++ [NullableRow index])%list in
    match nth_error rows index with
    | None => MissingRow index visited
    | Some rules =>
      let '(answer, trace) := any_rule (fun rule => callback rule (nullables st)) rules in
      let ops := (analysis_trace visited ++ trace)%list in
      if answer && negb (default false (get cat (nullables st))) then
        nullable_round callback rows rest (S index) true
          (state (put cat true (nullables st)) (obligations st) (ops ++ [SetNullable cat])%list)
      else nullable_round callback rows rest (S index) changed
          (state (nullables st) (obligations st) ops)
    end end.
Fixpoint must_round callback rows cats index changed alpha st := match cats with
| [] => RoundDone changed st
| cat :: rest =>
    let visited := state (nullables st) (obligations st)
      (analysis_trace st ++ [MustRow index])%list in
    match nth_error rows index with
    | None => MissingRow index visited
    | Some rules =>
      let '(mask, trace) := match rules with
        | [] => (0%N, [])
        | _ :: _ => intersect_rules
            (fun rule => callback rule (obligations st) (nullables st)) rules (top alpha) end in
      let previous := default (match rules with [] => 0%N | _ => top alpha end) (get cat (obligations st)) in
      let ops := (analysis_trace visited ++ trace)%list in
      if N.eqb mask previous then
        must_round callback rows rest (S index) changed alpha (state (nullables st) (obligations st) ops)
      else must_round callback rows rest (S index) true alpha
        (state (nullables st) (put cat mask (obligations st)) (ops ++ [SetMust cat mask])%list)
    end end.
Lemma nullable_round_substitution : forall old new,
  (forall rule nullable, new rule nullable = old rule nullable) ->
  forall rows cats index changed st,
  nullable_round new rows cats index changed st = nullable_round old rows cats index changed st.
Proof.
  intros old new H rows cats; induction cats; intros index changed st; cbn; [reflexivity|].
  destruct (nth_error rows index) as [rules|]; [|reflexivity].
  rewrite (any_rule_substitution (fun r => old r (nullables st))
    (fun r => new r (nullables st)) (fun r => H r (nullables st))).
  destruct (any_rule (fun r => old r (nullables st)) rules) as [answer trace].
  destruct (answer && negb (default false (get a (nullables st)))); apply IHcats.
Qed.
Lemma must_round_substitution : forall old new,
  (forall rule must nullable, new rule must nullable = old rule must nullable) ->
  forall rows cats index changed alpha st,
  must_round new rows cats index changed alpha st = must_round old rows cats index changed alpha st.
Proof.
  intros old new H rows cats; induction cats; intros index changed alpha st; cbn; [reflexivity|].
  destruct (nth_error rows index) as [rules|]; [|reflexivity].
  assert (E : (match rules with [] => (0%N, []) | _ :: _ =>
    intersect_rules (fun r => new r (obligations st) (nullables st)) rules (top alpha) end) =
    (match rules with [] => (0%N, []) | _ :: _ =>
    intersect_rules (fun r => old r (obligations st) (nullables st)) rules (top alpha) end)).
  { destruct rules; [reflexivity|]. apply intersect_rules_substitution; intros; apply H. }
  rewrite E.
  destruct (match rules with [] => (0%N, []) | _ :: _ =>
    intersect_rules (fun r => old r (obligations st) (nullables st)) rules (top alpha) end) as [mask trace].
  destruct (N.eqb mask (default (match rules with [] => 0%N | _ => top alpha end)
    (get a (obligations st)))); apply IHcats.
Qed.

Inductive FixedOutcome := Converged (final : AnalysisState)
| Suspended (partial : AnalysisState) | IndexFault (index : nat) (partial : AnalysisState).
Fixpoint iterate_rounds fuel round st := match fuel with
| 0 => Suspended st
| S remaining => match round st with
    | MissingRow i partial => IndexFault i partial
    | RoundDone false final => Converged final
    | RoundDone true next => iterate_rounds remaining round next end end.
Lemma finite_round_iteration_substitution : forall old new,
  (forall st, new st = old st) -> forall fuel st,
  iterate_rounds fuel new st = iterate_rounds fuel old st.
Proof.
  intros old new H fuel; induction fuel; intros st; cbn; [reflexivity|].
  rewrite H; destruct (old st) as [[|] final|i partial]; try reflexivity; apply IHfuel.
Qed.
Definition seed {A} cats (value : A) := fold_left (fun entries cat => put cat value entries) cats [].
Definition analyze nullable_callback must_callback nfuel mfuel rows cats alpha :=
  match iterate_rounds nfuel (nullable_round nullable_callback rows cats 0 false)
    (state (seed cats false) [] []) with
  | Converged nullable_state => iterate_rounds mfuel
      (must_round must_callback rows cats 0 false alpha)
      (state (nullables nullable_state) (seed cats (top alpha)) (analysis_trace nullable_state))
  | other => other end.
Theorem finite_in_place_analysis_substitution : forall s nfuel mfuel rows cats alpha,
  analyze (fun r n => shared_nullable (project s) r n alpha)
    (fun r m n => shared_must (project s) r m n alpha) nfuel mfuel rows cats alpha =
  analyze (fun r n => source_nullable s r n alpha)
    (fun r m n => source_must s r m n alpha) nfuel mfuel rows cats alpha.
Proof.
  intros; unfold analyze.
  erewrite finite_round_iteration_substitution.
  2: { intros; apply nullable_round_substitution; intros; apply production_nullable_substitution. }
  destruct (iterate_rounds nfuel
    (nullable_round (fun r n => source_nullable s r n alpha) rows cats 0 false)
    (state (seed cats false) [] [])); try reflexivity.
  apply finite_round_iteration_substitution; intros.
  apply must_round_substitution; intros; apply production_must_substitution.
Qed.

(** The original alphabet: classify every authored rule; retain eligible
    trigger text in lexical BTreeSet order; visit ALL triggers, assigning only
    while next<127. Later unassigned texts use the coarse fallback. Strings
    here represent Rust string bytes, so their lexical order is byte order. *)
Fixpoint insert_trigger text triggers := match triggers with
| [] => [text]
| head :: rest => match String.compare text head with
    | Eq => triggers | Lt => text :: triggers | Gt => head :: insert_trigger text rest end end.
Fixpoint trigger_scan callback rules triggers : list string * list Observation := match rules with
| [] => (triggers, [])
| rule :: rest => prefix [Classify rule]
    (trigger_scan callback rest
      (match callback rule with
      | Some info => if cross_category info && negb (String.eqb (operand_category info) (result_category info))
          then insert_trigger (terminal info) triggers else triggers
      | None => triggers end)) end.
Fixpoint assign_bits triggers next : NameMap nat * nat := match triggers with
| [] => ([], next)
| text :: rest => if Nat.ltb next 127 then
    let '(rows, coarse) := assign_bits rest (S next) in ((text, next) :: rows, coarse)
    else assign_bits rest next end.
Definition build_alphabet callback rules :=
  let '(triggers, trace) := trigger_scan callback rules [] in
  let '(rows, coarse) := assign_bits triggers 0 in
  ({| trigger_bits := rows; coarse_bit := coarse |}, trace).
Lemma trigger_scan_substitution : forall old new,
  (forall rule, new rule = old rule) -> forall rules triggers,
  trigger_scan new rules triggers = trigger_scan old rules triggers.
Proof.
  intros old new H rules; induction rules; intros triggers; cbn; [reflexivity|].
  rewrite H, IHrules; reflexivity.
Qed.
Theorem alphabet_callback_substitution : forall old new,
  (forall rule, new rule = old rule) -> forall rules,
  build_alphabet new rules = build_alphabet old rules.
Proof. intros; unfold build_alphabet; rewrite (trigger_scan_substitution old new H); reflexivity. Qed.
Theorem assigned_bits_are_consecutive : forall triggers next,
  map snd (fst (assign_bits triggers next)) =
  seq next (List.length (fst (assign_bits triggers next))).
Proof.
  induction triggers as [|text rest IH]; intros next; cbn [assign_bits]; [reflexivity|].
  destruct (Nat.ltb next 127); [|apply IH].
  specialize (IH (S next)). destruct (assign_bits rest (S next)) as [rows coarse].
  cbn in *; rewrite IH; reflexivity.
Qed.
(** At next=0, consecutive distinct bit indices imply that sorting the HashMap
    entries by (bit,text), as the original quote emitter does, yields exactly
    this assignment order. No HashMap iteration order is assumed. *)
Theorem assigned_coarse_bit_stays_below_128 : forall triggers next,
  next <= 127 -> snd (assign_bits triggers next) <= 127.
Proof.
  induction triggers as [|text rest IH]; intros next H; cbn [assign_bits]; [exact H|].
  destruct (Nat.ltb next 127) eqn:E; [|apply IH; exact H].
  apply Nat.ltb_lt in E.
  pose proof (IH (S next)) as Hnext.
  destruct (assign_bits rest (S next)) as [rows coarse]; cbn in *.
  apply Hnext; lia.
Qed.

(** Exact nonzero table map, sorted by the original (u16,u16,u8) tuple key.
    Equality replaces the previous row; zero masks do not insert OR remove.
    A wrapped position may therefore retain an earlier nonzero row if its
    later colliding position has zero mask. This is the existing behavior. *)
Definition Key := (nat * nat * nat)%type.
Definition key_compare (left right : Key) :=
  let '(lc, lr, lp) := left in let '(rc, rr, rp) := right in
  match Nat.compare lc rc with
  | Eq => match Nat.compare lr rr with Eq => Nat.compare lp rp | other => other end
  | other => other end.
Fixpoint insert_row key mask (rows : list (Key * Mask)) := match rows with
| [] => [(key, mask)]
| (other, value) :: rest => match key_compare key other with
    | Eq => (key, mask) :: rest
    | Lt => (key, mask) :: rows
    | Gt => (other, value) :: insert_row key mask rest end end.
Definition row_key cat rule pos : Key := (C.cast_u16 cat, C.cast_u16 rule, pos mod 256).
Record TableState := { must_entries : list (Key * Mask); table_trace : list Observation }.
Definition table_state rows trace := {| must_entries := rows; table_trace := trace |}.
Fixpoint position_rows (expression_callback : ExprCallback)
    handles positions params must nullable alpha cat rule st :=
  match positions with
  | [] => st
  | pos :: rest =>
    let '(mask, trace) := suffix_scan
      (fun h => expression_callback h params must nullable alpha) (skipn pos handles) 0%N in
    position_rows expression_callback handles rest params must nullable alpha cat rule
      (table_state (if N.eqb mask 0 then must_entries st
        else insert_row (row_key cat rule pos) mask (must_entries st))
        (table_trace st ++ trace)%list) end.
Definition rule_rows syntax_field (parameter_callback : ParamCallback)
    (expression_callback : ExprCallback) handle must nullable alpha cat rule st :=
  let visited := table_state (must_entries st) (table_trace st ++ [ReadSyntax handle])%list in
  match syntax_field handle with
  | None | Some [] => visited
  | Some (head :: rest) =>
    let '(params, trace) := parameter_callback handle in
    position_rows expression_callback (head :: rest) (seq 0 (List.length (head :: rest)))
      params must nullable alpha cat rule
      (table_state (must_entries visited) (table_trace visited ++ trace)%list) end.
Fixpoint rules_rows (callback : nat -> nat -> nat -> TableState -> TableState)
    cat rule rules st := match rules with
| [] => st
| handle :: rest => rules_rows callback cat (S rule) rest (callback handle cat rule st) end.
Fixpoint categories_rows callback cat rows st := match rows with
| [] => st
| rules :: rest => categories_rows callback (S cat) rest (rules_rows callback cat 0 rules st) end.
Lemma position_rows_substitution : forall old new,
  (forall h p m n a, new h p m n a = old h p m n a) ->
  forall handles positions params must nullable alpha cat rule st,
  position_rows new handles positions params must nullable alpha cat rule st =
  position_rows old handles positions params must nullable alpha cat rule st.
Proof.
  intros old new H handles positions; induction positions; intros params must nullable alpha cat rule st;
    cbn; [reflexivity|].
  rewrite (suffix_scan_substitution (fun h => old h params must nullable alpha)
    (fun h => new h params must nullable alpha) (fun h => H h params must nullable alpha)).
  destruct (suffix_scan (fun h => old h params must nullable alpha) (skipn a handles) 0%N).
  apply IHpositions.
Qed.
Definition source_rule_rows s := rule_rows
  (fun r => source_syntax (source_rule s r)) (source_parameters s) (source_expression s).
Definition shared_rule_rows a := rule_rows (read_syntax a) (shared_parameters a) (shared_expression a).
Lemma rule_rows_substitution : forall s handle must nullable alpha cat rule st,
  shared_rule_rows (project s) handle must nullable alpha cat rule st =
  source_rule_rows s handle must nullable alpha cat rule st.
Proof.
  intros; unfold shared_rule_rows, source_rule_rows, rule_rows; cbn [project read_syntax].
  destruct (source_syntax (source_rule s handle)) as [[|h rest]|]; try reflexivity.
  rewrite parameter_map_substitution. destruct (source_parameters s handle) as [params trace].
  apply position_rows_substitution; intros; apply expression_substitution.
Qed.
Lemma rules_rows_substitution : forall old new,
  (forall h cat rule st, new h cat rule st = old h cat rule st) ->
  forall cat rule rules st, rules_rows new cat rule rules st = rules_rows old cat rule rules st.
Proof.
  intros old new H cat rule rules; revert rule; induction rules; intros rule st; cbn; [reflexivity|].
  rewrite H; apply IHrules.
Qed.
Lemma categories_rows_substitution : forall old new,
  (forall h cat rule st, new h cat rule st = old h cat rule st) ->
  forall cat rows st, categories_rows new cat rows st = categories_rows old cat rows st.
Proof.
  intros old new H cat rows; revert cat; induction rows; intros cat st; cbn; [reflexivity|].
  rewrite (rules_rows_substitution old new H); apply IHrows.
Qed.
Theorem complete_suffix_rows_substitution : forall s rows must nullable alpha,
  categories_rows (fun h c r => shared_rule_rows (project s) h must nullable alpha c r)
    0 rows (table_state [] []) =
  categories_rows (fun h c r => source_rule_rows s h must nullable alpha c r)
    0 rows (table_state [] []).
Proof. intros; apply categories_rows_substitution; intros; apply rule_rows_substitution. Qed.

Record Descriptors := { alphabet : Alphabet; suffix_rows : list (Key * Mask);
  descriptor_trace : list Observation }.
Inductive DescriptorOutcome := DescriptorsReady (value : Descriptors)
| AnalysisIncomplete (alpha : Alphabet) (prefix_trace : list Observation) (outcome : FixedOutcome).
Definition descriptor_driver classify_callback nullable_callback must_callback rows_callback
    authored rows cats nfuel mfuel :=
  let '(alpha, alpha_trace) := build_alphabet classify_callback authored in
  match analyze (fun r n => nullable_callback r n alpha)
    (fun r m n => must_callback r m n alpha) nfuel mfuel rows cats alpha with
  | Converged final =>
    let table := categories_rows
      (fun h c r => rows_callback h (obligations final) (nullables final) alpha c r)
      0 rows (table_state [] []) in
    DescriptorsReady {| alphabet := alpha; suffix_rows := must_entries table;
      descriptor_trace := (alpha_trace ++ analysis_trace final ++ table_trace table)%list |}
  | other => AnalysisIncomplete alpha alpha_trace other end.
Definition source_driver s := descriptor_driver (original_classify s) (source_nullable s)
  (source_must s) (source_rule_rows s).
Definition shared_driver a := descriptor_driver (classify a) (shared_nullable a)
  (shared_must a) (shared_rule_rows a).
Theorem original_descriptor_driver_substitution : forall s authored rows cats nfuel mfuel,
  shared_driver (project s) authored rows cats nfuel mfuel =
  source_driver s authored rows cats nfuel mfuel.
Proof.
  intros; unfold shared_driver, source_driver, descriptor_driver; cbn [project classify].
  destruct (build_alphabet (original_classify s) authored) as [alpha trace].
  rewrite finite_in_place_analysis_substitution.
  destruct (analyze (fun r n => source_nullable s r n alpha)
    (fun r m n => source_must s r m n alpha) nfuel mfuel rows cats alpha); try reflexivity.
  rewrite complete_suffix_rows_substitution; reflexivity.
Qed.

(** Scoped behavioral laws and witnesses guard against plausible but DIFFERENT
    algorithms: recursive Optional flattening, nullable filtering in suffixes,
    simultaneous map rounds, eager .any/.all, and widened/refused casts. *)
Theorem optional_parameter_is_not_traversed : forall s h children,
  source_param s h = SOptional children -> source_parameter s h = (None, [ReadParam h]).
Proof. intros; unfold source_parameter; rewrite H; reflexivity. Qed.
Theorem unknown_parameter_has_empty_nullable_obligation : forall name params must nullable,
  get name params = None -> parameter_obligation name params must nullable = (true, 0%N).
Proof. intros; unfold parameter_obligation; rewrite H; reflexivity. Qed.
Theorem known_missing_category_is_nonnullable_with_zero_mask : forall name cat params,
  get name params = Some cat -> parameter_obligation name params [] [] = (false, 0%N).
Proof. intros; unfold parameter_obligation; rewrite H; reflexivity. Qed.
Theorem all_stops_on_first_nonnullable : forall callback h rest mask trace,
  callback h = ((false, mask), trace) -> all_nullable callback (h :: rest) = (false, trace).
Proof. intros; cbn; rewrite H; reflexivity. Qed.
Theorem any_stops_on_first_nullable : forall callback rule rest trace,
  callback rule = (true, trace) -> any_rule callback (rule :: rest) = (true, trace).
Proof. intros; cbn; rewrite H; reflexivity. Qed.
Theorem zero_fuel_does_not_claim_convergence : forall round st,
  iterate_rounds 0 round st = Suspended st.
Proof. reflexivity. Qed.
Theorem category_rule_casts_reuse_original_u16_domain : forall n,
  n < 65536 -> C.cast_u16 n = n.
Proof. apply C.cast_exact_in_u16_domain. Qed.
Theorem position_cast_domain : forall n, n mod 256 < 256.
Proof. intros; apply Nat.mod_upper_bound; discriminate. Qed.

Definition sample_alpha := {| trigger_bits := [("!"%string, 0)]; coarse_bit := 1 |}.
Example suffix_does_not_filter_a_nullable_nonzero_mask :
  suffix_scan (fun _ => ((true, 2%N), [])) [0] 0%N = (2%N, []).
Proof. reflexivity. Qed.
Example cap_keeps_coarse_room_and_visits_remaining_triggers :
  assign_bits ["x"%string; "y"%string; "z"%string] 126 = ([("x"%string, 126)], 127).
Proof. reflexivity. Qed.
Example lexical_trigger_order_and_duplicate_suppression :
  insert_trigger "a"%string (insert_trigger "z"%string (insert_trigger "a"%string [])) =
  ["a"%string; "z"%string].
Proof. vm_compute; reflexivity. Qed.
Example duplicate_parameter_uses_last_successful_insert :
  get "p"%string (put "p"%string "B"%string (put "p"%string "A"%string [])) = Some "B"%string.
Proof. reflexivity. Qed.
Example nullable_round_observes_earlier_same_round_update :
  nullable_round (fun rule nullable =>
    (if Nat.eqb rule 0 then true else default false (get "A"%string nullable), []))
    [[0]; [1]] ["A"%string; "B"%string] 0 false
    (state (seed ["A"%string; "B"%string] false) [] []) =
  RoundDone true (state
    [("B"%string, true); ("A"%string, true); ("B"%string, false); ("A"%string, false)] []
    [NullableRow 0; SetNullable "A"%string; NullableRow 1; SetNullable "B"%string]).
Proof. vm_compute; reflexivity. Qed.
Example must_round_observes_earlier_same_round_update :
  must_round (fun rule must (_ : NameMap bool) =>
    (if Nat.eqb rule 0 then 1%N else default 0%N (get "A"%string must), []))
    [[0]; [1]] ["A"%string; "B"%string] 0 false sample_alpha
    (state [] (seed ["A"%string; "B"%string] (top sample_alpha)) []) =
  RoundDone true (state []
    [("B"%string, 1%N); ("A"%string, 1%N); ("B"%string, 3%N); ("A"%string, 3%N)]
    [MustRow 0; SetMust "A"%string 1%N; MustRow 1; SetMust "B"%string 1%N]).
Proof. vm_compute; reflexivity. Qed.
Example short_row_array_is_a_fault_even_with_no_rules :
  nullable_round (fun _ _ => (false, [])) [] ["A"%string] 0 false (state [] [] []) =
  MissingRow 0 (state [] [] [NullableRow 0]).
Proof. reflexivity. Qed.
Example wrapped_position_overwrites_same_key :
  insert_row (row_key 0 0 256) 2%N (insert_row (row_key 0 0 0) 1%N []) =
  [((0, 0, 0), 2%N)].
Proof. vm_compute; reflexivity. Qed.
Example tuple_rows_emit_in_key_order :
  insert_row (row_key 1 0 0) 1%N (insert_row (row_key 0 2 0) 2%N
    (insert_row (row_key 0 1 3) 3%N [])) =
  [((0, 1, 3), 3%N); ((0, 2, 0), 2%N); ((1, 0, 0), 1%N)].
Proof. vm_compute; reflexivity. Qed.

Print Assumptions parameter_substitution.
Print Assumptions parameter_map_substitution.
Print Assumptions expression_substitution.
Print Assumptions production_must_substitution.
Print Assumptions production_nullable_substitution.
Print Assumptions finite_in_place_analysis_substitution.
Print Assumptions alphabet_callback_substitution.
Print Assumptions assigned_bits_are_consecutive.
Print Assumptions assigned_coarse_bit_stays_below_128.
Print Assumptions complete_suffix_rows_substitution.
Print Assumptions original_descriptor_driver_substitution.
Print Assumptions optional_parameter_is_not_traversed.
Print Assumptions all_stops_on_first_nonnullable.
Print Assumptions any_stops_on_first_nullable.
Print Assumptions zero_fuel_does_not_claim_convergence.
Print Assumptions category_rule_casts_reuse_original_u16_domain.
Print Assumptions position_cast_domain.
End ParikhDescriptorProjection.
