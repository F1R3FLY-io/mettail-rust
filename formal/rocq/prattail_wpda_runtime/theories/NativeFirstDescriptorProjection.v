(** Exact original native FIRST/home descriptor relocation.

    Source: macros/src/gen/runtime/wpda_codegen/prefix.rs:
    literal_family_for, declared_literal_token_def, literal_family_for_category,
    home_polymorphic_token_arm, literal_patterned_pattern_and_guard_for_kind.

    NativeKind is the EXISTING ast enum: from_syn_type remains the original
    source-side callback, not an inference from CoreCarrier. Native absence is
    independent of Other. Source spelling lookup is deliberately distinct from
    classify_literal_patterned's earlier Ident-Eq lookup, which is not moved by
    this slice. Token payloads are opaque and the selected declaration is kept.

    The source lookup bodies below read concrete fields; the shared bodies read
    generic borrowed handles. ProjectionLaw is the explicit source-adapter
    obligation, not admission of arbitrary runtime metadata. The row model
    enumerates the original quotation sites and substitutes opaque constructors
    at those same sites. In particular Boolean is ONE alternative-pattern row;
    Integer Home calls the home helper twice, discarding its first result.

    All lists/indices are finite and fit the source usize domain. No new fuel,
    allocator/resource policy, evaluator, lexer completeness, native parsing,
    source reconstruction, or transition-body claim is made. Deterministic
    callback result laws and the original NativeKind observation are required;
    effectful callbacks violating those laws are outside this theorem.
*)
From Stdlib Require Import List String Bool Arith.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Set Implicit Arguments.

Module NativeFirstDescriptorProjection.

Inductive NativeKind :=
| Int8 | Int16 | Int32 | Int64 | Int128 | Isize
| UInt8 | UInt16 | UInt32 | UInt64 | UInt128 | Usize
| CanonicalBigInt | CanonicalBigRat | CanonicalFixedPoint
| Float32 | Float64 | BoolKind | Str | Other.
Inductive Family := Integer | Rational | FixedPoint | Float | Boolean | String | Custom.
Inductive Context := HomeCategory | FirstSet.

Definition family_for kind := match kind with
| Int8 | Int16 | Int32 | Int64 | Int128 | Isize
| UInt8 | UInt16 | UInt32 | UInt64 | UInt128 | Usize | CanonicalBigInt => Some Integer
| CanonicalBigRat => Some Rational | CanonicalFixedPoint => Some FixedPoint
| Float32 | Float64 => Some Float | BoolKind => Some Boolean | Str => Some String
| Other => None end.

Record Native := { native_kind : NativeKind; static_type_payload : nat }.
Record Category := { category_id : nat; category_name : string; native : option Native }.
Record Token := { token_id : nat; from_literals : bool; has_rust_code : bool;
  token_category : option string; opaque_payload : nat }.

Inductive LookupEvent :=
| CategoryName (id : nat) | NativePresence (id : nat) | ResolveNativeKind (id : nat)
| FromLiterals (id : nat) | RustCodePresence (id : nat) | TokenCategory (id : nat).
Definition prefix_trace {A} events (answer : A * list LookupEvent) :=
  (fst answer, events ++ snd answer).
Definition map_answer {A B} (f : A -> B) (answer : option A * list LookupEvent) :=
  (option_map f (fst answer), snd answer).

(** The source && and Option::is_some_and are nested, not eager field reads. *)
Definition source_eligible target token : bool * list LookupEvent :=
  if from_literals token then
    if has_rust_code token then
      (match token_category token with
       | Some name => String.eqb name target | None => false end,
       [FromLiterals (token_id token); RustCodePresence (token_id token);
        TokenCategory (token_id token)])
    else (false, [FromLiterals (token_id token); RustCodePresence (token_id token)])
  else (false, [FromLiterals (token_id token)]).

Fixpoint source_declared target tokens : option Token * list LookupEvent :=
  match tokens with
  | [] => (None, [])
  | token :: rest => let '(eligible, events) := source_eligible target token in
    if eligible then (Some token, events)
    else prefix_trace events (source_declared target rest)
  end.

Fixpoint source_family target categories tokens : option Family * list LookupEvent :=
  match categories with
  | [] => (None, [])
  | category :: rest =>
    let named := [CategoryName (category_id category)] in
    if String.eqb (category_name category) target then
      let checked := named ++ [NativePresence (category_id category)] in
      match native category with
      | None => (None, checked)
      | Some value =>
        let resolved := checked ++ [ResolveNativeKind (category_id category)] in
        match family_for (native_kind value) with
        | Some family => (Some family, resolved)
        | None => let '(found, events) := source_declared target tokens in
          (match found with Some _ => Some Custom | None => None end, resolved ++ events)
        end
      end
    else prefix_trace named (source_family target rest tokens)
  end.

Record Reader (C T : Type) := {
  read_category_id : C -> nat;
  read_category_name : C -> string;
  read_native : C -> option Native;
  read_token_id : T -> nat;
  read_from_literals : T -> bool;
  read_rust_code_presence : T -> bool;
  read_token_category : T -> option string
}.

Definition shared_eligible {C T} (reader : Reader C T) target token :=
  if read_from_literals reader token then
    if read_rust_code_presence reader token then
      (match read_token_category reader token with
       | Some name => String.eqb name target | None => false end,
       [FromLiterals (read_token_id reader token); RustCodePresence (read_token_id reader token);
        TokenCategory (read_token_id reader token)])
    else (false, [FromLiterals (read_token_id reader token);
                  RustCodePresence (read_token_id reader token)])
  else (false, [FromLiterals (read_token_id reader token)]).

Fixpoint shared_declared {C T} (reader : Reader C T) target tokens :=
  match tokens with
  | [] => (None, [])
  | token :: rest => let '(eligible, events) := shared_eligible reader target token in
    if eligible then (Some token, events)
    else prefix_trace events (shared_declared reader target rest)
  end.

Fixpoint shared_family {C T} (reader : Reader C T) target categories tokens :=
  match categories with
  | [] => (None, [])
  | category :: rest =>
    let named := [CategoryName (read_category_id reader category)] in
    if String.eqb (read_category_name reader category) target then
      let checked := named ++ [NativePresence (read_category_id reader category)] in
      match read_native reader category with
      | None => (None, checked)
      | Some value =>
        let resolved := checked ++ [ResolveNativeKind (read_category_id reader category)] in
        match family_for (native_kind value) with
        | Some family => (Some family, resolved)
        | None => let '(found, events) := shared_declared reader target tokens in
          (match found with Some _ => Some Custom | None => None end, resolved ++ events)
        end
      end
    else prefix_trace named (shared_family reader target rest tokens)
  end.

Record ProjectionLaw {C T} (reader : Reader C T)
    (project_category : Category -> C) (project_token : Token -> T) : Prop := {
  category_id_law : forall c, read_category_id reader (project_category c) = category_id c;
  category_name_law : forall c, read_category_name reader (project_category c) = category_name c;
  native_law : forall c, read_native reader (project_category c) = native c;
  token_id_law : forall t, read_token_id reader (project_token t) = token_id t;
  from_literals_law : forall t, read_from_literals reader (project_token t) = from_literals t;
  rust_code_law : forall t, read_rust_code_presence reader (project_token t) = has_rust_code t;
  token_category_law : forall t, read_token_category reader (project_token t) = token_category t
}.

Theorem eligible_observation_substitution : forall C T (reader : Reader C T) cp tp,
  ProjectionLaw reader cp tp -> forall target token,
  shared_eligible reader target (tp token) = source_eligible target token.
Proof.
  intros C T reader cp tp law target token.
  unfold shared_eligible, source_eligible.
  rewrite (from_literals_law law), (rust_code_law law),
    (token_category_law law), (token_id_law law). reflexivity.
Qed.

Theorem selected_token_and_trace_substitution : forall C T (reader : Reader C T) cp tp,
  ProjectionLaw reader cp tp -> forall target tokens,
  shared_declared reader target (map tp tokens) = map_answer tp (source_declared target tokens).
Proof.
  intros C T reader cp tp law target tokens; induction tokens as [|token rest IH]; cbn.
  - reflexivity.
  - rewrite (eligible_observation_substitution law).
    destruct (source_eligible target token) as [eligible events].
    destruct eligible; cbn; [reflexivity|]. rewrite IH.
    unfold map_answer, prefix_trace. reflexivity.
Qed.

Theorem category_family_and_trace_substitution : forall C T (reader : Reader C T) cp tp,
  ProjectionLaw reader cp tp -> forall target categories tokens,
  shared_family reader target (map cp categories) (map tp tokens) =
  source_family target categories tokens.
Proof.
  intros C T reader cp tp law target categories; induction categories as [|category rest IH];
    intros tokens; cbn; [reflexivity|].
  rewrite (category_name_law law), (category_id_law law), (native_law law).
  destruct (String.eqb (category_name category) target); [|rewrite IH; reflexivity].
  destruct (native category) as [value|]; [|reflexivity].
  destruct (family_for (native_kind value)); [reflexivity|].
  rewrite (selected_token_and_trace_substitution law).
  unfold map_answer. destruct (source_declared target tokens) as [[token|] events]; reflexivity.
Qed.

Lemma selected_token_is_original_member : forall target tokens token,
  fst (source_declared target tokens) = Some token -> In token tokens.
Proof.
  intros target tokens; induction tokens as [|head rest IH]; intros token H; cbn in H.
  - discriminate.
  - destruct (source_eligible target head) as [eligible events]. destruct eligible.
    + cbn in H; inversion H; subst; left; reflexivity.
    + right. apply IH. exact H.
Qed.

Lemma from_literals_false_skips_later_observations : forall target token,
  from_literals token = false ->
  source_eligible target token = (false, [FromLiterals (token_id token)]).
Proof. intros target token H; unfold source_eligible; rewrite H; reflexivity. Qed.

Lemma missing_eval_skips_category : forall target token,
  from_literals token = true -> has_rust_code token = false ->
  source_eligible target token =
    (false, [FromLiterals (token_id token); RustCodePresence (token_id token)]).
Proof. intros target token H E; unfold source_eligible; rewrite H, E; reflexivity. Qed.

Lemma first_match_without_native_stops : forall target id rest tokens,
  source_family target ({| category_id := id; category_name := target; native := None |} :: rest)
    tokens = (None, [CategoryName id; NativePresence id]).
Proof. intros; cbn; rewrite String.eqb_refl; reflexivity. Qed.

Lemma builtin_family_skips_token_scan : forall target id value family rest tokens,
  family_for (native_kind value) = Some family ->
  source_family target
    ({| category_id := id; category_name := target; native := Some value |} :: rest) tokens =
    (Some family, [CategoryName id; NativePresence id; ResolveNativeKind id]).
Proof. intros; cbn; rewrite String.eqb_refl, H; reflexivity. Qed.

(** Quotation sites are syntactic constructors, not a replacement token taxonomy.
    BooleanAlternative represents the entire original True|False|BooleanLit
    quotation. Guard construction is separately sequenced after its pattern. *)
Inductive PatternSite := IntegerTyped | CustomTyped | RationalTyped | FixedPointTyped
  | FloatBare | BooleanAlternative | StringBare | IntegerBare.
Inductive SyntaxPayload := Pattern (site : PatternSite) | CategoryGuard (name : string).
Inductive QuoteEvent := QuotePattern (site : PatternSite) | QuoteGuard (name : string)
  | CallHome (family : Family).
Record Rows (P : Type) := { rows : list (P * option P); calls : list QuoteEvent }.
Arguments rows {P} _.
Arguments calls {P} _.
Definition one {P} (pattern : P) guard events : Rows P :=
  {| rows := [(pattern, guard)]; calls := events |}.
Definition join {P} (lhs rhs : Rows P) :=
  {| rows := rows lhs ++ rows rhs; calls := calls lhs ++ calls rhs |}.
Definition guarded_source cat site :=
  one (Pattern site) (Some (CategoryGuard cat)) [QuotePattern site; QuoteGuard cat].
Definition bare_source site := one (Pattern site) None [QuotePattern site].
Definition source_home family := match family with
| Integer => (Some (Pattern IntegerBare), [CallHome Integer; QuotePattern IntegerBare])
| _ => (None, [CallHome family]) end.
Definition append_home {P} (base : Rows P) (home : option P * list QuoteEvent) :=
  {| rows := match fst home with Some pattern => rows base ++ [(pattern, None)]
             | None => rows base end;
     calls := calls base ++ snd home |}.

Definition primitive_first kind := match kind with
| None | Some Int8 | Some Int16 | Some Int32 | Some Int64 | Some Int128 | Some Isize
| Some UInt8 | Some UInt16 | Some UInt32 | Some UInt64 | Some UInt128 | Some Usize => true
| _ => false end.

Definition source_rows cat family kind context : Rows SyntaxPayload := match family with
| Integer =>
  let base := join (guarded_source cat IntegerTyped) (guarded_source cat CustomTyped) in
  let '(emit, gate_calls) := match context with
    | HomeCategory => let '(pattern, trace) := source_home family in
      (match pattern with Some _ => true | None => false end, trace)
    | FirstSet => (primitive_first kind, []) end in
  let gated := {| rows := rows base; calls := calls base ++ gate_calls |} in
  if emit then append_home gated (source_home family) else gated
| Rational => join (guarded_source cat RationalTyped) (guarded_source cat CustomTyped)
| FixedPoint => join (guarded_source cat FixedPointTyped) (guarded_source cat CustomTyped)
| Float => bare_source FloatBare | Boolean => bare_source BooleanAlternative
| String => bare_source StringBare | Custom => guarded_source cat CustomTyped end.

Record Constructors (P : Type) := { quote_pattern : PatternSite -> P; quote_guard : string -> P }.
Definition interpret {P} (constructors : Constructors P) payload := match payload with
| Pattern site => quote_pattern constructors site | CategoryGuard name => quote_guard constructors name end.
Definition project_rows {P} (constructors : Constructors P) (source : Rows SyntaxPayload) :=
  {| rows := map (fun row => (interpret constructors (fst row),
                             option_map (interpret constructors) (snd row))) (rows source);
     calls := calls source |}.
Definition guarded_shared {P} (constructors : Constructors P) cat site :=
  one (quote_pattern constructors site) (Some (quote_guard constructors cat))
    [QuotePattern site; QuoteGuard cat].
Definition bare_shared {P} (constructors : Constructors P) site :=
  one (quote_pattern constructors site) None [QuotePattern site].
Definition shared_home {P} (constructors : Constructors P) family := match family with
| Integer => (Some (quote_pattern constructors IntegerBare),
              [CallHome Integer; QuotePattern IntegerBare])
| _ => (None, [CallHome family]) end.

(** Same branch/constructor sites as Rust, with generic payload construction.
    The Home test remains a call, not an optimized constant-true rewrite. *)
Definition shared_rows {P} (constructors : Constructors P) cat family kind context : Rows P :=
  match family with
| Integer =>
  let base := join (guarded_shared constructors cat IntegerTyped)
                   (guarded_shared constructors cat CustomTyped) in
  let '(emit, gate_calls) := match context with
    | HomeCategory => let '(pattern, trace) := shared_home constructors family in
      (match pattern with Some _ => true | None => false end, trace)
    | FirstSet => (primitive_first kind, []) end in
  let gated := {| rows := rows base; calls := calls base ++ gate_calls |} in
  if emit then append_home gated (shared_home constructors family) else gated
| Rational => join (guarded_shared constructors cat RationalTyped)
                   (guarded_shared constructors cat CustomTyped)
| FixedPoint => join (guarded_shared constructors cat FixedPointTyped)
                     (guarded_shared constructors cat CustomTyped)
| Float => bare_shared constructors FloatBare
| Boolean => bare_shared constructors BooleanAlternative
| String => bare_shared constructors StringBare
| Custom => guarded_shared constructors cat CustomTyped end.

Theorem original_rows_constructor_substitution : forall P (constructors : Constructors P)
  cat family kind context,
  shared_rows constructors cat family kind context =
  project_rows constructors (source_rows cat family kind context).
Proof.
  intros P constructors cat family kind context.
  destruct family; destruct context; destruct kind as [kind|]; try destruct kind; reflexivity.
Qed.

Theorem constructor_callback_trace_preserved : forall P (constructors : Constructors P)
  cat family kind context,
  calls (shared_rows constructors cat family kind context) = calls (source_rows cat family kind context).
Proof. intros; rewrite original_rows_constructor_substitution; reflexivity. Qed.

Lemma integer_home_exact_schedule : forall cat kind,
  calls (source_rows cat Integer kind HomeCategory) =
    [QuotePattern IntegerTyped; QuoteGuard cat; QuotePattern CustomTyped; QuoteGuard cat;
     CallHome Integer; QuotePattern IntegerBare; CallHome Integer; QuotePattern IntegerBare].
Proof. reflexivity. Qed.

Lemma bigint_first_omits_home_callback : forall cat,
  calls (source_rows cat Integer (Some CanonicalBigInt) FirstSet) =
    [QuotePattern IntegerTyped; QuoteGuard cat; QuotePattern CustomTyped; QuoteGuard cat].
Proof. reflexivity. Qed.

Lemma missing_kind_first_keeps_bare_integer : forall cat,
  rows (source_rows cat Integer None FirstSet) =
    [(Pattern IntegerTyped, Some (CategoryGuard cat));
     (Pattern CustomTyped, Some (CategoryGuard cat)); (Pattern IntegerBare, None)].
Proof. reflexivity. Qed.

Lemma boolean_is_one_alternative_row : forall cat kind context,
  rows (source_rows cat Boolean kind context) = [(Pattern BooleanAlternative, None)].
Proof. reflexivity. Qed.

Lemma other_has_no_builtin_family : family_for Other = None.
Proof. reflexivity. Qed.

Example custom_uses_first_eligible_not_first_same_category :
  let rejected := {| token_id := 10; from_literals := true; has_rust_code := false;
                     token_category := Some "Value"; opaque_payload := 101 |} in
  let accepted := {| token_id := 11; from_literals := true; has_rust_code := true;
                     token_category := Some "Value"; opaque_payload := 202 |} in
  source_declared "Value" [rejected; accepted; rejected] =
    (Some accepted, [FromLiterals 10; RustCodePresence 10;
                    FromLiterals 11; RustCodePresence 11; TokenCategory 11]).
Proof. reflexivity. Qed.

Print Assumptions eligible_observation_substitution.
Print Assumptions selected_token_and_trace_substitution.
Print Assumptions category_family_and_trace_substitution.
Print Assumptions selected_token_is_original_member.
Print Assumptions from_literals_false_skips_later_observations.
Print Assumptions missing_eval_skips_category.
Print Assumptions first_match_without_native_stops.
Print Assumptions builtin_family_skips_token_scan.
Print Assumptions original_rows_constructor_substitution.
Print Assumptions constructor_callback_trace_preserved.
Print Assumptions integer_home_exact_schedule.
Print Assumptions bigint_first_omits_home_callback.
Print Assumptions missing_kind_first_keeps_bare_integer.
Print Assumptions boolean_is_one_alternative_row.
Print Assumptions other_has_no_builtin_family.
Print Assumptions custom_uses_first_eligible_not_first_same_category.
End NativeFirstDescriptorProjection.
