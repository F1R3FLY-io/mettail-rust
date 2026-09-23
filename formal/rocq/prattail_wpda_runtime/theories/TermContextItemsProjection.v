(** Exact original ast::grammar::convert_term_context_to_items relocation.

    The outer loop and the nested Optional iterator-frame loop are explicit
    below. Optional abstractions emit codomains only; outer abstractions retain
    the original pre-domain/post-domain indices even when no item is emitted.
    No theorem asserts those indices name existing items. Map equality is the
    original identifier Eq supplied by the source, never spelling equality.

    Type handles are shallow; MultiBinder and Arrow domain are observations
    needed by THIS original converter, not reconstructed from lowered syntax.
    Reuse the existing TermParamReaderProjection parameter vocabulary and its
    exact sequence/index law. The mathematical type table is a source witness,
    not a Rust AST/normalizer. Source cases and adapter probes are separate;
    output and probe/constructor traces commute by case analysis, then the
    actual frame controller commutes over every finite execution.

    NT kind denotes the already-shared original NonTerminalKind classifier;
    this proof does not rederive it. Constructor and Eq callbacks are the
    original pure observations. Naturals model representable usize lengths;
    allocation, fallible constructors, arbitrary cyclic-reader termination,
    borrow checking, dynamic resource admission, metadata ABI extension and
    complete macro/runtime descriptor parity are explicitly outside scope.
    Fuel is proof instrumentation, never a new Rust limit or refusal.
*)
From Stdlib Require Import List String Bool Arith Lia.
From PrattailWpdaRuntime Require Import TermParamReaderProjection.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Set Implicit Arguments.

Module TermContextItemsProjection.
Module T := TermParamReaderProjection.TermParamReaderProjection.

Inductive SourceType := Base (name : nat) | Collection (kind element : nat)
  | MapType (key value : nat) | Arrow (domain codomain : nat)
  | MultiBinder (inner : nat) | Other (identity : nat).
Record Source := {
  terms : T.SourceStore;
  types : nat -> SourceType;
  names_equal : nat -> nat -> bool;
  nonterminal_kind : nat -> nat;
  hash_map_kind : nat
}.

Inductive Item := NT (name kind : nat) | Binder (name : nat)
  | Coll (kind element : nat) (separator : string).
(** Original collection outputs always have delimiters=None; Coll records only
    the remaining varying fields, not a freedom to synthesize delimiters. *)
Inductive Event := ReadBase (ty : nat) | ReadCollection (ty : nat)
  | ReadMap (ty : nat) | ReadArrow (ty : nat) | ReadMulti (ty : nat)
  | CompareNames (key value : nat) | MakeNT (name : nat)
  | MakeBinder (name : nat) | MakeCollection (kind element : nat) (separator : string)
  | AddBinding (binder body : nat) | ReadParam (handle : nat)
  | EnterOptional (handle : nat) | PopOptional.
Record Buffer := { items : list Item; bindings : list (nat * list nat); trace : list Event }.
Definition buffer is bs tr := {| items := is; bindings := bs; trace := tr |}.
Definition emit s is tr := buffer (items s ++ is) (bindings s) (trace s ++ tr).
Definition nt source name := NT name (nonterminal_kind source name).

Record Probes := {
  base_name : nat -> option nat;
  collection : nat -> option (nat * nat);
  map_type : nat -> option (nat * nat);
  arrow : nat -> option (nat * nat);
  multi_binder : nat -> option nat
}.
Definition project_types source : Probes :=
 {| base_name := fun t => match types source t with Base n => Some n | _ => None end;
    collection := fun t => match types source t with Collection k e => Some (k,e) | _ => None end;
    map_type := fun t => match types source t with MapType k v => Some (k,v) | _ => None end;
    arrow := fun t => match types source t with Arrow d c => Some (d,c) | _ => None end;
    multi_binder := fun t => match types source t with MultiBinder i => Some i | _ => None end |}.

(** The original if-let chain: only later outer probes execute on mismatch;
    both immediate Map child shapes are observed before the equality branch. *)
Definition source_simple source ty : list Item * list Event :=
  match types source ty with
  | Base name => ([nt source name], [ReadBase ty; MakeNT name])
  | Collection kind element =>
      let prefix := [ReadBase ty; ReadCollection ty; ReadBase element] in
      match types source element with
      | Base name => ([Coll kind name "|"], prefix ++ [MakeCollection kind name "|"])
      | _ => ([], prefix) end
  | MapType key value =>
      let prefix := [ReadBase ty; ReadCollection ty; ReadMap ty; ReadBase key; ReadBase value] in
      match types source key, types source value with
      | Base k, Base v =>
          if names_equal source k v
          then ([Coll (hash_map_kind source) v ","], prefix ++ [CompareNames k v; MakeCollection (hash_map_kind source) v ","])
          else ([], prefix ++ [CompareNames k v])
      | _, _ => ([], prefix) end
  | _ => ([], [ReadBase ty; ReadCollection ty; ReadMap ty])
  end.

Definition shared_simple source probes ty : list Item * list Event :=
  match base_name probes ty with
  | Some name => ([nt source name], [ReadBase ty; MakeNT name])
  | None => match collection probes ty with
    | Some (kind, element) =>
        let prefix := [ReadBase ty; ReadCollection ty; ReadBase element] in
        match base_name probes element with
        | Some name => ([Coll kind name "|"], prefix ++ [MakeCollection kind name "|"])
        | None => ([], prefix) end
    | None => match map_type probes ty with
      | Some (key, value) =>
          let prefix := [ReadBase ty; ReadCollection ty; ReadMap ty; ReadBase key; ReadBase value] in
          match base_name probes key, base_name probes value with
          | Some k, Some v =>
              if names_equal source k v
              then ([Coll (hash_map_kind source) v ","], prefix ++ [CompareNames k v; MakeCollection (hash_map_kind source) v ","])
              else ([], prefix ++ [CompareNames k v])
          | _, _ => ([], prefix) end
      | None => ([], [ReadBase ty; ReadCollection ty; ReadMap ty]) end
    end
  end.

Theorem simple_substitution_preserves_items_and_lazy_probes : forall source ty,
  shared_simple source (project_types source) ty = source_simple source ty.
Proof.
  intros source ty. unfold shared_simple, source_simple, project_types; cbn.
  destruct (types source ty); cbn; try reflexivity;
    repeat match goal with |- context [types source ?t] => destruct (types source t); cbn end;
    reflexivity.
Qed.

Definition source_domain source (multiple : bool) domain : list Item * list Event :=
  if multiple then
    match types source domain with
    | MultiBinder inner => match types source inner with
      | Base name => ([Binder name], [ReadMulti domain; ReadBase inner; MakeBinder name])
      | _ => ([], [ReadMulti domain; ReadBase inner]) end
    | _ => ([], [ReadMulti domain]) end
  else match types source domain with
    | Base name => ([Binder name], [ReadBase domain; MakeBinder name])
    | _ => ([], [ReadBase domain]) end.

Definition shared_domain probes (multiple : bool) domain : list Item * list Event :=
  if multiple then
    match multi_binder probes domain with
    | Some inner => match base_name probes inner with
      | Some name => ([Binder name], [ReadMulti domain; ReadBase inner; MakeBinder name])
      | None => ([], [ReadMulti domain; ReadBase inner]) end
    | None => ([], [ReadMulti domain]) end
  else match base_name probes domain with
    | Some name => ([Binder name], [ReadBase domain; MakeBinder name])
    | None => ([], [ReadBase domain]) end.

Theorem domain_substitution_is_exact : forall source multiple domain,
  shared_domain (project_types source) multiple domain = source_domain source multiple domain.
Proof.
  intros source [] domain; unfold shared_domain, source_domain, project_types; cbn;
    destruct (types source domain); cbn; try reflexivity;
    repeat match goal with |- context [types source ?t] => destruct (types source t); cbn end;
    reflexivity.
Qed.

Definition source_body source codomain : list Item * list Event :=
  match types source codomain with
  | Base name => ([nt source name], [ReadBase codomain; MakeNT name])
  | _ => ([], [ReadBase codomain]) end.
Definition shared_body source probes codomain : list Item * list Event :=
  match base_name probes codomain with
  | Some name => ([nt source name], [ReadBase codomain; MakeNT name])
  | None => ([], [ReadBase codomain]) end.
Theorem body_substitution_is_exact : forall source codomain,
  shared_body source (project_types source) codomain = source_body source codomain.
Proof. intros. unfold shared_body, source_body, project_types; cbn. destruct (types source codomain); reflexivity. Qed.

Definition append_abstraction s ty dom bod :=
  let '(domain_items, domain_trace) := dom in
  let '(body_items, body_trace) := bod in
  let binder_index := List.length (items s) in
  let body_index := List.length (items s ++ domain_items) in
  buffer ((items s ++ domain_items) ++ body_items)
    (bindings s ++ [(binder_index, [body_index])])
    (trace s ++ ([ReadArrow ty] ++ domain_trace ++ body_trace ++ [AddBinding binder_index body_index])).

Definition source_abstraction source (nested : bool) multiple ty s :=
  match types source ty with
  | Arrow domain codomain =>
      if nested then let '(is, tr) := source_body source codomain in
        emit s is (ReadArrow ty :: tr)
      else append_abstraction s ty (source_domain source multiple domain) (source_body source codomain)
  | _ => emit s [] [ReadArrow ty] end.
Definition shared_abstraction source probes (nested : bool) multiple ty s :=
  match arrow probes ty with
  | Some (domain, codomain) =>
      if nested then let '(is, tr) := shared_body source probes codomain in
        emit s is (ReadArrow ty :: tr)
      else append_abstraction s ty (shared_domain probes multiple domain) (shared_body source probes codomain)
  | None => emit s [] [ReadArrow ty] end.

Theorem abstraction_substitution_preserves_indices_and_events : forall source nested multiple ty s,
  shared_abstraction source (project_types source) nested multiple ty s =
  source_abstraction source nested multiple ty s.
Proof.
  intros. unfold shared_abstraction, source_abstraction.
  cbn [project_types arrow].
  destruct (types source ty); try reflexivity.
  rewrite body_substitution_is_exact, domain_substitution_is_exact. reflexivity.
Qed.

Definition source_leaf source nested param s := match param with
| T.SSimple _ ty => let '(is,tr) := source_simple source ty in emit s is tr
| T.SAbstraction _ _ ty => source_abstraction source nested false ty s
| T.SMultiAbstraction _ _ ty => source_abstraction source nested true ty s
| T.SGuardBody _ | T.SOptional _ => s end.
Definition shared_leaf source nested param s := match param with
| T.Simple _ ty => let '(is,tr) := shared_simple source (project_types source) ty in emit s is tr
| T.Abstraction _ _ ty => shared_abstraction source (project_types source) nested false ty s
| T.MultiAbstraction _ _ ty => shared_abstraction source (project_types source) nested true ty s
| T.GuardBody _ | T.Optional _ => s end.

Theorem every_leaf_substitution_is_exact : forall source nested param s,
  shared_leaf source nested (T.project_param param) s = source_leaf source nested param s.
Proof.
  intros source nested [] s; cbn; try reflexivity.
  - now rewrite simple_substitution_preserves_items_and_lazy_probes.
  - apply abstraction_substitution_preserves_indices_and_events.
  - apply abstraction_substitution_preserves_indices_and_events.
Qed.

Record State := { outer : list nat; optional_frames : list (list nat); output : Buffer }.
Definition state os fs out := {| outer := os; optional_frames := fs; output := out |}.
Inductive Outcome := Next (st : State) | Done (out : Buffer) | InvalidReader.

(** Exactly the two original loops: nested frames take priority; an exhausted
    inner iterator pops only itself. The outer iterator resumes after all inner
    frames are exhausted. No flattening roster or worklist reordering occurs. *)
Inductive Cursor := Finished | Pop (next : State)
  | Visit (nested : bool) (handle : nat) (next : State).
Definition cursor st := match optional_frames st with
| [] => match outer st with [] => Finished
    | p :: rest => Visit false p (state rest [] (output st)) end
| [] :: rest => Pop (state (outer st) rest (output st))
| (p :: rest) :: frames => Visit true p (state (outer st) (rest :: frames) (output st))
end.
Definition set_output st out := state (outer st) (optional_frames st) out.
Definition push_optional st handle children := state (outer st) (children :: optional_frames st)
  (emit (output st) [] [EnterOptional handle]).

Definition source_step source st := match cursor st with
| Finished => Done (output st)
| Pop next => Next (set_output next (emit (output next) [] [PopOptional]))
| Visit nested handle next =>
    let next := set_output next (emit (output next) [] [ReadParam handle]) in
    match T.source_param (terms source) handle with
    | T.SOptional children => Next (push_optional next children (T.source_parameters (terms source) children))
    | param => Next (set_output next (source_leaf source nested param (output next))) end
end.
Definition shared_step source st := match cursor st with
| Finished => Done (output st)
| Pop next => Next (set_output next (emit (output next) [] [PopOptional]))
| Visit nested handle next =>
    let next := set_output next (emit (output next) [] [ReadParam handle]) in
    match T.param (T.source_reader (terms source)) handle with
    | T.Optional children => match T.read_parameters (T.source_reader (terms source)) children with
      | Some params => Next (push_optional next children params)
      | None => InvalidReader end
    | param => Next (set_output next (shared_leaf source nested param (output next))) end
end.

Theorem each_original_frame_step_commutes : forall source st,
  shared_step source st = source_step source st.
Proof.
  intros. unfold shared_step, source_step.
  destruct (cursor st) as [|next|nested handle next]; try reflexivity.
  cbn [T.source_reader T.param].
  destruct (T.source_param (terms source) handle); cbn [T.project_param shared_leaf source_leaf];
    try rewrite simple_substitution_preserves_items_and_lazy_probes;
    try rewrite abstraction_substitution_preserves_indices_and_events;
    try rewrite T.source_read_parameters_exact; reflexivity.
Qed.

Inductive RunResult := Suspended (st : State) | Completed (out : Buffer) | BadReader.
Fixpoint run fuel step st := match fuel with
| 0 => Suspended st
| S rest => match step st with
  | Next next => run rest step next | Done out => Completed out | InvalidReader => BadReader end
end.
Theorem every_finite_execution_preserves_outputs_bindings_and_order : forall fuel source st,
  run fuel (shared_step source) st = run fuel (source_step source) st.
Proof.
  induction fuel; intros; cbn; [reflexivity|].
  rewrite each_original_frame_step_commutes.
  destruct (source_step source st); [apply IHfuel|reflexivity|reflexivity].
Qed.

Theorem nested_abstractions_never_add_bindings : forall source multiple ty s,
  bindings (source_abstraction source true multiple ty s) = bindings s.
Proof.
  intros. unfold source_abstraction.
  destruct (types source ty) as [name|kind element|key value|domain codomain|inner|identity];
    cbn; try reflexivity.
  unfold source_body. destruct (types source codomain); reflexivity.
Qed.

Theorem original_partial_arrow_indices_are_kept : forall s ty domtr bodytr,
  bindings (append_abstraction s ty ([], domtr) ([], bodytr)) =
  bindings s ++ [(List.length (items s), [List.length (items s)])].
Proof. intros. cbn [append_abstraction buffer bindings]. now rewrite app_nil_r. Qed.

Theorem optional_cursor_preserves_parent_continuation : forall os p rest frames out,
  cursor (state os ((p :: rest) :: frames) out) =
  Visit true p (state os (rest :: frames) out).
Proof. reflexivity. Qed.

Theorem nested_arrow_does_not_observe_domain : forall source ty domain codomain multiple s,
  types source ty = Arrow domain codomain ->
  source_abstraction source true multiple ty s =
  let '(is,tr) := source_body source codomain in emit s is (ReadArrow ty :: tr).
Proof. intros. unfold source_abstraction. now rewrite H. Qed.

Print Assumptions simple_substitution_preserves_items_and_lazy_probes.
Print Assumptions domain_substitution_is_exact.
Print Assumptions body_substitution_is_exact.
Print Assumptions abstraction_substitution_preserves_indices_and_events.
Print Assumptions every_leaf_substitution_is_exact.
Print Assumptions each_original_frame_step_commutes.
Print Assumptions every_finite_execution_preserves_outputs_bindings_and_order.
Print Assumptions nested_abstractions_never_add_bindings.
Print Assumptions original_partial_arrow_indices_are_kept.
Print Assumptions optional_cursor_preserves_parent_continuation.
Print Assumptions nested_arrow_does_not_observe_domain.
End TermContextItemsProjection.
