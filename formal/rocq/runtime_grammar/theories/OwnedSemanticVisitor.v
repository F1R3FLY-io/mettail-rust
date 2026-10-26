(** * Borrowed observations for the original generated semantic visitor

    Source map: macros/src/gen/term_ops/semantic_hash.rs, the sink support,
    category handler, iterative task loop, ordered collection scheduler and
    generate_semantic_variant_arm; subst.rs collect_category_variants.

    This is an extraction model, not a serialization specification. Hash
    payloads below stand for calls to the SAME Rust Hash/native-byte worker;
    an adapter is not allowed to replace them with DynamicValue.semantic_key.
    The category-local constructor roster and borrowed children must first be
    related to the original typed AST. In particular, global semantic operator
    discriminants and WPDA-local rule indices are NOT constructor tags.

    The finite model covers the admitted regular/transparent/ordered-list,
    native literal and variable arms. Existing scoped/fold/unordered callbacks
    remain the original static workers. Cache soundness and failure publication
    are supplied by KbestCompositionalSemanticKey, not assumed hash injectivity.
    Structural holes without an original typed AST observation retain the
    existing no-key hook; they are not assigned invented encoded bytes. *)
From Stdlib Require Import List Bool Arith.PeanoNat.
From RuntimeGrammar Require Import KbestCompositionalSemanticKey.
From PrattailWpdaRuntime Require Import FacadeDriverFallThrough.
Import ListNotations.

Module OwnedSemanticVisitor.

Inductive WriteEvent : Type :=
| WriteU8 : nat -> WriteEvent
| WriteUsize : nat -> WriteEvent
| HashUsize : nat -> WriteEvent
| HashPayload : nat -> WriteEvent
| WriteBytes : list nat -> WriteEvent.

Definition free_variable (name : option nat) : list WriteEvent :=
  [WriteU8 251; WriteU8 0] ++
  match name with
  | Some payload => [WriteU8 1; HashPayload payload]
  | None => [WriteU8 0]
  end.
Definition bound_variable scope binder : list WriteEvent :=
  [WriteU8 251; WriteU8 1; HashPayload scope; HashPayload binder].
Definition literal tag payload := [WriteU8 tag; HashPayload payload].
Definition integer_literal bytes :=
  [WriteU8 254; WriteUsize (length bytes); WriteBytes bytes].

(** Top of stack is the list head. The concrete Vec implementation appends
    children in reverse order, so the next pop observes the first child. *)
Inductive Task : Type :=
| Visit : nat -> Task
| Emit : WriteEvent -> Task
| Finish : nat -> Task.

Record NodeObservation : Type := {
  local_events : list WriteEvent;
  child_tasks : list Task
}.

Definition original_schedule (node : NodeObservation) (rest : list Task) :=
  map Emit (local_events node) ++ child_tasks node ++ rest.
Definition borrowed_schedule := original_schedule.

Definition transparent child : NodeObservation :=
  {| local_events := []; child_tasks := [Visit child] |}.
Definition regular tag children : NodeObservation :=
  {| local_events := [WriteU8 tag]; child_tasks := map Visit children |}.
Definition ordered_list children : NodeObservation :=
  {| local_events := [HashUsize (length children)]; child_tasks := map Visit children |}.

Section Observation.
Variable typed borrowed : nat -> NodeObservation.

Fixpoint run (observe : nat -> NodeObservation) (fuel : nat) (stack : list Task)
    : list WriteEvent * list Task :=
  match fuel, stack with
  | O, _ => ([], stack)
  | S remaining, [] => ([], [])
  | S remaining, Visit node :: rest =>
      run observe remaining (original_schedule (observe node) rest)
  | S remaining, Emit event :: rest =>
      let '(events, pending) := run observe remaining rest in
      (event :: events, pending)
  | S remaining, Finish _ :: rest => run observe remaining rest
  end.

Theorem borrowed_worker_preserves_each_write_and_pending_task :
  (forall node, borrowed node = typed node) -> forall fuel stack,
  run borrowed fuel stack = run typed fuel stack.
Proof.
  intros same_observation.
  induction fuel as [|fuel IH]; intros stack; [reflexivity|].
  destruct stack as [|task rest]; [reflexivity|].
  destruct task; simpl; try rewrite same_observation; now rewrite IH.
Qed.

End Observation.

Theorem transparent_has_no_discriminant : forall child rest,
  borrowed_schedule (transparent child) rest = Visit child :: rest.
Proof. reflexivity. Qed.
Theorem regular_retains_child_order : forall tag children rest,
  borrowed_schedule (regular tag children) rest =
    Emit (WriteU8 tag) :: (map Visit children ++ rest).
Proof. reflexivity. Qed.
Theorem ordered_list_hashes_length_before_first_child : forall children rest,
  borrowed_schedule (ordered_list children) rest =
    Emit (HashUsize (length children)) :: (map Visit children ++ rest).
Proof. reflexivity. Qed.
Theorem variable_name_not_native_allocation_identity : forall name (left right : nat),
  (fun _ => free_variable name) left = (fun _ => free_variable name) right.
Proof. reflexivity. Qed.

(** Roster assembly moves without replacing its source classifiers. The native
    and HOL callbacks below execute at their original sites and retain state,
    so lazy queries and their error/observation state cannot be hoisted. *)
Section Roster.
Context {Variant State : Type}.
Variable is_var : Variant -> bool.
Variable implicit_var : State -> bool * State.
Variable make_var : State -> Variant * State.
Variable native_literal : list Variant -> State -> option Variant * State.
Variable hol_variants : State -> list Variant * State.

Definition original_roster (authored : list Variant) state :=
  let '(after_var, state) :=
    if existsb is_var authored then (authored, state) else
    let '(enabled, state) := implicit_var state in
    if enabled then let '(variant, state) := make_var state in
      (authored ++ [variant], state)
    else (authored, state) in
  let '(native, state) := native_literal after_var state in
  let after_literal := match native with
    | Some variant => after_var ++ [variant]
    | None => after_var end in
  let '(hol, state) := hol_variants state in
  (after_literal ++ hol, state).
Definition shared_roster := original_roster.
Theorem roster_preserves_order_and_callback_state : forall authored state,
  shared_roster authored state = original_roster authored state.
Proof. reflexivity. Qed.
Theorem explicit_variable_skips_implicit_probe : forall authored state,
  existsb is_var authored = true ->
  shared_roster authored state =
    let '(native, next) := native_literal authored state in
    let '(hol, final) := hol_variants next in
    ((match native with Some variant => authored ++ [variant] | None => authored end)
      ++ hol, final).
Proof. intros; unfold shared_roster, original_roster; now rewrite H. Qed.
End Roster.

Section CacheBoundary.
Import KbestCompositionalSemanticKey.KbestCompositionalSemanticKey.
Variable encode : WriteEvent -> list Byte.
Definition encode_events events := concat (map encode events).
Theorem equal_event_traces_have_equal_exact_keys : forall left right,
  left = right -> encode_events left = encode_events right.
Proof. intros; now subst. Qed.
Theorem shared_child_composition_preserves_original_stream : forall events children,
  flatten_key (compose_key (encode_events events) children) =
    encode_events events ++ concat (map flatten_key children).
Proof. intros events children; apply compose_key_exact. Qed.
Theorem cached_node_uses_exact_original_observation : forall exact cache node key,
  CacheSound exact cache -> cache_lookup node cache = Some key ->
  flatten_key key = exact node.
Proof. exact cache_hit_returns_exact_stream. Qed.
Theorem successful_key_construction_publishes_candidates : forall (Term : Type)
    (candidates : list Term),
  exposed_terms (finalize_realization candidates true) = candidates.
Proof. exact construction_success_publishes_all_candidates. Qed.
Theorem failed_key_construction_cannot_publish_candidates : forall (Term : Type)
    (candidates : list Term),
  exposed_terms (finalize_realization candidates false) = [].
Proof. exact construction_failure_publishes_no_candidates. Qed.
End CacheBoundary.

(** A hook dispatch distinguishes absence of an original semantic observation
    from a failure constructing its key. It never changes Err into None. *)
Section Hook.
Context {Node Key Fault : Type}.
Variable key_worker : Node -> (Fault + Key)%type.
Definition hook (node : option Node) : (Fault + option Key)%type :=
  match node with
  | None => inr None
  | Some node => match key_worker node with
    | inl error => inl error
    | inr key => inr (Some key)
    end
  end.
Theorem no_original_observation_retains_no_key : hook None = inr None.
Proof. reflexivity. Qed.
Theorem key_error_is_not_no_key : forall node error,
  key_worker node = inl error -> hook (Some node) = inl error.
Proof. intros; unfold hook; now rewrite H. Qed.
End Hook.

Print Assumptions borrowed_worker_preserves_each_write_and_pending_task.
Print Assumptions transparent_has_no_discriminant.
Print Assumptions regular_retains_child_order.
Print Assumptions ordered_list_hashes_length_before_first_child.
Print Assumptions variable_name_not_native_allocation_identity.
Print Assumptions roster_preserves_order_and_callback_state.
Print Assumptions explicit_variable_skips_implicit_probe.
Print Assumptions equal_event_traces_have_equal_exact_keys.
Print Assumptions shared_child_composition_preserves_original_stream.
Print Assumptions cached_node_uses_exact_original_observation.
Print Assumptions successful_key_construction_publishes_candidates.
Print Assumptions failed_key_construction_cannot_publish_candidates.
Print Assumptions no_original_observation_retains_no_key.
Print Assumptions key_error_is_not_no_key.

Inductive CastTerm :=
| CBoolLit (b : bool)
| CBoolToUInt32 (x : CastTerm)
| CCastUInt32 (x : CastTerm)
| CCastBool (x : CastTerm).

Fixpoint cast_key (term : CastTerm) : list WriteEvent :=
  match term with
  | CBoolLit b => literal 1 (if b then 1 else 0)
  | CBoolToUInt32 x | CCastUInt32 x | CCastBool x => cast_key x
  end.

Inductive CastVal := VBool (b : bool) | VU32 (n : nat).

Fixpoint cast_eval (term : CastTerm) : option CastVal :=
  match term with
  | CBoolLit b => Some (VBool b)
  | CBoolToUInt32 x => match cast_eval x with
    | Some (VBool b) => Some (VU32 (if b then 1 else 0))
    | _ => None end
  | CCastUInt32 x => match cast_eval x with
    | Some (VU32 n) => Some (VU32 n)
    | _ => None end
  | CCastBool x => match cast_eval x with
    | Some (VBool b) => Some (VBool b)
    | _ => None end
  end.

Definition t_u32 b := CCastUInt32 (CBoolToUInt32 (CBoolLit b)).
Definition t_bool b := CCastBool (CBoolLit b).
Definition w_u32 := {| lw_open_len := 0; lw_primary := 0; lw_lex_alt := 0;
  lw_src := 0; lw_rule := 39 |}.
Definition w_bool := {| lw_open_len := 0; lw_primary := 0; lw_lex_alt := 0;
  lw_src := 0; lw_rule := 40 |}.

Definition we_eq_dec : forall a b : WriteEvent, {a = b} + {a <> b}.
Proof. decide equality; try apply Nat.eq_dec; apply (list_eq_dec Nat.eq_dec). Defined.

Definition key_eqb (a b : list WriteEvent) :=
  if list_eq_dec we_eq_dec a b then true else false.

Theorem key_eqb_spec : forall a b, key_eqb a b = true <-> a = b.
Proof.
  intros; unfold key_eqb; destruct (list_eq_dec we_eq_dec a b); intuition discriminate.
Qed.

Theorem cast_cohort_key_collision : forall b, cast_key (t_u32 b) = cast_key (t_bool b).
Proof. reflexivity. Qed.

Theorem cast_cohort_eval_differs : forall b, cast_eval (t_u32 b) <> cast_eval (t_bool b).
Proof. intros b; destruct b; discriminate. Qed.

Theorem g1_fold_keeps_cast_u32 : forall b,
  all_fold key_eqb cast_key [(t_u32 b, w_u32); (t_bool b, w_bool)] = [(t_u32 b, w_u32)] /\
  all_fold key_eqb cast_key [(t_bool b, w_bool); (t_u32 b, w_u32)] = [(t_u32 b, w_u32)].
Proof. intros b; destruct b; split; reflexivity. Qed.

Theorem g1_fold_drops_elected_term : forall b,
  ~ In (t_bool b) (map fst (all_fold key_eqb cast_key [(t_u32 b,w_u32); (t_bool b,w_bool)])).
Proof.
  intros b; rewrite (proj1 (g1_fold_keeps_cast_u32 b)); simpl; intuition discriminate.
Qed.

Theorem g1_consumer_value : forall b,
  map (fun pair => cast_eval (fst pair))
    (all_fold key_eqb cast_key [(t_u32 b,w_u32); (t_bool b,w_bool)]) =
  [Some (VU32 (if b then 1 else 0))].
Proof. intros b; destruct b; reflexivity. Qed.

Theorem g1_aligned_rep_is_elected : forall b,
  align key_eqb cast_key [t_bool b]
    (all_fold key_eqb cast_key [(t_u32 b,w_u32); (t_bool b,w_bool)]) = [(t_bool b,w_u32)].
Proof. intros b; destruct b; reflexivity. Qed.

Theorem g1_aligned_value : forall b,
  map (fun pair => cast_eval (fst pair))
    (align key_eqb cast_key [t_bool b]
      (all_fold key_eqb cast_key [(t_u32 b,w_u32); (t_bool b,w_bool)])) = [Some (VBool b)].
Proof. intros b; destruct b; reflexivity. Qed.

Print Assumptions key_eqb_spec.
Print Assumptions cast_cohort_key_collision.
Print Assumptions cast_cohort_eval_differs.
Print Assumptions g1_fold_keeps_cast_u32.
Print Assumptions g1_fold_drops_elected_term.
Print Assumptions g1_consumer_value.
Print Assumptions g1_aligned_rep_is_elected.
Print Assumptions g1_aligned_value.

End OwnedSemanticVisitor.
