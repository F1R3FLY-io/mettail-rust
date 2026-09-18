(** First-occurrence synchronization for binder-local FLT body preparation.

    Source correspondence: [find_first_body_site] in rholang_ast.rs schedules
    children before Emit; [replace_first_body_site] schedules the same children
    before Build. For dynamic FLTs, only PFlt/PFltFence/PFltBrace leaf events
    qualify. Name wrappers emit no FLT event. Send sugar is expanded before
    scheduling; nested PForUser/PNew/PNewUris bodies are opaque. PPar occurrences
    retain multiplicity and native iteration order; Map visits key then value.

    The model below deliberately distinguishes occurrence positions from Arc
    keys. Its event lists are the ORIGINAL FLT occurrence roster, not lists of
    rebuilt ancestor terms. Rebuilding an ancestor changes its term but must
    preserve its unaffected child slots. Nor is this a claim that rewalking a
    rebuilt hash collection preserves its native iteration order.

    [expand] is the source-correspondence parameter: each concrete source arm
    must supply its actual ordered child jobs and optional event. [Run] models
    the explicit worklist, not a recursive Rust algorithm. Proof recursion is
    structural induction over finite derivations/lists, never source execution.
    Sugar normalization, identical child scheduling in both Rust workers,
    immutable environment, and pointer-preserving Clone require source review
    and Rust regression tests. Open/Close are NOT pointer-preserving Clone.

    [seek] and [replace_first] specify occurrence selection only. Their laws
    show that the finder's selector-identity eligibility and the replacer's
    Arc pointer comparison select exactly the same position, even if later
    positions share that Arc. They do not identify distinct same-looking Arcs.
    Payment/refusal and saved result-stack suffix assembly remain governed by
    RholangPreparationReservation and RholangWorklistStorage; this file adds
    no second budget, evaluator, allocator model, or full-Rust proof. *)
From Stdlib Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

Module BodyFirstOccurrence.

Section WorklistOrder.
Context {Node Event : Type}.
Inductive Frame := Visit (node : Node) | Emit (event : Event).
Variable expand : Node -> list Frame.

Inductive Run : list Frame -> list Event -> Prop :=
| Done : Run [] []
| Enter : forall node rest trace,
    Run (expand node ++ rest) trace -> Run (Visit node :: rest) trace
| Output : forall event rest trace,
    Run rest trace -> Run (Emit event :: rest) (event :: trace).

(** Extending the pending work executes its suffix only after the exact first
    trace. No sorting, set quotient, or deduplication occurs. *)
Theorem run_append : forall first trace,
  Run first trace -> forall rest suffix,
  Run rest suffix -> Run (first ++ rest) (trace ++ suffix).
Proof.
  intros first trace H. induction H; intros tail suffix T; cbn.
  - exact T.
  - apply Enter. rewrite app_assoc. now apply IHRun.
  - apply Output. now apply IHRun.
Qed.

Theorem children_precede_emission : forall node children event rest before after,
  expand node = children ++ [Emit event] ->
  Run children before -> Run rest after ->
  Run (Visit node :: rest) (before ++ event :: after).
Proof.
  intros node children event rest before after EXP CHILD REST.
  apply Enter. rewrite EXP, <- app_assoc. cbn.
  apply run_append; [exact CHILD | now apply Output].
Qed.

(** Empty-event expansion covers names and sugar; an opaque binder uses no
    children either. The premises are concrete source scheduling witnesses. *)
Theorem transparent_expansion : forall node children rest before after,
  expand node = children -> Run children before -> Run rest after ->
  Run (Visit node :: rest) (before ++ after).
Proof. intros. apply Enter. rewrite H. now apply run_append. Qed.

Theorem opaque_node_preserves_remaining_trace : forall node rest trace,
  expand node = [] -> Run rest trace -> Run (Visit node :: rest) trace.
Proof. intros. apply Enter. now rewrite H. Qed.

Theorem shared_events_are_not_deduplicated : forall event,
  Run [Emit event; Emit event] [event; event].
Proof. intros. repeat constructor. Qed.
End WorklistOrder.

Section FirstOccurrence.
Context {Event : Type}.

Fixpoint seek (predicate : Event -> bool) (events : list Event)
    : option (list Event * Event * list Event) :=
  match events with
  | [] => None
  | event :: rest =>
      if predicate event then Some ([], event, rest)
      else match seek predicate rest with
           | None => None
           | Some (prefix, found, suffix) => Some (event :: prefix, found, suffix)
           end
  end.

Theorem seek_records_exact_first_position : forall predicate events prefix found suffix,
  seek predicate events = Some (prefix, found, suffix) ->
  events = prefix ++ found :: suffix /\ predicate found = true /\
  Forall (fun event => predicate event = false) prefix.
Proof.
  intros predicate events. induction events as [|event rest IH];
    intros prefix found suffix H; cbn in H; [discriminate |].
  destruct (predicate event) eqn:P.
  - inversion H; subst. cbn. repeat split; auto.
  - destruct (seek predicate rest) as [[[pre chosen] post]|] eqn:S;
      [|discriminate]. inversion H; subst.
    specialize (IH pre found suffix eq_refl).
    destruct IH as [SAME [YES BEFORE]]. cbn. split.
    + now rewrite SAME.
    + split; [exact YES | now constructor].
Qed.

Theorem seek_from_first_position : forall predicate prefix found suffix,
  Forall (fun event => predicate event = false) prefix ->
  predicate found = true ->
  seek predicate (prefix ++ found :: suffix) = Some (prefix, found, suffix).
Proof.
  intros predicate prefix found suffix BEFORE YES.
  induction BEFORE; cbn; [now rewrite YES | now rewrite H, IHBEFORE].
Qed.

Theorem seek_none_means_every_occurrence_rejected : forall predicate events,
  seek predicate events = None <->
  Forall (fun event => predicate event = false) events.
Proof.
  intros predicate events. induction events as [|event rest IH]; cbn.
  - split; auto.
  - destruct (predicate event) eqn:P.
    + split; [discriminate | intros H; inversion H; congruence].
    + split.
      * destruct (seek predicate rest) as [[[pre found] suffix]|] eqn:S;
          [discriminate |]. intros _. constructor; [exact P | now apply IH].
      * intros H. inversion H; subst. apply IH in H3. now rewrite H3.
Qed.

Fixpoint replace_first (predicate : Event -> bool) (replacement : Event)
    (events : list Event) : list Event :=
  match events with
  | [] => []
  | event :: rest => if predicate event then replacement :: rest
                     else event :: replace_first predicate replacement rest
  end.

Theorem replace_exactly_first_position : forall predicate prefix found suffix replacement,
  Forall (fun event => predicate event = false) prefix ->
  predicate found = true ->
  replace_first predicate replacement (prefix ++ found :: suffix) =
    prefix ++ replacement :: suffix.
Proof.
  intros predicate prefix found suffix replacement BEFORE YES.
  induction BEFORE; cbn; [now rewrite YES | now rewrite H, IHBEFORE].
Qed.

Theorem replacement_preserves_occurrence_count : forall predicate replacement events,
  length (replace_first predicate replacement events) = length events.
Proof.
  intros predicate replacement events. induction events; cbn; auto.
  destruct (predicate a); cbn; congruence.
Qed.

Section IdentitySynchronization.
Context {Key : Type}.
Variable key : Event -> Key.
Variable key_eq_dec : forall left right : Key, {left = right} + {left <> right}.
Variable eligible : Event -> bool.

Definition matches_target (target event : Event) : bool :=
  if key_eq_dec (key event) (key target) then true else false.

(** Fixed immutable Arc content and fixed selector environment establish this
    extensionality premise. Equality is pointer identity, not printed syntax. *)
Theorem first_eligible_has_no_earlier_target_key :
  (forall left right, key left = key right -> eligible left = eligible right) ->
  forall events prefix found suffix,
  seek eligible events = Some (prefix, found, suffix) ->
  Forall (fun event => matches_target found event = false) prefix.
Proof.
  intros EXT events prefix found suffix FOUND.
  apply seek_records_exact_first_position in FOUND.
  destruct FOUND as [_ [YES BEFORE]].
  eapply Forall_impl; [|exact BEFORE]. intros event NO.
  unfold matches_target. destruct (key_eq_dec (key event) (key found)) as [EQ|NE];
    [|reflexivity]. specialize (EXT event found EQ). congruence.
Qed.

Theorem finder_and_pointer_replacer_select_same_occurrence :
  (forall left right, key left = key right -> eligible left = eligible right) ->
  forall events prefix found suffix replacement,
  seek eligible events = Some (prefix, found, suffix) ->
  seek (matches_target found) events = Some (prefix, found, suffix) /\
  replace_first (matches_target found) replacement events =
    prefix ++ replacement :: suffix.
Proof.
  intros EXT events prefix found suffix replacement FOUND.
  pose proof (first_eligible_has_no_earlier_target_key EXT events prefix found suffix FOUND)
    as BEFORE.
  apply seek_records_exact_first_position in FOUND. destruct FOUND as [SAME _].
  assert (YES : matches_target found found = true).
  { unfold matches_target. destruct (key_eq_dec (key found) (key found)); congruence. }
  rewrite SAME. split.
  - now apply seek_from_first_position.
  - now apply replace_exactly_first_position.
Qed.

Theorem later_shared_arc_occurrence_is_untouched : forall prefix found between suffix replacement,
  Forall (fun event => matches_target found event = false) prefix ->
  replace_first (matches_target found) replacement
    (prefix ++ found :: between ++ found :: suffix) =
    prefix ++ replacement :: between ++ found :: suffix.
Proof.
  intros. apply replace_exactly_first_position; [assumption |].
  unfold matches_target. destruct (key_eq_dec (key found) (key found)); congruence.
Qed.
End IdentitySynchronization.
End FirstOccurrence.

(** Distinct positions with the same key are retained, while an earlier
    ineligible distinct key is not accidentally selected. *)
Example occurrence_identity_example :
  seek (fun event : nat * nat => Nat.eqb (fst event) 7)
    [(3, 0); (7, 1); (7, 2)] = Some ([(3, 0)], (7, 1), [(7, 2)]).
Proof. reflexivity. Qed.

Example shared_key_replacement_example :
  replace_first (fun event : nat * nat => Nat.eqb (fst event) 7) (9, 1)
    [(3, 0); (7, 1); (7, 2)] = [(3, 0); (9, 1); (7, 2)].
Proof. reflexivity. Qed.

End BodyFirstOccurrence.
