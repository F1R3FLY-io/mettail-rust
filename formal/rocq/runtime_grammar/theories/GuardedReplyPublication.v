(** Control refinement for the host's one-shot reply publication boundary.

    The host state explicitly includes the storage, log, counters and replay
    projections which must remain unchanged on authorization refusal. The
    mutation is a parameter, not an assumed-correct RSpace implementation:
    these laws hold for every mutation function. Candidate selection, the
    detailed COMM update, Rust lock correctness and callback termination need
    separate source correspondence and tests. In particular these laws do
    not assert rollback of receiver effects or atomicity against every reader.

    Preparation and asynchronous channel-lock acquisition precede this
    machine. Its authority-held phases contain neither await nor callbacks.
    Revocation may interleave before acquisition or after release, never while
    the authority read guard is held. Callback transitions mark invocation;
    their arbitrary effects are outside the publication transaction.
*)
From Stdlib Require Import List Bool PeanoNat Lia.
From RuntimeGrammar Require Import CapabilitySeparation InstalledLanguageAuthority.
Import ListNotations.

Module GuardedReplyPublication.

Definition rights_contained (child parent : list LanguageRight) : bool :=
  forallb (fun right => has_language_right right parent) child.

Lemma rights_contained_correct : forall child parent,
  rights_contained child parent = true <-> language_attenuates child parent.
Proof.
  intros child parent. unfold rights_contained, language_attenuates.
  rewrite forallb_forall. split.
  - intros H right Hin. apply has_language_right_sound, H, Hin.
  - intros H right Hin. apply has_language_right_complete, H, Hin.
Qed.

Definition authorized (entry : InstalledEntry) (handle : InstalledHandle)
    (rights : list LanguageRight) : bool :=
  entry_live entry &&
  Nat.eqb (handle_generation handle) (entry_generation entry) &&
  Nat.eqb (handle_commitment handle) (entry_commitment entry) &&
  Nat.eqb (handle_seal handle) (entry_seal entry) &&
  rights_contained (handle_rights handle) (entry_ceiling entry) &&
  rights_contained rights (handle_rights handle).

Theorem authorized_correct : forall entry handle rights,
  authorized entry handle rights = true <-> authorize_all entry handle rights.
Proof.
  intros entry handle rights.
  unfold authorized, authorize_all, handle_valid.
  repeat rewrite andb_true_iff. repeat rewrite Nat.eqb_eq.
  repeat rewrite rights_contained_correct.
  unfold language_attenuates. tauto.
Qed.

Theorem revoked_authority_is_refused : forall entry handle rights,
  authorized (revoke entry) handle rights = false.
Proof. reflexivity. Qed.

Record HostState := {
  stored_data : list nat;
  waiting_continuations : list nat;
  channel_joins : list (nat * nat);
  event_log : list nat;
  produce_counters : list (nat * nat);
  replay_bindings : list (nat * nat);
  caller_random_state : list nat
}.

Inductive Phase :=
| Prepared | AuthorityHeld | MutationApplied | Released
| ObserverInvoked | ReceiverInvoked | Refused.

Record Machine := {
  phase : Phase;
  authority : InstalledEntry;
  host : HostState;
  mutation_count : nat
}.

Inductive Event :=
| AcquireAuthority | ApplyMutation | ReleaseAuthority
| InvokeObserver | InvokeReceiver | RevokeAuthority.

Definition holds_authority (p : Phase) : bool :=
  match p with AuthorityHeld | MutationApplied => true | _ => false end.

Definition initial (entry : InstalledEntry) (state : HostState) : Machine :=
  {| phase := Prepared; authority := entry; host := state; mutation_count := 0 |}.

Definition with_phase (m : Machine) (p : Phase) : Machine :=
  {| phase := p; authority := authority m; host := host m;
     mutation_count := mutation_count m |}.

Definition advance (handle : InstalledHandle) (rights : list LanguageRight)
    (mutation : HostState -> HostState) (event : Event) (m : Machine)
    : option Machine :=
  match event with
  | RevokeAuthority =>
      if holds_authority (phase m) then None else
      Some {| phase := phase m; authority := revoke (authority m);
              host := host m; mutation_count := mutation_count m |}
  | AcquireAuthority =>
      match phase m with
      | Prepared => Some (with_phase m
          (if authorized (authority m) handle rights
           then AuthorityHeld else Refused))
      | _ => None
      end
  | ApplyMutation =>
      match phase m with
      | AuthorityHeld => Some {| phase := MutationApplied;
          authority := authority m; host := mutation (host m);
          mutation_count := S (mutation_count m) |}
      | _ => None
      end
  | ReleaseAuthority =>
      match phase m with MutationApplied => Some (with_phase m Released)
      | _ => None end
  | InvokeObserver =>
      match phase m with Released => Some (with_phase m ObserverInvoked)
      | _ => None end
  | InvokeReceiver =>
      match phase m with ObserverInvoked => Some (with_phase m ReceiverInvoked)
      | _ => None end
  end.

Fixpoint run (handle : InstalledHandle) (rights : list LanguageRight)
    (mutation : HostState -> HostState) (events : list Event) (m : Machine)
    : option Machine :=
  match events with
  | [] => Some m
  | event :: rest =>
      match advance handle rights mutation event m with
      | None => None
      | Some next => run handle rights mutation rest next
      end
  end.

Definition phase_count (p : Phase) : nat :=
  match p with Prepared | AuthorityHeld | Refused => 0 | _ => 1 end.

Definition invariant (handle : InstalledHandle) (rights : list LanguageRight)
    (m : Machine) : Prop :=
  mutation_count m = phase_count (phase m) /\
  (holds_authority (phase m) = true ->
     authorize_all (authority m) handle rights).

Lemma initial_invariant : forall entry state handle rights,
  invariant handle rights (initial entry state).
Proof. intros. split; [reflexivity | discriminate]. Qed.

Lemma advance_preserves_invariant : forall handle rights mutation event before after,
  invariant handle rights before ->
  advance handle rights mutation event before = Some after ->
  invariant handle rights after.
Proof.
  intros handle rights mutation event [p entry state count] after [Hcount Hauth] Hstep.
  destruct event, p; cbn in Hstep, Hcount, Hauth; try discriminate;
    try (inversion Hstep; subst; split; [reflexivity | assumption]);
    try (inversion Hstep; subst; split; [reflexivity | discriminate]).
  destruct (authorized entry handle rights) eqn:Hcheck;
    inversion Hstep; subst; split; try reflexivity; try discriminate.
  intros _. now apply authorized_correct.
Qed.

Lemma run_preserves_invariant : forall events handle rights mutation before after,
  invariant handle rights before ->
  run handle rights mutation events before = Some after ->
  invariant handle rights after.
Proof.
  induction events as [|event rest IH]; intros handle rights mutation before after Hinv Hrun.
  - simpl in Hrun. inversion Hrun; subst. exact Hinv.
  - simpl in Hrun. destruct (advance handle rights mutation event before)
      as [next|] eqn:Hstep; try discriminate.
    eapply IH; [eapply advance_preserves_invariant; eauto | exact Hrun].
Qed.

Theorem every_execution_mutates_at_most_once :
  forall events handle rights mutation entry state after,
  run handle rights mutation events (initial entry state) = Some after ->
  mutation_count after <= 1.
Proof.
  intros events handle rights mutation entry state after Hrun.
  assert (Hinv : invariant handle rights after).
  { eapply run_preserves_invariant; [apply initial_invariant | exact Hrun]. }
  destruct Hinv as [Hcount _]. rewrite Hcount.
  destruct (phase after); simpl; lia.
Qed.

Theorem mutation_requires_live_authority_at_its_actual_boundary :
  forall events handle rights mutation entry state before after,
  run handle rights mutation events (initial entry state) = Some before ->
  advance handle rights mutation ApplyMutation before = Some after ->
  authorize_all (authority before) handle rights /\
  host after = mutation (host before).
Proof.
  intros events handle rights mutation entry state before after Hrun Hstep.
  assert (Hinv : invariant handle rights before).
  { eapply run_preserves_invariant; [apply initial_invariant | exact Hrun]. }
  destruct Hinv as [_ Hauth]. unfold advance in Hstep.
  destruct (phase before) eqn:Hphase; try discriminate.
  inversion Hstep; subst. split; [apply Hauth; reflexivity | reflexivity].
Qed.

Theorem refusal_preserves_every_host_projection :
  forall handle rights mutation entry state,
  authorized entry handle rights = false ->
  advance handle rights mutation AcquireAuthority (initial entry state) =
    Some {| phase := Refused; authority := entry; host := state; mutation_count := 0 |}.
Proof. intros handle rights mutation entry state H. cbn. now rewrite H. Qed.

Theorem refused_request_has_no_mutation_or_callback :
  forall handle rights mutation entry state event,
  event <> RevokeAuthority ->
  advance handle rights mutation event
    {| phase := Refused; authority := entry; host := state; mutation_count := 0 |} = None.
Proof. intros. destruct event; try reflexivity; contradiction. Qed.

Theorem authority_cannot_be_revoked_inside_mutation_boundary :
  forall handle rights mutation m,
  holds_authority (phase m) = true ->
  advance handle rights mutation RevokeAuthority m = None.
Proof. intros handle rights mutation m H. cbn. now rewrite H. Qed.

Theorem callbacks_cannot_run_under_authority_guard :
  forall handle rights mutation m,
  holds_authority (phase m) = true ->
  advance handle rights mutation InvokeObserver m = None /\
  advance handle rights mutation InvokeReceiver m = None.
Proof.
  intros handle rights mutation [p entry state count] H.
  destruct p; cbn in *; try discriminate; split; reflexivity.
Qed.

Definition publication_events :=
  [AcquireAuthority; ApplyMutation; ReleaseAuthority; InvokeObserver; InvokeReceiver].

Theorem authorized_publication_applies_exactly_the_supplied_mutation :
  forall handle rights mutation entry state,
  authorized entry handle rights = true ->
  run handle rights mutation publication_events (initial entry state) =
    Some {| phase := ReceiverInvoked; authority := entry;
            host := mutation state; mutation_count := 1 |}.
Proof. intros handle rights mutation entry state H. cbn. now rewrite H. Qed.

Theorem revoke_before_guard_refuses_even_a_prepared_reply :
  forall handle rights mutation entry state,
  run handle rights mutation [RevokeAuthority; AcquireAuthority] (initial entry state) =
    Some {| phase := Refused; authority := revoke entry;
            host := state; mutation_count := 0 |}.
Proof. reflexivity. Qed.

Theorem reentrant_revocation_after_release_is_allowed_without_republishing :
  forall handle rights mutation entry state,
  authorized entry handle rights = true ->
  run handle rights mutation
    [AcquireAuthority; ApplyMutation; ReleaseAuthority; RevokeAuthority;
     InvokeObserver; InvokeReceiver; RevokeAuthority] (initial entry state) =
    Some {| phase := ReceiverInvoked; authority := revoke (revoke entry);
            host := mutation state; mutation_count := 1 |}.
Proof. intros handle rights mutation entry state H. cbn. now rewrite H. Qed.

(** Replay candidate selection observes the count which the pending produce
    would create, without updating the shared counter before authorization.
    Produce identities are abstract naturals here, not datum positions: every
    repeated occurrence of the same source sees the same virtual increment. *)
Definition Counter := nat -> nat.

Definition increment_counter (counter : Counter) (source : nat) : Counter :=
  fun queried => if Nat.eqb queried source then S (counter queried) else counter queried.

Definition pending_counter (counter : Counter) (source : nat) (persist : bool)
    (queried : nat) : nat :=
  if persist then counter queried else
  if Nat.eqb queried source then S (counter queried) else counter queried.

Definition committed_counter (counter : Counter) (source : nat) (persist : bool)
    : Counter :=
  if persist then counter else increment_counter counter source.

Theorem replay_pending_count_equals_postcommit_count :
  forall counter source persist queried,
  pending_counter counter source persist queried =
    committed_counter counter source persist queried.
Proof. intros. destruct persist; reflexivity. Qed.

Theorem replay_candidate_repeat_test_is_preserved :
  forall counter source persist queried recorded,
  Nat.eqb recorded (pending_counter counter source persist queried) =
    Nat.eqb recorded (committed_counter counter source persist queried).
Proof. intros. now rewrite replay_pending_count_equals_postcommit_count. Qed.

Theorem pending_increment_covers_every_equal_source_occurrence :
  forall counter source first second,
  first = source -> second = source ->
  pending_counter counter source false first = S (counter source) /\
  pending_counter counter source false second = S (counter source).
Proof. intros counter source first second -> ->. cbn. rewrite Nat.eqb_refl. auto. Qed.

Theorem pending_increment_preserves_every_other_source :
  forall counter source queried persist,
  queried <> source -> pending_counter counter source persist queried = counter queried.
Proof.
  intros counter source queried persist Hneq. unfold pending_counter.
  destruct persist; [reflexivity |]. apply Nat.eqb_neq in Hneq. now rewrite Hneq.
Qed.

Print Assumptions authorized_correct.
Print Assumptions revoked_authority_is_refused.
Print Assumptions every_execution_mutates_at_most_once.
Print Assumptions mutation_requires_live_authority_at_its_actual_boundary.
Print Assumptions refusal_preserves_every_host_projection.
Print Assumptions refused_request_has_no_mutation_or_callback.
Print Assumptions authority_cannot_be_revoked_inside_mutation_boundary.
Print Assumptions callbacks_cannot_run_under_authority_guard.
Print Assumptions authorized_publication_applies_exactly_the_supplied_mutation.
Print Assumptions revoke_before_guard_refuses_even_a_prepared_reply.
Print Assumptions reentrant_revocation_after_release_is_allowed_without_republishing.
Print Assumptions replay_pending_count_equals_postcommit_count.
Print Assumptions replay_candidate_repeat_test_is_preserved.
Print Assumptions pending_increment_covers_every_equal_source_occurrence.
Print Assumptions pending_increment_preserves_every_other_source.

End GuardedReplyPublication.
