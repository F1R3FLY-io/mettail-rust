From Stdlib Require Import List Bool PeanoNat Lia.
From RuntimeGrammar Require Import TheoremChannel BoundedAdmissionChecker.
Import ListNotations.

(** The Rholang-facing theorem service is a capability router around the
    source-neutral theorem-channel kernel.  It deliberately stores no tuple-
    space messages: preparation computes a checked, matcher-owned capture
    transaction and commit merely publishes that transaction's result after
    revalidating the channel epoch.  Persistent storage remains the concern of
    a later Reified-RSpace adapter. *)

Record ServicePolicy : Type := {
  policy_produce : bool;
  policy_consume : bool;
  policy_max_work : nat;
  policy_max_evidence : nat;
  policy_max_cache : nat
}.

Record OpenRequest : Type := {
  request_produce : bool;
  request_consume : bool;
  request_work : nat;
  request_evidence : nat;
  request_cache : nat
}.

Record EffectiveChannel : Type := {
  effective_produce : bool;
  effective_consume : bool;
  effective_budget : AdmissionBudget;
  effective_cache : nat
}.

Definition attenuate_bool (host requested : bool) : bool := host && requested.

Definition request_within_policy
    (policy : ServicePolicy) (request : OpenRequest) : bool :=
  (request_work request <=? policy_max_work policy) &&
  (request_evidence request <=? policy_max_evidence policy) &&
  (request_cache request <=? policy_max_cache policy).

Definition effective_rights_nonempty
    (policy : ServicePolicy) (request : OpenRequest) : bool :=
  attenuate_bool (policy_produce policy) (request_produce request) ||
  attenuate_bool (policy_consume policy) (request_consume request).

Definition open_channel
    (policy : ServicePolicy) (request : OpenRequest) : option EffectiveChannel :=
  if request_within_policy policy request &&
     effective_rights_nonempty policy request
  then Some
    {| effective_produce := attenuate_bool
         (policy_produce policy) (request_produce request);
       effective_consume := attenuate_bool
         (policy_consume policy) (request_consume request);
       effective_budget :=
         {| budget_work_units := request_work request;
            budget_evidence_bytes := request_evidence request |};
       effective_cache := request_cache request |}
  else None.

Theorem opened_channel_cannot_amplify_produce :
  forall policy request channel,
    open_channel policy request = Some channel ->
    effective_produce channel = true -> policy_produce policy = true.
Proof.
  intros policy request channel Hopen Hproduce.
  unfold open_channel in Hopen.
  destruct (request_within_policy policy request &&
            effective_rights_nonempty policy request); [| discriminate].
  inversion Hopen; subst. unfold attenuate_bool in Hproduce.
  apply andb_true_iff in Hproduce as [Hhost _]. exact Hhost.
Qed.

Theorem opened_channel_cannot_amplify_consume :
  forall policy request channel,
    open_channel policy request = Some channel ->
    effective_consume channel = true -> policy_consume policy = true.
Proof.
  intros policy request channel Hopen Hconsume.
  unfold open_channel in Hopen.
  destruct (request_within_policy policy request &&
            effective_rights_nonempty policy request); [| discriminate].
  inversion Hopen; subst. unfold attenuate_bool in Hconsume.
  apply andb_true_iff in Hconsume as [Hhost _]. exact Hhost.
Qed.

Theorem opened_channel_resources_are_policy_bounded :
  forall policy request channel,
    open_channel policy request = Some channel ->
    budget_work_units (effective_budget channel) <= policy_max_work policy /\
    budget_evidence_bytes (effective_budget channel) <= policy_max_evidence policy /\
    effective_cache channel <= policy_max_cache policy.
Proof.
  intros policy request channel Hopen.
  unfold open_channel in Hopen.
  destruct (request_within_policy policy request &&
            effective_rights_nonempty policy request) eqn:Hadmitted;
    [| discriminate].
  inversion Hopen; subst; simpl.
  apply andb_true_iff in Hadmitted as [Hbounds _].
  unfold request_within_policy in Hbounds.
  repeat rewrite andb_true_iff in Hbounds.
  destruct Hbounds as [[Hwork Hevidence] Hcache].
  repeat split; apply Nat.leb_le; assumption.
Qed.

(** Channel and transaction capabilities occupy disjoint constructors in the
    abstract model.  The Rust wire realizes this sum with distinct, framed
    private-name domains. *)
Inductive ServiceToken : Type :=
| ChannelToken : nat -> ServiceToken
| TransactionToken : nat -> ServiceToken.

Theorem channel_and_transaction_tokens_are_disjoint :
  forall channel transaction,
    ChannelToken channel <> TransactionToken transaction.
Proof. discriminate. Qed.

Record LiveChannel : Type := {
  live_token : ServiceToken;
  live_epoch : nat;
  live_rights : EffectiveChannel
}.

Record PreparedExchange : Type := {
  prepared_channel_token : ServiceToken;
  prepared_epoch : nat;
  prepared_captures : CaptureEnvironment
}.

Inductive PrepareResult : Type :=
| Prepared : PreparedExchange -> PrepareResult
| PrepareRefused : PrepareResult
| PrepareExhausted : PrepareResult.

(** [structural_match] represents exact language/category/pattern admission and
    matcher-owned capture derivation.  A caller supplies neither captures nor a
    Boolean override; the production adapter computes both before invoking this
    transition. *)
Definition prepare_exchange
    (channel : LiveChannel) (decision : AdmissionDecision)
    (structural_match : option CaptureEnvironment) : PrepareResult :=
  if effective_produce (live_rights channel) &&
     effective_consume (live_rights channel)
  then match decision, structural_match with
       | Proven _, Some captures =>
           Prepared
             {| prepared_channel_token := live_token channel;
                prepared_epoch := live_epoch channel;
                prepared_captures := captures |}
       | Undetermined, _ => PrepareExhausted
       | _, _ => PrepareRefused
       end
  else PrepareRefused.

Theorem refuted_prepare_publishes_no_transaction :
  forall channel captures transaction,
    prepare_exchange channel Refuted captures <> Prepared transaction.
Proof.
  intros. unfold prepare_exchange.
  destruct (effective_produce (live_rights channel) &&
            effective_consume (live_rights channel)); discriminate.
Qed.

Theorem exhausted_prepare_publishes_no_transaction :
  forall channel captures transaction,
    prepare_exchange channel Undetermined captures <> Prepared transaction.
Proof.
  intros. unfold prepare_exchange.
  destruct (effective_produce (live_rights channel) &&
            effective_consume (live_rights channel)); discriminate.
Qed.

Theorem unmatched_prepare_publishes_no_transaction :
  forall channel certificate transaction,
    prepare_exchange channel (Proven certificate) None <> Prepared transaction.
Proof.
  intros. unfold prepare_exchange.
  destruct (effective_produce (live_rights channel) &&
            effective_consume (live_rights channel)); discriminate.
Qed.

Definition token_beq (left right : ServiceToken) : bool :=
  match left, right with
  | ChannelToken l, ChannelToken r
  | TransactionToken l, TransactionToken r => Nat.eqb l r
  | _, _ => false
  end.

Definition checked_commit
    (channel : LiveChannel) (transaction : PreparedExchange)
    : option CaptureEnvironment :=
  if token_beq
       (live_token channel) (prepared_channel_token transaction) &&
     Nat.eqb (live_epoch channel) (prepared_epoch transaction) &&
     effective_produce (live_rights channel) &&
     effective_consume (live_rights channel)
  then Some (prepared_captures transaction)
  else None.

(** Each transaction-directory entry is a linear cell.  The Rust service
    realizes a directory as a finite map and removes the selected entry before
    kernel revalidation; this per-key model proves that no result, successful
    or stale, leaves the same authority available for a second attempt. *)
Definition take_transaction
    (slot : option PreparedExchange)
    : option PreparedExchange * option PreparedExchange :=
  match slot with
  | Some transaction => (Some transaction, None)
  | None => (None, None)
  end.

Theorem transaction_capability_is_consumed_linearly :
  forall slot first remainder second final,
    take_transaction slot = (first, remainder) ->
    take_transaction remainder = (second, final) ->
    first <> None ->
    second = None /\ final = None.
Proof.
  intros slot first remainder second final Hfirst Hsecond Hpresent.
  destruct slot as [transaction |]; simpl in Hfirst.
  - inversion Hfirst; subst. simpl in Hsecond. inversion Hsecond. auto.
  - inversion Hfirst; subst. contradiction.
Qed.

Definition revoke_channel (channel : LiveChannel) : LiveChannel :=
  {| live_token := live_token channel;
     live_epoch := S (live_epoch channel);
     live_rights :=
       {| effective_produce := false;
          effective_consume := false;
          effective_budget := effective_budget (live_rights channel);
          effective_cache := effective_cache (live_rights channel) |} |}.

Theorem revoke_invalidates_every_prepared_exchange :
  forall channel transaction,
    checked_commit (revoke_channel channel) transaction = None.
Proof.
  intros channel transaction.
  unfold checked_commit, revoke_channel; simpl.
  repeat rewrite andb_false_r. reflexivity.
Qed.

Theorem successful_commit_returns_exact_matcher_captures :
  forall channel transaction captures,
    checked_commit channel transaction = Some captures ->
    captures = prepared_captures transaction.
Proof.
  intros channel transaction captures Hcommit.
  unfold checked_commit in Hcommit.
  destruct
    (token_beq (live_token channel) (prepared_channel_token transaction) &&
     Nat.eqb (live_epoch channel) (prepared_epoch transaction) &&
     effective_produce (live_rights channel) &&
     effective_consume (live_rights channel)); [| discriminate].
  inversion Hcommit. reflexivity.
Qed.

Print Assumptions opened_channel_cannot_amplify_produce.
Print Assumptions opened_channel_cannot_amplify_consume.
Print Assumptions opened_channel_resources_are_policy_bounded.
Print Assumptions channel_and_transaction_tokens_are_disjoint.
Print Assumptions refuted_prepare_publishes_no_transaction.
Print Assumptions exhausted_prepare_publishes_no_transaction.
Print Assumptions unmatched_prepare_publishes_no_transaction.
Print Assumptions transaction_capability_is_consumed_linearly.
Print Assumptions revoke_invalidates_every_prepared_exchange.
Print Assumptions successful_commit_returns_exact_matcher_captures.
