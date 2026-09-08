(** Owned extraction and late guard binding for the existing contract producer.
    Terms and random states are opaque values: no syntax traversal, evaluation,
    hashing or regenerated random state is modeled. Rust buffer ownership and
    absence of cloning need allocation-identity tests in addition to these laws.
    Publication reuses GuardedReplyPublication, including its explicit limits. *)
From Stdlib Require Import List Bool.
From RuntimeGrammar Require Import GuardedReplyPublication.
Import ListNotations.

Module OwnedContractCall.
Module G := GuardedReplyPublication.GuardedReplyPublication.

Section Owned.
Context {Term Random : Type}.

Record Datum := { payload : list Term; random_state : Random }.
Record Arguments := { messages : list Datum; replay : bool; previous : list Term }.
Record Split := {
  retained_random : Random;
  retained_replay : bool;
  retained_previous : list Term;
  request : list Term
}.

Definition split_owned args :=
  match messages args with
  | [datum] => Some {| retained_random := random_state datum;
      retained_replay := replay args; retained_previous := previous args;
      request := payload datum |}
  | _ => None
  end.

Theorem split_accepts_exactly_one_message : forall args,
  (exists result, split_owned args = Some result) <-> length (messages args) = 1.
Proof.
  intros [messages replay previous]. destruct messages as [|d [|e rest]]; cbn.
  - split; [intros [result H]; discriminate | discriminate].
  - split; [intros; reflexivity | intros; eexists; reflexivity].
  - split; [intros [result H]; discriminate | discriminate].
Qed.

Theorem split_preserves_all_fields : forall terms random replay previous,
  split_owned {| messages := [{| payload := terms; random_state := random |}];
                 replay := replay; previous := previous |} =
  Some {| retained_random := random; retained_replay := replay;
          retained_previous := previous; request := terms |}.
Proof. reflexivity. Qed.

Definition reconstruct result :=
  {| messages := [{| payload := request result; random_state := retained_random result |}];
     replay := retained_replay result; previous := retained_previous result |}.

Theorem split_has_an_exact_inverse_on_accepted_arguments : forall args result,
  split_owned args = Some result -> reconstruct result = args.
Proof.
  intros [messages replay previous] result H.
  destruct messages as [|[terms random] [|extra rest]]; cbn in H; try discriminate.
  inversion H; reflexivity.
Qed.

Record Reply := { values : list Term; channel : Term; caller_random : Random }.
Definition prepare_reply context output target :=
  {| values := output; channel := target; caller_random := retained_random context |}.

Theorem reply_preserves_values_channel_and_random : forall context output target,
  values (prepare_reply context output target) = output /\
  channel (prepare_reply context output target) = target /\
  caller_random (prepare_reply context output target) = retained_random context.
Proof. intros; repeat split; reflexivity. Qed.

(** Binding a guard captures a capability but does not acquire its lock or run
    its authorization check. The supplied entry here is the live entry when the
    existing publication machine is actually polled, not when the closure forms. *)
Definition publish_owned context output target handle rights mutation events entry host :=
  G.run handle rights (mutation (prepare_reply context output target)) events
    (G.initial entry host).

Theorem owned_publication_is_the_same_host_execution :
  forall context output target handle rights mutation events entry host,
  publish_owned context output target handle rights mutation events entry host =
  G.run handle rights (mutation
    {| values := output; channel := target; caller_random := retained_random context |})
    events (G.initial entry host).
Proof. reflexivity. Qed.

Theorem late_revocation_preserves_the_host :
  forall context output target handle rights mutation entry host,
  publish_owned context output target handle rights mutation
    [G.RevokeAuthority; G.AcquireAuthority] entry host =
  Some {| G.phase := G.Refused; G.authority := InstalledLanguageAuthority.revoke entry;
          G.host := host; G.mutation_count := 0 |}.
Proof. intros. apply G.revoke_before_guard_refuses_even_a_prepared_reply. Qed.

Theorem owned_publication_mutates_at_most_once :
  forall context output target handle rights mutation events entry host after,
  publish_owned context output target handle rights mutation events entry host = Some after ->
  G.mutation_count after <= 1.
Proof. intros. eapply G.every_execution_mutates_at_most_once; eauto. Qed.

Theorem borrowed_value_wrapper_preserves_execution :
  forall context output target handle rights mutation events entry host,
  publish_owned context (map (fun term => term) output) target handle rights mutation events entry host =
  publish_owned context output target handle rights mutation events entry host.
Proof. intros. now rewrite map_id. Qed.

End Owned.
End OwnedContractCall.

Print Assumptions OwnedContractCall.split_accepts_exactly_one_message.
Print Assumptions OwnedContractCall.split_preserves_all_fields.
Print Assumptions OwnedContractCall.split_has_an_exact_inverse_on_accepted_arguments.
Print Assumptions OwnedContractCall.reply_preserves_values_channel_and_random.
Print Assumptions OwnedContractCall.owned_publication_is_the_same_host_execution.
Print Assumptions OwnedContractCall.late_revocation_preserves_the_host.
Print Assumptions OwnedContractCall.owned_publication_mutates_at_most_once.
Print Assumptions OwnedContractCall.borrowed_value_wrapper_preserves_execution.
