(*
 * LookaheadTraceDelivery: the wire-shape obligations for complete lookahead
 * provenance paths.
 *
 * A reduction trace publishes the submitted process, the administratively
 * saturated initial configuration, and every successor configuration.  A
 * digest names a retained path; it is not a substitute for any process node.
 * Success reports retain the complete path positionally, while the aggregate
 * delivery places that same path in a set-valued PathMap carrier.
 *
 * Production correspondence:
 *
 *   ReductionTrace::processes       rholang-runtime/src/speculation.rs
 *   service::trace_list             rholang-runtime/src/speculation/service.rs
 *   delivery::success_entry         rholang-runtime/src/speculation/delivery.rs
 *   delivery::trace_pathmap         rholang-runtime/src/speculation/delivery.rs
 *   service::truncated_datum        rholang-runtime/src/speculation/service.rs
 *
 * The model is constructive and finite.  It has no axioms, admitted results,
 * classical choice, or recursive native-stack assumption.
 *)

From Stdlib Require Import List Lia.
Import ListNotations.

Section CompleteProcessTrace.
  Context {Process Digest : Type}.

  Inductive WireNode : Type :=
  | ProcessNode : Process -> WireNode
  | DigestNode : Digest -> WireNode.

  Record ReductionTrace : Type := {
    submitted_input : Process;
    saturated_initial : Process;
    successor_configurations : list Process
  }.

  Definition process_path (trace : ReductionTrace) : list Process :=
    submitted_input trace
      :: saturated_initial trace
      :: successor_configurations trace.

  Definition published_trace (trace : ReductionTrace) : list WireNode :=
    map ProcessNode (process_path trace).

  Definition trace_terminal (trace : ReductionTrace) : Process :=
    last (process_path trace) (saturated_initial trace).

  Definition SuccessReport : Type := (list WireNode * list Process)%type.

  Definition success_report
      (trace : ReductionTrace) (terms : list Process) : SuccessReport :=
    (published_trace trace, terms).

  (** A set-mode PathMap is modeled extensionally by membership.  Trie layout,
      prefix sharing, and enumeration order are representation choices; set
      membership is the semantic interface the delivery contract consumes. *)
  Definition PathSet : Type := list Process -> Prop.

  Definition success_delivery (trace : ReductionTrace) : PathSet :=
    fun candidate => candidate = process_path trace.

  Definition truncated_handle (digest : Digest) : WireNode :=
    DigestNode digest.

  Theorem published_trace_starts_with_submitted_input :
    forall trace,
      hd_error (published_trace trace) =
        Some (ProcessNode (submitted_input trace)).
  Proof.
    intros trace. reflexivity.
  Qed.

  Lemma last_map_nonempty :
    forall (values : list Process) (default_process : Process)
           (default_wire : WireNode),
      values <> [] ->
      last (map ProcessNode values) default_wire =
        ProcessNode (last values default_process).
  Proof.
    induction values as [|head tail IH]; intros default_process default_wire Hnonempty.
    - contradiction.
    - destruct tail as [|next rest].
      + reflexivity.
      + simpl. apply IH. discriminate.
  Qed.

  Theorem published_trace_ends_with_terminal_configuration :
    forall trace,
      last (published_trace trace)
        (ProcessNode (saturated_initial trace)) =
      ProcessNode (trace_terminal trace).
  Proof.
    intros trace.
    unfold published_trace, trace_terminal.
    apply last_map_nonempty.
    unfold process_path. discriminate.
  Qed.

  Theorem published_trace_has_two_roots_and_every_successor :
    forall trace,
      length (published_trace trace) =
        2 + length (successor_configurations trace).
  Proof.
    intros trace.
    unfold published_trace, process_path.
    rewrite length_map. simpl. lia.
  Qed.

  Theorem success_report_retains_the_complete_process_path :
    forall trace terms,
      fst (success_report trace terms) =
        map ProcessNode (process_path trace).
  Proof.
    reflexivity.
  Qed.

  Theorem success_delivery_contains_the_complete_process_path :
    forall trace,
      success_delivery trace (process_path trace).
  Proof.
    intros trace. reflexivity.
  Qed.

  Theorem success_delivery_contains_only_the_complete_process_path :
    forall trace candidate,
      success_delivery trace candidate ->
      candidate = process_path trace.
  Proof.
    intros trace candidate Hmember. exact Hmember.
  Qed.

  Theorem published_trace_never_substitutes_a_digest_for_a_process :
    forall trace digest,
      ~ In (DigestNode digest) (published_trace trace).
  Proof.
    intros trace digest Hin.
    unfold published_trace in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [process [Hequal _]].
    discriminate Hequal.
  Qed.

  Theorem truncated_handle_is_a_name_not_a_trace_node :
    forall trace digest,
      truncated_handle digest = DigestNode digest /\
      ~ In (truncated_handle digest) (published_trace trace).
  Proof.
    intros trace digest. split.
    - reflexivity.
    - apply published_trace_never_substitutes_a_digest_for_a_process.
  Qed.
End CompleteProcessTrace.

(** The v2 reply is one RSpace datum with exactly two payloads.  Rendering
    every branch is a prerequisite for constructing either PathMap; a failed
    render or a failed publication guard leaves the reply channel untouched.
    The separate, version-tagged truncation report never changes this arity. *)
Section CompletePathMapReply.
  Context {Entry : Type}.

  Definition PathMapName : Type := Entry -> Prop.

  Fixpoint render_all (leaves : list (option Entry)) : option (list Entry) :=
    match leaves with
    | [] => Some []
    | Some entry :: rest =>
        match render_all rest with
        | Some entries => Some (entry :: entries)
        | None => None
        end
    | None :: _ => None
    end.

  Definition pathmap_name (entries : list Entry) : PathMapName :=
    fun candidate => In candidate entries.

  Definition prepare_reply
      (success failure : list (option Entry))
      : option (PathMapName * PathMapName) :=
    match render_all success, render_all failure with
    | Some successes, Some failures =>
        Some (pathmap_name successes, pathmap_name failures)
    | _, _ => None
    end.

  (** A single produce receives the whole payload vector.  This is the public
      reply's atomic unit, not two independent one-payload sends. *)
  Definition publish_reply
      (guard_admits : bool) (success failure : list (option Entry))
      : option (list PathMapName) :=
    if guard_admits then
      match prepare_reply success failure with
      | Some (success_name, failure_name) =>
          Some [success_name; failure_name]
      | None => None
      end
    else None.

  Record VersionedTruncation : Type := {
    truncation_version : nat;
    truncated_name : PathMapName
  }.

  Definition internal_truncation_v2 (entries : list Entry)
      : VersionedTruncation :=
    {| truncation_version := 2;
       truncated_name := pathmap_name entries |}.

  Lemma render_all_preserves_branch_count :
    forall leaves entries,
      render_all leaves = Some entries -> length entries = length leaves.
  Proof.
    induction leaves as [|[entry|] rest IH]; intros entries Hrender.
    - inversion Hrender. reflexivity.
    - simpl in Hrender. destruct (render_all rest) as [tail|] eqn:Htail;
        try discriminate.
      inversion Hrender; subst. simpl. f_equal. apply IH. reflexivity.
    - discriminate Hrender.
  Qed.

  Theorem published_reply_has_exactly_two_pathmap_names :
    forall guard success failure payloads,
      publish_reply guard success failure = Some payloads ->
      length payloads = 2.
  Proof.
    intros guard success failure payloads Hpublished.
    unfold publish_reply in Hpublished.
    destruct guard; try discriminate.
    destruct (prepare_reply success failure) as [[success_name failure_name]|];
      try discriminate.
    inversion Hpublished. reflexivity.
  Qed.

  Theorem failed_render_publishes_no_reply :
    forall guard success failure,
      render_all success = None \/ render_all failure = None ->
      publish_reply guard success failure = None.
  Proof.
    intros guard success failure [Hfailed|Hfailed];
      unfold publish_reply, prepare_reply;
      destruct guard; try reflexivity;
      rewrite Hfailed;
      destruct (render_all success);
      destruct (render_all failure); reflexivity.
  Qed.

  Theorem refused_guard_publishes_no_reply :
    forall success failure,
      publish_reply false success failure = None.
  Proof. reflexivity. Qed.

  Theorem published_reply_contains_every_prepared_branch :
    forall success failure successes failures payloads,
      render_all success = Some successes ->
      render_all failure = Some failures ->
      publish_reply true success failure = Some payloads ->
      exists success_name failure_name,
        payloads = [success_name; failure_name] /\
        (forall entry, success_name entry <-> In entry successes) /\
        (forall entry, failure_name entry <-> In entry failures).
  Proof.
    intros success failure successes failures payloads Hsuccess Hfailure Hpublished.
    unfold publish_reply, prepare_reply in Hpublished.
    rewrite Hsuccess, Hfailure in Hpublished.
    inversion Hpublished; subst.
    exists (pathmap_name successes), (pathmap_name failures).
    split; [reflexivity|].
    split; intros entry; split; intro Hmember; exact Hmember.
  Qed.

  Definition publish_with_internal_truncation
      (guard : bool) (success failure : list (option Entry))
      (truncated : list Entry)
      : option (list PathMapName) * VersionedTruncation :=
    (publish_reply guard success failure, internal_truncation_v2 truncated).

  Theorem internal_truncation_does_not_change_public_reply :
    forall guard success failure truncated,
      fst (publish_with_internal_truncation guard success failure truncated) =
        publish_reply guard success failure /\
      truncation_version
        (snd (publish_with_internal_truncation guard success failure truncated)) = 2.
  Proof. intros. split; reflexivity. Qed.
End CompletePathMapReply.

Print Assumptions published_trace_starts_with_submitted_input.
Print Assumptions published_trace_ends_with_terminal_configuration.
Print Assumptions published_trace_has_two_roots_and_every_successor.
Print Assumptions success_report_retains_the_complete_process_path.
Print Assumptions success_delivery_contains_the_complete_process_path.
Print Assumptions success_delivery_contains_only_the_complete_process_path.
Print Assumptions published_trace_never_substitutes_a_digest_for_a_process.
Print Assumptions truncated_handle_is_a_name_not_a_trace_node.
Print Assumptions render_all_preserves_branch_count.
Print Assumptions published_reply_has_exactly_two_pathmap_names.
Print Assumptions failed_render_publishes_no_reply.
Print Assumptions refused_guard_publishes_no_reply.
Print Assumptions published_reply_contains_every_prepared_branch.
Print Assumptions internal_truncation_does_not_change_public_reply.
