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

Print Assumptions published_trace_starts_with_submitted_input.
Print Assumptions published_trace_ends_with_terminal_configuration.
Print Assumptions published_trace_has_two_roots_and_every_successor.
Print Assumptions success_report_retains_the_complete_process_path.
Print Assumptions success_delivery_contains_the_complete_process_path.
Print Assumptions success_delivery_contains_only_the_complete_process_path.
Print Assumptions published_trace_never_substitutes_a_digest_for_a_process.
Print Assumptions truncated_handle_is_a_name_not_a_trace_node.
