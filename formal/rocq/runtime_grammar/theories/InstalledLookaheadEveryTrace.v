(** A one-step EveryTrace contract for installed GSLT lookahead.

    SemanticNormalization's witnesses and validator are reused without
    redefining the kernel. Its normal-form driver coalesces equal successor
    keys; this step roster intentionally does not. A CompleteRoster is a claim
    by the runtime enumerator that all enabled host COMM and guest rewrite
    occurrences were found. This file proves consequences of that claim, not
    completeness of RSpace matching, receipt generation, or Rust enumeration.

    LookaheadTraceDelivery (RhoBridge) supplies the corresponding process-path
    wire shape. Importing RhoBridge here would invert the project dependency,
    so the path below retains its same submitted/saturated/successor structure. *)

From Stdlib Require Import List Bool PeanoNat Lia.
From RuntimeGrammar Require Import SemanticNormalization SemanticTransitionKernel.
Import ListNotations.

Module InstalledLookaheadEveryTrace.
Module Norm := SemanticNormalization.SemanticNormalization.
Module Kernel := SemanticTransitionKernel.SemanticTransitionKernel.

Definition OwnerId := nat.
Definition HandleId := nat.
Definition LocationId := nat.

Record GuestSlot := {
  slot_handle : HandleId;
  slot_owner : OwnerId;
  slot_state : Norm.MachineState
}.

Record Binding := {
  binding_handle : HandleId;
  binding_owner : OwnerId;
  binding_epoch : nat;
  binding_reduce : bool
}.

Record Configuration := {
  configuration_host : nat;
  configuration_guests : list GuestSlot;
  configuration_epoch : nat;
  configuration_bindings : list Binding
}.

Record HostCommOccurrence := {
  host_comm_id : nat;
  host_proof_id : nat;
  host_successor : Configuration
}.

Record GuestRewriteOccurrence := {
  guest_location : LocationId;
  guest_claimed_owner : OwnerId;
  guest_proof_id : nat;
  guest_witness : Norm.NormalizationStepWitness
}.

Inductive EdgeForm :=
| HostComm (host : HostCommOccurrence)
| GuestRewrite (guest : GuestRewriteOccurrence).

Record StepOccurrence := {
  occurrence_order : nat;
  occurrence_form : EdgeForm
}.

Fixpoint replace_nth {A : Type} (index : nat) (value : A)
    (items : list A) : list A :=
  match index, items with
  | 0, _ :: rest => value :: rest
  | S next, head :: rest => head :: replace_nth next value rest
  | _, [] => []
  end.

Lemma nth_error_replace_nth : forall (A : Type) (items : list A)
    index old value,
  nth_error items index = Some old ->
  nth_error (replace_nth index value items) index = Some value.
Proof.
  intros A items. induction items as [|head rest IH]; intros [|index] old value H;
    simpl in *; try discriminate; auto.
  now apply IH with (old := old).
Qed.

Definition find_binding (handle : HandleId) (bindings : list Binding)
    : option Binding :=
  find (fun binding => Nat.eqb (binding_handle binding) handle) bindings.

Definition guest_ready
    (policy : Norm.NormalizationPolicy)
    (rules : list Norm.NormalizationRuleManifest)
    (profile : Kernel.ResourceProfile)
    (bounds : Kernel.SemanticTermBounds)
    (configuration : Configuration)
    (slot : GuestSlot) (guest : GuestRewriteOccurrence) : bool :=
  Nat.eqb (slot_owner slot) (guest_claimed_owner guest) &&
  match find_binding (slot_handle slot) (configuration_bindings configuration) with
  | None => false
  | Some binding =>
      Nat.eqb (binding_handle binding) (slot_handle slot) &&
      Nat.eqb (binding_owner binding) (slot_owner slot) &&
      Nat.eqb (binding_epoch binding) (configuration_epoch configuration) &&
      binding_reduce binding &&
      Nat.eqb (Norm.machine_state_sort (slot_state slot))
        (Norm.policy_relation_sort policy) &&
      Norm.normalization_step_valid policy rules profile bounds
        (slot_state slot) (guest_witness guest) &&
      Nat.eqb
        (Norm.machine_state_sort
          (Norm.normalization_step_after (guest_witness guest)))
        (Norm.policy_relation_sort policy)
  end.

Definition fire_guest
    (policy : Norm.NormalizationPolicy)
    (rules : list Norm.NormalizationRuleManifest)
    (profile : Kernel.ResourceProfile)
    (bounds : Kernel.SemanticTermBounds)
    (configuration : Configuration)
    (guest : GuestRewriteOccurrence) : option Configuration :=
  match nth_error (configuration_guests configuration) (guest_location guest) with
  | None => None
  | Some slot =>
      if guest_ready policy rules profile bounds configuration slot guest then
        Some {| configuration_host := configuration_host configuration;
                configuration_guests :=
                  replace_nth (guest_location guest)
                    {| slot_handle := slot_handle slot;
                       slot_owner := slot_owner slot;
                       slot_state :=
                         Norm.normalization_step_after (guest_witness guest) |}
                    (configuration_guests configuration);
                configuration_epoch := configuration_epoch configuration;
                configuration_bindings := configuration_bindings configuration |}
      else None
  end.

Theorem guest_fire_preserves_owner_sort_and_host :
  forall policy rules profile bounds configuration guest successor,
    fire_guest policy rules profile bounds configuration guest = Some successor ->
    exists before after,
      nth_error (configuration_guests configuration) (guest_location guest) =
        Some before /\
      nth_error (configuration_guests successor) (guest_location guest) =
        Some after /\
      slot_handle after = slot_handle before /\
      slot_owner after = slot_owner before /\
      Norm.machine_state_sort (slot_state after) =
        Norm.policy_relation_sort policy /\
      configuration_host successor = configuration_host configuration.
Proof.
  intros policy rules profile bounds configuration guest successor Hfire.
  unfold fire_guest in Hfire.
  destruct (nth_error (configuration_guests configuration) (guest_location guest))
    as [before|] eqn:Hslot; [|discriminate].
  destruct (guest_ready policy rules profile bounds configuration before guest)
    eqn:Hready; [|discriminate].
  inversion Hfire; subst successor; clear Hfire.
  eexists before. eexists
    {| slot_handle := slot_handle before;
       slot_owner := slot_owner before;
       slot_state := Norm.normalization_step_after (guest_witness guest) |}.
  split; [reflexivity|].
  split.
  - cbn. now apply nth_error_replace_nth with (old := before).
  - repeat split; try reflexivity.
    unfold guest_ready in Hready.
    destruct (find_binding (slot_handle before)
                (configuration_bindings configuration));
      [|rewrite andb_false_r in Hready; discriminate].
    repeat rewrite andb_true_iff in Hready.
    apply Nat.eqb_eq. tauto.
Qed.

Definition HostChecker := Configuration -> HostCommOccurrence -> bool.

Definition fire_occurrence
    (host_checked : HostChecker)
    (policy : Norm.NormalizationPolicy)
    (rules : list Norm.NormalizationRuleManifest)
    (profile : Kernel.ResourceProfile)
    (bounds : Kernel.SemanticTermBounds)
    (configuration : Configuration)
    (occurrence : StepOccurrence) : option Configuration :=
  match occurrence_form occurrence with
  | HostComm host =>
      if host_checked configuration host then Some (host_successor host) else None
  | GuestRewrite guest =>
      fire_guest policy rules profile bounds configuration guest
  end.

Fixpoint fire_roster
    (host_checked : HostChecker)
    (policy : Norm.NormalizationPolicy)
    (rules : list Norm.NormalizationRuleManifest)
    (profile : Kernel.ResourceProfile)
    (bounds : Kernel.SemanticTermBounds)
    (configuration : Configuration)
    (roster : list StepOccurrence)
    : option (list (StepOccurrence * Configuration)) :=
  match roster with
  | [] => Some []
  | occurrence :: rest =>
      match fire_occurrence host_checked policy rules profile bounds
              configuration occurrence,
            fire_roster host_checked policy rules profile bounds
              configuration rest with
      | Some next, Some successors => Some ((occurrence, next) :: successors)
      | _, _ => None
      end
  end.

Fixpoint increasing_orders (orders : list nat) : bool :=
  match orders with
  | [] | [_] => true
  | first :: (second :: _ as rest) =>
      Nat.ltb first second && increasing_orders rest
  end.

Definition canonically_ordered (roster : list StepOccurrence) : bool :=
  increasing_orders (map occurrence_order roster).

Inductive StepEnumeration :=
| CompleteRoster (roster : list StepOccurrence)
| IncompleteRoster (reason : nat).

Record Trace := {
  trace_submitted : Configuration;
  trace_saturated : Configuration;
  trace_steps : list (StepOccurrence * Configuration)
}.

Definition trace_current (trace : Trace) : Configuration :=
  last (map snd (trace_steps trace)) (trace_saturated trace).

Definition trace_process_path (trace : Trace) : list Configuration :=
  trace_submitted trace :: trace_saturated trace :: map snd (trace_steps trace).

Definition extend_trace (trace : Trace)
    (successor : StepOccurrence * Configuration) : Trace :=
  {| trace_submitted := trace_submitted trace;
     trace_saturated := trace_saturated trace;
     trace_steps := trace_steps trace ++ [successor] |}.

Lemma last_snoc : forall (A : Type) (items : list A) value fallback,
  last (items ++ [value]) fallback = value.
Proof.
  intros A items. induction items as [|head rest IH]; intros value fallback;
    simpl; [reflexivity|].
  destruct rest; simpl; [reflexivity|apply IH].
Qed.

Theorem selected_edge_appends_exactly_one_configuration :
  forall trace occurrence successor,
    trace_current (extend_trace trace (occurrence, successor)) = successor /\
    trace_process_path (extend_trace trace (occurrence, successor)) =
      trace_process_path trace ++ [successor].
Proof.
  intros trace occurrence successor. split.
  - unfold trace_current, extend_trace; simpl.
    rewrite map_app. simpl. apply last_snoc.
  - unfold trace_process_path, extend_trace; simpl.
    rewrite map_app. simpl. reflexivity.
Qed.

Inductive StepDecision :=
| StepComplete (traces : list Trace)
| StepTruncated (traces : list Trace)
| StepRefused
| StepIncomplete (reason : nat).

Definition expand_one
    (host_checked : HostChecker)
    (policy : Norm.NormalizationPolicy)
    (rules : list Norm.NormalizationRuleManifest)
    (profile : Kernel.ResourceProfile)
    (bounds : Kernel.SemanticTermBounds)
    (trace : Trace) (enumeration : StepEnumeration) : StepDecision :=
  match enumeration with
  | IncompleteRoster reason => StepIncomplete reason
  | CompleteRoster roster =>
      if canonically_ordered roster then
        match fire_roster host_checked policy rules profile bounds
                (trace_current trace) roster with
        | None => StepRefused
        | Some successors => StepComplete (map (extend_trace trace) successors)
        end
      else StepRefused
  end.

Definition at_zero (authorized : Configuration -> bool)
    (trace : Trace) (enumeration : StepEnumeration) : StepDecision :=
  if authorized (trace_current trace) then
    match enumeration with
    | IncompleteRoster reason => StepIncomplete reason
    | CompleteRoster [] => StepComplete [trace]
    | CompleteRoster (_ :: _) => StepTruncated [trace]
    end
  else StepRefused.

Definition publish_success (live : Configuration -> bool)
    (decision : StepDecision) : option (list Trace) :=
  match decision with
  | StepComplete traces =>
      if forallb (fun trace => live (trace_current trace)) traces
      then Some traces else None
  | StepTruncated _ | StepRefused | StepIncomplete _ => None
  end.

Theorem every_complete_occurrence_gets_one_trace :
  forall host_checked policy rules profile bounds trace roster successors,
    canonically_ordered roster = true ->
    fire_roster host_checked policy rules profile bounds
      (trace_current trace) roster = Some successors ->
    expand_one host_checked policy rules profile bounds trace
      (CompleteRoster roster) =
      StepComplete (map (extend_trace trace) successors) /\
    length successors = length roster.
Proof.
  intros host_checked policy rules profile bounds trace roster successors
    Horder Hfire. split.
  - unfold expand_one. now rewrite Horder, Hfire.
  - clear Horder. revert successors Hfire.
    induction roster as [|occurrence rest IH];
      intros successors Hfire; simpl in Hfire.
    + inversion Hfire. reflexivity.
    + destruct (fire_occurrence host_checked policy rules profile bounds
                  (trace_current trace) occurrence) as [next|];
        destruct (fire_roster host_checked policy rules profile bounds
                    (trace_current trace) rest) as [tail|] eqn:Htail;
        try discriminate.
      inversion Hfire; subst. simpl. now rewrite (IH tail eq_refl).
Qed.

Fixpoint host_only_roster_from (ordinal : nat)
    (hosts : list HostCommOccurrence) : list StepOccurrence :=
  match hosts with
  | [] => []
  | host :: rest =>
      {| occurrence_order := ordinal; occurrence_form := HostComm host |} ::
      host_only_roster_from (S ordinal) rest
  end.

Theorem host_only_roster_refines_checked_host_successors :
  forall host_checked policy rules profile bounds configuration ordinal hosts,
    forallb (host_checked configuration) hosts = true ->
    fire_roster host_checked policy rules profile bounds configuration
      (host_only_roster_from ordinal hosts) =
    Some (combine (host_only_roster_from ordinal hosts)
                  (map host_successor hosts)).
Proof.
  intros host_checked policy rules profile bounds configuration ordinal hosts.
  revert ordinal. induction hosts as [|host rest IH]; intros ordinal Hchecked;
    simpl in *; [reflexivity|].
  apply andb_true_iff in Hchecked. destruct Hchecked as [Hhost Hrest].
  cbn [host_only_roster_from fire_roster fire_occurrence].
  destruct (host_checked configuration host) eqn:Hcheck; [|congruence].
  rewrite (IH (S ordinal) Hrest).
  unfold fire_occurrence. simpl. now rewrite Hcheck.
Qed.

Theorem mixed_host_guest_roster_keeps_two_occurrences :
  forall host_checked policy rules profile bounds trace host guest successors,
    fire_roster host_checked policy rules profile bounds (trace_current trace)
      [{| occurrence_order := 0; occurrence_form := HostComm host |};
       {| occurrence_order := 1; occurrence_form := GuestRewrite guest |}] =
      Some successors ->
    length successors = 2 /\
    length (map (extend_trace trace) successors) = 2.
Proof.
  intros host_checked policy rules profile bounds trace host guest successors Hfire.
  pose proof (every_complete_occurrence_gets_one_trace
    host_checked policy rules profile bounds trace
    [{| occurrence_order := 0; occurrence_form := HostComm host |};
     {| occurrence_order := 1; occurrence_form := GuestRewrite guest |}]
    successors eq_refl Hfire)
    as [_ Hlength].
  split; [exact Hlength|]. now rewrite length_map.
Qed.

Theorem zero_step_empty_roster_succeeds :
  forall authorized trace,
    authorized (trace_current trace) = true ->
    at_zero authorized trace (CompleteRoster []) = StepComplete [trace].
Proof. intros. unfold at_zero. now rewrite H. Qed.

Theorem zero_step_enabled_roster_is_truncated :
  forall authorized trace head tail,
    authorized (trace_current trace) = true ->
    at_zero authorized trace (CompleteRoster (head :: tail)) =
      StepTruncated [trace].
Proof. intros. unfold at_zero. now rewrite H. Qed.

Theorem incomplete_roster_cannot_certify_success_or_no_successor :
  forall host_checked policy rules profile bounds trace reason live,
    expand_one host_checked policy rules profile bounds trace
      (IncompleteRoster reason) = StepIncomplete reason /\
    publish_success live
      (expand_one host_checked policy rules profile bounds trace
        (IncompleteRoster reason)) = None.
Proof. intros. split; reflexivity. Qed.

Theorem refusal_and_truncation_never_publish_success :
  forall live traces reason,
    publish_success live StepRefused = None /\
    publish_success live (StepTruncated traces) = None /\
    publish_success live (StepIncomplete reason) = None.
Proof. intros. repeat split; reflexivity. Qed.

Theorem revoked_at_publication_discards_complete_traces :
  forall live traces trace,
    In trace traces -> live (trace_current trace) = false ->
    publish_success live (StepComplete traces) = None.
Proof.
  intros live traces trace Hin Hrevoked.
  unfold publish_success.
  destruct (forallb (fun candidate => live (trace_current candidate)) traces)
    eqn:Hall; [|reflexivity].
  pose proof (proj1 (forallb_forall
    (fun candidate => live (trace_current candidate)) traces)
    Hall trace Hin) as Hlive.
  congruence.
Qed.

Theorem process_path_retains_every_successor :
  forall trace,
    length (trace_process_path trace) = 2 + length (trace_steps trace).
Proof.
  intros. unfold trace_process_path. simpl. now rewrite length_map.
Qed.

Definition sample_state : Norm.MachineState :=
  {| Norm.machine_state_sort := 1; Norm.machine_state_root := 2;
     Norm.machine_state_key := [7]; Norm.machine_state_nodes := 1;
     Norm.machine_state_bytes := 1 |}.

Definition sample_step (rule : nat) : Norm.NormalizationStepWitness :=
  {| Norm.normalization_step_rule := rule;
     Norm.normalization_step_before := sample_state;
     Norm.normalization_step_after := sample_state;
     Norm.normalization_step_premises := [];
     Norm.normalization_step_intrinsics := [];
     Norm.normalization_step_grade := Kernel.NoSemanticGrade;
     Norm.normalization_step_effects := [];
     Norm.normalization_step_match_work := 0;
     Norm.normalization_step_premise_work := 0;
     Norm.normalization_step_build_work := 0 |}.

Definition sample_guest (rule : nat) : GuestRewriteOccurrence :=
  {| guest_location := 0; guest_claimed_owner := 3;
     guest_proof_id := 0; guest_witness := sample_step rule |}.

Definition sample_roster : list StepOccurrence :=
  [{| occurrence_order := 0; occurrence_form := GuestRewrite (sample_guest 10) |};
   {| occurrence_order := 1; occurrence_form := GuestRewrite (sample_guest 11) |}].

Example equal_target_different_rule_counterexample :
  length sample_roster = 2 /\
  length (Norm.coalesce_successors [sample_step 10; sample_step 11]) = 1.
Proof. split; reflexivity. Qed.

Print Assumptions guest_fire_preserves_owner_sort_and_host.
Print Assumptions every_complete_occurrence_gets_one_trace.
Print Assumptions selected_edge_appends_exactly_one_configuration.
Print Assumptions host_only_roster_refines_checked_host_successors.
Print Assumptions mixed_host_guest_roster_keeps_two_occurrences.
Print Assumptions zero_step_empty_roster_succeeds.
Print Assumptions zero_step_enabled_roster_is_truncated.
Print Assumptions incomplete_roster_cannot_certify_success_or_no_successor.
Print Assumptions refusal_and_truncation_never_publish_success.
Print Assumptions revoked_at_publication_discards_complete_traces.
Print Assumptions process_path_retains_every_successor.
Print Assumptions equal_target_different_rule_counterexample.

End InstalledLookaheadEveryTrace.
