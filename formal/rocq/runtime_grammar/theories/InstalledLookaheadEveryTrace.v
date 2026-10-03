(** A one-step EveryTrace contract for installed GSLT lookahead.

    SemanticNormalization's witnesses and validator are reused without
    redefining the kernel. Its normal-form driver coalesces equal successor
    keys; this step roster intentionally does not. A CompleteRoster is a claim
    by the runtime enumerator that all enabled host COMM and guest rewrite
    occurrences were found. This file proves consequences of that claim, not
    completeness of RSpace matching, receipt generation, or Rust enumeration.

    Production correspondence: search.rs enumerates RSpace rendezvous in
    SpeculativeSandbox::enabled, fires each selected rendezvous, appends its
    successor to ReductionTrace, and classifies the boundary frontier by
    enabled-edge emptiness. The host-only refinement below applies to that
    search only when host_checked agrees with enabled/fire, enumeration is
    complete and stable, and TraceMode::EveryTrace disables pruning and
    merging. The current Rust explorer does not yet enumerate installed guest
    rewrites, so no theorem here asserts that dynamic lookahead is implemented.
    The runtime must also prove that recorded work equals actual host charges,
    and that the complete roster contains every enabled occurrence.

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
  (* A sandboxed guest rewrite changes only its structural guest slot. The
     normalization witness may carry effect IDs for ordinary normalization;
     those are not admitted on the speculative route. *)
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
      (match Norm.normalization_step_effects (guest_witness guest) with
       | [] => true | _ :: _ => false
       end) &&
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

Theorem guest_fire_requires_live_reduce_binding_and_pure_step :
  forall policy rules profile bounds configuration guest successor,
    fire_guest policy rules profile bounds configuration guest = Some successor ->
    exists slot binding,
      nth_error (configuration_guests configuration) (guest_location guest) =
        Some slot /\
      find_binding (slot_handle slot) (configuration_bindings configuration) =
        Some binding /\
      slot_owner slot = guest_claimed_owner guest /\
      binding_handle binding = slot_handle slot /\
      binding_owner binding = slot_owner slot /\
      binding_epoch binding = configuration_epoch configuration /\
      binding_reduce binding = true /\
      Norm.normalization_step_effects (guest_witness guest) = [] /\
      Norm.normalization_step_before (guest_witness guest) = slot_state slot.
Proof.
  intros policy rules profile bounds configuration guest successor Hfire.
  unfold fire_guest in Hfire.
  destruct (nth_error (configuration_guests configuration) (guest_location guest))
    as [slot|] eqn:Hslot; [|discriminate].
  destruct (guest_ready policy rules profile bounds configuration slot guest)
    eqn:Hready; [|discriminate].
  unfold guest_ready in Hready.
  apply andb_true_iff in Hready.
  destruct Hready as [Howner Hbinding].
  destruct (find_binding (slot_handle slot)
    (configuration_bindings configuration)) as [binding|] eqn:Hfind;
    [|discriminate].
  cbn in Hbinding.
  repeat rewrite andb_true_iff in Hbinding.
  destruct (Norm.normalization_step_effects (guest_witness guest))
    as [|effect rest] eqn:Heffects.
  2: {
    cbn in Hbinding.
    destruct Hbinding as [[_ Himpossible] _].
    discriminate Himpossible.
  }
  exists slot, binding.
  repeat split; try reflexivity; try (apply Nat.eqb_eq; tauto); try tauto.
  assert (Hvalid : Norm.normalization_step_valid policy rules profile bounds
    (slot_state slot) (guest_witness guest) = true) by tauto.
  apply (proj1 (Norm.valid_step_preserves_exact_source_and_sort
    policy rules profile bounds (slot_state slot) (guest_witness guest) Hvalid)).
Qed.

Theorem guest_fire_preserves_authority_snapshot :
  forall policy rules profile bounds configuration guest successor,
    fire_guest policy rules profile bounds configuration guest = Some successor ->
    configuration_epoch successor = configuration_epoch configuration /\
    configuration_bindings successor = configuration_bindings configuration.
Proof.
  intros policy rules profile bounds configuration guest successor Hfire.
  unfold fire_guest in Hfire.
  destruct (nth_error (configuration_guests configuration) (guest_location guest))
    as [slot|]; [|discriminate].
  destruct (guest_ready policy rules profile bounds configuration slot guest);
    [|discriminate].
  now inversion Hfire.
Qed.

Corollary guest_fire_has_no_committable_effects :
  forall policy rules profile bounds configuration guest successor,
    fire_guest policy rules profile bounds configuration guest = Some successor ->
    Norm.normalization_step_effects (guest_witness guest) = [].
Proof.
  intros policy rules profile bounds configuration guest successor Hfire.
  destruct (guest_fire_requires_live_reduce_binding_and_pure_step
    policy rules profile bounds configuration guest successor Hfire)
    as [slot [binding Hbinding]].
  tauto.
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

(** The occurrence itself is the receipt carrier: a host occurrence retains
    its rendezvous and proof identity, while a guest occurrence retains its
    exact normalization witness, including rule, premises, intrinsic receipts,
    grade, and component work. Neither the successor state nor its exact key
    is used to merge receipts. The caller supplies the host COMM charge, since
    this model cannot derive the RSpace metering policy. On refusal,
    fire_roster returns None and this abstraction loses attempted-prefix work;
    production must separately retain and charge that work. Host COMM effects
    must likewise remain confined to the speculative RSpace snapshot. *)
Definition fired_receipts
    (successors : list (StepOccurrence * Configuration)) : list EdgeForm :=
  map (fun fired => occurrence_form (fst fired)) successors.

Definition occurrence_work
    (host_work : HostCommOccurrence -> nat)
    (occurrence : StepOccurrence) : nat :=
  match occurrence_form occurrence with
  | HostComm host => host_work host
  | GuestRewrite guest => Norm.normalization_step_work (guest_witness guest)
  end.

Definition roster_work (host_work : HostCommOccurrence -> nat)
    (roster : list StepOccurrence) : nat :=
  fold_right (fun occurrence total => occurrence_work host_work occurrence + total)
    0 roster.

Definition fired_work (host_work : HostCommOccurrence -> nat)
    (successors : list (StepOccurrence * Configuration)) : nat :=
  roster_work host_work (map fst successors).

Theorem fired_roster_retains_exact_occurrences :
  forall host_checked policy rules profile bounds configuration roster successors,
    fire_roster host_checked policy rules profile bounds configuration roster =
      Some successors ->
    map fst successors = roster.
Proof.
  intros host_checked policy rules profile bounds configuration roster.
  induction roster as [|occurrence rest IH]; intros successors Hfire;
    simpl in Hfire.
  - now inversion Hfire.
  - destruct (fire_occurrence host_checked policy rules profile bounds
        configuration occurrence) as [next|];
      destruct (fire_roster host_checked policy rules profile bounds
        configuration rest) as [tail|] eqn:Htail; try discriminate.
    inversion Hfire; subst. simpl. now rewrite (IH tail eq_refl).
Qed.

Theorem fired_roster_receipts_and_work_are_exact :
  forall host_checked policy rules profile bounds configuration roster
      successors host_work,
    fire_roster host_checked policy rules profile bounds configuration roster =
      Some successors ->
    fired_receipts successors = map occurrence_form roster /\
    fired_work host_work successors = roster_work host_work roster.
Proof.
  intros host_checked policy rules profile bounds configuration roster
    successors host_work Hfire.
  pose proof (fired_roster_retains_exact_occurrences
    host_checked policy rules profile bounds configuration roster successors
    Hfire) as Hoccurrences.
  split.
  - unfold fired_receipts. now rewrite <- map_map, Hoccurrences.
  - unfold fired_work. now rewrite Hoccurrences.
Qed.

Theorem fired_roster_has_no_guest_committable_effects :
  forall host_checked policy rules profile bounds configuration roster successors,
    fire_roster host_checked policy rules profile bounds configuration roster =
      Some successors ->
    Forall (fun fired =>
      match occurrence_form (fst fired) with
      | HostComm _ => True
      | GuestRewrite guest =>
          Norm.normalization_step_effects (guest_witness guest) = []
      end) successors.
Proof.
  intros host_checked policy rules profile bounds configuration roster.
  induction roster as [|occurrence rest IH]; intros successors Hfire;
    simpl in Hfire.
  - inversion Hfire. constructor.
  - destruct (fire_occurrence host_checked policy rules profile bounds
        configuration occurrence) as [next|] eqn:Hnext;
      destruct (fire_roster host_checked policy rules profile bounds
        configuration rest) as [tail|] eqn:Htail; try discriminate.
    inversion Hfire; subst. constructor.
    + cbn.
      destruct (occurrence_form occurrence) as [host|guest] eqn:Hform;
        cbn; [exact I|].
      unfold fire_occurrence in Hnext. rewrite Hform in Hnext.
      eapply guest_fire_has_no_committable_effects; eauto.
    + exact (IH tail eq_refl).
Qed.

Theorem guest_occurrence_has_positive_logical_work :
  forall host_work guest order,
    1 <= occurrence_work host_work
      {| occurrence_order := order; occurrence_form := GuestRewrite guest |}.
Proof.
  intros. unfold occurrence_work. simpl.
  apply Norm.normalization_step_work_positive.
Qed.

Fixpoint increasing_orders (orders : list nat) : bool :=
  match orders with
  | [] => true
  | first :: rest =>
      match rest with
      | [] => true
      | second :: _ => Nat.ltb first second && increasing_orders rest
      end
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

Definition trace_last_edge (trace : Trace) : option StepOccurrence :=
  option_map fst (hd_error (rev (trace_steps trace))).

Lemma trace_last_edge_extend : forall trace successor,
  trace_last_edge (extend_trace trace successor) = Some (fst successor).
Proof.
  intros trace successor. unfold trace_last_edge, extend_trace; simpl.
  rewrite rev_app_distr. reflexivity.
Qed.

Lemma map_trace_last_edge_extend : forall trace successors,
  map trace_last_edge (map (extend_trace trace) successors) =
    map (fun successor => Some (fst successor)) successors.
Proof.
  intros trace successors. induction successors as [|successor rest IH];
    simpl; [reflexivity|].
  now rewrite trace_last_edge_extend, IH.
Qed.

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

Theorem published_complete_roster_has_no_partial_prefix :
  forall host_checked policy rules profile bounds trace roster live published,
    publish_success live
      (expand_one host_checked policy rules profile bounds trace
        (CompleteRoster roster)) = Some published ->
    canonically_ordered roster = true /\
    length published = length roster /\
    map trace_last_edge published = map Some roster.
Proof.
  intros host_checked policy rules profile bounds trace roster live published
    Hpublished.
  unfold publish_success in Hpublished.
  unfold expand_one in Hpublished.
  destruct (canonically_ordered roster) eqn:Horder; [|discriminate].
  destruct (fire_roster host_checked policy rules profile bounds
    (trace_current trace) roster) as [successors|] eqn:Hfire;
    [|discriminate].
  destruct (forallb (fun child => live (trace_current child))
    (map (extend_trace trace) successors)) eqn:Hlive; [|discriminate].
  inversion Hpublished; subst published.
  split; [reflexivity|].
  split.
  - rewrite length_map.
    exact (proj2 (every_complete_occurrence_gets_one_trace
      host_checked policy rules profile bounds trace roster successors
      Horder Hfire)).
  - rewrite map_trace_last_edge_extend.
    rewrite <- map_map.
    now rewrite (fired_roster_retains_exact_occurrences
      host_checked policy rules profile bounds (trace_current trace)
      roster successors Hfire).
Qed.

Fixpoint host_only_roster_from (ordinal : nat)
    (hosts : list HostCommOccurrence) : list StepOccurrence :=
  match hosts with
  | [] => []
  | host :: rest =>
      {| occurrence_order := ordinal; occurrence_form := HostComm host |} ::
      host_only_roster_from (S ordinal) rest
  end.

Lemma host_only_roster_orders : forall ordinal hosts,
  map occurrence_order (host_only_roster_from ordinal hosts) =
    seq ordinal (length hosts).
Proof.
  intros ordinal hosts. revert ordinal.
  induction hosts as [|host rest IH]; intro ordinal; simpl;
    [reflexivity|].
  now rewrite IH.
Qed.

Lemma increasing_seq : forall ordinal count,
  increasing_orders (seq ordinal count) = true.
Proof.
  intros ordinal count. revert ordinal.
  induction count as [|count IH]; intro ordinal.
  - reflexivity.
  - destruct count as [|count']; [reflexivity|].
    cbn [seq increasing_orders].
    apply andb_true_iff. split.
    + apply Nat.ltb_lt. lia.
    + apply IH.
Qed.

Theorem host_only_roster_is_canonical : forall ordinal hosts,
  canonically_ordered (host_only_roster_from ordinal hosts) = true.
Proof.
  intros ordinal hosts. unfold canonically_ordered.
  now rewrite host_only_roster_orders, increasing_seq.
Qed.

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

Theorem host_only_expansion_refines_one_every_trace_level :
  forall host_checked policy rules profile bounds trace ordinal hosts,
    forallb (host_checked (trace_current trace)) hosts = true ->
    expand_one host_checked policy rules profile bounds trace
      (CompleteRoster (host_only_roster_from ordinal hosts)) =
    StepComplete
      (map (extend_trace trace)
        (combine (host_only_roster_from ordinal hosts)
          (map host_successor hosts))).
Proof.
  intros host_checked policy rules profile bounds trace ordinal hosts Hchecked.
  unfold expand_one.
  rewrite host_only_roster_is_canonical.
  now rewrite (host_only_roster_refines_checked_host_successors
    host_checked policy rules profile bounds (trace_current trace) ordinal hosts
    Hchecked).
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

Theorem zero_step_incomplete_cannot_succeed :
  forall authorized trace reason,
    authorized (trace_current trace) = true ->
    at_zero authorized trace (IncompleteRoster reason) =
      StepIncomplete reason.
Proof. intros. unfold at_zero. now rewrite H. Qed.

Theorem zero_step_revoked_is_refused :
  forall authorized trace enumeration,
    authorized (trace_current trace) = false ->
    at_zero authorized trace enumeration = StepRefused.
Proof. intros. unfold at_zero. now rewrite H. Qed.

Theorem incomplete_roster_cannot_certify_success_or_no_successor :
  forall host_checked policy rules profile bounds trace reason live,
    expand_one host_checked policy rules profile bounds trace
      (IncompleteRoster reason) = StepIncomplete reason /\
    publish_success live
      (expand_one host_checked policy rules profile bounds trace
        (IncompleteRoster reason)) = None.
Proof. intros. split; reflexivity. Qed.

Theorem failed_roster_never_publishes_a_partial_prefix :
  forall host_checked policy rules profile bounds trace roster live,
    canonically_ordered roster = true ->
    fire_roster host_checked policy rules profile bounds
      (trace_current trace) roster = None ->
    expand_one host_checked policy rules profile bounds trace
      (CompleteRoster roster) = StepRefused /\
    publish_success live
      (expand_one host_checked policy rules profile bounds trace
        (CompleteRoster roster)) = None.
Proof.
  intros host_checked policy rules profile bounds trace roster live
    Horder Hfire.
  unfold expand_one. now rewrite Horder, Hfire.
Qed.

Theorem published_traces_rechecked_live :
  forall live decision traces,
    publish_success live decision = Some traces ->
    Forall (fun trace => live (trace_current trace) = true) traces.
Proof.
  intros live [completed | truncated | | reason] traces Hpublished;
    simpl in Hpublished; try discriminate.
  destruct (forallb (fun trace => live (trace_current trace)) completed)
    eqn:Hall; [|discriminate].
  inversion Hpublished; subst.
  apply Forall_forall. intros trace Hin.
  exact (proj1 (forallb_forall
    (fun candidate => live (trace_current candidate)) traces)
    Hall trace Hin).
Qed.

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
Print Assumptions guest_fire_requires_live_reduce_binding_and_pure_step.
Print Assumptions guest_fire_preserves_authority_snapshot.
Print Assumptions guest_fire_has_no_committable_effects.
Print Assumptions fired_roster_retains_exact_occurrences.
Print Assumptions fired_roster_receipts_and_work_are_exact.
Print Assumptions fired_roster_has_no_guest_committable_effects.
Print Assumptions guest_occurrence_has_positive_logical_work.
Print Assumptions every_complete_occurrence_gets_one_trace.
Print Assumptions published_complete_roster_has_no_partial_prefix.
Print Assumptions selected_edge_appends_exactly_one_configuration.
Print Assumptions host_only_roster_refines_checked_host_successors.
Print Assumptions host_only_roster_is_canonical.
Print Assumptions host_only_expansion_refines_one_every_trace_level.
Print Assumptions mixed_host_guest_roster_keeps_two_occurrences.
Print Assumptions zero_step_empty_roster_succeeds.
Print Assumptions zero_step_enabled_roster_is_truncated.
Print Assumptions zero_step_incomplete_cannot_succeed.
Print Assumptions zero_step_revoked_is_refused.
Print Assumptions incomplete_roster_cannot_certify_success_or_no_successor.
Print Assumptions failed_roster_never_publishes_a_partial_prefix.
Print Assumptions published_traces_rechecked_live.
Print Assumptions refusal_and_truncation_never_publish_success.
Print Assumptions revoked_at_publication_discards_complete_traces.
Print Assumptions process_path_retains_every_successor.
Print Assumptions equal_target_different_rule_counterexample.

End InstalledLookaheadEveryTrace.
