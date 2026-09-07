(** Installed FLT dispatch and publication.

    This module composes the existing authority and kernel result boundaries;
    it does not define another evaluator. Kernel.Decision is the result of the
    complete requested action, including normalization when declared. The
    separately supplied structural codec must still receive a concrete
    semantic-preservation proof before its Rust implementation is accepted.
    The traversal below proves all-or-error transport for every such codec,
    not correctness of an arbitrary codec.

    Identifiers and work are mathematical naturals. Exact name resolution,
    cryptographic commitments, finite-integer overflow, and Rust source
    correspondence are separate implementation obligations.
*)

From Stdlib Require Import List Bool PeanoNat Lia.
From RuntimeGrammar Require Import CapabilitySeparation InstalledLanguageAuthority.
From RuntimeGrammar Require Import SemanticTransitionKernel.
Import ListNotations.

Module InstalledFltJudgments.
Module Kernel := SemanticTransitionKernel.SemanticTransitionKernel.

(** Canonical name resolution yields dense identifiers inside one installed
    language. Rule-backed actions have one admitted input sort. *)
Record Action := {
  action_input_sort : nat;
  action_output_sort : nat;
  action_rights : list LanguageRight
}.

Record Observation := {
  observation_action : nat;
  observation_result_sort : nat
}.

Inductive Operation :=
| ReduceAction (action : nat)
| ObserveDeclaration (observation : nat).

Record Selection := {
  selected_action_id : nat;
  selected_action : Action;
  selected_observation : option nat
}.

Definition select_operation (actions : list Action)
    (observations : list Observation) (operation : Operation)
    : option Selection :=
  match operation with
  | ReduceAction id =>
      match nth_error actions id with
      | None => None
      | Some action => Some {| selected_action_id := id;
          selected_action := action; selected_observation := None |}
      end
  | ObserveDeclaration id =>
      match nth_error observations id with
      | None => None
      | Some observation =>
          match nth_error actions (observation_action observation) with
          | None => None
          | Some action =>
              if Nat.eqb (observation_result_sort observation)
                         (action_output_sort action)
              then Some {| selected_action_id := observation_action observation;
                  selected_action := action; selected_observation := Some id |}
              else None
          end
      end
  end.

Definition required_rights (selection : Selection) : list LanguageRight :=
  match selected_observation selection with
  | None => Reduce :: action_rights (selected_action selection)
  | Some _ => Observe :: action_rights (selected_action selection)
  end.

Theorem reduce_selects_only_the_requested_action :
  forall actions observations id selection,
    select_operation actions observations (ReduceAction id) = Some selection ->
    selected_action_id selection = id /\
    nth_error actions id = Some (selected_action selection) /\
    selected_observation selection = None.
Proof.
  intros actions observations id selection Hselect.
  unfold select_operation in Hselect.
  destruct (nth_error actions id) as [action|] eqn:Haction; try discriminate.
  inversion Hselect; subst. simpl. auto.
Qed.

Theorem observation_selects_its_declared_action_and_result :
  forall actions observations id selection,
    select_operation actions observations (ObserveDeclaration id) = Some selection ->
    exists observation,
      nth_error observations id = Some observation /\
      selected_action_id selection = observation_action observation /\
      nth_error actions (observation_action observation) =
        Some (selected_action selection) /\
      observation_result_sort observation =
        action_output_sort (selected_action selection) /\
      selected_observation selection = Some id.
Proof.
  intros actions observations id selection Hselect.
  unfold select_operation in Hselect.
  destruct (nth_error observations id) as [observation|] eqn:Hobservation;
    try discriminate.
  destruct (nth_error actions (observation_action observation))
    as [action|] eqn:Haction; try discriminate.
  destruct (Nat.eqb (observation_result_sort observation)
                   (action_output_sort action)) eqn:Hsort; try discriminate.
  apply Nat.eqb_eq in Hsort.
  inversion Hselect; subst. exists observation. simpl. auto.
Qed.

Theorem unknown_observation_has_no_action_fallback :
  forall actions observations id,
    nth_error observations id = None ->
    select_operation actions observations (ObserveDeclaration id) = None.
Proof. intros actions observations id H. unfold select_operation. now rewrite H. Qed.

Theorem every_selected_reduction_requires_reduce :
  forall selection,
    selected_observation selection = None ->
    In Reduce (required_rights selection).
Proof. intros selection H. unfold required_rights. rewrite H. now left. Qed.

Theorem every_selected_observation_requires_observe :
  forall selection id,
    selected_observation selection = Some id ->
    In Observe (required_rights selection).
Proof. intros selection id H. unfold required_rights. rewrite H. simpl. auto. Qed.

Theorem action_requirements_are_not_erased :
  forall selection right,
    In right (action_rights (selected_action selection)) ->
    In right (required_rights selection).
Proof.
  intros selection right Hin. unfold required_rights.
  destruct (selected_observation selection); simpl; auto.
Qed.

(** Every resource dimension has its own ceiling. Logical work covers the
    whole request, including the codec; receipt fields do not replenish it. *)
Inductive Dimension :=
| LogicalWork | NormalizationSteps | OutputCount | FrontierCount
| ProofCount | ProofNodes | InputNodes | InputBytes | OutputNodes | OutputAtoms.

Definition Limits := Dimension -> nat.
Definition effective_limits (installed host requested : Limits) : Limits :=
  fun dimension => Nat.min (installed dimension)
    (Nat.min (host dimension) (requested dimension)).

Theorem effective_limits_cannot_amplify_any_ceiling :
  forall installed host requested dimension,
    effective_limits installed host requested dimension <= installed dimension /\
    effective_limits installed host requested dimension <= host dimension /\
    effective_limits installed host requested dimension <= requested dimension.
Proof.
  intros. unfold effective_limits.
  pose proof (Nat.le_min_l (installed dimension)
    (Nat.min (host dimension) (requested dimension))).
  pose proof (Nat.le_min_r (installed dimension)
    (Nat.min (host dimension) (requested dimension))).
  pose proof (Nat.le_min_l (host dimension) (requested dimension)).
  pose proof (Nat.le_min_r (host dimension) (requested dimension)). lia.
Qed.

Definition charge_work (ceiling used charge : nat) : option nat :=
  if Nat.leb (used + charge) ceiling then Some (used + charge) else None.

Theorem successful_charge_preserves_prefix_and_ceiling :
  forall ceiling used charge total,
    charge_work ceiling used charge = Some total ->
    total = used + charge /\ used <= total /\ total <= ceiling.
Proof.
  intros ceiling used charge total Hcharge. unfold charge_work in Hcharge.
  destruct (Nat.leb (used + charge) ceiling) eqn:Hlimit; try discriminate.
  apply Nat.leb_le in Hlimit. inversion Hcharge; subst. lia.
Qed.

(** A codec contributes abstract payload atoms only. The exact kernel result and its
    receipt remain attached by this traversal, never reconstructed from a tag
    or backend e-class identifier. The accumulator is private until EOF. *)
Record EncodedResult := {
  encoded_source : Kernel.ProvenTransition;
  encoded_payload : list nat
}.

Fixpoint encode_pending
    (encode : Kernel.ProvenTransition -> Kernel.Decision (list nat))
    (pending : list Kernel.ProvenTransition) (private : list EncodedResult)
    : Kernel.Decision (list EncodedResult) :=
  match pending with
  | [] => Kernel.Proven (rev private)
  | source :: rest =>
      match encode source with
      | Kernel.Proven payload =>
          encode_pending encode rest
            ({| encoded_source := source; encoded_payload := payload |} :: private)
      | Kernel.Refuted reason => Kernel.Refuted reason
      | Kernel.Undetermined reason => Kernel.Undetermined reason
      end
  end.

Lemma successful_encoding_keeps_the_entire_ordered_source :
  forall pending encode private exports,
    encode_pending encode pending private = Kernel.Proven exports ->
    map encoded_source exports = rev (map encoded_source private) ++ pending.
Proof.
  induction pending as [|source rest IH]; intros encode private exports Hencode.
  - simpl in Hencode. inversion Hencode; subst.
    rewrite map_rev. now rewrite app_nil_r.
  - simpl in Hencode.
    destruct (encode source) as [payload|reason|reason] eqn:Hsource;
      try discriminate.
    apply IH in Hencode. rewrite Hencode. simpl.
    rewrite <- app_assoc. reflexivity.
Qed.

Definition prepare_results
    (encode : Kernel.ProvenTransition -> Kernel.Decision (list nat))
    (kernel_result : Kernel.Decision (list Kernel.ProvenTransition))
    : Kernel.Decision (list EncodedResult) :=
  match kernel_result with
  | Kernel.Proven results => encode_pending encode results []
  | Kernel.Refuted reason => Kernel.Refuted reason
  | Kernel.Undetermined reason => Kernel.Undetermined reason
  end.

Theorem successful_preparation_preserves_every_result_and_receipt :
  forall encode result exports,
    prepare_results encode result = Kernel.Proven exports ->
    exists sources, result = Kernel.Proven sources /\
      map encoded_source exports = sources.
Proof.
  intros encode result exports Hprepare.
  destruct result as [sources|reason|reason]; simpl in Hprepare; try discriminate.
  exists sources. split; [reflexivity|].
  apply successful_encoding_keeps_the_entire_ordered_source in Hprepare.
  exact Hprepare.
Qed.

Theorem rejected_kernel_result_stays_rejected :
  forall encode reason,
    prepare_results encode (Kernel.Refuted reason) = Kernel.Refuted reason.
Proof. reflexivity. Qed.

Theorem exhausted_kernel_result_stays_undetermined :
  forall encode reason,
    prepare_results encode (Kernel.Undetermined reason) = Kernel.Undetermined reason.
Proof. reflexivity. Qed.

Definition visible_exports (decision : Kernel.Decision (list EncodedResult)) :=
  match decision with
  | Kernel.Proven exports => exports
  | Kernel.Refuted _ | Kernel.Undetermined _ => []
  end.

Theorem codec_exhaustion_discards_an_arbitrary_private_prefix :
  forall encode source rest private reason,
    encode source = Kernel.Undetermined reason ->
    visible_exports (encode_pending encode (source :: rest) private) = [].
Proof. intros encode source rest private reason H. simpl. now rewrite H. Qed.

Theorem codec_rejection_discards_an_arbitrary_private_prefix :
  forall encode source rest private reason,
    encode source = Kernel.Refuted reason ->
    visible_exports (encode_pending encode (source :: rest) private) = [].
Proof. intros encode source rest private reason H. simpl. now rewrite H. Qed.

(** The authority model covers every current Rust LanguageRight. This total
    encoding is an injective bridge to the kernel's abstract natural IDs. *)
Definition right_id (right : LanguageRight) : nat :=
  match right with
  | Parse => 0 | Construct => 1 | Match => 2 | Observe => 3 | ReflectAst => 4
  | Reduce => 5 | Bridge => 6 | Publish => 7 | Introspect => 8
  | Check => 9 | SearchProof => 10 | Spend => 11
  end.

Theorem right_id_is_injective :
  forall left right, right_id left = right_id right -> left = right.
Proof. intros left right. destruct left, right; simpl; congruence. Qed.

Record InstalledBundle := {
  bundle_manifest : Kernel.KernelManifest;
  bundle_actions : list Action;
  bundle_observations : list Observation;
  bundle_limits : Limits;
  bundle_matcher_image : Kernel.Commitment
}.

(** The store is the trusted installed table, keyed by the authority entry's
    commitment. It is not supplied by a reflected tag or by the caller. *)
Definition BundleStore := Commitment -> option InstalledBundle.

Record Invocation := {
  invocation_handle : InstalledHandle;
  invocation_bundle : InstalledBundle;
  invocation_selection : Selection;
  invocation_input_sort : nat;
  invocation_input_key : Kernel.Commitment;
  invocation_decode_work : nat;
  invocation_host_limits : Limits;
  invocation_requested_limits : Limits
}.

Definition invocation_limits (call : Invocation) : Limits :=
  effective_limits (bundle_limits (invocation_bundle call))
    (invocation_host_limits call) (invocation_requested_limits call).

Definition invocation_request (call : Invocation) : Kernel.TransitionRequest :=
  let manifest := bundle_manifest (invocation_bundle call) in
  {| Kernel.request_language := Kernel.manifest_language manifest;
     Kernel.request_theory := Kernel.manifest_theory manifest;
     Kernel.request_image := Kernel.manifest_image manifest;
     Kernel.request_action := selected_action_id (invocation_selection call);
     Kernel.request_input := invocation_input_key call;
     Kernel.request_granted_rights := map right_id
       (handle_rights (invocation_handle call)) |}.

Definition resolved_invocation (store : BundleStore) (before : InstalledEntry)
    (operation : Operation) (call : Invocation) : Prop :=
  store (entry_commitment before) = Some (invocation_bundle call) /\
  select_operation (bundle_actions (invocation_bundle call))
    (bundle_observations (invocation_bundle call)) operation =
    Some (invocation_selection call) /\
  invocation_input_sort call =
    action_input_sort (selected_action (invocation_selection call)) /\
  bundle_matcher_image (invocation_bundle call) =
    Kernel.manifest_image (bundle_manifest (invocation_bundle call)) /\
  (exists manifest_action,
    Kernel.find_action (selected_action_id (invocation_selection call))
      (Kernel.manifest_actions (bundle_manifest (invocation_bundle call))) =
        Some manifest_action /\
    Kernel.manifest_required_rights manifest_action =
      map right_id (action_rights (selected_action (invocation_selection call)))) /\
  Kernel.request_admitted (bundle_manifest (invocation_bundle call))
    (invocation_request call) = true.

(** The complete execution boundary is a parameter, not an axiom asserting
    correctness. Its result is obtained only by applying it to this manifest,
    derived request and attenuated limits. Kernel correctness and normalization
    refinements are separate proofs of a concrete instantiation. *)
Record KernelExecution := {
  execution_decision : Kernel.Decision (list Kernel.ProvenTransition);
  execution_usage : Limits
}.

Definition KernelBoundary := Kernel.KernelManifest -> Kernel.TransitionRequest ->
  Limits -> KernelExecution.

Definition invoke_kernel (run : KernelBoundary) (call : Invocation) :=
  run (bundle_manifest (invocation_bundle call)) (invocation_request call)
    (invocation_limits call).

Definition receipts_bound (call : Invocation) (results : list Kernel.ProvenTransition) :=
  forallb (fun source => Kernel.receipt_bound
    (bundle_manifest (invocation_bundle call)) (invocation_request call)
    (Kernel.proven_transition source) (Kernel.proven_receipt source)) results.

(** Every receipt repeats the one execution aggregate, not a per-result charge.
    Binding identity alone cannot rule out an under-reported work aggregate. *)
Definition receipt_work_agrees (execution : KernelExecution)
    (results : list Kernel.ProvenTransition) : bool :=
  forallb (fun source => Nat.eqb
    (Kernel.receipt_work (Kernel.proven_receipt source))
    (execution_usage execution LogicalWork)) results.

(** Encoding size is measured in the abstract wire atoms used by this model:
    nine scalar fields plus all receipt commitment/effect atoms and payload
    atoms. Concrete byte encoding and traversal costs must refine these
    measures; the model does not treat a mathematical nat as one Rust byte. *)
Definition receipt_atoms (receipt : Kernel.TransitionReceipt) : nat :=
  9 + length (Kernel.receipt_language receipt) +
  length (Kernel.receipt_theory receipt) + length (Kernel.receipt_image receipt) +
  length (Kernel.receipt_input receipt) + length (Kernel.receipt_output receipt) +
  length (Kernel.receipt_effects receipt) +
  match Kernel.receipt_grade receipt with
  | Kernel.NoSemanticGrade => 0
  | Kernel.CheckedSemanticGrade grade => length grade
  end.

Definition exported_atoms (exports : list EncodedResult) : nat :=
  fold_left (fun total export => total + length (encoded_payload export) +
    receipt_atoms (Kernel.proven_receipt (encoded_source export))) exports 0.

Definition publication_usage (call : Invocation) (execution : KernelExecution)
    (exports : list EncodedResult) : Limits :=
  fun dimension => match dimension with
  | LogicalWork => invocation_decode_work call + execution_usage execution LogicalWork +
      length exports + exported_atoms exports
  | OutputCount => length exports
  | OutputAtoms => exported_atoms exports
  | _ => execution_usage execution dimension
  end.

Definition dimensions : list Dimension :=
  [LogicalWork; NormalizationSteps; OutputCount; FrontierCount; ProofCount;
   ProofNodes; InputNodes; InputBytes; OutputNodes; OutputAtoms].

Lemma dimensions_complete : forall dimension, In dimension dimensions.
Proof. intros dimension. destruct dimension; simpl; auto 12. Qed.

Definition usage_within (usage ceiling : Limits) : bool :=
  forallb (fun dimension => Nat.leb (usage dimension) (ceiling dimension)) dimensions.

Lemma usage_within_sound :
  forall usage ceiling, usage_within usage ceiling = true ->
    forall dimension, usage dimension <= ceiling dimension.
Proof.
  intros usage ceiling H dimension. unfold usage_within in H.
  apply forallb_forall with (x := dimension) in H; [|apply dimensions_complete].
  now apply Nat.leb_le in H.
Qed.

Definition prepare_invocation (run : KernelBoundary)
    (encode : nat -> Kernel.ProvenTransition -> Kernel.Decision (list nat))
    (call : Invocation) : Kernel.Decision (list EncodedResult) :=
  let execution := invoke_kernel run call in
  match execution_decision execution with
  | Kernel.Refuted reason => Kernel.Refuted reason
  | Kernel.Undetermined reason => Kernel.Undetermined reason
  | Kernel.Proven results =>
      if receipts_bound call results && receipt_work_agrees execution results then
        match prepare_results
          (encode (action_output_sort (selected_action (invocation_selection call))))
          (Kernel.Proven results) with
        | Kernel.Refuted reason => Kernel.Refuted reason
        | Kernel.Undetermined reason => Kernel.Undetermined reason
        | Kernel.Proven exports =>
            if usage_within (execution_usage execution) (invocation_limits call) &&
               usage_within (publication_usage call execution exports) (invocation_limits call)
            then Kernel.Proven exports
            else Kernel.Undetermined Kernel.WorkBudgetExhausted
        end
      else Kernel.Undetermined Kernel.InvalidInternalEvidence
  end.

Lemma prepared_invocation_is_bound_and_metered :
  forall run encode call exports,
    prepare_invocation run encode call = Kernel.Proven exports ->
    exists results,
      execution_decision (invoke_kernel run call) = Kernel.Proven results /\
      receipts_bound call results = true /\
      map encoded_source exports = results /\
      usage_within (execution_usage (invoke_kernel run call)) (invocation_limits call) = true /\
      usage_within (publication_usage call (invoke_kernel run call) exports)
        (invocation_limits call) = true /\
      receipt_work_agrees (invoke_kernel run call) results = true.
Proof.
  intros run encode call exports Hprepare. unfold prepare_invocation in Hprepare.
  destruct (execution_decision (invoke_kernel run call)) as [results|reason|reason]
    eqn:Hresult; try discriminate.
  destruct (receipts_bound call results &&
    receipt_work_agrees (invoke_kernel run call) results) eqn:Hreceipts; try discriminate.
  apply andb_true_iff in Hreceipts as [Hbound Hwork].
  destruct (prepare_results
    (encode (action_output_sort (selected_action (invocation_selection call))))
    (Kernel.Proven results)) as [prepared|reason|reason] eqn:Hencoded; try discriminate.
  destruct (usage_within (execution_usage (invoke_kernel run call)) (invocation_limits call) &&
    usage_within (publication_usage call (invoke_kernel run call) prepared)
      (invocation_limits call)) eqn:Husage; try discriminate.
  inversion Hprepare; subst prepared. apply andb_true_iff in Husage.
  apply successful_preparation_preserves_every_result_and_receipt in Hencoded.
  destruct Hencoded as [sources [Heq Hsources]]. inversion Heq; subst sources.
  exists results. intuition congruence.
Qed.

(** Successful encoding alone is not publication authority. This relation is
    the final service commit, not a later asynchronous RSpace produce or node
    settlement. Its result is obtained by the same resolved invocation. *)
Inductive Publishes (store : BundleStore) (before after : InstalledEntry)
    (operation : Operation) (call : Invocation) (run : KernelBoundary)
    (encode : nat -> Kernel.ProvenTransition -> Kernel.Decision (list nat))
    : list EncodedResult -> Prop :=
| PublishAll : forall exports,
    resolved_invocation store before operation call ->
    revalidated_operation before after (invocation_handle call)
      (required_rights (invocation_selection call)) ->
    prepare_invocation run encode call = Kernel.Proven exports ->
    Publishes store before after operation call run encode exports.

Theorem publication_rechecks_all_required_rights_at_both_epochs :
  forall store before after operation call run encode exports right,
    Publishes store before after operation call run encode exports ->
    In right (required_rights (invocation_selection call)) ->
    authorize before (invocation_handle call) right /\
    authorize after (invocation_handle call) right.
Proof.
  intros store before after operation call run encode exports right Hpublish Hin.
  inversion Hpublish as [published Hresolved [Hbefore Hafter] Hprepared]; subst.
  split; eapply authorize_all_covers_every_requested_right; eauto.
Qed.

Theorem revoked_completion_publishes_nothing :
  forall store before operation call run encode exports,
    ~ Publishes store before (revoke before) operation call run encode exports.
Proof.
  intros store before operation call run encode exports Hpublish.
  inversion Hpublish as [published Hresolved Hrevalidated Hprepared]; subst.
  eapply revoked_completion_fails_revalidation. exact Hrevalidated.
Qed.

Theorem publication_preserves_the_complete_invoked_result :
  forall store before after operation call run encode exports,
    Publishes store before after operation call run encode exports ->
    exists sources, execution_decision (invoke_kernel run call) = Kernel.Proven sources /\
      map encoded_source exports = sources.
Proof.
  intros store before after operation call run encode exports Hpublish.
  inversion Hpublish as [published Hresolved Hrevalidated Hprepared]; subst.
  apply prepared_invocation_is_bound_and_metered in Hprepared.
  destruct Hprepared as [sources [Hresult [_ [Hsources _]]]]. exists sources. auto.
Qed.

Theorem publication_requires_exact_installed_selection_and_input_sort :
  forall store before after operation call run encode exports,
    Publishes store before after operation call run encode exports ->
    store (entry_commitment before) = Some (invocation_bundle call) /\
    select_operation (bundle_actions (invocation_bundle call))
      (bundle_observations (invocation_bundle call)) operation =
      Some (invocation_selection call) /\
    invocation_input_sort call =
      action_input_sort (selected_action (invocation_selection call)).
Proof.
  intros store before after operation call run encode exports Hpublish.
  inversion Hpublish as [published Hresolved Hrevalidated Hprepared]; subst.
  unfold resolved_invocation in Hresolved. tauto.
Qed.

Theorem every_published_receipt_binds_the_exact_request :
  forall store before after operation call run encode exports export,
    Publishes store before after operation call run encode exports ->
    In export exports ->
    Kernel.receipt_bound (bundle_manifest (invocation_bundle call))
      (invocation_request call) (Kernel.proven_transition (encoded_source export))
      (Kernel.proven_receipt (encoded_source export)) = true.
Proof.
  intros store before after operation call run encode exports export Hpublish Hin.
  inversion Hpublish as [published Hresolved Hrevalidated Hprepared]; subst.
  apply prepared_invocation_is_bound_and_metered in Hprepared.
  destruct Hprepared as [sources [Hresult [Hreceipts [Hsources _]]]].
  unfold receipts_bound in Hreceipts. rewrite <- Hsources in Hreceipts.
  apply forallb_forall with (x := encoded_source export) in Hreceipts.
  - exact Hreceipts.
  - now apply in_map.
Qed.

Theorem published_usage_respects_every_effective_ceiling :
  forall store before after operation call run encode exports dimension,
    Publishes store before after operation call run encode exports ->
    publication_usage call (invoke_kernel run call) exports dimension <=
      invocation_limits call dimension.
Proof.
  intros store before after operation call run encode exports dimension Hpublish.
  inversion Hpublish as [published Hresolved Hrevalidated Hprepared]; subst.
  apply prepared_invocation_is_bound_and_metered in Hprepared.
  destruct Hprepared as [sources [_ [_ [_ [_ [Husage _]]]]]].
  now apply usage_within_sound with (dimension := dimension) in Husage.
Qed.

Theorem every_published_receipt_reports_the_single_execution_aggregate :
  forall store before after operation call run encode exports export,
    Publishes store before after operation call run encode exports ->
    In export exports ->
    Kernel.receipt_work (Kernel.proven_receipt (encoded_source export)) =
      execution_usage (invoke_kernel run call) LogicalWork.
Proof.
  intros store before after operation call run encode exports export Hpublish Hin.
  inversion Hpublish as [published Hresolved Hrevalidated Hprepared]; subst.
  apply prepared_invocation_is_bound_and_metered in Hprepared.
  destruct Hprepared as [sources [_ [_ [Hsources [_ [_ Hwork]]]]]].
  unfold receipt_work_agrees in Hwork. rewrite <- Hsources in Hwork.
  apply forallb_forall with (x := encoded_source export) in Hwork.
  - now apply Nat.eqb_eq in Hwork.
  - now apply in_map.
Qed.

Theorem mismatched_receipt_work_prevents_successful_preparation :
  forall run encode call results,
    execution_decision (invoke_kernel run call) = Kernel.Proven results ->
    receipt_work_agrees (invoke_kernel run call) results = false ->
    prepare_invocation run encode call =
      Kernel.Undetermined Kernel.InvalidInternalEvidence.
Proof.
  intros run encode call results Hresult Hwork.
  unfold prepare_invocation. rewrite Hresult, Hwork, andb_false_r. reflexivity.
Qed.

Theorem zero_output_ceiling_forbids_nonempty_publication :
  forall store before after operation call run encode exports,
    invocation_limits call OutputCount = 0 ->
    Publishes store before after operation call run encode exports ->
    exports = [].
Proof.
  intros store before after operation call run encode exports Hzero Hpublish.
  pose proof (published_usage_respects_every_effective_ceiling
    store before after operation call run encode exports OutputCount Hpublish) as Husage.
  rewrite Hzero in Husage. unfold publication_usage in Husage.
  destruct exports; [reflexivity|simpl in Husage; lia].
Qed.

Theorem invoked_exhaustion_cannot_publish_an_empty_success :
  forall store before after operation call run encode exports reason,
    execution_decision (invoke_kernel run call) = Kernel.Undetermined reason ->
    ~ Publishes store before after operation call run encode exports.
Proof.
  intros store before after operation call run encode exports reason Hstop Hpublish.
  apply publication_preserves_the_complete_invoked_result in Hpublish.
  destruct Hpublish as [sources [Hsuccess _]]. rewrite Hstop in Hsuccess. discriminate.
Qed.

(** The kernel reports aggregate request work, repeated in each transition
    receipt. Host work uses the aggregate once, plus boundary work. *)
Definition request_work (decode_work kernel_work encode_work : nat) :=
  decode_work + kernel_work + encode_work.

Theorem shared_kernel_work_is_charged_once :
  forall decode_work kernel_work encode_work ceiling total,
    charge_work ceiling (decode_work + kernel_work) encode_work = Some total ->
    total = request_work decode_work kernel_work encode_work /\ total <= ceiling.
Proof.
  intros decode_work kernel_work encode_work ceiling total Hcharge.
  apply successful_charge_preserves_prefix_and_ceiling in Hcharge.
  unfold request_work. tauto.
Qed.

Example declared_observation_resolves_without_reflection_right :
  let action := {| action_input_sort := 0; action_output_sort := 1;
                   action_rights := [Reduce] |} in
  let observation := {| observation_action := 0; observation_result_sort := 1 |} in
  select_operation [action] [observation] (ObserveDeclaration 0) =
    Some {| selected_action_id := 0; selected_action := action;
            selected_observation := Some 0 |}.
Proof. reflexivity. Qed.

Example mismatched_observation_result_is_rejected :
  select_operation
    [{| action_input_sort := 0; action_output_sort := 1; action_rights := [] |}]
    [{| observation_action := 0; observation_result_sort := 2 |}]
    (ObserveDeclaration 0) = None.
Proof. reflexivity. Qed.

Example exhausted_work_cannot_reset_the_consumed_prefix :
  charge_work 10 8 3 = None.
Proof. reflexivity. Qed.

Example observational_one_step_does_not_invent_reduce_authority :
  required_rights {| selected_action_id := 0;
    selected_action := {| action_input_sort := 0; action_output_sort := 1;
                           action_rights := [] |};
    selected_observation := Some 0 |} = [Observe].
Proof. reflexivity. Qed.

(** Closed counterexample to the old identity-only gate: a receipt with work
    100 matches the request, but an execution reporting zero work could fit a
    ceiling of 20. The new aggregate check rejects it before encoding. *)
Module WorkAgreementExamples.

Definition manifest : Kernel.KernelManifest :=
  {| Kernel.manifest_language := []; Kernel.manifest_theory := [];
     Kernel.manifest_image := [];
     Kernel.manifest_actions := [{| Kernel.manifest_action := 0;
       Kernel.manifest_required_rights := [];
       Kernel.manifest_resource_profile := Kernel.Uncosted |}];
     Kernel.manifest_deterministic_actions := [] |}.

Definition source (work : nat) : Kernel.ProvenTransition :=
  {| Kernel.proven_transition := {| Kernel.transition_action := 0;
       Kernel.transition_rule := 0; Kernel.transition_input := [];
       Kernel.transition_output := []; Kernel.transition_grade := Kernel.NoSemanticGrade;
       Kernel.transition_observation := []; Kernel.transition_effects := [] |};
     Kernel.proven_receipt := {| Kernel.receipt_language := [];
       Kernel.receipt_theory := []; Kernel.receipt_image := [];
       Kernel.receipt_action := 0; Kernel.receipt_rule := 0;
       Kernel.receipt_input := []; Kernel.receipt_output := [];
       Kernel.receipt_grade := Kernel.NoSemanticGrade;
       Kernel.receipt_effects := []; Kernel.receipt_work := work |} |}.

Definition action : Action :=
  {| action_input_sort := 0; action_output_sort := 0; action_rights := [] |}.

Definition call : Invocation :=
  {| invocation_handle := {| handle_generation := 0; handle_commitment := 0;
       handle_rights := [Reduce]; handle_seal := 0 |};
     invocation_bundle := {| bundle_manifest := manifest; bundle_actions := [action];
       bundle_observations := []; bundle_limits := fun _ => 20;
       bundle_matcher_image := [] |};
     invocation_selection := {| selected_action_id := 0; selected_action := action;
       selected_observation := None |};
     invocation_input_sort := 0; invocation_input_key := []; invocation_decode_work := 0;
     invocation_host_limits := fun _ => 20; invocation_requested_limits := fun _ => 20 |}.

Definition run (receipt_work aggregate_work : nat) : KernelBoundary :=
  fun _ _ _ => {| execution_decision := Kernel.Proven [source receipt_work];
    execution_usage := fun dimension => match dimension with
      | LogicalWork => aggregate_work | _ => 0 end |}.

Definition encode (_ : nat) (_ : Kernel.ProvenTransition) : Kernel.Decision (list nat) :=
  Kernel.Proven [].

Example identity_checks_alone_miss_underreported_work :
  receipts_bound call [source 100] = true /\
  usage_within (execution_usage (invoke_kernel (run 100 0) call))
    (invocation_limits call) = true /\
  usage_within (publication_usage call (invoke_kernel (run 100 0) call)
    [{| encoded_source := source 100; encoded_payload := [] |}])
    (invocation_limits call) = true /\
  prepare_invocation (run 100 0) encode call =
    Kernel.Undetermined Kernel.InvalidInternalEvidence.
Proof. repeat split; reflexivity. Qed.

Example agreement_within_the_ceiling_prepares_the_complete_result :
  prepare_invocation (run 1 1) encode call =
    Kernel.Proven [{| encoded_source := source 1; encoded_payload := [] |}].
Proof. reflexivity. Qed.

End WorkAgreementExamples.

Print Assumptions reduce_selects_only_the_requested_action.
Print Assumptions observation_selects_its_declared_action_and_result.
Print Assumptions unknown_observation_has_no_action_fallback.
Print Assumptions every_selected_reduction_requires_reduce.
Print Assumptions every_selected_observation_requires_observe.
Print Assumptions action_requirements_are_not_erased.
Print Assumptions effective_limits_cannot_amplify_any_ceiling.
Print Assumptions successful_charge_preserves_prefix_and_ceiling.
Print Assumptions successful_preparation_preserves_every_result_and_receipt.
Print Assumptions rejected_kernel_result_stays_rejected.
Print Assumptions exhausted_kernel_result_stays_undetermined.
Print Assumptions codec_exhaustion_discards_an_arbitrary_private_prefix.
Print Assumptions codec_rejection_discards_an_arbitrary_private_prefix.
Print Assumptions publication_rechecks_all_required_rights_at_both_epochs.
Print Assumptions revoked_completion_publishes_nothing.
Print Assumptions right_id_is_injective.
Print Assumptions prepared_invocation_is_bound_and_metered.
Print Assumptions publication_preserves_the_complete_invoked_result.
Print Assumptions publication_requires_exact_installed_selection_and_input_sort.
Print Assumptions every_published_receipt_binds_the_exact_request.
Print Assumptions published_usage_respects_every_effective_ceiling.
Print Assumptions every_published_receipt_reports_the_single_execution_aggregate.
Print Assumptions mismatched_receipt_work_prevents_successful_preparation.
Print Assumptions WorkAgreementExamples.identity_checks_alone_miss_underreported_work.
Print Assumptions WorkAgreementExamples.agreement_within_the_ceiling_prepares_the_complete_result.
Print Assumptions zero_output_ceiling_forbids_nonempty_publication.
Print Assumptions invoked_exhaustion_cannot_publish_an_empty_success.
Print Assumptions shared_kernel_work_is_charged_once.

End InstalledFltJudgments.
