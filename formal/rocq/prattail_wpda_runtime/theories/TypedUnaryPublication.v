From Stdlib Require Import List Bool PeanoNat Lia.
From PrattailWpdaRuntime Require Import PurePackingPreservation.
Import ListNotations.
Set Implicit Arguments.

Module TypedUnaryPublication.

Record Signature := {
  arity : nat;
  inputs : list (option nat);
  output : option nat
}.

Definition unary_input (signature : option Signature) : option nat :=
  match signature with
  | Some {| arity := 1; inputs := [Some expected] |} => Some expected
  | _ => None
  end.

Definition reject (signature : option Signature) (body : option nat) : bool :=
  match unary_input signature, body with
  | Some expected, Some actual => negb (Nat.eqb actual expected)
  | _, _ => false
  end.

Definition certified_mismatch signature body : Prop :=
  exists expected actual,
    unary_input signature = Some expected /\
    body = Some actual /\ actual <> expected.

Theorem reject_exact_certificate : forall signature body,
  reject signature body = true <-> certified_mismatch signature body.
Proof.
  intros signature body. unfold reject, certified_mismatch.
  destruct (unary_input signature) as [expected|] eqn:Hinput;
    destruct body as [actual|].
  - rewrite Bool.negb_true_iff, Nat.eqb_neq. split.
    + intros H. exists expected, actual. auto.
    + intros [expected' [actual' [He [Ha Hneq]]]].
      inversion He; inversion Ha; subst. exact Hneq.
  - split; [discriminate|]. intros [? [? [_ [H _]]]]. discriminate.
  - split; [discriminate|]. intros [? [? [H _]]]. discriminate.
  - split; [discriminate|]. intros [? [? [H _]]]. discriminate.
Qed.

Theorem unary_input_exact_metadata : forall signature expected,
  unary_input signature = Some expected <->
  exists result, signature = Some {| arity := 1; inputs := [Some expected];
                                    output := result |}.
Proof.
  intros signature expected. split.
  - destruct signature as [[a ins out]|]; [|discriminate].
    destruct a as [|[|a]]; try discriminate.
    destruct ins as [|[input|] rest]; try discriminate;
      destruct rest; try discriminate.
    cbn. intros H. inversion H. exists out. reflexivity.
  - intros [result ->]. reflexivity.
Qed.

Theorem unknown_metadata_is_not_rejected : forall body,
  reject None body = false.
Proof. reflexivity. Qed.

Theorem unknown_body_is_not_rejected : forall signature,
  reject signature None = false.
Proof. intros. unfold reject. destruct (unary_input signature); reflexivity. Qed.

Theorem uncertified_signature_is_not_rejected : forall signature body,
  unary_input signature = None -> reject signature body = false.
Proof. intros. unfold reject. now rewrite H. Qed.

Theorem wildcard_is_not_rejected : forall result body,
  reject (Some {| arity := 1; inputs := [None]; output := result |}) body = false.
Proof. reflexivity. Qed.

Theorem matching_input_is_not_rejected : forall signature category,
  unary_input signature = Some category -> reject signature (Some category) = false.
Proof. intros. unfold reject. rewrite H, Nat.eqb_refl. reflexivity. Qed.

Theorem mismatching_input_is_rejected : forall signature actual expected,
  unary_input signature = Some expected -> actual <> expected ->
  reject signature (Some actual) = true.
Proof.
  intros. apply reject_exact_certificate. exists expected, actual. auto.
Qed.

Definition rename_signature (rename : nat -> nat) (signature : Signature) :=
  {| arity := arity signature;
     inputs := map (option_map rename) (inputs signature);
     output := option_map rename (output signature) |}.

Lemma unary_input_renamed : forall rename signature,
  unary_input (option_map (rename_signature rename) signature) =
  option_map rename (unary_input signature).
Proof.
  intros rename [[a ins out]|]; [|reflexivity].
  destruct a as [|[|a]]; try reflexivity.
  destruct ins as [|[input|] rest]; try reflexivity;
    destruct rest; reflexivity.
Qed.

Theorem category_renaming_preserves_rejection : forall rename,
  (forall left right, rename left = rename right -> left = right) ->
  forall signature body,
  reject (option_map (rename_signature rename) signature) (option_map rename body) =
  reject signature body.
Proof.
  intros rename Hinj signature body. unfold reject. rewrite unary_input_renamed.
  destruct (unary_input signature) as [expected|]; destruct body as [actual|];
    try reflexivity. cbn.
  destruct (Nat.eqb actual expected) eqn:Hsame.
  - apply Nat.eqb_eq in Hsame. subst. now rewrite Nat.eqb_refl.
  - assert (Nat.eqb (rename actual) (rename expected) = false).
    { apply Nat.eqb_neq. intro He. apply Hinj in He. subst.
      rewrite Nat.eqb_refl in Hsame. discriminate. }
    now rewrite H.
Qed.

Section TypedMeaning.
Context {Value Fault : Type}.
Variable category_of : Value -> nat.
Variable action : option Signature -> Value -> Fault + option Value.
Hypothesis action_input_contract : forall signature expected value,
  unary_input signature = Some expected -> category_of value <> expected ->
  action signature value = inr None.

Definition symbol_is_typed body values :=
  forall actual, body = Some actual ->
    Forall (fun value => category_of value = actual) values.

Theorem certified_mismatch_rejects_every_typed_value : forall signature body values,
  symbol_is_typed body values -> reject signature body = true ->
  Forall (fun value => action signature value = inr None) values.
Proof.
  intros signature body values Htyped Hreject.
  apply reject_exact_certificate in Hreject.
  destruct Hreject as [expected [actual [Hinput [Hbody Hneq]]]].
  specialize (Htyped actual Hbody).
  eapply Forall_impl; [|exact Htyped].
  intros value Hcat. apply (@action_input_contract signature expected value Hinput).
  now rewrite Hcat.
Qed.

Definition successful_values signature value : list Value :=
  match action signature value with inr (Some result) => [result] | _ => [] end.

Lemma rejected_values_have_no_success : forall signature values,
  Forall (fun value => action signature value = inr None) values ->
  flat_map (successful_values signature) values = [].
Proof.
  intros signature values H. induction H; [reflexivity|].
  cbn. unfold successful_values. rewrite H. cbn. exact IHForall.
Qed.

Theorem rejection_preserves_typed_successes : forall signature body values,
  symbol_is_typed body values ->
  (if reject signature body then [] else flat_map (successful_values signature) values) =
  flat_map (successful_values signature) values.
Proof.
  intros signature body values Htyped.
  destruct (reject signature body) eqn:Hreject; [|reflexivity].
  symmetry. apply rejected_values_have_no_success.
  exact (@certified_mismatch_rejects_every_typed_value signature body values Htyped Hreject).
Qed.
End TypedMeaning.

Inductive FrameClass := D1 | D2.
Inductive SymbolKind := Return | RuleAt (position : nat) | MixfixMarker | Structural.
Record Boundary := {
  frame_class : FrameClass;
  symbol_kind : SymbolKind;
  spine_rule : bool
}.

Definition eligible boundary :=
  match frame_class boundary, symbol_kind boundary with
  | D1, Return | D1, RuleAt _ | D1, MixfixMarker => negb (spine_rule boundary)
  | _, _ => false
  end.

Theorem d2_is_ineligible : forall kind spine,
  eligible {| frame_class := D2; symbol_kind := kind; spine_rule := spine |} = false.
Proof. intros. destruct kind; reflexivity. Qed.

Theorem structural_pop_is_ineligible : forall frame spine,
  eligible {| frame_class := frame; symbol_kind := Structural; spine_rule := spine |} = false.
Proof. intros. destruct frame; reflexivity. Qed.

Theorem spine_rule_is_ineligible : forall frame kind,
  eligible {| frame_class := frame; symbol_kind := kind; spine_rule := true |} = false.
Proof. intros. destruct frame, kind; reflexivity. Qed.

Record Request (Payload : Type) := {
  request_boundary : Boundary;
  request_signature : option Signature;
  request_body : option nat;
  request_payload : Payload
}.
Arguments request_boundary {Payload} _.
Arguments request_signature {Payload} _.
Arguments request_body {Payload} _.
Arguments request_payload {Payload} _.

Definition request_rejected {Payload} (request : Request Payload) :=
  eligible (request_boundary request) &&
    reject (request_signature request) (request_body request).

Definition request_mismatch {Payload} (request : Request Payload) :=
  eligible (request_boundary request) = true /\
    certified_mismatch (request_signature request) (request_body request).

Theorem request_rejection_exact : forall Payload (request : Request Payload),
  request_rejected request = true <-> request_mismatch request.
Proof.
  intros. unfold request_rejected, request_mismatch.
  rewrite Bool.andb_true_iff, reject_exact_certificate. reflexivity.
Qed.

Theorem ineligible_request_is_unchanged : forall Payload (request : Request Payload),
  eligible (request_boundary request) = false -> request_rejected request = false.
Proof. intros. unfold request_rejected. now rewrite H. Qed.

Section Publication.
Context {Payload State Fault : Type}.
Variable original : Request Payload -> State -> Fault + State.

Definition publish request state :=
  if request_rejected request then inr state else original request state.

Inductive reference_step (request : Request Payload) (state : State)
    : Fault + State -> Prop :=
| ReferenceReject : request_mismatch request ->
    reference_step request state (inr state)
| ReferenceKeep : ~ request_mismatch request ->
    reference_step request state (original request state).

Theorem publication_matches_typed_reference : forall request state result,
  publish request state = result <-> reference_step request state result.
Proof.
  intros request state result. split.
  - unfold publish. destruct (request_rejected request) eqn:Hreject; intros <-.
    + constructor. now apply request_rejection_exact.
    + apply ReferenceKeep. intros H. apply request_rejection_exact in H. congruence.
  - intros H. inversion H; subst; unfold publish.
    + apply request_rejection_exact in H0. now rewrite H0.
    + destruct (request_rejected request) eqn:Hreject;
        [|reflexivity]. exfalso. apply H0. now apply request_rejection_exact.
Qed.

Theorem rejected_publication_preserves_all_state : forall request state,
  request_rejected request = true -> publish request state = inr state.
Proof. intros. unfold publish. now rewrite H. Qed.

Theorem retained_publication_is_exact : forall request state,
  request_rejected request = false -> publish request state = original request state.
Proof. intros. unfold publish. now rewrite H. Qed.

Theorem retained_error_is_exact : forall request state fault,
  request_rejected request = false -> original request state = inl fault ->
  publish request state = inl fault.
Proof. intros. now rewrite retained_publication_is_exact. Qed.
End Publication.

Definition admitted_requests {Payload} (requests : list (Request Payload)) :=
  filter (fun request => negb (request_rejected request)) requests.

Inductive reference_trace {Payload} : list (Request Payload) -> list (Request Payload) -> Prop :=
| ReferenceNil : reference_trace [] []
| ReferenceCons : forall request tail kept,
    ~ request_mismatch request ->
    reference_trace tail kept -> reference_trace (request :: tail) (request :: kept)
| ReferenceSkip : forall request tail kept,
    request_mismatch request ->
    reference_trace tail kept -> reference_trace (request :: tail) kept.

Theorem ordered_typed_reference : forall Payload requests kept,
  @reference_trace Payload requests kept <-> kept = admitted_requests requests.
Proof.
  intros Payload requests kept. split.
  - intros H. induction H; [reflexivity| |].
    + unfold admitted_requests in *. cbn.
      destruct (request_rejected request) eqn:Hreject.
      * exfalso. apply H. now apply request_rejection_exact.
      * cbn. now rewrite IHreference_trace.
    + apply request_rejection_exact in H.
      unfold admitted_requests. cbn. rewrite H. cbn.
      exact IHreference_trace.
  - intros ->. induction requests as [|request tail IH]; [constructor|].
    unfold admitted_requests in *. cbn.
    destruct (request_rejected request) eqn:Hreject; cbn.
    + apply ReferenceSkip; [now apply request_rejection_exact|exact IH].
    + apply ReferenceCons; [|exact IH]. intro H.
      apply request_rejection_exact in H. congruence.
Qed.

Theorem valid_siblings_are_retained : forall Payload (request : Request Payload) requests,
  In request (admitted_requests requests) <->
  In request requests /\ request_rejected request = false.
Proof.
  intros. unfold admitted_requests. rewrite filter_In, Bool.negb_true_iff. reflexivity.
Qed.

Theorem rejection_is_idempotent : forall Payload (requests : list (Request Payload)),
  admitted_requests (admitted_requests requests) = admitted_requests requests.
Proof.
  intros Payload requests. induction requests as [|request tail IH]; [reflexivity|].
  unfold admitted_requests in *. cbn.
  destruct (request_rejected request) eqn:Hreject; cbn; [exact IH|].
  rewrite Hreject. cbn. now rewrite IH.
Qed.

Theorem typed_reference_preserves_election_observation :
  forall Payload Forest Observation (construct : list (Request Payload) -> Forest)
    (elect : Forest -> Observation) requests kept,
  reference_trace requests kept ->
  elect (construct (admitted_requests requests)) = elect (construct kept).
Proof. intros. apply ordered_typed_reference in H. now subst kept. Qed.

Section DynamicDriver.
Context {Payload State Fault : Type}.
Variable next : State -> option (Request Payload * State).
Variable original : Request Payload -> State -> Fault + State.

Fixpoint drive fuel state : list (Request Payload) * (Fault + State) :=
  match fuel with
  | 0 => ([], inr state)
  | S rest =>
      match next state with
      | None => ([], inr state)
      | Some (request, ready) =>
          if request_rejected request then drive rest ready
          else match original request ready with
               | inl fault => ([request], inl fault)
               | inr after =>
                   let '(trace, result) := drive rest after in
                   (request :: trace, result)
               end
      end
  end.

Inductive reference_drive : nat -> State -> list (Request Payload) -> Fault + State -> Prop :=
| DriveZero : forall state, reference_drive 0 state [] (inr state)
| DriveDone : forall fuel state,
    next state = None -> reference_drive (S fuel) state [] (inr state)
| DriveReject : forall fuel state request ready trace result,
    next state = Some (request, ready) -> request_mismatch request ->
    reference_drive fuel ready trace result ->
    reference_drive (S fuel) state trace result
| DriveFault : forall fuel state request ready fault,
    next state = Some (request, ready) -> ~ request_mismatch request ->
    original request ready = inl fault ->
    reference_drive (S fuel) state [request] (inl fault)
| DriveKeep : forall fuel state request ready after trace result,
    next state = Some (request, ready) -> ~ request_mismatch request ->
    original request ready = inr after ->
    reference_drive fuel after trace result ->
    reference_drive (S fuel) state (request :: trace) result.

Theorem dynamic_driver_is_a_typed_reference_run : forall fuel state,
  let '(trace, result) := drive fuel state in reference_drive fuel state trace result.
Proof.
  induction fuel as [|fuel IH]; intros state; [constructor|]. cbn [drive].
  destruct (next state) as [[request ready]|] eqn:Hnext.
  - destruct (request_rejected request) eqn:Hreject.
    + specialize (IH ready). destruct (drive fuel ready) as [trace result].
      eapply DriveReject; [exact Hnext| |exact IH]. now apply request_rejection_exact.
    + assert (Hkeep : ~ request_mismatch request).
      { intro H. apply request_rejection_exact in H. congruence. }
      destruct (original request ready) as [fault|after] eqn:Horiginal.
      * eapply DriveFault; eassumption.
      * specialize (IH after). destruct (drive fuel after) as [trace result].
        eapply DriveKeep; eassumption.
  - now apply DriveDone.
Qed.

Theorem dynamic_typed_reference_determines_exact_trace_and_state :
  forall fuel state trace result,
  reference_drive fuel state trace result -> drive fuel state = (trace, result).
Proof.
  intros fuel state trace result Hrun. induction Hrun; cbn [drive].
  - reflexivity.
  - now rewrite H.
  - rewrite H. apply request_rejection_exact in H0. now rewrite H0.
  - rewrite H. destruct (request_rejected request) eqn:Hreject.
    + exfalso. apply H0. now apply request_rejection_exact.
    + now rewrite H1.
  - rewrite H. destruct (request_rejected request) eqn:Hreject.
    + exfalso. apply H0. now apply request_rejection_exact.
    + now rewrite H1, IHHrun.
Qed.

Theorem dynamic_typed_reference_preserves_election :
  forall Observation (elect : State -> Observation) fuel state trace final,
  reference_drive fuel state trace (inr final) ->
  (match snd (drive fuel state) with
   | inl _ => None
   | inr observed => Some (elect observed)
   end) = Some (elect final).
Proof.
  intros Observation elect fuel state trace final Hrun.
  now rewrite (dynamic_typed_reference_determines_exact_trace_and_state Hrun).
Qed.
End DynamicDriver.

Section ReusedReplay.
Context {Edge Pop : Type}.
Variable edge_eq_dec : forall x y : Edge, {x = y} + {x <> y}.
Variable pop_eq_dec : forall x y : Pop, {x = y} + {x <> y}.

Inductive Submission :=
| IncomingEdge (edge : Edge)
| CompletedRequest (request : Request Pop).

Definition operations submission : list (GssOp Edge Pop) :=
  match submission with
  | IncomingEdge edge => [OpEdge Edge Pop edge]
  | CompletedRequest request =>
      if request_rejected request then [] else [OpPop Edge Pop (request_payload request)]
  end.

Definition admitted_operations submissions := flat_map operations submissions.
Definition replay submissions :=
  gss_run Edge Pop edge_eq_dec pop_eq_dec (admitted_operations submissions).

Theorem rejected_request_has_no_pop : forall request,
  request_rejected request = true -> operations (CompletedRequest request) = [].
Proof. intros. cbn. now rewrite H. Qed.

Theorem retained_request_has_exact_pop : forall request,
  request_rejected request = false ->
  operations (CompletedRequest request) = [OpPop Edge Pop (request_payload request)].
Proof. intros. cbn. now rewrite H. Qed.

Lemma edge_operation_in_iff : forall submissions edge,
  In (OpEdge Edge Pop edge) (admitted_operations submissions) <->
  In (IncomingEdge edge) submissions.
Proof.
  intros submissions edge. unfold admitted_operations. rewrite in_flat_map. split.
  - intros [submission [Hin Hop]]. destruct submission as [other|request].
    + cbn in Hop. destruct Hop as [Heq|[]]. inversion Heq. now subst.
    + cbn in Hop. destruct (request_rejected request); cbn in Hop.
      * contradiction.
      * destruct Hop as [Heq|[]]. discriminate.
  - intros Hin. exists (IncomingEdge edge). split; [exact Hin|]. cbn. auto.
Qed.

Lemma pop_operation_in_iff : forall submissions pop,
  In (OpPop Edge Pop pop) (admitted_operations submissions) <->
  exists request, In (CompletedRequest request) submissions /\
    request_rejected request = false /\ request_payload request = pop.
Proof.
  intros submissions pop. unfold admitted_operations. rewrite in_flat_map. split.
  - intros [submission [Hin Hop]]. destruct submission as [edge|request].
    + cbn in Hop. destruct Hop as [Heq|[]]. discriminate.
    + cbn in Hop. destruct (request_rejected request) eqn:Hreject; [contradiction|].
      cbn in Hop. destruct Hop as [Heq|[]]. inversion Heq.
      exists request. auto.
  - intros [request [Hin [Hreject Hpop]]]. exists (CompletedRequest request).
    split; [exact Hin|]. cbn. rewrite Hreject, Hpop. cbn. auto.
Qed.

Theorem typed_replay_is_exact_edge_pop_product : forall submissions edge pop,
  In (edge, pop) (gss_resumes Edge Pop (replay submissions)) <->
  In (IncomingEdge edge) submissions /\
  exists request, In (CompletedRequest request) submissions /\
    request_rejected request = false /\ request_payload request = pop.
Proof.
  intros. unfold replay. rewrite gss_replay_completeness.
  unfold gss_run.
  rewrite gss_run_edges_in_iff_general, gss_run_pops_in_iff_general.
  cbn [gss_empty gss_edges gss_pops In].
  rewrite edge_operation_in_iff, pop_operation_in_iff. tauto.
Qed.

Theorem typed_replay_resumes_each_pair_once : forall submissions,
  NoDup (gss_resumes Edge Pop (replay submissions)).
Proof. intros. apply gss_resumes_exactly_once. Qed.

Theorem typed_replay_is_order_independent : forall left right,
  (forall submission, In submission left <-> In submission right) ->
  forall edge pop,
  In (edge, pop) (gss_resumes Edge Pop (replay left)) <->
  In (edge, pop) (gss_resumes Edge Pop (replay right)).
Proof.
  intros left right Hsame edge pop.
  rewrite !typed_replay_is_exact_edge_pop_product.
  rewrite Hsame. split; intros [Hedge [request [Hin Hrest]]];
    split; [exact Hedge| |exact Hedge|]; exists request; split;
    try exact Hrest; now apply Hsame.
Qed.
End ReusedReplay.

End TypedUnaryPublication.

Print Assumptions TypedUnaryPublication.reject_exact_certificate.
Print Assumptions TypedUnaryPublication.category_renaming_preserves_rejection.
Print Assumptions TypedUnaryPublication.certified_mismatch_rejects_every_typed_value.
Print Assumptions TypedUnaryPublication.rejection_preserves_typed_successes.
Print Assumptions TypedUnaryPublication.publication_matches_typed_reference.
Print Assumptions TypedUnaryPublication.ordered_typed_reference.
Print Assumptions TypedUnaryPublication.typed_reference_preserves_election_observation.
Print Assumptions TypedUnaryPublication.dynamic_typed_reference_determines_exact_trace_and_state.
Print Assumptions TypedUnaryPublication.dynamic_typed_reference_preserves_election.
Print Assumptions TypedUnaryPublication.typed_replay_is_exact_edge_pop_product.
Print Assumptions TypedUnaryPublication.typed_replay_resumes_each_pair_once.
Print Assumptions TypedUnaryPublication.typed_replay_is_order_independent.
