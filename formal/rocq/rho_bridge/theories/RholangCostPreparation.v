(** * Structural cost preparation and the separate native offer boundary

    This is a specification of preparation evidence, not another normalizer or
    interpreter. Signature conversion, stack ownership, and signed placement
    are imported from [RholangCostSurface]. Resolved principal, binder, guard,
    channel, and payload identities below are opaque; they are never funding.

    Source evidence is the parser's transparent [signed_cont] case, the native
    [uniform_sign]/[lollipop] adapters, and [descend_p_input]: signing replaces
    the final continuation before semicolon rows become nested receives, and
    complex sources are expanded only after that nesting. Requests in a later
    row must therefore remain beneath the preceding receive.

    This model does not prove parsing, capture avoidance, canonical binder or
    Par encoding, complete language identity, resource charging, or Rust's
    iterative implementation. Exact octet strings model the comparison
    boundary. Replacing them with digests requires a separately justified
    cryptographic refinement, not a global hash-injectivity axiom. The host
    must supply the complete language identity, not a grammar-only digest.

    ProgramFrontend::prepare has no authenticated envelope or phlo controls.
    Its receipt therefore carries neither. The final section consumes an
    abstract offer already checked by the existing native offered-funded
    boundary, and preserves its exact envelope controls. Live authority,
    signature verification, policy validity, ledger reservation, execution,
    and atomic commit remain native obligations, not consequences of parsing.
*)

From Stdlib Require Import List Arith Bool ZArith Ascii.
From RhoBridge Require Import RholangCostSurface.
Import ListNotations.
Module Surface := RholangCostSurface.RholangCostSurface.

Module RholangCostPreparation.

Inductive Continuation : Type :=
| PlainContinuation (body : Surface.Process)
| SignedContinuationMarker (body : Surface.Process).

Definition erase_continuation (continuation : Continuation) : Surface.Process :=
  match continuation with
  | PlainContinuation body | SignedContinuationMarker body => body
  end.

Theorem signed_continuation_marker_is_transparent : forall body,
  erase_continuation (SignedContinuationMarker body) =
  erase_continuation (PlainContinuation body).
Proof. reflexivity. Qed.

(** A query return binder has already been freshly resolved by the adapter.
    Freshness and scope correspondence are refinement obligations; the model
    proves that preparation preserves that exact identity, not its spelling.
    Only request/return query sugar is modeled here, not acknowledgement sugar. *)
Inductive ClauseSource : Type :=
| PlainChannel (channel : nat)
| RequestReturn (channel : nat) (arguments : list nat) (return_binder : nat).

Record Clause : Type := {
  clause_binders : list nat;
  clause_signature : option Surface.Signature;
  clause_source : ClauseSource
}.

Record Row : Type := {
  row_identity : nat;
  row_clauses : list Clause;
  row_guard : option nat
}.

Record PreparedClause : Type := {
  prepared_binders : list nat;
  prepared_signature : option Surface.Signature;
  prepared_channel : nat
}.

Record PreparedRow : Type := {
  prepared_row_identity : nat;
  prepared_clauses : list PreparedClause;
  prepared_guard : option nat
}.

Record QueryRequest : Type := {
  request_channel : nat;
  request_arguments : list nat;
  request_return_binder : nat
}.

Definition prepare_clause (clause : Clause) : PreparedClause :=
  {| prepared_binders := clause_binders clause;
     prepared_signature := clause_signature clause;
     prepared_channel :=
       match clause_source clause with
       | PlainChannel channel => channel
       | RequestReturn _ _ return_binder => return_binder
       end |}.

Definition clause_requests (clause : Clause) : list QueryRequest :=
  match clause_source clause with
  | PlainChannel _ => []
  | RequestReturn channel arguments return_binder =>
      [{| request_channel := channel;
          request_arguments := arguments;
          request_return_binder := return_binder |}]
  end.

Definition row_requests (row : Row) : list QueryRequest :=
  flat_map clause_requests (row_clauses row).

Definition prepare_row (row : Row) : PreparedRow :=
  {| prepared_row_identity := row_identity row;
     prepared_clauses := map prepare_clause (row_clauses row);
     prepared_guard := row_guard row |}.

Theorem preparation_preserves_per_clause_binders_and_signatures : forall clauses,
  map (fun clause => (prepared_binders clause, prepared_signature clause))
      (map prepare_clause clauses) =
  map (fun clause => (clause_binders clause, clause_signature clause)) clauses.
Proof.
  induction clauses as [|clause clauses IH]; cbn; [reflexivity | now rewrite IH].
Qed.

Theorem preparation_preserves_row_identity_and_guard : forall row,
  prepared_row_identity (prepare_row row) = row_identity row /\
  prepared_guard (prepare_row row) = row_guard row.
Proof. intros; split; reflexivity. Qed.

Theorem query_requests_preserve_authored_order : forall first second,
  flat_map clause_requests (first ++ second) =
  flat_map clause_requests first ++ flat_map clause_requests second.
Proof. intros; apply flat_map_app. Qed.

Theorem query_rewrite_preserves_return_identity_and_payload :
  forall binders sig channel arguments return_binder,
  let clause := {| clause_binders := binders; clause_signature := sig;
                  clause_source := RequestReturn channel arguments return_binder |} in
  prepared_channel (prepare_clause clause) = return_binder /\
  clause_requests clause =
    [{| request_channel := channel; request_arguments := arguments;
        request_return_binder := return_binder |}].
Proof. intros; split; reflexivity. Qed.

(** [ScopeRequests] binds each request's return identity locally and emits that
    request with the return name prepended to its original arguments. It is a
    structural description, not a request executor. [Await] records exactly
    one source row, including its individual signatures and optional guard. *)
Inductive StagedReceive : Type :=
| Finish (body : Surface.Process)
| Await (row : PreparedRow) (continuation : StagedReceive)
| ScopeRequests (requests : list QueryRequest) (body : StagedReceive)
| Annotate (sig : Surface.Signature) (body : StagedReceive).

Definition scope_requests (requests : list QueryRequest) (body : StagedReceive)
    : StagedReceive :=
  match requests with
  | [] => body
  | _ => ScopeRequests requests body
  end.

Fixpoint stage_rows (rows : list Row) (body : Surface.Process) : StagedReceive :=
  match rows with
  | [] => Finish body
  | row :: rest =>
      scope_requests (row_requests row)
        (Await (prepare_row row) (stage_rows rest body))
  end.

Fixpoint entry_requests (term : StagedReceive) : list QueryRequest :=
  match term with
  | Finish _ | Await _ _ => []
  | ScopeRequests requests inner => requests ++ entry_requests inner
  | Annotate _ inner => entry_requests inner
  end.

Fixpoint staged_rows (term : StagedReceive) : list PreparedRow :=
  match term with
  | Finish _ => []
  | Await row inner => row :: staged_rows inner
  | ScopeRequests _ inner | Annotate _ inner => staged_rows inner
  end.

Fixpoint staged_receive_count (term : StagedReceive) : nat :=
  match term with
  | Finish body => Surface.receive_count body
  | Await _ inner => S (staged_receive_count inner)
  | ScopeRequests _ inner | Annotate _ inner => staged_receive_count inner
  end.

Theorem later_queries_stay_beneath_the_previous_receive : forall row rest body,
  entry_requests (stage_rows (row :: rest) body) = row_requests row.
Proof.
  intros row rest body. cbn [stage_rows].
  unfold scope_requests. destruct (row_requests row); cbn; now rewrite ?app_nil_r.
Qed.

Theorem staged_rows_preserve_order_and_all_clause_metadata : forall rows body,
  staged_rows (stage_rows rows body) = map prepare_row rows.
Proof.
  induction rows as [|row rows IH]; intros body; cbn [stage_rows]; [reflexivity |].
  unfold scope_requests. destruct (row_requests row); cbn; now rewrite IH.
Qed.

Theorem staging_adds_exactly_one_receive_per_source_row : forall rows body,
  staged_receive_count (stage_rows rows body) =
  length rows + Surface.receive_count body.
Proof.
  induction rows as [|row rows IH]; intros body; cbn [stage_rows]; [reflexivity |].
  unfold scope_requests. destruct (row_requests row); cbn; now rewrite IH.
Qed.

(** The imported rewrite chooses rendezvous and FINAL continuation placement.
    Only then does row staging nest receives. This is not a uniform signature
    added independently to every intermediate semicolon-row continuation. *)
Definition receive_placement (row_id : nat) (sig : option Surface.Signature)
    (continuation : Continuation)
    : option (option Surface.Signature * Surface.Process) :=
  match sig with
  | None => Some (None, erase_continuation continuation)
  | Some signature =>
      match Surface.rewrite_signed signature
          (Surface.Receive row_id (erase_continuation continuation)) with
      | Some (Surface.Signed outer (Surface.Receive _ body)) =>
          Some (Some outer, body)
      | _ => None
      end
  end.

Record ReceiveSource : Type := {
  source_rows : list Row;
  source_annotation : option Surface.Signature;
  source_continuation : Continuation
}.

Definition elaborate_receive (source : ReceiveSource) : option StagedReceive :=
  match source_rows source with
  | [] => None
  | row :: rest =>
      match receive_placement (row_identity row) (source_annotation source)
          (source_continuation source) with
      | None => None
      | Some (outer, body) =>
          let staged := stage_rows (row :: rest) body in
          Some (match outer with
                | None => staged
                | Some sig => Annotate sig staged
                end)
      end
  end.

Theorem marker_erasure_preserves_the_entire_staged_result : forall rows sig body,
  elaborate_receive {| source_rows := rows; source_annotation := sig;
                       source_continuation := SignedContinuationMarker body |} =
  elaborate_receive {| source_rows := rows; source_annotation := sig;
                       source_continuation := PlainContinuation body |}.
Proof. intros; destruct rows; reflexivity. Qed.

Theorem lollipop_signs_only_outer_and_final_continuation :
  forall row rest source target continuation,
  elaborate_receive
    {| source_rows := row :: rest;
       source_annotation := Some (Surface.Transfer source target);
       source_continuation := continuation |} =
  Some (Annotate source
    (stage_rows (row :: rest)
      (Surface.Signed target (erase_continuation continuation)))).
Proof. reflexivity. Qed.

Theorem uniform_signing_retains_an_explicit_final_signature :
  forall row rest sig wire explicit body,
  Surface.direct_signature sig = Some wire ->
  elaborate_receive
    {| source_rows := row :: rest; source_annotation := Some sig;
       source_continuation := SignedContinuationMarker (Surface.Signed explicit body) |} =
  Some (Annotate sig (stage_rows (row :: rest) (Surface.Signed explicit body))).
Proof.
  intros row rest sig wire explicit body Hfundable.
  destruct sig; try reflexivity; discriminate Hfundable.
Qed.

Theorem uniform_signing_places_authority_on_the_final_unsigned_body :
  forall row rest sig wire payload,
  Surface.direct_signature sig = Some wire ->
  elaborate_receive
    {| source_rows := row :: rest; source_annotation := Some sig;
       source_continuation := SignedContinuationMarker (Surface.Atom payload) |} =
  Some (Annotate sig
    (stage_rows (row :: rest) (Surface.Signed sig (Surface.Atom payload)))).
Proof.
  intros row rest sig wire payload Hfundable.
  destruct sig; try reflexivity; discriminate Hfundable.
Qed.

(** Structural receipts bind exact source, complete language identity, and
    output octets. The parser and encoder are parameters with NO correctness
    axioms: theorems below establish receipt binding and source derivation,
    not that those parameter implementations correspond to Rust or Par. *)
Definition Octets := list ascii.

Definition octets_equal (left right : Octets) : bool :=
  if list_eq_dec ascii_dec left right then true else false.

Lemma octets_equal_true : forall left right,
  octets_equal left right = true <-> left = right.
Proof.
  intros left right. unfold octets_equal.
  destruct (list_eq_dec ascii_dec left right); split; congruence.
Qed.

Record PreparationReceipt : Type := {
  receipt_source : Octets;
  receipt_language : Octets;
  receipt_output : Octets
}.

Record Prepared : Type := {
  prepared_source : Octets;
  prepared_language : Octets;
  prepared_output : StagedReceive
}.

Definition receipt_matches (source language output : Octets)
    (receipt : PreparationReceipt) : bool :=
  (octets_equal source (receipt_source receipt) &&
   octets_equal language (receipt_language receipt)) &&
  octets_equal output (receipt_output receipt).

Theorem receipt_acceptance_binds_all_three_identities :
  forall source language output receipt,
  receipt_matches source language output receipt = true ->
  source = receipt_source receipt /\
  language = receipt_language receipt /\
  output = receipt_output receipt.
Proof.
  intros source language output receipt H.
  unfold receipt_matches in H.
  repeat rewrite andb_true_iff in H.
  destruct H as [[Hsource Hlanguage] Houtput].
  repeat split; apply octets_equal_true; assumption.
Qed.

Theorem changed_identity_refuses_the_receipt : forall source language output receipt,
  (source <> receipt_source receipt \/
   language <> receipt_language receipt \/
   output <> receipt_output receipt) ->
  receipt_matches source language output receipt = false.
Proof.
  intros source language output receipt Hchanged.
  destruct (receipt_matches source language output receipt) eqn:Hcheck; [|reflexivity].
  apply receipt_acceptance_binds_all_three_identities in Hcheck.
  destruct Hcheck as [Hsource [Hlanguage Houtput]].
  destruct Hchanged as [Hchanged | [Hchanged | Hchanged]]; contradiction.
Qed.

Section StructuralPreparation.
  Variable parse_source : Octets -> option ReceiveSource.
  Variable encode_output : StagedReceive -> Octets.

  Definition prepare (source language : Octets) (receipt : PreparationReceipt)
      : option Prepared :=
    match parse_source source with
    | None => None
    | Some parsed =>
        match elaborate_receive parsed with
        | None => None
        | Some output =>
            if receipt_matches source language (encode_output output) receipt then
              Some {| prepared_source := source; prepared_language := language;
                      prepared_output := output |}
            else None
        end
    end.

  Theorem preparation_derives_output_and_checks_its_exact_binding :
    forall source language receipt prepared,
    prepare source language receipt = Some prepared ->
    exists parsed,
      parse_source source = Some parsed /\
      elaborate_receive parsed = Some (prepared_output prepared) /\
      prepared_source prepared = source /\
      prepared_language prepared = language /\
      source = receipt_source receipt /\
      language = receipt_language receipt /\
      encode_output (prepared_output prepared) = receipt_output receipt.
  Proof.
    intros source language receipt prepared H.
    unfold prepare in H.
    destruct (parse_source source) as [parsed|] eqn:Hparse; try discriminate.
    destruct (elaborate_receive parsed) as [output|] eqn:Helaborate; try discriminate.
    destruct (receipt_matches source language (encode_output output) receipt)
      eqn:Hreceipt; try discriminate.
    inversion H; subst; clear H.
    apply receipt_acceptance_binds_all_three_identities in Hreceipt.
    destruct Hreceipt as [Hsource [Hlanguage Houtput]].
    exists parsed. cbn. repeat split; assumption || reflexivity.
  Qed.

  (** Publication is the only frontend state change modeled here. The opaque
      funded ledger is neither a receipt field nor a result of preparation. *)
  Context {Authority : Type}.

  Record FrontendState : Type := {
    published : list Prepared;
    funded_ledger : list Authority
  }.

  Definition publish_preparation (result : option Prepared) (state : FrontendState)
      : FrontendState :=
    match result with
    | None => state
    | Some prepared =>
        {| published := prepared :: published state;
           funded_ledger := funded_ledger state |}
    end.

  Theorem failed_preparation_publishes_nothing : forall source language receipt state,
    prepare source language receipt = None ->
    publish_preparation (prepare source language receipt) state = state.
  Proof. intros source language receipt state H; now rewrite H. Qed.

  Theorem frontend_never_changes_funded_authority : forall result state,
    funded_ledger (publish_preparation result state) = funded_ledger state.
  Proof. intros result state; destruct result; reflexivity. Qed.
End StructuralPreparation.

(** Native binding happens AFTER structural preparation. The abstract type has
    no constructor available to the frontend. Its values must come from the
    existing check_offered_phlo_controls boundary, including signed scalar,
    funding limit, and adopted-price checks. No validity property of that
    external check is assumed or proved by this structural model. *)
Record PhloControls : Type := {
  phlo_price : Z;
  phlo_limit : Z
}.

Definition controls_equal (left right : PhloControls) : bool :=
  Z.eqb (phlo_price left) (phlo_price right) &&
  Z.eqb (phlo_limit left) (phlo_limit right).

Lemma controls_equal_true : forall left right,
  controls_equal left right = true <-> left = right.
Proof.
  intros [left_price left_limit] [right_price right_limit].
  unfold controls_equal; cbn.
  rewrite andb_true_iff, !Z.eqb_eq. split.
  - intros [Hprice Hlimit]; subst; reflexivity.
  - intros H; inversion H; split; reflexivity.
Qed.

Section NativeOfferBinding.
  Context {CheckedOffer : Type}.
  Variable checked_controls : CheckedOffer -> PhloControls.

  Record NativeBinding : Type := {
    bound_preparation : Prepared;
    bound_offer : CheckedOffer;
    bound_controls : PhloControls
  }.

  Definition bind_native_offer (prepared : Prepared) (source language : Octets)
      (envelope_controls : PhloControls) (checked_offer : option CheckedOffer)
      : option NativeBinding :=
    match checked_offer with
    | None => None
    | Some offer =>
        if (octets_equal source (prepared_source prepared) &&
            octets_equal language (prepared_language prepared)) &&
           controls_equal envelope_controls (checked_controls offer) then
          Some {| bound_preparation := prepared; bound_offer := offer;
                  bound_controls := envelope_controls |}
        else None
    end.

  Theorem native_binding_preserves_the_exact_signed_controls :
    forall prepared source language controls offer binding,
    bind_native_offer prepared source language controls (Some offer) = Some binding ->
    source = prepared_source prepared /\
    language = prepared_language prepared /\
    controls = checked_controls offer /\
    bound_controls binding = controls /\
    bound_preparation binding = prepared /\
    bound_offer binding = offer.
  Proof.
    intros prepared source language controls offer binding H.
    unfold bind_native_offer in H.
    destruct ((octets_equal source (prepared_source prepared) &&
               octets_equal language (prepared_language prepared)) &&
              controls_equal controls (checked_controls offer)) eqn:Hcheck;
      try discriminate.
    inversion H; subst; clear H.
    repeat rewrite andb_true_iff in Hcheck.
    destruct Hcheck as [[Hsource Hlanguage] Hcontrols].
    apply octets_equal_true in Hsource.
    apply octets_equal_true in Hlanguage.
    apply controls_equal_true in Hcontrols.
    cbn. repeat split; assumption || reflexivity.
  Qed.

  Theorem missing_checked_offer_refuses_native_binding :
    forall prepared source language controls,
    bind_native_offer prepared source language controls None = None.
  Proof. reflexivity. Qed.

  Theorem changed_signed_controls_refuse_native_binding :
    forall prepared source language controls offer,
    controls <> checked_controls offer ->
    bind_native_offer prepared source language controls (Some offer) = None.
  Proof.
    intros prepared source language controls offer Hdifferent.
    destruct (bind_native_offer prepared source language controls (Some offer))
      as [binding|] eqn:Hbinding; [|reflexivity].
    apply native_binding_preserves_the_exact_signed_controls in Hbinding.
    destruct Hbinding as [_ [_ [Hcontrols _]]]. contradiction.
  Qed.
End NativeOfferBinding.

Print Assumptions staged_rows_preserve_order_and_all_clause_metadata.
Print Assumptions later_queries_stay_beneath_the_previous_receive.
Print Assumptions lollipop_signs_only_outer_and_final_continuation.
Print Assumptions preparation_derives_output_and_checks_its_exact_binding.
Print Assumptions frontend_never_changes_funded_authority.
Print Assumptions native_binding_preserves_the_exact_signed_controls.

End RholangCostPreparation.
