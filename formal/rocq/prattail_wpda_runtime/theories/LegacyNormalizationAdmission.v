(** Admission at the ORIGINAL legacy-normalization sites, not another normalizer.

    Rust target: ast/src/legacy_rule_normalization.rs. The existing infallible
    normalize_legacy_rule_with becomes the no-admission wrapper of the SAME
    two loops in try_normalize_legacy_rule_with. The borrowed reader and original
    constructor trait remain unchanged. Result None is original semantic refusal;
    admission, checked-counter, and reservation failures are separate errors.

    LegacyRuleNormalizationProjection supplies the concrete original and shared
    executions. Instrumentation below consumes their finite mathematical traces;
    it is NOT a runtime trace allocation, preflight walk, or delayed constructor
    pass. Each block describes one original source site. Pending-binder copies,
    absent from the older callback trace, are tied to the actual item observed
    at InspectBuild. The runtime reuses that already borrowed item; it does not
    read it again to produce the admission event.

    Admission precedes argument clones, string copies and vector reservation;
    reservation precedes the constructor and push. Fresh-name admission precedes
    formatting; the checked next increment precedes the constructor on this new
    fallible path. Successful bounded runs retain original callback order. No
    equivalence to the original overflow behavior is claimed. Original binder
    cloning occurs even when a later binder overwrites it, and collection names
    and separators remain paid at every occurrence.

    The caller supplies logical charges and actual shallow constructor costs.
    Constructors are total on admitted inputs, private, and do not publish
    external effects. Name/kind clones and adapter-internal allocations are not
    magically bounded by counting vector slots. Allocation success is an
    independent premise; finite reservation outcomes below are observations,
    not an allocator implementation or a physical RSS bound. This model does
    not implement owned-node materialization, generated-name equality policy,
    half-delimiter admission, or a fallible synthesis driver.
*)
From Stdlib Require Import List String Bool Arith Lia.
From PrattailWpdaRuntime Require Import LegacyRuleNormalizationProjection
  ReconstructionWorkBudget ContextItemsAdmission.
Import ListNotations.
Open Scope list_scope.
Set Implicit Arguments.

Module LegacyNormalizationAdmission.
Module L := LegacyRuleNormalizationProjection.LegacyRuleNormalizationProjection.

Inductive Site :=
| PreflightItem (index : nat) | BuildItem (index : nat)
| FreshName (index : nat) | ElemsName
| PendingBinder (category : L.OriginalIdent)
| Simple (name : L.Name) (category : L.OriginalIdent)
| Abstraction (binder body : L.Name) (domain codomain : L.OriginalIdent)
| Collection (name : L.Name) (kind : L.S.CollectionKind) (element : L.OriginalIdent)
| Literal (text : string) | Param (name : L.Name)
| Sep (name : L.Name) (separator : string).

Inductive BufferKind := ContextBuffer | SyntaxBuffer.
Inductive Effect :=
| OriginalCallback (operation : L.Operation)
| CloneOriginal (name : L.OriginalIdent)
| CloneGenerated (name : L.Name)
| CloneKind (kind : L.S.CollectionKind)
| CopyString (text : string).

Record Block := {
  request : option Site;
  reserve : option BufferKind;
  increment : option nat;
  effects : list Effect
}.
Definition block site target next actions :=
  {| request := site; reserve := target; increment := next; effects := actions |}.
Definition observation op := block None None None [OriginalCallback op].
Definition visit site op := block (Some site) None None [OriginalCallback op].
Definition pending_copy category :=
  block (Some (PendingBinder category)) None None [CloneOriginal category].

(** Fixed original field/clone mapping. Domain of an abstraction is moved from
    pending_binder, not cloned again. Its codomain and both generated arguments
    are cloned at make_abstraction. Collection names/kind/element are cloned at
    make_collection. Param and Sep consume their generated name by move. *)
Definition instrument_operation (source : nat -> L.SourceItem) op : list Block :=
  match op with
  | L.InspectPreflight index => [visit (PreflightItem index) op]
  | L.InspectBuild index =>
      visit (BuildItem index) op ::
      match source index with L.SBinder category => [pending_copy category] | _ => [] end
  | L.Fresh index =>
      [block (Some (FreshName index)) None (Some index) [OriginalCallback op]]
  | L.FixedElems => [block (Some ElemsName) None None [OriginalCallback op]]
  | L.ConstructSimple name category =>
      [block (Some (Simple name category)) (Some ContextBuffer) None
        [CloneGenerated name; CloneOriginal category; OriginalCallback op]]
  | L.ConstructAbstraction binder body domain codomain =>
      [block (Some (Abstraction binder body domain codomain)) (Some ContextBuffer) None
        [CloneGenerated binder; CloneGenerated body; CloneOriginal codomain; OriginalCallback op]]
  | L.ConstructCollection name kind element =>
      [block (Some (Collection name kind element)) (Some ContextBuffer) None
        [CloneGenerated name; CloneKind kind; CloneOriginal element; OriginalCallback op]]
  | L.ConstructLiteral text =>
      [block (Some (Literal text)) (Some SyntaxBuffer) None
        [CopyString text; OriginalCallback op]]
  | L.ConstructParam name =>
      [block (Some (Param name)) (Some SyntaxBuffer) None [OriginalCallback op]]
  | L.ConstructSep name separator =>
      [block (Some (Sep name separator)) (Some SyntaxBuffer) None
        [CopyString separator; OriginalCallback op]]
  | _ => [observation op]
  end.
Definition instrument source trace := flat_map (instrument_operation source) trace.
Definition original_effect effect :=
  match effect with OriginalCallback op => [op] | _ => [] end.
Definition erase blocks := flat_map (fun b => flat_map original_effect (effects b)) blocks.

Lemma one_original_site_erases_exactly : forall source op,
  erase (instrument_operation source op) = [op].
Proof.
  intros source op; destruct op; cbn [instrument_operation erase observation visit block
    pending_copy original_effect]; try reflexivity.
  destruct (source handle); reflexivity.
Qed.
Lemma erase_app : forall first second,
  erase (first ++ second) = erase first ++ erase second.
Proof. intros; unfold erase; apply flat_map_app. Qed.
Theorem instrumentation_preserves_exact_original_callbacks : forall source trace,
  erase (instrument source trace) = trace.
Proof.
  intros source trace; induction trace as [|op rest IH]; [reflexivity|].
  change (erase (instrument_operation source op ++ instrument source rest) = op :: rest).
  rewrite erase_app, one_original_site_erases_exactly, IH; reflexivity.
Qed.
Theorem binder_copy_is_tied_to_actual_original_build : forall source index category b,
  source index = L.SBinder category ->
  L.source_step (source index) (L.inspect_build index b) =
    L.Continue (L.buffer (L.params b) (L.syntax b) (L.next_param b) (Some category)
      (L.operations b ++ [L.InspectBuild index])) /\
  instrument_operation source (L.InspectBuild index) =
    [visit (BuildItem index) (L.InspectBuild index); pending_copy category].
Proof.
  intros; split.
  - rewrite H; reflexivity.
  - unfold instrument_operation; rewrite H; reflexivity.
Qed.
Theorem nonbinder_build_does_not_invent_pending_copy : forall source index,
  (forall category, source index <> L.SBinder category) ->
  instrument_operation source (L.InspectBuild index) =
    [visit (BuildItem index) (L.InspectBuild index)].
Proof.
  intros source index H; unfold instrument_operation.
  destruct (source index) eqn:E; try reflexivity.
  exfalso; eapply H; reflexivity.
Qed.

Definition source_schedule source rule := instrument source (L.trace (L.source_normalize source rule)).
Definition shared_schedule source rule := instrument source
  (L.trace (L.shared_normalize (fun id => L.project_item (source id)) L.original_constructors rule)).
Theorem original_and_shared_have_identical_paid_sites : forall source rule,
  shared_schedule source rule = source_schedule source rule.
Proof. intros; unfold shared_schedule, source_schedule; now rewrite L.original_normalization_relocated_exactly. Qed.
Theorem present_context_has_no_item_or_constructor_admission : forall source rule tc,
  L.term_context rule = Some tc ->
  shared_schedule source rule = [observation L.HasTermContext].
Proof.
  intros; unfold shared_schedule.
  rewrite (@L.term_context_presence_short_circuits_all_other_reads _ _ _ tc H); reflexivity.
Qed.
Theorem present_syntax_has_no_item_or_constructor_admission : forall source rule sp,
  L.term_context rule = None -> L.syntax_pattern rule = Some sp ->
  shared_schedule source rule = [observation L.HasTermContext; observation L.HasSyntaxPattern].
Proof.
  intros; unfold shared_schedule.
  rewrite (@L.syntax_presence_short_circuits_item_reads _ _ _ sp H H0); reflexivity.
Qed.
Theorem preflight_is_still_the_original_complete_scan : forall source handles,
  instrument source (snd (L.shared_preflight (fun id => L.project_item (source id)) handles)) =
  instrument source (snd (L.source_preflight source handles)).
Proof. intros; now rewrite L.preflight_preserves_refusal_and_read_order. Qed.

(** Admission policy is external. The scalar debit is the existing checked work
    budget law; a caller can precheck multiple actual units independently. *)
Definition charge (cost : Site -> nat) b :=
  match request b with Some site => cost site | None => 0 end.
Definition charges cost blocks := map (charge cost) blocks.
Definition counter_ok maximum b :=
  match increment b with None => true | Some index => Nat.ltb index maximum end.
Definition reservation_ok (available : BufferKind -> bool) b :=
  match reserve b with None => true | Some target => available target end.
Inductive Failure := AdmissionFailure | CounterOverflow | AllocationFailure.
Inductive Attempt := Allowed (remaining : nat) | Rejected (reason : Failure) (remaining : nat).
Definition attempt cost maximum available budget b :=
  match debit budget (charge cost b) with
  | None => Rejected AdmissionFailure budget
  | Some next => if counter_ok maximum b then
      if reservation_ok available b then Allowed next else Rejected AllocationFailure next
    else Rejected CounterOverflow next
  end.

(** Reservation outcomes are indexed by occurrence, allowing equal payloads to
    have distinct outcomes. Effects execute only on Allowed, after all checks.
    Rejected local buffers and charged counters remain private. *)
Inductive Run :=
| Completed (remaining : nat)
| Stopped (accepted : list Block) (next : Block) (suffix : list Block)
    (reason : Failure) (remaining : nat).
Fixpoint run cost maximum (available : nat -> BufferKind -> bool)
    position budget blocks :=
  match blocks with
  | [] => Completed budget
  | b :: rest => match attempt cost maximum (available position) budget b with
      | Rejected reason remaining => Stopped [] b rest reason remaining
      | Allowed remaining => match run cost maximum available (S position) remaining rest with
          | Completed final => Completed final
          | Stopped accepted next suffix reason final => Stopped (b :: accepted) next suffix reason final
          end
      end
  end.
Lemma allowed_attempt_uses_original_checked_debit : forall cost maximum available budget b remaining,
  attempt cost maximum available budget b = Allowed remaining ->
  debit budget (charge cost b) = Some remaining /\
  counter_ok maximum b = true /\ reservation_ok available b = true.
Proof.
  intros cost maximum available budget b remaining H; unfold attempt in H.
  destruct (debit budget (charge cost b)) as [next|] eqn:D; [|discriminate].
  destruct (counter_ok maximum b) eqn:C; [|discriminate].
  destruct (reservation_ok available b) eqn:R; [|discriminate].
  inversion H; subst; auto.
Qed.
Theorem complete_run_has_exact_prepaid_total : forall blocks cost maximum available position budget remaining,
  run cost maximum available position budget blocks = Completed remaining ->
  debit_all budget (charges cost blocks) = Some remaining.
Proof.
  induction blocks as [|b rest IH]; intros cost maximum available position budget remaining H.
  - cbn in H; inversion H; reflexivity.
  - cbn in H. destruct (attempt cost maximum (available position) budget b) eqn:A; [|discriminate].
    destruct (run cost maximum available (S position) remaining0 rest) eqn:R; try discriminate.
    inversion H; subst.
    apply allowed_attempt_uses_original_checked_debit in A; destruct A as [D _].
    change (match debit budget (charge cost b) with
      | Some next => debit_all next (charges cost rest) | None => None end = Some remaining).
    rewrite D. eapply IH; exact R.
Qed.
Theorem successful_budget_is_exact : forall blocks cost maximum available position budget remaining,
  run cost maximum available position budget blocks = Completed remaining ->
  remaining + total_charge (charges cost blocks) = budget.
Proof.
  intros; apply successful_sequence_has_exact_total_cost.
  eapply complete_run_has_exact_prepaid_total; exact H.
Qed.
Theorem first_refusal_exposes_only_executed_prefix :
  forall blocks cost maximum available position budget accepted next suffix reason remaining,
  run cost maximum available position budget blocks = Stopped accepted next suffix reason remaining ->
  blocks = accepted ++ next :: suffix.
Proof.
  induction blocks as [|b rest IH]; intros cost maximum available position budget accepted next suffix reason remaining H.
  - discriminate.
  - cbn in H; destruct (attempt cost maximum (available position) budget b) eqn:A.
    + destruct (run cost maximum available (S position) remaining0 rest) eqn:R; try discriminate.
      inversion H; subst. cbn. f_equal. eapply IH; exact R.
    + inversion H; reflexivity.
Qed.
Theorem denied_site_executes_no_local_effect_or_suffix : forall cost maximum available position budget b rest,
  debit budget (charge cost b) = None ->
  run cost maximum available position budget (b :: rest) =
    Stopped [] b rest AdmissionFailure budget.
Proof. intros; cbn [run]; unfold attempt; rewrite H; reflexivity. Qed.
Theorem failed_reservation_precedes_argument_copies_and_constructor :
  forall cost maximum available position budget b rest remaining,
  debit budget (charge cost b) = Some remaining ->
  counter_ok maximum b = true -> reservation_ok (available position) b = false ->
  run cost maximum available position budget (b :: rest) =
    Stopped [] b rest AllocationFailure remaining.
Proof. intros; cbn [run]; unfold attempt; rewrite H, H0, H1; reflexivity. Qed.
Theorem checked_increment_precedes_fresh_constructor_on_overflow :
  forall cost maximum available position budget index rest remaining,
  debit budget (cost (FreshName index)) = Some remaining -> maximum <= index ->
  run cost maximum available position budget
    (block (Some (FreshName index)) None (Some index) [OriginalCallback (L.Fresh index)] :: rest) =
  Stopped [] (block (Some (FreshName index)) None (Some index) [OriginalCallback (L.Fresh index)])
    rest CounterOverflow remaining.
Proof.
  intros.
  change (debit budget (charge cost
    (block (Some (FreshName index)) None (Some index) [OriginalCallback (L.Fresh index)]))
    = Some remaining) in H.
  cbn [run]; unfold attempt; rewrite H.
  cbn [counter_ok block increment].
  assert (E : Nat.ltb index maximum = false) by (apply Nat.ltb_ge; exact H0).
  rewrite E; reflexivity.
Qed.

Definition all_checks maximum available position blocks :=
  forall offset b, nth_error blocks offset = Some b ->
    counter_ok maximum b = true /\ reservation_ok (available (position + offset)) b = true.
Theorem sufficient_paid_domain_preserves_every_original_site :
  forall blocks cost maximum available position budget,
  all_checks maximum available position blocks ->
  total_charge (charges cost blocks) <= budget ->
  run cost maximum available position budget blocks =
    Completed (budget - total_charge (charges cost blocks)).
Proof.
  induction blocks as [|b rest IH]; intros cost maximum available position budget Checks Fits.
  - cbn; now rewrite Nat.sub_0_r.
  - pose proof (Checks 0 b eq_refl) as [Counter Reservation].
    rewrite Nat.add_0_r in Reservation.
    assert (Tail : all_checks maximum available (S position) rest).
    { intros offset node Found. specialize (Checks (S offset) node Found).
      replace (position + S offset) with (S position + offset) in Checks by lia; exact Checks. }
    change (charge cost b + total_charge (charges cost rest) <= budget) in Fits.
    change (run cost maximum available position budget (b :: rest) =
      Completed (budget - (charge cost b + total_charge (charges cost rest)))).
    assert (D : debit budget (charge cost b) = Some (budget - charge cost b)).
    { unfold debit; assert (E : Nat.leb (charge cost b) budget = true) by (apply Nat.leb_le; lia).
      rewrite E; reflexivity. }
    cbn [run]; unfold attempt at 1; rewrite D, Counter, Reservation.
    rewrite IH by (assumption || lia). f_equal; lia.
Qed.

Definition answer out : option (list L.Param * list L.Syntax) :=
  match L.refused out with
  | Some _ => None
  | None => match L.term_context (L.result out), L.syntax_pattern (L.result out) with
      | Some params, Some syntax => Some (params, syntax) | _, _ => None end
  end.
Inductive Publication := Returned (value : option (list L.Param * list L.Syntax))
| Failed (reason : Failure).
Definition publish cost maximum available budget source out :=
  match run cost maximum available 0 budget (instrument source (L.trace out)) with
  | Completed _ => Returned (answer out)
  | Stopped _ _ _ reason _ => Failed reason
  end.
Theorem successful_publication_has_exact_original_output : forall cost maximum available budget source out remaining,
  run cost maximum available 0 budget (instrument source (L.trace out)) = Completed remaining ->
  publish cost maximum available budget source out = Returned (answer out).
Proof. intros; unfold publish; now rewrite H. Qed.
Theorem error_never_publishes_a_partial_normalized_pair :
  forall cost maximum available budget source out accepted next suffix reason remaining,
  run cost maximum available 0 budget (instrument source (L.trace out)) =
    Stopped accepted next suffix reason remaining ->
  publish cost maximum available budget source out = Failed reason.
Proof. intros; unfold publish; now rewrite H. Qed.
Theorem original_semantic_refusal_is_not_an_admission_error :
  forall cost maximum available budget source out reason remaining,
  L.refused out = Some reason ->
  run cost maximum available 0 budget (instrument source (L.trace out)) = Completed remaining ->
  publish cost maximum available budget source out = Returned None.
Proof. intros; unfold publish; rewrite H0; unfold answer; rewrite H; reflexivity. Qed.
Theorem shared_and_original_publication_are_identical : forall cost maximum available budget source rule,
  publish cost maximum available budget source
    (L.shared_normalize (fun id => L.project_item (source id)) L.original_constructors rule) =
  publish cost maximum available budget source (L.source_normalize source rule).
Proof. intros; now rewrite L.original_normalization_relocated_exactly. Qed.

Example collection_prepays_each_string_and_keeps_original_callback_order : forall source name kind elem sep open close,
  instrument source [L.FixedElems; L.ConstructCollection name kind elem;
    L.ConstructLiteral open; L.ConstructSep name sep; L.ConstructLiteral close] =
  [block (Some ElemsName) None None [OriginalCallback L.FixedElems];
   block (Some (Collection name kind elem)) (Some ContextBuffer) None
     [CloneGenerated name; CloneKind kind; CloneOriginal elem;
      OriginalCallback (L.ConstructCollection name kind elem)];
   block (Some (Literal open)) (Some SyntaxBuffer) None
     [CopyString open; OriginalCallback (L.ConstructLiteral open)];
   block (Some (Sep name sep)) (Some SyntaxBuffer) None
     [CopyString sep; OriginalCallback (L.ConstructSep name sep)];
   block (Some (Literal close)) (Some SyntaxBuffer) None
     [CopyString close; OriginalCallback (L.ConstructLiteral close)]].
Proof. reflexivity. Qed.

Print Assumptions instrumentation_preserves_exact_original_callbacks.
Print Assumptions binder_copy_is_tied_to_actual_original_build.
Print Assumptions nonbinder_build_does_not_invent_pending_copy.
Print Assumptions original_and_shared_have_identical_paid_sites.
Print Assumptions present_context_has_no_item_or_constructor_admission.
Print Assumptions present_syntax_has_no_item_or_constructor_admission.
Print Assumptions preflight_is_still_the_original_complete_scan.
Print Assumptions complete_run_has_exact_prepaid_total.
Print Assumptions successful_budget_is_exact.
Print Assumptions first_refusal_exposes_only_executed_prefix.
Print Assumptions denied_site_executes_no_local_effect_or_suffix.
Print Assumptions failed_reservation_precedes_argument_copies_and_constructor.
Print Assumptions checked_increment_precedes_fresh_constructor_on_overflow.
Print Assumptions sufficient_paid_domain_preserves_every_original_site.
Print Assumptions successful_publication_has_exact_original_output.
Print Assumptions error_never_publishes_a_partial_normalized_pair.
Print Assumptions original_semantic_refusal_is_not_an_admission_error.
Print Assumptions shared_and_original_publication_are_identical.
Print Assumptions collection_prepays_each_string_and_keeps_original_callback_order.
End LegacyNormalizationAdmission.
