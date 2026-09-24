(** Source-observation and election interface for the ORIGINAL numeric cast
    participation helpers. No cast evaluator or numeric classifier is defined.

    Source: numeric_cast_adapter.rs::cast_machinery_participates,
    recognize_cast_fold, is_numeric_kind, arity_of_kind; semantic_actions.rs::
    trigger_unary_wrapper_source_cat. Rust relocates those bodies once, using
    BinderRuleReader for their existing shallow observations.

    The finite program below specifies the original effectful probe order.
    trigger_shape, wrapper_inner and fold_shape stand for the ORIGINAL borrowed
    structural observations; count_insert is the original HashMap entry/update.
    Their source correspondence is an explicit obligation of mechanical body
    relocation and differential tests, not a conclusion manufactured here.
    numeric, integer and numeric_output reuse existing NativeKind predicates.

    Source facts record body presence and EXPLICIT Fold. DDL captures its actual
    evaluation/mode declarations; the later ReductionPlan default Fold is not a
    source annotation. Unavailable is never false. Normalization keeps these
    facts; original synthetic constructors have known absent body/mode.

    Original winner selection is deliberately a callback: HashMap tie iteration
    is not deterministic. Owned selection can accept a unique maximum and must
    refuse ambiguous maxima. No tie policy, observation equality, or source name
    identity is invented. The rendered-trigger lookup is a DIFFERENT callback
    from native lookup by retained name identity, just as the source constructs
    a fresh Ident from rendered text. Refusal there precedes body/Fold checks.

    Allocation/panic recovery, semantic cast execution and parser correctness
    are not claimed. F.Program is proof instrumentation; Rust does not allocate
    a program/trace or replay source. *)
From Stdlib Require Import List Bool Arith String.
From PrattailWpdaRuntime Require Import PrefixCallbackFailure.
Import ListNotations.
Set Implicit Arguments.

Module CastSourceObservation.
Module F := PrefixCallbackFailure.PrefixCallbackFailure.

Inductive Observation (A : Type) := Known (value : A) | Unavailable.
Arguments Known {A} value.
Arguments Unavailable {A}.
Record SourceFacts := {
  source_body_present : Observation bool;
  explicit_fold : Observation bool
}.
Definition captured_facts body fold :=
  {| source_body_present := Known body; explicit_fold := Known fold |}.
Definition normalized_facts (facts : SourceFacts) := facts.
Definition synthetic_facts := captured_facts false false.
Definition observe_flag (flag : Observation bool) : option bool :=
  match flag with Known value => Some value | Unavailable => None end.

Theorem unavailable_is_not_known_absence :
  observe_flag Unavailable <> observe_flag (Known false).
Proof. discriminate. Qed.
Theorem source_flags_capture_exactly : forall body fold,
  observe_flag (source_body_present (captured_facts body fold)) = Some body /\
  observe_flag (explicit_fold (captured_facts body fold)) = Some fold.
Proof. intros; split; reflexivity. Qed.
Theorem normalization_preserves_both_observations : forall facts,
  normalized_facts facts = facts.
Proof. reflexivity. Qed.
Theorem synthetic_constructor_has_known_absence :
  synthetic_facts =
    {| source_body_present := Known false; explicit_fold := Known false |}.
Proof. reflexivity. Qed.
Theorem implicit_lowering_default_does_not_rewrite_source_flag : forall body,
  explicit_fold (captured_facts body false) = Known false.
Proof. reflexivity. Qed.

Section OriginalSchedule.
Context {Rule Name Native Counts : Type}.
Variable trigger_shape : Rule -> option string.
Variable wrapper_inner : Rule -> option Name.
(** After the original context/length/simple-base/first-name tests, the fold
    shape supplies optional width category and output category. *)
Variable fold_shape : Rule -> Name -> option (option Name * Name).
Variable binary_object_output : Rule -> Name -> bool.
Variable numeric integer numeric_output : Native -> bool.
Variable count_insert : Counts -> Rule -> Counts.

Inductive Request :=
| BodyPresent (rule : Rule)
| ExplicitFold (rule : Rule)
| NativeByIdentity (name : Name)
| NativeByRenderedTrigger (text : string)
| ElectObjectCategory (counts : Counts).

Definition Response request : Type := match request with
| BodyPresent _ | ExplicitFold _ => bool
| NativeByIdentity _ | NativeByRenderedTrigger _ => option Native
| ElectObjectCategory _ => option Name
end.
Definition Program := @F.Program Request Response bool.
Definition ret (value : bool) : Program :=
  @F.Return Request Response bool value.
Definition call request (next : Response request -> Program) : Program :=
  @F.Call Request Response bool request next.

Definition wrapper_program rule (next : bool -> Program) : Program :=
  call (BodyPresent rule) (fun body =>
    if body then next false else
    match wrapper_inner rule with
    | None => next false
    | Some inner => call (NativeByIdentity inner) (fun kind =>
        next (match kind with Some native => numeric native | None => false end))
    end).

Definition fold_output_program rule object output (next : bool -> Program) :=
  call (NativeByIdentity output) (fun kind =>
    next (match kind with
          | Some native => numeric_output native
          | None => binary_object_output rule object
          end)).

Definition fold_program rule object (next : bool -> Program) : Program :=
  call (ExplicitFold rule) (fun fold =>
    if fold then match fold_shape rule object with
    | None => next false
    | Some (width, output) => match width with
      | None => fold_output_program rule object output next
      | Some category => call (NativeByIdentity category) (fun kind =>
          match kind with
          | Some native => if integer native
              then fold_output_program rule object output next else next false
          | None => next false
          end)
      end
    end else next false).

Fixpoint census_program rules counts (next : Counts -> Program) : Program :=
  match rules with
  | [] => next counts
  | rule :: rest => wrapper_program rule (fun wraps =>
      census_program rest (if wraps then count_insert counts rule else counts) next)
  end.

Definition after_trigger_program rule rules counts : Program :=
  wrapper_program rule (fun wraps =>
    if wraps then ret true else
    census_program rules counts (fun counted =>
      call (ElectObjectCategory counted) (fun object =>
        match object with None => ret false
        | Some name => fold_program rule name ret
        end))).

Definition participation_program rule rules counts : Program :=
  match trigger_shape rule with
  | None => after_trigger_program rule rules counts
  | Some text => call (NativeByRenderedTrigger text) (fun kind =>
      match kind with
      | Some native => if numeric native then ret true
          else after_trigger_program rule rules counts
      | None => after_trigger_program rule rules counts
      end)
  end.

Theorem body_probe_precedes_wrapper_shape : forall rule next,
  wrapper_program rule next =
    call (BodyPresent rule) (fun body =>
      if body then next false else
      match wrapper_inner rule with None => next false
      | Some inner => call (NativeByIdentity inner) (fun kind =>
          next (match kind with Some native => numeric native | None => false end))
      end).
Proof. reflexivity. Qed.

Theorem fold_probe_precedes_fold_shape : forall rule object next,
  fold_program rule object next =
    call (ExplicitFold rule) (fun fold =>
      if fold then match fold_shape rule object with
      | None => next false
      | Some (width, output) => match width with
        | None => fold_output_program rule object output next
        | Some category => call (NativeByIdentity category) (fun kind =>
            match kind with
            | Some native => if integer native
                then fold_output_program rule object output next else next false
            | None => next false
            end)
        end
      end else next false).
Proof. reflexivity. Qed.

Theorem rendered_trigger_probe_precedes_any_body_or_fold : forall rule rules counts text,
  trigger_shape rule = Some text ->
  participation_program rule rules counts =
    call (NativeByRenderedTrigger text) (fun kind =>
      match kind with
      | Some native => if numeric native then ret true
          else after_trigger_program rule rules counts
      | None => after_trigger_program rule rules counts
      end).
Proof. intros rule rules counts text H; unfold participation_program; now rewrite H. Qed.

Theorem original_source_roster_keeps_every_wrapper_probe : forall rule rest counts next,
  census_program (rule :: rest) counts next =
    wrapper_program rule (fun wraps =>
      census_program rest (if wraps then count_insert counts rule else counts) next).
Proof. reflexivity. Qed.

(** Immediate refusal applies to EVERY request above, including rendered
    lookup before a Fold observation. Failed observation is not a nonmatch. *)
Definition first_error_stops_without_fallback := @F.first_error_skips_any_continuation.
Definition first_failure_exact_prefix := @F.failed_run_has_exact_first_failure.
Definition all_ok_preserves_source_program := @F.all_ok_exact_original.
Definition source_reader_substitution := @F.callback_reader_substitution.
Definition failure_publishes_no_partial_result := @F.failure_has_no_partial_output.
End OriginalSchedule.

Section Election.
Context {Name : Type}.
Definition maximal (entries : list (Name * nat)) name :=
  exists count, In (name, count) entries /\
    forall other other_count, In (other, other_count) entries -> other_count <= count.
Definition unique_maximum entries name :=
  maximal entries name /\ forall other, maximal entries other -> other = name.

Theorem admitted_unique_winner_agrees_with_any_original_maximum :
  forall entries chosen original,
  unique_maximum entries chosen -> maximal entries original -> original = chosen.
Proof. intros entries chosen original [_ H] M; now apply H. Qed.

Theorem distinct_maximal_names_cannot_receive_unique_election_evidence :
  forall entries left right chosen,
  maximal entries left -> maximal entries right -> left <> right ->
  ~ unique_maximum entries chosen.
Proof.
  intros entries left right chosen L R N [_ U].
  specialize (U left L) as A.
  specialize (U right R) as B.
  apply N. now rewrite A, B.
Qed.

Theorem empty_census_has_no_winner : forall name,
  ~ maximal [] name.
Proof. intros name [count [H _]]; inversion H. Qed.

(** The actual owned election compares map keys/winner observations with the
    original grouping identity. The theorem cannot justify spelling-based
    equality if the reader or map has not established that correspondence. *)
End Election.

Print Assumptions unavailable_is_not_known_absence.
Print Assumptions source_flags_capture_exactly.
Print Assumptions normalization_preserves_both_observations.
Print Assumptions synthetic_constructor_has_known_absence.
Print Assumptions implicit_lowering_default_does_not_rewrite_source_flag.
Print Assumptions body_probe_precedes_wrapper_shape.
Print Assumptions fold_probe_precedes_fold_shape.
Print Assumptions rendered_trigger_probe_precedes_any_body_or_fold.
Print Assumptions original_source_roster_keeps_every_wrapper_probe.
Print Assumptions first_error_stops_without_fallback.
Print Assumptions first_failure_exact_prefix.
Print Assumptions all_ok_preserves_source_program.
Print Assumptions source_reader_substitution.
Print Assumptions failure_publishes_no_partial_result.
Print Assumptions admitted_unique_winner_agrees_with_any_original_maximum.
Print Assumptions distinct_maximal_names_cannot_receive_unique_election_evidence.
Print Assumptions empty_census_has_no_winner.
End CastSourceObservation.
