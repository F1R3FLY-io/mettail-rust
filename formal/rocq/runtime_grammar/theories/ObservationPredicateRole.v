(** * Optional predicate roles at the existing observation boundary

    A role identifies an input constructor and two closed result terms. It is
    neither authority nor a second observation registry. This model covers the
    new binding checks, their exact source coordinates, role commitments before
    hashing, and the borrowed-view refinement used to reuse term construction.

    Closed term construction itself remains the existing checked compiler and
    kernel worker. Its successful output keys are compared, not source arena
    indices or an invented alpha-equivalence. The model deliberately does not
    claim correctness of Rust, hash injectivity, whole-kernel normalization, or
    the later FLT where/COMM integration. *)

From Stdlib Require Import Lists.List Strings.String Bool.Bool Arith.PeanoNat.
Import ListNotations.

Module ObservationPredicateRole.

Record Action := action {
  action_name : string;
  domain : list string;
  codomain : string;
  pure_class : bool;
  effect_name : string;
  executable_rule : bool
}.

Record Effect := effect {
  declared_effect_name : string;
  declared_pure_class : bool;
  emitted_effects : list string
}.

(** Exact closed result keys are produced by the existing native worker.
    Failure to construct either constant cannot establish a predicate role. *)
Record Role := role {
  input_constructor : string;
  input_sort : string;
  result_sort : string;
  accepting_key : option (list nat);
  rejecting_key : option (list nat)
}.

Fixpoint words_equal (left right : list nat) : bool :=
  match left, right with
  | [], [] => true
  | x :: xs, y :: ys => Nat.eqb x y && words_equal xs ys
  | _, _ => false
  end.

Lemma words_equal_spec : forall left right,
  words_equal left right = true <-> left = right.
Proof.
  induction left as [|x xs IH]; intros [|y ys]; cbn.
  - tauto.
  - split; discriminate.
  - split; discriminate.
  - rewrite andb_true_iff, Nat.eqb_eq, IH.
    split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

Definition distinct_results (r : Role) :=
  match accepting_key r, rejecting_key r with
  | Some yes, Some no => negb (words_equal yes no)
  | _, _ => false
  end.

Definition valid_binding (observation_action observation_result : string)
    (a : Action) (e : Effect) (r : Role) : bool :=
  String.eqb observation_action (action_name a) &&
  (match domain a with
   | [input] => String.eqb input (input_sort r)
   | _ => false
   end) &&
  String.eqb observation_result (codomain a) &&
  String.eqb (result_sort r) (codomain a) &&
  pure_class a && executable_rule a &&
  String.eqb (effect_name a) (declared_effect_name e) &&
  declared_pure_class e &&
  (match emitted_effects e with [] => true | _ => false end) &&
  distinct_results r.

Theorem accepted_role_has_distinct_constructed_results :
  forall oa os a e r, valid_binding oa os a e r = true ->
  exists yes no, accepting_key r = Some yes /\ rejecting_key r = Some no /\
    yes <> no.
Proof.
  intros oa os a e r H.
  unfold valid_binding in H; apply andb_true_iff in H; destruct H as [_ H].
  unfold distinct_results in H.
  destruct (accepting_key r) as [yes|] eqn:Y; [|discriminate].
  destruct (rejecting_key r) as [no|] eqn:N; [|discriminate].
  exists yes, no; repeat split; try assumption.
  intros E; subst no. rewrite (proj2 (words_equal_spec yes yes) eq_refl) in H.
  discriminate.
Qed.

Theorem effect_emission_refuses_role :
  forall oa os a e r emitted rest,
    emitted_effects e = emitted :: rest -> valid_binding oa os a e r = false.
Proof.
  intros oa os a e r emitted rest H.
  unfold valid_binding; rewrite H, andb_false_r; reflexivity.
Qed.

Theorem wrong_observation_action_refuses_role :
  forall oa os a e r, oa <> action_name a -> valid_binding oa os a e r = false.
Proof.
  intros oa os a e r H. unfold valid_binding.
  assert (String.eqb oa (action_name a) = false) as E by now apply String.eqb_neq.
  now rewrite E.
Qed.

(** Selection operates on the original declaration list, retaining its dense
    observation coordinate. Validation rejects duplicate input bindings before
    this selector can be used; it never chooses the first of several roles. *)
Definition bindings_for (requested : string) (roles : list (nat * Role)) :=
  filter (fun binding => String.eqb (input_constructor (snd binding)) requested)
    roles.

Definition select_role requested roles : option (nat * Role) :=
  match bindings_for requested roles with
  | [binding] => Some binding
  | _ => None
  end.

Theorem selection_has_exactly_one_source_binding : forall requested roles binding,
  select_role requested roles = Some binding ->
  bindings_for requested roles = [binding].
Proof.
  intros requested roles binding H. unfold select_role in H.
  destruct (bindings_for requested roles) as [|first rest] eqn:E; [discriminate|].
  destruct rest; [inversion H; reflexivity | discriminate].
Qed.

Theorem selection_preserves_source_member : forall requested roles binding,
  select_role requested roles = Some binding -> In binding roles.
Proof.
  intros requested roles binding H.
  apply selection_has_exactly_one_source_binding in H.
  assert (In binding (bindings_for requested roles)) as M by (rewrite H; now left).
  apply filter_In in M; tauto.
Qed.

Theorem missing_role_never_infers_truthiness : forall requested roles,
  bindings_for requested roles = [] -> select_role requested roles = None.
Proof. intros requested roles H; unfold select_role; now rewrite H. Qed.

Theorem duplicate_role_never_selects_first : forall requested roles first second rest,
  bindings_for requested roles = first :: second :: rest ->
  select_role requested roles = None.
Proof. intros requested roles first second rest H; unfold select_role; now rewrite H. Qed.

(** Canonical payload records include the entire optional role, with an explicit
    schema/ABI version. Equality below concerns unhashed values, not digests. *)
Record CanonicalObservation (Term : Type) := canonical_observation {
  observation_name : string;
  observation_action : string;
  observation_result : string;
  predicate_role : option (string * Term * Term)
}.
Arguments predicate_role {Term}.

Definition theory_payload {Term} (abi : nat)
    (observations : list (CanonicalObservation Term)) :=
  (abi, observations).

Theorem canonical_payload_retains_roles : forall Term abi left right,
  @theory_payload Term abi left = theory_payload abi right ->
  map predicate_role left = map predicate_role right.
Proof. intros Term abi left right H; inversion H; reflexivity. Qed.

Theorem canonical_payload_rejects_old_version : forall Term old current left right,
  old <> current -> @theory_payload Term old left <> theory_payload current right.
Proof. intros Term old current left right H E; inversion E; contradiction. Qed.

Definition language_payload {Grammar Term} abi (grammar : Grammar)
    (observations : list (CanonicalObservation Term)) :=
  (grammar, theory_payload abi observations).

Theorem role_changes_preserve_parser_projection : forall Grammar Term abi grammar left right,
  fst (@language_payload Grammar Term abi grammar left) =
  fst (@language_payload Grammar Term abi grammar right).
Proof. reflexivity. Qed.

(** The runtime refactoring only exposes the term and variable slices already
    read by the worker. Arbitrary rule metadata cannot affect this adapter.
    The theorem is universal in the existing worker, not an assumed proof of it. *)
Record Rule (Term Slot Metadata : Type) := rule {
  terms : list Term; variables : list Slot; metadata : Metadata
}.
Arguments terms {Term Slot Metadata}.
Arguments variables {Term Slot Metadata}.

Definition through_rule {Term Slot Metadata Result}
    (worker : list Term -> list Slot -> Result) (r : Rule Term Slot Metadata) :=
  worker (terms r) (variables r).

Theorem borrowed_view_preserves_worker_result : forall Term Slot Metadata Result
    (worker : list Term -> list Slot -> Result) (r : Rule Term Slot Metadata),
  through_rule worker r = worker (terms r) (variables r).
Proof. reflexivity. Qed.

End ObservationPredicateRole.
