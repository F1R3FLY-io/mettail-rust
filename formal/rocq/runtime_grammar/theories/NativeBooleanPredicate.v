(** * Checked native Boolean results at the FLT/where boundary

    A guest constructor named [yes] is not a Rholang Boolean. The guest theory
    must reduce its predicate to a native Boolean literal in a declared Boolean
    carrier sort. This interface model consumes the existing semantic kernel's
    complete, receipt-checked result roster; it does not implement another
    evaluator or assume that a bounded but unfinished search is complete.

    The flags below stand for concrete checks at the installed-language
    boundary: exact handle ownership, sort, exhaustive outgoing-transition
    enumeration, absence of a successor, receipt validation, all parser
    readings, rights, purity, cancellation, and resource limits. A successful
    verdict requires every relevant check. The model proves the classifier and
    COMM composition law, not the implementation of those checks in Rust.
*)

From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
From RuntimeGrammar Require Import WherePredicateCommit SemanticTransitionKernel.
Import ListNotations.

Module NativeBooleanPredicate.
Module Guard := WherePredicateCommit.WherePredicateCommit.
Module Kernel := SemanticTransitionKernel.SemanticTransitionKernel.

Record Context := context {
  installed_owner : nat;
  boolean_sort : nat
}.

Record NativeResult := native_result {
  result_owner : nat;
  result_sort : nat;
  native_boolean : option bool;
  outgoing_enumeration_complete : bool;
  has_no_successor : bool;
  receipt_checked : bool
}.

(** A literal is a normal form only after complete transition enumeration.
    A constructor with the spelling [yes] or [no] has [native_boolean = None]. *)
Definition result_certified (ctx : Context) (result : NativeResult) : bool :=
  Nat.eqb (result_owner result) (installed_owner ctx) &&
  Nat.eqb (result_sort result) (boolean_sort ctx) &&
  outgoing_enumeration_complete result &&
  has_no_successor result && receipt_checked result.

Definition project (ctx : Context) (result : NativeResult) : Guard.Verdict :=
  if result_certified ctx result then
    match native_boolean result with
    | Some true => Guard.Yes
    | Some false => Guard.No
    | None => Guard.Unknown
    end
  else Guard.Unknown.

Record Run := run {
  required_rights_held : bool;
  relation_effect_safe : bool;
  handle_still_installed : bool;
  every_parse_retained : bool;
  semantic_roster_complete : bool;
  within_resource_limits : bool;
  not_cancelled : bool;
  results : list NativeResult
}.

Definition execution_authorized (r : Run) : bool :=
  required_rights_held r && relation_effect_safe r && handle_still_installed r.

Definition complete (r : Run) : bool :=
  every_parse_retained r && semantic_roster_complete r &&
  within_resource_limits r && not_cancelled r.

Definition predicate (ctx : Context) (r : Run) : Guard.Verdict :=
  if execution_authorized r then
    Guard.classify (complete r) (map (project ctx) (results r))
  else Guard.Unknown.

(** The same checked verdict may be materialized as a host GBool only when
    complete; [Unknown] is not a host false value. *)
Definition host_boolean (ctx : Context) (r : Run) : option bool :=
  match predicate ctx r with
  | Guard.Yes => Some true
  | Guard.No => Some false
  | Guard.Unknown => None
  end.

Lemma unmapped_constructor_is_unknown : forall ctx result,
  native_boolean result = None -> project ctx result = Guard.Unknown.
Proof.
  intros ctx result H.
  unfold project.
  destruct (result_certified ctx result); [now rewrite H|reflexivity].
Qed.

Lemma uncertified_result_is_unknown : forall ctx result,
  result_certified ctx result = false -> project ctx result = Guard.Unknown.
Proof.
  intros ctx result H; unfold project; now rewrite H.
Qed.

Lemma projected_true_is_certified : forall ctx result,
  project ctx result = Guard.Yes ->
  result_certified ctx result = true /\ native_boolean result = Some true.
Proof.
  intros ctx result H; unfold project in H.
  destruct (result_certified ctx result) eqn:Certified; [|discriminate].
  destruct (native_boolean result) as [value|] eqn:Native; [|discriminate].
  destruct value; [now split|discriminate].
Qed.

Lemma projected_false_is_certified : forall ctx result,
  project ctx result = Guard.No ->
  result_certified ctx result = true /\ native_boolean result = Some false.
Proof.
  intros ctx result H; unfold project in H.
  destruct (result_certified ctx result) eqn:Certified; [|discriminate].
  destruct (native_boolean result) as [value|] eqn:Native; [|discriminate].
  destruct value; [discriminate|now split].
Qed.

Lemma incomplete_is_unknown : forall ctx r,
  complete r = false -> predicate ctx r = Guard.Unknown.
Proof.
  intros ctx r H; unfold predicate.
  destruct (execution_authorized r); [now rewrite H; apply Guard.incomplete_unknown|reflexivity].
Qed.

Lemma empty_is_unknown : forall ctx r,
  results r = [] -> predicate ctx r = Guard.Unknown.
Proof.
  intros ctx r H; unfold predicate; rewrite H.
  destruct (execution_authorized r); [apply Guard.empty_unknown|reflexivity].
Qed.

Lemma missing_rights_is_unknown : forall ctx r,
  required_rights_held r = false -> predicate ctx r = Guard.Unknown.
Proof.
  intros ctx r H; unfold predicate, execution_authorized; now rewrite H.
Qed.

Lemma unsafe_effect_is_unknown : forall ctx r,
  relation_effect_safe r = false -> predicate ctx r = Guard.Unknown.
Proof.
  intros ctx r H; unfold predicate, execution_authorized.
  destruct (required_rights_held r); simpl; try reflexivity; now rewrite H.
Qed.

Lemma revoked_handle_is_unknown : forall ctx r,
  handle_still_installed r = false -> predicate ctx r = Guard.Unknown.
Proof.
  intros ctx r H; unfold predicate, execution_authorized.
  destruct (required_rights_held r), (relation_effect_safe r); simpl;
    try reflexivity; now rewrite H.
Qed.

Lemma incomplete_parse_roster_is_unknown : forall ctx r,
  every_parse_retained r = false -> predicate ctx r = Guard.Unknown.
Proof.
  intros ctx r H; apply incomplete_is_unknown.
  unfold complete; now rewrite H.
Qed.

Lemma incomplete_semantic_roster_is_unknown : forall ctx r,
  semantic_roster_complete r = false -> predicate ctx r = Guard.Unknown.
Proof.
  intros ctx r H; apply incomplete_is_unknown.
  unfold complete; destruct (every_parse_retained r); simpl; try reflexivity; now rewrite H.
Qed.

Lemma exhausted_budget_is_unknown : forall ctx r,
  within_resource_limits r = false -> predicate ctx r = Guard.Unknown.
Proof.
  intros ctx r H; apply incomplete_is_unknown.
  unfold complete.
  destruct (every_parse_retained r), (semantic_roster_complete r); simpl;
    try reflexivity; now rewrite H.
Qed.

Lemma cancellation_is_unknown : forall ctx r,
  not_cancelled r = false -> predicate ctx r = Guard.Unknown.
Proof.
  intros ctx r H; apply incomplete_is_unknown.
  unfold complete.
  destruct (every_parse_retained r), (semantic_roster_complete r),
    (within_resource_limits r); simpl; try reflexivity; now rewrite H.
Qed.

Lemma uniform_verdict_classifies : forall verdict values,
  (verdict = Guard.Yes \/ verdict = Guard.No) ->
  values <> [] -> Forall (fun value => value = verdict) values ->
  Guard.classify true values = verdict.
Proof.
  intros verdict [|first rest] Known Nonempty Uniform; [contradiction|].
  inversion Uniform as [| ? ? First Rest]; subst first.
  destruct Known as [Known|Known]; subst verdict; simpl.
  - assert (forallb (fun value => match value with
              | Guard.Yes => true | _ => false end) rest = true) as All.
    { apply forallb_forall. intros value Member.
      pose proof ((proj1 (Forall_forall _ _) Rest) value Member) as Equal.
      now rewrite Equal. }
    now rewrite All.
  - assert (forallb (fun value => match value with
              | Guard.No => true | _ => false end) rest = true) as All.
    { apply forallb_forall. intros value Member.
      pose proof ((proj1 (Forall_forall _ _) Rest) value Member) as Equal.
      now rewrite Equal. }
    now rewrite All.
Qed.

Lemma uniform_projected_verdict : forall ctx verdict values,
  Forall (fun result => project ctx result = verdict) values ->
  Forall (fun value => value = verdict) (map (project ctx) values).
Proof.
  intros ctx verdict values Uniform.
  induction Uniform; simpl; constructor; assumption.
Qed.

Lemma true_verdict_is_uniform_and_complete : forall ctx r,
  predicate ctx r = Guard.Yes ->
  execution_authorized r = true /\ complete r = true /\
  results r <> [] /\
  Forall (fun result => project ctx result = Guard.Yes) (results r).
Proof.
  intros ctx r H; unfold predicate in H.
  destruct (execution_authorized r) eqn:Authorized; [|discriminate].
  destruct (complete r) eqn:Complete; [|simpl in H; discriminate].
  apply Guard.classified_yes_sound in H as [Nonempty Uniform].
  repeat split; try assumption.
  - destruct (results r) as [|head tail]; [simpl in Nonempty; contradiction|discriminate].
  - apply Forall_forall; intros result Member.
    apply (proj1 (Forall_forall _ _) Uniform).
    apply in_map; exact Member.
Qed.

Lemma false_verdict_is_uniform_and_complete : forall ctx r,
  predicate ctx r = Guard.No ->
  execution_authorized r = true /\ complete r = true /\
  results r <> [] /\
  Forall (fun result => project ctx result = Guard.No) (results r).
Proof.
  intros ctx r H; unfold predicate in H.
  destruct (execution_authorized r) eqn:Authorized; [|discriminate].
  destruct (complete r) eqn:Complete; [|simpl in H; discriminate].
  apply Guard.classified_no_sound in H as [Nonempty Uniform].
  repeat split; try assumption.
  - destruct (results r) as [|head tail]; [simpl in Nonempty; contradiction|discriminate].
  - apply Forall_forall; intros result Member.
    apply (proj1 (Forall_forall _ _) Uniform).
    apply in_map; exact Member.
Qed.

Theorem true_verdict_iff_complete_uniform_native_true : forall ctx r,
  predicate ctx r = Guard.Yes <->
  execution_authorized r = true /\ complete r = true /\
  results r <> [] /\
  Forall (fun result => project ctx result = Guard.Yes) (results r).
Proof.
  intros ctx r; split.
  - apply true_verdict_is_uniform_and_complete.
  - intros [Authorized [Complete [Nonempty Uniform]]].
    unfold predicate; rewrite Authorized, Complete.
    apply uniform_verdict_classifies; [now left| |].
    + destruct (results r); [contradiction|discriminate].
    + now apply uniform_projected_verdict.
Qed.

Theorem false_verdict_iff_complete_uniform_native_false : forall ctx r,
  predicate ctx r = Guard.No <->
  execution_authorized r = true /\ complete r = true /\
  results r <> [] /\
  Forall (fun result => project ctx result = Guard.No) (results r).
Proof.
  intros ctx r; split.
  - apply false_verdict_is_uniform_and_complete.
  - intros [Authorized [Complete [Nonempty Uniform]]].
    unfold predicate; rewrite Authorized, Complete.
    apply uniform_verdict_classifies; [now right| |].
    + destruct (results r); [contradiction|discriminate].
    + now apply uniform_projected_verdict.
Qed.

Theorem unknown_iff_neither_certified_boolean : forall ctx r,
  predicate ctx r = Guard.Unknown <->
  ~ (execution_authorized r = true /\ complete r = true /\
     results r <> [] /\
     Forall (fun result => project ctx result = Guard.Yes) (results r)) /\
  ~ (execution_authorized r = true /\ complete r = true /\
     results r <> [] /\
     Forall (fun result => project ctx result = Guard.No) (results r)).
Proof.
  intros ctx r; split.
  - intros Unknown; split; intros Uniform.
    + apply (proj2 (true_verdict_iff_complete_uniform_native_true ctx r)) in Uniform.
      now rewrite Uniform in Unknown.
    + apply (proj2 (false_verdict_iff_complete_uniform_native_false ctx r)) in Uniform.
      now rewrite Uniform in Unknown.
  - intros [NotTrue NotFalse].
    destruct (predicate ctx r) eqn:Verdict; [| |reflexivity].
    + apply (proj1 (true_verdict_iff_complete_uniform_native_true ctx r)) in Verdict.
      now apply NotTrue in Verdict.
    + apply (proj1 (false_verdict_iff_complete_uniform_native_false ctx r)) in Verdict.
      now apply NotFalse in Verdict.
Qed.

Theorem accepted_result_is_native_true : forall ctx r result,
  predicate ctx r = Guard.Yes -> In result (results r) ->
  result_certified ctx result = true /\ native_boolean result = Some true.
Proof.
  intros ctx r result Accepted Member.
  apply true_verdict_is_uniform_and_complete in Accepted as [_ [_ [_ Uniform]]].
  apply projected_true_is_certified.
  exact ((proj1 (Forall_forall _ _) Uniform) result Member).
Qed.

Theorem rejected_result_is_native_false : forall ctx r result,
  predicate ctx r = Guard.No -> In result (results r) ->
  result_certified ctx result = true /\ native_boolean result = Some false.
Proof.
  intros ctx r result Rejected Member.
  apply false_verdict_is_uniform_and_complete in Rejected as [_ [_ [_ Uniform]]].
  apply projected_false_is_certified.
  exact ((proj1 (Forall_forall _ _) Uniform) result Member).
Qed.

Theorem mixed_candidates_are_unknown : forall ctx r positive negative,
  In positive (results r) -> In negative (results r) ->
  project ctx positive = Guard.Yes -> project ctx negative = Guard.No ->
  predicate ctx r = Guard.Unknown.
Proof.
  intros ctx r positive negative Positive Negative IsYes IsNo.
  destruct (predicate ctx r) eqn:Verdict; [| |reflexivity].
  - apply true_verdict_is_uniform_and_complete in Verdict as [_ [_ [_ Uniform]]].
    pose proof ((proj1 (Forall_forall _ _) Uniform) negative Negative) as Evidence.
    rewrite Evidence in IsNo; discriminate.
  - apply false_verdict_is_uniform_and_complete in Verdict as [_ [_ [_ Uniform]]].
    pose proof ((proj1 (Forall_forall _ _) Uniform) positive Positive) as Evidence.
    rewrite Evidence in IsYes; discriminate.
Qed.

Theorem unclassified_candidate_is_unknown : forall ctx r result,
  In result (results r) -> project ctx result = Guard.Unknown ->
  predicate ctx r = Guard.Unknown.
Proof.
  intros ctx r result Member Unclassified.
  destruct (predicate ctx r) eqn:Verdict; [| |reflexivity].
  - apply true_verdict_is_uniform_and_complete in Verdict as [_ [_ [_ Uniform]]].
    pose proof ((proj1 (Forall_forall _ _) Uniform) result Member) as Evidence.
    now rewrite Evidence in Unclassified.
  - apply false_verdict_is_uniform_and_complete in Verdict as [_ [_ [_ Uniform]]].
    pose proof ((proj1 (Forall_forall _ _) Uniform) result Member) as Evidence.
    now rewrite Evidence in Unclassified.
Qed.

(** Existing explicit predicate roles and native-Boolean projection agree when
    they assign the same verdict to every original result occurrence. Neither
    classifier may elect a first candidate or discard a duplicate. *)
Theorem explicit_role_compatibility : forall ctx r role_project,
  (forall result, In result (results r) ->
    role_project result = project ctx result) ->
  (if execution_authorized r then
     Guard.classify (complete r) (map role_project (results r))
   else Guard.Unknown) = predicate ctx r.
Proof.
  intros ctx r role_project Same; unfold predicate.
  assert (map role_project (results r) = map (project ctx) (results r)) as Equal.
  { apply map_ext_in; intros result Member; apply Same; exact Member. }
  now rewrite Equal.
Qed.

Lemma unknown_has_no_host_boolean : forall ctx r,
  predicate ctx r = Guard.Unknown -> host_boolean ctx r = None.
Proof. intros ctx r H; unfold host_boolean; now rewrite H. Qed.

Definition verdict_boolean (verdict : Guard.Verdict) : option bool :=
  match verdict with
  | Guard.Yes => Some true
  | Guard.No => Some false
  | Guard.Unknown => None
  end.

Theorem strong_kleene_negation_preserves_native_boolean : forall verdict,
  verdict_boolean (Guard.negate verdict) =
  option_map negb (verdict_boolean verdict).
Proof. intros []; reflexivity. Qed.

Theorem host_boolean_negation : forall ctx r,
  verdict_boolean (Guard.negate (predicate ctx r)) =
  option_map negb (host_boolean ctx r).
Proof.
  intros ctx r; unfold host_boolean.
  exact (strong_kleene_negation_preserves_native_boolean (predicate ctx r)).
Qed.

Theorem unknown_cannot_commit : forall State ctx r authority funded mutation (state : State),
  predicate ctx r = Guard.Unknown ->
  Guard.commit (predicate ctx r) authority funded mutation state = state.
Proof.
  intros State ctx r authority funded mutation state H.
  apply Guard.refusal_preserves_state.
  now left; rewrite H; discriminate.
Qed.

Theorem unauthorized_or_incomplete_cannot_commit :
  forall State ctx r authority funded mutation (state : State),
  (execution_authorized r = false \/ complete r = false) ->
  Guard.commit (predicate ctx r) authority funded mutation state = state.
Proof.
  intros State ctx r authority funded mutation state [Unauthorized|Incomplete].
  - apply unknown_cannot_commit; unfold predicate; now rewrite Unauthorized.
  - apply unknown_cannot_commit; now apply incomplete_is_unknown.
Qed.

(** Direct normalization reuses the existing theory-wide rewrite selector.
    There is no synthetic action ID or second rewrite algorithm. *)
Definition direct_rule_selected := Kernel.rewrite_relation_rule_selected.

Theorem direct_entry_selects_exactly_the_existing_relation : forall sort rule,
  direct_rule_selected sort rule = true <->
  Kernel.transition_rule_executable rule = true /\
  Kernel.transition_rule_origin rule = Kernel.RewriteOrigin /\
  Kernel.transition_rule_source_sort rule = sort.
Proof.
  exact Kernel.rewrite_relation_selects_exactly_executable_same_sort_rewrites.
Qed.

Theorem direct_entry_never_selects_an_equation : forall sort rule,
  Kernel.transition_rule_origin rule = Kernel.EquationOrigin ->
  direct_rule_selected sort rule = false.
Proof. exact Kernel.rewrite_relation_never_selects_an_equation. Qed.

End NativeBooleanPredicate.
