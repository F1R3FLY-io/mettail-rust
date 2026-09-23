(** Runtime schema capture: conservative logical-size admission.

    This instantiates the existing checked debit lemmas and the existing
    AuthoredRuleCaptureProjection schedule; it is not a second capture walk.
    N = first shallow observations; E = immediate typed-reference fields;
    Q = elements of Names/Params/Syntax/Rule.items vectors; R = ordered roots;
    B = UTF-8 bytes copied into shallow payloads. A reference inside a vector
    occupies both one Q payload slot and one E reference field. Duplicates
    count; completed-node reuse does not produce another observation.

    Retained-capture admission uses existing canonical caps with I=R+E+Q.
    This deliberately does NOT assert the same accepted domain as canonical
    value admission. The original canonical gate still executes unchanged.
    Its string helper only becomes crate-visible; its checks, order, counter
    mutation on total-limit failure and diagnostics remain the original ones.

    Source shallow admission precedes payload clone/collect. Root admission
    precedes root Vec construction. Finish moves strings and remaps IDs;
    it does not charge content a second time. The callback checks actual
    frame and memo/store/class lengths against the bounds below before growth.
    All sums are checked against the machine ceiling before Rust addition.

    These are logical lengths, not physical allocator capacities, byte sizes,
    RSS, timing, allocator-failure recovery, or arbitrary traversal termination.
    Borrowed schema source already exists; its memory is not recharged here.
    Scalar payload tags are fixed-size. Pending/finished recipe vectors may
    coexist with one remapped vector, yielding the explicit factor two below.
    No capture/transport/ABI/source parser equivalence is added by this model.
*)
From Stdlib Require Import List Arith Bool Lia.
From PrattailWpdaRuntime Require Import ReconstructionWorkBudget AuthoredRuleCaptureProjection.
Import ListNotations.
Module C := AuthoredRuleCaptureProjection.AuthoredRuleCaptureProjection.

Module AuthoredRuntimeCaptureAdmission.

(** Reuse the existing component-wise overflow check. No unchecked sum is
    needed in the executable gate to decide whether the components fit. *)
Definition checked_total ceiling parts :=
  match debit_all ceiling parts with
  | Some _ => Some (total_charge parts)
  | None => None
  end.

Theorem checked_total_exact_and_bounded : forall ceiling parts total,
  checked_total ceiling parts = Some total ->
  total = total_charge parts /\ total <= ceiling.
Proof.
  intros ceiling parts total H. unfold checked_total in H.
  destruct (debit_all ceiling parts) as [remaining|] eqn:D; [|discriminate].
  inversion H; subst. split; [reflexivity|].
  pose proof (component_checks_make_their_later_size_sum_machine_safe
    parts ceiling ceiling remaining (Nat.le_refl _) D). tauto.
Qed.

Theorem checked_total_accepts_exactly_fitting_components : forall ceiling parts,
  checked_total ceiling parts = Some (total_charge parts) <->
  total_charge parts <= ceiling.
Proof.
  intros ceiling parts. split.
  - intro H. apply checked_total_exact_and_bounded in H. tauto.
  - intro H. unfold checked_total.
    rewrite (every_affordable_sequence_succeeds parts ceiling H). reflexivity.
Qed.

(** Exact original string-helper branch/mutation order. None is the old error
    result; the second component is its mutable total after returning. The
    machine check models usize::checked_add, before total assignment. *)
Definition original_string_gate word per_string aggregate used bytes
    : option unit * nat :=
  if bytes <=? per_string then
    if used + bytes <=? word then
      if used + bytes <=? aggregate
      then (Some tt, used + bytes) else (None, used + bytes)
    else (None, used)
  else (None, used).

Definition exposed_string_gate := original_string_gate.

Theorem exposing_original_helper_changes_no_branch_or_counter :
  forall word single aggregate used bytes,
  exposed_string_gate word single aggregate used bytes =
  original_string_gate word single aggregate used bytes.
Proof. reflexivity. Qed.

Theorem string_success_has_exact_size : forall word single aggregate used bytes next,
  original_string_gate word single aggregate used bytes = (Some tt, next) ->
  next = used + bytes /\ bytes <= single /\ next <= word /\ next <= aggregate.
Proof.
  intros word single aggregate used bytes next H. unfold original_string_gate in H.
  destruct (bytes <=? single) eqn:S; [|discriminate].
  destruct (used + bytes <=? word) eqn:W; [|discriminate].
  destruct (used + bytes <=? aggregate) eqn:A; [|discriminate].
  inversion H; subst. apply Nat.leb_le in S, W, A. auto.
Qed.

Theorem individual_refusal_keeps_counter : forall word single aggregate used bytes,
  single < bytes -> original_string_gate word single aggregate used bytes = (None, used).
Proof.
  intros. unfold original_string_gate.
  assert (bytes <=? single = false) by (apply Nat.leb_gt; lia).
  now rewrite H0.
Qed.

Theorem total_refusal_retains_original_assignment : forall word single aggregate used bytes,
  bytes <= single -> used + bytes <= word -> aggregate < used + bytes ->
  original_string_gate word single aggregate used bytes = (None, used + bytes).
Proof.
  intros. unfold original_string_gate.
  assert (bytes <=? single = true) by (apply Nat.leb_le; lia).
  assert (used + bytes <=? word = true) by (apply Nat.leb_le; lia).
  assert (used + bytes <=? aggregate = false) by (apply Nat.leb_gt; lia).
  now rewrite H2, H3, H4.
Qed.

Definition copy_after_string_gate {X} word single aggregate used bytes
    (copy : unit -> X) : option X :=
  match fst (original_string_gate word single aggregate used bytes) with
  | Some _ => Some (copy tt) | None => None
  end.

Theorem refused_string_has_no_copied_result : forall X word single aggregate used bytes next
    (copy : unit -> X),
  original_string_gate word single aggregate used bytes = (None, next) ->
  copy_after_string_gate word single aggregate used bytes copy = None.
Proof. intros. unfold copy_after_string_gate. now rewrite H. Qed.

(** Canonical nodes/items caps are reused for retained content, not every
    transient allocation event. Q and E are distinct logical dimensions. *)
Definition admit_sizes word node_cap item_cap roots nodes edges slots :=
  match checked_total word [roots; edges; slots] with
  | None => false
  | Some items => (nodes <=? word) && (nodes <=? node_cap) && (items <=? item_cap)
  end.

Theorem admitted_sizes_are_bounded : forall word nc ic r n e q,
  admit_sizes word nc ic r n e q = true ->
  n <= word /\ n <= nc /\ r + e + q <= word /\ r + e + q <= ic.
Proof.
  intros word nc ic r n e q H. unfold admit_sizes in H.
  destruct (checked_total word [r; e; q]) as [items|] eqn:T; [|discriminate].
  apply checked_total_exact_and_bounded in T. cbn in T.
  repeat rewrite andb_true_iff in H. destruct H as [[N C] I].
  apply Nat.leb_le in N, C, I. lia.
Qed.

Theorem admitted_root_roster_is_bounded : forall word nc ic roots,
  admit_sizes word nc ic roots 0 0 0 = true -> roots <= word /\ roots <= ic.
Proof. intros. apply admitted_sizes_are_bounded in H. lia. Qed.

(** Counts are cumulative first observations, never allocations. A successful
    Enter adds one node and its edge/slot fields; Ready reuse and Finish leave
    these content counts unchanged. This charge is before shallow allocation. *)
Definition first_observation word nc ic r n e q new_edges new_slots :=
  match checked_total word [n; 1], checked_total word [e; new_edges],
        checked_total word [q; new_slots] with
  | Some nn, Some ee, Some qq => admit_sizes word nc ic r nn ee qq
  | _, _, _ => false
  end.

Theorem first_observation_bounds_new_content : forall word nc ic r n e q de dq,
  first_observation word nc ic r n e q de dq = true ->
  n + 1 <= nc /\ r + (e + de) + (q + dq) <= ic.
Proof.
  intros word nc ic r n e q de dq H. unfold first_observation in H.
  destruct (checked_total word [n; 1]) as [nn|] eqn:N; [|discriminate].
  destruct (checked_total word [e; de]) as [ee|] eqn:E; [|discriminate].
  destruct (checked_total word [q; dq]) as [qq|] eqn:Q; [|discriminate].
  apply checked_total_exact_and_bounded in N, E, Q.
  apply admitted_sizes_are_bounded in H. cbn in N, E, Q. lia.
Qed.

(** The actual existing scheduling equation supplies the frame increment;
    no replacement traversal or scheduler is defined. *)
Theorem existing_enter_frame_count : forall edge source rest,
  length (C.schedule edge source rest) = length rest + length (C.source_edges source) + 1.
Proof. intros. unfold C.schedule. rewrite app_length, map_length. cbn. lia. Qed.

Theorem enter_preserves_derived_frame_bound : forall roots nodes edges edge source rest,
  length (C.Enter edge :: rest) <= roots + nodes + edges ->
  length (C.schedule edge source rest) <=
    roots + (nodes + 1) + (edges + length (C.source_edges source)).
Proof. intros. rewrite existing_enter_frame_count. cbn in H. lia. Qed.

Theorem pop_preserves_derived_frame_bound : forall roots nodes edges frame rest,
  length (frame :: rest : list C.Frame) <= roots + nodes + edges ->
  length rest <= roots + nodes + edges.
Proof. intros. cbn in H. lia. Qed.

Theorem initial_frames_equal_root_roster : forall roots,
  length (C.work (C.initial roots)) = length roots.
Proof. intros. cbn. apply map_length. Qed.

(** The callback checks these actual occupancies; the theorem does not infer
    HashMap capacity from length. New class allocation occurs only for Name. *)
Theorem admitted_occupancies_remain_node_bounded : forall n cap memo store classes,
  n <= cap -> memo <= n -> store <= n -> classes <= n ->
  memo <= cap /\ store <= cap /\ classes <= cap.
Proof. intros; lia. Qed.

(** Finish keeps B bytes by moving strings. At worst old and remapped field
    storage coexist: each is bounded by admitted logical content. Root input
    and returned roots likewise coexist. No second charge is performed. *)
Theorem temporary_and_retained_slots_have_constant_factor_bound :
  forall q old mapped, old <= q -> mapped <= q -> old + mapped <= 2 * q.
Proof. intros; lia. Qed.

Theorem root_rosters_have_constant_factor_bound :
  forall r input output, input <= r -> output <= r -> input + output <= 2 * r.
Proof. intros; lia. Qed.

Theorem checked_frame_ceiling_is_not_an_independent_cap : forall word r n e bound,
  checked_total word [r; n; e] = Some bound -> bound = r + n + e /\ bound <= word.
Proof.
  intros. apply checked_total_exact_and_bounded in H. cbn in H. lia.
Qed.

Print Assumptions checked_total_exact_and_bounded.
Print Assumptions checked_total_accepts_exactly_fitting_components.
Print Assumptions exposing_original_helper_changes_no_branch_or_counter.
Print Assumptions string_success_has_exact_size.
Print Assumptions individual_refusal_keeps_counter.
Print Assumptions total_refusal_retains_original_assignment.
Print Assumptions refused_string_has_no_copied_result.
Print Assumptions admitted_sizes_are_bounded.
Print Assumptions admitted_root_roster_is_bounded.
Print Assumptions first_observation_bounds_new_content.
Print Assumptions existing_enter_frame_count.
Print Assumptions enter_preserves_derived_frame_bound.
Print Assumptions pop_preserves_derived_frame_bound.
Print Assumptions initial_frames_equal_root_roster.
Print Assumptions admitted_occupancies_remain_node_bounded.
Print Assumptions temporary_and_retained_slots_have_constant_factor_bound.
Print Assumptions root_rosters_have_constant_factor_bound.
Print Assumptions checked_frame_ceiling_is_not_an_independent_cap.

End AuthoredRuntimeCaptureAdmission.
