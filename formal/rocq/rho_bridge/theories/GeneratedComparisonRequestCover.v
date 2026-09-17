(** Compose original directed request membership with an existing count bound.

    Lists are proof-only occurrence inventories, not another runtime traversal.
    The shared row/column cursor enumerates their Cartesian product without
    allocating it. Repeated values and pointer aliases remain repeated list
    occurrences; neither decidable equality nor comparator coherence is used.

    A cost is an already-justified nonnegative callback allowance. These laws
    do not provide that allowance, prove a source request bound, or equate
    metadata inspection with admission. The source supplies original operand
    membership through existing copy/permutation laws. Primary and secondary
    costs remain distinct; charging both permits a native primary verdict to
    omit its secondary call without inventing an Equal response.

    The lex corollary uses the existing actual request annotation and its
    compressed-roster width bound. Sort instantiations use the independently
    established request count and original-copy/source association, not a new
    sorter or a callback-list replay. Machine arithmetic and typed original
    pointer lifetime remain checked Rust obligations. *)
From Stdlib Require Import List Arith.PeanoNat Lia Sorting.Permutation.
From RhoBridge Require Import NativeCollectionRequestBound.
Import ListNotations.

Module GeneratedComparisonRequestCover.
Module N := NativeCollectionRequestBound.NativeCollectionRequestBound.
Module L := CollectionPairAndUnitLexResults.CollectionPairAndUnitLexResults.

Definition cost_sum {A : Type} (cost : A -> nat) (items : list A) :=
  fold_right (fun item total => cost item + total) 0 items.

Lemma original_member_cost_is_bounded_by_sum : forall A (cost : A -> nat) items item,
  In item items -> cost item <= cost_sum cost items.
Proof.
  intros A cost items. induction items as [|head rest IH]; intros item MEMBER.
  - contradiction.
  - destruct MEMBER as [SAME|MEMBER].
    + subst item. change (cost head <= cost head + cost_sum cost rest). lia.
    + specialize (IH item MEMBER).
      change (cost item <= cost head + cost_sum cost rest). lia.
Qed.

Lemma original_members_cover_each_request : forall A (cost : A -> nat) original requests,
  Forall (fun request => In request original) requests ->
  cost_sum cost requests <= length requests * cost_sum cost original.
Proof.
  intros A cost original requests MEMBERS.
  induction MEMBERS as [|request rest MEMBER MEMBERS IH].
  - change (0 <= 0). reflexivity.
  - pose proof (original_member_cost_is_bounded_by_sum A cost original request MEMBER) as HEAD.
    change (cost request + cost_sum cost rest <= S (length rest) * cost_sum cost original).
    nia.
Qed.

Theorem request_count_times_original_sum_covers_actual_cost :
  forall A (cost : A -> nat) original requests bound,
  Forall (fun request => In request original) requests ->
  length requests <= bound ->
  cost_sum cost requests <= bound * cost_sum cost original.
Proof.
  intros A cost original requests bound MEMBERS COUNT.
  pose proof (original_members_cover_each_request A cost original requests MEMBERS).
  nia.
Qed.

Theorem directed_product_covers_both_callback_roles :
  forall A B (primary secondary : A * B -> nat) left right requests bound,
  Forall (fun request => In (fst request) left /\ In (snd request) right) requests ->
  length requests <= bound ->
  cost_sum primary requests + cost_sum secondary requests <=
    bound * (cost_sum primary (list_prod left right) +
      cost_sum secondary (list_prod left right)).
Proof.
  intros A B primary secondary left right requests bound MEMBERS COUNT.
  assert (PRODUCT : Forall (fun request => In request (list_prod left right)) requests).
  { apply Forall_forall. intros [lhs rhs] MEMBER.
    apply in_prod_iff. rewrite Forall_forall in MEMBERS.
    exact (MEMBERS (lhs, rhs) MEMBER). }
  pose proof (request_count_times_original_sum_covers_actual_cost
    (A * B)%type primary _ _ _ PRODUCT COUNT) as PRIMARY.
  pose proof (request_count_times_original_sum_covers_actual_cost
    (A * B)%type secondary _ _ _ PRODUCT COUNT) as SECONDARY.
  nia.
Qed.

Theorem reordered_product_membership_returns_to_original_occurrences :
  forall A B (left reordered_left : list A) (right reordered_right : list B) requests,
  Permutation reordered_left left -> Permutation reordered_right right ->
  Forall (fun request => In request (list_prod reordered_left reordered_right)) requests ->
  Forall (fun request => In request (list_prod left right)) requests.
Proof.
  intros A B left reordered_left right reordered_right requests LEFT RIGHT MEMBERS.
  apply Forall_forall. intros [lhs rhs] MEMBER.
  rewrite Forall_forall in MEMBERS. specialize (MEMBERS (lhs, rhs) MEMBER).
  apply in_prod_iff in MEMBERS. destruct MEMBERS as [LM RM].
  apply in_prod_iff. split; eapply Permutation_in; eassumption.
Qed.

Theorem original_compressed_lex_rosters_cover_both_callback_roles :
  forall Entry (compare : Entry -> Entry -> comparison)
    (primary secondary : Entry * Entry -> nat)
    left right sorted_left sorted_right requests,
  Permutation sorted_left left -> Permutation sorted_right right ->
  N.LexRequests compare sorted_left sorted_right (L.unit_cursor 0) requests ->
  cost_sum primary requests + cost_sum secondary requests <=
    (length left + length right) *
      (cost_sum primary (list_prod (map fst left) (map fst right)) +
       cost_sum secondary (list_prod (map fst left) (map fst right))).
Proof.
  intros Entry compare primary secondary left right sorted_left sorted_right requests
    LEFT RIGHT RUN.
  apply directed_product_covers_both_callback_roles.
  - apply Forall_forall. intros [lhs rhs] MEMBER.
    destruct (N.every_lex_request_retains_original_operands
      compare _ _ _ _ RUN lhs rhs MEMBER) as [[lc LM] [rc RM]].
    split; apply in_map_iff.
    + exists (lhs, lc). split; [reflexivity|]. eapply Permutation_in; eassumption.
    + exists (rhs, rc). split; [reflexivity|]. eapply Permutation_in; eassumption.
  - pose proof (N.initial_weighted_lex_requests_do_not_expand_multiplicities
      compare _ _ _ RUN) as COUNT.
    pose proof (Permutation_length LEFT).
    pose proof (Permutation_length RIGHT). lia.
Qed.

Print Assumptions original_member_cost_is_bounded_by_sum.
Print Assumptions original_members_cover_each_request.
Print Assumptions request_count_times_original_sum_covers_actual_cost.
Print Assumptions directed_product_covers_both_callback_roles.
Print Assumptions reordered_product_membership_returns_to_original_occurrences.
Print Assumptions original_compressed_lex_rosters_cover_both_callback_roles.
End GeneratedComparisonRequestCover.
