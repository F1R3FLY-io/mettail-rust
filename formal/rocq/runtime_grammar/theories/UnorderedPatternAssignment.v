(** Finite unordered pattern assignment contract.

    Each row lists the ground occurrences compatible with one pattern
    occurrence. Occurrences, rather than distinct values, are essential for
    bags: two copies of the same value still need two distinct witnesses.

    This model specifies the existential [Option<MatchBindings>] contract of
    the generated first-order matcher. It does not enumerate all substitution
    environments, and it makes no claim about parser-forest ambiguity. The
    Rust augmenting-path search is checked against this exhaustive finite
    oracle by property tests. *)
From Stdlib Require Import List Arith.PeanoNat Lia.
Import ListNotations.

Module UnorderedPatternAssignment.

Inductive valid : list (list nat) -> list nat -> Prop :=
| valid_nil : valid [] []
| valid_cons : forall row rows ground rest,
    In ground row ->
    valid rows rest ->
    ~ In ground rest ->
    valid (row :: rows) (ground :: rest).

Definition unclaimed (ground : nat) (rest : list nat) : bool :=
  if in_dec Nat.eq_dec ground rest then false else true.

Fixpoint enumerate (rows : list (list nat)) : list (list nat) :=
  match rows with
  | [] => [[]]
  | row :: rest =>
      flat_map
        (fun ground =>
           map (cons ground)
             (filter (unclaimed ground) (enumerate rest)))
        row
  end.

Lemma unclaimed_exact : forall ground rest,
  unclaimed ground rest = true <-> ~ In ground rest.
Proof.
  intros ground rest; unfold unclaimed.
  destruct (in_dec Nat.eq_dec ground rest) as [present | absent].
  - split; intro H; [discriminate | contradiction].
  - split; intro H; [exact absent | reflexivity].
Qed.

Lemma enumerate_cons_exact : forall row rows ground rest,
  In (ground :: rest) (enumerate (row :: rows)) <->
  In ground row /\ In rest (enumerate rows) /\ ~ In ground rest.
Proof.
  intros row rows ground rest; simpl.
  rewrite in_flat_map.
  split.
  - intros [candidate [in_row in_image]].
    apply in_map_iff in in_image.
    destruct in_image as [tail [equal in_filter]].
    inversion equal; subst candidate tail.
    apply filter_In in in_filter as [in_enum free].
    split; [exact in_row |].
    split; [exact in_enum |].
    apply unclaimed_exact; exact free.
  - intros [in_row [in_enum free]].
    exists ground; split; [exact in_row |].
    apply in_map_iff.
    exists rest; split; [reflexivity |].
    apply filter_In; split; [exact in_enum |].
    apply unclaimed_exact; exact free.
Qed.

Theorem enumeration_is_sound : forall rows assignment,
  In assignment (enumerate rows) -> valid rows assignment.
Proof.
  induction rows as [|row rows IH]; intros assignment found.
  - simpl in found. destruct found as [equal | impossible].
    + subst assignment; constructor.
    + contradiction.
  - destruct assignment as [|ground rest].
    + apply in_flat_map in found.
      destruct found as [candidate [_ image]].
      apply in_map_iff in image.
      destruct image as [tail [equal _]].
      discriminate.
    + apply enumerate_cons_exact in found as [in_row [in_enum free]].
      constructor; [exact in_row | apply IH; exact in_enum | exact free].
Qed.

Theorem enumeration_is_complete : forall rows assignment,
  valid rows assignment -> In assignment (enumerate rows).
Proof.
  intros rows assignment established.
  induction established as
    [|row rows ground rest in_row tail_valid IH free].
  - simpl; left; reflexivity.
  - apply enumerate_cons_exact; repeat split; assumption.
Qed.

Theorem success_iff_a_complete_assignment_exists : forall rows,
  (exists assignment, In assignment (enumerate rows)) <->
  (exists assignment, valid rows assignment).
Proof.
  intro rows; split; intros [assignment witness];
    exists assignment.
  - apply enumeration_is_sound; exact witness.
  - apply enumeration_is_complete; exact witness.
Qed.

(** The generated [Option<MatchBindings>] interface needs only an existential
    witness. The pre-existing runtime enumerator has the stronger all-witness
    contract and therefore serves as the finite property-test oracle; the
    implementation may instead find one witness by augmenting paths. *)
Definition first_witness (rows : list (list nat)) : option (list nat) :=
  hd_error (enumerate rows).

Theorem first_witness_is_sound : forall rows assignment,
  first_witness rows = Some assignment -> valid rows assignment.
Proof.
  intros rows assignment found.
  apply enumeration_is_sound.
  unfold first_witness in found.
  destruct (enumerate rows) as [|head tail] eqn:all; simpl in found.
  - discriminate.
  - inversion found; subst assignment; simpl; left; reflexivity.
Qed.

Theorem first_witness_is_complete_for_existence : forall rows,
  (exists assignment, valid rows assignment) <->
  (exists assignment, first_witness rows = Some assignment).
Proof.
  intro rows; split.
  - intros [assignment valid_assignment].
    apply enumeration_is_complete in valid_assignment.
    unfold first_witness.
    destruct (enumerate rows) as [|head tail] eqn:all.
    + contradiction.
    + exists head; reflexivity.
  - intros [assignment found]; exists assignment.
    apply first_witness_is_sound with (rows := rows); exact found.
Qed.

(** The implementation's alternating-path BFS marks each pattern vertex and
    each ground vertex at most once per root. The scan of one pattern vertex
    is a bounded [0,n) loop. The following natural-number measure therefore
    bounds all newly discovered vertices by [2*n]; it does not rely on the
    host call stack. The outer root loop itself has exactly [n] iterations. *)
Definition undiscovered (n seen_pattern seen_ground : nat) : nat :=
  2 * n - (seen_pattern + seen_ground).

Theorem discovering_one_fresh_vertex_decreases_measure :
  forall n seen_pattern seen_ground,
    seen_pattern + seen_ground < 2 * n ->
    undiscovered n (S seen_pattern) seen_ground <
      undiscovered n seen_pattern seen_ground /\
    undiscovered n seen_pattern (S seen_ground) <
      undiscovered n seen_pattern seen_ground.
Proof.
  intros n seen_pattern seen_ground room.
  unfold undiscovered; lia.
Qed.

(** Predecessors are written only when a ground vertex is first seen, and a
    matched owner is enqueued only when a pattern vertex is first seen. The
    replay chain therefore has no repeated pattern vertex and cannot exceed
    the collection cardinality. *)
Theorem alternating_replay_has_bounded_length : forall n path,
  NoDup path ->
  (forall pattern, In pattern path -> pattern < n) ->
  length path <= n.
Proof.
  intros n path distinct bounded.
  replace n with (length (seq 0 n)) by apply length_seq.
  apply NoDup_incl_length; [exact distinct |].
  intros pattern present.
  apply in_seq; split; [lia | apply bounded; exact present].
Qed.

(** Without an edge cache, pair compatibility may be reevaluated by different
    root searches. There are at most [n] roots, at most [n] popped patterns
    per root, and at most [n] pair checks per popped pattern. These counters
    are the loop-bound invariant checked by the Rust property test. *)
Theorem uncached_pair_evaluations_have_cubic_bound :
  forall n roots popped_patterns evaluations,
    roots <= n ->
    popped_patterns <= roots * n ->
    evaluations <= popped_patterns * n ->
    evaluations <= n * (n * n).
Proof. intros; nia. Qed.

(** Runtime correspondence for the augmenting search:

    Rocq notion                    Rust [first_perfect_matching] state
    ---------------------------------------------------------------
    root                           loop variable [root]
    seen_patterns                  [seen_pattern] flags
    seen_grounds                   [seen_ground] flags
    owner                           [pattern_for_ground]
    compatible edge                [compatible] predicate result on scan
    alternating predecessor        [predecessor] per-ground array

    The exhausted scan establishes edge closure; no compatibility result is
    cached. Debug assertions check ownership away from the root and strict
    frontier cardinality. The final replay in the generated matcher rechecks
    every selected edge before publishing its bindings. *)

(** When the augmenting BFS exhausts its queue, [seen_patterns] is closed
    under compatibility edges into [seen_grounds]. Every seen ground is owned
    by a distinct seen pattern other than the unmatched root. Hence the seen
    patterns have strictly more members than their entire neighborhood. Any
    perfect assignment would inject them into that neighborhood, an
    impossibility. These are precisely the failure-certificate invariants
    maintained by the Rust queue, owner arrays, and [seen_*] flags. *)
Lemma injective_image_is_nodup : forall (xs : list nat) (f : nat -> nat),
  NoDup xs ->
  (forall x y, In x xs -> In y xs -> f x = f y -> x = y) ->
  NoDup (map f xs).
Proof.
  induction xs as [|x xs IH]; intros f distinct injective.
  - simpl; constructor.
  - inversion distinct as [|? ? fresh tail_distinct]; subst.
    simpl; constructor.
    + intro in_image.
      apply in_map_iff in in_image.
      destruct in_image as [y [equal in_tail]].
      apply fresh.
      assert (x = y) as same by
        (apply injective; simpl; auto; symmetry; exact equal).
      subst y; exact in_tail.
    + apply IH; [exact tail_distinct |].
      intros a b in_a in_b equal.
      apply injective; simpl; auto.
Qed.

Theorem exhausted_augmenting_frontier_excludes_perfect_assignment :
  forall n (edge : nat -> nat -> Prop) owner root
         (seen_patterns seen_grounds : list nat) pick,
    NoDup seen_patterns ->
    NoDup seen_grounds ->
    In root seen_patterns ->
    (forall ground, In ground seen_grounds ->
       In (owner ground) seen_patterns /\ owner ground <> root) ->
    (forall left right,
       In left seen_grounds -> In right seen_grounds ->
       owner left = owner right -> left = right) ->
    (forall pattern, In pattern seen_patterns -> pattern < n) ->
    (forall pattern ground,
       In pattern seen_patterns -> pattern < n ->
       edge pattern ground -> ground < n ->
       In ground seen_grounds) ->
    (forall pattern, pattern < n ->
       pick pattern < n /\ edge pattern (pick pattern)) ->
    (forall left right, left < n -> right < n ->
       pick left = pick right -> left = right) ->
    False.
Proof.
  intros n edge owner root seen_patterns seen_grounds pick
    patterns_distinct grounds_distinct root_seen owner_seen owner_unique
    patterns_bounded edges_closed pick_compatible pick_unique.
  assert (NoDup (map owner seen_grounds)) as owners_distinct.
  { apply injective_image_is_nodup; assumption. }
  assert (NoDup (root :: map owner seen_grounds)) as owners_plus_root_distinct.
  { constructor.
    - intro root_in_owners.
      apply in_map_iff in root_in_owners.
      destruct root_in_owners as [ground [same present]].
      specialize (owner_seen ground present) as [_ not_root].
      contradiction.
    - exact owners_distinct. }
  assert (incl (root :: map owner seen_grounds) seen_patterns) as owners_seen.
  { intros pattern present.
    simpl in present; destruct present as [same | present].
    - subst pattern; exact root_seen.
    - apply in_map_iff in present.
      destruct present as [ground [same in_ground]].
      subst pattern; apply (proj1 (owner_seen ground in_ground)). }
  assert (S (length seen_grounds) <= length seen_patterns) as deficit.
  { replace (S (length seen_grounds)) with
      (length (root :: map owner seen_grounds))
      by (simpl; rewrite length_map; reflexivity).
    apply NoDup_incl_length; assumption. }
  assert (NoDup (map pick seen_patterns)) as picked_distinct.
  { apply injective_image_is_nodup; [exact patterns_distinct |].
    intros left right in_left in_right equal.
    apply pick_unique; [apply patterns_bounded; exact in_left |
      apply patterns_bounded; exact in_right | exact equal]. }
  assert (incl (map pick seen_patterns) seen_grounds) as picks_in_neighborhood.
  { intros ground present.
    apply in_map_iff in present.
    destruct present as [pattern [same in_pattern]].
    subst ground.
    pose proof (patterns_bounded pattern in_pattern) as bounded.
    destruct (pick_compatible pattern bounded) as [ground_bounded compatible].
    apply (edges_closed pattern (pick pattern)); assumption. }
  assert (length seen_patterns <= length seen_grounds) as perfect_needs_room.
  { rewrite <- length_map with (f := pick) (l := seen_patterns).
    apply NoDup_incl_length; assumption. }
  lia.
Qed.

(** The minimal false rejection of first-claim greedy matching: pattern 0
    accepts either occurrence, while pattern 1 accepts only occurrence 0.
    The valid assignment is [1; 0]. *)
Example greedy_first_claim_is_incomplete :
  valid [[0; 1]; [0]] [1; 0] /\
  In [1; 0] (enumerate [[0; 1]; [0]]).
Proof.
  split.
  - repeat constructor; simpl; intuition congruence.
  - simpl; intuition congruence.
Qed.

(** Two occurrences of one Rholang formula variable lower to two independent
    Wildcards. The rows may be identical, but the ground occurrences must be
    distinct. This is intentionally not GSLT rewrite-variable unification. *)
Example repeated_formula_wildcards_remain_occurrence_wise :
  valid [[0; 1]; [0; 1]] [0; 1].
Proof. repeat constructor; simpl; intuition congruence. Qed.

Print Assumptions success_iff_a_complete_assignment_exists.
Print Assumptions first_witness_is_complete_for_existence.
Print Assumptions discovering_one_fresh_vertex_decreases_measure.
Print Assumptions alternating_replay_has_bounded_length.
Print Assumptions uncached_pair_evaluations_have_cubic_bound.
Print Assumptions exhausted_augmenting_frontier_excludes_perfect_assignment.
Print Assumptions greedy_first_claim_is_incomplete.
Print Assumptions repeated_formula_wildcards_remain_occurrence_wise.

End UnorderedPatternAssignment.
