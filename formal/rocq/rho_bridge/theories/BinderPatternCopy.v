(** Ordered, resource-admitted copying of the two generated scope patterns.

    Source: moniker-0.5.0 Binder<String> is a transparent FreeVar wrapper.
    Its BoundPattern open/close methods do nothing. Vec delegates in order
    to its elements, so neither operation freshens these patterns. Identity
    and optional diagnostic names must both survive, including duplicates.

    Reuse KnownRosterLeaves.FreeName and the existing flat name-copy charge.
    A Binder adds two NativeWork events (wrapper construction and flat
    teardown), but no storage record beyond its in-place FreeVar. A Vec adds
    header construction/cleanup and one record. Each entry adds two work
    events for copy-loop insertion and cleanup-loop dispatch. Allocating its
    capacity first requires admitting all entry records first; name work and
    bytes remain cancellable per entry. The equations below show that moving
    those records earlier neither omits nor duplicates an entry record.

    These are logical construction/normal-cleanup counts, not allocator
    capacity, wall time, panic recovery, or arbitrary BoundPattern laws.
    Rust correspondence requires a private preadmission path, checked usize
    arithmetic, unchanged input, and no push before that entry's paid copy.
    The prefix invariant describes Vec push order, not list-append execution. *)
From Stdlib Require Import List String Arith Lia.
From RhoBridge Require Import FlatBindingLeafReservation.
Import ListNotations.

Module BinderPatternCopy.
Module K := MonikerLeafOperations.KnownRosterLeaves.
Module F := FlatBindingLeafReservation.

Definition Name := @K.FreeName string.
Definition binder_copy (_operation : K.Operation) (name : Name) := name.
Definition pattern_copy operation (pattern : list Name) :=
  map (binder_copy operation) pattern.

Theorem binder_copy_preserves_identity_and_hint : forall operation name,
  K.name_identity (binder_copy operation name) = K.name_identity name /\
  K.name_pretty (binder_copy operation name) = K.name_pretty name.
Proof. intros; split; reflexivity. Qed.

Theorem pattern_copy_is_exact : forall operation pattern,
  pattern_copy operation pattern = pattern.
Proof.
  intros operation pattern. unfold pattern_copy, binder_copy. apply map_id.
Qed.

Theorem pattern_copy_preserves_positional_lookup : forall operation pattern index,
  nth_error (pattern_copy operation pattern) index = nth_error pattern index.
Proof. intros. now rewrite pattern_copy_is_exact. Qed.

Theorem pattern_copy_preserves_first_identity_lookup : forall operation pattern id,
  K.roster_lookup id (pattern_copy operation pattern) = K.roster_lookup id pattern.
Proof. intros. now rewrite pattern_copy_is_exact. Qed.

(** The positional connector for moniker-0.5.0 Scope::unbind.

    After cloning the source pattern, unbind visits every binder in order,
    replaces its identity with FreeVar::fresh(old.pretty_name.clone()), then
    clones pattern.binders() and opens the body at ScopeState::new() (zero).
    Binder is a transparent wrapper; Vec delegates to ordered slice visits.

    [identities] records the actual fresh-call results in that order. It is
    not an allocator model: the results need not be consecutive, ordered or
    distinct for these positional laws. Original duplicate identities are
    still separate occurrences. Equal lengths is the concrete obligation of
    one fresh call per binder; a short trace is not a completed freshening.

    The adapter below only connects those names to the existing known-roster
    opening theorem. It does not prove global freshness, the concrete Rust
    worker, arbitrary BoundTerm implementations, or freshening resource costs.
    Rust must precharge each actual copy/fresh call and preserve its private
    partial-result cleanup. Existing inherited binding-depth and generated
    reconstruction proofs remain the obligations for the body traversal. *)
Definition freshened_name (identity : nat) (original : Name) : Name :=
  {| K.name_identity := identity; K.name_pretty := K.name_pretty original |}.

Definition freshened_roster (identities : list nat) (pattern : list Name) : list Name :=
  map (fun pair => freshened_name (fst pair) (snd pair)) (combine identities pattern).

Theorem source_pattern_copy_preserves_freshening : forall operation identities pattern,
  freshened_roster identities (pattern_copy operation pattern) =
  freshened_roster identities pattern.
Proof. intros. now rewrite pattern_copy_is_exact. Qed.

Theorem freshened_roster_preserves_ordered_projections : forall identities pattern,
  List.length identities = List.length pattern ->
  List.length (freshened_roster identities pattern) = List.length pattern /\
  map K.name_identity (freshened_roster identities pattern) = identities /\
  map K.name_pretty (freshened_roster identities pattern) = map K.name_pretty pattern.
Proof.
  induction identities as [|identity identities IH]; intros [|name pattern] Hlength;
    cbn in Hlength; try discriminate.
  - repeat split; reflexivity.
  - injection Hlength as Hlength.
    destruct (IH pattern Hlength) as [HL [HI HP]].
    cbn [freshened_roster combine map freshened_name K.name_identity K.name_pretty].
    change (
      S (List.length (freshened_roster identities pattern)) = S (List.length pattern) /\
      identity :: map K.name_identity (freshened_roster identities pattern) =
        identity :: identities /\
      K.name_pretty name :: map K.name_pretty (freshened_roster identities pattern) =
        K.name_pretty name :: map K.name_pretty pattern).
    now rewrite HL, HI, HP.
Qed.

Theorem freshened_roster_preserves_positional_lookup :
  forall identities pattern index identity original,
  nth_error identities index = Some identity ->
  nth_error pattern index = Some original ->
  nth_error (freshened_roster identities pattern) index =
    Some (freshened_name identity original).
Proof.
  induction identities as [|head identities IH]; intros [|name pattern] index identity original HI HP;
    destruct index as [|index]; cbn in HI, HP; try discriminate.
  - inversion HI; inversion HP; subst. reflexivity.
  - cbn [freshened_roster combine map nth_error].
    now apply IH.
Qed.

(** The roster is copied from the fresh pattern, not from the original one.
    Reuse the already exact opening leaf algebra, without a second evaluator. *)
Theorem copied_fresh_roster_open_at_zero_is_exact :
  forall operation maximum identities pattern variable,
  K.checked_operation K.OpenLeaf maximum 0
    (pattern_copy operation (freshened_roster identities pattern)) variable =
  K.reference_open 0 (freshened_roster identities pattern) variable.
Proof.
  intros. rewrite pattern_copy_is_exact. apply K.checked_open_is_exact_reference.
Qed.

(** The checked adapter may borrow the returned fresh roster directly: neither
    the original-pattern copy nor pattern.binders() changes opening semantics.
    Eliminating those pure copies does not eliminate fresh calls or their costs. *)
Theorem direct_fresh_roster_open_omits_only_identity_preserving_copies :
  forall operation maximum identities pattern variable,
  K.checked_operation K.OpenLeaf maximum 0 (freshened_roster identities pattern) variable =
  K.checked_operation K.OpenLeaf maximum 0
    (pattern_copy operation (freshened_roster identities (pattern_copy operation pattern)))
    variable.
Proof. intros. now rewrite !pattern_copy_is_exact. Qed.

Theorem copied_fresh_roster_opens_selected_occurrence :
  forall operation maximum identities pattern index identity original old_pretty,
  nth_error identities index = Some identity ->
  nth_error pattern index = Some original ->
  K.checked_operation K.OpenLeaf maximum 0
    (pattern_copy operation (freshened_roster identities pattern))
    (K.Bound 0 index old_pretty) = Some (K.Free (freshened_name identity original)).
Proof.
  intros operation maximum identities pattern index identity original old_pretty HI HP.
  rewrite pattern_copy_is_exact.
  apply K.matching_depth_open_selects_roster_identity_and_pretty.
  now apply freshened_roster_preserves_positional_lookup.
Qed.

(** Repeated original identities do not collapse, and the supplied fresh-call
    sequence need not be numerically increasing. Hints stay with positions. *)
Example repeated_original_identity_retains_both_fresh_positions :
  let first := {| K.name_identity := 9; K.name_pretty := Some "first"%string |} in
  let second := {| K.name_identity := 9; K.name_pretty := None |} in
  freshened_roster [21; 7] [first; second] =
    [freshened_name 21 first; freshened_name 7 second].
Proof. reflexivity. Qed.

(** Prefixes include all occurrences, not only distinct binder identities. *)
Definition prefix_invariant (source done pending : list Name) :=
  done ++ pending = source.

Theorem initial_prefix : forall source, prefix_invariant source [] source.
Proof. reflexivity. Qed.

Theorem paid_push_preserves_prefix : forall source done name rest,
  prefix_invariant source done (name :: rest) ->
  prefix_invariant source (done ++ [name]) rest.
Proof.
  intros source done name rest H. unfold prefix_invariant in *.
  rewrite <- app_assoc. exact H.
Qed.

Theorem refused_copy_retains_exact_prefix : forall source done pending,
  prefix_invariant source done pending ->
  done = firstn (List.length done) source.
Proof.
  intros source done pending H. unfold prefix_invariant in H. subst source.
  rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. now rewrite app_nil_r.
Qed.

Theorem completed_prefix_is_exact_source : forall source done,
  prefix_invariant source done [] -> done = source.
Proof. intros source done H. unfold prefix_invariant in H. now rewrite app_nil_r in H. Qed.

Definition name_work (name : Name) := F.name_copy_work (K.name_pretty name).
Definition name_bytes (name : Name) :=
  FltSelectorBinding.SelectorPayloadComposition.optional_bytes (K.name_pretty name).
Definition binder_work name := 2 + name_work name.
Definition entry_work name := 2 + binder_work name.
Definition copied_work pattern :=
  2 + fold_right (fun name rest => entry_work name + rest) 0 pattern.
Definition copied_records (pattern : list Name) := 1 + List.length pattern.
Definition copied_bytes pattern :=
  fold_right (fun name rest => name_bytes name + rest) 0 pattern.

(** reserve_binding_parts converts records/bytes to retention units exactly
    as in the existing leaf interface. The vector prefix admits only record
    storage; each residual name copy still pays its bytes and all its work. *)
Definition ordinary_entry_units name := 4 + name_bytes name.
Definition residual_entry_units name := name_bytes name.
Definition upfront_units pattern := 4 * copied_records pattern.
Definition staged_units pattern := upfront_units pattern +
  fold_right (fun name rest => residual_entry_units name + rest) 0 pattern.
Definition unstaged_units pattern := 4 +
  fold_right (fun name rest => ordinary_entry_units name + rest) 0 pattern.

Lemma entry_records_paid_exactly_once : forall pattern,
  fold_right (fun name rest => ordinary_entry_units name + rest) 0 pattern =
  4 * List.length pattern + copied_bytes pattern.
Proof.
  intro pattern. unfold ordinary_entry_units, copied_bytes.
  induction pattern as [|name rest IH]; cbn [fold_right List.length];
    [lia|rewrite IH; lia].
Qed.

Theorem preallocation_moves_but_does_not_duplicate_records : forall pattern,
  staged_units pattern = unstaged_units pattern.
Proof.
  intro pattern. unfold staged_units, unstaged_units, upfront_units,
    copied_records, residual_entry_units.
  rewrite entry_records_paid_exactly_once. unfold copied_bytes. lia.
Qed.

Theorem staged_units_are_records_plus_owned_bytes : forall pattern,
  staged_units pattern = 4 * copied_records pattern + copied_bytes pattern.
Proof. reflexivity. Qed.

Theorem empty_pattern_still_pays_header :
  copied_work [] = 2 /\ copied_records [] = 1 /\ copied_bytes [] = 0 /\
  staged_units [] = 4.
Proof. repeat split; reflexivity. Qed.

Theorem copied_name_work_includes_owned_hint_cleanup : forall identity text,
  binder_work {| K.name_identity := identity; K.name_pretty := Some text |} =
    4 + String.length text.
Proof. reflexivity. Qed.

(** Full original-pattern allowance dominates cleanup of every produced
    prefix. No result is pushed before its name-copy callback succeeds. *)
Theorem copied_prefix_work_is_bounded : forall done pending,
  copied_work done <= copied_work (done ++ pending).
Proof.
  intros done pending. unfold copied_work.
  induction done as [|name rest IH]; cbn [fold_right app] in *; lia.
Qed.

Theorem copied_prefix_records_are_bounded : forall done pending,
  copied_records done <= copied_records (done ++ pending).
Proof. intros. unfold copied_records. rewrite length_app. lia. Qed.

Theorem copied_prefix_bytes_are_bounded : forall done pending,
  copied_bytes done <= copied_bytes (done ++ pending).
Proof.
  intros done pending. unfold copied_bytes.
  induction done as [|name rest IH]; cbn [fold_right app] in *; lia.
Qed.

Print Assumptions binder_copy_preserves_identity_and_hint.
Print Assumptions pattern_copy_is_exact.
Print Assumptions pattern_copy_preserves_positional_lookup.
Print Assumptions pattern_copy_preserves_first_identity_lookup.
Print Assumptions source_pattern_copy_preserves_freshening.
Print Assumptions freshened_roster_preserves_ordered_projections.
Print Assumptions freshened_roster_preserves_positional_lookup.
Print Assumptions copied_fresh_roster_open_at_zero_is_exact.
Print Assumptions direct_fresh_roster_open_omits_only_identity_preserving_copies.
Print Assumptions copied_fresh_roster_opens_selected_occurrence.
Print Assumptions repeated_original_identity_retains_both_fresh_positions.
Print Assumptions initial_prefix.
Print Assumptions paid_push_preserves_prefix.
Print Assumptions refused_copy_retains_exact_prefix.
Print Assumptions completed_prefix_is_exact_source.
Print Assumptions entry_records_paid_exactly_once.
Print Assumptions preallocation_moves_but_does_not_duplicate_records.
Print Assumptions staged_units_are_records_plus_owned_bytes.
Print Assumptions empty_pattern_still_pays_header.
Print Assumptions copied_name_work_includes_owned_hint_cleanup.
Print Assumptions copied_prefix_work_is_bounded.
Print Assumptions copied_prefix_records_are_bounded.
Print Assumptions copied_prefix_bytes_are_bounded.
End BinderPatternCopy.
