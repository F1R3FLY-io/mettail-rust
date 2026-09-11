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
