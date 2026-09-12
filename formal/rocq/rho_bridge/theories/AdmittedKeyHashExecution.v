(** First shared ordinary/admitted hash-emission contract.

    Source: macros/src/gen/term_ops/iterative_hash.rs already has category
    tasks, AbsorbU8/AbsorbUsize, and type-erased native Hash callbacks using
    the ORIGINAL generic Hasher. Its eager leaves and deferred native tasks
    must share the same native operation when admission is added.

    The inspected Rust toolchain's core/src/hash/mod.rs maps i64 to write_i64,
    bool/u8 to write_u8, and usize to write_usize. alloc/src/string.rs delegates
    String to str, whose Hash calls write_str. Do not replace that generic
    write_str call by a byte buffer or its default bytes-plus-255 expansion:
    a Hasher can override the method. Byte strings below denote the existing
    UTF-8 bytes; they do not request validation or copying.

    This first concrete leaf schedule covers i64, bool, u8/usize tags and
    String. One inspection work event precedes projecting a leaf's native
    call and dynamic byte extent. One native-dispatch event and an explicit
    supported-hasher receipt precede invoking that call. A borrowed String
    byte extent contributes NO OwnedByte retention. Arbitrary H: Hasher work
    is not bounded by call count or byte length: the supported-hasher trace
    contract below is an explicit, separate premise.

    Each source-only task push reserves two NativeWork events (construction/
    push and possible pending disposal) and one NativeRecord before the push.
    A pop reserves one NativeWork before removal. Range routing/advances and
    pointer extraction are separate admitted NativeWork actions. The modeled
    lists are traces of the existing emitter's operations, not a proposal for
    another Rust engine, buffer of hash bytes, or runtime plan allocation.

    Successful leaf admission erases to the same native call for ANY hasher
    state transition, without replacing its state. Local refusal happens before
    its action; no theorem rolls back earlier hasher writes. Task push/disposal
    projections are local facts; the shared-emitter trace composition follows
    in a separate increment.
    Concrete vector headers/growth, TLS lifecycle, machine-word arithmetic,
    source-pointer lifetime and routing-to-command correspondence still need
    their actual emission-site contracts.

    Required next leaves: OrdVar/moniker identity hashing, binder vectors,
    and full derived FltNode payload hashing. Other native carriers remain
    outside this first demo increment. FltNode hashes diagnostic Strings,
    hole/piece vectors and ranges;
    a copy receipt or trusted bounds field is not a hash receipt. This model
    claims neither those leaves nor Eq/Ord, HashBag key admission, or complete
    bounded Rholang activation. The final section supplies the concrete
    fixed/String Fx2.1.3 source-group envelope for the audited x86_64 profile;
    it is not a claim about arbitrary hashers or machine instruction counts. *)
From Stdlib Require Import List Arith Bool Lia ZArith.
From RhoBridge Require Import GeneratedDummyCleanupReservation
  GeneratedBindingOutputReservation RholangInitialGraphResources
  ScalarArcBindingReservation RequiredVecBindingReservation.
Import ListNotations.

Module AdmittedKeyHashExecution.
Module D := GeneratedDummyCleanupReservation.
Module O := GeneratedBindingOutputReservation.
Module S := ScalarArcBindingReservation.
Module V := RequiredVecBindingReservation.

(** Values denote already-valid Rust payloads. Range/UTF-8 validity is supplied
    by the Rust type; no new validation or machine integer representation is
    inferred from these mathematical labels. *)
Inductive Leaf :=
| Integer64 (value : Z)
| Boolean (value : bool)
| Tag8 (value : nat)
| TagWord (value : nat)
| Text (bytes : list nat).

Inductive NativeCall :=
| WriteI64 (value : Z)
| WriteU8 (value : nat)
| WriteUsize (value : nat)
| WriteStr (bytes : list nat).

Definition ordinary_leaf_call (leaf : Leaf) : NativeCall :=
  match leaf with
  | Integer64 value => WriteI64 value
  | Boolean value => WriteU8 (if value then 1 else 0)
  | Tag8 value => WriteU8 value
  | TagWord value => WriteUsize value
  | Text bytes => WriteStr bytes
  end.

Definition dynamic_byte_extent (leaf : Leaf) : nat :=
  match leaf with Text bytes => length bytes | _ => 0 end.

Record InspectedLeaf := {
  inspected_call : NativeCall;
  inspected_bytes : nat
}.
Definition inspect_leaf (leaf : Leaf) : InspectedLeaf :=
  {| inspected_call := ordinary_leaf_call leaf;
     inspected_bytes := dynamic_byte_extent leaf |}.

Theorem fixed_native_calls_are_exact : forall integer boolean byte word,
  ordinary_leaf_call (Integer64 integer) = WriteI64 integer /\
  ordinary_leaf_call (Boolean boolean) = WriteU8 (if boolean then 1 else 0) /\
  ordinary_leaf_call (Tag8 byte) = WriteU8 byte /\
  ordinary_leaf_call (TagWord word) = WriteUsize word.
Proof. repeat split; reflexivity. Qed.

Theorem string_inspection_preserves_native_call_and_byte_extent : forall bytes,
  inspected_call (inspect_leaf (Text bytes)) = WriteStr bytes /\
  inspected_bytes (inspect_leaf (Text bytes)) = length bytes.
Proof. split; reflexivity. Qed.

Definition inspection_counts : D.Counts := D.atom D.NativeWork.
Definition pop_counts : D.Counts := D.atom D.NativeWork.
Definition push_range_counts width : D.Counts := fun event =>
  (2 * width) * D.atom D.NativeWork event + width * D.atom D.NativeRecord event.
Definition routing_counts advances extractions : D.Counts := fun event =>
  (advances + extractions) * D.atom D.NativeWork event.
Definition pending_disposal_counts width : D.Counts := fun event =>
  width * D.atom D.NativeWork event.

(** Reuse Counts and the existing two-dimensional precharged_action. *)
Definition paid_counts {A} cancelled available (counts : D.Counts)
    (action : unit -> option A) :=
  precharged_action cancelled available
    (D.weighted D.logical_work_weight counts)
    (D.weighted D.logical_unit_weight counts) action.

Theorem successful_paid_counts_reuses_same_action :
  forall A cancelled available counts (action : unit -> option A) paid value,
  paid_counts cancelled available counts action = Accepted paid value ->
  action tt = Some value.
Proof.
  intros A cancelled available counts action paid value H.
  apply successful_action_constructs_only_the_paid_result in H. tauto.
Qed.

Theorem refused_counts_precede_action : forall A available counts
    (action : unit -> option A),
  reserve available (D.weighted D.logical_work_weight counts)
    (D.weighted D.logical_unit_weight counts) = None ->
  paid_counts false available counts action = Refused available.
Proof. intros. now apply failed_precharge_is_independent_of_constructor. Qed.

Theorem cancelled_counts_precede_action : forall A available counts
    (action : unit -> option A),
  paid_counts true available counts action = Refused available.
Proof. reflexivity. Qed.

Theorem inspection_projection :
  D.weighted D.base_work_weight inspection_counts = 1 /\
  D.weighted D.record_weight inspection_counts = 0 /\
  D.weighted D.byte_weight inspection_counts = 0.
Proof. repeat split; reflexivity. Qed.

Theorem push_range_projection : forall width,
  D.weighted D.base_work_weight (push_range_counts width) = 2 * width /\
  D.weighted D.record_weight (push_range_counts width) = width /\
  D.weighted D.byte_weight (push_range_counts width) = 0.
Proof.
  intro width. unfold push_range_counts.
  rewrite !S.weighted_add, !V.weighted_scale.
  change (2 * width * 1 + width * 0 = 2 * width /\
    2 * width * 0 + width * 1 = width /\
    2 * width * 0 + width * 0 = 0).
  repeat split; lia.
Qed.

Theorem task_push_also_pays_pending_disposal : forall width event,
  pending_disposal_counts width event <= push_range_counts width event.
Proof. intros. unfold pending_disposal_counts, push_range_counts. nia. Qed.

Theorem borrowed_inspection_does_not_retain_bytes : forall leaf,
  inspection_counts D.OwnedByte = 0 /\
  inspected_bytes (inspect_leaf leaf) = dynamic_byte_extent leaf.
Proof. split; reflexivity. Qed.

Definition paid_inspection cancelled available leaf :=
  paid_counts cancelled available inspection_counts (fun _ => Some (inspect_leaf leaf)).

Theorem admitted_inspection_is_exact : forall cancelled available leaf paid inspected,
  paid_inspection cancelled available leaf = Accepted paid inspected ->
  inspected = inspect_leaf leaf.
Proof.
  intros cancelled available leaf paid inspected H.
  apply successful_paid_counts_reuses_same_action in H.
  now inversion H.
Qed.

Section SharedEmission.
Context {HasherState : Type}.
(** Same actual generic hasher operation in ordinary and admitted emission.
    No cost bound, purity of an arbitrary Rust implementation, or byte-level
    serialization equivalence is assumed by the erasure theorem. *)
Variable apply_native : NativeCall -> HasherState -> HasherState.
Variable hasher_receipt : NativeCall -> D.Counts.

Definition execution_counts (inspected : InspectedLeaf) : D.Counts := fun event =>
  D.atom D.NativeWork event + hasher_receipt (inspected_call inspected) event.

Definition paid_leaf cancelled available leaf state :=
  match paid_inspection cancelled available leaf with
  | Refused remaining => Refused remaining
  | Accepted inspected_budget inspected =>
      paid_counts cancelled inspected_budget (execution_counts inspected)
        (fun _ => Some (apply_native (inspected_call inspected) state))
  end.

Theorem successful_leaf_preserves_original_hasher_call :
  forall cancelled available leaf state paid output,
  paid_leaf cancelled available leaf state = Accepted paid output ->
  output = apply_native (ordinary_leaf_call leaf) state.
Proof.
  intros cancelled available leaf state paid output H.
  unfold paid_leaf in H.
  destruct (paid_inspection cancelled available leaf) as [remaining|remaining inspected]
    eqn:HI; [discriminate|].
  apply admitted_inspection_is_exact in HI. subst inspected.
  apply successful_paid_counts_reuses_same_action in H.
  now inversion H.
Qed.

Theorem inspection_refusal_cannot_execute_leaf :
  forall cancelled available leaf state remaining,
  paid_inspection cancelled available leaf = Refused remaining ->
  paid_leaf cancelled available leaf state = Refused remaining.
Proof. intros. unfold paid_leaf. now rewrite H. Qed.

Theorem execution_refusal_keeps_inspection_charge :
  forall available leaf state inspected_budget inspected,
  paid_inspection false available leaf = Accepted inspected_budget inspected ->
  reserve inspected_budget
    (D.weighted D.logical_work_weight (execution_counts inspected))
    (D.weighted D.logical_unit_weight (execution_counts inspected)) = None ->
  paid_leaf false available leaf state = Refused inspected_budget.
Proof.
  intros available leaf state inspected_budget inspected HI HE.
  unfold paid_leaf. rewrite HI. now apply refused_counts_precede_action.
Qed.

End SharedEmission.

Section SupportedHasher.
Context {HasherState : Type}.
Variable actual_hasher_trace : NativeCall -> HasherState -> list D.Event.
Variable hasher_receipt : NativeCall -> D.Counts.

(** This predicate is the remaining supported-hasher instantiation, not an
    assertion that all Hasher implementations satisfy an envelope. It includes
    byte-processing work and scratch in the actual supported implementation. *)
Definition supports_receipt call state : Prop := forall event,
  O.sum_counts D.atom (actual_hasher_trace call state) event <= hasher_receipt call event.

Theorem supported_leaf_execution_cover : forall leaf state event,
  supports_receipt (ordinary_leaf_call leaf) state ->
  D.atom D.NativeWork event +
    O.sum_counts D.atom (actual_hasher_trace (ordinary_leaf_call leaf) state) event <=
  execution_counts hasher_receipt (inspect_leaf leaf) event.
Proof.
  intros leaf state event H. specialize (H event).
  unfold execution_counts. cbn [inspect_leaf inspected_call]. lia.
Qed.

End SupportedHasher.

(** Concrete source profile: rustc-hash 2.1.3 src/lib.rs, 64-bit pointers on
    x86_64, and the Rust Hash delegation audited at compiler revision
    2e2b193f8ada105f27608b7be81c293e0d7292cb. Profile selection and original
    native Hash invocation are Rust obligations. Ordinary generic H remains
    unchanged. Both Fx nightly write_str profiles fit the same envelope.

    hash_bytes uses floor((n-1)/16) bulk chunks only when n>16, then reads a
    full 16-byte suffix, which can overlap the last chunk. Short inputs read
    0, 3, 8 or 16 byte occurrences: duplicated positions still count. *)
Definition fx_bulk_chunks bytes := if bytes <=? 16 then 0 else (bytes - 1) / 16.
Definition fx_loaded_bytes bytes :=
  if bytes <=? 16 then
    if bytes =? 0 then 0 else if bytes <? 4 then 3 else if bytes <? 8 then 8 else 16
  else 16 * fx_bulk_chunks bytes + 16.
Definition fx_bulk_probes bytes :=
  if bytes <=? 16 then 0 else fx_bulk_chunks bytes + 1.

(** Audited bounded native groups, each excluding separately counted loads
    and mixes: leaf Hash dispatch (including String-to-str delegation),
    write_str dispatch, write(bytes) dispatch, compression setup, bulk probes,
    chunk decode/xor/update, short/suffix group, multiply_mix calls, loaded
    bytes, write_u64/accumulator group, optional sentinel accumulator, and
    final length xor. The short path has no bulk probe; the envelope safely
    includes the same terminal-probe allowance as the long path.
    These groups are logical NativeWork, not individual CPU instructions. *)
Definition fx_string_source_work (sentinel : bool) bytes :=
  1 + 1 + 1 + 1 + fx_bulk_probes bytes + fx_bulk_chunks bytes + 1 +
  (fx_bulk_chunks bytes + 1) + fx_loaded_bytes bytes + 1 +
  (if sentinel then 1 else 0) + 1.
Definition fx_string_envelope bytes :=
  10 + 3 * fx_bulk_chunks bytes + fx_loaded_bytes bytes.

Theorem fx_string_source_groups_are_covered : forall sentinel bytes,
  fx_string_source_work sentinel bytes <= fx_string_envelope bytes.
Proof.
  intros sentinel bytes.
  unfold fx_string_source_work, fx_string_envelope, fx_bulk_probes.
  destruct (bytes <=? 16); destruct sentinel; lia.
Qed.

Theorem fx_long_string_sentinel_profile_is_exact : forall bytes,
  16 < bytes -> fx_string_source_work true bytes = fx_string_envelope bytes.
Proof.
  intros bytes H.
  assert (HB : (bytes <=? 16) = false) by (apply Nat.leb_gt; lia).
  unfold fx_string_source_work, fx_string_envelope, fx_bulk_probes.
  rewrite HB. lia.
Qed.

Theorem fx_bulk_quotient_and_suffix_envelope : forall bytes,
  16 < bytes ->
  fx_bulk_chunks bytes = (bytes - 1) / 16 /\
  fx_loaded_bytes bytes <= bytes + 15.
Proof.
  intros bytes H.
  assert (HB : (bytes <=? 16) = false) by (apply Nat.leb_gt; lia).
  unfold fx_loaded_bytes, fx_bulk_chunks. rewrite HB.
  split; [reflexivity|].
  pose proof (Nat.div_mod (bytes - 1) 16 ltac:(lia)) as HD.
  nia.
Qed.

Theorem fx_short_loaded_bytes_are_bounded : forall bytes,
  bytes <= 16 -> fx_loaded_bytes bytes <= 16.
Proof.
  intros bytes H. unfold fx_loaded_bytes.
  assert (HB : (bytes <=? 16) = true) by (apply Nat.leb_le; lia).
  rewrite HB. destruct (bytes =? 0), (bytes <? 4), (bytes <? 8); lia.
Qed.

Example fx_short_and_bulk_boundary_loads :
  map fx_loaded_bytes [0; 1; 3; 4; 7; 8; 16; 17; 32; 33] =
  [0; 3; 3; 8; 8; 16; 16; 32; 32; 48].
Proof. reflexivity. Qed.

Definition fx_leaf_work leaf := match leaf with
  | Integer64 _ => 3
  | Text bytes => fx_string_envelope (length bytes)
  | _ => 2
  end.

(** execution_counts already pays the leaf dispatch. The concrete hasher
    receipt excludes precisely that event: signed i64 forwarding plus one
    accumulator group; one accumulator for bool/u8/usize; the String envelope
    minus its already-paid leaf dispatch. There is no allocation in these
    native hashing paths. Borrowed byte loads are work, not owned retention. *)
Definition fx_hasher_receipt call : D.Counts := fun event =>
  (match call with
   | WriteI64 _ => 2
   | WriteU8 _ | WriteUsize _ => 1
   | WriteStr bytes => fx_string_envelope (length bytes) - 1
   end) * D.atom D.NativeWork event.

Theorem fx_fixed_leaf_groups_are_exact : forall integer boolean byte word,
  fx_leaf_work (Integer64 integer) = 1 + 1 + 1 /\
  fx_leaf_work (Boolean boolean) = 1 + 1 /\
  fx_leaf_work (Tag8 byte) = 1 + 1 /\
  fx_leaf_work (TagWord word) = 1 + 1.
Proof. repeat split; reflexivity. Qed.

Theorem fx_execution_projection : forall leaf,
  D.weighted D.base_work_weight
    (execution_counts fx_hasher_receipt (inspect_leaf leaf)) = fx_leaf_work leaf /\
  D.weighted D.record_weight
    (execution_counts fx_hasher_receipt (inspect_leaf leaf)) = 0 /\
  D.weighted D.byte_weight
    (execution_counts fx_hasher_receipt (inspect_leaf leaf)) = 0.
Proof.
  intro leaf. unfold execution_counts, fx_hasher_receipt.
  rewrite !S.weighted_add, !V.weighted_scale.
  destruct leaf; try (repeat split; reflexivity).
  change (1 + (fx_string_envelope (length bytes) - 1) * 1 =
    fx_string_envelope (length bytes) /\
    0 + (fx_string_envelope (length bytes) - 1) * 0 = 0 /\
    0 + (fx_string_envelope (length bytes) - 1) * 0 = 0).
  unfold fx_string_envelope. repeat split; lia.
Qed.

Print Assumptions fixed_native_calls_are_exact.
Print Assumptions string_inspection_preserves_native_call_and_byte_extent.
Print Assumptions successful_paid_counts_reuses_same_action.
Print Assumptions refused_counts_precede_action.
Print Assumptions cancelled_counts_precede_action.
Print Assumptions inspection_projection.
Print Assumptions push_range_projection.
Print Assumptions task_push_also_pays_pending_disposal.
Print Assumptions borrowed_inspection_does_not_retain_bytes.
Print Assumptions admitted_inspection_is_exact.
Print Assumptions successful_leaf_preserves_original_hasher_call.
Print Assumptions inspection_refusal_cannot_execute_leaf.
Print Assumptions execution_refusal_keeps_inspection_charge.
Print Assumptions supported_leaf_execution_cover.
Print Assumptions fx_string_source_groups_are_covered.
Print Assumptions fx_long_string_sentinel_profile_is_exact.
Print Assumptions fx_bulk_quotient_and_suffix_envelope.
Print Assumptions fx_short_loaded_bytes_are_bounded.
Print Assumptions fx_short_and_bulk_boundary_loads.
Print Assumptions fx_fixed_leaf_groups_are_exact.
Print Assumptions fx_execution_projection.
End AdmittedKeyHashExecution.
