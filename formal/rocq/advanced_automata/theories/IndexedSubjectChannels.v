(*
 * IndexedSubjectChannels
 *
 * Zero-admission model of the compact in-Rho subject-channel ABI.  The Rust
 * encoder writes a length-delimited root-site field and one fixed-width u64
 * subject-position field, then scopes that path by channel family and language
 * fingerprint.  The model retains those field boundaries explicitly; the
 * hexadecimal rendering used by Rust is canonical for each natural-number
 * field, so tuple equality is exactly wire-field equality.
 *
 * Rust correspondence:
 *   - indexed_path_wire       rho_net_location::SubjectLocationIndex::channel
 *   - channel_wire            scoped_channel_name(family, fingerprint, path)
 *   - live_position/dead      MatcherPosition::{Live, Dead}
 *   - indexed_path_wire_size  constant-per-position channel materialization
 *
 * The proofs establish exact (non-hash) injectivity, family/fingerprint
 * isolation, separation of live positions from the reserved dead position,
 * and position-independent encoded size.  No Admitted, Axioms, or assumptions.
 *)

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Definition root_site := list nat.
Definition position := nat.

(* The first component is the byte length prefix.  The second and third are
   the root bytes and fixed-width position field. *)
Definition indexed_path_wire (root : root_site) (pos : position)
  : nat * (root_site * position) :=
  (length root, (root, pos)).

Definition channel_wire
  (fingerprint family : nat) (root : root_site) (pos : position)
  : nat * (nat * (nat * (root_site * position))) :=
  (fingerprint, (family, indexed_path_wire root pos)).

Theorem indexed_path_wire_injective : forall root_left root_right pos_left pos_right,
  indexed_path_wire root_left pos_left = indexed_path_wire root_right pos_right ->
  root_left = root_right /\ pos_left = pos_right.
Proof.
  intros root_left root_right pos_left pos_right Heq.
  unfold indexed_path_wire in Heq.
  split; congruence.
Qed.

Theorem channel_wire_injective : forall fp_left fp_right family_left family_right
  root_left root_right pos_left pos_right,
  channel_wire fp_left family_left root_left pos_left =
  channel_wire fp_right family_right root_right pos_right ->
  fp_left = fp_right /\ family_left = family_right /\
  root_left = root_right /\ pos_left = pos_right.
Proof.
  intros fp_left fp_right family_left family_right
    root_left root_right pos_left pos_right Heq.
  unfold channel_wire, indexed_path_wire in Heq.
  repeat split; congruence.
Qed.

Theorem distinct_positions_have_distinct_channels : forall fingerprint family root left right,
  left <> right ->
  channel_wire fingerprint family root left <>
  channel_wire fingerprint family root right.
Proof.
  intros fingerprint family root left right Hneq Heq.
  apply channel_wire_injective in Heq as [_ [_ [_ Hpos]]].
  contradiction.
Qed.

Theorem channel_families_are_isolated : forall fingerprint left_family right_family
  root left right,
  left_family <> right_family ->
  channel_wire fingerprint left_family root left <>
  channel_wire fingerprint right_family root right.
Proof.
  intros fingerprint left_family right_family root left right Hneq Heq.
  apply channel_wire_injective in Heq as [_ [Hfamily _]].
  contradiction.
Qed.

Theorem channel_languages_are_isolated : forall left_fp right_fp family root left right,
  left_fp <> right_fp ->
  channel_wire left_fp family root left <>
  channel_wire right_fp family root right.
Proof.
  intros left_fp right_fp family root left right Hneq Heq.
  apply channel_wire_injective in Heq as [Hfp _].
  contradiction.
Qed.

(* Rust reserves u64::MAX for an absent pattern continuation.  [capacity] is
   that reserved value; every real index is admitted only below it. *)
Definition live_position (pos : position) : position := pos.
Definition dead_position (capacity : nat) : position := capacity.

Theorem live_position_never_equals_dead : forall capacity pos,
  pos < capacity -> live_position pos <> dead_position capacity.
Proof.
  unfold live_position, dead_position. intros capacity pos Hlt Heq. lia.
Qed.

(* One length field, the root-site bytes, and one fixed-width position field.
   In particular, size does not depend on tree depth or the numeric position. *)
Definition indexed_path_wire_size (root : root_site) : nat :=
  1 + length root + 1.

Definition indexed_position_wire_size (root : root_site) (_pos : position) : nat :=
  indexed_path_wire_size root.

Theorem indexed_path_size_is_position_independent : forall root left right,
  indexed_position_wire_size root left = indexed_position_wire_size root right.
Proof.
  reflexivity.
Qed.

Theorem indexed_path_size_is_linear_in_root_site : forall root,
  indexed_path_wire_size root = length root + 2.
Proof.
  intro root. unfold indexed_path_wire_size. lia.
Qed.

Print Assumptions indexed_path_wire_injective.
Print Assumptions channel_wire_injective.
Print Assumptions distinct_positions_have_distinct_channels.
Print Assumptions channel_families_are_isolated.
Print Assumptions channel_languages_are_isolated.
Print Assumptions live_position_never_equals_dead.
Print Assumptions indexed_path_size_is_position_independent.
Print Assumptions indexed_path_size_is_linear_in_root_site.
