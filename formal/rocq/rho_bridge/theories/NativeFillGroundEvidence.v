(** Canonical native fills retain the ground evidence of direct reflection.

    The production change is limited to the Fill transition of the existing
    construction worklist. A native leaf has no explicit marker, but its
    direct nullary reflection has hereditary-ground value true. The new
    evidence requires exact equality with the existing canonical writer.

    Wire below denotes the whole retained Par, not just its decoded tag.
    The decoder and writer are universally quantified: no codec-correctness
    axiom is assumed. Successful enrollment proves exact writer equality;
    the round-trip premise for a particular native value must be supplied by
    the concrete codec checks. Existing native validators decide the closed
    family; this model does not replace or certify their Rust implementation.

    Construction still retains the original fill. Ancestor assembly receives
    identical ordered children and ground bits, so every continuation returns
    an identical result. No parse family is filtered by this correction. *)

From Stdlib Require Import List Bool PeanoNat.
From RhoBridge Require Import DeBruijnSubstTRS InRhoCreeperTrace.
Import ListNotations.

Section ExactNativeEvidence.
  Context {Wire Native : Type}.
  Variable wire_eq_dec : forall first second : Wire, {first = second} + {first <> second}.
  Variable decode_native : Wire -> option Native.
  Variable encode_native : Native -> Wire.

  Definition native_evidence (fill : Wire) : bool :=
    match decode_native fill with
    | None => false
    | Some atom => if wire_eq_dec fill (encode_native atom) then true else false
    end.

  Definition construction_fill (fill : Wire) (marker_ground : bool) : Wire * bool :=
    (fill, marker_ground || native_evidence fill).

  Theorem native_evidence_retains_exact_wire : forall fill,
    native_evidence fill = true ->
    exists atom, decode_native fill = Some atom /\ fill = encode_native atom.
  Proof.
    intros fill H. unfold native_evidence in H.
    destruct (decode_native fill) as [atom|] eqn:E; [|discriminate].
    destruct (wire_eq_dec fill (encode_native atom)); [exists atom; auto|discriminate].
  Qed.

  Theorem noncanonical_wire_is_not_promoted : forall fill atom,
    decode_native fill = Some atom -> fill <> encode_native atom -> native_evidence fill = false.
  Proof.
    intros fill atom Hdecode Hneq. unfold native_evidence. rewrite Hdecode.
    destruct (wire_eq_dec fill (encode_native atom)); [contradiction|reflexivity].
  Qed.

  Theorem unrecognized_fill_retains_existing_ground_bit : forall fill observed,
    decode_native fill = None -> construction_fill fill observed = (fill, observed).
  Proof.
    intros fill observed H. unfold construction_fill, native_evidence. rewrite H.
    now rewrite orb_false_r.
  Qed.

  Theorem unenrolled_fill_retains_existing_ground_bit : forall fill observed,
    native_evidence fill = false -> construction_fill fill observed = (fill, observed).
  Proof.
    intros fill observed H. unfold construction_fill. rewrite H. now rewrite orb_false_r.
  Qed.

  Theorem construction_never_rewrites_the_fill : forall fill observed,
    fst (construction_fill fill observed) = fill.
  Proof. reflexivity. Qed.

  Theorem canonical_native_fill_matches_direct_result : forall atom observed,
    decode_native (encode_native atom) = Some atom ->
    construction_fill (encode_native atom) observed = (encode_native atom, true).
  Proof.
    intros atom observed H. unfold construction_fill, native_evidence. rewrite H.
    destruct (wire_eq_dec (encode_native atom) (encode_native atom)); [|contradiction].
    now rewrite orb_true_r.
  Qed.

  (** The list is the actual ordered child sequence, not a set: duplicate
      occurrences and their positions survive. Only the evidence bit changes. *)
  Theorem native_fill_preserves_order_and_multiplicity : forall before after atom observed,
    decode_native (encode_native atom) = Some atom ->
    before ++ construction_fill (encode_native atom) observed :: after =
    before ++ (encode_native atom, true) :: after.
  Proof. intros; now rewrite canonical_native_fill_matches_direct_result. Qed.

  Variable assemble : nat -> list (Wire * bool) -> Wire * bool.

  Record Frame := {
    frame_label : nat;
    frame_before : list (Wire * bool);
    frame_after : list (Wire * bool)
  }.

  Definition resume_frame (value : Wire * bool) (frame : Frame) : Wire * bool :=
    assemble (frame_label frame) (frame_before frame ++ value :: frame_after frame).

  Definition resume_ancestors (frames : list Frame) (value : Wire * bool) :=
    fold_left resume_frame frames value.

  Theorem canonical_native_fill_preserves_every_ancestor : forall frames atom observed,
    decode_native (encode_native atom) = Some atom ->
    resume_ancestors frames (construction_fill (encode_native atom) observed) =
    resume_ancestors frames (encode_native atom, true).
  Proof. intros; now rewrite canonical_native_fill_matches_direct_result. Qed.

  Theorem canonical_native_fill_preserves_any_observation :
    forall (Result : Type) (observe : Wire * bool -> Result) frames atom observed,
    decode_native (encode_native atom) = Some atom ->
    observe (resume_ancestors frames (construction_fill (encode_native atom) observed)) =
    observe (resume_ancestors frames (encode_native atom, true)).
  Proof. intros; now rewrite canonical_native_fill_preserves_every_ancestor. Qed.
End ExactNativeEvidence.

(** Nullary native syntax is a binder-free node under the existing object
    algebra. Its payload identity is retained by the Wire laws above, not
    represented or compared by this groundness projection. *)
Theorem native_nullary_is_hereditarily_ground : forall label,
  oground (oNode label []) = true.
Proof. reflexivity. Qed.

Corollary native_nullary_substitution_is_identity : forall label depth replacement,
  osubst depth replacement (oNode label []) = oNode label [].
Proof. intros; apply oground_subst_id, native_nullary_is_hereditarily_ground. Qed.

Corollary native_nullary_shift_is_identity : forall label cutoff,
  oshift cutoff (oNode label []) = oNode label [].
Proof. intros; apply oground_shift_id, native_nullary_is_hereditarily_ground. Qed.

Print Assumptions native_evidence_retains_exact_wire.
Print Assumptions noncanonical_wire_is_not_promoted.
Print Assumptions unrecognized_fill_retains_existing_ground_bit.
Print Assumptions unenrolled_fill_retains_existing_ground_bit.
Print Assumptions construction_never_rewrites_the_fill.
Print Assumptions canonical_native_fill_matches_direct_result.
Print Assumptions native_fill_preserves_order_and_multiplicity.
Print Assumptions canonical_native_fill_preserves_every_ancestor.
Print Assumptions canonical_native_fill_preserves_any_observation.
Print Assumptions native_nullary_is_hereditarily_ground.
Print Assumptions native_nullary_substitution_is_identity.
Print Assumptions native_nullary_shift_is_identity.
