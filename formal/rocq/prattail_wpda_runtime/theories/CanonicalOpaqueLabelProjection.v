(** One shared constructor-label body with an explicit canonical opaque input.

    Sources: grammar-core/src/constructor_labels.rs::generate_literal_label;
    macros/src/gen/native/mod.rs::NativeTypeFromSynType/is_byte_vector;
    mettail-elab/src/schema.rs::decode_carrier (extern retains only its URN),
    and grammar-core/src/normalize.rs106--125 (TokenValue adds no constructor).
    The canonical contract is FIPS-mettail-in-rholang-specs/under-review/
    2026-07-25-MeTTaIL-Language-Specs-in-Rholang/
    2026-07-25-MeTTaIL-Language-Specs-in-Rholang.md1488--1538,2698--2699,3146.
    It declares registered opaque carriers, not recoverable Rust type paths.

    Intended interface: generate_literal_label_observed receives the original
    byte callback, an observation callback, and the original constructor.
    ExactNativeType unwraps into the ONE unchanged original integer/match body.
    CanonicalOpaque chooses the generic Lit constructor without manufacturing
    NativeType::Other text. The existing public API delegates by wrapping its
    original classifier result in ExactNativeType, at the same lazy call site.
    NativeType and its string classifier are imported, never extended here.

    CanonicalOpaque is a positive observation supplied only by the validated
    canonical extern producer, whose byte observation is false. The URN remains
    registry identity, never a classifier input. This is a label-only quotient
    of genuinely generic Other results, not equality of hidden Rust source,
    classifier effects, integer/string probe traces, carriers, values, decoders,
    fingerprints, or capture arenas. Existing special wrapper cases remain
    distinct. Metadata availability/capture/admission/ABI refinement is separate.
*)
From Stdlib Require Import List String Bool.
From PrattailWpdaRuntime Require Import ConstructorLabelProjection.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.
Set Implicit Arguments.

Module CanonicalOpaqueLabelProjection.
Module P := ConstructorLabelProjection.ConstructorLabelProjection.

Inductive LiteralNativeObservation :=
| ExactNativeType (native : P.NativeType)
| CanonicalOpaque.

Definition canonical_extern (_urn : string) := CanonicalOpaque.
Definition canonical_extern_byte (_urn : string) := false.
Definition nonbyte_selection observation := match observation with
| ExactNativeType native => P.shared_nonbyte_selection native
| CanonicalOpaque => ("Lit", []) end.
Definition selected_label (byte : bool) observation :=
  if byte then "BytesLit" else fst (nonbyte_selection observation).

Theorem exact_selection_reuses_original_match : forall byte native,
  selected_label byte (ExactNativeType native) = P.selected_label byte native.
Proof. intros [] native; reflexivity. Qed.

Theorem generic_other_is_a_label_only_quotient : forall spelling,
  spelling <> "HashSetLit" -> spelling <> "PathMapLit" ->
  selected_label false CanonicalOpaque = P.selected_label false (P.Other spelling).
Proof.
  intros spelling NotSet NotPathmap.
  assert (SetFalse : String.eqb spelling "HashSetLit" = false)
    by (apply String.eqb_neq; exact NotSet).
  assert (PathFalse : String.eqb spelling "PathMapLit" = false)
    by (apply String.eqb_neq; exact NotPathmap).
  unfold P.selected_label, P.shared_nonbyte_selection, P.original_is_integer,
    P.original_kind_match; rewrite SetFalse, PathFalse; reflexivity.
Qed.

Theorem distinguished_wrappers_are_not_collapsed :
  P.selected_label false (P.Other "HashSetLit") = "SetLit" /\
  P.selected_label false (P.Other "PathMapLit") = "PathmapLit" /\
  selected_label false CanonicalOpaque = "Lit" /\
  P.selected_label false (P.Other "HashSetLit") <> selected_label false CanonicalOpaque /\
  P.selected_label false (P.Other "PathMapLit") <> selected_label false CanonicalOpaque.
Proof. vm_compute; repeat split; try reflexivity; discriminate. Qed.

Theorem canonical_opaque_selection_does_not_parse_urn : forall first second,
  selected_label (canonical_extern_byte first) (canonical_extern first) =
  selected_label (canonical_extern_byte second) (canonical_extern second).
Proof. reflexivity. Qed.

Section Callbacks.
Context {State Label Error : Type}.
Variable byte_probe : State -> bool * State.
Variable classify : State -> P.NativeType * State.
Variable observe : State -> LiteralNativeObservation * State.
Variable construct : string -> State -> (Label + Error) * State.

(** This is the original callback schedule with one new observation case;
    native matching remains the imported original body, not a second match. *)
Definition observed_literal observation state :=
  let '(byte, after_byte) := byte_probe state in
  if byte then P.invoke construct [P.ByteProbe] "BytesLit" after_byte
  else let '(native, after_native) := observation after_byte in
       let '(label, probes) := nonbyte_selection native in
       P.invoke construct ([P.ByteProbe; P.NativeClassification] ++ probes) label after_native.
Definition exact_callback state :=
  let '(native, next) := classify state in (ExactNativeType native, next).

Theorem exact_wrapper_preserves_full_state_result_and_trace : forall state,
  observed_literal exact_callback state = P.original_literal byte_probe classify construct state.
Proof.
  intros state; rewrite <- P.exact_lazy_literal_callback_schedule.
  unfold observed_literal, P.shared_literal.
  destruct (byte_probe state) as [byte next]; destruct byte; [reflexivity|].
  unfold exact_callback; destruct (classify next) as [native ready]; reflexivity.
Qed.

Theorem byte_probe_suppresses_every_observation : forall state after_byte,
  byte_probe state = (true, after_byte) ->
  observed_literal observe state = P.invoke construct [P.ByteProbe] "BytesLit" after_byte.
Proof. intros state after_byte Byte; unfold observed_literal; rewrite Byte; reflexivity. Qed.

Theorem opaque_invokes_only_generic_constructor : forall state after_byte ready,
  byte_probe state = (false, after_byte) ->
  observe after_byte = (CanonicalOpaque, ready) ->
  observed_literal observe state =
    P.invoke construct [P.ByteProbe; P.NativeClassification] "Lit" ready.
Proof. intros state after_byte ready Byte Opaque; unfold observed_literal; rewrite Byte, Opaque; reflexivity. Qed.

Theorem opaque_preserves_constructor_result_and_state : forall state after_byte ready result next,
  byte_probe state = (false, after_byte) ->
  observe after_byte = (CanonicalOpaque, ready) ->
  construct "Lit" ready = (result, next) ->
  observed_literal observe state =
    (result, next, [P.ByteProbe; P.NativeClassification; P.Construct "Lit"]).
Proof.
  intros state after_byte ready result next Byte Opaque Built.
  rewrite (@opaque_invokes_only_generic_constructor state after_byte ready Byte Opaque).
  unfold P.invoke; rewrite Built; reflexivity.
Qed.

Theorem opaque_constructor_failure_is_not_replaced : forall state after_byte ready error failed,
  byte_probe state = (false, after_byte) ->
  observe after_byte = (CanonicalOpaque, ready) ->
  construct "Lit" ready = (inr error, failed) ->
  observed_literal observe state =
    (inr error, failed, [P.ByteProbe; P.NativeClassification; P.Construct "Lit"]).
Proof. intros; eapply opaque_preserves_constructor_result_and_state; eauto. Qed.

(** Both constructors start in the same ready state. No equality of the prior
    native-classification callbacks or hidden probe traces is asserted. *)
Theorem generic_other_preserves_only_constructor_outcome : forall spelling ready,
  spelling <> "HashSetLit" -> spelling <> "PathMapLit" ->
  construct (selected_label false CanonicalOpaque) ready =
    construct (P.selected_label false (P.Other spelling)) ready.
Proof. intros; rewrite (generic_other_is_a_label_only_quotient H H0); reflexivity. Qed.

Theorem canonical_opaque_callback_is_urn_independent : forall first second state,
  observed_literal (fun ready => (canonical_extern first, ready)) state =
  observed_literal (fun ready => (canonical_extern second, ready)) state.
Proof. reflexivity. Qed.
End Callbacks.

Print Assumptions exact_selection_reuses_original_match.
Print Assumptions generic_other_is_a_label_only_quotient.
Print Assumptions distinguished_wrappers_are_not_collapsed.
Print Assumptions canonical_opaque_selection_does_not_parse_urn.
Print Assumptions exact_wrapper_preserves_full_state_result_and_trace.
Print Assumptions byte_probe_suppresses_every_observation.
Print Assumptions opaque_invokes_only_generic_constructor.
Print Assumptions opaque_preserves_constructor_result_and_state.
Print Assumptions opaque_constructor_failure_is_not_replaced.
Print Assumptions generic_other_preserves_only_constructor_outcome.
Print Assumptions canonical_opaque_callback_is_urn_independent.
End CanonicalOpaqueLabelProjection.
