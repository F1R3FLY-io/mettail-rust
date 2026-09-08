(** Shared intrinsic shape admission before contextual theory compilation.

    This model covers the extracted opcode/arity/name boundary. A RawShape
    contains the ordered fields after the existing map/list/typed-output and
    sort-syntax decoders; those concrete decoders require Rust tests. It does
    not stand for a trusted executable intrinsic or grant authority. The
    existing compiler must still check available inputs, fresh outputs, sort
    existence, carrier compatibility and limits. The final composition law is
    universal in that unchanged compiler, not an assumed correctness flag. *)

From Stdlib Require Import String List Bool PeanoNat.
From RuntimeGrammar Require Import SemanticIntrinsics.
Import ListNotations SemanticIntrinsics.SemanticIntrinsics.

Definition opcode_spelling (opcode : IntrinsicOpcode) : string :=
  match opcode with
  | ExactTermEq => "exact_term_eq"
  | Utf8AtEnd => "utf8_at_end"
  | Utf8ScalarAt => "utf8_scalar_at"
  | Utf8Slice => "utf8_slice"
  | CheckedNatAdd => "checked_nat_add"
  | TextPlanMaterialize => "utf8_concat_many"
  end%string.

Definition decode_opcode (name : string) : option IntrinsicOpcode :=
  if String.eqb name "exact_term_eq" then Some ExactTermEq else
  if String.eqb name "utf8_at_end" then Some Utf8AtEnd else
  if String.eqb name "utf8_scalar_at" then Some Utf8ScalarAt else
  if String.eqb name "utf8_slice" then Some Utf8Slice else
  if String.eqb name "checked_nat_add" then Some CheckedNatAdd else
  if String.eqb name "utf8_concat_many" then Some TextPlanMaterialize else None.

Theorem opcode_round_trip : forall opcode,
  decode_opcode (opcode_spelling opcode) = Some opcode.
Proof. destruct opcode; reflexivity. Qed.

Theorem decoded_opcode_has_exact_spelling : forall name opcode,
  decode_opcode name = Some opcode -> name = opcode_spelling opcode.
Proof.
  intros name opcode H. unfold decode_opcode in H.
  repeat match type of H with
  | context [if String.eqb name ?literal then _ else _] =>
      destruct (String.eqb name literal) eqn:E;
      [apply String.eqb_eq in E; inversion H; subst; reflexivity|clear E]
  end. discriminate.
Qed.

Record RawShape := {
  raw_opcode : string;
  raw_inputs : list string;
  raw_outputs : list (string * string)
}.

Record DecodedShape := {
  shape_opcode : IntrinsicOpcode;
  shape_inputs : list string;
  shape_outputs : list (string * string)
}.

Definition nonempty_name (name : string) : bool := negb (String.eqb name EmptyString).

Definition shape_fields_valid (opcode : IntrinsicOpcode)
    (inputs : list string) (outputs : list (string * string)) : bool :=
  (List.length inputs =? List.length (intrinsic_domain opcode)) &&
  (List.length outputs =? List.length (intrinsic_codomain opcode)) &&
  forallb nonempty_name inputs && forallb (fun output => nonempty_name (fst output)) outputs.

Definition decode_shape (raw : RawShape) : option DecodedShape :=
  match decode_opcode (raw_opcode raw) with
  | None => None
  | Some opcode =>
      if shape_fields_valid opcode (raw_inputs raw) (raw_outputs raw)
      then Some {| shape_opcode := opcode; shape_inputs := raw_inputs raw;
                   shape_outputs := raw_outputs raw |}
      else None
  end.

Definition encode_shape (shape : DecodedShape) : RawShape :=
  {| raw_opcode := opcode_spelling (shape_opcode shape);
     raw_inputs := shape_inputs shape; raw_outputs := shape_outputs shape |}.

Theorem decoded_shape_preserves_every_ordered_field : forall raw shape,
  decode_shape raw = Some shape ->
  encode_shape shape = raw /\
  shape_fields_valid (shape_opcode shape) (shape_inputs shape) (shape_outputs shape) = true.
Proof.
  intros [name inputs outputs] shape H. unfold decode_shape in H; cbn in H.
  destruct (decode_opcode name) as [opcode|] eqn:E; [|discriminate].
  destruct (shape_fields_valid opcode inputs outputs) eqn:V; [|discriminate].
  inversion H; subst. split; [|exact V].
  apply decoded_opcode_has_exact_spelling in E. subst name. reflexivity.
Qed.

Theorem valid_shape_round_trip : forall shape,
  shape_fields_valid (shape_opcode shape) (shape_inputs shape) (shape_outputs shape) = true ->
  decode_shape (encode_shape shape) = Some shape.
Proof.
  intros [opcode inputs outputs] H. cbn [shape_opcode shape_inputs shape_outputs] in H.
  unfold decode_shape, encode_shape; cbn.
  rewrite opcode_round_trip, H. reflexivity.
Qed.

Theorem decoded_shape_has_exact_existing_arities : forall raw shape,
  decode_shape raw = Some shape ->
  List.length (shape_inputs shape) = List.length (intrinsic_domain (shape_opcode shape)) /\
  List.length (shape_outputs shape) = List.length (intrinsic_codomain (shape_opcode shape)).
Proof.
  intros raw shape H.
  destruct (decoded_shape_preserves_every_ordered_field _ _ H) as [_ V].
  unfold shape_fields_valid in V. repeat rewrite andb_true_iff in V.
  destruct V as [[[Hin Hout] _] _]. apply Nat.eqb_eq in Hin, Hout. auto.
Qed.

Theorem unknown_opcode_is_rejected : forall raw,
  decode_opcode (raw_opcode raw) = None -> decode_shape raw = None.
Proof. intros raw H; unfold decode_shape; now rewrite H. Qed.

Definition schema_admits (raw : RawShape) : bool :=
  match decode_shape raw with Some _ => true | None => false end.

Section CompilerComposition.
  Context {Result : Type}.
  Variable contextual_compile : DecodedShape -> option Result.

  Definition direct_compile (raw : RawShape) : option Result :=
    match decode_shape raw with
    | Some shape => contextual_compile shape
    | None => None
    end.

  Definition schema_then_compile (raw : RawShape) : option Result :=
    if schema_admits raw then direct_compile raw else None.

  Theorem shared_schema_preserves_contextual_compilation : forall raw,
    schema_then_compile raw = direct_compile raw.
  Proof. intro raw; unfold schema_then_compile, schema_admits, direct_compile;
    destruct (decode_shape raw); reflexivity. Qed.

  Theorem shape_acceptance_cannot_bypass_contextual_refusal : forall raw shape,
    decode_shape raw = Some shape -> contextual_compile shape = None ->
    schema_then_compile raw = None.
  Proof. intros raw shape Hdecode Hreject.
    rewrite shared_schema_preserves_contextual_compilation.
    unfold direct_compile. now rewrite Hdecode, Hreject. Qed.
End CompilerComposition.

Print Assumptions opcode_round_trip.
Print Assumptions decoded_opcode_has_exact_spelling.
Print Assumptions decoded_shape_preserves_every_ordered_field.
Print Assumptions valid_shape_round_trip.
Print Assumptions decoded_shape_has_exact_existing_arities.
Print Assumptions unknown_opcode_is_rejected.
Print Assumptions shared_schema_preserves_contextual_compilation.
Print Assumptions shape_acceptance_cannot_bypass_contextual_refusal.
