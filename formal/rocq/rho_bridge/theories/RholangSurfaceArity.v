(** Surface argument boundaries are semantic: a one-element list datum is not a
    two-argument send. The target constructors already retain ordered payload
    and pattern vectors; the frontend must map each surface argument to one
    vector entry, without synthesizing a list around a zero/polyadic form. *)

From Stdlib Require Import List PeanoNat.
From RhoBridge Require Import RholangTargetConstruction.
Import ListNotations.

Definition lower_surface_send (persistent : bool) (channel : Value)
    (arguments : list Value) : Value := send persistent channel arguments.

Definition lower_surface_bind (source : Value) (patterns : list Value)
    (capture_count : nat) : BindValue :=
  {| bind_source := source;
     bind_patterns := patterns;
     bind_free_count := capture_count;
     bind_remainder := None |}.

Theorem surface_send_preserves_every_argument : forall persistent channel arguments,
  heads_of (lower_surface_send persistent channel arguments) =
    [MakeHead (SendHead persistent) (channel :: arguments)].
Proof. reflexivity. Qed.

Theorem surface_bind_preserves_every_pattern : forall source patterns captures,
  bind_patterns (lower_surface_bind source patterns captures) = patterns /\
  pattern_count (bind_shape (lower_surface_bind source patterns captures)) =
    List.length patterns /\
  bind_children (lower_surface_bind source patterns captures) = source :: patterns.
Proof. intros; repeat split; reflexivity. Qed.

Theorem zero_one_and_polyadic_arities_are_distinct : forall source first second,
  pattern_count (bind_shape (lower_surface_bind source [] 0)) = 0 /\
  pattern_count (bind_shape (lower_surface_bind source [first] 0)) = 1 /\
  pattern_count (bind_shape (lower_surface_bind source [first; second] 0)) = 2 /\
  pattern_count (bind_shape (lower_surface_bind source [list_value [first; second]] 0)) = 1.
Proof. intros; repeat split; reflexivity. Qed.

Theorem explicit_list_send_is_not_polyadic : forall persistent channel first second,
  lower_surface_send persistent channel [list_value [first; second]] <>
  lower_surface_send persistent channel [first; second].
Proof.
  intros persistent channel first second H.
  apply (f_equal heads_of) in H.
  cbn [lower_surface_send send ordinary heads_of] in H.
  discriminate H.
Qed.

(** The install service is an ABI boundary, not a general arity coercion. Its
    two-pattern receive binds both surface arguments exactly. A singleton
    list datum is not silently unpacked into two RSpace message slots. *)
Definition decode_install_payload (payload : list Value) : option (Value * Value) :=
  match payload with
  | specification :: reply :: [] => Some (specification, reply)
  | _ => None
  end.

Theorem install_surface_pair_preserves_both_arguments : forall specification reply,
  decode_install_payload [specification; reply] = Some (specification, reply).
Proof. reflexivity. Qed.

Theorem install_canonical_list_is_not_two_arguments : forall specification reply,
  decode_install_payload [list_value [specification; reply]] = None.
Proof. reflexivity. Qed.

Theorem install_rejects_other_payload_cardinalities : forall a b c d,
  decode_install_payload [] = None /\
  decode_install_payload [a] = None /\
  decode_install_payload [a; b; c] = None /\
  decode_install_payload [a; b; c; d] = None.
Proof. intros; repeat split; reflexivity. Qed.

Print Assumptions surface_send_preserves_every_argument.
Print Assumptions surface_bind_preserves_every_pattern.
Print Assumptions zero_one_and_polyadic_arities_are_distinct.
Print Assumptions explicit_list_send_is_not_polyadic.
Print Assumptions install_surface_pair_preserves_both_arguments.
Print Assumptions install_canonical_list_is_not_two_arguments.
Print Assumptions install_rejects_other_payload_cardinalities.
