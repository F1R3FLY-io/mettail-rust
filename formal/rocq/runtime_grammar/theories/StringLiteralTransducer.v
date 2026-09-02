From Stdlib Require Import PeanoNat Lia List.
Import ListNotations.

(** An abstract alphabet is sufficient for the literal decoder: double quote
    and backslash are the only distinguished characters. All other Unicode
    scalar values travel through the same [Other] arm. *)
Inductive LiteralChar : Type :=
| Quote
| Slash
| Other (codepoint : nat).

(** The executable refinement is a two-state iterative transducer. This
    structurally recursive definition consumes the same one-or-two-character
    chunks as that loop: only escaped quote and escaped slash are contracted;
    every other escape pair is preserved literally. *)
Fixpoint decode_literal_body (input : list LiteralChar) : list LiteralChar :=
  match input with
  | [] => []
  | Slash :: Quote :: rest => Quote :: decode_literal_body rest
  | Slash :: Slash :: rest => Slash :: decode_literal_body rest
  | Slash :: character :: rest => Slash :: character :: decode_literal_body rest
  | character :: rest => character :: decode_literal_body rest
  end.

Fixpoint encode_literal_body (value : list LiteralChar) : list LiteralChar :=
  match value with
  | [] => []
  | Quote :: rest => Slash :: Quote :: encode_literal_body rest
  | Slash :: rest => Slash :: Slash :: encode_literal_body rest
  | Other codepoint :: rest => Other codepoint :: encode_literal_body rest
  end.

Theorem decode_encode_round_trip :
  forall value,
    decode_literal_body (encode_literal_body value) = value.
Proof.
  intros value.
  induction value as [| character rest IH].
  - reflexivity.
  - destruct character; simpl; rewrite IH; reflexivity.
Qed.

Theorem unknown_escape_is_preserved :
  forall codepoint rest,
    decode_literal_body (Slash :: Other codepoint :: rest) =
    Slash :: Other codepoint :: decode_literal_body rest.
Proof.
  reflexivity.
Qed.

Theorem decoded_length_never_exceeds_input :
  forall input,
    length (decode_literal_body input) <= length input.
Proof.
  fix IH 1.
  intros input.
  destruct input as [| first rest].
  - simpl. lia.
  - destruct first.
    + simpl. specialize (IH rest). lia.
    + destruct rest as [| second tail].
      * simpl. lia.
      * destruct second; simpl; specialize (IH tail); lia.
    + simpl. specialize (IH rest). lia.
Qed.

Theorem escaped_quote_and_slash_are_the_only_contractions :
  forall character rest,
    character <> Quote ->
    character <> Slash ->
    length (decode_literal_body (Slash :: character :: rest)) =
    2 + length (decode_literal_body rest).
Proof.
  intros character rest Hquote Hslash.
  destruct character; try contradiction. simpl. lia.
Qed.

(** Escape pairs are consumed from left to right.  In particular, the first
    two slashes below form one escaped slash; the remaining slash then escapes
    the quote.  A sequence of global textual replacements can incorrectly
    rewrite across the boundary created by its preceding pass, so it is not a
    refinement of this transition system. *)
Example overlapping_escape_pairs_preserve_the_literal_slash :
  decode_literal_body [Slash; Slash; Slash; Quote] = [Slash; Quote].
Proof. reflexivity. Qed.

Print Assumptions decode_encode_round_trip.
Print Assumptions unknown_escape_is_preserved.
Print Assumptions decoded_length_never_exceeds_input.
Print Assumptions escaped_quote_and_slash_are_the_only_contractions.
Print Assumptions overlapping_escape_pairs_preserve_the_literal_slash.
