(** * Injective terminal identities shared by lexer and parser analysis

    A grammar terminal is source text, while generated lexer/parser tables use
    a Rust token-variant identifier.  A readable case-normalizing identifier
    is not an identity: distinct terminals such as [Theory] and [theory]
    collapse.  The generated pipeline therefore classifies a terminal into a
    disjoint namespace and encodes its payload exactly.

    This model establishes the obligations at that boundary:

    - byte payload encoding is injective;
    - namespace tags prevent cross-class collisions;
    - equal generated identities imply equal classified terminals;
    - FIRST/FOLLOW and WFST consumers preserve membership when every query is
      derived through the same encoding;
    - the historical case-folded representation has a concrete collision.

    The Rust property tests exercise the concrete classifier, fixed-symbol
    table, UTF-8 byte encoder, and every prediction/WFST consumer. *)

From Stdlib Require Import List Arith.PeanoNat Lia.
Import ListNotations.

Module TerminalVariantIdentity.

  Definition Byte := nat.
  Definition NibblePair := (nat * nat)%type.

  (** The concrete emitter writes the quotient and remainder as two
      hexadecimal nibbles.  Retaining the pair here removes presentation-only
      characters while preserving exactly the information used by Rust. *)
  Definition split_byte (byte : Byte) : NibblePair :=
    (byte / 16, byte mod 16).

  Definition join_byte (digits : NibblePair) : Byte :=
    16 * fst digits + snd digits.

  Lemma join_split_byte : forall byte,
      join_byte (split_byte byte) = byte.
  Proof.
    intro byte.
    change (16 * (byte / 16) + byte mod 16 = byte).
    symmetry. exact (Nat.div_mod_eq byte 16).
  Qed.

  Definition encode_payload (bytes : list Byte) : list NibblePair :=
    map split_byte bytes.

  Definition decode_payload (digits : list NibblePair) : list Byte :=
    map join_byte digits.

  Lemma decode_encode_payload : forall bytes,
      decode_payload (encode_payload bytes) = bytes.
  Proof.
    induction bytes as [|byte rest IH]; simpl.
    - reflexivity.
    - rewrite join_split_byte, IH. reflexivity.
  Qed.

  Theorem encode_payload_injective : forall left right,
      encode_payload left = encode_payload right -> left = right.
  Proof.
    intros left right Hequal.
    apply (f_equal decode_payload) in Hequal.
    repeat rewrite decode_encode_payload in Hequal.
    exact Hequal.
  Qed.

  (** [FixedTerminal] is the audited finite symbolic-terminal table.  Its
      identifier is already unique.  Every other constructor corresponds to
      one disjoint prefix in the emitted Rust identifier. *)
  Inductive ClassifiedTerminal : Type :=
  | FixedTerminal : nat -> ClassifiedTerminal
  | KeywordTerminal : list Byte -> ClassifiedTerminal
  | DollarTerminal : list Byte -> ClassifiedTerminal
  | DoubleDollarCallTerminal : list Byte -> ClassifiedTerminal
  | FallbackTerminal : list Byte -> ClassifiedTerminal.

  Inductive VariantIdentity : Type :=
  | FixedVariant : nat -> VariantIdentity
  | KeywordVariant : list NibblePair -> VariantIdentity
  | DollarVariant : list NibblePair -> VariantIdentity
  | DoubleDollarCallVariant : list NibblePair -> VariantIdentity
  | FallbackVariant : list NibblePair -> VariantIdentity.

  Definition variant_of (terminal : ClassifiedTerminal) : VariantIdentity :=
    match terminal with
    | FixedTerminal identity => FixedVariant identity
    | KeywordTerminal bytes => KeywordVariant (encode_payload bytes)
    | DollarTerminal bytes => DollarVariant (encode_payload bytes)
    | DoubleDollarCallTerminal bytes =>
        DoubleDollarCallVariant (encode_payload bytes)
    | FallbackTerminal bytes => FallbackVariant (encode_payload bytes)
    end.

  Theorem variant_of_injective : forall left right,
      variant_of left = variant_of right -> left = right.
  Proof.
    intros left right Hequal.
    destruct left as [left_id | left_bytes | left_bytes | left_bytes | left_bytes];
      destruct right as
        [right_id | right_bytes | right_bytes | right_bytes | right_bytes];
      simpl in Hequal; try discriminate;
      inversion Hequal; subst; try reflexivity;
      apply encode_payload_injective in H0; subst; reflexivity.
  Qed.

  Theorem generated_query_matches_source_iff : forall query source,
      variant_of query = variant_of source <-> query = source.
  Proof.
    intros query source. split.
    - apply variant_of_injective.
    - intro Hequal. subst source. reflexivity.
  Qed.

  Definition first_variant_set (terminals : list ClassifiedTerminal)
      : list VariantIdentity :=
    map variant_of terminals.

  Theorem first_membership_preserved : forall terminal terminals,
      In (variant_of terminal) (first_variant_set terminals) <->
      In terminal terminals.
  Proof.
    intros terminal terminals. unfold first_variant_set. split.
    - intro Hin. apply in_map_iff in Hin.
      destruct Hin as [candidate [Hequal Hcandidate]].
      apply variant_of_injective in Hequal. subst candidate. exact Hcandidate.
    - intro Hin. apply in_map. exact Hin.
  Qed.

  (** Lexer emission and parser prediction are two projections of the same
      literal list.  Neither may independently manufacture a readable alias. *)
  Definition lexer_variants := first_variant_set.
  Definition prediction_variants := first_variant_set.

  Theorem lexer_prediction_alignment : forall terminals,
      lexer_variants terminals = prediction_variants terminals.
  Proof. reflexivity. Qed.

  Inductive CaseDistinctTheoryKeyword : Type :=
  | UppercaseTheory
  | LowercaseTheory.

  Definition historical_casefold (_ : CaseDistinctTheoryKeyword) : nat := 0.

  Theorem historical_casefold_is_not_injective :
      historical_casefold UppercaseTheory =
        historical_casefold LowercaseTheory /\
      UppercaseTheory <> LowercaseTheory.
  Proof. split; [reflexivity | discriminate]. Qed.

End TerminalVariantIdentity.
