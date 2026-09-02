From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.

Record Token : Type := {
  token_mode : nat;
  token_priority : nat;
  token_id : nat
}.

Definition owned_by (mode : nat) (token : Token) : Prop := token_mode token = mode.

Definition owned_byb (mode : nat) (token : Token) : bool :=
  Nat.eqb (token_mode token) mode.

Definition accepting_state_validb (mode : nat) (tokens : list Token) : bool :=
  forallb (owned_byb mode) tokens.

Theorem verified_accepting_state_has_only_mode_tokens :
  forall mode tokens token,
    accepting_state_validb mode tokens = true ->
    In token tokens ->
    owned_by mode token.
Proof.
  intros mode tokens token Hvalid Hin.
  unfold accepting_state_validb in Hvalid.
  rewrite forallb_forall in Hvalid. specialize (Hvalid token Hin).
  unfold owned_byb, owned_by in *. apply Nat.eqb_eq. exact Hvalid.
Qed.

Definition precedes (left right : Token) : Prop :=
  token_priority right < token_priority left \/
  (token_priority left = token_priority right /\ token_id left <= token_id right).

Fixpoint canonical_accepts (tokens : list Token) : Prop :=
  match tokens with
  | [] | [_] => True
  | first :: ((second :: _) as rest) =>
      precedes first second /\ canonical_accepts rest
  end.

Definition selected (tokens : list Token) : option Token :=
  match tokens with
  | [] => None
  | token :: _ => Some token
  end.

Theorem canonical_head_precedes_second :
  forall first second rest,
    canonical_accepts (first :: second :: rest) -> precedes first second.
Proof.
  intros first second rest H. simpl in H. exact (proj1 H).
Qed.

Theorem nonempty_accepts_selects_a_member :
  forall token rest,
    selected (token :: rest) = Some token /\ In token (token :: rest).
Proof.
  intros. split; simpl; auto.
Qed.

(** Extending a grammar must distinguish lexical ownership from contextual
    parser admission.  Every identifier-shaped literal has one fixed lexical
    reading.  A parser position may additionally admit that fixed token as a
    name without adding an [IdentifierReading] edge to the token lattice.

    A newly introduced spelling is admitted in host identifier positions to
    preserve programs that used it as a name before the extension.  An
    inherited fixed spelling remains excluded from host identifier positions.
    It may be admitted in an extension-specific name position only by an
    explicit promotion, as required for a constructor label such as [PPar]. *)
Section ExtensionKeywordOwnership.
  Inductive KeywordOrigin : Type :=
  | InheritedFixedKeyword
  | ExtensionKeyword.

  Inductive KeywordReading : Type :=
  | FixedKeywordReading
  | IdentifierReading.

  Inductive IdentifierContext : Type :=
  | HostIdentifierContext
  | ExtensionIdentifierContext.

  Definition keyword_readings (_ : KeywordOrigin) : list KeywordReading :=
    [FixedKeywordReading].

  Definition allows_identifier
      (origin : KeywordOrigin) (context : IdentifierContext)
      (promote_inherited_in_extension : bool) : bool :=
    match origin, context with
    | ExtensionKeyword, _ => true
    | InheritedFixedKeyword, HostIdentifierContext => false
    | InheritedFixedKeyword, ExtensionIdentifierContext =>
        promote_inherited_in_extension
    end.

  Definition capture_as_identifier
      (origin : KeywordOrigin) (context : IdentifierContext)
      (promote_inherited_in_extension : bool) (reading : KeywordReading) : bool :=
    match reading with
    | FixedKeywordReading =>
        allows_identifier origin context promote_inherited_in_extension
    | IdentifierReading => false
    end.

  Theorem keyword_lexical_ownership_is_singleton :
    forall origin,
      keyword_readings origin = [FixedKeywordReading].
  Proof.
    intros []; reflexivity.
  Qed.

  Theorem inherited_host_delimiter_is_not_an_identifier :
    forall promotion,
      capture_as_identifier InheritedFixedKeyword HostIdentifierContext
        promotion FixedKeywordReading = false.
  Proof.
    intros []; reflexivity.
  Qed.

  Theorem extension_keyword_preserves_host_identifier_use :
    forall promotion,
      capture_as_identifier ExtensionKeyword HostIdentifierContext
        promotion FixedKeywordReading = true.
  Proof.
    intros []; reflexivity.
  Qed.

  Theorem inherited_extension_promotion_is_scoped :
    capture_as_identifier InheritedFixedKeyword ExtensionIdentifierContext
      true FixedKeywordReading = true /\
    capture_as_identifier InheritedFixedKeyword HostIdentifierContext
      true FixedKeywordReading = false.
  Proof.
    split; reflexivity.
  Qed.

  Theorem contextual_capture_adds_no_identifier_edge :
    forall origin context promotion,
      ~ In IdentifierReading (keyword_readings origin) /\
      capture_as_identifier origin context promotion IdentifierReading = false.
  Proof.
    intros origin context promotion; split.
    - simpl. intros [Heq | Hin]; [discriminate | contradiction].
    - reflexivity.
  Qed.
End ExtensionKeywordOwnership.

Print Assumptions verified_accepting_state_has_only_mode_tokens.
Print Assumptions canonical_head_precedes_second.
Print Assumptions nonempty_accepts_selects_a_member.
Print Assumptions keyword_lexical_ownership_is_singleton.
Print Assumptions inherited_host_delimiter_is_not_an_identifier.
Print Assumptions extension_keyword_preserves_host_identifier_use.
Print Assumptions inherited_extension_promotion_is_scoped.
Print Assumptions contextual_capture_adds_no_identifier_edge.
