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


Module EntryContext.

Inductive Action := Keep | Push (mode : nat) | Pop.

Definition initial (mode : nat) := [mode].

Definition step (stack : list nat) (action : Action) : option (list nat) :=
  match stack with
  | [] => None
  | _ :: rest =>
      match action with
      | Keep => Some stack
      | Push mode => Some (mode :: stack)
      | Pop => match rest with [] => None | _ :: _ => Some rest end
      end
  end.

Fixpoint run (stack : list nat) (actions : list Action) : option (list nat) :=
  match actions with
  | [] => Some stack
  | action :: rest =>
      match step stack action with
      | Some next => run next rest
      | None => None
      end
  end.

Definition complete (entry : nat) (stack : list nat) : bool :=
  match stack with
  | [mode] => Nat.eqb entry mode
  | _ => false
  end.

Definition skip_layout (raw : bool) := negb raw.

Theorem initial_mode_is_active : forall mode, hd 0 (initial mode) = mode.
Proof. reflexivity. Qed.

Theorem empty_fragment_preserves_entry : forall mode,
  run (initial mode) [] = Some (initial mode) /\ complete mode (initial mode) = true.
Proof. intros. split; [reflexivity | apply Nat.eqb_refl]. Qed.

Theorem ordinary_token_keeps_context : forall mode rest,
  step (mode :: rest) Keep = Some (mode :: rest).
Proof. reflexivity. Qed.

Theorem nested_region_restores_context : forall entry rest nested,
  run (entry :: rest) [Push nested; Pop] = Some (entry :: rest).
Proof. reflexivity. Qed.

Theorem fragment_cannot_pop_entry : forall entry,
  step (initial entry) Pop = None.
Proof. reflexivity. Qed.

Theorem failed_transition_cannot_recover : forall stack action rest,
  step stack action = None -> run stack (action :: rest) = None.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Theorem completion_requires_original_context : forall entry stack,
  complete entry stack = true <-> stack = initial entry.
Proof.
  intros entry stack. destruct stack as [|mode rest]; simpl.
  - split; discriminate.
  - destruct rest as [|next rest]; simpl.
    + rewrite Nat.eqb_eq. split; intro H; [subst | inversion H]; reflexivity.
    + split; discriminate.
Qed.

Theorem unclosed_region_rejects : forall entry nested rest,
  complete entry (nested :: entry :: rest) = false.
Proof. reflexivity. Qed.

Theorem raw_mode_preserves_layout : skip_layout true = false.
Proof. reflexivity. Qed.

Theorem ordinary_mode_skips_layout : skip_layout false = true.
Proof. reflexivity. Qed.

Theorem token_ownership_is_independent_of_entry : forall entry mode token,
  owned_by mode token -> owned_by (hd entry [mode]) token.
Proof. intros. exact H. Qed.

Print Assumptions initial_mode_is_active.
Print Assumptions empty_fragment_preserves_entry.
Print Assumptions ordinary_token_keeps_context.
Print Assumptions nested_region_restores_context.
Print Assumptions fragment_cannot_pop_entry.
Print Assumptions failed_transition_cannot_recover.
Print Assumptions completion_requires_original_context.
Print Assumptions unclosed_region_rejects.
Print Assumptions raw_mode_preserves_layout.
Print Assumptions ordinary_mode_skips_layout.
Print Assumptions token_ownership_is_independent_of_entry.

Definition display_boundary (raw requested : bool) : list nat :=
  if raw then [] else if requested then [32] else [].

Definition display_separator (raw : bool) (declared : list nat) :=
  if raw then declared else [32] ++ declared ++ [32].

Theorem raw_boundary_adds_no_bytes : forall requested,
  display_boundary true requested = [].
Proof. reflexivity. Qed.

Theorem ordinary_boundary_preserves_request : forall requested,
  display_boundary false requested = if requested then [32] else [].
Proof. reflexivity. Qed.

Theorem raw_separator_preserves_declared_bytes : forall declared,
  display_separator true declared = declared.
Proof. reflexivity. Qed.

Theorem ordinary_separator_preserves_layout : forall declared,
  display_separator false declared = [32] ++ declared ++ [32].
Proof. reflexivity. Qed.

Theorem raw_frame_preserves_payload : forall open payload close before after,
  open ++ display_boundary true before ++ payload ++ display_boundary true after ++ close =
  open ++ payload ++ close.
Proof. reflexivity. Qed.

Print Assumptions raw_boundary_adds_no_bytes.
Print Assumptions ordinary_boundary_preserves_request.
Print Assumptions raw_separator_preserves_declared_bytes.
Print Assumptions ordinary_separator_preserves_layout.
Print Assumptions raw_frame_preserves_payload.

End EntryContext.
