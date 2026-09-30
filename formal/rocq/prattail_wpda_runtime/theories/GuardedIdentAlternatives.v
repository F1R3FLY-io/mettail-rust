(** A guarded identifier scan observes every lexical edge at its current
    position, rather than only the preferred edge. The lexer supplies at most
    one longest edge per token kind, but this model does not require that
    invariant: even a source with several identifier edges retains them all.

    This is a local selection proof. It does not assert whole-parser
    correctness, SPPF reconstruction, or lexical-weight parity. *)
From Stdlib Require Import List Bool Arith.
Import ListNotations.

Module GuardedIdentAlternatives.
Inductive Kind := Ident | Other (tag : nat).
Record Edge := {
  kind : Kind;
  next_position : nat;
  spelling : list nat
}.

Definition is_ident (edge : Edge) : bool :=
  match kind edge with Ident => true | Other _ => false end.
Definition guarded_ident_edges (edges : list Edge) : list Edge :=
  filter is_ident edges.

Theorem guarded_ident_sound_complete : forall edges edge,
  In edge (guarded_ident_edges edges) <->
  In edge edges /\ kind edge = Ident.
Proof.
  intros edges edge; unfold guarded_ident_edges.
  rewrite filter_In; split.
  - intros [Hinside Hkind]; split; [exact Hinside |].
    unfold is_ident in Hkind; destruct (kind edge); [reflexivity | discriminate].
  - intros [Hinside Hkind]; split; [exact Hinside |].
    unfold is_ident; now rewrite Hkind.
Qed.

Theorem preferred_keyword_does_not_hide_identifier : forall keyword identifier,
  kind keyword <> Ident -> kind identifier = Ident ->
  guarded_ident_edges [keyword; identifier] = [identifier].
Proof.
  intros keyword identifier Hkeyword Hidentifier.
  unfold guarded_ident_edges, is_ident; simpl.
  destruct (kind keyword); [contradiction |].
  now rewrite Hidentifier.
Qed.

Theorem primary_identifier_unchanged : forall identifier,
  kind identifier = Ident -> guarded_ident_edges [identifier] = [identifier].
Proof.
  intros identifier Hidentifier; unfold guarded_ident_edges, is_ident; simpl.
  now rewrite Hidentifier.
Qed.

Theorem every_matching_successor_survives : forall edges edge,
  In edge edges -> kind edge = Ident ->
  In (next_position edge) (map next_position (guarded_ident_edges edges)).
Proof.
  intros edges edge Hinside Hkind; apply in_map.
  apply guarded_ident_sound_complete; now split.
Qed.
End GuardedIdentAlternatives.
