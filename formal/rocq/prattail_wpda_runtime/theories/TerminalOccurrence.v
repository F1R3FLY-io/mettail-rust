(** Selected lexical occurrences survive existing terminal interning and
    action reconstruction. An origin is a source-local accepted-edge index,
    not a guessed token family, text hash, decoder, or authority.

    The unchanged static entry uses None. The owned source supplies Some id
    only from the edge selected by the original walker. Parent positions and
    this index are retained independently. The existing lexer, interner, and
    semantic decoder remain workers; this model does not prove their bodies.
*)
From Stdlib Require Import List Arith.
Import ListNotations.
Module TerminalOccurrence.
Section Identity.
Context {OldKey Payload : Type}.
Definition key (old : OldKey) (origin : option nat) := (old, origin).
Theorem legacy_identity : forall a b,
  key a None = key b None <-> a = b.
Proof. intros; split; intro H; [now inversion H | now subst]. Qed.
Theorem selected_occurrences_do_not_collapse : forall a b i j,
  i <> j -> key a (Some i) <> key b (Some j).
Proof. intros a b i j H E; inversion E; contradiction. Qed.
Theorem origins_are_not_legacy : forall a b i,
  key a (Some i) <> key b None.
Proof. intros a b i E; discriminate E. Qed.
Definition reconstruct (terminal : OldKey * option nat) := snd terminal.
Theorem reconstruct_retains_origin : forall old origin,
  reconstruct (key old origin) = origin.
Proof. reflexivity. Qed.
Definition resolve (edges : list Payload) (origin : option nat) :=
  match origin with Some i => nth_error edges i | None => None end.
Theorem selected_decoder_input_is_exact : forall edges i value,
  nth_error edges i = Some value -> resolve edges (Some i) = Some value.
Proof. auto. Qed.
Theorem absent_origin_is_not_guessed : forall edges,
  resolve edges None = None.
Proof. reflexivity. Qed.
Theorem invalid_origin_is_not_guessed : forall edges i,
  nth_error edges i = None -> resolve edges (Some i) = None.
Proof. auto. Qed.
End Identity.
Print Assumptions legacy_identity.
Print Assumptions selected_occurrences_do_not_collapse.
Print Assumptions origins_are_not_legacy.
Print Assumptions reconstruct_retains_origin.
Print Assumptions selected_decoder_input_is_exact.
Print Assumptions absent_origin_is_not_guessed.
Print Assumptions invalid_origin_is_not_guessed.
End TerminalOccurrence.
