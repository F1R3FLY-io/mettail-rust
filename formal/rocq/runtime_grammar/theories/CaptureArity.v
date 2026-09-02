From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.

Inductive Semantic : Type :=
| Reduce : nat -> Semantic
| EmptyOptional : nat -> Semantic
| PresentOptional : nat -> Semantic
| EmptyCollection : nat -> Semantic
| SingletonCollection : nat -> Semantic
| AppendCollection : nat -> Semantic
| FinalizeCollection : nat -> Semantic
| Tuple : nat -> Semantic
| UnitSlots : nat -> Semantic.

Definition expected_captures (semantic : Semantic) : option nat :=
  match semantic with
  | Reduce arity => Some arity
  | EmptyOptional _ | EmptyCollection _ | UnitSlots _ => Some 0
  | PresentOptional slots | SingletonCollection slots => Some slots
  | AppendCollection slots => Some (slots + slots)
  | FinalizeCollection slots => Some slots
  | Tuple slots => Some slots
  end.

Definition output_arity (semantic : Semantic) : nat :=
  match semantic with
  | Reduce _ | Tuple _ => 1
  | EmptyOptional slots | PresentOptional slots | UnitSlots slots => slots
  | EmptyCollection slots
  | SingletonCollection slots
  | AppendCollection slots
  | FinalizeCollection slots => slots
  end.

Inductive CapturedSymbol : Type :=
| Uncaptured : CapturedSymbol
| CapturedTerminal : CapturedSymbol
| CapturedNonterminal : nat -> CapturedSymbol.

Fixpoint capture_width (symbols : list CapturedSymbol) : nat :=
  match symbols with
  | [] => 0
  | Uncaptured :: rest => capture_width rest
  | CapturedTerminal :: rest => S (capture_width rest)
  | CapturedNonterminal width :: rest => width + capture_width rest
  end.

Lemma capture_width_app :
  forall left right,
    capture_width (left ++ right) = capture_width left + capture_width right.
Proof.
  induction left as [| symbol rest IH]; intros right; simpl.
  - lia.
  - destruct symbol; simpl; rewrite IH; lia.
Qed.

Definition semantic_validb (captures : nat) (semantic : Semantic) : bool :=
  match expected_captures semantic with
  | None => true
  | Some expected => Nat.eqb captures expected
  end.

Theorem verified_semantic_has_exact_capture_arity :
  forall captures semantic expected,
    semantic_validb captures semantic = true ->
    expected_captures semantic = Some expected ->
    captures = expected.
Proof.
  intros captures semantic expected Hvalid Hexpected.
  unfold semantic_validb in Hvalid. rewrite Hexpected in Hvalid.
  apply Nat.eqb_eq. exact Hvalid.
Qed.

Theorem captured_nonterminal_contributes_declared_output_width :
  forall prefix suffix semantic,
    capture_width
      (prefix ++ CapturedNonterminal (output_arity semantic) :: suffix) =
    capture_width prefix + output_arity semantic + capture_width suffix.
Proof.
  intros. rewrite capture_width_app. simpl. lia.
Qed.

Record MappedCollection : Type := {
  source_slots : nat;
  binding_count : nat;
  body_captures : nat
}.

Definition mapped_collection_validb (mapped : MappedCollection) : bool :=
  Nat.eqb (source_slots mapped) (binding_count mapped) &&
  Nat.eqb (binding_count mapped) (body_captures mapped).

Theorem mapped_collection_preserves_slot_arity :
  forall mapped,
    mapped_collection_validb mapped = true ->
    source_slots mapped = body_captures mapped.
Proof.
  intros mapped Hvalid. unfold mapped_collection_validb in Hvalid.
  apply andb_true_iff in Hvalid as [Hsource Hbody].
  apply Nat.eqb_eq in Hsource. apply Nat.eqb_eq in Hbody. lia.
Qed.

Definition zip_validb (left_slots right_slots bindings : nat) : bool :=
  Nat.eqb left_slots 1 && Nat.eqb right_slots 1 && Nat.eqb bindings 2.

Theorem valid_zip_has_two_lockstep_outputs :
  forall left_slots right_slots bindings,
    zip_validb left_slots right_slots bindings = true ->
    left_slots + right_slots = bindings.
Proof.
  intros left_slots right_slots bindings Hvalid.
  unfold zip_validb in Hvalid.
  repeat rewrite andb_true_iff in Hvalid.
  destruct Hvalid as [[Hleft Hright] Hbindings].
  apply Nat.eqb_eq in Hleft.
  apply Nat.eqb_eq in Hright.
  apply Nat.eqb_eq in Hbindings.
  lia.
Qed.

Print Assumptions verified_semantic_has_exact_capture_arity.
Print Assumptions captured_nonterminal_contributes_declared_output_width.
Print Assumptions mapped_collection_preserves_slot_arity.
Print Assumptions valid_zip_has_two_lockstep_outputs.
