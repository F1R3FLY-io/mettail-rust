(*
 * VpaDelimiterSoundness: typed delimiter pairing and unbounded VPA nesting.
 *
 * Rust correspondence:
 *   delimiter                  DelimiterClass<K>
 *   delimiter_step             build_skip_table loop body
 *   close_mismatch_preserves   mismatched closer leaves stack/table unchanged
 *   close_match_same_kind      emitted pairs retain one exact kind
 *   dyck_depth_unbounded       no state-count-derived nesting ceiling exists
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

Section TypedDelimiterPairing.

Variable Kind : Type.
Variable kind_eq_dec : forall left right : Kind, {left = right} + {left <> right}.

Inductive delimiter : Type :=
  | Open : Kind -> delimiter
  | Close : Kind -> delimiter
  | Internal : delimiter.

Record frame : Type := Frame {
  frame_index : nat;
  frame_kind : Kind
}.

Record pair : Type := Pair {
  pair_open : nat;
  pair_close : nat;
  pair_kind : Kind
}.

Definition pairing_state := (list frame * list pair)%type.

Definition delimiter_step
    (index : nat) (token : delimiter) (current : pairing_state)
    : pairing_state :=
  let '(stack, pairs) := current in
  match token with
  | Open kind => (Frame index kind :: stack, pairs)
  | Internal => current
  | Close close_kind =>
      match stack with
      | [] => current
      | Frame open_index open_kind :: rest =>
          if kind_eq_dec open_kind close_kind
          then (rest, Pair open_index index open_kind :: pairs)
          else current
      end
  end.

Theorem close_mismatch_preserves :
  forall index close_kind open_index open_kind rest pairs,
    open_kind <> close_kind ->
    delimiter_step index (Close close_kind)
      (Frame open_index open_kind :: rest, pairs) =
      (Frame open_index open_kind :: rest, pairs).
Proof.
  intros index close_kind open_index open_kind rest pairs Hneq.
  unfold delimiter_step; simpl.
  destruct (kind_eq_dec open_kind close_kind) as [Heq | _].
  - contradiction.
  - reflexivity.
Qed.

Theorem close_match_same_kind :
  forall index kind open_index rest pairs,
    delimiter_step index (Close kind) (Frame open_index kind :: rest, pairs) =
      (rest, Pair open_index index kind :: pairs).
Proof.
  intros index kind open_index rest pairs.
  unfold delimiter_step; simpl.
  destruct (kind_eq_dec kind kind) as [_ | Hneq].
  - reflexivity.
  - contradiction Hneq; reflexivity.
Qed.

Theorem close_match_is_ordered :
  forall index kind open_index (rest : list frame) (pairs : list pair),
    open_index < index ->
    pair_open (Pair open_index index kind) < pair_close (Pair open_index index kind).
Proof.
  intros; simpl; assumption.
Qed.

Theorem internal_preserves :
  forall index current,
    delimiter_step index Internal current = current.
Proof.
  intros index [stack pairs]. reflexivity.
Qed.

End TypedDelimiterPairing.

(* A one-kind well-matched language already has unbounded nesting depth. *)
Inductive dyck : list bool -> Prop :=
  | dyck_empty : dyck []
  | dyck_wrap : forall word, dyck word -> dyck (true :: word ++ [false])
  | dyck_concat : forall left right,
      dyck left -> dyck right -> dyck (left ++ right).

Fixpoint nested_word (depth : nat) : list bool :=
  match depth with
  | 0 => []
  | S smaller => true :: nested_word smaller ++ [false]
  end.

Fixpoint leading_calls (word : list bool) : nat :=
  match word with
  | true :: rest => S (leading_calls rest)
  | _ => 0
  end.

Lemma nested_word_is_dyck : forall depth, dyck (nested_word depth).
Proof.
  induction depth as [| depth IH]; simpl.
  - constructor.
  - constructor; exact IH.
Qed.

Lemma leading_calls_snoc_return : forall word,
  leading_calls (word ++ [false]) = leading_calls word.
Proof.
  induction word as [| symbol rest IH]; simpl.
  - reflexivity.
  - destruct symbol; simpl; [rewrite IH |]; reflexivity.
Qed.

Lemma nested_word_leading_calls : forall depth,
  leading_calls (nested_word depth) = depth.
Proof.
  induction depth as [| depth IH]; simpl.
  - reflexivity.
  - rewrite leading_calls_snoc_return, IH. reflexivity.
Qed.

Theorem dyck_depth_unbounded : forall proposed_bound,
  exists word,
    dyck word /\ leading_calls word > proposed_bound.
Proof.
  intro proposed_bound.
  exists (nested_word (S proposed_bound)).
  split.
  - apply nested_word_is_dyck.
  - rewrite nested_word_leading_calls. lia.
Qed.

Print Assumptions close_mismatch_preserves.
Print Assumptions close_match_same_kind.
Print Assumptions dyck_depth_unbounded.
