From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Definition Byte := nat.
Definition Token := nat.

Record Dfa : Type := {
  start_state : nat;
  transition : nat -> Byte -> option nat;
  accepting : nat -> list Token
}.

Fixpoint run_from
    (step : nat -> Byte -> option nat) (state : nat) (input : list Byte)
    : option nat :=
  match input with
  | [] => Some state
  | byte :: rest =>
      match step state byte with
      | Some next => run_from step next rest
      | None => None
      end
  end.

Definition run (dfa : Dfa) (input : list Byte) : option nat :=
  run_from (transition dfa) (start_state dfa) input.

Definition accepting_length (dfa : Dfa) (input : list Byte) (count : nat) : Prop :=
  count <= length input /\
  exists state,
    run dfa (firstn count input) = Some state /\
    accepting dfa state <> [].

Definition maximal_accepting_length
    (dfa : Dfa) (input : list Byte) (count : nat) : Prop :=
  accepting_length dfa input count /\
  forall other, accepting_length dfa input other -> other <= count.

Record LexChoice (dfa : Dfa) (input : list Byte) : Type := {
  choice_length : nat;
  choice_state : nat;
  choice_tokens : list Token;
  choice_positive : 0 < choice_length;
  choice_run : run dfa (firstn choice_length input) = Some choice_state;
  choice_accepting : choice_tokens = accepting dfa choice_state;
  choice_nonempty : choice_tokens <> [];
  choice_maximal : maximal_accepting_length dfa input choice_length
}.

Theorem transition_is_deterministic :
  forall dfa state byte left right,
    transition dfa state byte = Some left ->
    transition dfa state byte = Some right ->
    left = right.
Proof.
  intros dfa state byte left right Hleft Hright.
  rewrite Hleft in Hright. inversion Hright. reflexivity.
Qed.

Theorem run_is_deterministic :
  forall dfa input left right,
    run dfa input = Some left ->
    run dfa input = Some right ->
    left = right.
Proof.
  intros dfa input left right Hleft Hright.
  rewrite Hleft in Hright. inversion Hright. reflexivity.
Qed.

Theorem maximal_accepting_length_unique :
  forall dfa input left right,
    maximal_accepting_length dfa input left ->
    maximal_accepting_length dfa input right ->
    left = right.
Proof.
  intros dfa input left right [Hleft Hleft_max] [Hright Hright_max].
  apply Nat.le_antisymm; [apply Hright_max | apply Hleft_max]; assumption.
Qed.

Theorem lex_choice_length_unique :
  forall dfa input (left right : LexChoice dfa input),
    choice_length dfa input left = choice_length dfa input right.
Proof.
  intros dfa input left right.
  exact (maximal_accepting_length_unique
    dfa input (choice_length dfa input left) (choice_length dfa input right)
    (choice_maximal dfa input left) (choice_maximal dfa input right)).
Qed.

Theorem lex_choice_tokens_unique :
  forall dfa input (left right : LexChoice dfa input),
    choice_tokens dfa input left = choice_tokens dfa input right.
Proof.
  intros dfa input left right.
  pose proof (lex_choice_length_unique dfa input left right) as Hlength.
  destruct left as [ll ls lt lp lr la ln lm].
  destruct right as [rl rs rt rp rr ra rn rm]. simpl in *.
  subst rl. rewrite lr in rr. inversion rr. subst rs.
  rewrite la, ra. reflexivity.
Qed.

Theorem lex_choice_makes_progress :
  forall dfa input (choice : LexChoice dfa input),
    choice_length dfa input choice > 0 /\
    choice_length dfa input choice <= length input.
Proof.
  intros dfa input choice. split.
  - apply choice_positive.
  - destruct (choice_maximal dfa input choice) as [[Hbounded _] _]. exact Hbounded.
Qed.

Theorem no_zero_length_token_can_be_selected :
  forall dfa input (choice : LexChoice dfa input),
    choice_length dfa input choice <> 0.
Proof.
  intros dfa input choice Hzero.
  pose proof (choice_positive dfa input choice). lia.
Qed.

Print Assumptions transition_is_deterministic.
Print Assumptions lex_choice_tokens_unique.
Print Assumptions no_zero_length_token_can_be_selected.
