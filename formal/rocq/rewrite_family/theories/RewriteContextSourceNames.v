From Stdlib Require Import Bool PeanoNat.

Inductive SourceToken :=
| IdentifierToken (name : nat)
| KeywordToken (name : nat)
| StringToken (payload : nat)
| NonwordToken (spelling : nat).

Definition token_spelling (token : SourceToken) : nat :=
  match token with
  | IdentifierToken name | KeywordToken name => name
  | StringToken payload => payload
  | NonwordToken spelling => spelling
  end.

Definition classified_token (word_spelling : nat -> bool) (token : SourceToken) : Prop :=
  match token with
  | IdentifierToken _ | StringToken _ => True
  | KeywordToken name => word_spelling name = true
  | NonwordToken spelling => word_spelling spelling = false
  end.

Definition observe_context_name (word_spelling : nat -> bool) (token : SourceToken)
    : option nat :=
  match token with
  | IdentifierToken name => Some name
  | StringToken _ => None
  | _ =>
      if word_spelling (token_spelling token)
      then Some (token_spelling token)
      else None
  end.

Inductive ContextName : SourceToken -> nat -> Prop :=
| IdentifierName : forall name, ContextName (IdentifierToken name) name
| KeywordName : forall name, ContextName (KeywordToken name) name.

Theorem context_name_observation_matches_independent_relation :
  forall word_spelling token name,
    classified_token word_spelling token ->
    (observe_context_name word_spelling token = Some name <-> ContextName token name).
Proof.
  intros word_spelling token name Htable.
  destruct token; simpl in *; try rewrite Htable.
  all: split; intro H; try discriminate; inversion H; subst; try constructor; reflexivity.
Qed.

Print Assumptions context_name_observation_matches_independent_relation.

Theorem context_name_observation_refuses_strings_and_nonwords :
  forall word_spelling payload,
    observe_context_name word_spelling (StringToken payload) = None /\
    (classified_token word_spelling (NonwordToken payload) ->
     observe_context_name word_spelling (NonwordToken payload) = None).
Proof.
  intros word_spelling payload. split.
  - reflexivity.
  - simpl. intro Htable. rewrite Htable. reflexivity.
Qed.

Print Assumptions context_name_observation_refuses_strings_and_nonwords.

Definition checked_context_name
    (word_spelling valid_name : nat -> bool) (token : SourceToken) : option nat :=
  match observe_context_name word_spelling token with
  | Some name => if valid_name name then Some name else None
  | None => None
  end.

Theorem context_name_validation_is_exact :
  forall word_spelling valid_name token name,
    classified_token word_spelling token ->
    (checked_context_name word_spelling valid_name token = Some name <->
     ContextName token name /\ valid_name name = true).
Proof.
  intros word_spelling valid_name token name Htable.
  unfold checked_context_name.
  destruct (observe_context_name word_spelling token) as [observed|] eqn:Hobserve.
  - destruct (valid_name observed) eqn:Hvalid.
    + split.
      * intro H. inversion H; subst. split.
        -- apply (proj1 (context_name_observation_matches_independent_relation _ _ _ Htable)).
           exact Hobserve.
        -- exact Hvalid.
      * intros [Hname Hvalid_name].
        apply (proj2 (context_name_observation_matches_independent_relation _ _ _ Htable)) in Hname.
        rewrite Hobserve in Hname. inversion Hname. reflexivity.
    + split.
      * discriminate.
      * intros [Hname Hvalid_name].
        apply (proj2 (context_name_observation_matches_independent_relation _ _ _ Htable)) in Hname.
        rewrite Hobserve in Hname. inversion Hname; subst.
        rewrite Hvalid in Hvalid_name. discriminate.
  - split.
    + discriminate.
    + intros [Hname _].
      apply (proj2 (context_name_observation_matches_independent_relation _ _ _ Htable)) in Hname.
      rewrite Hobserve in Hname. discriminate.
Qed.

Print Assumptions context_name_validation_is_exact.
