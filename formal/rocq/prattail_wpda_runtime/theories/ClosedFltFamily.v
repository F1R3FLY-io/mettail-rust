(** A closed FLT is one term, not a parallel composition of parse readings.

    The original WPDA may return several weighted derivations of an identical
    structural term. The construction boundary inspects the entire admitted
    family and publishes that term only when every reading has the same
    syntax AND value. A distinct reading is rejected here, never silently
    elected by order or weight. The parser's weighted family remains intact;
    this theorem concerns only the closed-term publication boundary.

    Source correspondence: RholangLanguageRuntime::construct_template_with_budget
    compares the stack-safe DynamicValue syntax and value of every parse with
    the first reading before reflecting exactly one term. Resource exhaustion
    and empty families remain errors, not success. *)
From Stdlib Require Import List Bool.
Import ListNotations.

Module ClosedFltFamilyLaws.
Section Family.
Context {Syntax Value Weight : Type}.
Variable syntax_eq_dec : forall x y : Syntax, {x = y} + {x <> y}.
Variable value_eq_dec : forall x y : Value, {x = y} + {x <> y}.

Record Reading := reading {
  syntax : Syntax;
  value : Value;
  weight : Weight
}.

Definition same_term (left right : Reading) : bool :=
  if syntax_eq_dec (syntax left) (syntax right) then
    if value_eq_dec (value left) (value right) then true else false
  else false.

Definition close_family (readings : list Reading) : option Reading :=
  match readings with
  | [] => None
  | first :: rest =>
      if forallb (same_term first) rest then Some first else None
  end.

Lemma same_term_sound : forall left right,
  same_term left right = true ->
  syntax left = syntax right /\ value left = value right.
Proof.
  intros left right H.
  unfold same_term in H.
  destruct (syntax_eq_dec (syntax left) (syntax right)) as [Hs | Hs];
    [| discriminate].
  destruct (value_eq_dec (value left) (value right)) as [Hv | Hv];
    [| discriminate].
  now split.
Qed.

Theorem published_term_is_every_reading : forall readings selected member,
  close_family readings = Some selected ->
  In member readings ->
  syntax member = syntax selected /\ value member = value selected.
Proof.
  intros [| first rest] selected member Hclose Hin; [discriminate|].
  unfold close_family in Hclose.
  destruct (forallb (same_term first) rest) eqn:Hagree;
    [inversion Hclose; subst selected|discriminate].
  simpl in Hin.
  destruct Hin as [Heq | Hin]; [subst member; auto|].
  apply forallb_forall with (x := member) in Hagree; [|assumption].
  apply same_term_sound in Hagree.
  destruct Hagree as [Hs Hv].
  now split; symmetry.
Qed.

Theorem distinct_term_cannot_be_published : forall readings left right selected,
  In left readings -> In right readings ->
  (syntax left <> syntax right \/ value left <> value right) ->
  close_family readings <> Some selected.
Proof.
  intros readings left right selected Hleft Hright Hdiff Hclose.
  pose proof (published_term_is_every_reading _ _ _ Hclose Hleft) as [Hls Hlv].
  pose proof (published_term_is_every_reading _ _ _ Hclose Hright) as [Hrs Hrv].
  destruct Hdiff as [Hs | Hv].
  - apply Hs. now rewrite Hls, Hrs.
  - apply Hv. now rewrite Hlv, Hrv.
Qed.

Theorem duplicate_derivations_do_not_block_publication : forall first rest,
  (forall member, In member rest ->
    syntax member = syntax first /\ value member = value first) ->
  close_family (first :: rest) = Some first.
Proof.
  intros first rest Hall.
  unfold close_family.
  assert (Hagree : forallb (same_term first) rest = true).
  { apply forallb_forall. intros member Hin.
    destruct (Hall member Hin) as [Hs Hv].
    unfold same_term.
    destruct (syntax_eq_dec (syntax first) (syntax member)) as [_ | Hcontra];
      [|exfalso; apply Hcontra; symmetry; exact Hs].
    destruct (value_eq_dec (value first) (value member)) as [_ | Hcontra];
      [reflexivity|exfalso; apply Hcontra; symmetry; exact Hv]. }
  now rewrite Hagree.
Qed.
End Family.
Print Assumptions published_term_is_every_reading.
Print Assumptions distinct_term_cannot_be_published.
Print Assumptions duplicate_derivations_do_not_block_publication.
End ClosedFltFamilyLaws.
