From Stdlib Require Import List PeanoNat.
Import ListNotations.

Definition Token := nat.
Definition Word := list Token.

Fixpoint join_separated (separator : Word) (segments : list Word) : Word :=
  match segments with
  | [] => []
  | [segment] => segment
  | segment :: rest => segment ++ separator ++ join_separated separator rest
  end.

Definition SurfaceCollection
    (element : Word -> Prop) (separator : Word) (word : Word) : Prop :=
  exists segments,
    Forall element segments /\
    word = join_separated separator segments.

Definition SurfaceSeparated
    (element : Word -> Prop) (separator : Word) (word : Word) : Prop :=
  exists first rest,
    element first /\
    Forall element rest /\
    word = join_separated separator (first :: rest).

Inductive NormalizedSeparated
    (element : Word -> Prop) (separator : Word) : Word -> Prop :=
| SeparatedSingleton : forall word,
    element word ->
    NormalizedSeparated element separator word
| SeparatedAppend : forall prefix word,
    NormalizedSeparated element separator prefix ->
    element word ->
    NormalizedSeparated element separator (prefix ++ separator ++ word).

Inductive NormalizedCollection
    (element : Word -> Prop) (separator : Word) : Word -> Prop :=
| CollectionEmpty : NormalizedCollection element separator []
| CollectionNonempty : forall word,
    NormalizedSeparated element separator word ->
    NormalizedCollection element separator word.

Lemma join_separated_snoc :
  forall separator segments last,
    segments <> [] ->
    join_separated separator (segments ++ [last]) =
    join_separated separator segments ++ separator ++ last.
Proof.
  intros separator segments. induction segments as [| first rest IH]; intros last Hnonempty.
  - contradiction.
  - destruct rest as [| second tail].
    + reflexivity.
    + change
        (first ++ separator ++
           join_separated separator ((second :: tail) ++ [last]) =
         (first ++ separator ++ join_separated separator (second :: tail)) ++
           separator ++ last).
      rewrite IH; [| discriminate]. rewrite !app_assoc. reflexivity.
Qed.

Lemma cons_app_singleton :
  forall (A : Type) (first : A) (prefix : list A) (last : A),
    first :: (prefix ++ [last]) = (first :: prefix) ++ [last].
Proof. reflexivity. Qed.

Theorem separated_normalization_sound :
  forall element separator word,
    NormalizedSeparated element separator word ->
    SurfaceSeparated element separator word.
Proof.
  intros element separator word H. induction H.
  - exists word, []. repeat split; try assumption. constructor.
  - destruct IHNormalizedSeparated as [first [rest [Hfirst [Hall Heq]]]].
    exists first, (rest ++ [word]). split; [exact Hfirst |]. split.
    + apply Forall_app. split; [exact Hall |]. constructor; [exact H0 | constructor].
    + change
        (prefix ++ separator ++ word =
         join_separated separator ((first :: rest) ++ [word])).
      rewrite join_separated_snoc; [rewrite Heq; reflexivity | discriminate].
Qed.

Theorem separated_normalization_complete :
  forall element separator word,
    SurfaceSeparated element separator word ->
    NormalizedSeparated element separator word.
Proof.
  intros element separator word [first [rest [Hfirst [Hall Heq]]]]. subst word.
  revert first Hfirst Hall. induction rest using rev_ind; intros first Hfirst Hall.
  - simpl. constructor. exact Hfirst.
  - apply Forall_app in Hall as [Hprefix Hlast].
    inversion Hlast as [| ? ? Hword Hnil]; subst.
    rewrite cons_app_singleton, join_separated_snoc; [| discriminate].
    apply SeparatedAppend; [eauto | exact Hword].
Qed.

Theorem collection_normalization_sound :
  forall element separator word,
    NormalizedCollection element separator word ->
    SurfaceCollection element separator word.
Proof.
  intros element separator word H. destruct H as [| parsed Hnonempty].
  - exists []. split; constructor.
  - apply separated_normalization_sound in Hnonempty.
    destruct Hnonempty as [first [rest [Hfirst [Hall Heq]]]].
    exists (first :: rest). split; [constructor; assumption | exact Heq].
Qed.

Theorem collection_normalization_complete :
  forall element separator word,
    SurfaceCollection element separator word ->
    NormalizedCollection element separator word.
Proof.
  intros element separator word [segments [Hall Heq]].
  destruct segments as [| first rest].
  - subst word. constructor.
  - apply CollectionNonempty. apply separated_normalization_complete.
    exists first, rest. inversion Hall. subst. repeat split; assumption.
Qed.

Inductive SurfaceOptional (body : Word -> Prop) : Word -> Prop :=
| OptionalAbsent : SurfaceOptional body []
| OptionalPresent : forall word, body word -> SurfaceOptional body word.

Inductive NormalizedOptional (body : Word -> Prop) : Word -> Prop :=
| OptionalEmptyRule : NormalizedOptional body []
| OptionalBodyRule : forall word, body word -> NormalizedOptional body word.

Theorem optional_normalization_exact :
  forall body word,
    SurfaceOptional body word <-> NormalizedOptional body word.
Proof.
  intros body word. split; intro H; inversion H; constructor; assumption.
Qed.

Print Assumptions collection_normalization_sound.
Print Assumptions collection_normalization_complete.
Print Assumptions separated_normalization_complete.
