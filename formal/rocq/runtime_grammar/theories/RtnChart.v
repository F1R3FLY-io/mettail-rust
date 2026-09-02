From Stdlib Require Import List PeanoNat.
From RuntimeGrammar Require Import ImageAdmission.
Import ListNotations.

Definition Token := nat.
Definition Word := list Token.

Inductive Delimited (open close : Token) : Word -> Prop :=
| DelimitedRegion : forall content,
    Delimited open close (open :: content ++ [close]).

Inductive Derives (grammar : list Rule) : nat -> Word -> Prop :=
| DeriveRule : forall rule word,
    In rule grammar ->
    DerivesSymbols grammar (rhs rule) word ->
    Derives grammar (lhs rule) word
with DerivesSymbols (grammar : list Rule) : list Symbol -> Word -> Prop :=
| DeriveEmpty : DerivesSymbols grammar [] []
| DeriveScan : forall token symbols word,
    DerivesSymbols grammar symbols word ->
    DerivesSymbols grammar (Scan token :: symbols) (token :: word)
| DeriveCall : forall nonterminal symbols child suffix,
    Derives grammar nonterminal child ->
    DerivesSymbols grammar symbols suffix ->
    DerivesSymbols grammar (Call nonterminal :: symbols) (child ++ suffix)
| DeriveForeign : forall open close symbols region suffix,
    Delimited open close region ->
    DerivesSymbols grammar symbols suffix ->
    DerivesSymbols grammar (Foreign open close :: symbols) (region ++ suffix).

Scheme Derives_ind' := Induction for Derives Sort Prop
with DerivesSymbols_ind' := Induction for DerivesSymbols Sort Prop.
Combined Scheme derivation_mutind from Derives_ind', DerivesSymbols_ind'.

Lemma derives_symbols_append :
  forall grammar left left_word,
    DerivesSymbols grammar left left_word ->
    forall right right_word,
      DerivesSymbols grammar right right_word ->
      DerivesSymbols grammar (left ++ right) (left_word ++ right_word).
Proof.
  intros grammar left left_word Hleft.
  induction Hleft; intros right right_word Hright; simpl.
  - exact Hright.
  - constructor. apply IHHleft. exact Hright.
  - replace ((child ++ suffix) ++ right_word)
      with (child ++ (suffix ++ right_word)) by apply app_assoc.
    eapply DeriveCall with (child := child) (suffix := suffix ++ right_word).
    + exact H.
    + apply IHHleft. exact Hright.
  - replace ((region ++ suffix) ++ right_word)
      with (region ++ (suffix ++ right_word)) by apply app_assoc.
    eapply DeriveForeign with (region := region) (suffix := suffix ++ right_word).
    + exact H.
    + apply IHHleft. exact Hright.
Qed.

Record Item : Type := {
  item_rule : Rule;
  before_dot : list Symbol;
  after_dot : list Symbol;
  consumed : Word
}.

Definition item_sound (grammar : list Rule) (item : Item) : Prop :=
  In (item_rule item) grammar /\
  rhs (item_rule item) = before_dot item ++ after_dot item /\
  DerivesSymbols grammar (before_dot item) (consumed item).

Definition complete_item (item : Item) : Prop := after_dot item = [].

Definition advance_scan_item (item : Item) (token : Token) (rest : list Symbol) : Item :=
  {| item_rule := item_rule item;
     before_dot := before_dot item ++ [Scan token];
     after_dot := rest;
     consumed := consumed item ++ [token] |}.

Definition advance_call_item
    (item : Item) (nonterminal : nat) (rest : list Symbol) (child_word : Word) : Item :=
  {| item_rule := item_rule item;
     before_dot := before_dot item ++ [Call nonterminal];
     after_dot := rest;
     consumed := consumed item ++ child_word |}.

Theorem seed_item_is_sound :
  forall grammar rule,
    In rule grammar ->
    item_sound grammar
      {| item_rule := rule; before_dot := []; after_dot := rhs rule; consumed := [] |}.
Proof.
  intros grammar rule Hin. split; [exact Hin |]. split; [reflexivity | constructor].
Qed.

Theorem scan_preserves_item_soundness :
  forall grammar item token rest,
    item_sound grammar item ->
    after_dot item = Scan token :: rest ->
    item_sound grammar (advance_scan_item item token rest).
Proof.
  intros grammar item token rest [Hin [Hrhs Hbefore]] Hafter.
  assert (Hadvanced :
    rhs (item_rule item) = (before_dot item ++ [Scan token]) ++ rest).
  {
    rewrite Hrhs, Hafter, <- app_assoc. reflexivity.
  }
  unfold advance_scan_item. simpl. split; [exact Hin |]. split.
  - exact Hadvanced.
  - apply derives_symbols_append with (left_word := consumed item).
    + exact Hbefore.
    + constructor. constructor.
Qed.

Theorem completed_item_denotes_derivation :
  forall grammar item,
    item_sound grammar item ->
    complete_item item ->
    Derives grammar (lhs (item_rule item)) (consumed item).
Proof.
  intros grammar item [Hin [Hrhs Hbefore]] Hcomplete.
  unfold complete_item in Hcomplete. rewrite Hcomplete, app_nil_r in Hrhs.
  apply DeriveRule with (rule := item_rule item); [exact Hin |].
  rewrite Hrhs. exact Hbefore.
Qed.

Theorem completion_preserves_item_soundness :
  forall grammar waiting child nonterminal rest,
    item_sound grammar waiting ->
    after_dot waiting = Call nonterminal :: rest ->
    item_sound grammar child ->
    complete_item child ->
    lhs (item_rule child) = nonterminal ->
    item_sound grammar
      (advance_call_item waiting nonterminal rest (consumed child)).
Proof.
  intros grammar waiting child nonterminal rest
    [Hwaiting [Hwaiting_rhs Hwaiting_before]] Hafter
    Hchild Hcomplete Hlhs.
  assert (Hadvanced :
    rhs (item_rule waiting) =
      (before_dot waiting ++ [Call nonterminal]) ++ rest).
  {
    rewrite Hwaiting_rhs, Hafter, <- app_assoc. reflexivity.
  }
  unfold advance_call_item. simpl. split; [exact Hwaiting |]. split.
  - exact Hadvanced.
  - apply derives_symbols_append with (left_word := consumed waiting).
    + exact Hwaiting_before.
    + replace (consumed child) with (consumed child ++ []) by apply app_nil_r.
      apply DeriveCall.
      * rewrite <- Hlhs. apply completed_item_denotes_derivation; assumption.
      * constructor.
Qed.

Theorem every_derivation_has_a_sound_completed_item :
  forall grammar nonterminal word,
    Derives grammar nonterminal word ->
    exists item,
      item_sound grammar item /\
      complete_item item /\
      lhs (item_rule item) = nonterminal /\
      consumed item = word.
Proof.
  intros grammar nonterminal word Hderive. destruct Hderive as [rule parsed Hin Hsymbols].
  exists {| item_rule := rule;
            before_dot := rhs rule;
            after_dot := [];
            consumed := parsed |}.
  split.
  - unfold item_sound. simpl. split; [exact Hin |]. split.
    + rewrite app_nil_r. reflexivity.
    + exact Hsymbols.
  - split; [reflexivity |]. split; reflexivity.
Qed.

Theorem sound_completed_item_iff_derivation :
  forall grammar nonterminal word,
    Derives grammar nonterminal word <->
    exists item,
      item_sound grammar item /\
      complete_item item /\
      lhs (item_rule item) = nonterminal /\
      consumed item = word.
Proof.
  intros grammar nonterminal word. split.
  - apply every_derivation_has_a_sound_completed_item.
  - intros [item [Hsound [Hcomplete [Hlhs Hword]]]].
    rewrite <- Hlhs, <- Hword. apply completed_item_denotes_derivation; assumption.
Qed.

Print Assumptions scan_preserves_item_soundness.
Print Assumptions completion_preserves_item_soundness.
Print Assumptions sound_completed_item_iff_derivation.
