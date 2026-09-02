From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.

Inductive Symbol : Type :=
| Scan : nat -> Symbol
| Call : nat -> Symbol
| Foreign : nat -> nat -> Symbol.

Record Rule : Type := {
  lhs : nat;
  rhs : list Symbol;
  production : option nat
}.

Record Core : Type := {
  core_fingerprint : nat;
  category_count : nat;
  token_count : nat;
  production_count : nat;
  normalized_nonterminal_count : nat;
  normalized_starts : list nat;
  normalized_rules : list Rule
}.

Record Image : Type := {
  image_fingerprint : nat;
  executable : bool;
  exact : bool;
  nonterminal_count : nat;
  starts : list nat;
  rules : list Rule
}.

Definition symbol_valid (core : Core) (image : Image) (symbol : Symbol) : Prop :=
  match symbol with
  | Scan token => token < token_count core
  | Call nonterminal => nonterminal < nonterminal_count image
  | Foreign open close => open <> close
  end.

Definition rule_valid (core : Core) (image : Image) (rule : Rule) : Prop :=
  lhs rule < nonterminal_count image /\
  Forall (symbol_valid core image) (rhs rule) /\
  match production rule with
  | None => True
  | Some id => id < production_count core /\ lhs rule < category_count core
  end.

Definition Symbol_eq_dec : forall left right : Symbol, {left = right} + {left <> right}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition Rule_eq_dec : forall left right : Rule, {left = right} + {left <> right}.
Proof.
  decide equality.
  - decide equality. apply Nat.eq_dec.
  - apply list_eq_dec. exact Symbol_eq_dec.
  - apply Nat.eq_dec.
Defined.

Definition exact_normalization (core : Core) (image : Image) : Prop :=
  nonterminal_count image = normalized_nonterminal_count core /\
  starts image = normalized_starts core /\
  rules image = normalized_rules core.

Definition exact_normalizationb (core : Core) (image : Image) : bool :=
  Nat.eqb (nonterminal_count image) (normalized_nonterminal_count core) &&
  (if list_eq_dec Nat.eq_dec (starts image) (normalized_starts core)
   then true else false) &&
  (if list_eq_dec Rule_eq_dec (rules image) (normalized_rules core)
   then true else false).

Definition image_valid (core : Core) (image : Image) : Prop :=
  image_fingerprint image = core_fingerprint core /\
  executable image = true /\
  exact image = true /\
  category_count core <= nonterminal_count image /\
  Forall (fun start => start < category_count core) (starts image) /\
  Forall (rule_valid core image) (rules image) /\
  (forall id, id < production_count core ->
    exists rule, In rule (rules image) /\ production rule = Some id) /\
  exact_normalization core image.

Definition symbol_validb (core : Core) (image : Image) (symbol : Symbol) : bool :=
  match symbol with
  | Scan token => Nat.ltb token (token_count core)
  | Call nonterminal => Nat.ltb nonterminal (nonterminal_count image)
  | Foreign open close => negb (Nat.eqb open close)
  end.

Definition production_validb (core : Core) (image : Image) (rule : Rule) : bool :=
  match production rule with
  | None => true
  | Some id =>
      Nat.ltb id (production_count core) &&
      Nat.ltb (lhs rule) (category_count core)
  end.

Definition rule_validb (core : Core) (image : Image) (rule : Rule) : bool :=
  Nat.ltb (lhs rule) (nonterminal_count image) &&
  forallb (symbol_validb core image) (rhs rule) &&
  production_validb core image rule.

Definition production_coveredb (image : Image) (id : nat) : bool :=
  existsb
    (fun rule =>
       match production rule with
       | None => false
       | Some candidate => Nat.eqb candidate id
       end)
    (rules image).

Definition verify_image (core : Core) (image : Image) : bool :=
  Nat.eqb (image_fingerprint image) (core_fingerprint core) &&
  executable image &&
  exact image &&
  Nat.leb (category_count core) (nonterminal_count image) &&
  forallb (fun start => Nat.ltb start (category_count core)) (starts image) &&
  forallb (rule_validb core image) (rules image) &&
  forallb (production_coveredb image) (seq 0 (production_count core)) &&
  exact_normalizationb core image.

Definition metadata_only (image : Image) : Prop := executable image = false.

Definition admitted (core : Core) (image : Image) : option Image :=
  if Nat.eqb (image_fingerprint image) (core_fingerprint core)
  then if executable image && exact image then Some image else None
  else None.

Definition admit_executable (core : Core) (image : Image) : option Image :=
  if verify_image core image then Some image else None.

Lemma symbol_validb_sound :
  forall core image symbol,
    symbol_validb core image symbol = true ->
    symbol_valid core image symbol.
Proof.
  intros core image symbol H. destruct symbol; simpl in *.
  - apply Nat.ltb_lt. exact H.
  - apply Nat.ltb_lt. exact H.
  - apply negb_true_iff in H. apply Nat.eqb_neq. exact H.
Qed.

Lemma rule_validb_sound :
  forall core image rule,
    rule_validb core image rule = true ->
    rule_valid core image rule.
Proof.
  intros core image rule H. unfold rule_validb in H.
  apply andb_true_iff in H as [H Hproduction].
  apply andb_true_iff in H as [Hlhs Hsymbols].
  split; [apply Nat.ltb_lt; exact Hlhs |]. split.
  - rewrite forallb_forall in Hsymbols. rewrite Forall_forall.
    intros symbol Hin. apply symbol_validb_sound. apply Hsymbols. exact Hin.
  - unfold production_validb in Hproduction.
    destruct (production rule) as [id|] eqn:Hid; [| exact I].
    apply andb_true_iff in Hproduction as [Hid_bound Hcategory].
    split; apply Nat.ltb_lt; assumption.
Qed.

Lemma exact_normalizationb_sound :
  forall core image,
    exact_normalizationb core image = true ->
    exact_normalization core image.
Proof.
  intros core image H. unfold exact_normalizationb in H.
  apply andb_true_iff in H as [H Hrules].
  apply andb_true_iff in H as [Hcount Hstarts].
  unfold exact_normalization. repeat split.
  - apply Nat.eqb_eq. exact Hcount.
  - destruct (list_eq_dec Nat.eq_dec (starts image) (normalized_starts core));
      [assumption | discriminate].
  - destruct (list_eq_dec Rule_eq_dec (rules image) (normalized_rules core));
      [assumption | discriminate].
Qed.

Theorem verify_image_sound :
  forall core image,
    verify_image core image = true ->
    image_valid core image.
Proof.
  intros core image Hverify. unfold verify_image in Hverify.
  apply andb_true_iff in Hverify as [Hverify Hnormalization].
  apply andb_true_iff in Hverify as [Hverify Hcoverage].
  apply andb_true_iff in Hverify as [Hverify Hrules].
  apply andb_true_iff in Hverify as [Hverify Hstarts].
  apply andb_true_iff in Hverify as [Hverify Hcategories].
  apply andb_true_iff in Hverify as [Hverify Hexact].
  apply andb_true_iff in Hverify as [Hfingerprint Hexecutable].
  unfold image_valid. split.
  - apply Nat.eqb_eq. exact Hfingerprint.
  - split; [exact Hexecutable |].
    split; [exact Hexact |].
    split; [apply Nat.leb_le; exact Hcategories |].
    split.
    + rewrite Forall_forall. intros start Hin.
      apply Nat.ltb_lt. rewrite forallb_forall in Hstarts. apply Hstarts. exact Hin.
    + split.
      * rewrite Forall_forall. intros rule Hin.
        apply rule_validb_sound. rewrite forallb_forall in Hrules. apply Hrules. exact Hin.
      * split.
        -- intros id Hid. rewrite forallb_forall in Hcoverage.
    assert (Hin : In id (seq 0 (production_count core))).
    { apply in_seq. lia. }
    specialize (Hcoverage id Hin). unfold production_coveredb in Hcoverage.
    rewrite existsb_exists in Hcoverage.
    destruct Hcoverage as [rule [Hrule Hproduction]]. exists rule. split; [exact Hrule |].
    destruct (production rule) as [candidate|] eqn:Hcandidate; try discriminate.
    apply Nat.eqb_eq in Hproduction. subst candidate. reflexivity.
        -- apply exact_normalizationb_sound. exact Hnormalization.
Qed.

Theorem executable_admission_is_safe :
  forall core image admitted_image,
    admit_executable core image = Some admitted_image ->
    admitted_image = image /\ image_valid core admitted_image.
Proof.
  intros core image admitted_image H. unfold admit_executable in H.
  destruct (verify_image core image) eqn:Hverify; try discriminate.
  inversion H. subst admitted_image. split; [reflexivity |].
  apply verify_image_sound. exact Hverify.
Qed.

Theorem admission_checks_authoritative_identity :
  forall core image admitted_image,
    admitted core image = Some admitted_image ->
    image_fingerprint image = core_fingerprint core.
Proof.
  intros core image admitted_image H.
  unfold admitted in H. destruct (Nat.eqb _ _) eqn:Heq; [| discriminate].
  apply Nat.eqb_eq. exact Heq.
Qed.

Theorem admission_checks_executable_exact :
  forall core image admitted_image,
    admitted core image = Some admitted_image ->
    executable image = true /\ exact image = true.
Proof.
  intros core image admitted_image H.
  unfold admitted in H. destruct (Nat.eqb _ _); [| discriminate].
  destruct (executable image && exact image) eqn:Hflags; [| discriminate].
  apply andb_true_iff. exact Hflags.
Qed.

Theorem metadata_is_never_admitted :
  forall core image,
    metadata_only image -> admitted core image = None.
Proof.
  intros core image Hmetadata. unfold metadata_only in Hmetadata.
  unfold admitted. destruct (Nat.eqb _ _); [rewrite Hmetadata |]; reflexivity.
Qed.

Theorem stale_image_is_never_admitted :
  forall core image,
    image_fingerprint image <> core_fingerprint core ->
    admitted core image = None.
Proof.
  intros core image Hstale. unfold admitted.
  destruct (Nat.eqb _ _) eqn:Heq; [apply Nat.eqb_eq in Heq; contradiction | reflexivity].
Qed.

Theorem valid_image_start_is_a_category :
  forall core image start,
    image_valid core image -> In start (starts image) -> start < category_count core.
Proof.
  intros core image start [_ [_ [_ [_ [Hstarts _]]]]] Hin.
  rewrite Forall_forall in Hstarts. apply Hstarts. exact Hin.
Qed.

Theorem valid_image_rule_symbols_are_bounded :
  forall core image rule symbol,
    image_valid core image ->
    In rule (rules image) ->
    In symbol (rhs rule) ->
    symbol_valid core image symbol.
Proof.
  intros core image rule symbol [_ [_ [_ [_ [_ [Hrules _]]]]]] Hrule Hsymbol.
  rewrite Forall_forall in Hrules. specialize (Hrules rule Hrule).
  destruct Hrules as [_ [Hsymbols _]]. rewrite Forall_forall in Hsymbols.
  apply Hsymbols. exact Hsymbol.
Qed.

Theorem valid_image_covers_every_production :
  forall core image id,
    image_valid core image -> id < production_count core ->
    exists rule, In rule (rules image) /\ production rule = Some id.
Proof.
  intros core image id [_ [_ [_ [_ [_ [_ [Hcoverage _]]]]]]]. apply Hcoverage.
Qed.

Theorem admitted_executable_is_canonical_normalization :
  forall core image admitted_image,
    admit_executable core image = Some admitted_image ->
    exact_normalization core admitted_image.
Proof.
  intros core image admitted_image Hadmitted.
  pose proof (executable_admission_is_safe _ _ _ Hadmitted) as [_ Hvalid].
  destruct Hvalid as [_ [_ [_ [_ [_ [_ [_ Hnormalization]]]]]]].
  exact Hnormalization.
Qed.

Print Assumptions metadata_is_never_admitted.
Print Assumptions executable_admission_is_safe.
Print Assumptions admitted_executable_is_canonical_normalization.
Print Assumptions valid_image_rule_symbols_are_bounded.
Print Assumptions valid_image_covers_every_production.
