(** The authored Options/Semantics/Limits builder is a typed presentation of
    the nine existing TheoryLimitsV1 fields.  The source-name admission step
    precedes this model: its closed lookup maps only those nine spellings to
    LimitKey, and a checked integer conversion maps values to the canonical
    u32 domain.  This model proves that successful structural accumulation
    retains source order and never silently overrides a repeated key. *)
From Stdlib Require Import List String FunctionalExtensionality.
Import ListNotations.

Module OptionsLimitsProjection.

Inductive LimitKey := RuleVariables | TermNodes | PremiseNodes | ProofNodes
                   | Frontier | Steps | GradeBits | OutputNodes | OutputBytes.

Definition source_name (key : LimitKey) : string :=
  match key with
  | RuleVariables => "max_rule_variables"
  | TermNodes => "max_term_nodes"
  | PremiseNodes => "max_premise_nodes"
  | ProofNodes => "max_proof_nodes"
  | Frontier => "max_frontier"
  | Steps => "max_steps"
  | GradeBits => "max_grade_bits"
  | OutputNodes => "max_output_nodes"
  | OutputBytes => "max_output_bytes"
  end.

Definition decode_source_name (name : string) : option LimitKey :=
  if String.eqb name "max_rule_variables" then Some RuleVariables else
  if String.eqb name "max_term_nodes" then Some TermNodes else
  if String.eqb name "max_premise_nodes" then Some PremiseNodes else
  if String.eqb name "max_proof_nodes" then Some ProofNodes else
  if String.eqb name "max_frontier" then Some Frontier else
  if String.eqb name "max_steps" then Some Steps else
  if String.eqb name "max_grade_bits" then Some GradeBits else
  if String.eqb name "max_output_nodes" then Some OutputNodes else
  if String.eqb name "max_output_bytes" then Some OutputBytes else None.

Theorem every_canonical_limit_name_is_admitted : forall key,
  decode_source_name (source_name key) = Some key.
Proof. destruct key; reflexivity. Qed.

Definition limit_key_eq_dec : forall first second : LimitKey,
  {first = second} + {first <> second}.
Proof. decide equality. Defined.

Definition Entry := (LimitKey * nat)%type.

Fixpoint project (entries : list Entry) : option (list Entry) :=
  match entries with
  | [] => Some []
  | (key, value) :: remaining =>
      match project remaining with
      | None => None
      | Some accepted =>
          if in_dec limit_key_eq_dec key (map fst accepted) then None
          else Some ((key, value) :: accepted)
      end
  end.

Theorem empty_options_preserve_defaults : project [] = Some [].
Proof. reflexivity. Qed.

Theorem successful_projection_is_exact : forall entries accepted,
  project entries = Some accepted -> entries = accepted.
Proof.
  induction entries as [|[key value] remaining IH]; intros accepted H.
  - inversion H. reflexivity.
  - simpl in H.
    destruct (project remaining) as [tail|] eqn:Tail; try discriminate.
    destruct (in_dec limit_key_eq_dec key (map fst tail)); try discriminate.
    inversion H; subst accepted. f_equal. apply IH. reflexivity.
Qed.

Theorem successful_projection_has_unique_keys : forall entries accepted,
  project entries = Some accepted -> NoDup (map fst accepted).
Proof.
  induction entries as [|[key value] remaining IH]; intros accepted H.
  - inversion H; constructor.
  - simpl in H.
    destruct (project remaining) as [tail|] eqn:Tail; try discriminate.
    destruct (in_dec limit_key_eq_dec key (map fst tail)) as [Present|Absent];
      try discriminate.
    inversion H; subst accepted. simpl. constructor.
    + exact Absent.
    + apply IH. reflexivity.
Qed.

Theorem adjacent_duplicate_is_refused : forall key first second,
  project [(key, first); (key, second)] = None.
Proof.
  intros key first second. simpl.
  destruct (in_dec limit_key_eq_dec key []) as [Impossible|_].
  - inversion Impossible.
  - destruct (limit_key_eq_dec key key) as [_|Impossible].
    + reflexivity.
    + exfalso. apply Impossible. reflexivity.
Qed.

(** A TheoryLimitsV1 record is extensionally a total map over the nine keys.
    Its defaults are supplied by the pre-existing theory core; the authored
    Options builder updates only fields it names. *)
Definition Limits := LimitKey -> nat.

Definition apply_entry (limits : Limits) (entry : Entry) : Limits :=
  fun key => if limit_key_eq_dec key (fst entry) then snd entry else limits key.

Definition install (defaults : Limits) (entries : list Entry) : option Limits :=
  match project entries with
  | None => None
  | Some accepted => Some (fold_left apply_entry accepted defaults)
  end.

Theorem one_named_limit_updates_exactly_its_field : forall defaults key value,
  exists result, install defaults [(key, value)] = Some result /\
    result key = value /\
    (forall other, other <> key -> result other = defaults other).
Proof.
  intros defaults key value.
  unfold install, project. simpl.
  destruct (in_dec limit_key_eq_dec key []) as [Impossible|_].
  - inversion Impossible.
  - exists (apply_entry defaults (key, value)).
    split; [reflexivity|].
    split.
    + unfold apply_entry. simpl. destruct (limit_key_eq_dec key key); [reflexivity|contradiction].
    + intros other Different. unfold apply_entry. simpl.
      destruct (limit_key_eq_dec other key); [contradiction|reflexivity].
Qed.

Theorem distinct_named_limits_commute : forall defaults first second first_value second_value,
  first <> second ->
  apply_entry (apply_entry defaults (first, first_value)) (second, second_value) =
  apply_entry (apply_entry defaults (second, second_value)) (first, first_value).
Proof.
  intros defaults first second first_value second_value Different.
  apply functional_extensionality. intro key.
  unfold apply_entry. simpl.
  destruct (limit_key_eq_dec key second) as [Second|NotSecond];
  destruct (limit_key_eq_dec key first) as [First|NotFirst];
    subst; try contradiction; reflexivity.
Qed.

End OptionsLimitsProjection.
