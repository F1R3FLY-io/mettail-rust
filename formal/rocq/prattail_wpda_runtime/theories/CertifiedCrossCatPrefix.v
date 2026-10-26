(*
 * A one-token prefix certificate is only issued when every derivation of the
 * selected lexical edge begins with a complete atom.  Any longer source
 * derivation must first consume a declared extension operator.  This model
 * states that premise explicitly; the grammar analysis that issues the
 * certificate must fail open if it cannot establish it.
 *
 * A cross-category LHS then needs either its target operator immediately
 * after the atom, or a source extension operator there.  Rejection examines
 * all alternatives at the selected edge's successor, never merely the
 * primary token or a later occurrence of the target operator.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
Import ListNotations.

Section CertifiedCrossCatPrefix.

  Variable token : Type.
  Variable first target : token.
  Variable extensions : list token.

  Inductive certified_source : list token -> Prop :=
  | source_atom : certified_source [first]
  | source_extend : forall source operator suffix,
      certified_source source ->
      In operator extensions ->
      certified_source (source ++ operator :: suffix).

  Lemma certified_source_first_follow :
    forall source,
      certified_source source ->
      source = [first] \/
      exists operator suffix,
        source = first :: operator :: suffix /\ In operator extensions.
  Proof.
    intros source derivation.
    induction derivation as
      [| source operator suffix _ IH operator_in_extensions].
    - left; reflexivity.
    - right. destruct IH as [single | [earliest [rest [shape member]]]].
      + subst source. exists operator, suffix. simpl.
        split; [reflexivity | exact operator_in_extensions].
      + subst source. exists earliest, (rest ++ operator :: suffix).
        simpl. split; [reflexivity | exact member].
  Qed.

  Definition relevant (candidate : token) : Prop :=
    candidate = target \/ In candidate extensions.

  Theorem accepted_crosscat_requires_immediate_evidence :
    forall source remainder trailing alternatives next,
      certified_source source ->
      first :: next :: remainder = source ++ target :: trailing ->
      In next alternatives ->
      exists candidate, In candidate alternatives /\ relevant candidate.
  Proof.
    intros source remainder trailing alternatives next derivation equation next_in.
    exists next. split; [exact next_in |].
    destruct (certified_source_first_follow source derivation)
      as [single | [operator [suffix [shape member]]]].
    - subst source. simpl in equation. inversion equation; subst.
      left; reflexivity.
    - subst source. simpl in equation. inversion equation; subst.
      right; exact member.
  Qed.

  Corollary rejected_successor_has_no_crosscat_derivation :
    forall source remainder trailing alternatives next,
      certified_source source ->
      first :: next :: remainder = source ++ target :: trailing ->
      In next alternatives ->
      (forall candidate, In candidate alternatives -> ~ relevant candidate) ->
      False.
  Proof.
    intros source remainder trailing alternatives next derivation equation next_in rejected.
    destruct (accepted_crosscat_requires_immediate_evidence
      source remainder trailing alternatives next derivation equation next_in)
      as [candidate [candidate_in evidence]].
    exact (rejected candidate candidate_in evidence).
  Qed.

  Lemma unknown_certificate_keeps_branch :
    forall (certified : bool), certified = false -> negb certified = true.
  Proof. intros [] H; discriminate || reflexivity. Qed.

End CertifiedCrossCatPrefix.
