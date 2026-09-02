(**
  SelfHostingFixedPoint: executable proof obligations for the DDL migration
  corpus and the Rholang two-generation bootstrap gate.

  The Rust harness assigns every discovered [language!] occurrence a stable
  natural-number key. A migration manifest is accepted only when its ordered
  keys equal the mechanically discovered non-Rholang keys and those discovery
  keys contain no duplicate. Equality therefore rules out missing, extra,
  exempted, and multiply represented declarations at the same time.

  The bootstrap theorem deliberately starts after the seed generation. A seed
  is only an audited implementation used to obtain generation one. Once
  generation two is byte-identical to generation one, deterministic
  regeneration remains at that fixed point for every later generation.

  Rocq 9.1 compatible. No admitted results, axioms, or assumptions.
*)

From Stdlib Require Import List.
From Stdlib Require Import ListDec.
From Stdlib Require Import PeanoNat.

Import ListNotations.

Module SelfHostingFixedPoint.

Section MigrationCorpus.

  Context {Artifact : Type}.
  Variable source_key : Artifact -> nat.

  Definition verify_inventory
      (declarations : list nat) (artifacts : list Artifact) : bool :=
    if list_eq_dec Nat.eq_dec declarations (map source_key artifacts) then
      if NoDup_dec Nat.eq_dec declarations then true else false
    else false.

  Theorem verify_inventory_sound :
    forall declarations artifacts,
      verify_inventory declarations artifacts = true ->
      map source_key artifacts = declarations /\ NoDup declarations.
  Proof.
    intros declarations artifacts.
    unfold verify_inventory.
    destruct (list_eq_dec Nat.eq_dec declarations (map source_key artifacts))
      as [Heq | Hneq]; [| discriminate].
    destruct (NoDup_dec Nat.eq_dec declarations) as [Hnodup | Hdup];
      [intros _; split; [symmetry; exact Heq | exact Hnodup] | discriminate].
  Qed.

  Lemma nodup_mapped_key_is_injective_on_members :
    forall artifacts left right,
      NoDup (map source_key artifacts) ->
      In left artifacts ->
      In right artifacts ->
      source_key left = source_key right ->
      left = right.
  Proof.
    induction artifacts as [|head tail IH]; intros left right Hnodup Hleft Hright Hkey.
    - contradiction.
    - inversion Hnodup as [|? ? Hhead Htail]; subst.
      simpl in Hleft, Hright.
      destruct Hleft as [Hleft | Hleft]; destruct Hright as [Hright | Hright].
      + now subst.
      + subst left.
        exfalso.
        apply Hhead.
        rewrite Hkey.
        apply in_map.
        exact Hright.
      + subst right.
        exfalso.
        apply Hhead.
        rewrite <- Hkey.
        apply in_map.
        exact Hleft.
      + apply IH; assumption.
  Qed.

  Theorem verified_inventory_has_exactly_one_artifact_per_declaration :
    forall declarations artifacts key,
      verify_inventory declarations artifacts = true ->
      In key declarations ->
      exists! artifact,
        In artifact artifacts /\ source_key artifact = key.
  Proof.
    intros declarations artifacts key Hverified Hkey.
    pose proof (verify_inventory_sound declarations artifacts Hverified)
      as [Hkeys Hnodup].
    assert (Hin : In key (map source_key artifacts)).
    { rewrite Hkeys. exact Hkey. }
    apply in_map_iff in Hin.
    destruct Hin as [artifact [Hartifact_key Hartifact_in]].
    exists artifact.
    split.
    - split; [exact Hartifact_in | exact Hartifact_key].
    - intros other [Hother_in Hother_key].
      apply nodup_mapped_key_is_injective_on_members
        with (artifacts := artifacts).
      + rewrite Hkeys. exact Hnodup.
      + exact Hartifact_in.
      + exact Hother_in.
      + rewrite Hartifact_key. symmetry. exact Hother_key.
  Qed.

  Theorem verified_inventory_has_no_extra_artifact :
    forall declarations artifacts artifact,
      verify_inventory declarations artifacts = true ->
      In artifact artifacts ->
      In (source_key artifact) declarations.
  Proof.
    intros declarations artifacts artifact Hverified Hin.
    pose proof (verify_inventory_sound declarations artifacts Hverified)
      as [Hkeys _].
    rewrite <- Hkeys.
    apply in_map.
    exact Hin.
  Qed.

End MigrationCorpus.

Section Bootstrap.

  Context {Bundle : Type}.
  Variable regenerate : Bundle -> Bundle.

  Fixpoint iterate (count : nat) (bundle : Bundle) : Bundle :=
    match count with
    | 0 => bundle
    | S rest => regenerate (iterate rest bundle)
    end.

  Definition two_generation_fixed (seed : Bundle) : Prop :=
    regenerate (regenerate seed) = regenerate seed.

  Theorem fixed_point_persists :
    forall bundle,
      regenerate bundle = bundle ->
      forall count, iterate count bundle = bundle.
  Proof.
    intros bundle Hfixed count.
    induction count as [|count IH]; simpl; [reflexivity |].
    now rewrite IH.
  Qed.

  Theorem two_generation_check_implies_all_later_generations :
    forall seed,
      two_generation_fixed seed ->
      forall count, iterate (S count) seed = regenerate seed.
  Proof.
    intros seed Hfixed count.
    induction count as [|count IH].
    - reflexivity.
    - change (regenerate (iterate (S count) seed) = regenerate seed).
    rewrite IH.
    exact Hfixed.
  Qed.

End Bootstrap.

Section DiverseChecking.

  Context {Bundle Digest Meaning : Type}.
  Variable canonical_meaning : Bundle -> Meaning.
  Variable digest_meaning : Meaning -> Digest.
  Variables checker_a checker_b : Bundle -> option Digest.

  Definition checker_sound (checker : Bundle -> option Digest) : Prop :=
    forall bundle digest,
      checker bundle = Some digest ->
      digest = digest_meaning (canonical_meaning bundle).

  Definition diverse_agreement (bundle : Bundle) (digest : Digest) : Prop :=
    checker_a bundle = Some digest /\ checker_b bundle = Some digest.

  Theorem diverse_agreement_is_canonical :
    checker_sound checker_a ->
    checker_sound checker_b ->
    forall bundle digest,
      diverse_agreement bundle digest ->
      digest = digest_meaning (canonical_meaning bundle).
  Proof.
    intros Hsound_a _ bundle digest [Haccepted_a _].
    now apply Hsound_a with (bundle := bundle).
  Qed.

  Theorem diverse_agreement_has_no_checker_disagreement :
    forall bundle digest,
      diverse_agreement bundle digest ->
      checker_a bundle = checker_b bundle.
  Proof.
    intros bundle digest [Haccepted_a Haccepted_b].
    now rewrite Haccepted_a, Haccepted_b.
  Qed.

End DiverseChecking.

End SelfHostingFixedPoint.
