(*
 * Funding-decision conformance for the MeTTaIL GSLT adapter.
 *
 * The merged host's delta_sigma::is_funded accepts precisely a certified
 * finite upper bound that fits the effective supply. `unknown` means that
 * structural analysis has no finite certificate; no numeric safety margin
 * turns that into a proof. Production may instead use independently checked
 * state-bound evidence. This file models the finite structural decision,
 * not that state-bound evidence and not the Rust implementation itself.
 *
 * The adapter delegates to the host checker. These laws are the abstract
 * obligations exercised concretely in rholang-adapter/src/conformance.rs.
 * No Admitted, Axiom, or unproved correspondence claim is used.
 *)

From Stdlib Require Import PeanoNat Arith Bool Lia.

Section MettaFundingLaws.

  Definition is_funded (bound supply : nat) (unknown : bool) : bool :=
    negb unknown && Nat.leb bound supply.

  Theorem law_sound : forall bound supply unknown,
    is_funded bound supply unknown = true
      <-> unknown = false /\ bound <= supply.
  Proof.
    intros bound supply unknown.
    unfold is_funded.
    rewrite andb_true_iff, negb_true_iff, Nat.leb_le.
    tauto.
  Qed.

  Theorem law_unknown_rejects : forall bound supply,
    is_funded bound supply true = false.
  Proof.
    intros. reflexivity.
  Qed.

  Theorem law_reject_underfunded : forall bound supply,
    supply < bound -> is_funded bound supply false = false.
  Proof.
    intros bound supply H.
    unfold is_funded. simpl. apply Nat.leb_gt. exact H.
  Qed.

  Theorem law_supply_monotone : forall bound supply unknown,
    is_funded bound supply unknown = true
      -> is_funded bound (S supply) unknown = true.
  Proof.
    intros bound supply unknown H.
    apply law_sound in H as [Hknown Hbound].
    apply law_sound. split; [exact Hknown | lia].
  Qed.

  Theorem law_decidable : forall bound supply unknown,
    is_funded bound supply unknown = true
      \/ is_funded bound supply unknown = false.
  Proof.
    intros. destruct (is_funded bound supply unknown); auto.
  Qed.

  Theorem metta_resource_logic_is_funding_sound :
    (forall bound supply unknown,
      is_funded bound supply unknown = true
        <-> unknown = false /\ bound <= supply)
    /\ (forall bound supply, is_funded bound supply true = false)
    /\ (forall bound supply, supply < bound
          -> is_funded bound supply false = false)
    /\ (forall bound supply unknown,
          is_funded bound supply unknown = true
          -> is_funded bound (S supply) unknown = true)
    /\ (forall bound supply unknown,
          is_funded bound supply unknown = true
          \/ is_funded bound supply unknown = false).
  Proof.
    split. { exact law_sound. }
    split. { exact law_unknown_rejects. }
    split. { exact law_reject_underfunded. }
    split. { exact law_supply_monotone. }
    exact law_decidable.
  Qed.

End MettaFundingLaws.
