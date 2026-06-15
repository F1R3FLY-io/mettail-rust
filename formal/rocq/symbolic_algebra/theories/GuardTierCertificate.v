(*
 * GuardTierCertificate: the decidability-tier lattice carried by guard
 * dispositions, and its correspondence with Heyting regularity.
 *
 * A guard's decision procedure is classified by a tier (guard_codegen.rs
 * GuardTier {T1Static, T2Decidable, T3Bounded, T4Assert}; the richer
 * DecidabilityTier in symbolic.rs:1440). Combining guards takes the WEAKER tier
 * (`tier_max` = the join in the ≤ order T1 ≤ T2 ≤ T3 ≤ T4 of *decreasing*
 * guarantee strength), exactly as `max_tier` does in the macro layer.
 *
 * This file proves, zero-admission:
 *   - `tier_le` is a decidable total order and `tier_max` is its least upper
 *     bound (a join-semilattice: associative, commutative, idempotent).
 *   - the per-tier GUARANTEE: each tier fixes whether its decision is sound and
 *     complete — T1/T2 exact, T3 bounded (sound only), T4 trusted (asserted).
 *   - the combination HOMOMORPHISM: the guarantee of a combined guard is the
 *     conjunction (meet) of the components' guarantees —
 *     `tier_max_sound_hom` / `tier_max_complete_hom`. So `max_tier` degrades the
 *     guarantee exactly as the weakest leg dictates; soundness is preserved
 *     through T3, lost only at T4.
 *   - the TIER ↔ REGULARITY correspondence (the Esakia-space reading of
 *     HeytingAlgebra.v): T1/T2 = regular/clopen (the exact Boolean core), T3 =
 *     boundary (sound-only; the ¬¬φ ∖ φ gap, Sat3::DontKnow), T4 = closed
 *     (refutable-only / trusted). `tier_regularity_*` tie each class to its
 *     decision guarantee.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.

(* The four guard tiers, in increasing order of WEAKNESS (decreasing
   decidability strength): T1 static < T2 decidable < T3 bounded < T4 asserted. *)
Inductive Tier := T1 | T2 | T3 | T4.

Definition tier_idx (t : Tier) : nat :=
  match t with T1 => 0 | T2 => 1 | T3 => 2 | T4 => 3 end.

Definition tier_le (a b : Tier) : bool := Nat.leb (tier_idx a) (tier_idx b).
Definition tier_max (a b : Tier) : Tier := if tier_le a b then b else a.

(* ===================================================================== *)
(*  Order and join-semilattice laws                                      *)
(* ===================================================================== *)

Lemma tier_le_refl : forall a, tier_le a a = true.
Proof. intro a; unfold tier_le; apply Nat.leb_refl. Qed.

Lemma tier_le_antisym : forall a b, tier_le a b = true -> tier_le b a = true -> a = b.
Proof.
  intros a b Hab Hba. unfold tier_le in *.
  apply Nat.leb_le in Hab, Hba.
  assert (Hidx : tier_idx a = tier_idx b) by (apply Nat.le_antisymm; assumption).
  destruct a, b; simpl in Hidx; try reflexivity; discriminate.
Qed.

Lemma tier_le_trans : forall a b c,
  tier_le a b = true -> tier_le b c = true -> tier_le a c = true.
Proof.
  intros a b c Hab Hbc. unfold tier_le in *.
  apply Nat.leb_le in Hab, Hbc. apply Nat.leb_le.
  apply (Nat.le_trans _ _ _ Hab Hbc).
Qed.

Lemma tier_le_total : forall a b, tier_le a b = true \/ tier_le b a = true.
Proof.
  intros a b. unfold tier_le.
  destruct (Nat.leb (tier_idx a) (tier_idx b)) eqn:E; [left; reflexivity|].
  right. apply Nat.leb_le. apply Nat.leb_gt in E. apply Nat.lt_le_incl. exact E.
Qed.

Lemma tier_max_comm : forall a b, tier_max a b = tier_max b a.
Proof.
  intros a b. unfold tier_max.
  destruct (tier_le a b) eqn:Eab, (tier_le b a) eqn:Eba; try reflexivity.
  - apply tier_le_antisym; assumption.
  - destruct (tier_le_total a b) as [H|H]; [rewrite H in Eab | rewrite H in Eba];
      discriminate.
Qed.

Lemma tier_max_idem : forall a, tier_max a a = a.
Proof. intro a; unfold tier_max; rewrite tier_le_refl; reflexivity. Qed.

Lemma tier_max_ub_l : forall a b, tier_le a (tier_max a b) = true.
Proof.
  intros a b. unfold tier_max. destruct (tier_le a b) eqn:E.
  - exact E.
  - apply tier_le_refl.
Qed.

Lemma tier_max_ub_r : forall a b, tier_le b (tier_max a b) = true.
Proof.
  intros a b. unfold tier_max. destruct (tier_le a b) eqn:E.
  - apply tier_le_refl.
  - destruct (tier_le_total a b) as [H|H]; [rewrite H in E; discriminate|].
    exact H.
Qed.

Lemma tier_max_least : forall a b c,
  tier_le a c = true -> tier_le b c = true -> tier_le (tier_max a b) c = true.
Proof.
  intros a b c Hac Hbc. unfold tier_max. destruct (tier_le a b); assumption.
Qed.

Lemma tier_max_assoc : forall a b c,
  tier_max a (tier_max b c) = tier_max (tier_max a b) c.
Proof.
  intros a b c. apply tier_le_antisym.
  - apply tier_max_least.
    + apply (tier_le_trans a (tier_max a b) (tier_max (tier_max a b) c)).
      * apply tier_max_ub_l.
      * apply tier_max_ub_l.
    + apply tier_max_least.
      * apply (tier_le_trans b (tier_max a b) (tier_max (tier_max a b) c)).
        -- apply tier_max_ub_r.
        -- apply tier_max_ub_l.
      * apply tier_max_ub_r.
  - apply tier_max_least.
    + apply tier_max_least.
      * apply tier_max_ub_l.
      * apply (tier_le_trans b (tier_max b c) (tier_max a (tier_max b c))).
        -- apply tier_max_ub_l.
        -- apply tier_max_ub_r.
    + apply (tier_le_trans c (tier_max b c) (tier_max a (tier_max b c))).
      * apply tier_max_ub_r.
      * apply tier_max_ub_r.
Qed.

(* ===================================================================== *)
(*  Per-tier guarantee and the combination homomorphism                  *)
(* ===================================================================== *)

(* Whether a tier's decision procedure is sound / complete w.r.t. the guard's
   true denotation. T1/T2 are exact; T3 is bounded (sound, may be incomplete);
   T4 is an asserted/trusted guard (no static guarantee). *)
Definition tsound (t : Tier) : bool :=
  match t with T1 | T2 | T3 => true | T4 => false end.
Definition tcomplete (t : Tier) : bool :=
  match t with T1 | T2 => true | T3 | T4 => false end.

Theorem tier_max_sound_hom : forall a b,
  tsound (tier_max a b) = tsound a && tsound b.
Proof. intros a b; destruct a, b; reflexivity. Qed.

Theorem tier_max_complete_hom : forall a b,
  tcomplete (tier_max a b) = tcomplete a && tcomplete b.
Proof. intros a b; destruct a, b; reflexivity. Qed.

(* A combined guard is exact iff both legs are exact. *)
Corollary tier_max_exact : forall a b,
  (tsound (tier_max a b) && tcomplete (tier_max a b))
  = (tsound a && tcomplete a) && (tsound b && tcomplete b).
Proof.
  intros a b. rewrite tier_max_sound_hom, tier_max_complete_hom.
  destruct a, b; reflexivity.
Qed.

(* Soundness is preserved through T3 and lost only when some leg is T4. *)
Corollary tier_max_sound_unless_assert : forall a b,
  tsound (tier_max a b) = true <-> (a <> T4 /\ b <> T4).
Proof.
  intros a b. rewrite tier_max_sound_hom. split.
  - intro H. apply andb_true_iff in H. destruct H as [Ha Hb].
    split; intro Heq; subst; discriminate.
  - intros [Ha Hb]. apply andb_true_iff. split.
    + destruct a; try reflexivity. exfalso; apply Ha; reflexivity.
    + destruct b; try reflexivity. exfalso; apply Hb; reflexivity.
Qed.

(* ===================================================================== *)
(*  Tier ↔ regularity correspondence (Esakia space, HeytingAlgebra.v)    *)
(* ===================================================================== *)

(* Regular/clopen (exact Boolean core), Boundary (sound-only; the ¬¬φ∖φ gap =
   Sat3::DontKnow), Closed (refutable-only / trusted). *)
Inductive Regularity := Reg | Boundary | Closed.

Definition tier_regularity (t : Tier) : Regularity :=
  match t with T1 | T2 => Reg | T3 => Boundary | T4 => Closed end.

Theorem tier_regularity_reg : forall t,
  tier_regularity t = Reg <-> (tsound t = true /\ tcomplete t = true).
Proof.
  intro t. destruct t; simpl; split.
  - intros _. split; reflexivity.       (* T1 -> *)
  - intros _. reflexivity.              (* T1 <- *)
  - intros _. split; reflexivity.       (* T2 -> *)
  - intros _. reflexivity.              (* T2 <- *)
  - intro H. discriminate.              (* T3 -> (Boundary=Reg) *)
  - intros [_ H2]. discriminate.        (* T3 <- (tcomplete=false) *)
  - intro H. discriminate.              (* T4 -> (Closed=Reg) *)
  - intros [H1 _]. discriminate.        (* T4 <- (tsound=false) *)
Qed.

Theorem tier_regularity_boundary : forall t,
  tier_regularity t = Boundary <-> (tsound t = true /\ tcomplete t = false).
Proof.
  intro t. destruct t; simpl; split.
  - intro H. discriminate.              (* T1 -> (Reg=Boundary) *)
  - intros [_ H2]. discriminate.        (* T1 <- (tcomplete=false vs true) *)
  - intro H. discriminate.              (* T2 -> *)
  - intros [_ H2]. discriminate.        (* T2 <- *)
  - intros _. split; reflexivity.       (* T3 -> *)
  - intros _. reflexivity.              (* T3 <- *)
  - intro H. discriminate.              (* T4 -> (Closed=Boundary) *)
  - intros [H1 _]. discriminate.        (* T4 <- (tsound=false) *)
Qed.

Theorem tier_regularity_closed : forall t,
  tier_regularity t = Closed <-> tsound t = false.
Proof.
  intro t. destruct t; simpl; split.
  - intro H. discriminate.              (* T1 -> (Reg=Closed) *)
  - intro H. discriminate.              (* T1 <- (true=false) *)
  - intro H. discriminate.              (* T2 -> *)
  - intro H. discriminate.              (* T2 <- *)
  - intro H. discriminate.              (* T3 -> (Boundary=Closed) *)
  - intro H. discriminate.              (* T3 <- (true=false) *)
  - intros _. reflexivity.              (* T4 -> *)
  - intros _. reflexivity.              (* T4 <- *)
Qed.

(* Combination cannot improve regularity: the combined class is at least as weak
   as each leg (monotone under tier_max). *)
Theorem regularity_combination_monotone : forall a b,
  tier_le a (tier_max a b) = true /\ tier_le b (tier_max a b) = true.
Proof. intros a b. split; [apply tier_max_ub_l | apply tier_max_ub_r]. Qed.

Print Assumptions tier_max_assoc.
Print Assumptions tier_max_sound_hom.
Print Assumptions tier_regularity_reg.
