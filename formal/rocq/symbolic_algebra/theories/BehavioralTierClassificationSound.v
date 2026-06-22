(*
 * BehavioralTierClassificationSound: soundness of the algebra_tower-backed
 * BEHAVIORAL decidability classifier (OSLF Phase 3 wiring lemma).
 *
 * The Rust classifier `BehavioralFormula::decidability_tier`
 * (prattail/src/behavioral_algebra.rs) maps a behavioral guard to a decidability
 * tier from its SHAPE:
 *   - Top/Bot              -> T1 (compile-time decidable: ground constants)
 *   - any modal operator   -> T3 (semi-decidable: is_satisfiable_3v ⇒ DontKnow)
 *   - otherwise relational -> T2 (runtime-decidable: closed-world over the
 *                                 fact snapshot, reject-safe)
 *
 * `testkit/src/analytical/guards.rs::check_guard_decidability` routes every
 * behavioral guard (freshness / congruence / binder side-conditions, and — once
 * Phase 5 lands surface syntax — modal/temporal guards) through this classifier.
 * The runtime evaluator `evaluate_pred_with_bindings` decides only the RELATIONAL
 * fragment exactly; the modal fragment is merely semi-decidable
 * (is_satisfiable_3v honestly returns DontKnow for modal formulas — see
 * behavioral_algebra.rs:621). The load-bearing soundness obligation is therefore:
 *
 *   the classifier routes a guard to the exact relational runtime (tier ≤ T2)
 *   IFF that guard has an exact decision procedure (i.e. is non-modal)
 *
 * so a semi-decidable modal guard is NEVER mis-routed to the relational-only
 * evaluator. This file proves it zero-admission.
 *
 * Theorems:
 *   - tier_ground_is_t1       : ground constants are compile-time decidable.
 *   - tier_relational_is_t2   : a non-ground, non-modal guard is runtime-decidable.
 *   - tier_modal_is_t3        : any modal guard is (at most) semi-decidable.
 *   - tier_bounded            : the behavioral fragment never exceeds T3
 *                               (no behavioral guard is undecidable T4).
 *   - routing_sound           : tier ≤ T2  =  exact (the load-bearing equality).
 *   - routing_complete        : tier ≤ T2  <->  non-modal (iff form).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.

(* ===================================================================== *)
(*  A minimal behavioral formula: the modal-vs-relational structure only  *)
(* ===================================================================== *)

(* `Rel` abstracts any relational atom / ∀ / ∃ (the closed-world fragment);
   `Modal` abstracts any modal/temporal operator (Diamond/BoxAll/Mu/Nu/Atom/
   FixVar). And/Or/Not are the boolean combinators. This is exactly the modal
   structure `has_modal` inspects in the Rust `BehavioralFormula`. *)
Inductive BForm : Type :=
  | Top   : BForm
  | Bot   : BForm
  | Rel   : BForm
  | Modal : BForm -> BForm
  | And   : BForm -> BForm -> BForm
  | Or    : BForm -> BForm -> BForm
  | Not   : BForm -> BForm.

(* Mirror of `BehavioralFormula::has_modal`. *)
Fixpoint has_modal (f : BForm) : bool :=
  match f with
  | Top => false
  | Bot => false
  | Rel => false
  | Modal _ => true
  | And a b => orb (has_modal a) (has_modal b)
  | Or a b => orb (has_modal a) (has_modal b)
  | Not a => has_modal a
  end.

(* Top/Bot are the ground constants. *)
Definition is_ground (f : BForm) : bool :=
  match f with
  | Top => true
  | Bot => true
  | _ => false
  end.

(* ===================================================================== *)
(*  Decidability tiers                                                     *)
(* ===================================================================== *)

Inductive Tier : Type := T1 | T2 | T3 | T4.

(* The certificate lattice order T1 ≤ T2 ≤ T3 ≤ T4 (stronger ≤ weaker). *)
Definition tier_le (a b : Tier) : bool :=
  match a, b with
  | T1, _ => true
  | T2, T1 => false
  | T2, _ => true
  | T3, T1 => false
  | T3, T2 => false
  | T3, _ => true
  | T4, T4 => true
  | T4, _ => false
  end.

(* Mirror of `BehavioralFormula::decidability_tier`. *)
Definition tier (f : BForm) : Tier :=
  if is_ground f then T1
  else if has_modal f then T3 else T2.

(* The SEMANTIC anchor: a behavioral guard has an EXACT decision procedure iff it
   is non-modal. The relational fragment is closed-world decidable
   (is_satisfiable_3v returns Sat/Unsat); the modal fragment is only
   semi-decidable (is_satisfiable_3v returns DontKnow). Mirror of
   prattail/src/behavioral_algebra.rs::is_satisfiable_3v. *)
Definition exact (f : BForm) : bool := negb (has_modal f).

(* ===================================================================== *)
(*  Soundness                                                             *)
(* ===================================================================== *)

(* A ground constant carries no modal operator. *)
Lemma ground_not_modal : forall f, is_ground f = true -> has_modal f = false.
Proof.
  intros f H. destruct f; simpl in *; try reflexivity; discriminate.
Qed.

Theorem tier_ground_is_t1 : forall f, is_ground f = true -> tier f = T1.
Proof.
  intros f H. unfold tier. rewrite H. reflexivity.
Qed.

Theorem tier_relational_is_t2 :
  forall f, is_ground f = false -> has_modal f = false -> tier f = T2.
Proof.
  intros f G H. unfold tier. rewrite G, H. reflexivity.
Qed.

Theorem tier_modal_is_t3 : forall f, has_modal f = true -> tier f = T3.
Proof.
  intros f H. unfold tier.
  destruct (is_ground f) eqn:G.
  - apply ground_not_modal in G. congruence.
  - rewrite H. reflexivity.
Qed.

(* The behavioral fragment tops out at semi-decidable: no guard is undecidable. *)
Theorem tier_bounded : forall f, tier_le (tier f) T3 = true.
Proof.
  intros f. unfold tier.
  destruct (is_ground f); [reflexivity|].
  destruct (has_modal f); reflexivity.
Qed.

(* THE load-bearing soundness: the classifier routes a guard to the exact
   relational runtime (tier ≤ T2) exactly when the guard has an exact decision
   procedure. As a boolean equality, this is both soundness (≤ T2 ⇒ exact) and
   completeness (exact ⇒ ≤ T2). *)
Theorem routing_sound : forall f, tier_le (tier f) T2 = exact f.
Proof.
  intros f. unfold tier, exact.
  destruct (is_ground f) eqn:G.
  - apply ground_not_modal in G. rewrite G. reflexivity.
  - destruct (has_modal f); reflexivity.
Qed.

(* The iff reading: a guard is routed to the relational evaluator iff it is
   non-modal — so a modal guard is never sent to the relational-only path. *)
Corollary routing_complete :
  forall f, tier_le (tier f) T2 = true <-> has_modal f = false.
Proof.
  intros f. rewrite routing_sound. unfold exact.
  destruct (has_modal f); simpl; split; intro H;
    solve [ reflexivity | discriminate ].
Qed.

Print Assumptions tier_modal_is_t3.
Print Assumptions tier_bounded.
Print Assumptions routing_sound.
Print Assumptions routing_complete.
