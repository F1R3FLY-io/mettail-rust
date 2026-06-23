(*
 * BehavioralLoweringSound: soundness of the behavioral_pred -> behavioral_algebra
 * relational-core LOWERING (OSLF Phase 9 de-dup foundation).
 *
 * The Rust `BehavioralPred::to_behavioral_formula` (prattail/src/behavioral_pred.rs)
 * lowers the runtime CARRIER's relational fragment into the compile-time DECIDER
 * `BehavioralFormula` (behavioral_algebra.rs) — making the decider the single
 * relational representation any classification/analysis consumes. `AcMatch` (the
 * structural leg) is rejected (`None`); the carrier has no modal variants, so the
 * lowering image is the RELATIONAL fragment only.
 *
 * This file models that lowering self-contained (reusing the modal-vs-relational
 * shape + Tier framework of `BehavioralTierClassificationSound.v`) and proves the
 * correspondence the classifier depends on:
 *
 *   - lower_acmatch_none     : an AcMatch anywhere => rejected (`None`).
 *   - lower_relational_some  : every AcMatch-free carrier lowers.
 *   - lower_non_modal        : the image is modal-free (LOAD-BEARING — a lowered
 *                              carrier can never be mis-classified above T2).
 *   - lower_preserves_exact  : the image always has an exact decision procedure.
 *   - lower_tier_sound       : tier(lower(p)) = T1 iff p is Top, else T2 — the
 *                              Coq image of the Phase-9 snapshot's tier invariant.
 *   - lower_implies_demorgan : the `a -> b == ~a \/ b` reduct is the proof's
 *                              definitional mirror of the Rust mapping.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.

(* ===================================================================== *)
(*  Source: the RELATIONAL behavioral_pred carrier                        *)
(* ===================================================================== *)

Inductive BPred : Type :=
  | PTop
  | PRel (negated : bool)
  | PForall (body : BPred)
  | PExists (body : BPred)
  | PAnd (a b : BPred)
  | POr (a b : BPred)
  | PNot (x : BPred)
  | PImplies (a b : BPred)
  | PAcMatch.

Fixpoint has_acmatch (p : BPred) : bool :=
  match p with
  | PTop => false
  | PRel _ => false
  | PForall q => has_acmatch q
  | PExists q => has_acmatch q
  | PAnd a b => orb (has_acmatch a) (has_acmatch b)
  | POr a b => orb (has_acmatch a) (has_acmatch b)
  | PNot x => has_acmatch x
  | PImplies a b => orb (has_acmatch a) (has_acmatch b)
  | PAcMatch => true
  end.

Definition is_ptop (p : BPred) : bool :=
  match p with PTop => true | _ => false end.

(* ===================================================================== *)
(*  Target: the BehavioralFormula shape (with the modal fragment present, *)
(*  so we can PROVE the lowering never reaches it)                         *)
(* ===================================================================== *)

Inductive BForm : Type :=
  | FTop
  | FBot
  | FRel
  | FModal (g : BForm)   (* stands for any modal op: Atom/Diamond/BoxAll/Mu/Nu/FixVar *)
  | FForall (g : BForm)
  | FExists (g : BForm)
  | FAnd (a b : BForm)
  | FOr (a b : BForm)
  | FNot (g : BForm).

Fixpoint has_modal (f : BForm) : bool :=
  match f with
  | FTop => false
  | FBot => false
  | FRel => false
  | FModal _ => true
  | FForall g => has_modal g
  | FExists g => has_modal g
  | FNot g => has_modal g
  | FAnd a b => orb (has_modal a) (has_modal b)
  | FOr a b => orb (has_modal a) (has_modal b)
  end.

Definition is_ground (f : BForm) : bool :=
  match f with FTop => true | FBot => true | _ => false end.

Inductive Tier : Type := T1 | T2 | T3 | T4.

(* Mirror of BehavioralFormula::decidability_tier (BehavioralTierClassificationSound). *)
Definition tier (f : BForm) : Tier :=
  if is_ground f then T1 else if has_modal f then T3 else T2.

Definition exact (f : BForm) : bool := negb (has_modal f).

(* ===================================================================== *)
(*  The lowering — mirror of `to_behavioral_formula`                      *)
(* ===================================================================== *)

Fixpoint lower (p : BPred) : option BForm :=
  match p with
  | PTop => Some FTop
  | PRel negated => Some (if negated then FNot FRel else FRel)
  | PForall q => match lower q with Some f => Some (FForall f) | None => None end
  | PExists q => match lower q with Some f => Some (FExists f) | None => None end
  | PAnd a b =>
      match lower a, lower b with Some fa, Some fb => Some (FAnd fa fb) | _, _ => None end
  | POr a b =>
      match lower a, lower b with Some fa, Some fb => Some (FOr fa fb) | _, _ => None end
  | PNot x => match lower x with Some f => Some (FNot f) | None => None end
  | PImplies a b =>
      (* De Morgan: a -> b  ==  ~a \/ b  (matches HeytingAlgebra::implies and the
         runtime eval `!p || c`). *)
      match lower a, lower b with Some fa, Some fb => Some (FOr (FNot fa) fb) | _, _ => None end
  | PAcMatch => None
  end.

(* ===================================================================== *)
(*  Soundness                                                            *)
(* ===================================================================== *)

(* 1. An AcMatch anywhere is rejected (the structural leg never reaches the
   relational decider). *)
Theorem lower_acmatch_none : forall p, has_acmatch p = true -> lower p = None.
Proof.
  induction p as
    [ | negated | body IHbody | body IHbody | a IHa b IHb
    | a IHa b IHb | x IHx | a IHa b IHb | ];
    simpl; intro H; try discriminate.
  - rewrite (IHbody H). reflexivity.
  - rewrite (IHbody H). reflexivity.
  - apply orb_true_iff in H. destruct H as [Ha | Hb].
    + rewrite (IHa Ha). reflexivity.
    + rewrite (IHb Hb). destruct (lower a); reflexivity.
  - apply orb_true_iff in H. destruct H as [Ha | Hb].
    + rewrite (IHa Ha). reflexivity.
    + rewrite (IHb Hb). destruct (lower a); reflexivity.
  - rewrite (IHx H). reflexivity.
  - apply orb_true_iff in H. destruct H as [Ha | Hb].
    + rewrite (IHa Ha). reflexivity.
    + rewrite (IHb Hb). destruct (lower a); reflexivity.
  - reflexivity.
Qed.

(* 2. Every AcMatch-free carrier lowers successfully. *)
Theorem lower_relational_some : forall p, has_acmatch p = false -> exists f, lower p = Some f.
Proof.
  induction p as
    [ | negated | body IHbody | body IHbody | a IHa b IHb
    | a IHa b IHb | x IHx | a IHa b IHb | ];
    simpl; intro H.
  - exists FTop. reflexivity.
  - exists (if negated then FNot FRel else FRel). reflexivity.
  - destruct (IHbody H) as [f Hf]. exists (FForall f). rewrite Hf. reflexivity.
  - destruct (IHbody H) as [f Hf]. exists (FExists f). rewrite Hf. reflexivity.
  - apply orb_false_iff in H. destruct H as [Ha Hb].
    destruct (IHa Ha) as [fa Hfa]. destruct (IHb Hb) as [fb Hfb].
    exists (FAnd fa fb). rewrite Hfa, Hfb. reflexivity.
  - apply orb_false_iff in H. destruct H as [Ha Hb].
    destruct (IHa Ha) as [fa Hfa]. destruct (IHb Hb) as [fb Hfb].
    exists (FOr fa fb). rewrite Hfa, Hfb. reflexivity.
  - destruct (IHx H) as [f Hf]. exists (FNot f). rewrite Hf. reflexivity.
  - apply orb_false_iff in H. destruct H as [Ha Hb].
    destruct (IHa Ha) as [fa Hfa]. destruct (IHb Hb) as [fb Hfb].
    exists (FOr (FNot fa) fb). rewrite Hfa, Hfb. reflexivity.
  - discriminate H.
Qed.

(* 3. THE load-bearing fact: the lowering image is modal-free, so a lowered
   carrier is never mis-classified above T2. *)
Theorem lower_non_modal : forall p f, lower p = Some f -> has_modal f = false.
Proof.
  induction p as
    [ | negated | body IHbody | body IHbody | a IHa b IHb
    | a IHa b IHb | x IHx | a IHa b IHb | ];
    simpl; intros f H.
  - injection H as H; subst; reflexivity.
  - destruct negated; injection H as H; subst; reflexivity.
  - destruct (lower body) as [g |]; [| discriminate].
    injection H as H; subst. simpl. exact (IHbody g eq_refl).
  - destruct (lower body) as [g |]; [| discriminate].
    injection H as H; subst. simpl. exact (IHbody g eq_refl).
  - destruct (lower a) as [ga |]; [| discriminate].
    destruct (lower b) as [gb |]; [| discriminate].
    injection H as H; subst. simpl. rewrite (IHa ga eq_refl), (IHb gb eq_refl). reflexivity.
  - destruct (lower a) as [ga |]; [| discriminate].
    destruct (lower b) as [gb |]; [| discriminate].
    injection H as H; subst. simpl. rewrite (IHa ga eq_refl), (IHb gb eq_refl). reflexivity.
  - destruct (lower x) as [g |]; [| discriminate].
    injection H as H; subst. simpl. exact (IHx g eq_refl).
  - destruct (lower a) as [ga |]; [| discriminate].
    destruct (lower b) as [gb |]; [| discriminate].
    injection H as H; subst. simpl. rewrite (IHa ga eq_refl), (IHb gb eq_refl). reflexivity.
  - discriminate H.
Qed.

(* 4. The image always has an exact decision procedure (reject-safe routing
   preserved). *)
Theorem lower_preserves_exact : forall p f, lower p = Some f -> exact f = true.
Proof.
  intros p f H. unfold exact. rewrite (lower_non_modal p f H). reflexivity.
Qed.

(* A lowered formula is ground iff its source is Top. *)
Lemma lower_ground : forall p f, lower p = Some f -> is_ground f = is_ptop p.
Proof.
  destruct p as [ | negated | body | body | a b | a b | x | a b | ]; simpl; intros f H.
  - injection H as H; subst; reflexivity.
  - destruct negated; injection H as H; subst; reflexivity.
  - destruct (lower body) as [g |]; [| discriminate]. injection H as H; subst; reflexivity.
  - destruct (lower body) as [g |]; [| discriminate]. injection H as H; subst; reflexivity.
  - destruct (lower a) as [ga |]; [| discriminate].
    destruct (lower b) as [gb |]; [| discriminate]. injection H as H; subst; reflexivity.
  - destruct (lower a) as [ga |]; [| discriminate].
    destruct (lower b) as [gb |]; [| discriminate]. injection H as H; subst; reflexivity.
  - destruct (lower x) as [g |]; [| discriminate]. injection H as H; subst; reflexivity.
  - destruct (lower a) as [ga |]; [| discriminate].
    destruct (lower b) as [gb |]; [| discriminate]. injection H as H; subst; reflexivity.
  - discriminate H.
Qed.

(* 5. tier(lower(p)) = T1 iff p is Top, else T2 — the Coq image of the snapshot's
   tier-equivalence invariant. *)
Theorem lower_tier_sound : forall p f,
  lower p = Some f -> tier f = (if is_ptop p then T1 else T2).
Proof.
  intros p f H. unfold tier.
  rewrite (lower_ground p f H).
  rewrite (lower_non_modal p f H).
  destruct (is_ptop p); reflexivity.
Qed.

(* 6. The `Implies` De Morgan reduct is the proof's definitional mirror of the
   Rust mapping (`a -> b == ~a \/ b`). *)
Theorem lower_implies_demorgan : forall a b,
  lower (PImplies a b) =
  match lower a, lower b with
  | Some fa, Some fb => Some (FOr (FNot fa) fb)
  | _, _ => None
  end.
Proof. reflexivity. Qed.

Print Assumptions lower_acmatch_none.
Print Assumptions lower_non_modal.
Print Assumptions lower_tier_sound.
Print Assumptions lower_implies_demorgan.
