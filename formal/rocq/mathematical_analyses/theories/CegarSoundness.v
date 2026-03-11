(*
 * CegarSoundness: Soundness, relative completeness, and termination of the
 * CEGAR (Counterexample-Guided Abstraction Refinement) loop.
 *
 * Proves that the three-level abstraction ladder (Boolean → Counting →
 * Tropical) correctly implements the CEGAR paradigm:
 *   1. Soundness: if CEGAR reports "Verified", the concrete system is safe
 *   2. Relative completeness: if the concrete system is safe, CEGAR reports
 *      "Verified" (assuming the identity projection at Tropical level)
 *   3. Termination: the loop always terminates (at most 3 iterations)
 *   4. Spuriousness correctness: spurious ↔ concretely unreachable
 *
 * Structure:
 *   Part 1: BooleanWeight semiring instance
 *   Part 2: CountingWeight semiring instance
 *   Part 3: TropicalWeight semiring instance
 *   Part 4: SemiringAbstraction typeclass and instances
 *   Part 5: CEGAR loop model and theorems
 *   Part 6: Bridge lemma connecting to WpdsCorrectness.v
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition              | Rust Code                            | Location
 *   -----------------------------|--------------------------------------|--------------------------
 *   BoolSemiring                 | BooleanWeight                        | cegar.rs:300-354
 *   CountSemiring                | CountingWeight                       | cegar.rs:356-420
 *   TropSemiring                 | TropicalWeight                       | semiring.rs:63-130
 *   SemiringAbstraction          | project_wpds_to_*                    | cegar.rs:300,356
 *   abs_level                    | AbstractionLevel                     | cegar.rs:70-78
 *   refine_level                 | refine()                             | cegar.rs:626-632
 *   cegar_loop                   | cegar_verify() for-loop              | cegar.rs:659-790
 *   cegar_verify                 | cegar_verify(config.initial=Boolean) | cegar.rs:659
 *   cegar_soundness              | CegarResult::Verified ⟹ safe         | cegar.rs:218-222
 *   cegar_relative_completeness  | safe ⟹ ∃ Verified                    | cegar.rs:667-790
 *   cegar_terminates             | max_refinements=3 ⟹ no Inconclusive  | cegar.rs:667
 *   check_result                 | (CegarVerdict, Option<Trace>)        | cegar.rs:456-576
 *   is_spurious                  | is_spurious field                    | cegar.rs:132
 *
 * Abstraction Gap:
 *   The proof axiomatizes abstract_check, abs_safe_at, and is_spurious as
 *   Section variables with linking hypotheses. The Rust code implements these
 *   concretely via project_wpds_to_* and crate::wpds::prestar. The linking
 *   hypotheses (check_safe_iff, *_safe_sound, non_spurious_genuine) encode
 *   the trust boundary — they assert that the composition of projection +
 *   prestar correctly implements the abstract check. This follows the same
 *   Section-based axiomatization pattern as WpdsCorrectness.v.
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From MathematicalAnalyses Require Import SemiringLaws.
From MathematicalAnalyses Require Import WpdsCorrectness.

(* ===================================================================== *)
(*                                                                         *)
(*  PART 1: BOOLEAN WEIGHT SEMIRING                                        *)
(*                                                                         *)
(*  Carrier: bool.  Plus: or.  Times: and.  Zero: false.  One: true.       *)
(*  Mirrors BooleanWeight in cegar.rs:300-354.                             *)
(*                                                                         *)
(* ===================================================================== *)

Section BooleanSemiring.

  (* Plus: logical or. Mirrors BooleanWeight::plus (cegar.rs:310). *)
  Definition bool_plus (a b : bool) : bool := a || b.

  (* Times: logical and. Mirrors BooleanWeight::times (cegar.rs:320). *)
  Definition bool_times (a b : bool) : bool := a && b.

  (* Zero: false. Mirrors BooleanWeight::zero (cegar.rs:305). *)
  Definition bool_zero : bool := false.

  (* One: true. Mirrors BooleanWeight::one (cegar.rs:307). *)
  Definition bool_one : bool := true.

  (* Equality: Leibniz equality on bool. *)
  Definition bool_eq (a b : bool) : Prop := a = b.

  Lemma bool_eq_refl : forall a, bool_eq a a.
  Proof. intros a. reflexivity. Qed.

  Lemma bool_eq_sym : forall a b, bool_eq a b -> bool_eq b a.
  Proof. intros a b H. symmetry. exact H. Qed.

  Lemma bool_eq_trans : forall a b c, bool_eq a b -> bool_eq b c -> bool_eq a c.
  Proof. intros a b c Hab Hbc. unfold bool_eq in *. rewrite Hab. exact Hbc. Qed.

  Theorem bool_plus_comm : forall a b, bool_eq (bool_plus a b) (bool_plus b a).
  Proof. intros [] []; reflexivity. Qed.

  Theorem bool_plus_assoc : forall a b c,
    bool_eq (bool_plus (bool_plus a b) c) (bool_plus a (bool_plus b c)).
  Proof. intros [] [] []; reflexivity. Qed.

  Theorem bool_plus_zero_l : forall a, bool_eq (bool_plus bool_zero a) a.
  Proof. intros []; reflexivity. Qed.

  Theorem bool_times_assoc : forall a b c,
    bool_eq (bool_times (bool_times a b) c) (bool_times a (bool_times b c)).
  Proof. intros [] [] []; reflexivity. Qed.

  Theorem bool_times_one_l : forall a, bool_eq (bool_times bool_one a) a.
  Proof. intros []; reflexivity. Qed.

  Theorem bool_times_one_r : forall a, bool_eq (bool_times a bool_one) a.
  Proof. intros []; reflexivity. Qed.

  Theorem bool_distr_l : forall a b c,
    bool_eq (bool_times a (bool_plus b c))
            (bool_plus (bool_times a b) (bool_times a c)).
  Proof. intros [] [] []; reflexivity. Qed.

  Theorem bool_distr_r : forall a b c,
    bool_eq (bool_times (bool_plus a b) c)
            (bool_plus (bool_times a c) (bool_times b c)).
  Proof. intros [] [] []; reflexivity. Qed.

  Theorem bool_times_zero_l : forall a, bool_eq (bool_times bool_zero a) bool_zero.
  Proof. intros []; reflexivity. Qed.

  Theorem bool_times_zero_r : forall a, bool_eq (bool_times a bool_zero) bool_zero.
  Proof. intros []; reflexivity. Qed.

  Lemma bool_plus_compat : forall a b c d,
    bool_eq a b -> bool_eq c d -> bool_eq (bool_plus a c) (bool_plus b d).
  Proof. intros a b c d Hab Hcd. unfold bool_eq in *. rewrite Hab, Hcd. reflexivity. Qed.

  Lemma bool_times_compat : forall a b c d,
    bool_eq a b -> bool_eq c d -> bool_eq (bool_times a c) (bool_times b d).
  Proof. intros a b c d Hab Hcd. unfold bool_eq in *. rewrite Hab, Hcd. reflexivity. Qed.

  #[export] Instance BoolSemiring : Semiring bool := {
    sr_eq := bool_eq;
    sr_eq_refl := bool_eq_refl;
    sr_eq_sym := bool_eq_sym;
    sr_eq_trans := bool_eq_trans;
    sr_plus := bool_plus;
    sr_times := bool_times;
    sr_zero := bool_zero;
    sr_one := bool_one;
    sr_plus_comm := bool_plus_comm;
    sr_plus_assoc := bool_plus_assoc;
    sr_plus_zero_l := bool_plus_zero_l;
    sr_times_assoc := bool_times_assoc;
    sr_times_one_l := bool_times_one_l;
    sr_times_one_r := bool_times_one_r;
    sr_times_plus_distr_l := bool_distr_l;
    sr_times_plus_distr_r := bool_distr_r;
    sr_times_zero_l := bool_times_zero_l;
    sr_times_zero_r := bool_times_zero_r;
    sr_plus_compat := bool_plus_compat;
    sr_times_compat := bool_times_compat;
  }.

End BooleanSemiring.


(* ===================================================================== *)
(*                                                                         *)
(*  PART 2: COUNTING WEIGHT SEMIRING                                       *)
(*                                                                         *)
(*  Carrier: nat.  Plus: add.  Times: mul.  Zero: 0.  One: 1.             *)
(*  Mirrors CountingWeight in cegar.rs:356-420.                            *)
(*                                                                         *)
(* ===================================================================== *)

Section CountingSemiring.

  Definition count_eq (a b : nat) : Prop := a = b.

  Lemma count_eq_refl : forall a, count_eq a a.
  Proof. intros a. reflexivity. Qed.

  Lemma count_eq_sym : forall a b, count_eq a b -> count_eq b a.
  Proof. intros a b H. symmetry. exact H. Qed.

  Lemma count_eq_trans : forall a b c, count_eq a b -> count_eq b c -> count_eq a c.
  Proof. intros a b c Hab Hbc. unfold count_eq in *. lia. Qed.

  Theorem count_plus_comm : forall a b, count_eq (a + b) (b + a).
  Proof. intros a b. unfold count_eq. lia. Qed.

  Theorem count_plus_assoc : forall a b c,
    count_eq ((a + b) + c) (a + (b + c)).
  Proof. intros a b c. unfold count_eq. lia. Qed.

  Theorem count_plus_zero_l : forall a, count_eq (0 + a) a.
  Proof. intros a. unfold count_eq. lia. Qed.

  Theorem count_times_assoc : forall a b c,
    count_eq ((a * b) * c) (a * (b * c)).
  Proof. intros a b c. unfold count_eq. lia. Qed.

  Theorem count_times_one_l : forall a, count_eq (1 * a) a.
  Proof. intros a. unfold count_eq. lia. Qed.

  Theorem count_times_one_r : forall a, count_eq (a * 1) a.
  Proof. intros a. unfold count_eq. lia. Qed.

  Theorem count_distr_l : forall a b c,
    count_eq (a * (b + c)) (a * b + a * c).
  Proof. intros a b c. unfold count_eq. lia. Qed.

  Theorem count_distr_r : forall a b c,
    count_eq ((a + b) * c) (a * c + b * c).
  Proof. intros a b c. unfold count_eq. lia. Qed.

  Theorem count_times_zero_l : forall a, count_eq (0 * a) 0.
  Proof. intros a. unfold count_eq. lia. Qed.

  Theorem count_times_zero_r : forall a, count_eq (a * 0) 0.
  Proof. intros a. unfold count_eq. lia. Qed.

  Lemma count_plus_compat : forall a b c d,
    count_eq a b -> count_eq c d -> count_eq (a + c) (b + d).
  Proof. intros a b c d Hab Hcd. unfold count_eq in *. lia. Qed.

  Lemma count_times_compat : forall a b c d,
    count_eq a b -> count_eq c d -> count_eq (a * c) (b * d).
  Proof. intros a b c d Hab Hcd. unfold count_eq in *. lia. Qed.

  #[export] Instance CountSemiring : Semiring nat := {
    sr_eq := count_eq;
    sr_eq_refl := count_eq_refl;
    sr_eq_sym := count_eq_sym;
    sr_eq_trans := count_eq_trans;
    sr_plus := Nat.add;
    sr_times := Nat.mul;
    sr_zero := 0;
    sr_one := 1;
    sr_plus_comm := count_plus_comm;
    sr_plus_assoc := count_plus_assoc;
    sr_plus_zero_l := count_plus_zero_l;
    sr_times_assoc := count_times_assoc;
    sr_times_one_l := count_times_one_l;
    sr_times_one_r := count_times_one_r;
    sr_times_plus_distr_l := count_distr_l;
    sr_times_plus_distr_r := count_distr_r;
    sr_times_zero_l := count_times_zero_l;
    sr_times_zero_r := count_times_zero_r;
    sr_plus_compat := count_plus_compat;
    sr_times_compat := count_times_compat;
  }.

End CountingSemiring.


(* ===================================================================== *)
(*                                                                         *)
(*  PART 3: TROPICAL WEIGHT SEMIRING                                       *)
(*                                                                         *)
(*  Carrier: option nat.  Plus: min.  Times: add.                          *)
(*  Zero: None (+∞).  One: Some 0.                                         *)
(*  Mirrors TropicalWeight in semiring.rs:63-130.                          *)
(*                                                                         *)
(*  None represents +∞ (additive identity for min, multiplicative          *)
(*  annihilator for addition).                                             *)
(*                                                                         *)
(* ===================================================================== *)

Section TropicalSemiring.

  (* Plus: min with None = +∞ as identity *)
  Definition trop_plus (a b : option nat) : option nat :=
    match a, b with
    | None, _ => b
    | _, None => a
    | Some x, Some y => Some (Nat.min x y)
    end.

  (* Times: addition with None absorbing *)
  Definition trop_times (a b : option nat) : option nat :=
    match a, b with
    | Some x, Some y => Some (x + y)
    | _, _ => None
    end.

  Definition trop_zero : option nat := None.
  Definition trop_one : option nat := Some 0.

  Definition trop_eq (a b : option nat) : Prop := a = b.

  Lemma trop_eq_refl : forall a, trop_eq a a.
  Proof. intros a. reflexivity. Qed.

  Lemma trop_eq_sym : forall a b, trop_eq a b -> trop_eq b a.
  Proof. intros a b H. symmetry. exact H. Qed.

  Lemma trop_eq_trans : forall a b c,
    trop_eq a b -> trop_eq b c -> trop_eq a c.
  Proof. intros a b c Hab Hbc. unfold trop_eq in *. rewrite Hab. exact Hbc. Qed.

  Theorem trop_plus_comm : forall a b, trop_eq (trop_plus a b) (trop_plus b a).
  Proof.
    intros [] []; unfold trop_eq, trop_plus; try reflexivity.
    f_equal. lia.
  Qed.

  Theorem trop_plus_assoc : forall a b c,
    trop_eq (trop_plus (trop_plus a b) c) (trop_plus a (trop_plus b c)).
  Proof.
    intros [] [] []; unfold trop_eq, trop_plus; try reflexivity.
    f_equal. lia.
  Qed.

  Theorem trop_plus_zero_l : forall a, trop_eq (trop_plus trop_zero a) a.
  Proof. intros []; reflexivity. Qed.

  Theorem trop_times_assoc : forall a b c,
    trop_eq (trop_times (trop_times a b) c) (trop_times a (trop_times b c)).
  Proof.
    intros [] [] []; unfold trop_eq, trop_times; try reflexivity.
    f_equal. lia.
  Qed.

  Theorem trop_times_one_l : forall a, trop_eq (trop_times trop_one a) a.
  Proof.
    (* 0 + n reduces definitionally, so reflexivity suffices *)
    intros []; unfold trop_eq, trop_times, trop_one; reflexivity.
  Qed.

  Theorem trop_times_one_r : forall a, trop_eq (trop_times a trop_one) a.
  Proof.
    intros []; unfold trop_eq, trop_times, trop_one; try reflexivity.
    f_equal. lia.
  Qed.

  (* Key helper: a + min(b,c) = min(a+b, a+c) *)
  Lemma add_min_distr_l : forall a b c : nat,
    a + Nat.min b c = Nat.min (a + b) (a + c).
  Proof. intros a b c. lia. Qed.

  Lemma add_min_distr_r : forall a b c : nat,
    Nat.min a b + c = Nat.min (a + c) (b + c).
  Proof. intros a b c. lia. Qed.

  Theorem trop_distr_l : forall a b c,
    trop_eq (trop_times a (trop_plus b c))
            (trop_plus (trop_times a b) (trop_times a c)).
  Proof.
    intros [] [] []; unfold trop_eq, trop_times, trop_plus; try reflexivity.
    f_equal. apply add_min_distr_l.
  Qed.

  Theorem trop_distr_r : forall a b c,
    trop_eq (trop_times (trop_plus a b) c)
            (trop_plus (trop_times a c) (trop_times b c)).
  Proof.
    intros [] [] []; unfold trop_eq, trop_times, trop_plus; try reflexivity.
    f_equal. apply add_min_distr_r.
  Qed.

  Theorem trop_times_zero_l : forall a, trop_eq (trop_times trop_zero a) trop_zero.
  Proof. intros []; reflexivity. Qed.

  Theorem trop_times_zero_r : forall a, trop_eq (trop_times a trop_zero) trop_zero.
  Proof. intros []; reflexivity. Qed.

  Lemma trop_plus_compat : forall a b c d,
    trop_eq a b -> trop_eq c d -> trop_eq (trop_plus a c) (trop_plus b d).
  Proof. intros a b c d Hab Hcd. unfold trop_eq in *. rewrite Hab, Hcd. reflexivity. Qed.

  Lemma trop_times_compat : forall a b c d,
    trop_eq a b -> trop_eq c d -> trop_eq (trop_times a c) (trop_times b d).
  Proof. intros a b c d Hab Hcd. unfold trop_eq in *. rewrite Hab, Hcd. reflexivity. Qed.

  #[export] Instance TropSemiring : Semiring (option nat) := {
    sr_eq := trop_eq;
    sr_eq_refl := trop_eq_refl;
    sr_eq_sym := trop_eq_sym;
    sr_eq_trans := trop_eq_trans;
    sr_plus := trop_plus;
    sr_times := trop_times;
    sr_zero := trop_zero;
    sr_one := trop_one;
    sr_plus_comm := trop_plus_comm;
    sr_plus_assoc := trop_plus_assoc;
    sr_plus_zero_l := trop_plus_zero_l;
    sr_times_assoc := trop_times_assoc;
    sr_times_one_l := trop_times_one_l;
    sr_times_one_r := trop_times_one_r;
    sr_times_plus_distr_l := trop_distr_l;
    sr_times_plus_distr_r := trop_distr_r;
    sr_times_zero_l := trop_times_zero_l;
    sr_times_zero_r := trop_times_zero_r;
    sr_plus_compat := trop_plus_compat;
    sr_times_compat := trop_times_compat;
  }.

End TropicalSemiring.


(* ===================================================================== *)
(*                                                                         *)
(*  PART 4: SEMIRING ABSTRACTION TYPECLASS AND INSTANCES                   *)
(*                                                                         *)
(*  Minimal axioms for CEGAR soundness: abstract zero implies concrete     *)
(*  zero. This is NOT a full semiring homomorphism — the Counting          *)
(*  projection (option nat → nat) does not preserve multiplication.        *)
(*  We only require the "zero-reflecting" property.                        *)
(*                                                                         *)
(* ===================================================================== *)

Class SemiringAbstraction (C A : Type) (SC : Semiring C) (SA : Semiring A) := {
  alpha : C -> A;

  (* Core soundness: abstract zero implies concrete zero.
     If the abstract analysis reports zero (unreachable), the concrete
     weight must also be zero. Contrapositive: concrete reachability
     implies abstract reachability. *)
  alpha_sound : forall w, sr_eq (alpha w) sr_zero -> sr_eq w sr_zero;

  (* Forward: zero maps to zero *)
  alpha_zero : sr_eq (alpha sr_zero) sr_zero;

  (* Compatibility with equality *)
  alpha_compat : forall a b, sr_eq a b -> sr_eq (alpha a) (alpha b);
}.


(* ---- Instance 1: Boolean abstraction (option nat → bool) ---- *)
(* alpha(None) = false, alpha(Some _) = true.
   Mirrors project_wpds_to_boolean in cegar.rs:300-354. *)

Section BoolAbstraction.

  Definition alpha_bool (w : option nat) : bool :=
    match w with
    | None   => false
    | Some _ => true
    end.

  Lemma alpha_bool_sound : forall w,
    bool_eq (alpha_bool w) bool_zero -> trop_eq w trop_zero.
  Proof.
    intros [n |] H; unfold bool_eq, bool_zero, alpha_bool in H;
      unfold trop_eq, trop_zero.
    - discriminate H.
    - reflexivity.
  Qed.

  Lemma alpha_bool_zero : bool_eq (alpha_bool trop_zero) bool_zero.
  Proof. reflexivity. Qed.

  Lemma alpha_bool_compat : forall a b,
    trop_eq a b -> bool_eq (alpha_bool a) (alpha_bool b).
  Proof.
    intros a b Hab. unfold trop_eq in Hab. subst. apply bool_eq_refl.
  Qed.

  #[export] Instance BoolAbstraction
    : SemiringAbstraction (option nat) bool TropSemiring BoolSemiring := {
    alpha := alpha_bool;
    alpha_sound := alpha_bool_sound;
    alpha_zero := alpha_bool_zero;
    alpha_compat := alpha_bool_compat;
  }.

End BoolAbstraction.


(* ---- Instance 2: Counting abstraction (option nat → nat) ---- *)
(* alpha(None) = 0, alpha(Some _) = 1.
   Mirrors project_wpds_to_counting in cegar.rs:356-420. *)

Section CountAbstraction.

  Definition alpha_count (w : option nat) : nat :=
    match w with
    | None   => 0
    | Some _ => 1
    end.

  Lemma alpha_count_sound : forall w,
    count_eq (alpha_count w) 0 -> trop_eq w trop_zero.
  Proof.
    intros [n |] H; unfold count_eq, alpha_count in H;
      unfold trop_eq, trop_zero.
    - discriminate H.
    - reflexivity.
  Qed.

  Lemma alpha_count_zero : count_eq (alpha_count trop_zero) 0.
  Proof. reflexivity. Qed.

  Lemma alpha_count_compat : forall a b,
    trop_eq a b -> count_eq (alpha_count a) (alpha_count b).
  Proof.
    intros a b Hab. unfold trop_eq in Hab. subst. apply count_eq_refl.
  Qed.

  #[export] Instance CountAbstraction
    : SemiringAbstraction (option nat) nat TropSemiring CountSemiring := {
    alpha := alpha_count;
    alpha_sound := alpha_count_sound;
    alpha_zero := alpha_count_zero;
    alpha_compat := alpha_count_compat;
  }.

End CountAbstraction.


(* ---- Instance 3: Identity abstraction (Tropical → Tropical) ---- *)
(* alpha(w) = w. The Tropical level is the concrete level: no
   abstraction loss, no spurious counterexamples possible. *)

Section IdentityAbstraction.

  Definition alpha_id (w : option nat) : option nat := w.

  Lemma alpha_id_sound : forall w,
    trop_eq (alpha_id w) trop_zero -> trop_eq w trop_zero.
  Proof. intros w H. exact H. Qed.

  Lemma alpha_id_zero : trop_eq (alpha_id trop_zero) trop_zero.
  Proof. reflexivity. Qed.

  Lemma alpha_id_compat : forall a b,
    trop_eq a b -> trop_eq (alpha_id a) (alpha_id b).
  Proof. intros a b H. exact H. Qed.

  #[export] Instance IdentityAbstraction
    : SemiringAbstraction (option nat) (option nat) TropSemiring TropSemiring := {
    alpha := alpha_id;
    alpha_sound := alpha_id_sound;
    alpha_zero := alpha_id_zero;
    alpha_compat := alpha_id_compat;
  }.

End IdentityAbstraction.


(* ===================================================================== *)
(*                                                                         *)
(*  PART 5: CEGAR LOOP MODEL AND THEOREMS                                 *)
(*                                                                         *)
(*  Models the CEGAR loop from cegar.rs:659-790.                           *)
(*  The loop iterates over three abstraction levels, refining when a       *)
(*  spurious counterexample is found.                                      *)
(*                                                                         *)
(* ===================================================================== *)

Section CegarLoop.

  (* ------------------------------------------------------------------- *)
  (*  Abstraction levels                                                   *)
  (* ------------------------------------------------------------------- *)

  (* The three levels of the abstraction ladder.
     Mirrors AbstractionLevel in cegar.rs:70-78 (excluding Custom). *)

  Inductive abs_level : Type :=
    | LvlBoolean
    | LvlCounting
    | LvlTropical.

  (* Refinement: advance to the next level.
     Mirrors refine() in cegar.rs:626-632. *)
  Definition refine_level (l : abs_level) : option abs_level :=
    match l with
    | LvlBoolean  => Some LvlCounting
    | LvlCounting => Some LvlTropical
    | LvlTropical => None
    end.

  (* ------------------------------------------------------------------- *)
  (*  Abstract model                                                       *)
  (* ------------------------------------------------------------------- *)

  (* Counterexample trace type (abstract — any type of stack word sequence) *)
  Variable trace : Type.

  (* Result of an abstract check at a given level.
     Mirrors the (CegarVerdict, Option<CounterexampleTrace>) pair
     returned by abstract_check_at_level in cegar.rs:555-576. *)
  Inductive check_result : Type :=
    | Safe                                  (* No intersection with bad states *)
    | CounterexampleFound (t : trace).      (* Intersection found; witness trace *)

  (* The abstract check function. Parameterized by level.
     This is the composition of project_wpds_to_* + prestar + intersection
     check in the Rust code. *)
  Variable abstract_check : abs_level -> check_result.

  (* Spuriousness oracle. Returns true if the trace is concretely
     unreachable (weight = 0 at concrete level).
     Mirrors the is_spurious flag computation in cegar.rs:691-720. *)
  Variable is_spurious : trace -> bool.

  (* Concrete safety: the property we want to verify.
     "No reachable configuration is bad." *)
  Variable concrete_safe : Prop.

  (* Abstract safety at a given level *)
  Variable abs_safe_at : abs_level -> Prop.

  (* ------------------------------------------------------------------- *)
  (*  Soundness hypotheses                                                 *)
  (*                                                                       *)
  (*  These encode the trust boundary between the Rocq model and the Rust  *)
  (*  implementation. They assert that:                                    *)
  (*    1. Abstract safety at any level implies concrete safety            *)
  (*    2. The abstract_check function correctly reflects abs_safe_at      *)
  (*    3. Non-spurious counterexamples correspond to genuine violations   *)
  (* ------------------------------------------------------------------- *)

  (* Per-level soundness: abstract safety implies concrete safety.
     This follows from alpha_sound: if the abstract prestar reports
     no reachable bad state (empty intersection), then no concrete
     path reaches a bad state either. *)
  Hypothesis bool_safe_sound  : abs_safe_at LvlBoolean  -> concrete_safe.
  Hypothesis count_safe_sound : abs_safe_at LvlCounting -> concrete_safe.
  Hypothesis trop_safe_sound  : abs_safe_at LvlTropical -> concrete_safe.

  (* The abstract_check function correctly captures abs_safe_at:
     - If abstract_check returns Safe, the level is abstractly safe
     - If the level is abstractly safe, abstract_check returns Safe *)
  Hypothesis check_safe_iff : forall l,
    abstract_check l = Safe <-> abs_safe_at l.

  (* ------------------------------------------------------------------- *)
  (*  Completeness hypotheses                                              *)
  (* ------------------------------------------------------------------- *)

  (* Tropical is the identity projection: concrete safety implies
     Tropical-level safety. Since alpha_id(w) = w, no information
     is lost, so concrete safety is exactly Tropical-level safety. *)
  Hypothesis concrete_safe_implies_trop_safe :
    concrete_safe -> abs_safe_at LvlTropical.

  (* Non-spurious counterexamples are genuine: if a counterexample
     is found and it is not spurious, then the concrete system is
     actually unsafe. Contrapositive: if the system is safe, all
     counterexamples at any level must be spurious. *)
  Hypothesis non_spurious_genuine : forall l t,
    abstract_check l = CounterexampleFound t ->
    is_spurious t = false ->
    ~ concrete_safe.

  (* ------------------------------------------------------------------- *)
  (*  Spuriousness hypotheses                                              *)
  (* ------------------------------------------------------------------- *)

  (* Concrete reachability of traces *)
  Variable concretely_reachable : trace -> Prop.

  (* Spuriousness is equivalent to concrete unreachability.
     Mirrors the validation step in cegar.rs:691-720 where the
     concrete weight is checked against is_zero(). *)
  Hypothesis spurious_iff_unreachable : forall t,
    is_spurious t = true <-> ~ concretely_reachable t.

  (* ------------------------------------------------------------------- *)
  (*  CEGAR loop definition                                                *)
  (* ------------------------------------------------------------------- *)

  (* Result of the CEGAR loop.
     Mirrors CegarResult in cegar.rs:218-230. *)
  Inductive cegar_result : Type :=
    | Verified (l : abs_level)       (* Property verified at level l *)
    | Refuted                        (* Genuine counterexample found *)
    | Inconclusive.                  (* Fuel exhausted without verdict *)

  (* Fuel-based CEGAR loop.
     Mirrors the for-loop in cegar.rs:667-790.
     fuel = remaining iterations, level = current abstraction level. *)
  Fixpoint cegar_loop (fuel : nat) (level : abs_level) : cegar_result :=
    match fuel with
    | 0 => Inconclusive
    | S fuel' =>
      match abstract_check level with
      | Safe => Verified level
      | CounterexampleFound t =>
        if is_spurious t then
          match refine_level level with
          | Some next => cegar_loop fuel' next
          | None =>
            (* At Tropical, is_spurious should not be true for a genuine
               counterexample, but if it is, we report refuted since we
               cannot refine further. However, this case contradicts
               our completeness hypotheses — see cegar_terminates. *)
            Refuted
          end
        else Refuted
      end
    end.

  (* The standard entry point: 3 iterations starting from Boolean.
     Mirrors cegar_verify with config.max_refinements = 3 and
     config.initial_level = Boolean in cegar.rs:659. *)
  Definition cegar_verify : cegar_result := cegar_loop 3 LvlBoolean.

  (* ------------------------------------------------------------------- *)
  (*  Theorem 1: Soundness                                                 *)
  (*                                                                       *)
  (*  If the CEGAR loop reports Verified at any level, the concrete        *)
  (*  system is safe.                                                      *)
  (* ------------------------------------------------------------------- *)

  (* Lemma: cegar_loop returning Verified implies abstract safety *)
  Lemma cegar_loop_verified_implies_abs_safe :
    forall fuel level l,
      cegar_loop fuel level = Verified l -> abs_safe_at l.
  Proof.
    intros fuel.
    induction fuel as [| fuel' IH]; intros level l Hloop.
    - (* fuel = 0: cegar_loop returns Inconclusive, contradiction *)
      simpl in Hloop. discriminate Hloop.
    - (* fuel = S fuel': case split on abstract_check level *)
      simpl in Hloop.
      destruct (abstract_check level) as [| t] eqn:Hcheck.
      + (* abstract_check = Safe: Verified level, so l = level *)
        injection Hloop as Hl. subst l.
        apply check_safe_iff. exact Hcheck.
      + (* abstract_check = CounterexampleFound t *)
        destruct (is_spurious t) eqn:Hspur.
        * (* Spurious: refine and recurse *)
          destruct (refine_level level) as [next |] eqn:Hrefine.
          -- (* Some next: recurse *)
             apply IH with next. exact Hloop.
          -- (* None: Refuted, contradiction *)
             discriminate Hloop.
        * (* Not spurious: Refuted, contradiction *)
          discriminate Hloop.
  Qed.

  (* Helper: abstract safety at any level implies concrete safety *)
  Lemma abs_safe_implies_concrete : forall l,
    abs_safe_at l -> concrete_safe.
  Proof.
    intros []; [exact bool_safe_sound | exact count_safe_sound | exact trop_safe_sound].
  Qed.

  (* Main soundness theorem *)
  Theorem cegar_soundness :
    forall l, cegar_verify = Verified l -> concrete_safe.
  Proof.
    intros l Hverified.
    apply abs_safe_implies_concrete with l.
    apply cegar_loop_verified_implies_abs_safe with 3 LvlBoolean.
    exact Hverified.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  Theorem 2: Relative Completeness                                     *)
  (*                                                                       *)
  (*  If the concrete system is safe, then cegar_verify returns            *)
  (*  Verified at some level.                                              *)
  (* ------------------------------------------------------------------- *)

  (* Helper: if concrete_safe, then any non-Safe abstract_check result
     must produce a spurious counterexample. *)
  Lemma safe_implies_counterexample_spurious : forall l t,
    concrete_safe ->
    abstract_check l = CounterexampleFound t ->
    is_spurious t = true.
  Proof.
    intros l t Hsafe Hcheck.
    destruct (is_spurious t) eqn:Hspur.
    - reflexivity.
    - exfalso. exact (non_spurious_genuine l t Hcheck Hspur Hsafe).
  Qed.

  Theorem cegar_relative_completeness :
    concrete_safe -> exists l, cegar_verify = Verified l.
  Proof.
    intro Hsafe.
    unfold cegar_verify.
    (* Unfold cegar_loop 3 LvlBoolean step by step *)
    simpl.
    destruct (abstract_check LvlBoolean) as [| t_bool] eqn:Hbool.
    - (* Boolean check says Safe *)
      exists LvlBoolean. reflexivity.
    - (* Boolean produces counterexample t_bool *)
      assert (Hspur_bool : is_spurious t_bool = true)
        by (exact (safe_implies_counterexample_spurious LvlBoolean t_bool Hsafe Hbool)).
      rewrite Hspur_bool. simpl.
      destruct (abstract_check LvlCounting) as [| t_count] eqn:Hcount.
      + (* Counting check says Safe *)
        exists LvlCounting. reflexivity.
      + (* Counting produces counterexample t_count *)
        assert (Hspur_count : is_spurious t_count = true)
          by (exact (safe_implies_counterexample_spurious LvlCounting t_count Hsafe Hcount)).
        rewrite Hspur_count. simpl.
        destruct (abstract_check LvlTropical) as [| t_trop] eqn:Htrop.
        * (* Tropical check says Safe *)
          exists LvlTropical. reflexivity.
        * (* Tropical produces counterexample — contradiction:
             concrete_safe implies trop_safe implies abstract_check = Safe *)
          exfalso.
          assert (Htrop_safe : abs_safe_at LvlTropical)
            by (exact (concrete_safe_implies_trop_safe Hsafe)).
          apply check_safe_iff in Htrop_safe.
          rewrite Htrop_safe in Htrop. discriminate Htrop.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  Theorem 3: Termination                                               *)
  (*                                                                       *)
  (*  The CEGAR loop with fuel=3 never returns Inconclusive.               *)
  (*  This is a purely structural property of the three-level ladder:      *)
  (*  every branch of the computation produces Verified or Refuted.        *)
  (* ------------------------------------------------------------------- *)

  Theorem cegar_terminates : cegar_verify <> Inconclusive.
  Proof.
    unfold cegar_verify.
    simpl.
    destruct (abstract_check LvlBoolean) as [| t_bool].
    - (* Safe: returns Verified *)
      discriminate.
    - destruct (is_spurious t_bool).
      + (* Spurious: refine to Counting *)
        simpl.
        destruct (abstract_check LvlCounting) as [| t_count].
        * (* Safe *)
          discriminate.
        * destruct (is_spurious t_count).
          -- (* Spurious: refine to Tropical *)
             simpl.
             destruct (abstract_check LvlTropical) as [| t_trop].
             ++ (* Safe *)
                discriminate.
             ++ destruct (is_spurious t_trop).
                ** (* Spurious at Tropical: refine_level = None → Refuted *)
                   simpl. discriminate.
                ** (* Not spurious: Refuted *)
                   discriminate.
          -- (* Not spurious: Refuted *)
             discriminate.
      + (* Not spurious: Refuted *)
        discriminate.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  Theorem 4: Spuriousness Correctness                                  *)
  (*                                                                       *)
  (*  Spurious counterexamples are exactly those that are concretely       *)
  (*  unreachable.                                                         *)
  (* ------------------------------------------------------------------- *)

  Theorem spurious_implies_unreachable :
    forall t, is_spurious t = true -> ~ concretely_reachable t.
  Proof.
    intros t Hspur.
    apply spurious_iff_unreachable. exact Hspur.
  Qed.

  Theorem unreachable_implies_spurious :
    forall t, ~ concretely_reachable t -> is_spurious t = true.
  Proof.
    intros t Hunreach.
    apply spurious_iff_unreachable. exact Hunreach.
  Qed.

End CegarLoop.


(* ===================================================================== *)
(*                                                                         *)
(*  PART 6: BRIDGE LEMMA — CONNECTING TO WpdsCorrectness.v                *)
(*                                                                         *)
(*  This lemma shows how prestar soundness (from WpdsCorrectness.v)        *)
(*  implies the concrete safety property used by CEGAR.                    *)
(*                                                                         *)
(* ===================================================================== *)

Section PrestarBridge.

  Variable symbol : Type.
  Variable pa_state : Type.
  Variable embed_p : pa_state.
  Variable is_final : pa_state -> Prop.
  Variable rules : list (sl_rule symbol).

  (* Import sl_reachable and sl_accepts from WpdsCorrectness *)

  Definition bridge_reachable := sl_reachable symbol rules.
  Definition bridge_accepts (T : list (pa_state * symbol * pa_state))
    := sl_accepts symbol pa_state embed_p is_final T.

  Variable initial_stack : list symbol.

  (* Bridge lemma: if prestar is sound (from WpdsCorrectness.v's
     prestar_soundness theorem) and the initial configuration is not
     accepted by the prestar automaton, then no reachable configuration
     is bad (i.e., accepted by the target automaton).

     This provides the concrete_safe instantiation for CEGAR:
     "concrete_safe ≡ no bad configuration is reachable from
     initial_stack." *)

  Lemma safe_from_prestar :
    forall T_prestar T_target,
      (* Prestar soundness: every config from which a target-accepted
         config is reachable, is accepted by the prestar automaton.
         This is exactly prestar_soundness from WpdsCorrectness.v. *)
      (forall w0 w,
         bridge_reachable w0 w ->
         bridge_accepts T_target w ->
         bridge_accepts T_prestar w0) ->
      (* The initial config is NOT accepted by prestar *)
      ~ bridge_accepts T_prestar initial_stack ->
      (* Conclusion: no reachable config from initial_stack is bad *)
      forall w, bridge_reachable initial_stack w -> ~ bridge_accepts T_target w.
  Proof.
    intros T_prestar T_target Hprestar_sound Hnot_init w Hreach Hbad.
    apply Hnot_init.
    apply Hprestar_sound with w.
    - exact Hreach.
    - exact Hbad.
  Qed.

End PrestarBridge.


(* ===================================================================== *)
(*  Summary of Results                                                     *)
(*                                                                         *)
(*  Boolean Semiring:                                                      *)
(*    (bool, ||, &&, false, true) is a semiring                            *)
(*    Instance: BoolSemiring                                               *)
(*                                                                         *)
(*  Counting Semiring:                                                     *)
(*    (nat, +, *, 0, 1) is a semiring                                      *)
(*    Instance: CountSemiring                                              *)
(*                                                                         *)
(*  Tropical Semiring:                                                     *)
(*    (option nat, min, +, None, Some 0) is a semiring                     *)
(*    Instance: TropSemiring                                               *)
(*                                                                         *)
(*  Semiring Abstraction:                                                  *)
(*    SemiringAbstraction typeclass (zero-reflecting, not full hom)         *)
(*    BoolAbstraction:     option nat → bool    (None↦false, Some↦true)    *)
(*    CountAbstraction:    option nat → nat     (None↦0, Some↦1)           *)
(*    IdentityAbstraction: option nat → option nat (identity)              *)
(*                                                                         *)
(*  CEGAR Loop:                                                            *)
(*    cegar_loop_verified_implies_abs_safe  — verified ⟹ abstract safe     *)
(*    cegar_soundness                      — verified ⟹ concrete safe     *)
(*    cegar_relative_completeness          — concrete safe ⟹ ∃ verified   *)
(*    cegar_terminates                     — fuel=3 ⟹ not Inconclusive    *)
(*    spurious_implies_unreachable         — spurious ⟹ unreachable       *)
(*    unreachable_implies_spurious         — unreachable ⟹ spurious       *)
(*                                                                         *)
(*  Bridge:                                                                *)
(*    safe_from_prestar — prestar sound + init not accepted ⟹ safe        *)
(*                                                                         *)
(*  All proofs are COMPLETE — zero Admitted.                                *)
(* ===================================================================== *)
