(*
 * HeytingAlgebra: the algebraic foundation for reject-safe (intuitionistic)
 * negation of behavioral / semi-decidable predicates. A Heyting algebra is a
 * bounded lattice with a relative pseudo-complement (implication →) given by the
 * adjunction  a ∧ c ≤ b  ⟺  c ≤ (a → b).  Pseudo-complement is ¬a := a → ⊥.
 *
 * This file proves, fully and zero-admission, the results the symbolic-predicate
 * plan relies on (prattail/docs/design/constraint-theories/heyting-algebra-
 * extensions.md §2/§7/§9; Rust trait tower BooleanAlgebra:HeytingAlgebra:
 * RejectSafeAlgebra in prattail/src/algebra_tower.rs):
 *
 *   - ≤ (defined by meet) is a partial order; ∧ is the glb.
 *   - the counit a ∧ (a→b) = a ∧ b (modus ponens).
 *   - ¬¬ is a CLOSURE OPERATOR: extensive (a ≤ ¬¬a), monotone, idempotent
 *     (¬¬¬a = ¬a, hence ¬¬(¬¬a) = ¬¬a).  [doc §2]
 *   - the §7 REJECT-SAFE soundness  dneg_eq_bot_implies_bot : ¬¬a = ⊥ → a = ⊥
 *     (the algebraic core of `RejectSafeAlgebra`: a sound complement never drops
 *     a satisfiable predicate — no false negatives).  [doc §7]
 *   - the REGULAR elements H_reg = {a | ¬¬a = a} contain ⊥, ⊤ and every ¬a, are
 *     closed under ∧, and satisfy the law of EXCLUDED MIDDLE a ⊔ ¬a = ⊤ for the
 *     Boolean join a ⊔ b := ¬(¬a ∧ ¬b) — the machine-checked basis for
 *     "H_reg is a Boolean algebra" (so the classical core sits exactly on the
 *     regular elements, while the boundary ¬¬a ∖ a is the Sat3::DontKnow region).
 *
 * Excluded middle does NOT hold on all of H (no `a ∨ ¬a = ⊤` law is assumed or
 * derivable) — that is precisely why a behavioral algebra must implement
 * HeytingAlgebra, never classical BooleanAlgebra, on its semi-decidable leg.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Setoid.

(* A Heyting algebra over a carrier with propositional equality. Concrete
   predicate algebras realize this up to their own semantic equivalence; the
   abstract laws below transfer along that setoid. *)
Record HeytingAlgebra := {
  H     : Type;
  hmeet : H -> H -> H;
  hjoin : H -> H -> H;
  htop  : H;
  hbot  : H;
  himp  : H -> H -> H;

  (* bounded lattice laws *)
  meet_comm  : forall a b, hmeet a b = hmeet b a;
  meet_assoc : forall a b c, hmeet a (hmeet b c) = hmeet (hmeet a b) c;
  meet_idem  : forall a, hmeet a a = a;
  join_comm  : forall a b, hjoin a b = hjoin b a;
  absorb_mj  : forall a b, hmeet a (hjoin a b) = a;
  absorb_jm  : forall a b, hjoin a (hmeet a b) = a;
  meet_top   : forall a, hmeet a htop = a;
  join_bot   : forall a, hjoin a hbot = a;

  (* the Heyting adjunction, stated with ≤ unfolded to meet-equality:
     (a ∧ c) ∧ b = a ∧ c   ⟺   c ∧ (a → b) = c. *)
  himp_adj : forall a b c,
    hmeet (hmeet a c) b = hmeet a c <-> hmeet c (himp a b) = c;
}.

Section HeytingFacts.
  Variable A : HeytingAlgebra.

  Local Notation H := (H A).
  Local Notation "x ∧ y" := (hmeet A x y) (at level 40, left associativity).
  Local Notation "x ∨ y" := (hjoin A x y) (at level 50, left associativity).
  Local Notation "⊤" := (htop A).
  Local Notation "⊥" := (hbot A).
  Local Notation "x ⇒ y" := (himp A x y) (at level 60).
  Definition le (x y : H) : Prop := x ∧ y = x.
  Local Notation "x ≤ y" := (le x y) (at level 70).
  Definition hneg (x : H) : H := x ⇒ ⊥.
  Local Notation "¬ x" := (hneg x) (at level 35).

  (* ------------------------------------------------------------------ *)
  (*  ≤ is a partial order; ∧ is the greatest lower bound                *)
  (* ------------------------------------------------------------------ *)

  Lemma le_refl : forall a, a ≤ a.
  Proof. intro a. unfold le. apply (meet_idem A). Qed.

  Lemma le_antisym : forall a b, a ≤ b -> b ≤ a -> a = b.
  Proof.
    intros a b Hab Hba. unfold le in *.
    rewrite <- Hab. rewrite (meet_comm A). rewrite Hba. reflexivity.
  Qed.

  Lemma le_trans : forall a b c, a ≤ b -> b ≤ c -> a ≤ c.
  Proof.
    intros a b c Hab Hbc. unfold le in *.
    rewrite <- Hab. rewrite <- (meet_assoc A). rewrite Hbc. reflexivity.
  Qed.

  Lemma meet_glb_l : forall a b, (a ∧ b) ≤ a.
  Proof.
    intros a b. unfold le.
    rewrite <- (meet_assoc A). rewrite (meet_comm A b a).
    rewrite (meet_assoc A). rewrite (meet_idem A). reflexivity.
  Qed.

  Lemma meet_glb_r : forall a b, (a ∧ b) ≤ b.
  Proof.
    intros a b. unfold le.
    rewrite <- (meet_assoc A). rewrite (meet_idem A). reflexivity.
  Qed.

  Lemma meet_greatest : forall a b c, c ≤ a -> c ≤ b -> c ≤ (a ∧ b).
  Proof.
    intros a b c Hca Hcb. unfold le in *.
    rewrite (meet_assoc A). rewrite Hca. exact Hcb.
  Qed.

  Lemma meet_mono : forall a b c, a ≤ b -> (a ∧ c) ≤ (b ∧ c).
  Proof.
    intros a b c Hab.
    apply meet_greatest.
    - apply (le_trans (a ∧ c) a b); [apply meet_glb_l | exact Hab].
    - apply meet_glb_r.
  Qed.

  Lemma bot_le : forall a, ⊥ ≤ a.
  Proof.
    intro a. unfold le.
    (* ⊥ ∧ a = ⊥ ∨ (⊥ ∧ a) = ⊥, via join_bot and absorption *)
    transitivity (⊥ ∨ (⊥ ∧ a)).
    - rewrite (join_comm A). symmetry. apply (join_bot A).
    - apply (absorb_jm A).
  Qed.

  Lemma meet_bot : forall a, a ∧ ⊥ = ⊥.
  Proof.
    intro a. apply le_antisym.
    - rewrite (meet_comm A). apply meet_glb_l.
    - apply bot_le.
  Qed.

  Lemma le_top : forall a, a ≤ ⊤.
  Proof. intro a. unfold le. apply (meet_top A). Qed.

  (* ------------------------------------------------------------------ *)
  (*  The Heyting counit (modus ponens)                                  *)
  (* ------------------------------------------------------------------ *)

  Lemma imp_counit : forall a b, (a ∧ (a ⇒ b)) ≤ b.
  Proof.
    intros a b.
    (* from the adjunction with c := a ⇒ b and the reflexive right side *)
    assert (Hrefl : (a ⇒ b) ∧ (a ⇒ b) = (a ⇒ b)) by apply (meet_idem A).
    apply (himp_adj A a b (a ⇒ b)) in Hrefl.
    (* Hrefl : (a ∧ (a⇒b)) ∧ b = a ∧ (a⇒b) *)
    unfold le. exact Hrefl.
  Qed.

  Lemma imp_meet : forall a b, a ∧ (a ⇒ b) = a ∧ b.
  Proof.
    intros a b. apply le_antisym.
    - apply meet_greatest; [apply meet_glb_l | apply imp_counit].
    - apply meet_greatest.
      + apply meet_glb_l.
      + (* a ∧ b ≤ a ⇒ b, by adjunction: (a ∧ (a∧b)) ∧ b = a ∧ (a∧b) *)
        apply (himp_adj A a b (a ∧ b)).
        assert (H1 : a ∧ (a ∧ b) = a ∧ b).
        { rewrite (meet_assoc A). rewrite (meet_idem A). reflexivity. }
        rewrite H1.
        (* goal: (a ∧ b) ∧ b = a ∧ b *)
        rewrite <- (meet_assoc A a b b). rewrite (meet_idem A). reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Pseudo-complement and the ¬¬ closure operator                      *)
  (* ------------------------------------------------------------------ *)

  Lemma meet_neg : forall a, a ∧ (¬ a) = ⊥.
  Proof.
    intro a. unfold hneg. rewrite imp_meet. apply meet_bot.
  Qed.

  Lemma neg_meet_comm : forall a, (¬ a) ∧ a = ⊥.
  Proof. intro a. rewrite (meet_comm A). apply meet_neg. Qed.

  (* a ⇒ ⊥ characterization used to land negations below ⊥ targets. *)
  Lemma le_imp_bot : forall a c, (a ∧ c) ≤ ⊥ -> c ≤ (¬ a).
  Proof.
    intros a c H0. unfold hneg. apply (himp_adj A a ⊥ c).
    unfold le in H0. exact H0.
  Qed.

  Lemma neg_antitone : forall a b, a ≤ b -> (¬ b) ≤ (¬ a).
  Proof.
    intros a b Hab. apply le_imp_bot.
    (* a ∧ ¬b ≤ b ∧ ¬b = ⊥ *)
    apply (le_trans (a ∧ (¬ b)) (b ∧ (¬ b)) ⊥).
    - apply meet_mono. exact Hab.
    - rewrite meet_neg. apply le_refl.
  Qed.

  Lemma dneg_extensive : forall a, a ≤ ¬ (¬ a).
  Proof.
    intro a. apply le_imp_bot.
    (* (¬a) ∧ a ≤ ⊥ *)
    rewrite neg_meet_comm. apply le_refl.
  Qed.

  Lemma dneg_mono : forall a b, a ≤ b -> ¬ (¬ a) ≤ ¬ (¬ b).
  Proof.
    intros a b Hab. apply neg_antitone. apply neg_antitone. exact Hab.
  Qed.

  Lemma neg_triple : forall a, ¬ (¬ (¬ a)) = ¬ a.
  Proof.
    intro a. apply le_antisym.
    - (* ¬¬¬a ≤ ¬a : from a ≤ ¬¬a, antitone *)
      apply neg_antitone. apply dneg_extensive.
    - (* ¬a ≤ ¬¬¬a : extensive at ¬a *)
      apply dneg_extensive.
  Qed.

  Theorem dneg_idempotent : forall a, ¬ (¬ (¬ (¬ a))) = ¬ (¬ a).
  Proof.
    intro a. rewrite (neg_triple (¬ a)). reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  §7 reject-safety: a sound complement drops nothing satisfiable     *)
  (* ------------------------------------------------------------------ *)

  Theorem dneg_eq_bot_implies_bot : forall a, ¬ (¬ a) = ⊥ -> a = ⊥.
  Proof.
    intros a Hdn. apply le_antisym.
    - (* a ≤ ¬¬a = ⊥ *)
      apply (le_trans a (¬ (¬ a)) ⊥).
      + apply dneg_extensive.
      + rewrite Hdn. apply le_refl.
    - apply bot_le.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  Regular elements form the Boolean core H_reg                       *)
  (* ------------------------------------------------------------------ *)

  Definition regular (a : H) : Prop := ¬ (¬ a) = a.

  Lemma neg_regular : forall a, regular (¬ a).
  Proof. intro a. unfold regular. apply neg_triple. Qed.

  Lemma neg_top : ¬ ⊤ = ⊥.
  Proof.
    apply le_antisym.
    - (* ¬⊤ ≤ ⊥ : ⊤ ∧ ¬⊤ = ¬⊤ and = ⊥ *)
      assert (Hm : ⊤ ∧ (¬ ⊤) = ⊥) by apply meet_neg.
      rewrite (meet_comm A) in Hm. rewrite (meet_top A) in Hm.
      rewrite Hm. apply le_refl.
    - apply bot_le.
  Qed.

  Lemma neg_bot : ¬ ⊥ = ⊤.
  Proof.
    apply le_antisym.
    - apply le_top.
    - (* ⊤ ≤ ¬⊥ : ⊥ ∧ ⊤ = ⊥, so (⊥ ∧ ⊤) ≤ ⊥ *)
      apply le_imp_bot.
      assert (E : ⊥ ∧ ⊤ = ⊥) by (rewrite (meet_comm A); apply meet_bot).
      rewrite E. apply le_refl.
  Qed.

  Lemma regular_bot : regular ⊥.
  Proof. unfold regular. rewrite neg_bot. apply neg_top. Qed.

  Lemma regular_top : regular ⊤.
  Proof. unfold regular. rewrite neg_top. apply neg_bot. Qed.

  (* Regular elements are closed under meet: ¬¬ collapses on them. *)
  Theorem regular_meet : forall a b, regular a -> regular b -> regular (a ∧ b).
  Proof.
    intros a b Ra Rb. unfold regular in *. apply le_antisym.
    - (* ¬¬(a∧b) ≤ a∧b : ≤ ¬¬a = a and ≤ ¬¬b = b *)
      apply meet_greatest.
      + apply (le_trans (¬ (¬ (a ∧ b))) (¬ (¬ a)) a).
        * apply dneg_mono. apply meet_glb_l.
        * rewrite Ra. apply le_refl.
      + apply (le_trans (¬ (¬ (a ∧ b))) (¬ (¬ b)) b).
        * apply dneg_mono. apply meet_glb_r.
        * rewrite Rb. apply le_refl.
    - apply dneg_extensive.
  Qed.

  (* Boolean join on H_reg, and the law of excluded middle (holds for ALL a). *)
  Definition bjoin (a b : H) : H := ¬ ((¬ a) ∧ (¬ b)).

  Theorem excluded_middle_reg : forall a, bjoin a (¬ a) = ⊤.
  Proof.
    intro a. unfold bjoin.
    (* (¬a) ∧ ¬(¬a) matches meet_neg with a0 := ¬a, giving ⊥; then ¬⊥ = ⊤ *)
    rewrite meet_neg. apply neg_bot.
  Qed.

  (* On regular elements ¬ is involutive, completing the Boolean structure. *)
  Theorem neg_involutive_on_regular : forall a, regular a -> ¬ (¬ a) = a.
  Proof. intros a Ra. exact Ra. Qed.

End HeytingFacts.

Print Assumptions dneg_eq_bot_implies_bot.
Print Assumptions dneg_idempotent.
Print Assumptions excluded_middle_reg.
Print Assumptions regular_meet.
