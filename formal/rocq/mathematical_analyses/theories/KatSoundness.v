(*
 * KatSoundness: KAT soundness for Hoare logic.
 *
 * Proves that Kleene Algebra with Tests (KAT) provides a sound proof
 * system for propositional Hoare logic. The main theorem states that
 * if the KAT equation test(p) . e . test(~q) = 0 holds, then the
 * Hoare triple {p} e {q} is valid.
 *
 * ## Theoretical Foundations
 *
 * - Kozen (1997) -- "Kleene algebra with tests." Introduces KAT and
 *   proves that {b} p {c} is valid iff b . p . ~c = 0 in the free KAT.
 * - Kozen & Smith (1996) -- "Kleene algebra with tests: completeness
 *   and decidability." PSPACE decision procedure.
 * - Kozen (2000) -- "On Hoare logic and Kleene algebra with tests."
 *   Survey of the relationship between KAT and Hoare logic.
 *
 * ## Proof Strategy
 *
 * We define:
 *   1. KAT expressions (tests, seq, alt, star, actions)
 *   2. Denotational semantics: denote : kat_expr -> (state -> state -> Prop)
 *   3. Hoare triple validity: {p} e {q} means forall s s', p(s) -> denote(e)(s,s') -> q(s')
 *   4. Main theorem: if test(p).e.test(~q) denotes the empty relation, then {p} e {q} holds
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition           | Rust Code                         | Location
 *   --------------------------|-----------------------------------|--------------------------
 *   bool_test                 | BooleanTest                       | kat.rs:56-69
 *   kat_expr                  | KatExpr                           | kat.rs:131-147
 *   test_denote               | eval_test()                       | kat.rs:421-430
 *   denote                    | (symbolic bisimulation semantics) | kat.rs:312-382
 *   hoare_valid                | verify_hoare_triple()            | kat.rs:568-578
 *   hoare_condition           | KatExpr::hoare_condition()        | kat.rs:179-184
 *   kat_simplify              | simplify()                        | kat.rs:516-553
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.
From Hammer Require Import Tactics.
From Equations Require Import Equations.

Import ListNotations.

(* ===================================================================== *)
(*  State Model                                                           *)
(* ===================================================================== *)

Section KATSoundness.

  (** Abstract state type for program semantics *)
  Variable state : Type.

  (** A predicate on states *)
  Definition state_pred := state -> Prop.

  (** A binary relation on states (program semantics) *)
  Definition state_rel := state -> state -> Prop.

  (* ================================================================== *)
  (*  Boolean Test Expressions                                           *)
  (* ================================================================== *)

  (** Boolean tests form a Boolean subalgebra of the Kleene algebra.
      They correspond to program assertions / guards. *)
  Inductive bool_test : Type :=
    | BTrue    (* Boolean true: always passes *)
    | BFalse   (* Boolean false: always fails *)
    | BAtom    (n : nat)  (* Atomic test, identified by a natural number *)
    | BNot     (t : bool_test)
    | BAnd     (t1 t2 : bool_test)
    | BOr      (t1 t2 : bool_test).

  (** Semantics of Boolean tests: a valuation maps atom indices to
      state predicates. *)
  Variable atom_val : nat -> state_pred.

  (** Evaluate a Boolean test at a state under the atom valuation. *)
  Fixpoint test_denote (t : bool_test) (s : state) : Prop :=
    match t with
    | BTrue => True
    | BFalse => False
    | BAtom n => atom_val n s
    | BNot t' => ~ test_denote t' s
    | BAnd t1 t2 => test_denote t1 s /\ test_denote t2 s
    | BOr t1 t2 => test_denote t1 s \/ test_denote t2 s
    end.

  (** Decidability of test evaluation *)
  Hypothesis test_decidable : forall t s,
    test_denote t s \/ ~ test_denote t s.

  (* ================================================================== *)
  (*  KAT Expressions                                                    *)
  (* ================================================================== *)

  (** KAT expressions combine Kleene algebra operators with Boolean tests.
      They represent programs / parse actions. *)
  Inductive kat_expr : Type :=
    | KZero                     (* Zero: failure / empty language *)
    | KOne                      (* One: skip / identity *)
    | KTest  (t : bool_test)    (* Boolean test *)
    | KAct   (n : nat)          (* Atomic action, identified by nat *)
    | KSeq   (e1 e2 : kat_expr) (* Sequential composition: e1 ; e2 *)
    | KAlt   (e1 e2 : kat_expr) (* Alternation / choice: e1 + e2 *)
    | KStar  (e : kat_expr)     (* Kleene star: e* *).

  (* ================================================================== *)
  (*  Denotational Semantics                                             *)
  (* ================================================================== *)

  (** Action semantics: maps action indices to state relations.
      action_val n s s' means "action n transforms state s to state s'". *)
  Variable action_val : nat -> state_rel.

  (** Kleene star of a relation: reflexive-transitive closure.
      We model this as finite iteration (exists n, rel^n). *)
  Inductive rel_star (R : state_rel) : state_rel :=
    | star_refl : forall s, rel_star R s s
    | star_step : forall s1 s2 s3,
        R s1 s2 -> rel_star R s2 s3 -> rel_star R s1 s3.

  (** Denotational semantics of KAT expressions.
      denote e s s' means "expression e can transform state s to s'". *)
  Fixpoint denote (e : kat_expr) : state_rel :=
    match e with
    | KZero => fun _ _ => False
    | KOne => fun s s' => s = s'
    | KTest t => fun s s' => test_denote t s /\ s = s'
    | KAct n => action_val n
    | KSeq e1 e2 => fun s s' => exists s_mid, denote e1 s s_mid /\ denote e2 s_mid s'
    | KAlt e1 e2 => fun s s' => denote e1 s s' \/ denote e2 s s'
    | KStar e => rel_star (denote e)
    end.

  (* ================================================================== *)
  (*  Hoare Triple Validity                                              *)
  (* ================================================================== *)

  (** A Hoare triple {p} e {q} is valid iff:
      for all states s and s', if p holds at s and e transforms s to s',
      then q holds at s'. *)
  Definition hoare_valid (p : bool_test) (e : kat_expr) (q : bool_test) : Prop :=
    forall s s', test_denote p s -> denote e s s' -> test_denote q s'.

  (* ================================================================== *)
  (*  KAT Encoding of Hoare Triples                                      *)
  (* ================================================================== *)

  (** The Hoare condition: test(p) . e . test(~q).
      If this expression denotes the empty relation, the triple is valid.
      This is the key encoding from Kozen (1997). *)
  Definition hoare_condition (p : bool_test) (e : kat_expr) (q : bool_test)
    : kat_expr :=
    KSeq (KTest p) (KSeq e (KTest (BNot q))).

  (** The "empty" predicate on KAT expressions: the denotation is
      the empty relation (no pair (s, s') satisfies it). *)
  Definition denotes_empty (e : kat_expr) : Prop :=
    forall s s', ~ denote e s s'.

  (* ================================================================== *)
  (*  Auxiliary Lemmas                                                    *)
  (* ================================================================== *)

  (** Test denotation produces identity pairs: if KTest t relates s to s',
      then s = s'. *)
  Lemma test_denote_identity : forall t s s',
    denote (KTest t) s s' -> s = s'.
  Proof.
    intros t s s' [_ Heq]. exact Heq.
  Qed.

  (** Test denotation passes the test: if KTest t relates s to s',
      then test_denote t s holds. *)
  Lemma test_denote_satisfies : forall t s s',
    denote (KTest t) s s' -> test_denote t s.
  Proof.
    intros t s s' [Ht _]. exact Ht.
  Qed.

  (** Sequential composition is associative in denotation. *)
  Lemma seq_assoc : forall e1 e2 e3 s s',
    denote (KSeq (KSeq e1 e2) e3) s s' <->
    denote (KSeq e1 (KSeq e2 e3)) s s'.
  Proof. simpl; split; hauto lq: on. Qed.

  (** KZero is a left annihilator for Seq. *)
  Lemma seq_zero_left : forall e s s',
    denote (KSeq KZero e) s s' -> False.
  Proof.
    intros e s s' [smid [Habs _]]. exact Habs.
  Qed.

  (** KZero is a right annihilator for Seq. *)
  Lemma seq_zero_right : forall e s s',
    denote (KSeq e KZero) s s' -> False.
  Proof.
    intros e s s' [smid [_ Habs]]. exact Habs.
  Qed.

  (** KOne is a left identity for Seq. *)
  Lemma seq_one_left : forall e s s',
    denote (KSeq KOne e) s s' <-> denote e s s'.
  Proof. simpl; split; hauto lq: on. Qed.

  (** KOne is a right identity for Seq. *)
  Lemma seq_one_right : forall e s s',
    denote (KSeq e KOne) s s' <-> denote e s s'.
  Proof. simpl; split; hauto lq: on. Qed.

  (** KAlt is commutative in denotation. *)
  Lemma alt_comm : forall e1 e2 s s',
    denote (KAlt e1 e2) s s' <-> denote (KAlt e2 e1) s s'.
  Proof.
    intros e1 e2 s s'. split; intros [H | H]; [right | left | right | left]; exact H.
  Qed.

  (** BNot negation: test_denote (BNot q) s iff ~ test_denote q s. *)
  Lemma bnot_denote : forall q s,
    test_denote (BNot q) s <-> ~ test_denote q s.
  Proof.
    intros q s. simpl. split; auto.
  Qed.

  (* ================================================================== *)
  (*  Main Soundness Theorem                                             *)
  (* ================================================================== *)

  (** SOUNDNESS: If test(p) . e . test(~q) denotes the empty relation,
      then the Hoare triple {p} e {q} is valid.

      This is the core result from Kozen (1997): the KAT equation
      p . e . ~q = 0 implies the Hoare triple {p} e {q}. *)
  Theorem kat_hoare_soundness :
    forall p e q,
      denotes_empty (hoare_condition p e q) ->
      hoare_valid p e q.
  Proof.
    intros p e q Hempty.
    unfold hoare_valid. intros s s' Hpre Hrun.
    (* We proceed by contradiction: assume ~q(s') and derive
       that the hoare_condition is non-empty. *)
    destruct (test_decidable q s') as [Hq | Hnq].
    - (* q holds at s': done *)
      exact Hq.
    - (* ~q holds at s': construct a witness for the hoare_condition *)
      exfalso.
      apply (Hempty s s').
      (* Show: denote (KSeq (KTest p) (KSeq e (KTest (BNot q)))) s s' *)
      unfold hoare_condition.
      simpl. exists s. split.
      + (* KTest p: p holds at s, identity *)
        split; [exact Hpre | reflexivity].
      + (* KSeq e (KTest (BNot q)): e transforms s to s', then ~q at s' *)
        exists s'. split.
        * exact Hrun.
        * split; [exact Hnq | reflexivity].
  Qed.

  (* ================================================================== *)
  (*  Completeness Direction                                             *)
  (* ================================================================== *)

  (** COMPLETENESS: If the Hoare triple {p} e {q} is valid, then
      test(p) . e . test(~q) denotes the empty relation.

      Together with soundness, this establishes the biconditional:
      {p} e {q}  <->  p . e . ~q = 0  (in the relational model). *)
  Theorem kat_hoare_completeness :
    forall p e q,
      hoare_valid p e q ->
      denotes_empty (hoare_condition p e q).
  Proof.
    intros p e q Hvalid.
    unfold denotes_empty, hoare_condition.
    intros s s' Hden.
    simpl in Hden.
    destruct Hden as [s1 [[Hps Heq1] [s2 [Hrun [Hnq Heq2]]]]].
    subst s1. subst s2.
    (* From hoare_valid: p(s) /\ e(s, s') -> q(s') *)
    apply Hnq.
    apply Hvalid with s; assumption.
  Qed.

  (** The main biconditional: {p} e {q} iff p . e . ~q = 0. *)
  Theorem kat_hoare_iff :
    forall p e q,
      hoare_valid p e q <-> denotes_empty (hoare_condition p e q).
  Proof.
    intros p e q. split.
    - apply kat_hoare_completeness.
    - apply kat_hoare_soundness.
  Qed.

  (* ================================================================== *)
  (*  KAT Algebraic Laws (used by simplify() in kat.rs)                  *)
  (* ================================================================== *)

  (** These laws verify the algebraic identities used by the simplify()
      function in the Rust implementation. They are stated as semantic
      equivalences (same denotation). *)

  (** Zero is the identity for Alt. *)
  Theorem alt_zero_left : forall e s s',
    denote (KAlt KZero e) s s' <-> denote e s s'.
  Proof.
    intros e s s'. split.
    - intros [Habs | He]; [destruct Habs | exact He].
    - intros He. right. exact He.
  Qed.

  Theorem alt_zero_right : forall e s s',
    denote (KAlt e KZero) s s' <-> denote e s s'.
  Proof.
    intros e s s'. split.
    - intros [He | Habs]; [exact He | destruct Habs].
    - intros He. left. exact He.
  Qed.

  (** Alt is idempotent: e + e = e. *)
  Theorem alt_idempotent : forall e s s',
    denote (KAlt e e) s s' <-> denote e s s'.
  Proof.
    intros e s s'. split.
    - intros [He | He]; exact He.
    - intros He. left. exact He.
  Qed.

  (** Star of Zero is One: 0* = 1 *)
  Theorem star_zero : forall s s',
    denote (KStar KZero) s s' <-> denote KOne s s'.
  Proof.
    intros s s'. simpl. split.
    - intros Hstar. inversion Hstar.
      + reflexivity.
      + (* rel_star step case: KZero relates s1 to s2, contradiction *)
        destruct H.
    - intros Heq. subst. apply star_refl.
  Qed.

  (** Helper: rel_star of identity is identity.
      Uses standard induction instead of fix IH. *)
  Lemma rel_star_id : forall (s s' : state),
    rel_star (fun a b : state => a = b) s s' -> s = s'.
  Proof.
    intros s s' Hstar.
    induction Hstar.
    - reflexivity.
    - simpl in *. congruence.
  Qed.

  (** Star of One is One: 1* = 1 *)
  Theorem star_one : forall s s',
    denote (KStar KOne) s s' <-> denote KOne s s'.
  Proof.
    intros s s'. simpl. split.
    - apply rel_star_id.
    - intros Heq. subst. apply star_refl.
  Qed.

  (** Test(True) = One *)
  Theorem test_true_is_one : forall s s',
    denote (KTest BTrue) s s' <-> denote KOne s s'.
  Proof.
    intros s s'. simpl. split.
    - intros [_ Heq]. exact Heq.
    - intros Heq. split; [exact I | exact Heq].
  Qed.

  (** Test(False) = Zero *)
  Theorem test_false_is_zero : forall s s',
    denote (KTest BFalse) s s' <-> denote KZero s s'.
  Proof.
    intros s s'. simpl. split.
    - intros [Habs _]. destruct Habs.
    - intros Habs. destruct Habs.
  Qed.

  (** Test followed by its negation is Zero: b . ~b = 0 *)
  Theorem test_and_neg_is_zero : forall t s s',
    denote (KSeq (KTest t) (KTest (BNot t))) s s' -> False.
  Proof.
    intros t s s' [smid [[Ht Heq1] [Hnt Heq2]]].
    subst. simpl in Hnt. apply Hnt. exact Ht.
  Qed.

  (* ================================================================== *)
  (*  Hoare Logic Derived Rules                                          *)
  (* ================================================================== *)

  (** Rule of consequence: strengthening precondition, weakening postcondition *)
  Theorem hoare_consequence :
    forall p p' e q q',
      (forall s, test_denote p s -> test_denote p' s) ->
      hoare_valid p' e q' ->
      (forall s, test_denote q' s -> test_denote q s) ->
      hoare_valid p e q.
  Proof.
    intros p p' e q q' Hpre Hvalid Hpost.
    unfold hoare_valid. intros s s' Hp Hrun.
    apply Hpost. apply Hvalid with s.
    - apply Hpre. exact Hp.
    - exact Hrun.
  Qed.

  (** Skip rule: {p} skip {p} *)
  Theorem hoare_skip : forall p, hoare_valid p KOne p.
  Proof.
    intros p. unfold hoare_valid. intros s s' Hp Hskip.
    simpl in Hskip. subst. exact Hp.
  Qed.

  (** Sequencing rule: {p} e1 {r}, {r} e2 {q} implies {p} e1;e2 {q} *)
  Theorem hoare_seq :
    forall p e1 r e2 q,
      hoare_valid p e1 r ->
      hoare_valid r e2 q ->
      hoare_valid p (KSeq e1 e2) q.
  Proof.
    intros p e1 r e2 q H1 H2.
    unfold hoare_valid. intros s s' Hp Hseq.
    simpl in Hseq. destruct Hseq as [smid [He1 He2]].
    apply H2 with smid.
    - apply H1 with s; assumption.
    - exact He2.
  Qed.

  (** Choice rule: {p} e1 {q}, {p} e2 {q} implies {p} e1+e2 {q} *)
  Theorem hoare_choice :
    forall p e1 e2 q,
      hoare_valid p e1 q ->
      hoare_valid p e2 q ->
      hoare_valid p (KAlt e1 e2) q.
  Proof.
    intros p e1 e2 q H1 H2.
    unfold hoare_valid. intros s s' Hp Halt.
    simpl in Halt. destruct Halt as [He1 | He2].
    - apply H1 with s; assumption.
    - apply H2 with s; assumption.
  Qed.

  (** Star rule: {p} e {p} implies {p} e* {p} (loop invariant) *)
  Theorem hoare_star :
    forall p e,
      hoare_valid p e p ->
      hoare_valid p (KStar e) p.
  Proof.
    intros p e Hinv.
    unfold hoare_valid. intros s s' Hp Hstar.
    simpl in Hstar. induction Hstar as [s0 | s0 s1 s2 Hstep Hrest IH].
    - exact Hp.
    - apply IH. apply Hinv with s0; assumption.
  Qed.

  (** Zero rule: {p} 0 {q} for any p, q (the program never terminates) *)
  Theorem hoare_zero : forall p q, hoare_valid p KZero q.
  Proof.
    intros p q. unfold hoare_valid. intros s s' _ Habs.
    simpl in Habs. destruct Habs.
  Qed.

  (* ================================================================== *)
  (*  All Hoare Rules are Sound via KAT Encoding                         *)
  (* ================================================================== *)

  (** Verify that each Hoare rule is consistent with the KAT encoding:
      applying the rule preserves the emptiness of the hoare_condition. *)

  (** Skip via KAT: test(p) . 1 . test(~p) = 0 *)
  Theorem kat_skip_sound : forall p,
    denotes_empty (hoare_condition p KOne p).
  Proof.
    intros p. apply kat_hoare_completeness. apply hoare_skip.
  Qed.

  (** Zero via KAT: test(p) . 0 . test(~q) = 0 for any p, q *)
  Theorem kat_zero_sound : forall p q,
    denotes_empty (hoare_condition p KZero q).
  Proof.
    intros p q. apply kat_hoare_completeness. apply hoare_zero.
  Qed.

End KATSoundness.

(* Note: Section variables are automatically generalized after End.
   We omit explicit Arguments declarations to avoid fragile parameter
   ordering issues. Use @ for explicit application if needed. *)
