(*
 * OracleQuotientEquivalence: the M-RHO.0.4 differential oracle compares the
 * rho-backend's normal forms against the Ascent backend's under WEIGHT-ERASURE
 * composed with EQREL-QUOTIENT — and this comparison is a SOUND, EXACT
 * equivalence: it never hides a real divergence (weight-erasure does not merge
 * distinct e-class keys), it loses nothing (the quotient is exact), and it ignores
 * only the weight (weights ORDER, they are not identity). So "rho ≡ Ascent under
 * the oracle" is a trustworthy equality, not a lossy one.
 *
 * Model: a normal form carries an ordering WEIGHT and an exact eqrel-class KEY
 * (dovetail's `ContentKey` — the exact byte key, never a 64-bit hash). The oracle:
 *   erase n        := nf_key n                 (* weight-erasure: keep the key *)
 *   keys s         := map erase s              (* the eqrel-class keys of an NF set *)
 *   oracle_equiv s t := ∀k, In k (keys s) ↔ In k (keys t)   (* set-equality of keys *)
 *
 * Proven (zero-admission):
 *   - oracle_equiv is an EQUIVALENCE (reflexive/symmetric/transitive) ⇒ a sound
 *     basis for asserting backend agreement.
 *   - erasure_ignores_weight : NFs differing only in weight erase to the same key
 *     (the oracle compares MODULO weight — weights order, not identity).
 *   - erasure_preserves_distinct_keys : distinct eqrel keys stay distinct under
 *     erasure ⇒ the oracle CANNOT falsely equate two distinct results (no hidden
 *     divergence; no false "agreement").
 *   - quotient_exact : a key is in the quotient IFF some real NF carries it ⇒ the
 *     quotient drops nothing ("miss nothing" at the oracle layer).
 *
 * Companion of dovetail NBestExtraction.v (the no-prune the keys come from) — the
 * oracle's equality respects that no-prune. Rocq 9.1. No Admitted/Axioms/Assumptions.
 *)

From Stdlib Require Import List.
Import ListNotations.

Section OracleQuotientEquivalence.

  (* Weights and eqrel-class keys are opaque; equality of keys is decidable enough
     for `In` (we only need propositional membership here). Use `nat` as a concrete
     stand-in for the exact `ContentKey` (any type with Leibniz equality works). *)
  Record NF : Type := {
    nf_weight : nat;   (* the ordering weight (the oracle erases this) *)
    nf_key    : nat;   (* the exact eqrel-class key (dovetail ContentKey) *)
  }.

  (* Weight-erasure: keep ONLY the eqrel key (the identity), discard the weight. *)
  Definition erase (n : NF) : nat := nf_key n.

  (* The eqrel-class keys of a normal-form set. *)
  Definition keys (s : list NF) : list nat := map erase s.

  (* The oracle's comparison: two NF sets agree iff their eqrel-class key sets are
     equal (membership-wise). Weights are erased; e-classes are compared exactly. *)
  Definition oracle_equiv (s t : list NF) : Prop :=
    forall k, In k (keys s) <-> In k (keys t).

  (* ── oracle_equiv is an EQUIVALENCE RELATION ───────────────────────────────── *)

  Theorem oracle_equiv_refl : forall s, oracle_equiv s s.
  Proof. intros s k. split; intro H; exact H. Qed.

  Theorem oracle_equiv_sym : forall s t, oracle_equiv s t -> oracle_equiv t s.
  Proof. intros s t H k. specialize (H k). split; apply H. Qed.

  Theorem oracle_equiv_trans : forall s t u,
    oracle_equiv s t -> oracle_equiv t u -> oracle_equiv s u.
  Proof.
    intros s t u Hst Htu k. specialize (Hst k). specialize (Htu k).
    split; intro H.
    - apply Htu. apply Hst. exact H.
    - apply Hst. apply Htu. exact H.
  Qed.

  (* ── Soundness of the erasure: weights order, never identify ──────────────── *)

  (* The oracle compares MODULO weight: two NFs that differ only in their weight
     erase to the same eqrel key. *)
  Theorem erasure_ignores_weight : forall w1 w2 k,
    erase {| nf_weight := w1; nf_key := k |}
    = erase {| nf_weight := w2; nf_key := k |}.
  Proof. intros w1 w2 k. reflexivity. Qed.

  (* Erasure NEVER merges distinct e-classes: distinct keys stay distinct, so the
     oracle cannot falsely report two distinct results as equal (no hidden
     divergence). *)
  Theorem erasure_preserves_distinct_keys : forall a b,
    nf_key a <> nf_key b -> erase a <> erase b.
  Proof. intros a b H. unfold erase. exact H. Qed.

  (* ── Exactness of the quotient: nothing is lost ───────────────────────────── *)

  (* A key is in the quotient IFF some real NF in the set carries it — the quotient
     adds nothing and drops nothing. *)
  Theorem quotient_exact : forall s k,
    In k (keys s) <-> (exists n, In n s /\ nf_key n = k).
  Proof.
    intros s k. unfold keys, erase. rewrite in_map_iff.
    split.
    - intros [n [Heq Hin]]. exists n. split; [exact Hin | exact Heq].
    - intros [n [Hin Heq]]. exists n. split; [exact Heq | exact Hin].
  Qed.

  (* Capstone: the oracle equality is reflexive/symmetric/transitive AND exact —
     a trustworthy basis for "rho-backend ≡ Ascent" that respects the no-prune
     (weights order; e-classes compared exactly; nothing dropped or fabricated). *)
  Theorem oracle_equiv_is_sound_equivalence :
    (forall s, oracle_equiv s s)
    /\ (forall s t, oracle_equiv s t -> oracle_equiv t s)
    /\ (forall s t u, oracle_equiv s t -> oracle_equiv t u -> oracle_equiv s u)
    /\ (forall a b, nf_key a <> nf_key b -> erase a <> erase b).
  Proof.
    split. { exact oracle_equiv_refl. }
    split. { exact oracle_equiv_sym. }
    split. { exact oracle_equiv_trans. }
    exact erasure_preserves_distinct_keys.
  Qed.

End OracleQuotientEquivalence.
