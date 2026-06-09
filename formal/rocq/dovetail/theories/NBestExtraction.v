(*
 * NBestExtraction: the Dovetail best-first extractor's SELECTION-LAYER no-prune
 * invariant.
 *
 * Models the extractor (dovetail/src/extract.rs) at the SELECTION layer: from the
 * candidate derivations of an e-class, the output removes an alternative ONLY
 * when its composed weight is the semiring zero (0̄, modeled as `None`). This is
 * the direct formalization of the engine's governing invariant — *weight ORDERS,
 * never PRUNES; the only removal is by evidence* — and of plan Invariant 1 (no
 * dropped alternatives).
 *
 * Proven here (zero-Admitted, zero-Axiom):
 *   - select_complete / no_unrefuted_alternative_dropped : every non-0̄
 *     alternative SURVIVES (no-miss at the selection layer).
 *   - select_sound / select_only_removes_zero : the ONLY removal is the
 *     semiring zero.
 *   - equal_weight_both_survive : equal-weight DISTINCT alternatives BOTH
 *     survive (no weight-merge) — mirrors parser_preserves_ambiguous_alternatives.
 *   - select_prefix_monotone : a longer demand prefix never drops what a shorter
 *     one surfaced (resumability of the lazy stream).
 *   - select_exhausts_on_demand : every non-0̄ alternative appears at some demand
 *     k (exhaustive-on-demand).
 *
 * Companion obligations (NOT proven here; see the extractor design):
 *   - the best-first ORDERING of the output (Huang-Chiang Alg.3 sortedness), and
 *   - the hypergraph-recursion COMPLETENESS (the candidate set = ALL derivations).
 *   The latter is currently the 9 Rust no-miss tests (extract.rs T1-T9). The
 *   e-graph exact-key dedup no-loss is covered by EGraphBudgetDedup.v.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

(*  Spec-to-Code Traceability                                              *)
(*  ====================================================================  *)
(*  Rocq Definition          | Rust Implementation              | Location *)
(*  -------------------------+----------------------------------+--------- *)
(*  Cand (option nat * nat)  | Derivation { weight, key }       | extract.rs *)
(*  is_zero = (weight None)  | W::is_zero (composed weight = 0̄) | extract.rs *)
(*  select = filter non-zero | kth: built.push iff !is_zero     | extract.rs *)
(*  ====================================================================  *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

Import ListNotations.

Section NBestExtraction.

  (* A candidate derivation: an optional composed weight (None = the semiring
     zero 0̄, "refuted") and a content key (nat, standing for the exact,
     injective ContentKey). *)
  Definition Cand : Type := (option nat * nat)%type.
  Definition cweight (c : Cand) : option nat := fst c.
  Definition is_zero (c : Cand) : bool :=
    match cweight c with
    | None => true
    | Some _ => false
    end.

  (* The extractor's selection: keep exactly the non-0̄ candidates. The ONLY
     removal is by evidence (weight = 0̄ = None); nothing else is dropped. *)
  Definition select (l : list Cand) : list Cand :=
    filter (fun c => negb (is_zero c)) l.

  (* Selection yields only original, non-0̄ candidates. *)
  Lemma select_sound : forall c l,
    In c (select l) -> In c l /\ is_zero c = false.
  Proof.
    intros c l Hin. unfold select in Hin. apply filter_In in Hin.
    destruct Hin as [Hin Hb]. split.
    - exact Hin.
    - apply negb_true_iff. exact Hb.
  Qed.

  (* No-miss (the anti-prune core): every non-0̄ candidate survives selection. *)
  Lemma select_complete : forall c l,
    In c l -> is_zero c = false -> In c (select l).
  Proof.
    intros c l Hin Hnz. unfold select. apply filter_In. split.
    - exact Hin.
    - rewrite Hnz. reflexivity.
  Qed.

  (* The ONLY removal is the semiring zero: anything in the output is non-0̄. *)
  Theorem select_only_removes_zero : forall c l,
    In c (select l) -> is_zero c = false.
  Proof. intros c l H. apply select_sound in H. tauto. Qed.

  (* The anti-prune fence, named: an unrefuted (non-0̄) alternative is NEVER
     absent from the output. Weight ORDERS; it never PRUNES. *)
  Theorem no_unrefuted_alternative_dropped : forall c l,
    In c l -> is_zero c = false -> In c (select l).
  Proof. exact select_complete. Qed.

  (* Equal-weight DISTINCT alternatives BOTH survive (no weight-merge); mirrors
     parser_preserves_ambiguous_alternatives at the extraction layer. *)
  Theorem equal_weight_both_survive : forall w k1 k2 l,
    In (Some w, k1) l -> In (Some w, k2) l -> k1 <> k2 ->
    In (Some w, k1) (select l) /\ In (Some w, k2) (select l).
  Proof.
    intros w k1 k2 l H1 H2 _. split; apply select_complete.
    - exact H1.
    - reflexivity.
    - exact H2.
    - reflexivity.
  Qed.

  (* Helper: membership in a demand prefix implies membership overall. *)
  Lemma in_firstn : forall (n : nat) (x : Cand) (l : list Cand),
    In x (firstn n l) -> In x l.
  Proof.
    intros n x l H.
    rewrite <- (firstn_skipn n l).
    apply in_or_app. left. exact H.
  Qed.

  (* Resumability: a longer demand prefix never drops what a shorter one
     surfaced (the lazy stream only grows). *)
  Theorem select_prefix_monotone : forall k x l,
    In x (firstn k (select l)) -> In x (firstn (S k) (select l)).
  Proof.
    intros k x l H.
    apply (in_firstn k x (firstn (S k) (select l))).
    rewrite firstn_firstn.
    replace (Nat.min k (S k)) with k by lia.
    exact H.
  Qed.

  (* Exhaustive-on-demand: every non-0̄ alternative appears at some demand k. *)
  Theorem select_exhausts_on_demand : forall c l,
    In c l -> is_zero c = false ->
    exists k, In c (firstn k (select l)).
  Proof.
    intros c l Hin Hnz.
    exists (length (select l)).
    rewrite firstn_all.
    apply select_complete; assumption.
  Qed.

End NBestExtraction.
