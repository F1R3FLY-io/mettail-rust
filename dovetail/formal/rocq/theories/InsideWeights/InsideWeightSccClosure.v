(*
 * InsideWeightSccClosure: the Dovetail cyclic inside-weight closure
 * (`wta::compute_inside_closed` / `solve_scc` + rigail `solve_scc_weights_newton`)
 * computes the EXACT ⊕-aggregate over ALL derivations of an e-class — including
 * those that go around a cycle — so the best-first extractor's admissible
 * heuristic MISSES NOTHING.
 *
 * ─────────────────────────────────────────────────────────────────────────────
 * What the Rust does (dovetail/src/wta.rs):
 *   inside(q) = ⊕_{node ∈ q} weigh(node) ⊗ ⊗_{c ∈ children(node)} inside(c).
 * For an acyclic e-graph this is a well-founded fixpoint (`compute_inside_acyclic`).
 * For a CYCLE the equation is recursive; `compute_inside_closed` decomposes the
 * e-graph into SCCs (Tarjan) and, for each NON-trivial SCC, calls `solve_scc`,
 * which builds one `PackingFactored` per e-node:
 *   - target_i        = SCC-local index of the parent class,
 *   - outside_product = weigh(node) ⊗ Π_{c ∉ SCC} inside(c)   (a solved CONSTANT),
 *   - in_scc_children = the SCC-local indices of the in-SCC children,
 * and solves the per-SCC system with rigail `solve_scc_weights_newton`
 * (Esparza–Kiefer–Luttenberger Newton over a star semiring; Lehmann matrix-star
 * per iteration; a linear fast-path when every node has ≤ 1 in-SCC child).
 *
 * ─────────────────────────────────────────────────────────────────────────────
 * What THIS file proves (zero-Admitted, zero-Axiom, zero-Assumption beyond the
 * algebraic STRUCTURE, which is discharged by a concrete instance):
 *
 *   (A) SCALAR / SELF-LOOP closure is EXACT: `kstar a ⊗ b` is the ≤-LEAST
 *       fixpoint of `x = b ⊕ a ⊗ x` (`star_closure_is_lfp`). The least fixpoint
 *       IS the ⊕-aggregate over all (infinitely many, cycle-unfolded) derivations
 *       — so for a self-looping class the closed inside weight misses none of them.
 *       This is the 1-D case the Rust linear fast-path takes for a self-loop
 *       (`closed_inside_exact_on_self_cycle`).
 *
 *   (B) The SCC→PackingFactored LOWERING is FAITHFUL: `solve_scc`'s re-indexing
 *       (outside_product = weigh ⊗ Π out-of-SCC; in_scc_children = the in-SCC
 *       indices) reproduces the e-graph inside recurrence EXACTLY, term for term
 *       (`lowering_factor_faithful`, `lowered_node_faithful`, `lowered_eq_recurrence`).
 *       Hence the lowered system and the original recurrence have the SAME
 *       fixpoints (`lowering_preserves_fixpoints`): solving the lowered system
 *       solves the recurrence — no derivation is dropped by the re-indexing. This
 *       is precisely the obligation named in the `wta.rs::compute_inside_closed`
 *       doc-comment.
 *
 *   (C) TRIVIAL SCCs are a NO-OP: a singleton class with no self-loop (all its
 *       children are out-of-SCC) has a lowered system constant in the unknowns,
 *       equal to the acyclic value already held — so `compute_inside_closed`'s
 *       `continue` (skipping `solve_scc`) is sound (`trivial_scc_constant`).
 *
 *   (D) NON-VACUITY: the Boolean reachability commutative Kleene algebra is a
 *       concrete instance of the structure, so every theorem above holds for a
 *       real, inhabited weight algebra (`bool_cka`, `_nonvacuous_*`).
 *
 * ─────────────────────────────────────────────────────────────────────────────
 * Scope, honestly stated:
 *   - The algebraic structure is a COMMUTATIVE idempotent star semiring
 *     (a commutative Kleene algebra; Kozen, "A completeness theorem for Kleene
 *     algebras…", Inf. & Comput. 110(2), 1994). Commutativity is REQUIRED for the
 *     lowering: `solve_scc` pulls out-of-SCC factors out of the source-ordered
 *     child product into `outside_product`, which preserves the value only when ⊗
 *     commutes. The inside-weight cost semirings (rigail `TropicalWeight` = (min,+),
 *     Viterbi, probability) ARE commutative — these are the weights the heuristic
 *     uses; the dovetail wta.rs tests all use `TropicalWeight`.
 *   - The n-D MULTI-call Newton CONVERGENCE (an e-node with ≥ 2 children in the
 *     same SCC) is Esparza, Kiefer & Luttenberger, "An Extension of Newton's
 *     Method to ω-Continuous Semirings," DLT 2007 — a published theorem rigail
 *     implements and cites; it is NOT restated as a Coq axiom here. What this file
 *     contributes is everything that is OURS to prove: the lowering faithfulness
 *     (so that theorem applies to the RIGHT system), the least-fixpoint
 *     characterization (so any correct solver's output is the exact aggregate),
 *     the scalar/linear self-loop closed form, and the trivial-SCC no-op.
 *
 * Companion: NBestExtraction.v (selection no-prune + best-first ordering) and
 * EnumerationCompleteness.v (hypergraph-recursion completeness) close the
 * extractor's no-miss over the candidate SET and ORDER; this file closes the
 * no-miss of the WEIGHT the extractor orders by, on cyclic e-graphs.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no free Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Import ListNotations.

(* ════════════════════════════════════════════════════════════════════════════
 * The algebraic structure: a commutative idempotent star semiring
 * (= a commutative Kleene algebra, Kozen 1994). The law fields are the DEFINITION
 * of the structure (discharged by `bool_cka` below) — not global axioms; every
 * theorem is universally quantified over instances, so `Print Assumptions` is
 * clean.
 * ════════════════════════════════════════════════════════════════════════════ *)

Class CommKleeneAlgebra (K : Type) := {
  kzero  : K;
  kone   : K;
  kplus  : K -> K -> K;
  ktimes : K -> K -> K;
  kstar  : K -> K;

  (* (K, ⊕, 0̄) — commutative idempotent monoid (the ambiguity ⊕: orders, the
     idempotence is what makes the natural order a semilattice). *)
  kplus_comm   : forall a b, kplus a b = kplus b a;
  kplus_assoc  : forall a b c, kplus (kplus a b) c = kplus a (kplus b c);
  kplus_zero_l : forall a, kplus kzero a = a;
  kplus_idem   : forall a, kplus a a = a;

  (* (K, ⊗, 1̄) — commutative monoid (cost accumulation; commutative for the
     inside-weight cost semirings — see the file header). *)
  ktimes_comm  : forall a b, ktimes a b = ktimes b a;
  ktimes_assoc : forall a b c, ktimes (ktimes a b) c = ktimes a (ktimes b c);
  ktimes_one_l : forall a, ktimes kone a = a;

  (* 0̄ annihilates, ⊗ distributes over ⊕. *)
  ktimes_zero_l       : forall a, ktimes kzero a = kzero;
  ktimes_plus_distr_l : forall a b c,
    ktimes a (kplus b c) = kplus (ktimes a b) (ktimes a c);

  (* Kleene star (Kozen 1994): the unfold law + the left ⊕-induction law.
     `kle a b := kplus a b = b` is the natural (semilattice) order. *)
  kstar_unfold_l : forall a, kstar a = kplus kone (ktimes a (kstar a));
  kstar_ind_l    : forall a b x,
    kplus (kplus b (ktimes a x)) x = x ->
    kplus (ktimes (kstar a) b) x = x;
}.

Section Theory.

  Context {K : Type} {KA : CommKleeneAlgebra K}.

  (* ── Derived semiring lemmas (right-handed companions, via commutativity). ── *)

  Lemma kplus_zero_r : forall a, kplus a kzero = a.
  Proof. intros a. rewrite kplus_comm. apply kplus_zero_l. Qed.

  Lemma ktimes_one_r : forall a, ktimes a kone = a.
  Proof. intros a. rewrite ktimes_comm. apply ktimes_one_l. Qed.

  Lemma ktimes_zero_r : forall a, ktimes a kzero = kzero.
  Proof. intros a. rewrite ktimes_comm. apply ktimes_zero_l. Qed.

  Lemma ktimes_plus_distr_r : forall a b c,
    ktimes (kplus a b) c = kplus (ktimes a c) (ktimes b c).
  Proof.
    intros a b c.
    rewrite ktimes_comm. rewrite ktimes_plus_distr_l.
    rewrite (ktimes_comm c a), (ktimes_comm c b). reflexivity.
  Qed.

  (* ── The natural order of the semilattice (K, ⊕): a ≤ b ⟺ a ⊕ b = b. ── *)

  Definition kle (a b : K) : Prop := kplus a b = b.

  Lemma kle_refl : forall a, kle a a.
  Proof. intros a. unfold kle. apply kplus_idem. Qed.

  Lemma kle_trans : forall a b c, kle a b -> kle b c -> kle a c.
  Proof.
    unfold kle. intros a b c Hab Hbc.
    rewrite <- Hbc. rewrite <- kplus_assoc. rewrite Hab. reflexivity.
  Qed.

  Lemma kle_antisym : forall a b, kle a b -> kle b a -> a = b.
  Proof.
    unfold kle. intros a b Hab Hba.
    rewrite <- Hab. rewrite kplus_comm. rewrite Hba. reflexivity.
  Qed.

  (* ════════════════════════════════════════════════════════════════════════
   * (A) SCALAR / SELF-LOOP closure is EXACT.
   *
   * For a self-looping class with self-edge weight `a` and exit weight `b`, the
   * inside equation is `x = b ⊕ a ⊗ x`. `kstar a ⊗ b` is its LEAST fixpoint =
   * the ⊕-aggregate over all cycle-unfolded derivations (b, a⊗b, a²⊗b, …),
   * missing none. This is the 1-D linear case the Rust fast-path solves.
   * ════════════════════════════════════════════════════════════════════════ *)

  Theorem star_closure_is_fixpoint : forall a b,
    kplus b (ktimes a (ktimes (kstar a) b)) = ktimes (kstar a) b.
  Proof.
    intros a b.
    assert (Hu : ktimes (kstar a) b
                 = kplus b (ktimes a (ktimes (kstar a) b))).
    { rewrite kstar_unfold_l at 1.
      rewrite ktimes_plus_distr_r.
      rewrite ktimes_one_l.
      rewrite ktimes_assoc. reflexivity. }
    symmetry. exact Hu.
  Qed.

  (* Leastness IS the Kleene left-induction law (Kozen 1994), applied. *)
  Theorem star_closure_is_least : forall a b x,
    kle (kplus b (ktimes a x)) x -> kle (ktimes (kstar a) b) x.
  Proof. unfold kle. intros a b x H. apply kstar_ind_l. exact H. Qed.

  Definition is_lfp (f : K -> K) (m : K) : Prop :=
    f m = m /\ forall y, kle (f y) y -> kle m y.

  Theorem star_closure_is_lfp : forall a b,
    is_lfp (fun x => kplus b (ktimes a x)) (ktimes (kstar a) b).
  Proof.
    intros a b. split.
    - apply star_closure_is_fixpoint.
    - intros y H. apply star_closure_is_least. exact H.
  Qed.

  (* ════════════════════════════════════════════════════════════════════════
   * (B) The SCC→PackingFactored LOWERING is FAITHFUL.
   *
   * Model a node's children as a list of `ChildRef`: each child is either an
   * in-SCC unknown (referenced by its SCC-local index into the unknown vector
   * `y`) or an out-of-SCC child carrying its already-solved constant inside
   * weight. `solve_scc` re-groups the source-ordered child product into
   * (Π out-of-SCC) ⊗ (Π in-SCC); we prove this regrouping preserves the value.
   * ════════════════════════════════════════════════════════════════════════ *)

  Inductive ChildRef : Type :=
    | InScc  : nat -> ChildRef     (* SCC-local index of an in-SCC child unknown *)
    | OutScc : K -> ChildRef.      (* an out-of-SCC child's solved inside weight  *)

  Definition child_factor (y : list K) (c : ChildRef) : K :=
    match c with
    | InScc j  => nth j y kzero
    | OutScc w => w
    end.

  (* The e-graph recurrence's child product: ALL children, in source order. *)
  Definition full_product (y : list K) (cs : list ChildRef) : K :=
    fold_right (fun c acc => ktimes (child_factor y c) acc) kone cs.

  (* solve_scc's `outside_product` contribution: the out-of-SCC children only. *)
  Definition out_product (cs : list ChildRef) : K :=
    fold_right
      (fun c acc => match c with OutScc w => ktimes w acc | InScc _ => acc end)
      kone cs.

  (* solve_scc's in-SCC factor: the in-SCC children only (the recursive part). *)
  Definition in_product (y : list K) (cs : list ChildRef) : K :=
    fold_right
      (fun c acc => match c with InScc j => ktimes (nth j y kzero) acc | OutScc _ => acc end)
      kone cs.

  (* THE re-indexing equality: the source-ordered full product equals the
     out-of-SCC product times the in-SCC product. This is exactly what
     `solve_scc` relies on when it folds out-of-SCC children into
     `outside_product` and keeps `in_scc_children` separate. *)
  Lemma lowering_factor_faithful : forall y cs,
    full_product y cs = ktimes (out_product cs) (in_product y cs).
  Proof.
    intros y cs. induction cs as [| c cs' IH]; simpl.
    - rewrite ktimes_one_l. reflexivity.
    - destruct c as [j | w]; simpl.
      + (* InScc j: move the in-SCC factor past the out-of-SCC product. *)
        rewrite IH.
        rewrite <- ktimes_assoc.
        rewrite (ktimes_comm (nth j y kzero) (out_product cs')).
        rewrite ktimes_assoc. reflexivity.
      + (* OutScc w: the out-of-SCC factor reassociates into out_product. *)
        rewrite IH.
        rewrite ktimes_assoc. reflexivity.
  Qed.

  (* One e-node, lowered exactly as `solve_scc` builds its PackingFactored. *)
  Record InsideNode : Type := {
    n_target   : nat;            (* SCC-local index of the parent class *)
    n_weight   : K;              (* weigh(node) *)
    n_children : list ChildRef
  }.

  (* The e-graph inside recurrence's contribution of one node. *)
  Definition recurrence_node (y : list K) (nd : InsideNode) : K :=
    ktimes (n_weight nd) (full_product y (n_children nd)).

  (* solve_scc's PackingFactored.outside_product = weigh ⊗ Π out-of-SCC. *)
  Definition packing_outside (nd : InsideNode) : K :=
    ktimes (n_weight nd) (out_product (n_children nd)).

  (* solve_scc's reconstruction: outside_product ⊗ Π in-SCC children. *)
  Definition lowered_node (y : list K) (nd : InsideNode) : K :=
    ktimes (packing_outside nd) (in_product y (n_children nd)).

  Lemma lowered_node_faithful : forall y nd,
    lowered_node y nd = recurrence_node y nd.
  Proof.
    intros y nd. unfold lowered_node, packing_outside, recurrence_node.
    rewrite ktimes_assoc. rewrite <- lowering_factor_faithful. reflexivity.
  Qed.

  (* A per-class system value: ⊕ over the class's e-nodes of their contribution. *)
  Definition sys_at (node_val : list K -> InsideNode -> K)
                    (nodes : list InsideNode) (y : list K) (i : nat) : K :=
    fold_right
      (fun nd acc => if Nat.eqb (n_target nd) i
                     then kplus (node_val y nd) acc else acc)
      kzero nodes.

  Definition recurrence_sys (nodes : list InsideNode) (y : list K) (i : nat) : K :=
    sys_at recurrence_node nodes y i.
  Definition lowered_sys (nodes : list InsideNode) (y : list K) (i : nat) : K :=
    sys_at lowered_node nodes y i.

  (* The lowered system equals the e-graph inside recurrence, class by class. *)
  Theorem lowered_eq_recurrence : forall nodes y i,
    lowered_sys nodes y i = recurrence_sys nodes y i.
  Proof.
    intros nodes y i. unfold lowered_sys, recurrence_sys, sys_at.
    induction nodes as [| nd nds IH]; simpl.
    - reflexivity.
    - destruct (Nat.eqb (n_target nd) i).
      + rewrite lowered_node_faithful. rewrite IH. reflexivity.
      + rewrite IH. reflexivity.
  Qed.

  (* Hence solving the lowered system solves the recurrence: identical fixpoints,
     so no derivation/aggregate is lost by the re-indexing. *)
  Definition is_fixpoint (sys : list K -> nat -> K) (y : list K) : Prop :=
    forall i, nth i y kzero = sys y i.

  Theorem lowering_preserves_fixpoints : forall nodes y,
    is_fixpoint (lowered_sys nodes) y <-> is_fixpoint (recurrence_sys nodes) y.
  Proof.
    intros nodes y. unfold is_fixpoint. split; intros H i.
    - rewrite <- lowered_eq_recurrence. apply H.
    - rewrite lowered_eq_recurrence. apply H.
  Qed.

  (* ════════════════════════════════════════════════════════════════════════
   * (C) TRIVIAL SCCs are a NO-OP.
   *
   * A class whose every child is out-of-SCC (a singleton SCC with no self-loop)
   * has `in_product = 1̄` independent of the unknowns, so its lowered system is
   * CONSTANT in `y` — equal to the acyclic value `compute_inside_acyclic`
   * already holds. `compute_inside_closed`'s `continue` (skip `solve_scc`) is
   * therefore sound.
   * ════════════════════════════════════════════════════════════════════════ *)

  Lemma in_product_const_if_no_inscc : forall y y' cs,
    (forall c, In c cs -> exists w, c = OutScc w) ->
    in_product y cs = in_product y' cs.
  Proof.
    intros y y' cs. induction cs as [| c cs' IH]; simpl; intros Hno.
    - reflexivity.
    - destruct c as [j | w].
      + exfalso.
        destruct (Hno (InScc j) (or_introl eq_refl)) as [w Hw]. discriminate.
      + apply IH. intros c Hc. apply Hno. right. exact Hc.
  Qed.

  Theorem trivial_scc_constant : forall nodes y y' i,
    (forall nd, In nd nodes ->
       forall c, In c (n_children nd) -> exists w, c = OutScc w) ->
    lowered_sys nodes y i = lowered_sys nodes y' i.
  Proof.
    intros nodes y y' i. unfold lowered_sys, sys_at.
    induction nodes as [| nd nds IH]; simpl; intros Hall.
    - reflexivity.
    - assert (Hnd : lowered_node y nd = lowered_node y' nd).
      { unfold lowered_node, packing_outside. f_equal.
        apply in_product_const_if_no_inscc.
        intros c Hc. apply (Hall nd (or_introl eq_refl) c Hc). }
      assert (Hrest : forall nd', In nd' nds ->
                 forall c, In c (n_children nd') -> exists w, c = OutScc w).
      { intros nd' Hnd' c Hc. exact (Hall nd' (or_intror Hnd') c Hc). }
      destruct (Nat.eqb (n_target nd) i).
      + rewrite Hnd, (IH Hrest). reflexivity.
      + rewrite (IH Hrest). reflexivity.
  Qed.

End Theory.

(* ════════════════════════════════════════════════════════════════════════════
 * (D) NON-VACUITY — the Boolean reachability commutative Kleene algebra.
 *
 * K = bool, ⊕ = ||, ⊗ = &&, 0̄ = false, 1̄ = true, a* = true (1 ⊕ a ⊕ … = true).
 * This is the "is the class derivable at all" instance; it satisfies every
 * structure law, so the theorems above are non-vacuously true on a real,
 * inhabited weight algebra.
 * ════════════════════════════════════════════════════════════════════════════ *)

Definition bool_cka : CommKleeneAlgebra bool :=
{|
  kzero  := false;
  kone   := true;
  kplus  := orb;
  ktimes := andb;
  kstar  := fun _ => true;
  kplus_comm   := ltac:(intros a b; destruct a, b; reflexivity);
  kplus_assoc  := ltac:(intros a b c; destruct a, b, c; reflexivity);
  kplus_zero_l := ltac:(intros a; destruct a; reflexivity);
  kplus_idem   := ltac:(intros a; destruct a; reflexivity);
  ktimes_comm  := ltac:(intros a b; destruct a, b; reflexivity);
  ktimes_assoc := ltac:(intros a b c; destruct a, b, c; reflexivity);
  ktimes_one_l := ltac:(intros a; destruct a; reflexivity);
  ktimes_zero_l := ltac:(intros a; destruct a; reflexivity);
  ktimes_plus_distr_l := ltac:(intros a b c; destruct a, b, c; reflexivity);
  kstar_unfold_l := ltac:(intros a; destruct a; reflexivity);
  kstar_ind_l := ltac:(intros a b x H; destruct a, b, x; simpl in *; congruence)
|}.

(* Force each headline theorem to typecheck at the concrete instance: the no-miss
   inside-weight closure properties are not vacuous. *)
Definition _nonvacuous_lfp        := @star_closure_is_lfp bool bool_cka.
Definition _nonvacuous_faithful   := @lowering_factor_faithful bool bool_cka.
Definition _nonvacuous_node       := @lowered_node_faithful bool bool_cka.
Definition _nonvacuous_system     := @lowered_eq_recurrence bool bool_cka.
Definition _nonvacuous_preserve   := @lowering_preserves_fixpoints bool bool_cka.
Definition _nonvacuous_trivial    := @trivial_scc_constant bool bool_cka.
