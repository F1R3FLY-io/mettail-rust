(*
 * InRhoCreeperTrace: the SOUNDNESS obligation for E-2 MECHANISM D — the
 * hereditary-GROUND subst/shift short-circuit at the SHARED de-Bruijn subst-cascade
 * entry (`rholang-codegen/src/rho_net_subst_trs.rs`, the `^subst`/`^shift` receiver
 * head guard).
 *
 * ---------------------------------------------------------------------------------
 * WHAT MECHANISM D IS (and why THIS is its soundness kernel)
 * ---------------------------------------------------------------------------------
 *
 * The production β cascade reflects every object node with a HEREDITARY-GROUND marker
 * (a distinguished token in the reflected `EList`, computed host-side = `oground`
 * below). At the `^subst(j,a,t,ret)` / `^shift(c,t,ret)` receiver ENTRY a guard fires
 * when the subject `t` is hereditarily ground: it `ret!(t)` IMMEDIATELY, skipping the
 * dispatch + the C2 object-congruence reassembly joins for the whole closed subtree.
 *
 * This is sound because de-Bruijn substitution (and shift) is the IDENTITY on a term
 * with NO free bound-index leaf (`oBound`) anywhere — a HEREDITARILY-GROUND term. The
 * condition is DEPTH-INDEPENDENT: because a ground term contains no `oBound` at all, it
 * is fixed by `osubst j a` under ANY depth `j` and by `oshift c` under ANY cutoff `c`,
 * so the guard needs NO numeric `^cmp` test (unlike the depth-sensitive "closed at
 * index j" carve-out) — a single marker read decides it. This is STRICTLY STRONGER than
 * (hence subsumed by) BoundVar(j)-freedom, so it is the cheapest sound guard.
 *
 * The three theorems below are the guard's soundness kernel:
 *   `oground_subst_id`  — the `^subst`-entry guard: `oground t` ⟹ `osubst j a t = t`.
 *   `oground_shift_id`  — the `^shift`-entry guard: `oground t` ⟹ `oshift c t = t`.
 *   `oground_shiftk_id` — completeness: the iterated `^shiftk` is identity on ground
 *                         (the `^shift` guard's transitive coverage of the `^shiftk`
 *                         cascade), so a ground argument is never needlessly re-shifted.
 *
 * Production β NF RESULTS are therefore BYTE-IDENTICAL under the guard: it replaces a
 * chain of identity subst/shift steps with a single `ret!(t)`, moving only the
 * reflected-intermediate bytes, never the resting NF.
 *
 * ---------------------------------------------------------------------------------
 * STYLE / FV DISCIPLINE (mirrors InRhoScionGraft.v)
 * ---------------------------------------------------------------------------------
 *
 * ADDITIVE over `DeBruijnSubstTRS.v`'s `Obj` fragment (`oBound`/`oFree`/`oLam`/`oNode`,
 * DeBruijnSubstTRS.v:92-96) and its `osubst`/`oshift`/`oshiftk` spec fixpoints
 * (DeBruijnSubstTRS.v:122-152). It touches NOTHING in DeBruijnSubstTRS.v,
 * InRhoQuiescenceDriver.v, or InRhoScionGraft.v — it MIRRORS the decidable-`bool`
 * `Fixpoint` + `Obj_ind'` nested-induction style (DeBruijnSubstTRS.v:100-116). Fully
 * constructive / finite / decidable ⟹ zero-admission: the closing `Print Assumptions`
 * gate reports "Closed under the global context" for every theorem (no Admitted, no
 * Axiom, no Parameter, no Hypothesis).
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List PeanoNat Bool.
From RhoBridge Require Import DeBruijnSubstTRS.

Import ListNotations.

(* =================================================================================
   1.  `oground` — the decidable HEREDITARY-GROUND predicate on reflected `Obj` terms.

   A term is hereditarily ground iff it contains NO `oBound` leaf ANYWHERE (whether
   free at the root or bound under an `oLam`): every `oBound` is a substitutable
   de-Bruijn reference, so its ABSENCE is exactly "subst/shift is the identity".

     oBound _   ⟹ false   -- a bound index: the ONE substitutable/shiftable leaf.
     oFree  _   ⟹ true    -- a free object variable: inert under subst AND shift.
     oLam   b   ⟹ oground b            -- descend the binder body (the index is implicit;
                                          groundness is a property of the whole subtree,
                                          NOT of the binder-relative free set — the
                                          `oLam (oBound 0)` term is NOT ground here).
     oNode _ ts ⟹ forallb oground ts  -- a constructor node: all children ground.

   This is EXACTLY the host-side marker `reflect_ground_term_par` / the spread collapse
   fold compute (bound⟹NONGROUND, free⟹GROUND, else⟹all-children-GROUND); the guard
   fires on GROUND. `forallb oground ts` recurses `oground` under the list combinator —
   the SAME nested-recursion shape `osubst`'s `map (osubst j a) ts`
   (DeBruijnSubstTRS.v:151) uses, accepted by the guardedness checker identically.
   ================================================================================= *)

Fixpoint oground (t : Obj) : bool :=
  match t with
  | oBound _ => false
  | oFree _ => true
  | oLam b => oground b
  | oNode _ ts => forallb oground ts
  end.

(* =================================================================================
   2.  `oground_subst_id` — THE `^subst`-entry guard soundness.

   `oground t = true` ⟹ for ANY depth `j` and ANY replacement `a`, `osubst j a t = t`.
   The proof is `Obj_ind'` (DeBruijnSubstTRS.v:100, the nested induction with a
   `Forall` hypothesis for `oNode` children); the `oBound` case is discharged by
   `discriminate` (a bound index is never ground), and the `oNode` case pushes the
   `Forall` IH + the `forallb` witness pointwise through `map (osubst j a)`.
   ================================================================================= *)

(* The pointwise map-identity lemma for the `oNode` child list, kept separate so the
   `Forall` (from `Obj_ind'`) and the `forallb` witness compose cleanly. Generic over
   the term operation `f` (instantiated at `osubst j a` and `oshift c` below). *)
Lemma map_id_of_ground :
  forall (f : Obj -> Obj) (ts : list Obj),
    Forall (fun t => oground t = true -> f t = t) ts ->
    forallb oground ts = true ->
    map f ts = ts.
Proof.
  intros f ts HF. induction HF as [| t ts' Ht _ IH]; intro Hg.
  - reflexivity.
  - simpl in Hg. apply andb_prop in Hg. destruct Hg as [Hgt Hgts'].
    simpl. rewrite (Ht Hgt). rewrite (IH Hgts'). reflexivity.
Qed.

Theorem oground_subst_id :
  forall t, oground t = true -> forall j a, osubst j a t = t.
Proof.
  intro t.
  induction t as [n | x | b IHb | op ts IHts] using Obj_ind'; intros Hg j a.
  - (* oBound n : oground = false, contradiction *)
    discriminate Hg.
  - (* oFree x : osubst j a (oFree x) = oFree x by definition *)
    reflexivity.
  - (* oLam b : osubst j a (oLam b) = oLam (osubst (S j) a b) *)
    simpl. simpl in Hg. f_equal. apply (IHb Hg).
  - (* oNode op ts : osubst j a (oNode op ts) = oNode op (map (osubst j a) ts) *)
    simpl. simpl in Hg. f_equal.
    apply (map_id_of_ground (osubst j a) ts).
    + revert IHts. apply Forall_impl. intros u Hu Hu'. apply (Hu Hu').
    + exact Hg.
Qed.

(* =================================================================================
   3.  `oground_shift_id` — THE `^shift`-entry guard soundness.

   `oground t = true` ⟹ for ANY cutoff `c`, `oshift c t = t`. Identical structure to
   §2 (the `oBound` leaf is the only place `oshift` moves; its absence is identity).
   ================================================================================= *)

Theorem oground_shift_id :
  forall t, oground t = true -> forall c, oshift c t = t.
Proof.
  intro t.
  induction t as [n | x | b IHb | op ts IHts] using Obj_ind'; intros Hg c.
  - (* oBound n : oground = false, contradiction *)
    discriminate Hg.
  - (* oFree x : oshift c (oFree x) = oFree x *)
    reflexivity.
  - (* oLam b : oshift c (oLam b) = oLam (oshift (S c) b) *)
    simpl. simpl in Hg. f_equal. apply (IHb Hg).
  - (* oNode op ts : oshift c (oNode op ts) = oNode op (map (oshift c) ts) *)
    simpl. simpl in Hg. f_equal.
    apply (map_id_of_ground (oshift c) ts).
    + revert IHts. apply Forall_impl. intros u Hu Hu'. apply (Hu Hu').
    + exact Hg.
Qed.

(* =================================================================================
   4.  `oground_shiftk_id` — the iterated `^shiftk` is identity on ground.

   COMPLETENESS: the `^shiftk(k,a,ret)` receiver is `k` successive `oshift 0` passes
   (DeBruijnSubstTRS.v:132-134); on a ground argument every pass is the identity
   (§3), so the whole `^shiftk` cascade is the identity — the `^shift`-entry guard's
   transitive coverage of `^shiftk`. (`^shiftk` needs NO separate guard: each of its
   `^shift 0` calls short-circuits via the `^shift` guard.)
   ================================================================================= *)

Theorem oground_shiftk_id :
  forall a, oground a = true -> forall k, oshiftk k a = a.
Proof.
  intros a Hg k. induction k as [| k' IHk].
  - reflexivity.
  - simpl. rewrite IHk. apply (oground_shift_id a Hg 0).
Qed.

(* =================================================================================
   5.  NON-VACUITY witnesses — the guard fires on GENUINE closed subtrees (not only
       the degenerate leaf) and correctly DECLINES a term with a bound index.

   These pin that `oground` is neither constantly-false (the guard would be dead) nor
   constantly-true (the guard would be unsound): a constant function `oLam (oFree 0)`
   is ground (guard FIRES — `osubst 0 a` is identity), while `oLam (oBound 0)` (the
   identity combinator body) is NOT ground (guard DECLINES — `osubst` is NOT identity
   there, it is exactly the substituted position).
   ================================================================================= *)

(* A closed constant `λ. free_0`: hereditarily ground, and subst at depth 0 is identity. *)
Example ground_constant_fires :
  oground (oLam (oFree 0)) = true
  /\ forall a, osubst 0 a (oLam (oFree 0)) = oLam (oFree 0).
Proof.
  split.
  - reflexivity.
  - intro a. apply oground_subst_id. reflexivity.
Qed.

(* The identity-combinator body `λ. bound_0`: NOT ground, and `osubst 0 a` is NOT the
   identity there (`osubst 1 a (oBound 0) = oBound 0`, but the OUTER `osubst 0` matches
   the shifted index — the guard MUST decline, and does). *)
Example bound_index_declines :
  oground (oLam (oBound 0)) = false.
Proof. reflexivity. Qed.

(* A non-trivial closed node `C(free_0, λ. C(free_1, free_2))`: ground through nested
   binders + arity-≥1 nodes, so the guard transports the WHOLE subtree in one `ret!`. *)
Example nested_ground_node_fires :
  oground (oNode 7 [oFree 0; oLam (oNode 7 [oFree 1; oFree 2])]) = true
  /\ forall j a, osubst j a (oNode 7 [oFree 0; oLam (oNode 7 [oFree 1; oFree 2])])
                 = oNode 7 [oFree 0; oLam (oNode 7 [oFree 1; oFree 2])].
Proof.
  split.
  - reflexivity.
  - intros j a. apply oground_subst_id. reflexivity.
Qed.

(* =================================================================================
   L(D).ZERO-ADMISSION GATE.  Every theorem (and the non-vacuity witnesses) must report
   "Closed under the global context": no Admitted, no Axiom, no Parameter, no
   Hypothesis, no Assumption. This file introduces NO Section variable, so nothing is
   discharged as a premise either — every result is unconditionally closed.
   ================================================================================= *)

Print Assumptions oground_subst_id.
Print Assumptions oground_shift_id.
Print Assumptions oground_shiftk_id.
Print Assumptions map_id_of_ground.
Print Assumptions ground_constant_fires.
Print Assumptions bound_index_declines.
Print Assumptions nested_ground_node_fires.
