(*
 * BCG05_GuardKey: source-aware normalize-on-insert guard keys.
 *
 * BCG05 skips repeated normalize-on-insert work during one Ascent
 * fixpoint.  The optimization is sound only when the guard key refines
 * the emitted relation head: if two firings have the same key, they must
 * emit the same tuple.  This file isolates that obligation for:
 *
 *   1. equation-matching rewrite rules:
 *        rw_cat(s_orig, normalize(rhs(s))) <-- eq_cat(s_orig, s), ...
 *   2. category expansion:
 *        cat(normalize(c1)) <-- cat(c0), rw_cat(c0, c1)
 *   3. fused deconstruct+rewrite rules:
 *        rw_cat(sub, normalize(rhs(sub))) <-- ...
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition              | Rust Code                         | Location
 *   -----------------------------|-----------------------------------|-----------------------------------------
 *   rewrite_source_match_key     | BCG05 key in generate_rule_clause | macros/src/logic/rules.rs
 *   rewrite_match_only_key       | historical unsound key            | macros/src/logic/rules.rs
 *   category_expand_key          | BCG05 key in category expansion   | macros/src/logic/categories.rs
 *   fused_subterm_key            | BCG05 key in generate_fused_rule  | macros/src/logic/fusion.rs
 *   fused_parent_key             | historical unsound key            | macros/src/logic/fusion.rs
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

(* ===================================================================== *)
(*  Shared Head-Refinement Obligation                                      *)
(* ===================================================================== *)

Definition key_refines_head
    {A K H : Type}
    (key : A -> K)
    (head : A -> H) : Prop :=
  forall a b, key a = key b -> head a = head b.

(* ===================================================================== *)
(*  Equation-Matching Rewrite Rules                                        *)
(* ===================================================================== *)

Record rewrite_firing : Type := mkRewriteFiring {
  rewrite_source : nat;
  rewrite_match : nat
}.

Definition rewrite_rhs (f : rewrite_firing) : nat :=
  rewrite_match f.

Definition normalize (t : nat) : nat := t.

Definition rewrite_head (f : rewrite_firing) : nat * nat :=
  (rewrite_source f, normalize (rewrite_rhs f)).

Definition rewrite_source_match_key (f : rewrite_firing) : nat * nat :=
  (rewrite_source f, rewrite_match f).

Definition rewrite_match_only_key (f : rewrite_firing) : nat :=
  rewrite_match f.

Theorem rewrite_source_match_key_refines_head :
  key_refines_head rewrite_source_match_key rewrite_head.
Proof.
  intros [s m] [s' m'] Hkey.
  inversion Hkey.
  reflexivity.
Qed.

Theorem rewrite_match_only_key_does_not_refine_head :
  ~ key_refines_head rewrite_match_only_key rewrite_head.
Proof.
  intro Hrefines.
  pose (a := mkRewriteFiring 0 7).
  pose (b := mkRewriteFiring 1 7).
  assert (Hkey : rewrite_match_only_key a = rewrite_match_only_key b).
  { reflexivity. }
  specialize (Hrefines a b Hkey).
  unfold a, b, rewrite_head, normalize, rewrite_rhs in Hrefines.
  inversion Hrefines.
Qed.

Theorem rewrite_source_match_key_preserves_distinct_sources :
  forall source_a source_b matched,
    source_a <> source_b ->
    rewrite_source_match_key (mkRewriteFiring source_a matched) <>
    rewrite_source_match_key (mkRewriteFiring source_b matched).
Proof.
  intros source_a source_b matched Hneq Heq.
  inversion Heq.
  apply Hneq.
  assumption.
Qed.

(* ===================================================================== *)
(*  Category Expansion                                                     *)
(* ===================================================================== *)

Record expand_firing : Type := mkExpandFiring {
  expand_rewrite_rhs : nat
}.

Definition expand_head (f : expand_firing) : nat :=
  normalize (expand_rewrite_rhs f).

Definition category_expand_key (f : expand_firing) : nat :=
  expand_rewrite_rhs f.

Theorem category_expand_key_refines_head :
  key_refines_head category_expand_key expand_head.
Proof.
  intros [rhs_a] [rhs_b] Hkey.
  simpl in Hkey.
  subst rhs_b.
  reflexivity.
Qed.

(* ===================================================================== *)
(*  Fused Deconstruct + Rewrite Rules                                      *)
(* ===================================================================== *)

Record fused_firing : Type := mkFusedFiring {
  fused_parent : nat;
  fused_field_index : nat;
  fused_subterm : nat
}.

Definition fused_rhs (f : fused_firing) : nat :=
  fused_subterm f.

Definition fused_head (f : fused_firing) : nat * nat :=
  (fused_subterm f, normalize (fused_rhs f)).

Definition fused_subterm_key (f : fused_firing) : nat :=
  fused_subterm f.

Definition fused_parent_key (f : fused_firing) : nat :=
  fused_parent f.

Theorem fused_subterm_key_refines_head :
  key_refines_head fused_subterm_key fused_head.
Proof.
  intros [parent_a idx_a sub_a] [parent_b idx_b sub_b] Hkey.
  simpl in Hkey.
  subst sub_b.
  reflexivity.
Qed.

Theorem fused_parent_key_does_not_refine_head :
  ~ key_refines_head fused_parent_key fused_head.
Proof.
  intro Hrefines.
  pose (a := mkFusedFiring 10 0 3).
  pose (b := mkFusedFiring 10 1 4).
  assert (Hkey : fused_parent_key a = fused_parent_key b).
  { reflexivity. }
  specialize (Hrefines a b Hkey).
  unfold a, b, fused_head, fused_rhs, normalize in Hrefines.
  inversion Hrefines.
Qed.

Theorem fused_subterm_key_preserves_distinct_subterms :
  forall parent index_a index_b sub_a sub_b,
    sub_a <> sub_b ->
    fused_subterm_key (mkFusedFiring parent index_a sub_a) <>
    fused_subterm_key (mkFusedFiring parent index_b sub_b).
Proof.
  intros parent index_a index_b sub_a sub_b Hneq Heq.
  simpl in Heq.
  apply Hneq.
  assumption.
Qed.

(* ===================================================================== *)
(*  Summary                                                               *)
(*                                                                       *)
(*  T1: rewrite_source_match_key_refines_head                             *)
(*      Source-aware rewrite keys are sufficient for safe BCG05 skipping. *)
(*                                                                       *)
(*  T2: rewrite_match_only_key_does_not_refine_head                       *)
(*      The historical match-only key can collapse distinct source tuples. *)
(*                                                                       *)
(*  T3: category_expand_key_refines_head                                  *)
(*      Category expansion emits only normalize(c1), so c1 is sufficient. *)
(*                                                                       *)
(*  T4: fused_subterm_key_refines_head                                    *)
(*      Fused rules must key by the emitted rewrite source subterm.       *)
(*                                                                       *)
(*  T5: fused_parent_key_does_not_refine_head                             *)
(*      Parent-only fused keys can collapse distinct matching fields.     *)
(*                                                                       *)
(*  All proofs are COMPLETE -- zero Admitted.                             *)
(* ===================================================================== *)
