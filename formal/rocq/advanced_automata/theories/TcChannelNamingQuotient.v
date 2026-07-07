(*
 * TcChannelNamingQuotient: obligation (viii) of the in-Rho matching verification
 * plan (docs 16). The channel-naming map `tc(K) = ⌜T_M(K)⌝` (the interned StateId
 * trace) is the injective + coarsest-sound (O3) quotient, keyed by the outermost-
 * preserving relation `R_op` (same outermost rule), NOT the coarser `R_dep`. This
 * is what re-keying `pattern_trace_channel` to `sa:⌜root_state⌝` realizes (Stage 1
 * M2), and the load-bearing input to the `rem:nonopt` discharge (iii): distinct
 * `R_op` contexts get distinct channels (no cross-talk), R_op-equal contexts share.
 *
 * M1 depth-1 scope: because M1 serializes App roots over nullary Var leaves, a
 * context `K` is `PApp op [PVar…]` and its trace is the RootKey `(op, arity)` (the
 * name-erased canonical form — every Var leaf is a hole). We prove `tc` is the
 * O1∧O3 quotient at this scope, and bracket it: `@hd(K)` (head only) is too coarse
 * (O1-not-O3, `hd_violates_O3`), while `@K` (verbatim) COINCIDES with the quotient
 * here (`atK_equals_quotient_at_depth1`). The O3-not-O1 OVER-refinement of `@K` and
 * the `R_dep`-vs-`R_op` distinction are genuinely depth->=2 phenomena (they need a
 * non-inspected subterm / prefix-comparable positions), arriving with M2's nested-
 * pattern (collapse) slice; at depth-1 `@K` is already the quotient, which this
 * file records honestly rather than manufacturing a false depth-1 counterexample.
 *
 * Model boundary (plan 16 section 0): channels are modeled structurally (the trace
 * as (op, arity)); the concrete string naming + site freshness are obligation
 * (viii)'s `RhoGroundingAndNames` companion. Reuses Phase A `Pat`/`m1_pattern`.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool PeanoNat List.
Import ListNotations.
From AdvancedAutomata Require Import PositionalSetAutomatonSound.
From AdvancedAutomata Require Import SymbolOnceInjective.

(* The interned StateId trace, at M1's depth-1 all-leaf scope, is the RootKey
   (op, arity) — the name-erased canonical form (every Var leaf ↦ hole). *)
Definition trace (p : Pat) : option (nat * nat) :=
  match p with PApp op args => Some (op, length args) | _ => None end.

(* R_op: two M1 contexts fire the same outermost rule iff same op + same arity
   (leaves are holes, identified). *)
Definition op_equiv (p q : Pat) : bool :=
  match p, q with
  | PApp op args, PApp op' args' => Nat.eqb op op' && Nat.eqb (length args) (length args')
  | _, _ => false
  end.

(* The two rejected extremes: @K reflects the context verbatim; @hd(K) only the head. *)
Definition tc_atK (p : Pat) : Pat := p.
Definition tc_hd (p : Pat) : option nat :=
  match p with PApp op _ => Some op | _ => None end.

(* An M1 arg list is exactly a run of holes of its length. *)
Lemma all_leaves_repeat : forall args,
  all_leaves args = true -> args = repeat PVar (length args).
Proof.
  induction args as [| a args' IH]; simpl; intro H.
  - reflexivity.
  - apply andb_true_iff in H. destruct H as [Ha Hargs].
    destruct a; simpl in Ha; try discriminate Ha.
    f_equal. apply IH. exact Hargs.
Qed.

(* ---- O3 soundness: same channel ⇒ R_op-equivalent (no unsound collapse) ---- *)
Theorem tc_sound : forall K K',
  m1_pattern K = true -> m1_pattern K' = true ->
  trace K = trace K' -> op_equiv K K' = true.
Proof.
  intros K K' HK HK' Htr.
  destruct K as [| op args | op args]; try discriminate HK.
  destruct K' as [| op' args' | op' args']; try discriminate HK'.
  simpl in Htr. injection Htr as Hop Har.
  unfold op_equiv. rewrite Hop, Har, !Nat.eqb_refl. reflexivity.
Qed.

(* ---- O1 direction: R_op-equivalent ⇒ same channel (no over-refinement) ---- *)
Theorem tc_injective : forall K K',
  m1_pattern K = true -> m1_pattern K' = true ->
  op_equiv K K' = true -> trace K = trace K'.
Proof.
  intros K K' HK HK' Hoe.
  destruct K as [| op args | op args]; try discriminate HK.
  destruct K' as [| op' args' | op' args']; try discriminate HK'.
  unfold op_equiv in Hoe. apply andb_true_iff in Hoe. destruct Hoe as [Hop Har].
  apply Nat.eqb_eq in Hop. apply Nat.eqb_eq in Har.
  simpl. rewrite Hop, Har. reflexivity.
Qed.

(* ---- the interned trace IS the R_op quotient (both directions) ---- *)
Corollary tc_is_the_op_quotient : forall K K',
  m1_pattern K = true -> m1_pattern K' = true ->
  (trace K = trace K' <-> op_equiv K K' = true).
Proof.
  intros K K' HK HK'. split.
  - apply tc_sound; assumption.
  - apply tc_injective; assumption.
Qed.

(* ---- @hd(K) = O1-not-O3: same channel yet DIFFERENT outermost rule ---- *)
Theorem hd_violates_O3 : exists K K',
  m1_pattern K = true /\ m1_pattern K' = true /\
  tc_hd K = tc_hd K' /\ op_equiv K K' = false.
Proof.
  exists (PApp 0 [PVar]), (PApp 0 [PVar; PVar]).
  repeat split; reflexivity.
Qed.

(* ---- @K coincides with the quotient at depth-1 (no over-refinement here) ---- *)
Theorem atK_equals_quotient_at_depth1 : forall K K',
  m1_pattern K = true -> m1_pattern K' = true ->
  op_equiv K K' = true -> tc_atK K = tc_atK K'.
Proof.
  intros K K' HK HK' Hoe.
  destruct K as [| op args | op args]; try discriminate HK.
  destruct K' as [| op' args' | op' args']; try discriminate HK'.
  simpl in HK. simpl in HK'.
  unfold op_equiv in Hoe. apply andb_true_iff in Hoe. destruct Hoe as [Hop Har].
  apply Nat.eqb_eq in Hop. apply Nat.eqb_eq in Har.
  unfold tc_atK.
  rewrite (all_leaves_repeat args HK). rewrite (all_leaves_repeat args' HK').
  rewrite Hop, Har. reflexivity.
Qed.

Print Assumptions tc_sound.
Print Assumptions tc_injective.
Print Assumptions tc_is_the_op_quotient.
Print Assumptions hd_violates_O3.
Print Assumptions atK_equals_quotient_at_depth1.
