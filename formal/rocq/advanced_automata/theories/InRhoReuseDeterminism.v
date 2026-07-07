(*
 * InRhoReuseDeterminism: compile-once / reuse determinism for the Stage-1 M1 in-Rho
 * set-automaton serializer, obligation (x) of the in-Rho matching verification plan
 * (docs 16). The serialized network's accept verdict for a node is a pure function
 * of the node's RootKey (op, arity): compiling the automaton ONCE and reusing it
 * across e-graphs / redex sites gives each node exactly its own verdict — reuse
 * cannot cross-contaminate. Extends PositionalSetAutomatonSound's
 * `reuse_is_per_node_deterministic`.
 *
 * Abstraction boundary (plan 16, section 0): as with (i)/(ii) this reasons over the
 * abstract accept decision (`sa_accept` from InRhoMatchPositional), not the RSpace
 * reduction. Site-independence of the verdict is manifest here (sa_accept has no
 * site argument); the concrete channel relabeling under a fresh site nonce is
 * obligation (viii)'s freshness (Phase B), which (ii)'s injective `chan` seeds.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool PeanoNat List.
Import ListNotations.
From AdvancedAutomata Require Import PositionalSetAutomatonSound.
From AdvancedAutomata Require Import SymbolOnceInjective.
From AdvancedAutomata Require Import InRhoMatchPositional.

(* The M1 accept verdict factors through the node's RootKey (op, arity) alone. *)
Lemma sa_accept_factors_rootkey : forall op args n,
  all_leaves args = true ->
  sa_accept (PApp op args) n = Nat.eqb op (node_op n) && Nat.leb (length args) (node_arity n).
Proof.
  intros op args [nop nch] Hleaves. unfold sa_accept.
  rewrite (sa_chain_all_leaves args nch Hleaves). reflexivity.
Qed.

(* (x)-core: reuse across nodes with equal RootKey gives the SAME in-Rho verdict. *)
Theorem inrho_verdict_per_node_deterministic : forall p n1 n2,
  m1_pattern p = true ->
  node_op n1 = node_op n2 -> node_arity n1 = node_arity n2 ->
  sa_accept p n1 = sa_accept p n2.
Proof.
  intros p n1 n2 Hm Hop Har.
  destruct p as [| op args | op args]; try discriminate Hm. simpl in Hm.
  rewrite (sa_accept_factors_rootkey op args n1 Hm).
  rewrite (sa_accept_factors_rootkey op args n2 Hm).
  rewrite Hop, Har. reflexivity.
Qed.

(* (x)-dispatch: the host dispatched-set reuse, over the single compiled pattern. *)
Theorem inrho_reuse_dispatched_deterministic : forall p n1 n2,
  node_op n1 = node_op n2 -> node_arity n1 = node_arity n2 ->
  dispatched_at [p] n1 = dispatched_at [p] n2.
Proof.
  intros p n1 n2 Hop Har. apply reuse_is_per_node_deterministic; assumption.
Qed.

(* compile-once: the verdict is a pure function of (pattern, node) — no site state. *)
Theorem inrho_verdict_is_a_function : forall p n1 n2,
  n1 = n2 -> sa_accept p n1 = sa_accept p n2.
Proof.
  intros p n1 n2 H. subst n2. reflexivity.
Qed.

Print Assumptions sa_accept_factors_rootkey.
Print Assumptions inrho_verdict_per_node_deterministic.
Print Assumptions inrho_reuse_dispatched_deterministic.
Print Assumptions inrho_verdict_is_a_function.
