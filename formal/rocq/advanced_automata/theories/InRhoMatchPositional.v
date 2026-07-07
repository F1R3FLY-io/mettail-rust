(*
 * InRhoMatchPositional: the Stage-1 M1 in-Rho `sa:`-chain acceptance equals the
 * recursive positional matching relation (sound + complete), obligation (i) of the
 * in-Rho matching verification plan (docs 16). Paper: P1 Thm 6.12 = P2 Thm 2.
 *
 * The in-Rho automaton (`rholang-codegen/src/rho_net_automaton.rs`) matches a
 * spread subject by a LINEAR chain of `for`-receives: the root `Match` dispatches
 * on the head op, then one nested for-receive per argument binds one child, and the
 * innermost accept fires. We model that chain (`sa_accept` / `sa_chain_children`)
 * and prove it equals the recursive positional oracle.
 *
 * M1 all-leaf specialization: because M1 serializes only App roots over nullary Var
 * leaves (the `NonNullaryVarSubtree` guard), every argument is a `PVar`, and a Var
 * leaf matches ANY subterm. Hence the recursive positional matcher's children-match
 * is trivially satisfied and the oracle reduces to op + arity agreement — modeled by
 * the host `pmatch` (PositionalSetAutomatonSound) instantiated at the trivial
 * children-match `children_trivial`. The full recursive children-match arrives with
 * M2 (nested patterns), reinstantiating `children_match` at the general recursion.
 *
 * Abstraction boundary (plan 16, section 0): the operational faithfulness of the
 * emitted `Par` to this fold is witnessed by the runtime tests
 * (`rho_net_equivalence.rs` `m1_matches_swap_in_rho_and_fires_the_rewrite`,
 * `m1_does_not_match_a_non_matching_head_in_rho`, and the property-based oracle
 * `in_rho_match_binds_the_positional_sigma_for_random_linear_patterns`); this file
 * proves the SERIALIZATION LOGIC (the accept decision) correct, not the RSpace
 * reduction.
 *
 * HONEST PREMISE (`arity_consistent`): the serializer checks the head OP via
 * `Match` on `reflect_tag(fp, op)` (op-only) and realizes ARITY structurally, by
 * the count of emitted for-receives. In the abstract `Node` model (arbitrary arity
 * per op) an over-arity subject would fire all k receives and accept while the
 * oracle rejects (arity conjunct) — a genuine false-positive the model must
 * expose. It is closed by the typedness fact "op determines arity", which the
 * runtime term algebra guarantees; hence an explicit, discharged premise (no Axiom,
 * no free Section variable).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool PeanoNat List.
Import ListNotations.
From AdvancedAutomata Require Import PositionalSetAutomatonSound.
From AdvancedAutomata Require Import SymbolOnceInjective.

(* The recursive positional oracle, specialized to M1's all-leaf scope: each Var
   leaf matches any subterm, so children-match is trivially satisfied and the oracle
   is the host pmatch's own root (op + arity) check. *)
Definition children_trivial (args : list Pat) (nch : list Node) : bool := true.
Definition pmatch_M1 (p : Pat) (n : Node) : bool := pmatch children_trivial p n.

(* The in-Rho `sa:`-chain accept (mirrors automaton_receiver_network_par): args
   exhausted => accept fires (extra children never received — the over-arity gap the
   arity premise closes); a receive with no published child never rendezvous. *)
Fixpoint sa_chain_children (args : list Pat) (nch : list Node) {struct args} : bool :=
  match args, nch with
  | [], _        => true
  | _ :: _, []   => false
  | a :: args', _ :: nch' => is_leaf a && sa_chain_children args' nch'
  end.
Definition sa_accept (p : Pat) (n : Node) : bool :=
  match p, n with
  | PApp op args, NApp nop nch => Nat.eqb op nop && sa_chain_children args nch
  | _, _ => false
  end.

(* The typedness premise: op determines arity (guaranteed by the term algebra). *)
Definition arity_consistent (p : Pat) (n : Node) : Prop :=
  match p with
  | PApp op args => node_op n = op -> node_arity n = length args
  | _ => True
  end.

(* ---- support lemmas ---- *)

(* On all-leaf args the sa:-chain reduces to "pattern arity <= subject arity". *)
Lemma sa_chain_all_leaves : forall args nch,
  all_leaves args = true -> sa_chain_children args nch = Nat.leb (length args) (length nch).
Proof.
  induction args as [| a args' IH]; intros nch H.
  - reflexivity.
  - simpl in H. apply andb_true_iff in H. destruct H as [Ha Hargs].
    destruct a; simpl in Ha; try discriminate Ha.
    destruct nch as [| c nch']; simpl.
    + reflexivity.
    + rewrite (IH nch' Hargs). reflexivity.
Qed.

(* pmatch_M1 on an App reduces to op + arity agreement. *)
Lemma pmatch_M1_app : forall op args nop nch,
  pmatch_M1 (PApp op args) (NApp nop nch) = Nat.eqb op nop && Nat.eqb (length args) (length nch).
Proof.
  intros op args nop nch. unfold pmatch_M1, pmatch, children_trivial.
  rewrite Bool.andb_true_r. reflexivity.
Qed.

(* An M1 pattern is AC-free, hence compilable (reuses contains_ac from the host). *)
Lemma m1_compilable : forall p, m1_pattern p = true -> compilable p = true.
Proof.
  intros p Hp. destruct p as [| op args | op args]; try discriminate Hp.
  simpl in Hp. unfold compilable.
  assert (Hac : contains_ac (PApp op args) = false).
  { simpl. induction args as [| a args' IH]; simpl.
    - reflexivity.
    - apply andb_true_iff in Hp. destruct Hp as [Ha Hargs].
      destruct a; simpl in Ha; try discriminate Ha.
      simpl. apply IH. exact Hargs. }
  rewrite Hac. reflexivity.
Qed.

(* ---- SOUNDNESS: a chain accept on a well-typed subject is a positional match ---- *)
Theorem sa_accept_sound : forall p n,
  m1_pattern p = true -> arity_consistent p n ->
  sa_accept p n = true -> pmatch_M1 p n = true.
Proof.
  intros p n Hm Har Hacc.
  destruct p as [| op args | op args]; try discriminate Hm.
  destruct n as [nop nch]. simpl in Hm.
  unfold sa_accept in Hacc. apply andb_true_iff in Hacc. destruct Hacc as [Hop Hchain].
  apply Nat.eqb_eq in Hop. subst nop.
  rewrite (sa_chain_all_leaves args nch Hm) in Hchain. apply Nat.leb_le in Hchain.
  unfold arity_consistent in Har. simpl in Har. specialize (Har eq_refl).
  (* Har : length nch = length args *)
  rewrite pmatch_M1_app.
  assert (Hlen : length args = length nch) by (symmetry; exact Har).
  rewrite Hlen, !Nat.eqb_refl. reflexivity.
Qed.

(* ---- COMPLETENESS: every positional match is a chain accept (no side-condition) ---- *)
Theorem sa_accept_complete : forall p n,
  m1_pattern p = true -> pmatch_M1 p n = true -> sa_accept p n = true.
Proof.
  intros p n Hm Hpm.
  destruct p as [| op args | op args]; try discriminate Hm.
  destruct n as [nop nch]. simpl in Hm.
  rewrite pmatch_M1_app in Hpm. apply andb_true_iff in Hpm. destruct Hpm as [Hop Hlen].
  apply Nat.eqb_eq in Hlen.
  unfold sa_accept. rewrite Hop. simpl.
  rewrite (sa_chain_all_leaves args nch Hm), Hlen. apply Nat.leb_refl.
Qed.

(* ---- the relation equality = obligation (i) ---- *)
Corollary sa_matches_positional : forall p n,
  m1_pattern p = true -> arity_consistent p n -> sa_accept p n = pmatch_M1 p n.
Proof.
  intros p n Hm Har. apply Bool.eq_true_iff_eq. split; intro H.
  - apply sa_accept_sound; assumption.
  - apply sa_accept_complete; assumption.
Qed.

(* ---- reuse: every in-Rho match is dispatched by the host (op, arity) index ---- *)
Corollary inrho_match_dispatched : forall p n,
  m1_pattern p = true -> arity_consistent p n -> sa_accept p n = true -> dispatched p n = true.
Proof.
  intros p n Hm Har Hacc.
  apply (index_never_drops_match children_trivial p n).
  - apply m1_compilable. exact Hm.
  - apply sa_accept_sound; assumption.
Qed.

(* ---- reuse: a dispatched in-Rho match agrees on the root op + arity ---- *)
Corollary inrho_no_false_root : forall op args n,
  m1_pattern (PApp op args) = true -> arity_consistent (PApp op args) n ->
  sa_accept (PApp op args) n = true ->
  node_op n = op /\ node_arity n = length args.
Proof.
  intros op args n Hm Har Hacc.
  apply (app_match_requires_root_agreement children_trivial).
  apply sa_accept_sound; assumption.
Qed.

Print Assumptions sa_accept_sound.
Print Assumptions sa_accept_complete.
Print Assumptions sa_matches_positional.
Print Assumptions inrho_match_dispatched.
Print Assumptions inrho_no_false_root.
