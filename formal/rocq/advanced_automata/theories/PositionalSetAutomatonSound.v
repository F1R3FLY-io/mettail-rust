(*
 * PositionalSetAutomatonSound: soundness of the positional set-automaton
 * root-index dispatch (pgmcp #1956 Epic 8 #2045/#2046), and the reuse property
 * (#2047) as a corollary.
 *
 * Rust image (`dovetail/src/set_automaton.rs`): `compile_structural` rejects any
 * pattern that `contains_ac` (an `AcApp` anywhere) into `SetAutomatonError.unsupported`
 * — AC patterns stay on the lazy e-graph path (`AcApp` is `unreachable!` after
 * rejection, :126/:184). The scan indexes structural patterns by
 * `RootKey { op, arity }` and matches `Var` patterns at every root, then checks the
 * full recursive positional match. The oracle test
 * `prop_set_automaton_matches_recursive_positional_oracle`
 * (`dovetail/tests/properties.rs`) is the executable witness of the equivalence.
 *
 * We model the root-index dispatch and the recursive matcher's ROOT contract, and
 * prove:
 *   - #2045 the (op, arity) index NEVER drops a positional match — a structural
 *     pattern that matches a node has an agreeing root op + arity, and is therefore
 *     dispatched by the index (so the index is a sound pre-filter; the automaton's
 *     match set equals the oracle's);
 *   - #2046 the compiler admits exactly the AC-free patterns (an AC-containing
 *     pattern is never compiled; a structural one always is);
 *   - #2047 the index verdict is a pure function of (pattern, node): the same
 *     compiled patterns applied to any node give the correct per-node result — so
 *     compiling once and reusing across e-graphs preserves results.
 *
 * The recursive children-match is left abstract (`children_match`): the root-index
 * theorems depend only on the root op/arity check the real matcher performs first,
 * so they hold for ANY children semantics (hence the universally-quantified,
 * assumption-free statements below).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
Import ListNotations.

Section PositionalSetAutomatonSound.

  (* Positional patterns: a variable (matches any node), a structural application
     (op + child patterns), or an associative-commutative application (rejected). *)
  Inductive Pat : Type :=
    | PVar
    | PApp (op : nat) (args : list Pat)
    | PAcApp (op : nat) (args : list Pat).

  (* Subject e-nodes: an op applied to child nodes. *)
  Inductive Node : Type := NApp (op : nat) (children : list Node).

  Definition node_op (n : Node) : nat := match n with NApp op _ => op end.
  Definition node_arity (n : Node) : nat := match n with NApp _ ch => length ch end.

  (* `contains_ac` (Rust `contains_ac`, set_automaton.rs:334): an `AcApp` anywhere. *)
  Fixpoint contains_ac (p : Pat) : bool :=
    match p with
    | PVar => false
    | PApp _ args =>
        (fix any (ps : list Pat) : bool :=
           match ps with
           | [] => false
           | p' :: ps' => contains_ac p' || any ps'
           end) args
    | PAcApp _ _ => true
    end.

  (* The recursive positional children-match is abstract; the root theorems do not
     depend on it. *)
  Variable children_match : list Pat -> list Node -> bool.

  (* The recursive positional matcher's ROOT contract: `Var` matches any node; a
     structural `App op args` matches `NApp nop nch` only when op AND arity agree
     (then the children match); an AC application never matches positionally (it is
     handled by the lazy path). *)
  Definition pmatch (p : Pat) (n : Node) : bool :=
    match p, n with
    | PVar, _ => true
    | PApp op args, NApp nop nch =>
        Nat.eqb op nop && Nat.eqb (length args) (length nch) && children_match args nch
    | PAcApp _ _, _ => false
    end.

  (* The root-index dispatch: `Var` is dispatched at every root; a structural
     pattern is dispatched only where its (op, arity) key matches the node; an AC
     pattern is not compiled, so never dispatched by the positional automaton. *)
  Definition dispatched (p : Pat) (n : Node) : bool :=
    match p with
    | PVar => true
    | PApp op args => Nat.eqb (node_op n) op && Nat.eqb (node_arity n) (length args)
    | PAcApp _ _ => false
    end.

  (* The compiler admits a pattern iff it is AC-free. *)
  Definition compilable (p : Pat) : bool := negb (contains_ac p).

  (* ---- #2045: the (op, arity) index is a sound pre-filter ---- *)

  (* A structural match forces root op + arity agreement. *)
  Theorem app_match_requires_root_agreement : forall op args n,
    pmatch (PApp op args) n = true ->
    node_op n = op /\ node_arity n = length args.
  Proof.
    intros op args [nop nch] H. unfold pmatch in H.
    apply andb_true_iff in H. destruct H as [H _].
    apply andb_true_iff in H. destruct H as [Hop Har].
    apply Nat.eqb_eq in Hop. apply Nat.eqb_eq in Har.
    unfold node_op, node_arity. split; [symmetry; exact Hop | symmetry; exact Har].
  Qed.

  (* MAIN: the index never drops a match — every positional match of a compilable
     pattern is dispatched by the root index. *)
  Theorem index_never_drops_match : forall p n,
    compilable p = true -> pmatch p n = true -> dispatched p n = true.
  Proof.
    intros p n _ Hm. destruct p as [| op args | op args].
    - reflexivity.
    - apply app_match_requires_root_agreement in Hm. destruct Hm as [Hop Har].
      unfold dispatched. rewrite Hop, Har.
      rewrite Nat.eqb_refl, Nat.eqb_refl. reflexivity.
    - unfold pmatch in Hm. destruct n. discriminate Hm.
  Qed.

  (* Conversely the index admits no spurious node without an agreeing key: a
     dispatched structural pattern has the node's op + arity. (The automaton then
     runs the full `pmatch`, so the index adds no false positives.) *)
  Theorem dispatched_app_agrees_on_root : forall op args n,
    dispatched (PApp op args) n = true ->
    node_op n = op /\ node_arity n = length args.
  Proof.
    intros op args n H. unfold dispatched in H.
    apply andb_true_iff in H. destruct H as [Hop Har].
    apply Nat.eqb_eq in Hop. apply Nat.eqb_eq in Har.
    split; assumption.
  Qed.

  (* ---- #2046: the compiler admits exactly the AC-free patterns ---- *)

  Theorem ac_pattern_not_compilable : forall p,
    contains_ac p = true -> compilable p = false.
  Proof.
    intros p H. unfold compilable. rewrite H. reflexivity.
  Qed.

  Theorem structural_pattern_compilable : forall p,
    contains_ac p = false -> compilable p = true.
  Proof.
    intros p H. unfold compilable. rewrite H. reflexivity.
  Qed.

  (* A bare AC application at the root is never compiled and never dispatched. *)
  Theorem ac_root_not_dispatched : forall op args n,
    dispatched (PAcApp op args) n = false.
  Proof. intros. reflexivity. Qed.

  (* ---- #2047: reuse — the index verdict is a pure function of (pattern, node) ---- *)

  (* The set of dispatched patterns at a node is `filter (fun p => dispatched p n)`,
     a function of the compiled pattern list and the node ALONE. Hence compiling a
     pattern set once and applying it to any two nodes (in the same or different
     e-graphs) yields, at each node, exactly that node's result — reuse cannot
     change or cross-contaminate the per-node match set. *)
  Definition dispatched_at (patterns : list Pat) (n : Node) : list Pat :=
    filter (fun p => dispatched p n) patterns.

  Theorem reuse_is_per_node_deterministic : forall patterns n1 n2,
    node_op n1 = node_op n2 -> node_arity n1 = node_arity n2 ->
    dispatched_at patterns n1 = dispatched_at patterns n2.
  Proof.
    intros patterns n1 n2 Hop Har. unfold dispatched_at.
    apply filter_ext. intro p. destruct p as [| op args | op args].
    - reflexivity.
    - unfold dispatched. rewrite Hop, Har. reflexivity.
    - reflexivity.
  Qed.

End PositionalSetAutomatonSound.

Print Assumptions app_match_requires_root_agreement.
Print Assumptions index_never_drops_match.
Print Assumptions ac_pattern_not_compilable.
Print Assumptions reuse_is_per_node_deterministic.
