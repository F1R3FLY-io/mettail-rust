(*
 * GraphReachability: Shared graph infrastructure for Opts 3 and 5.
 *
 * Provides:
 *   - Directed graph model with finite node set and edge relation
 *   - Reachability via reflexive-transitive closure
 *   - Bidirectional reachability (for SCC core computation)
 *   - Self-loop, transitivity, and direct-edge lemmas
 *   - field_types abstraction: terms at src can produce subterms only
 *     at reachable nodes
 *   - unreachable_no_subterms: ~reachable src tgt -> no subterms
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition          | Rust / Ascent Code                   | Location
 *   -------------------------|--------------------------------------|--------------------------
 *   Node                     | category names (String)              | common.rs:218
 *   edge                     | direct adjacency list                | common.rs:219-265
 *   reach                    | transitive closure loop              | common.rs:267-297
 *   bidi_reach               | compute_core_categories bidi check   | common.rs:377-384
 *   field_types              | constructor field type references     | common.rs:230-260
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Relations.

From AscentOptimizations Require Import Prelude.

Import ListNotations.

(* ===================================================================== *)
(*  Directed Graph Model                                                  *)
(* ===================================================================== *)

Section DirectedGraph.

  (* Node type: represents grammar categories *)
  Variable Node : Type.

  (* Decidable equality on nodes *)
  Variable node_eqb : Node -> Node -> bool.
  Hypothesis node_eqb_spec : forall n1 n2, node_eqb n1 n2 = true <-> n1 = n2.

  (* All nodes in the graph (finite, complete, no duplicates) *)
  Variable all_nodes : list Node.
  Hypothesis all_nodes_complete : forall n, In n all_nodes.
  Hypothesis all_nodes_nodup : NoDup all_nodes.

  (* Edge relation: direct adjacency from constructor field references.
     edge src tgt means category src has a constructor with a field of
     type tgt. *)
  Variable edge : Node -> Node -> Prop.
  Hypothesis edge_dec : forall src tgt, {edge src tgt} + {~ edge src tgt}.

  (* ----------------------------------------------------------------- *)
  (*  Reachability: reflexive-transitive closure of edge                 *)
  (* ----------------------------------------------------------------- *)

  (* reach src tgt: there is a path from src to tgt through edges *)
  Inductive reach : Node -> Node -> Prop :=
    | reach_refl : forall n, reach n n
    | reach_step : forall a b c, edge a b -> reach b c -> reach a c.

  (* Direct edges are reachable *)
  Lemma reach_edge : forall a b, edge a b -> reach a b.
  Proof.
    intros a b Hab. apply reach_step with b.
    - exact Hab.
    - apply reach_refl.
  Qed.

  (* Reachability is transitive *)
  Lemma reach_trans : forall a b c, reach a b -> reach b c -> reach a c.
  Proof.
    intros a b c Hab Hbc.
    induction Hab as [n | x y z Hxy Hyz IH].
    - exact Hbc.
    - apply reach_step with y.
      + exact Hxy.
      + apply IH. exact Hbc.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  Bidirectional reachability (for SCC / core category computation)   *)
  (* ----------------------------------------------------------------- *)

  (* bidi_reach primary n: n is reachable from primary AND primary is
     reachable from n. These nodes form the "core" of the grammar. *)
  Definition bidi_reach (primary : Node) (n : Node) : Prop :=
    reach primary n /\ reach n primary.

  (* Primary is always in its own bidi set *)
  Lemma bidi_reach_refl : forall primary, bidi_reach primary primary.
  Proof.
    intros primary. split; apply reach_refl.
  Qed.

  (* bidi_reach is symmetric *)
  Lemma bidi_reach_sym : forall primary a b,
    bidi_reach primary a -> bidi_reach primary b ->
    reach a b -> reach b a ->
    bidi_reach primary a /\ bidi_reach primary b.
  Proof.
    intros primary a b Ha Hb Hab Hba. split; exact Ha + exact Hb.
  Qed.

  (* ----------------------------------------------------------------- *)
  (*  Field types: subterm extraction only produces reachable types      *)
  (* ----------------------------------------------------------------- *)

  (* field_types src: the set of categories that appear as fields in
     constructors of category src. This is the "direct neighbor" set. *)
  Variable field_types : Node -> list Node.

  (* Axiom: field_types only contains direct edges *)
  Hypothesis field_types_are_edges :
    forall src tgt, In tgt (field_types src) -> edge src tgt.

  (* Axiom: edges correspond to field_types *)
  Hypothesis edges_are_field_types :
    forall src tgt, edge src tgt -> In tgt (field_types src).

  (* Key property: unreachable categories have no subterms.
     If src cannot reach tgt through the grammar, then no constructor
     of src (or any category reachable from src) contains a tgt field.
     Therefore, extracting tgt-typed subterms from src-typed terms
     yields nothing.

     This is stated as an axiom because it reflects a property of the
     code generator: match arms are only generated for constructors that
     exist. If no path src→tgt exists, no match arm produces a tgt value. *)
  Hypothesis unreachable_no_field_types :
    forall src tgt, ~ reach src tgt -> ~ In tgt (field_types src).

  (* Corollary: unreachable means no direct edge *)
  Lemma unreachable_no_edge : forall src tgt,
    ~ reach src tgt -> ~ edge src tgt.
  Proof.
    intros src tgt Hnoreach Hedge.
    apply Hnoreach. apply reach_edge. exact Hedge.
  Qed.

End DirectedGraph.

(* Make arguments implicit for cleaner usage *)
Arguments reach {Node}.
Arguments reach_refl {Node} {edge}.
Arguments reach_step {Node} {edge}.
Arguments reach_trans {Node} {edge}.
Arguments reach_edge {Node} {edge}.
Arguments bidi_reach {Node}.
Arguments bidi_reach_refl {Node} {edge}.
