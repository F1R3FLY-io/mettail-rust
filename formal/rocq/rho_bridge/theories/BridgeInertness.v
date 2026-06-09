(*
 * BridgeInertness: the MeTTaIL <-> f1r3node-rust bridge is STRICTLY ONE-WAY.
 *
 * M-RHO compiles MeTTaIL GSLTs onto f1r3node-rust's Rho machine via three bridge
 * crates (mettail-rho-{codegen,runtime,adapter}) that depend ONE-WAY on
 * f1r3node-rust: MeTTaIL may depend on f1r3node-rust, f1r3node-rust NEVER on
 * MeTTaIL. f1r3node-rust enforces this OPERATIONALLY with the guard test
 * `mettail_rust_is_not_a_cargo_dependency`
 * (rholang/src/rust/interpreter/accounting/resource_logic.rs:293), which scans
 * every f1r3node-rust Cargo.toml and asserts none names mettail-rust.
 *
 * This file proves that the invariant the guard enforces is INTERNALLY
 * CONSISTENT: with the single permitted bridge edge (MeTTaIL -> f1r3node), the
 * dependency relation is irreversible (f1r3node never reaches MeTTaIL) and
 * ACYCLIC (no repo depends on something that reaches back to it). A dependency
 * cycle would make MeTTaIL a (transitive) dependency of f1r3node, contradicting
 * the one-way design and the guard; ruling cycles out is the formal content of
 * "the bridge is inert / one-way."
 *
 * (M-RHO.0.0 inert milestone: the bridge crates are empty + `engine`-gated; this
 * is the minimal non-vacuous invariant they must preserve — the bridge analogue
 * of the dovetail engine's NBestExtraction.v.)
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.

Import ListNotations.

Section BridgeInertness.

  (* The two repositories joined by the bridge. *)
  Inductive Repo : Type := MeTTaIL | F1r3node.

  (* Repo is discrete (the two repositories are distinguishable). *)
  Definition Repo_eq_dec (a b : Repo) : {a = b} + {a <> b}.
  Proof. decide equality. Defined.

  (* The ONLY permitted bridge dependency edge: MeTTaIL depends on f1r3node. *)
  Inductive dep : Repo -> Repo -> Prop :=
    | dep_bridge : dep MeTTaIL F1r3node.

  (* Reachability via dependency edges: the reflexive-transitive closure of dep. *)
  Inductive reaches : Repo -> Repo -> Prop :=
    | reaches_refl : forall r, reaches r r
    | reaches_step : forall a b c, dep a b -> reaches b c -> reaches a c.

  (* The allowed direction holds (MeTTaIL is permitted to depend on f1r3node). *)
  Theorem mettail_may_depend_on_f1r3node : dep MeTTaIL F1r3node.
  Proof. constructor. Qed.

  (* f1r3node NEVER depends on MeTTaIL — the exact invariant the guard test
     enforces, as a direct fact about the permitted edges. *)
  Theorem f1r3node_never_depends_on_mettail : ~ dep F1r3node MeTTaIL.
  Proof. intro H. inversion H. Qed.

  (* No repository depends on itself (the single edge connects distinct repos). *)
  Theorem no_self_dependency : forall r, ~ dep r r.
  Proof. intros r H. inversion H. Qed.

  (* Characterize reachability: from the single edge, the only reachable pairs are
     the diagonal (r,r) and the one bridge pair (MeTTaIL, f1r3node). *)
  Lemma reaches_cases : forall a b,
    reaches a b -> a = b \/ (a = MeTTaIL /\ b = F1r3node).
  Proof.
    intros a b H. induction H as [r | a b c Hdep Hr IH].
    - left. reflexivity.
    - inversion Hdep; subst.                 (* a = MeTTaIL, b = F1r3node *)
      destruct IH as [Heq | [H1 _]].
      + subst c. right. split; reflexivity.  (* F1r3node = c *)
      + discriminate H1.                      (* F1r3node = MeTTaIL is impossible *)
  Qed.

  (* f1r3node cannot even TRANSITIVELY reach MeTTaIL (no dependency chain back). *)
  Theorem f1r3node_does_not_reach_mettail : ~ reaches F1r3node MeTTaIL.
  Proof.
    intro H. apply reaches_cases in H. destruct H as [Heq | [H1 _]].
    - discriminate Heq.   (* F1r3node = MeTTaIL *)
    - discriminate H1.    (* F1r3node = MeTTaIL *)
  Qed.

  (* THE inertness invariant: the dependency graph is ACYCLIC — no repository
     depends on something that reaches back to it. (A cycle would make MeTTaIL a
     transitive dependency of f1r3node, which the one-way bridge forbids.) *)
  Theorem bridge_acyclic :
    forall r, ~ (exists s, dep r s /\ reaches s r).
  Proof.
    intros r [s [Hdep Hreach]].
    inversion Hdep; subst.                 (* r = MeTTaIL, s = F1r3node *)
    apply f1r3node_does_not_reach_mettail. (* Hreach : reaches F1r3node MeTTaIL *)
    exact Hreach.
  Qed.

End BridgeInertness.
