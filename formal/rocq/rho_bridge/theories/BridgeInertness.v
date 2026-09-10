(*
 * BridgeInertness: core independence and upper application composition.
 *
 * M-RHO compiles MeTTaIL GSLTs onto f1r3node-rust's Rho machine via three bridge
 * crates that depend on the node CORE, never the upper node application.
 * The two-object section below describes this core-only subgraph. F1r3node
 * there denotes core libraries, not every package in the repository.
 * DirectComposition then adds the upper application without reversing a core
 * edge. The executable Cargo package-graph gate must establish correspondence
 * with actual normal/build dependencies; these theorems do not inspect Cargo.
 *
 * The core-only subgraph and its extension are internally consistent: core
 * cannot reach the compiler or application, and no component dependency can
 * reach back to its source. Concrete packages may have within-layer edges;
 * their acyclicity is checked by the executable gate, not by this finite model.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List Arith Lia.

Import ListNotations.

Section BridgeInertness.

  (* The compiler and core-library sides of the bridge. The type and constructor
     names are retained for callers of the core-only model. *)
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

(** Component ranks concern cross-layer edges. Dependencies within one layer
    are not rank-decreasing; the executable gate checks package acyclicity
    separately, including those edges. *)
Module DirectComposition.
  Inductive Component := NodeApplication | MeTTaILBridge | NodeCore.
  Definition rank component :=
    match component with NodeApplication => 2 | MeTTaILBridge => 1 | NodeCore => 0 end.
  Inductive dependency : Component -> Component -> Prop :=
  | application_bridge : dependency NodeApplication MeTTaILBridge
  | application_core : dependency NodeApplication NodeCore
  | bridge_core : dependency MeTTaILBridge NodeCore.
  Inductive reachable : Component -> Component -> Prop :=
  | same_component : forall component, reachable component component
  | follow_dependency : forall source next target,
      dependency source next -> reachable next target -> reachable source target.

  Lemma dependency_decreases_rank : forall source target,
    dependency source target -> rank target < rank source.
  Proof. intros source target H; destruct H; cbn [rank]; lia. Qed.

  Lemma reachability_does_not_increase_rank : forall source target,
    reachable source target -> rank target <= rank source.
  Proof.
    intros source target H; induction H.
    - lia.
    - pose proof (dependency_decreases_rank _ _ H). lia.
  Qed.

  Theorem core_reaches_only_core : forall target,
    reachable NodeCore target -> target = NodeCore.
  Proof.
    intros target H. apply reachability_does_not_increase_rank in H.
    destruct target; cbn [rank] in H; congruence || lia.
  Qed.

  Theorem bridge_cannot_reach_application : ~ reachable MeTTaILBridge NodeApplication.
  Proof.
    intro H. apply reachability_does_not_increase_rank in H. cbn [rank] in H. lia.
  Qed.

  Theorem composition_is_acyclic : forall source target,
    dependency source target -> ~ reachable target source.
  Proof.
    intros source target Hedge Hback.
    apply dependency_decreases_rank in Hedge.
    apply reachability_does_not_increase_rank in Hback. lia.
  Qed.

  Definition embed_core_bridge repo :=
    match repo with MeTTaIL => MeTTaILBridge | F1r3node => NodeCore end.
  Theorem original_bridge_edges_are_preserved : forall source target,
    dep source target -> dependency (embed_core_bridge source) (embed_core_bridge target).
  Proof. intros source target H; destruct H; constructor. Qed.

  Theorem application_composes_existing_bridge : reachable NodeApplication NodeCore.
  Proof.
    eapply follow_dependency; [apply application_bridge|].
    eapply follow_dependency; [apply bridge_core|apply same_component].
  Qed.
End DirectComposition.

Print Assumptions DirectComposition.core_reaches_only_core.
Print Assumptions DirectComposition.bridge_cannot_reach_application.
Print Assumptions DirectComposition.composition_is_acyclic.
Print Assumptions DirectComposition.original_bridge_edges_are_preserved.
Print Assumptions DirectComposition.application_composes_existing_bridge.
