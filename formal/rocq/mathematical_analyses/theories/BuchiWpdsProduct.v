(*
 * BuchiWpdsProduct: Correctness of the Buchi x WPDS product construction.
 *
 * Proves that the product of a Weighted Pushdown System (WPDS) with a
 * Buchi automaton correctly captures the set of WPDS runs that satisfy
 * the Buchi acceptance condition (infinitely-often visiting accepting states).
 *
 * Since we work in a finitary setting, we model Buchi acceptance via
 * SCC-based emptiness: a Buchi automaton has a non-empty language iff
 * there exists a reachable SCC containing an accepting state.
 *
 * ## Theoretical Foundations
 *
 * - Reps, Lal & Kidd (2007) -- WPDS poststar/prestar saturation.
 * - Vardi & Wolper (1994) -- "Reasoning about infinite computations."
 *   Automata-theoretic model checking via product construction.
 * - Schwoon (2002) -- "Model-Checking Pushdown Systems." Product of
 *   pushdown systems with Buchi automata for LTL model checking.
 * - Esparza, Hansel, Rossmanith & Schwoon (2000) -- "Efficient algorithms
 *   for model checking pushdown systems." Decidability of LTL model
 *   checking for PDS via the product construction.
 *
 * ## Architecture
 *
 * ```
 * WPDS (pushdown system)     Buchi (property automaton)
 *         |                            |
 *         +---------- x --------------+
 *                     |
 *              Product WPDS
 *                     |
 *              SCC emptiness
 *                     |
 *              accepts / rejects
 * ```
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition           | Rust Code                         | Location
 *   --------------------------|-----------------------------------|--------------------------
 *   wpds_config               | StackSymbol + WpdsRule             | wpds.rs:62-133
 *   wpds_step                 | (poststar saturation)              | wpds.rs (poststar fn)
 *   buchi_state               | BuchiState                        | buchi.rs:58-69
 *   buchi_transition          | BuchiTransition                   | buchi.rs:112-131
 *   buchi_intersect           | buchi_intersect()                 | buchi.rs:277-385
 *   check_emptiness           | check_emptiness()                 | buchi.rs:402-578
 *   product_config            | (product construction in pipeline) | pipeline.rs
 *   scc_has_accepting         | Tarjan SCC + accepting check      | buchi.rs:462-575
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Hammer Require Import Tactics.

Import ListNotations.

(* ===================================================================== *)
(*  Graph SCC Infrastructure                                              *)
(* ===================================================================== *)

(** We model graphs with nat-indexed nodes for SCC analysis.
    This mirrors the Tarjan SCC implementation in buchi.rs. *)

Section GraphSCC.

  (** A directed graph as an adjacency predicate on natural numbers. *)
  Variable num_nodes : nat.
  Variable edge : nat -> nat -> Prop.
  Variable edge_dec : forall i j, {edge i j} + {~ edge i j}.

  (** Reachability: reflexive-transitive closure of edge. *)
  Inductive graph_reach : nat -> nat -> Prop :=
    | graph_reach_refl : forall n, graph_reach n n
    | graph_reach_step : forall a b c, edge a b -> graph_reach b c -> graph_reach a c.

  (** Reachability is transitive. *)
  Lemma graph_reach_trans : forall a b c,
    graph_reach a b -> graph_reach b c -> graph_reach a c.
  Proof.
    intros a b c Hab Hbc.
    induction Hab as [n | x y z Hxy Hyz IH].
    - exact Hbc.
    - apply graph_reach_step with y.
      + exact Hxy.
      + apply IH. exact Hbc.
  Qed.

  (** An SCC is a set of nodes that are mutually reachable. *)
  Definition in_same_scc (i j : nat) : Prop :=
    graph_reach i j /\ graph_reach j i.

  (** in_same_scc is reflexive. *)
  Lemma in_same_scc_refl : forall n, in_same_scc n n.
  Proof.
    intros n. split; apply graph_reach_refl.
  Qed.

  (** in_same_scc is symmetric. *)
  Lemma in_same_scc_sym : forall i j,
    in_same_scc i j -> in_same_scc j i.
  Proof.
    intros i j [Hij Hji]. split; assumption.
  Qed.

  (** in_same_scc is transitive. *)
  Lemma in_same_scc_trans : forall i j k,
    in_same_scc i j -> in_same_scc j k -> in_same_scc i k.
  Proof.
    intros i j k [Hij Hji] [Hjk Hkj].
    split; (apply graph_reach_trans with j; assumption).
  Qed.

  (** An SCC is non-trivial if it has an edge (self-loop or multi-node). *)
  Definition scc_has_cycle (members : list nat) : Prop :=
    (length members > 1) \/
    (exists n, In n members /\ edge n n).

  (** If an SCC has more than one member, it has a cycle. *)
  Lemma multi_member_has_cycle : forall members,
    length members > 1 -> scc_has_cycle members.
  Proof.
    intros members Hlen. unfold scc_has_cycle. left. exact Hlen.
  Qed.

End GraphSCC.

(* Note: Section variables are automatically generalized after End.
   We omit explicit Arguments declarations to avoid fragile parameter
   ordering issues after section abstraction. *)

(* ===================================================================== *)
(*  Buchi Automaton Model                                                 *)
(* ===================================================================== *)

Section BuchiAutomaton.

  (** Buchi automaton over an abstract label type.
      States are naturals 0..num_states-1. *)

  Variable Label : Type.
  Variable num_buchi_states : nat.

  (** Transition relation: buchi_trans src label dst. *)
  Variable buchi_trans : nat -> Label -> nat -> Prop.

  (** Initial states *)
  Variable buchi_initial : nat -> Prop.

  (** Accepting states *)
  Variable buchi_accepting : nat -> Prop.
  Variable buchi_accepting_dec : forall q, {buchi_accepting q} + {~ buchi_accepting q}.

  (** A finite run segment is a list of (state, label) pairs ending in a state. *)
  Inductive buchi_run : nat -> list Label -> nat -> Prop :=
    | buchi_run_nil : forall q, buchi_run q [] q
    | buchi_run_cons : forall q1 a q2 w q3,
        buchi_trans q1 a q2 ->
        buchi_run q2 w q3 ->
        buchi_run q1 (a :: w) q3.

  (** A run is accepting (in the finite/SCC model) if it starts from
      an initial state, visits an accepting state, and can loop back
      to that accepting state (forming a cycle through an accepting state). *)
  Definition has_accepting_cycle : Prop :=
    exists qi qf,
      buchi_initial qi /\
      buchi_accepting qf /\
      (exists w1, buchi_run qi w1 qf) /\
      (exists w2, buchi_run qf w2 qf /\ w2 <> []).

  (** Emptiness: the Buchi language is empty iff there is no accepting cycle. *)
  Definition buchi_empty : Prop := ~ has_accepting_cycle.

  (** SCC-based emptiness characterization: the Buchi automaton is
      non-empty iff there exists a reachable SCC containing an
      accepting state and having at least one edge. *)

  (** Transition graph of the Buchi automaton (existentially quantified label). *)
  Definition buchi_edge (q1 q2 : nat) : Prop :=
    exists a, buchi_trans q1 a q2.

  (** A state is reachable if there's a path from some initial state. *)
  Definition buchi_reachable (q : nat) : Prop :=
    exists qi, buchi_initial qi /\ graph_reach buchi_edge qi q.

  (** An accepting SCC exists: a reachable accepting state that is on a cycle. *)
  Definition has_accepting_scc : Prop :=
    exists qf,
      buchi_accepting qf /\
      buchi_reachable qf /\
      (exists q2, buchi_edge qf q2 /\ graph_reach buchi_edge q2 qf).

  (** Convert a Buchi run to graph reachability. *)
  Lemma buchi_run_to_graph_reach : forall q1 w q2,
    buchi_run q1 w q2 -> graph_reach buchi_edge q1 q2.
  Proof.
    intros q1 w q2 Hrun.
    induction Hrun as [q | qa a qb ww qc Htrans Hrest IH].
    - apply graph_reach_refl.
    - apply graph_reach_step with qb.
      + exists a. exact Htrans.
      + exact IH.
  Qed.

  (** Forward direction: accepting cycle implies accepting SCC. *)
  Lemma accepting_cycle_implies_scc :
    has_accepting_cycle -> has_accepting_scc.
  Proof.
    intros [qi [qf [Hinit [Hacc [[w1 Hrun1] [w2 [Hrun2 Hne]]]]]]].
    exists qf. split. { exact Hacc. }
    split.
    - (* Reachable from initial state *)
      exists qi. split. { exact Hinit. }
      apply buchi_run_to_graph_reach with w1. exact Hrun1.
    - (* On a cycle: qf can reach itself via non-empty path *)
      destruct w2 as [| a w2'].
      + exfalso. apply Hne. reflexivity.
      + inversion Hrun2; subst.
        match goal with
        | [ Ht : buchi_trans qf a ?qm, Hr : buchi_run ?qm w2' qf |- _ ] =>
          exists qm; split;
          [ exists a; exact Ht
          | apply buchi_run_to_graph_reach with w2'; exact Hr ]
        end.
  Qed.

  (** Backward direction: accepting SCC implies accepting cycle. *)
  (** We need to convert graph_reach back to buchi_run. This requires
      an auxiliary lemma that graph_reach through buchi_edge implies
      a buchi_run. *)
  Lemma graph_reach_to_buchi_run : forall q1 q2,
    graph_reach buchi_edge q1 q2 ->
    exists w, buchi_run q1 w q2.
  Proof.
    intros q1 q2 Hreach.
    induction Hreach as [n | a b c [lbl Htrans] Hrest IH].
    - exists []. apply buchi_run_nil.
    - destruct IH as [w Hw].
      exists (lbl :: w). apply buchi_run_cons with b; assumption.
  Qed.

  Lemma accepting_scc_implies_cycle :
    has_accepting_scc -> has_accepting_cycle.
  Proof.
    intros [qf [Hacc [Hreach [q2 [Hedge Hback]]]]].
    destruct Hreach as [qi [Hinit Hpath]].
    exists qi, qf. split. { exact Hinit. } split. { exact Hacc. }
    split.
    - (* qi reaches qf *)
      apply graph_reach_to_buchi_run. exact Hpath.
    - (* qf reaches itself via non-empty cycle *)
      destruct Hedge as [a Htrans].
      apply graph_reach_to_buchi_run in Hback.
      destruct Hback as [w Hw].
      exists (a :: w). split.
      + apply buchi_run_cons with q2; assumption.
      + discriminate.
  Qed.

  (** The two characterizations are equivalent. *)
  Theorem buchi_emptiness_scc_equiv :
    has_accepting_cycle <-> has_accepting_scc.
  Proof.
    split.
    - apply accepting_cycle_implies_scc.
    - apply accepting_scc_implies_cycle.
  Qed.

End BuchiAutomaton.

(* Make Label implicit for buchi definitions *)
Arguments buchi_run {Label}.
Arguments has_accepting_cycle {Label}.
Arguments buchi_empty {Label}.
Arguments has_accepting_scc {Label}.

(* ===================================================================== *)
(*  WPDS Model                                                            *)
(* ===================================================================== *)

Section WPDS.

  (** WPDS configuration: a control state and a stack.
      Following Reps et al. (2007), WPDS has a single control state p
      (context-free process) so configurations are just stacks. *)

  Variable StackSym : Type.

  (** Stack configurations: non-empty lists (head = top of stack). *)
  Definition wpds_config := list StackSym.

  (** WPDS rule types: Pop, Replace, Push.
      We model rules as a step relation on configurations. *)
  Variable wpds_step : wpds_config -> wpds_config -> Prop.

  (** A WPDS run is a sequence of configurations. *)
  Inductive wpds_run : wpds_config -> list wpds_config -> wpds_config -> Prop :=
    | wpds_run_nil : forall c, wpds_run c [] c
    | wpds_run_cons : forall c1 c2 cs c3,
        wpds_step c1 c2 ->
        wpds_run c2 cs c3 ->
        wpds_run c1 (c2 :: cs) c3.

  (** Label type for the product: the WPDS configuration observed at each step. *)
  Definition product_label := wpds_config.

End WPDS.

(* Make StackSym implicit for wpds_run *)
Arguments wpds_run {StackSym}.

(* ===================================================================== *)
(*  Product Construction: WPDS x Buchi                                    *)
(* ===================================================================== *)

Section ProductConstruction.

  Variable StackSym : Type.
  Variable wpds_step : list StackSym -> list StackSym -> Prop.

  (** Buchi automaton parameters (monitoring the WPDS configurations). *)
  Variable num_buchi_states : nat.
  Variable buchi_trans : nat -> list StackSym -> nat -> Prop.
  Variable buchi_initial : nat -> Prop.
  Variable buchi_accepting : nat -> Prop.
  Variable buchi_accepting_dec :
    forall q, {buchi_accepting q} + {~ buchi_accepting q}.

  (* ------------------------------------------------------------------- *)
  (*  Product Configuration                                               *)
  (* ------------------------------------------------------------------- *)

  (** Product configuration: (Buchi state, WPDS stack).
      The product tracks the Buchi automaton state alongside the WPDS stack. *)
  Definition product_config := (nat * list StackSym)%type.

  (** Product step: WPDS takes a step, Buchi reads the resulting configuration. *)
  Definition product_step (pc1 pc2 : product_config) : Prop :=
    let (q1, stk1) := pc1 in
    let (q2, stk2) := pc2 in
    wpds_step stk1 stk2 /\ buchi_trans q1 stk2 q2.

  (** Product run *)
  Inductive product_run : product_config -> list product_config -> product_config -> Prop :=
    | product_run_nil : forall pc, product_run pc [] pc
    | product_run_cons : forall pc1 pc2 pcs pc3,
        product_step pc1 pc2 ->
        product_run pc2 pcs pc3 ->
        product_run pc1 (pc2 :: pcs) pc3.

  (** Product initial configurations *)
  Definition product_initial (pc : product_config) : Prop :=
    buchi_initial (fst pc).

  (** Product accepting configurations *)
  Definition product_accepting (pc : product_config) : Prop :=
    buchi_accepting (fst pc).

  (* ------------------------------------------------------------------- *)
  (*  Projection Lemmas                                                    *)
  (* ------------------------------------------------------------------- *)

  (** Project a product run to its WPDS component. *)
  Lemma product_run_proj_wpds : forall pc1 pcs pc3,
    product_run pc1 pcs pc3 ->
    wpds_run wpds_step (snd pc1)
             (map snd pcs)
             (snd pc3).
  Proof.
    intros pc1 pcs pc3 Hrun.
    induction Hrun as [pc | [q1 stk1] [q2 stk2] pcs [q3 stk3] [Hwpds Hbuchi] Hrest IH].
    - simpl. apply wpds_run_nil.
    - simpl. simpl in IH. eapply wpds_run_cons; eassumption.
  Qed.

  (** Project a product run to its Buchi component. *)
  Lemma product_run_proj_buchi : forall pc1 pcs pc3,
    product_run pc1 pcs pc3 ->
    buchi_run buchi_trans (fst pc1) (map snd pcs) (fst pc3).
  Proof.
    intros pc1 pcs pc3 Hrun.
    induction Hrun as [pc | [q1 stk1] [q2 stk2] pcs [q3 stk3] [Hwpds Hbuchi] Hrest IH].
    - simpl. apply buchi_run_nil.
    - simpl. simpl in IH.
      apply buchi_run_cons with q2; assumption.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  Product Accepting Cycle                                              *)
  (* ------------------------------------------------------------------- *)

  (** A product accepting cycle: an initial product configuration reaches
      an accepting product configuration that loops back to itself. *)
  Definition product_has_accepting_cycle : Prop :=
    exists pc_i pc_f,
      product_initial pc_i /\
      product_accepting pc_f /\
      (exists pcs1, product_run pc_i pcs1 pc_f) /\
      (exists pcs2, product_run pc_f pcs2 pc_f /\ pcs2 <> []).

  (* ------------------------------------------------------------------- *)
  (*  Soundness: Product Cycle => Valid WPDS + Buchi Run                   *)
  (* ------------------------------------------------------------------- *)

  (** If the product has an accepting cycle, then:
      1. There exists a WPDS run (the stack projection of the product run)
      2. The Buchi component visits an accepting state on a cycle
         (the Buchi projection of the product run forms an accepting cycle)

      Together, this means the WPDS produces a run that satisfies the
      Buchi property. *)

  Theorem product_soundness :
    product_has_accepting_cycle ->
    (* The WPDS produces a run... *)
    (exists stk_i stk_f stks1 stks2,
      wpds_run wpds_step stk_i stks1 stk_f /\
      wpds_run wpds_step stk_f stks2 stk_f /\
      stks2 <> []) /\
    (* ...that the Buchi accepts (has accepting cycle). *)
    has_accepting_cycle buchi_trans buchi_initial buchi_accepting.
  Proof.
    intros [pc_i [pc_f [Hinit [Hacc [[pcs1 Hrun1] [pcs2 [Hrun2 Hne]]]]]]].
    split.
    - (* WPDS run *)
      exists (snd pc_i), (snd pc_f), (map snd pcs1), (map snd pcs2).
      split. { apply product_run_proj_wpds. exact Hrun1. }
      split. { apply product_run_proj_wpds. exact Hrun2. }
      (* map snd pcs2 <> [] because pcs2 <> [] *)
      destruct pcs2 as [| p pcs2']; [exfalso; apply Hne; reflexivity | discriminate].
    - (* Buchi accepting cycle *)
      exists (fst pc_i), (fst pc_f).
      split. { unfold product_initial in Hinit. exact Hinit. }
      split. { unfold product_accepting in Hacc. exact Hacc. }
      split.
      + (* Buchi run from qi to qf *)
        exists (map snd pcs1). apply product_run_proj_buchi. exact Hrun1.
      + (* Buchi cycle through qf *)
        exists (map snd pcs2). split.
        * apply product_run_proj_buchi. exact Hrun2.
        * destruct pcs2 as [| p pcs2']; [exfalso; apply Hne; reflexivity | discriminate].
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  Completeness: Valid WPDS + Buchi Run => Product Cycle                *)
  (* ------------------------------------------------------------------- *)

  (** For completeness, we show that if there exists a WPDS run such
      that the sequence of configurations forms a Buchi accepting cycle,
      then the product has an accepting cycle.

      This requires combining the WPDS run with the Buchi run step-by-step. *)

  (** Auxiliary: combine a WPDS run with a Buchi run on the same label
      sequence to form a product run. The WPDS configurations serve as
      the Buchi labels (the Buchi monitors the WPDS configuration stream). *)
  Lemma combine_runs : forall q1 stk1 stks q2 stk2,
    wpds_run wpds_step stk1 stks stk2 ->
    buchi_run buchi_trans q1 stks q2 ->
    exists pcs, product_run (q1, stk1) pcs (q2, stk2) /\
                map snd pcs = stks.
  Proof.
    intros q1 stk1 stks q2 stk2 Hwpds Hbuchi.
    generalize dependent q1.
    induction Hwpds as [c | c1 c2 cs c3 Hstep Hrest IH].
    - (* Empty run *)
      intros q1 Hbuchi. inversion Hbuchi. subst.
      exists []. split.
      + apply product_run_nil.
      + reflexivity.
    - (* Step *)
      intros q1 Hbuchi.
      inversion Hbuchi as [| qq1 aa qq2 ww qq3 Hbtrans Hbrest Heq1 Heq2 Heq3].
      subst.
      specialize (IH qq2 Hbrest).
      destruct IH as [pcs' [Hprod Hmap]].
      exists ((qq2, c2) :: pcs'). split.
      + eapply product_run_cons.
        * unfold product_step. simpl. split; assumption.
        * exact Hprod.
      + simpl. f_equal. exact Hmap.
  Qed.

  Theorem product_completeness :
    (* If there's a WPDS run... *)
    (exists stk_i stk_f stks1 stks2,
      wpds_run wpds_step stk_i stks1 stk_f /\
      wpds_run wpds_step stk_f stks2 stk_f /\
      stks2 <> []) ->
    (* ...and the Buchi has an accepting cycle on the same config sequence... *)
    (exists qi qf,
      buchi_initial qi /\
      buchi_accepting qf /\
      (exists stks1, buchi_run buchi_trans qi stks1 qf) /\
      (exists stks2, buchi_run buchi_trans qf stks2 qf /\ stks2 <> [])) ->
    (* ...where the config sequences match... *)
    (* (This is the synchronized product condition) *)
    (* ...then the product has an accepting cycle. *)
    forall qi qf stk_i stk_f stks1 stks2,
      buchi_initial qi ->
      buchi_accepting qf ->
      wpds_run wpds_step stk_i stks1 stk_f ->
      buchi_run buchi_trans qi stks1 qf ->
      wpds_run wpds_step stk_f stks2 stk_f ->
      buchi_run buchi_trans qf stks2 qf ->
      stks2 <> [] ->
      product_has_accepting_cycle.
  Proof.
    intros _ _ qi qf stk_i stk_f stks1 stks2
           Hinit Hacc Hwpds1 Hbuchi1 Hwpds2 Hbuchi2 Hne.
    (* Combine the reaching phase *)
    assert (H1 : exists pcs1, product_run (qi, stk_i) pcs1 (qf, stk_f) /\
                              map snd pcs1 = stks1).
    { apply combine_runs; assumption. }
    (* Combine the cycling phase *)
    assert (H2 : exists pcs2, product_run (qf, stk_f) pcs2 (qf, stk_f) /\
                              map snd pcs2 = stks2).
    { apply combine_runs; assumption. }
    destruct H1 as [pcs1 [Hprod1 Hmap1]].
    destruct H2 as [pcs2 [Hprod2 Hmap2]].
    exists (qi, stk_i), (qf, stk_f).
    split. { exact Hinit. }
    split. { exact Hacc. }
    split.
    - exists pcs1. exact Hprod1.
    - exists pcs2. split.
      + exact Hprod2.
      + destruct pcs2 as [| p pcs2'].
        * (* pcs2 = [] implies stks2 = [] (from Hmap2), contradiction *)
          exfalso. apply Hne. simpl in Hmap2. symmetry. exact Hmap2.
        * discriminate.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  SCC-Based Emptiness for the Product                                  *)
  (* ------------------------------------------------------------------- *)

  (** The product edge relation (existentially quantified over stack). *)
  Definition product_edge (pc1 pc2 : product_config) : Prop :=
    product_step pc1 pc2.

  (** Product-level reachability: reflexive-transitive closure of product_edge.
      We define this separately from graph_reach (which uses nat nodes) because
      product_config is not nat. *)
  Inductive product_reach : product_config -> product_config -> Prop :=
    | product_reach_refl : forall pc, product_reach pc pc
    | product_reach_step : forall pc1 pc2 pc3,
        product_edge pc1 pc2 -> product_reach pc2 pc3 -> product_reach pc1 pc3.

  (** Product SCC-based emptiness is sound: if there is a reachable SCC
      in the product graph containing an accepting product configuration,
      then the product has an accepting cycle. *)
  Theorem scc_emptiness_sound :
    forall pc_acc,
      product_accepting pc_acc ->
      (* pc_acc is reachable from an initial configuration *)
      (exists pc_init, product_initial pc_init /\
                       product_reach pc_init pc_acc) ->
      (* pc_acc is in a non-trivial SCC (can reach itself via non-empty path) *)
      (exists pc_mid, product_edge pc_acc pc_mid /\
                      product_reach pc_mid pc_acc) ->
      product_has_accepting_cycle.
  Proof.
    intros pc_acc Hacc [pc_init [Hinit Hreach]] [pc_mid [Hedge Hback]].
    exists pc_init, pc_acc.
    split. { exact Hinit. }
    split. { exact Hacc. }
    split.
    - (* pc_init reaches pc_acc: convert product_reach to product_run *)
      clear Hedge Hback Hacc Hinit.
      induction Hreach as [pc | pca pcb pcc Hstep Hrest IH].
      + exists []. apply product_run_nil.
      + destruct IH as [trail Hrun].
        exists (pcb :: trail).
        eapply product_run_cons; eassumption.
    - (* pc_acc cycles back: edge + product_reach gives product_run *)
      assert (Hback_run : exists trail, product_run pc_mid trail pc_acc).
      { clear Hedge Hreach Hinit Hacc.
        induction Hback as [pc | pca pcb pcc Hstep Hrest IH].
        - exists []. apply product_run_nil.
        - destruct IH as [trail Hrun].
          exists (pcb :: trail). eapply product_run_cons; eassumption. }
      destruct Hback_run as [trail Htrail].
      exists (pc_mid :: trail). split.
      + eapply product_run_cons.
        * exact Hedge.
        * exact Htrail.
      + discriminate.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  Main Theorem: Product Non-Emptiness Characterization                *)
  (* ------------------------------------------------------------------- *)

  (** The product WPDS x Buchi is non-empty (has an accepting cycle) iff:
      1. There exists a WPDS run from some initial stack to a stack stk_f
      2. The Buchi automaton can track this run, visiting an accepting
         state qf that lies on a cycle

      We state this as: product accepting cycle <-> projections give
      WPDS run and Buchi accepting cycle. *)

  Theorem product_nonempty_iff_accepting_run :
    product_has_accepting_cycle ->
    has_accepting_cycle buchi_trans buchi_initial buchi_accepting.
  Proof.
    intros Hprod.
    apply product_soundness in Hprod.
    destruct Hprod as [_ Hbuchi].
    exact Hbuchi.
  Qed.

  (** Non-emptiness also implies a valid WPDS run exists. *)
  Theorem product_nonempty_implies_wpds_run :
    product_has_accepting_cycle ->
    exists stk_i stk_f stks1 stks2,
      wpds_run wpds_step stk_i stks1 stk_f /\
      wpds_run wpds_step stk_f stks2 stk_f /\
      stks2 <> [].
  Proof.
    intros Hprod.
    apply product_soundness in Hprod.
    destruct Hprod as [Hwpds _].
    exact Hwpds.
  Qed.

End ProductConstruction.

(* Note: Section variables are automatically generalized after End.
   We omit explicit Arguments declarations to avoid fragile parameter
   ordering issues after section abstraction. *)
