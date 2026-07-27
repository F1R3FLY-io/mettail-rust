(*
 * CollectionPrefixDispatchFork: FV-FIRST spec for ROOT-A — the shared-open
 * `{` prefix-dispatch fork that lets Rholang Map literals `{1:2}` parse while
 * preserving braced `{P|Q}` parallel (PPar).
 *
 * THE DEFECT (trace-evidenced; rholang Proc entry):
 *   `Proc::parse("{1:2}")` FAILS but `Map::parse("{1:2}")` SUCCEEDS. At Proc
 *   entry the open `{` is a single (non-lex-ambiguous) token, so the lex-fork
 *   is SKIPPED and the braced PPar arm (collection.rs `emit_collection_prefix_
 *   arms`) commits a `ConsumeAndPush(collection_marker)` BEFORE the registered
 *   `Map` cross-cat projection alternative (`CrossCatProjection{source=Map}`)
 *   can be tried. The PPar continuation then dies on the `:` (it expects `|`
 *   or `}`), so `{1:2}` is lost.
 *
 * THE FIX (this spec, ROOT-A):
 *   At codegen time, when a braced collection rule's open token COLLIDES with
 *   a cross-cat projection into a collection-kind source sharing that open
 *   token, the prefix arm emits a `Fork` instead of a bare `ConsumeAndPush`:
 *     branch0  — the PPar collection marker (`ConsumeAndPush{Discard}`,
 *                weight BP_TIER_INFIX = 0.000, the PRIMARY infix tier);
 *     branch1+ — the Map cross-cat projection (`Push` into
 *                `CrossCatDelegate{source}`, weight
 *                BP_TIER_CROSSCAT_PROJECTION = 0.025).
 *   When there is NO collision the arm stays the byte-identical bare
 *   `ConsumeAndPush` (the no-collision fast path).
 *
 * THE MODEL: input is a lex DAG (node -> labelled out-edges) — the SAME
 * abstraction `CollectionForkEvidence.v` uses. The two collection
 * continuation languages sharing the open `{` are:
 *   ppar_run  =  ( elem (l_sep_par elem)* )?  l_close          (* {P|Q} / {} *)
 *   map_run   =  ( key l_kvsep val (l_sep_map key l_kvsep val)* )?  l_close
 *                                                              (* {k:v,..} / {} *)
 *   fork_run  =  ppar_run  \/  map_run     (the collision fork)
 *
 * THEOREMS (all admission-free; each followed by Print Assumptions, which
 * must report "Closed under the global context"):
 *   prefix_fork_no_loss                     — both branches' languages embed
 *                                             into the fork (NO valid parse is
 *                                             lost by forking);
 *   prefix_fork_no_spurious_accept          — the fork accepts ONLY a PPar or a
 *                                             Map run (no fabricated language);
 *   prefix_fork_mutually_exclusive_past_first_sep
 *                                           — at a DECISIVE post-element node
 *                                             (a real input position carries one
 *                                             token) a PPar separator (`|`) and a
 *                                             Map kv-separator (`:`) cannot
 *                                             coexist when `|` <> `:` (inversion
 *                                             on the loop constructors);
 *   empty_collection_tie_breaks_to_primary  — for empty `{}` both branches
 *                                             accept, so selection is by weight;
 *                                             0.0 < 0.025 picks the PPar branch;
 *   len1_fastpath_byte_identical            — empty projection set ⇒ the fork
 *                                             collapses to exactly ppar_run (the
 *                                             no-collision fast path is a
 *                                             propositional identity = same
 *                                             accepted language);
 *   prefix_fork_frontier_delta_le_one       — the fork adds at most one cursor
 *                                             (mirrors BalancedCohortGate
 *                                             `cursors_added_le_one`): +1 on a
 *                                             collision, +0 in the fast path.
 *
 * Non-vacuity witnesses (concrete finite DAGs): `{1:2}` accepts as a Map and
 * NOT as a PPar; `{1|2}` accepts as a PPar and NOT as a Map; `{}` accepts as
 * both (the weight tie-break decides).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Section CollectionPrefixDispatchFork.

  (* Lex DAG: nodes are nats; out-edges are (label, target) pairs — the same
     shape as CollectionForkEvidence.v. *)
  Definition Edge : Type := (nat * nat)%type.   (* (label, target) *)
  Variable out_edges : nat -> list Edge.

  (* The shared-open `{` collection literals' delimiter labels. *)
  Variable l_close   : nat.   (* "}" *)
  Variable l_sep_par : nat.   (* "|"  — PPar element separator        *)
  Variable l_sep_map : nat.   (* ","  — Map inter-pair separator      *)
  Variable l_kvsep   : nat.   (* ":"  — Map key/value separator       *)

  (* Elements abstractly: elem_spell n m = an element parse starting at node n
     ends at node m. A Proc (PPar element), or a key/value (Map). *)
  Variable elem_spell : nat -> nat -> Prop.

  (* ───────────────────────── PPar run ─────────────────────────
        ppar_run = ( elem (l_sep_par elem)* )? l_close
     ppar_loop is the post-(first-element) continuation: (l_sep_par elem)* l_close *)

  Inductive ppar_loop : nat -> nat -> Prop :=
    | pl_close : forall n t,
        In (l_close, t) (out_edges n) ->
        ppar_loop n t
    | pl_sep : forall n t e m,
        In (l_sep_par, t) (out_edges n) ->        (* `|` *)
        elem_spell t e ->                           (* next element *)
        ppar_loop e m ->
        ppar_loop n m.

  Inductive ppar_run : nat -> nat -> Prop :=
    | pr_empty : forall n t,                        (* `{}` — empty bag *)
        In (l_close, t) (out_edges n) ->
        ppar_run n t
    | pr_nonempty : forall n e m,
        elem_spell n e ->                           (* first element *)
        ppar_loop e m ->
        ppar_run n m.

  (* ───────────────────────── Map run ──────────────────────────
        map_run = ( key l_kvsep val (l_sep_map key l_kvsep val)* )? l_close
     map_pair_loop is the post-(first-pair) continuation:
        (l_sep_map key l_kvsep val)* l_close *)

  Inductive map_pair_loop : nat -> nat -> Prop :=
    | mpl_close : forall n t,
        In (l_close, t) (out_edges n) ->
        map_pair_loop n t
    | mpl_pair : forall n t kend vstart vend m,
        In (l_sep_map, t) (out_edges n) ->          (* `,` *)
        elem_spell t kend ->                          (* next key *)
        In (l_kvsep, vstart) (out_edges kend) ->     (* `:` *)
        elem_spell vstart vend ->                     (* value *)
        map_pair_loop vend m ->
        map_pair_loop n m.

  Inductive map_run : nat -> nat -> Prop :=
    | mr_empty : forall n t,                          (* `{}` — empty map *)
        In (l_close, t) (out_edges n) ->
        map_run n t
    | mr_nonempty : forall n kend vstart vend m,
        elem_spell n kend ->                          (* first key *)
        In (l_kvsep, vstart) (out_edges kend) ->     (* `:` *)
        elem_spell vstart vend ->                     (* first value *)
        map_pair_loop vend m ->
        map_run n m.

  (* ───────────────── The dispatch fork's accepted language ─────────────────
     The collision fork (branch0 PPar + branch1 Map) accepts the UNION. *)
  Definition fork_run (n m : nat) : Prop := ppar_run n m \/ map_run n m.

  (* The codegen-parameterized fork: when `proj = false` (empty projection set
     / no collision) the Map branch is NOT emitted, so the fork degenerates to
     exactly ppar_run; when `proj = true` (collision) both branches exist. *)
  Definition fork_run_when (proj : bool) (n m : nat) : Prop :=
    ppar_run n m \/ (proj = true /\ map_run n m).

  (* ══════════════════ T1 — prefix_fork_no_loss ══════════════════
     Both branch languages embed into the fork: forking REMOVES nothing. *)
  Theorem prefix_fork_no_loss :
    forall n m,
      (ppar_run n m -> fork_run n m)
      /\ (map_run n m -> fork_run n m).
  Proof.
    intros n m. unfold fork_run. split; intro H; [left | right]; exact H.
  Qed.

  (* ══════════════════ T2 — prefix_fork_no_spurious_accept ══════════════════
     The fork accepts ONLY a PPar run or a Map run — no fabricated language. *)
  Theorem prefix_fork_no_spurious_accept :
    forall n m, fork_run n m -> ppar_run n m \/ map_run n m.
  Proof.
    intros n m H. exact H.
  Qed.

  (* ── Inversion lemmas for the decisive theorem (inversion on the loop
        constructors). ── *)

  (* A PPar continuation at e that does NOT immediately close MUST consume the
     PPar separator `|`. *)
  Lemma ppar_loop_sep_edge_when_not_close :
    forall e m,
      ppar_loop e m ->
      (forall t, ~ In (l_close, t) (out_edges e)) ->
      exists t, In (l_sep_par, t) (out_edges e).
  Proof.
    intros e m H Hnc. inversion H; subst.
    - exfalso. eapply Hnc; eassumption.
    - eexists; eassumption.
  Qed.

  (* A non-empty Map run's first post-key edge is the key/value separator `:`. *)
  Lemma map_run_kvsep_edge :
    forall n m,
      map_run n m ->
      (forall t, ~ In (l_close, t) (out_edges n)) ->
      exists kend vstart,
        elem_spell n kend /\ In (l_kvsep, vstart) (out_edges kend).
  Proof.
    intros n m H Hnc. inversion H; subst.
    - exfalso. eapply Hnc; eassumption.
    - exists kend, vstart. split; assumption.
  Qed.

  (* ══════ T3 — prefix_fork_mutually_exclusive_past_first_sep ══════
     At a DECISIVE post-element node e (every out-edge of e shares one label —
     a real linear input position carries exactly one token), a PPar
     continuation taking the separator branch (`|`) and a Map continuation
     taking the kv-separator branch (`:`) cannot coexist when `|` <> `:`. *)
  Theorem prefix_fork_mutually_exclusive_past_first_sep :
    l_sep_par <> l_kvsep ->
    forall e m1 vstart,
      ppar_loop e m1 ->                               (* PPar continues at e *)
      (forall t, ~ In (l_close, t) (out_edges e)) ->  (* past the first sep:
                                                          not the immediate close *)
      In (l_kvsep, vstart) (out_edges e) ->           (* Map's `:` at e *)
      (forall l1 t1 l2 t2,                            (* e is DECISIVE *)
         In (l1, t1) (out_edges e) -> In (l2, t2) (out_edges e) -> l1 = l2) ->
      False.
  Proof.
    intros Hne e m1 vstart Hppar Hnc Hkv Hdec.
    destruct (ppar_loop_sep_edge_when_not_close e m1 Hppar Hnc) as [t Hsep].
    apply Hne. exact (Hdec _ _ _ _ Hsep Hkv).
  Qed.

  (* ── Branch weights (milliunits in nat — Rocq has no float; faithful to
        rigail::lex_weight where the runtime selects the MINIMUM-cost branch,
        i.e. LOWER weight wins). BP_TIER_INFIX = 0.000, the PPar collection
        marker / primary infix tier; BP_TIER_CROSSCAT_PROJECTION = 0.025, the
        Map projection. ── *)
  Definition BP_TIER_INFIX_milli : nat := 0.
  Definition BP_TIER_CROSSCAT_PROJECTION_milli : nat := 25.

  Theorem bp_tier_infix_lt_projection :
    BP_TIER_INFIX_milli < BP_TIER_CROSSCAT_PROJECTION_milli.
  Proof.
    unfold BP_TIER_INFIX_milli, BP_TIER_CROSSCAT_PROJECTION_milli. lia.
  Qed.

  Inductive ForkBranchTag := BranchPPar | BranchMap.

  Definition branch_weight (b : ForkBranchTag) : nat :=
    match b with
    | BranchPPar => BP_TIER_INFIX_milli
    | BranchMap  => BP_TIER_CROSSCAT_PROJECTION_milli
    end.

  (* For empty `{}` BOTH branches accept (an empty bag vs an empty map — see
     the EmptyWitness below), so selection is purely by weight: the min-cost
     winner of the two-branch fork. *)
  Definition empty_fork_winner : ForkBranchTag :=
    if Nat.leb (branch_weight BranchPPar) (branch_weight BranchMap)
    then BranchPPar else BranchMap.

  (* ══════ T4 — empty_collection_tie_breaks_to_primary ══════ *)
  Theorem empty_collection_tie_breaks_to_primary :
    empty_fork_winner = BranchPPar.
  Proof. reflexivity. Qed.

  (* Strengthening: BranchPPar is the STRICT minimum — the tie-break is a strict
     cost win, not an accident of the <= direction. *)
  Theorem empty_primary_strictly_cheaper :
    branch_weight BranchPPar < branch_weight BranchMap.
  Proof. simpl. exact bp_tier_infix_lt_projection. Qed.

  (* ══════ T5 — len1_fastpath_byte_identical ══════
     Empty projection set (proj = false) ⇒ the fork accepts EXACTLY ppar_run.
     This is the no-collision fast path: the codegen emits the byte-identical
     bare ConsumeAndPush, so the accepted language is unchanged. *)
  Theorem len1_fastpath_byte_identical :
    forall n m, fork_run_when false n m <-> ppar_run n m.
  Proof.
    intros n m. unfold fork_run_when. split.
    - intros [H | [Hc _]]; [exact H | discriminate Hc].
    - intro H. left. exact H.
  Qed.

  (* And the collision case (proj = true) is exactly the collision fork. *)
  Theorem fork_run_when_true_eq_collision :
    forall n m, fork_run_when true n m <-> fork_run n m.
  Proof.
    intros n m. unfold fork_run_when, fork_run. split.
    - intros [H | [_ H]]; [left | right]; exact H.
    - intros [H | H]; [left; exact H | right; split; [reflexivity | exact H]].
  Qed.

  (* ── Fork frontier delta (mirror BalancedCohortGate.cursors_added_le_one).
        The PPar branch is the baseline (the cursor the bare ConsumeAndPush
        would have produced anyway); the fork ADDS the Map projection branch:
        +1 cursor on a collision, +0 in the fast path. ── *)
  Definition fork_cursors_added (proj : bool) : nat :=
    if proj then 1 else 0.

  (* ══════ T6 — prefix_fork_frontier_delta_le_one ══════ *)
  Theorem prefix_fork_frontier_delta_le_one :
    forall proj, fork_cursors_added proj <= 1.
  Proof. intro proj. destruct proj; simpl; lia. Qed.

  Theorem prefix_fork_delta_zero_in_fastpath :
    fork_cursors_added false = 0.
  Proof. reflexivity. Qed.

  Theorem prefix_fork_delta_one_on_collision :
    fork_cursors_added true = 1.
  Proof. reflexivity. Qed.

End CollectionPrefixDispatchFork.

(* ════════════════════════════════════════════════════════════════════
   NON-VACUITY WITNESSES (concrete finite lex DAGs). Labels:
     0 = close ("}"), 1 = sep_par ("|"), 2 = sep_map (","), 3 = kvsep (":").
   ════════════════════════════════════════════════════════════════════ *)

(* ── `{1:2}`: a Map, NOT a PPar. After the key `1` (elem 0→1) the only edge
      at node 1 is `:` (kvsep, label 3) → 2; value `2` (elem 2→3); close `}`
      (label 0) → 4. ── *)
Section MapWitness.

  Definition mw_edges (n : nat) : list (nat * nat) :=
    match n with
    | 1 => [(3, 2)]          (* `:` → node 2 *)
    | 3 => [(0, 4)]          (* `}` → node 4 *)
    | _ => []
    end.
  Definition mw_elem (n m : nat) : Prop :=
    (n = 0 /\ m = 1) \/ (n = 2 /\ m = 3).

  (* The Map branch accepts `{1:2}`  (map_run discharges out_edges, l_close,
     l_sep_map, l_kvsep, elem_spell — here 0, 2, 3). *)
  Theorem map_witness_map_accepts :
    map_run mw_edges 0 2 3 mw_elem 0 4.
  Proof.
    eapply mr_nonempty.
    - left; split; reflexivity.          (* key elem 0→1 *)
    - simpl; left; reflexivity.           (* `:` edge at node 1 *)
    - right; split; reflexivity.          (* value elem 2→3 *)
    - eapply mpl_close. simpl; left; reflexivity.   (* `}` at node 3 *)
  Qed.

  (* No PPar continuation exists from node 1 in this DAG (node 1 offers only
     `:`, never `|` or `}`). *)
  Lemma mw_no_ppar_loop_from_1 :
    forall m, ~ ppar_loop mw_edges 0 1 mw_elem 1 m.
  Proof.
    intros m H. inversion H; subst.
    - simpl in *. intuition congruence.   (* pl_close: In (0,_) [(3,2)] *)
    - simpl in *. intuition congruence.   (* pl_sep:   In (1,_) [(3,2)] *)
  Qed.

  (* The PPar branch REJECTS `{1:2}` (disambiguation: no spurious PPar accept).
     ppar_run discharges out_edges, l_close, l_sep_par, elem_spell — here 0, 1. *)
  Theorem map_witness_ppar_rejects :
    forall m, ~ ppar_run mw_edges 0 1 mw_elem 0 m.
  Proof.
    intros m H. inversion H; subst.
    - simpl in *. intuition congruence.   (* pr_empty: In (0,_) (mw_edges 0)=[] *)
    - destruct H0 as [[_ He] | [Hc _]].
      + subst e. eapply mw_no_ppar_loop_from_1; eassumption.
      + discriminate Hc.                   (* mw_elem 0 _ second disjunct: 0=2 *)
  Qed.

End MapWitness.

(* ── `{1|2}`: a PPar, NOT a Map. After the element `1` (elem 0→1) the only
      edge at node 1 is `|` (sep_par, label 1) → 2; element `2` (elem 2→3);
      close `}` (label 0) → 4. ── *)
Section ParWitness.

  Definition pw_edges (n : nat) : list (nat * nat) :=
    match n with
    | 1 => [(1, 2)]          (* `|` → node 2 *)
    | 3 => [(0, 4)]          (* `}` → node 4 *)
    | _ => []
    end.
  Definition pw_elem (n m : nat) : Prop :=
    (n = 0 /\ m = 1) \/ (n = 2 /\ m = 3).

  (* The PPar branch accepts `{1|2}`. *)
  Theorem par_witness_ppar_accepts :
    ppar_run pw_edges 0 1 pw_elem 0 4.
  Proof.
    eapply pr_nonempty.
    - left; split; reflexivity.          (* first elem 0→1 *)
    - eapply pl_sep.
      + simpl; left; reflexivity.         (* `|` edge at node 1 *)
      + right; split; reflexivity.        (* second elem 2→3 *)
      + eapply pl_close. simpl; left; reflexivity.  (* `}` at node 3 *)
  Qed.

  (* The Map branch REJECTS `{1|2}` (disambiguation: no spurious Map accept).
     After the key `1` (elem 0→1) node 1 offers `|`, never `:`. *)
  Theorem par_witness_map_rejects :
    forall m, ~ map_run pw_edges 0 2 3 pw_elem 0 m.
  Proof.
    intros m H. inversion H; subst.
    - simpl in *. intuition congruence.   (* mr_empty: In (0,_) (pw_edges 0)=[] *)
    - destruct H0 as [[_ Hk] | [Hc _]].
      + subst kend. simpl in *. intuition congruence. (* `:` at node 1: In (3,_) [(1,2)] *)
      + discriminate Hc.                   (* pw_elem 0 _ second disjunct: 0=2 *)
  Qed.

End ParWitness.

(* ── `{}`: accepts as BOTH an empty bag and an empty map; node 0 offers only
      the close `}` (label 0) → 1. The weight tie-break (T4) selects PPar. ── *)
Section EmptyWitness.

  Definition ew_edges (n : nat) : list (nat * nat) :=
    match n with
    | 0 => [(0, 1)]          (* `}` → node 1 *)
    | _ => []
    end.
  Definition ew_elem (_ _ : nat) : Prop := False.

  Theorem empty_witness_ppar_accepts :
    ppar_run ew_edges 0 1 ew_elem 0 1.
  Proof.
    eapply pr_empty. simpl; left; reflexivity.
  Qed.

  Theorem empty_witness_map_accepts :
    map_run ew_edges 0 2 3 ew_elem 0 1.
  Proof.
    eapply mr_empty. simpl; left; reflexivity.
  Qed.

  (* Both branches accept `{}`; T4 (empty_collection_tie_breaks_to_primary)
     resolves the tie to the PPar branch by the 0.0 < 0.025 weight ordering. *)

End EmptyWitness.

(* ═════════════════ Assumption audit — must all print
   "Closed under the global context" ═════════════════ *)
Print Assumptions prefix_fork_no_loss.
Print Assumptions prefix_fork_no_spurious_accept.
Print Assumptions prefix_fork_mutually_exclusive_past_first_sep.
Print Assumptions empty_collection_tie_breaks_to_primary.
Print Assumptions empty_primary_strictly_cheaper.
Print Assumptions len1_fastpath_byte_identical.
Print Assumptions fork_run_when_true_eq_collision.
Print Assumptions prefix_fork_frontier_delta_le_one.
Print Assumptions prefix_fork_delta_zero_in_fastpath.
Print Assumptions prefix_fork_delta_one_on_collision.
Print Assumptions bp_tier_infix_lt_projection.
Print Assumptions map_witness_map_accepts.
Print Assumptions map_witness_ppar_rejects.
Print Assumptions par_witness_ppar_accepts.
Print Assumptions par_witness_map_rejects.
Print Assumptions empty_witness_ppar_accepts.
Print Assumptions empty_witness_map_accepts.
