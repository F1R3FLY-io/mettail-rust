(*
 * PureCommitFoldIntegrityAccept: S1-FACTORING F5-1 FV-3b(b) re-proof —
 * pure-arm commit-fold integrity under ACCEPT-LEAF commit coordinates
 * (the sibling-leaf hoist), over the SAME machine as the shipped
 * PureCommitFoldIntegrity (imported verbatim, never restated):
 *
 *   (a″) ReplacePreservesUW UNCHANGED — the commit transition at the
 *        hoisted accept edge is the very same PCommit constructor: the
 *        identity on (u, w) and the interning store
 *        (`accept_commit_preserves_uw` delegates to the shipped theorem —
 *        zero new proof obligations, which IS the claim: the accept fork
 *        emits only F1-emitted constructs);
 *   (b″) CommitPrecedesFinalPop STILL HOLDS when the commit happens at the
 *        hoisted accept edge. The key observation, made explicit here: the
 *        shipped machine's table booleans are INDEPENDENT — a node may
 *        carry BOTH a spine successor AND commit edges (`accept_fork_at`),
 *        which is exactly the F5-1 accept fork (walker: the arm consuming
 *        the accept's edge item forks into the spine-continue branch and
 *        the member's typed commit branch, both fork-delivered,
 *        wpda_walker.rs ReplaceAndPush fork arm @19583 / pure dispatch
 *        @31747). The shipped proofs never assumed commit-XOR-continue at
 *        a node, so:
 *          · both successors EXIST at an accept fork
 *            (`accept_fork_both_branches`);
 *          · any spine→Pop path — through EITHER branch — passes EXACTLY
 *            ONE commit (`accept_fork_commit_precedes_final_pop`, the
 *            commit lineage composition `accept_path_exactly_one_commit`,
 *            the per-lineage split `accept_fork_lineage_split`);
 *          · pop_key_below_base carries via member-rule stability + wf
 *            commits < SPINE_RULE_BASE, with the wf premise now DERIVED
 *            from the FV-1′ forest bijection (`forest_table_wf`: a table
 *            whose commits target only forest leaf rules is wf whenever
 *            the members' rule indices are below the synthetic spine id
 *            space — factoring.rs A9);
 *          · the ALL-ACCEPTS degenerate node (every branch a commit — the
 *            all-twins forest) only strengthens the law: every successor
 *            leaves spine-land (`all_accepts_every_branch_commits`);
 *   (c″-instance) the accept fork's branch weights are lex_one() — the
 *        pre-commit segment stays all-identity-like, so the shipped
 *        prefix-wash law covers accept lineages with no modification
 *        (`accept_precommit_segment_washes`).
 *
 * The concrete INSTANCE is the rholang InputBind@ table (plan §2.2 node
 * ids, matching flatten_forest's preorder: pre-root 1, root 2, L"<-" 3,
 * P(Name)-interior 4; the accept fork at arm 3):
 *   spine:  1→2 (P(Proc) operand), 2→3 (L"<-"), 3→4 (P(Name), the
 *           spine-continue branch);
 *   commit: 2 ⇒ (r6, 3) on L"<="; 3 ⇒ (r3, 4) on P(Name) — THE ACCEPT,
 *           landing DIRECTLY on r3's final-pos Pop arm (resume 4 =
 *           total + 1, FV-1′ (d′)); 4 ⇒ (r2, 5) on L"!";
 *   member: r6 (6,3)→(6,4) final; r2 (2,5)→…→(2,9) final; r3 final AT
 *           (3,4) with NO outgoing member edge (the TRUE-accept receipt).
 * All three lineages are driven end-to-end as explicit `steps`
 * derivations, each passing exactly ONE commit with its packing keyed by
 * the real member rule.
 *
 * `Print Assumptions` on every theorem must report
 * "Closed under the global context" (zero admission / axiom / parameter;
 * Rocq 9.1).
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Sorting.Permutation.
From PrattailWpdaRuntime Require Import TrieLeafBijection.
From PrattailWpdaRuntime Require Import TrieLeafBijectionAccept.
From PrattailWpdaRuntime Require Import PureCommitFoldIntegrity.
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════
   THE ACCEPT FORK in the machine: a spine node carrying BOTH a spine
   successor (the continue branch) and a commit edge (the accept member's
   typed commit branch) — expressible in the SHIPPED table model with no
   new transition species.
   ═══════════════════════════════════════════════════════════════════════ *)

Definition accept_fork_at (T : table) (n : nat) : Prop :=
  (exists n', spine_edge T n n' = true)
  /\ (exists r p, commit_edge T n r p = true).

(* Both branches of the accept fork EXIST as machine steps from the same
   configuration — the fork is nondeterministic branching, not a new rule. *)
Theorem accept_fork_both_branches :
  forall T u wl st n n' r p,
    spine_edge T n n' = true ->
    commit_edge T n r p = true ->
    pstep T (MkCfg u wl (CSpine n) st)
            (MkCfg u (wl ++ [w_one]) (CSpine n') st)
    /\ pstep T (MkCfg u wl (CSpine n) st)
               (MkCfg u wl (CMember r p) st).
Proof.
  intros T u wl st n n' r p HS HC.
  split.
  - pose proof (PSpineChain T u wl st n n' [] HS) as H.
    rewrite app_nil_r in H. exact H.
  - exact (PCommit T u wl st n r p HC).
Qed.

(* ── (a″) ReplacePreservesUW UNCHANGED at the accept fork: the commit
      branch is the shipped PCommit — identity on (u, w, store). The proof
      DELEGATES to the shipped theorem: the accept fork adds no new
      obligation. ── *)
Theorem accept_commit_preserves_uw :
  forall T u wl st n c',
    accept_fork_at T n ->
    pstep T (MkCfg u wl (CSpine n) st) c' ->
    (exists r p, g_coord c' = CMember r p) ->
    g_u c' = u /\ g_w c' = wl /\ g_store c' = st.
Proof.
  intros T u wl st n c' _ Hstep Hm.
  exact (replace_preserves_uw T u wl st n c' Hstep Hm).
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (b″) EXACTLY-ONE-COMMIT at the hoisted accept edge.
   ═══════════════════════════════════════════════════════════════════════ *)

(* The shipped law restated FROM an accept-fork node: any path from the
   fork to a Pop passes exactly one commit — through EITHER branch. The
   shipped proof never assumed a node lacks one of the two edge kinds; this
   restatement pins that the accept fork introduces no new case. *)
Theorem accept_fork_commit_precedes_final_pop :
  forall T n u wl st c' k rk pw,
    accept_fork_at T n ->
    steps T (MkCfg u wl (CSpine n) st) c' k ->
    packing_of T c' = Some (rk, pw) ->
    k = 1.
Proof.
  intros T n u wl st c' k rk pw _ H Hpack.
  eapply commit_precedes_final_pop; [exact H | reflexivity | exact Hpack].
Qed.

(* The COMMIT LINEAGE: after the accept commit, member-land admits no
   further commit (member coordinates never step back to spine). *)
Theorem no_commit_after_accept_commit :
  forall T c c' k r p,
    g_coord c = CMember r p ->
    steps T c c' k ->
    k = 0.
Proof.
  intros T c c' k r p Hc H.
  eapply steps_member_no_commits; [exact H |].
  rewrite Hc. reflexivity.
Qed.

(* Member-rule STABILITY across the accept lineage: the packing key read at
   the Pop is EXACTLY the committed member rule (the commit branch's frame
   carries the member id from birth — H9's branch-local form). *)
Theorem accept_commit_pop_key_exact :
  forall T c c' k r p rk pw,
    wf_member_rules T ->
    g_coord c = CMember r p ->
    steps T c c' k ->
    packing_of T c' = Some (rk, pw) ->
    rk = r.
Proof.
  intros T c c' k r p rk pw Hwfm Hc H Hpack.
  destruct (member_rule_stable T c c' k r p Hwfm H Hc) as [p' Hc'].
  unfold packing_of in Hpack.
  rewrite Hc' in Hpack.
  destruct (member_final T (r, p')) eqn:Ef; [| discriminate].
  inversion Hpack; subst. reflexivity.
Qed.

(* COMPOSITION: prefixing the accept commit onto its member lineage yields
   a spine→Pop path with EXACTLY ONE commit — the (b″) law in constructive
   form. *)
Theorem accept_path_exactly_one_commit :
  forall T u wl st n r p c1 k rk pw,
    commit_edge T n r p = true ->
    steps T (MkCfg u wl (CMember r p) st) c1 k ->
    packing_of T c1 = Some (rk, pw) ->
    k = 0
    /\ steps T (MkCfg u wl (CSpine n) st) c1 1.
Proof.
  intros T u wl st n r p c1 k rk pw HC Hsteps Hpack.
  assert (Hk : k = 0).
  { eapply steps_member_no_commits; [exact Hsteps | reflexivity]. }
  subst k.
  split; [reflexivity |].
  eapply StepsCommit.
  - exact (PCommit T u wl st n r p HC).
  - reflexivity.
  - reflexivity.
  - exact Hsteps.
Qed.

(* THE PER-LINEAGE SPLIT: at an accept fork, the commit lineage carries its
   ONE commit already behind it (zero ahead, key = the committed member,
   below the spine id space), while the spine-continue lineage still has
   its single commit AHEAD — and BOTH packing keys are real member rules. *)
Theorem accept_fork_lineage_split :
  forall T u wl st n n' r p c1 c2 k1 k2 rk1 rk2 pw1 pw2,
    wf_table T ->
    wf_member_rules T ->
    spine_edge T n n' = true ->
    commit_edge T n r p = true ->
    steps T (MkCfg u wl (CMember r p) st) c1 k1 ->
    packing_of T c1 = Some (rk1, pw1) ->
    steps T (MkCfg u (wl ++ [w_one]) (CSpine n') st) c2 k2 ->
    packing_of T c2 = Some (rk2, pw2) ->
    k1 = 0 /\ k2 = 1
    /\ rk1 = r
    /\ rk1 < SPINE_RULE_BASE
    /\ rk2 < SPINE_RULE_BASE.
Proof.
  intros T u wl st n n' r p c1 c2 k1 k2 rk1 rk2 pw1 pw2
    Hwf Hwfm HS HC H1 HP1 H2 HP2.
  assert (Hk1 : k1 = 0).
  { eapply steps_member_no_commits; [exact H1 | reflexivity]. }
  assert (Hrk1 : rk1 = r).
  { (* FAILED STRATEGY (do not re-attempt): `eapply accept_commit_pop_key_
       exact; [exact Hwfm | reflexivity | exact H1 | exact HP1]` — the
       coordinate-equation subgoal `g_coord ?c = CMember r ?p` is presented
       BEFORE H1 fixes ?c, so reflexivity faces a projection stuck on an
       evar. The fully-applied term fixes every argument up front. *)
    exact (accept_commit_pop_key_exact T
             (MkCfg u wl (CMember r p) st) c1 k1 r p rk1 pw1
             Hwfm eq_refl H1 HP1). }
  split; [exact Hk1 | split; [| split; [exact Hrk1 | split]]].
  - eapply commit_precedes_final_pop; [exact H2 | reflexivity | exact HP2].
  - subst rk1. exact (Hwf n r p HC).
  - eapply pop_key_below_base;
      [exact Hwf | exact Hwfm | exact H2 | reflexivity | exact HP2].
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   wf FROM THE FV-1′ FOREST: a table whose commits target only the built
   forest's leaf rules is well-formed whenever the bucket members' rule
   indices sit below the synthetic spine id space (factoring.rs A9 asserts
   SPINE_RULE_BASE = 0xF800 with all member indices far below) — the
   pop_key_below_base premise DERIVED from the FV-1′ bijection.
   ═══════════════════════════════════════════════════════════════════════ *)

Definition table_commits_in_forest (T : table) (f : list tree) : Prop :=
  forall n r p, commit_edge T n r p = true -> In r (forest_leaf_rules f).

Theorem forest_table_wf :
  forall T fuel depth edge ms f,
    build_node_a fuel depth edge ms = Some f ->
    (forall m, In m ms -> m_rule m < SPINE_RULE_BASE) ->
    table_commits_in_forest T f ->
    wf_table T.
Proof.
  intros T fuel depth edge ms f HB Hbound Hcom.
  unfold wf_table.
  intros n r p HC.
  pose proof (Hcom n r p HC) as Hin.
  pose proof (forest_leaf_bijection fuel depth edge ms f HB) as HP.
  apply (Permutation_in r HP) in Hin.
  unfold rules_of in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [m [Hr HinM]].
  subst r.
  exact (Hbound m HinM).
Qed.

Corollary forest_pop_key_below_base :
  forall T fuel depth edge ms f c c' k rk pw,
    build_node_a fuel depth edge ms = Some f ->
    (forall m, In m ms -> m_rule m < SPINE_RULE_BASE) ->
    table_commits_in_forest T f ->
    wf_member_rules T ->
    steps T c c' k ->
    is_spine (g_coord c) = true ->
    packing_of T c' = Some (rk, pw) ->
    rk < SPINE_RULE_BASE.
Proof.
  intros T fuel depth edge ms f c c' k rk pw HB Hbound Hcom Hwfm H Hs Hpack.
  eapply pop_key_below_base;
    [eapply forest_table_wf; [exact HB | exact Hbound | exact Hcom]
    | exact Hwfm | exact H | exact Hs | exact Hpack].
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   THE ALL-ACCEPTS DEGENERATE NODE (an all-twins forest: every branch is a
   commit, no spine successor) — every machine successor leaves spine-land,
   so the one-commit law holds a fortiori.
   ═══════════════════════════════════════════════════════════════════════ *)

Definition all_accepts_node (T : table) (n : nat) : Prop :=
  (forall n', spine_edge T n n' = false)
  /\ (exists r p, commit_edge T n r p = true).

Theorem all_accepts_every_branch_commits :
  forall T n c c',
    all_accepts_node T n ->
    g_coord c = CSpine n ->
    pstep T c c' ->
    is_spine (g_coord c') = false.
Proof.
  intros T n c c' [Hnos _] Hc Hstep.
  inversion Hstep; subst; cbn in *.
  - inversion Hc; subst. rewrite Hnos in H. discriminate.
  - reflexivity.
  - discriminate Hc.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (c″-instance) THE WASH at the accept fork: both fork branches carry
   lex_one() (factoring.rs child branch weights — F1 receipts extended by
   F5-1's fork), so the pre-commit segment is all-identity-like and the
   shipped prefix-wash law covers accept lineages with NO modification.
   ═══════════════════════════════════════════════════════════════════════ *)

Theorem accept_precommit_segment_washes :
  forall k post,
    post <> [] ->
    fold_left wtimes (repeat w_one k ++ post) w_one
    = fold_left wtimes post w_one.
Proof.
  intros k post Hne.
  apply fold_prefix_washes; [| exact Hne].
  intros x Hx.
  apply repeat_spec in Hx. subst x. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   INSTANCE — the rholang InputBind@ table (plan §2.2 / flatten_forest
   preorder ids; member rules 2, 3, 6 = the FV-1′ ib forest's leaves).
   ═══════════════════════════════════════════════════════════════════════ *)

Definition ib_spine_edge (a b : nat) : bool :=
  ((a =? 1) && (b =? 2))
  || ((a =? 2) && (b =? 3))
  || ((a =? 3) && (b =? 4)).

Definition ib_commit_edge (n r p : nat) : bool :=
  ((n =? 2) && (r =? 6) && (p =? 3))      (* L"<=" ⇒ r6, resume 3 *)
  || ((n =? 3) && (r =? 3) && (p =? 4))   (* THE ACCEPT: P(Name) ⇒ r3,
                                             resume 4 = its final-pos arm *)
  || ((n =? 4) && (r =? 2) && (p =? 5)).  (* L"!" ⇒ r2, resume 5 *)

Definition ib_member_edge (a b : nat * nat) : bool :=
  match a, b with
  | (r, p), (r', p') =>
      ((r =? 6) && (p =? 3) && (r' =? 6) && (p' =? 4))
      || ((r =? 2) && (p =? 5) && (r' =? 2) && (p' =? 6))
      || ((r =? 2) && (p =? 6) && (r' =? 2) && (p' =? 7))
      || ((r =? 2) && (p =? 7) && (r' =? 2) && (p' =? 8))
      || ((r =? 2) && (p =? 8) && (r' =? 2) && (p' =? 9))
  end.

Definition ib_member_final (a : nat * nat) : bool :=
  match a with
  | (r, p) =>
      ((r =? 3) && (p =? 4))
      || ((r =? 6) && (p =? 4))
      || ((r =? 2) && (p =? 9))
  end.

Definition ib_table : table :=
  MkTable ib_spine_edge ib_commit_edge ib_member_edge ib_member_final.

(* The table's commits are wf DIRECTLY (every committed rule is a real
   member rule, far below the 0xF800 spine id space).
   FAILED STRATEGY (do not re-attempt): `unfold SPINE_RULE_BASE; lia` —
   the literal 63488 elaborates to an UNREDUCED `Init.Nat.of_num_uint`
   decimal coercion, which lia treats as an uninterpreted atom ("Cannot
   find witness"). The shipped PureCommitFoldIntegrity never hits this
   because its theorems keep the bound hypothetical; concrete instances
   must take the computational route `apply Nat.ltb_lt; vm_compute;
   reflexivity` (used below and in ib_table_wf_via_forest). *)
Lemma ib_table_wf : wf_table ib_table.
Proof.
  unfold wf_table.
  intros n r p H.
  unfold ib_table in H; cbn in H; unfold ib_commit_edge in H.
  apply orb_true_iff in H; destruct H as [H | H];
    [apply orb_true_iff in H; destruct H as [H | H] |].
  - apply andb_true_iff in H; destruct H as [H Hp].
    apply andb_true_iff in H; destruct H as [Hn Hr].
    apply Nat.eqb_eq in Hr; subst r.
    apply Nat.ltb_lt. vm_compute. reflexivity.
  - apply andb_true_iff in H; destruct H as [H Hp].
    apply andb_true_iff in H; destruct H as [Hn Hr].
    apply Nat.eqb_eq in Hr; subst r.
    apply Nat.ltb_lt. vm_compute. reflexivity.
  - apply andb_true_iff in H; destruct H as [H Hp].
    apply andb_true_iff in H; destruct H as [Hn Hr].
    apply Nat.eqb_eq in Hr; subst r.
    apply Nat.ltb_lt. vm_compute. reflexivity.
Qed.

Lemma ib_table_wf_member_rules : wf_member_rules ib_table.
Proof.
  unfold wf_member_rules.
  intros r p r' p' H.
  unfold ib_table in H; cbn in H; unfold ib_member_edge in H.
  repeat match goal with
         | HH : (_ || _)%bool = true |- _ =>
             apply orb_true_iff in HH; destruct HH as [HH | HH]
         end.
  all: repeat match goal with
              | HH : (_ && _)%bool = true |- _ =>
                  apply andb_true_iff in HH;
                  let Hy := fresh "Hy" in destruct HH as [HH Hy]
              end.
  all: repeat match goal with
              | HH : (_ =? _) = true |- _ => apply Nat.eqb_eq in HH
              end.
  all: subst; reflexivity.
Qed.

(* The wf premise ALSO derivable from the FV-1′ forest (the bijection-based
   route): the table's commits target exactly the ib forest's leaf rules. *)
Theorem ib_table_commits_in_forest :
  table_commits_in_forest ib_table ib_forest.
Proof.
  unfold table_commits_in_forest.
  intros n r p H.
  unfold ib_table in H; cbn in H; unfold ib_commit_edge in H.
  rewrite rholang_inputbind_leaves.
  apply orb_true_iff in H; destruct H as [H | H];
    [apply orb_true_iff in H; destruct H as [H | H] |].
  - apply andb_true_iff in H; destruct H as [H Hp].
    apply andb_true_iff in H; destruct H as [Hn Hr].
    apply Nat.eqb_eq in Hr; subst r.
    right; right; left; reflexivity.
  - apply andb_true_iff in H; destruct H as [H Hp].
    apply andb_true_iff in H; destruct H as [Hn Hr].
    apply Nat.eqb_eq in Hr; subst r.
    right; left; reflexivity.
  - apply andb_true_iff in H; destruct H as [H Hp].
    apply andb_true_iff in H; destruct H as [Hn Hr].
    apply Nat.eqb_eq in Hr; subst r.
    left; reflexivity.
Qed.

Theorem ib_table_wf_via_forest : wf_table ib_table.
Proof.
  eapply forest_table_wf.
  - exact rholang_inputbind_forest.
  - intros m Hin.
    destruct Hin as [Hm | [Hm | [Hm | []]]]; subst m;
      apply Nat.ltb_lt; vm_compute; reflexivity.
  - exact ib_table_commits_in_forest.
Qed.

(* Node 3 IS the accept fork: the spine-continue edge to node 4 AND the r3
   commit coexist on the same consumed P(Name) item. *)
Theorem ib_accept_fork : accept_fork_at ib_table 3.
Proof.
  split.
  - exists 4. reflexivity.
  - exists 3, 4. reflexivity.
Qed.

(* The TRUE-accept receipt: the r3 commit coordinate (3, 4) is ITSELF a
   final-pos Pop coordinate, with NO outgoing member edge — the accept
   lands directly on the member's own completion machinery (FV-1′ (d′)). *)
Theorem ib_true_accept_lands_on_final_pop :
  member_final ib_table (3, 4) = true
  /\ (forall b, member_edge ib_table (3, 4) b = false).
Proof.
  split.
  - reflexivity.
  - intros [r' p']. reflexivity.
Qed.

(* ── The three end-to-end lineage receipts (explicit `steps` derivations;
      st stays [] with fresh := [] throughout; every spine arm folds
      lex_one = w_one). Each path passes EXACTLY ONE commit and its packing
      is keyed by the real member rule. ── *)

(* The ACCEPT lineage (plain `for(@y <- z){…}`): 1 →chain→ 2 →chain→ 3
   →COMMIT r3→ (3,4), which IS final — zero member steps, packing key 3. *)
Theorem ib_accept_lineage_receipt :
  steps ib_table (MkCfg 0 [] (CSpine 1) [])
                 (MkCfg 0 [w_one; w_one] (CMember 3 4) []) 1
  /\ packing_of ib_table (MkCfg 0 [w_one; w_one] (CMember 3 4) [])
     = Some (3, w_one).
Proof.
  split.
  - eapply StepsChain;
      [exact (PSpineChain ib_table 0 [] [] 1 2 [] eq_refl)
      | reflexivity | reflexivity |].
    eapply StepsChain;
      [exact (PSpineChain ib_table 0 [w_one] [] 2 3 [] eq_refl)
      | reflexivity | reflexivity |].
    eapply StepsCommit;
      [exact (PCommit ib_table 0 [w_one; w_one] [] 3 3 4 eq_refl)
      | reflexivity | reflexivity |].
    apply StepsRefl.
  - vm_compute. reflexivity.
Qed.

(* The PERSISTENT lineage (`for(@y <= z){…}`): 1 →chain→ 2 →COMMIT r6→
   (6,3) →member→ (6,4) final — one commit, packing key 6. *)
Theorem ib_persistent_lineage_receipt :
  steps ib_table (MkCfg 0 [] (CSpine 1) [])
                 (MkCfg 0 [w_one; w_one] (CMember 6 4) []) 1
  /\ packing_of ib_table (MkCfg 0 [w_one; w_one] (CMember 6 4) [])
     = Some (6, w_one).
Proof.
  split.
  - eapply StepsChain;
      [exact (PSpineChain ib_table 0 [] [] 1 2 [] eq_refl)
      | reflexivity | reflexivity |].
    eapply StepsCommit;
      [exact (PCommit ib_table 0 [w_one] [] 2 6 3 eq_refl)
      | reflexivity | reflexivity |].
    eapply StepsMember;
      [exact (PMemberStep ib_table 0 [w_one] [] 6 3 6 4 w_one [] eq_refl)
      | reflexivity |].
    apply StepsRefl.
  - vm_compute. reflexivity.
Qed.

(* The QUERY lineage (`for(@y <- z!?(…)){…}`): the spine-continue branch of
   THE ACCEPT FORK — 1 →chain→ 2 →chain→ 3 →chain→ 4 →COMMIT r2→ (2,5)
   →member×4→ (2,9) final — still exactly one commit, packing key 2. *)
Theorem ib_query_lineage_receipt :
  steps ib_table (MkCfg 0 [] (CSpine 1) [])
        (MkCfg 0 [w_one; w_one; w_one; w_one; w_one; w_one; w_one]
               (CMember 2 9) []) 1
  /\ packing_of ib_table
       (MkCfg 0 [w_one; w_one; w_one; w_one; w_one; w_one; w_one]
              (CMember 2 9) [])
     = Some (2, w_one).
Proof.
  split.
  - eapply StepsChain;
      [exact (PSpineChain ib_table 0 [] [] 1 2 [] eq_refl)
      | reflexivity | reflexivity |].
    eapply StepsChain;
      [exact (PSpineChain ib_table 0 [w_one] [] 2 3 [] eq_refl)
      | reflexivity | reflexivity |].
    eapply StepsChain;
      [exact (PSpineChain ib_table 0 [w_one; w_one] [] 3 4 [] eq_refl)
      | reflexivity | reflexivity |].
    eapply StepsCommit;
      [exact (PCommit ib_table 0 [w_one; w_one; w_one] [] 4 2 5 eq_refl)
      | reflexivity | reflexivity |].
    eapply StepsMember;
      [exact (PMemberStep ib_table 0 [w_one; w_one; w_one] []
                2 5 2 6 w_one [] eq_refl)
      | reflexivity |].
    eapply StepsMember;
      [exact (PMemberStep ib_table 0 [w_one; w_one; w_one; w_one] []
                2 6 2 7 w_one [] eq_refl)
      | reflexivity |].
    eapply StepsMember;
      [exact (PMemberStep ib_table 0 [w_one; w_one; w_one; w_one; w_one] []
                2 7 2 8 w_one [] eq_refl)
      | reflexivity |].
    eapply StepsMember;
      [exact (PMemberStep ib_table 0
                [w_one; w_one; w_one; w_one; w_one; w_one] []
                2 8 2 9 w_one [] eq_refl)
      | reflexivity |].
    apply StepsRefl.
  - vm_compute. reflexivity.
Qed.

(* Both fork branches EXIST at the instance's accept node. *)
Theorem ib_accept_fork_both_branches :
  pstep ib_table (MkCfg 0 [w_one; w_one] (CSpine 3) [])
                 (MkCfg 0 ([w_one; w_one] ++ [w_one]) (CSpine 4) [])
  /\ pstep ib_table (MkCfg 0 [w_one; w_one] (CSpine 3) [])
                    (MkCfg 0 [w_one; w_one] (CMember 3 4) []).
Proof.
  exact (accept_fork_both_branches ib_table 0 [w_one; w_one] [] 3 4 3 4
           eq_refl eq_refl).
Qed.

(* The GENERIC one-commit + key-bound law instantiated at the ib table:
   every spine→Pop path — accept fork included — has exactly one commit,
   keyed below the spine id space. *)
Theorem ib_any_spine_path_one_commit :
  forall c c' k rk pw,
    steps ib_table c c' k ->
    is_spine (g_coord c) = true ->
    packing_of ib_table c' = Some (rk, pw) ->
    k = 1 /\ rk < SPINE_RULE_BASE.
Proof.
  intros c c' k rk pw H Hs Hpack.
  split.
  - eapply commit_precedes_final_pop; [exact H | exact Hs | exact Hpack].
  - eapply pop_key_below_base;
      [exact ib_table_wf | exact ib_table_wf_member_rules
      | exact H | exact Hs | exact Hpack].
Qed.

(* The accept lineage's pre-commit fold is the identity — its two spine
   arms are lex_one, so the packing weight is post-commit-determined
   exactly as OFF (the shipped wash law, instantiated). *)
Theorem ib_accept_precommit_washes :
  forall post,
    post <> [] ->
    fold_left wtimes ([w_one; w_one] ++ post) w_one
    = fold_left wtimes post w_one.
Proof.
  intros post Hne.
  exact (accept_precommit_segment_washes 2 post Hne).
Qed.

(* ── Assumption audit — every line must print "Closed under the global
      context". ── *)
Print Assumptions accept_fork_both_branches.
Print Assumptions accept_commit_preserves_uw.
Print Assumptions accept_fork_commit_precedes_final_pop.
Print Assumptions no_commit_after_accept_commit.
Print Assumptions accept_commit_pop_key_exact.
Print Assumptions accept_path_exactly_one_commit.
Print Assumptions accept_fork_lineage_split.
Print Assumptions forest_table_wf.
Print Assumptions forest_pop_key_below_base.
Print Assumptions all_accepts_every_branch_commits.
Print Assumptions accept_precommit_segment_washes.
Print Assumptions ib_table_wf.
Print Assumptions ib_table_wf_member_rules.
Print Assumptions ib_table_commits_in_forest.
Print Assumptions ib_table_wf_via_forest.
Print Assumptions ib_accept_fork.
Print Assumptions ib_true_accept_lands_on_final_pop.
Print Assumptions ib_accept_lineage_receipt.
Print Assumptions ib_persistent_lineage_receipt.
Print Assumptions ib_query_lineage_receipt.
Print Assumptions ib_accept_fork_both_branches.
Print Assumptions ib_any_spine_path_one_commit.
Print Assumptions ib_accept_precommit_washes.
