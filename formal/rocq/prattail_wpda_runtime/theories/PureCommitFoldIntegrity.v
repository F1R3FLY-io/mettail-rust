(*
 * PureCommitFoldIntegrity: S1-FACTORING FV-3b (pure-arm commit-fold
 * integrity) — the descriptor-pure canonical-GLL side of the F3 election
 * argument, in the PureDescriptorSpaceBound/PurePackingPreservation
 * small-step house style. Three theorem families (F3 plan §3, delta A-2):
 *
 *   (a) ReplacePreservesUW + NO-CARRIER-WRITE — the commit transition
 *       (marker Replace) is the IDENTITY on (u, w) and the interning
 *       store, and NO transition of the machine writes an existing
 *       carrier (the store is append-only) — the A-2 soundness boundary
 *       as a theorem: the refuted "restamp the shared trigger carrier"
 *       fallback would REQUIRE a store-mutating transition this model
 *       provably lacks. Walker receipts: the pure Replace arm discards
 *       action weights (`weight: _` @ wpda_walker.rs:30499; Push twin
 *       @30451), commit-Replace keeps `u` and `w` (the S1 delta §B(a));
 *       SPPF interning is add-only (intern_* family).
 *
 *   (b) CommitPrecedesFinalPop — over the emitted spine table (FV-1/2's
 *       shape: spine coordinates step to spine coordinates or COMMIT to
 *       member coordinates; member coordinates never step back), every
 *       path from a spine descent to a Pop passes EXACTLY ONE commit,
 *       hence the reduce packing key read at the Pop is a MEMBER id
 *       (< SPINE_RULE_BASE) — the live H9 asserts (pure-reduce packing
 *       intern @~28216 twin, realize @~10930, emit_fire_action @38136+)
 *       as a theorem.
 *
 *   (c) PackingWeightMemberDetermined — the reduce packing weight is a
 *       function of POST-COMMIT data only. Weight model = the three
 *       integer tiebreaks of rigail's LexicographicWeight under the §1.1
 *       wash-out law (lex_weight.rs: `is_one` tests primary ONLY @534-537
 *       ⇒ every zero-cost weight is identity-like; `times` @498-527
 *       right-projects past an identity-like LEFT operand and
 *       left-projects fields at real cost). SCOPE (red-team F3 amendment):
 *       open_len is EXCLUDED — it is MAX-projected through the identity
 *       short-circuit (sticky, never washed) and is S1-neutral separately
 *       (every S1 surface carries open_len 0 or the identical AV5 @-len
 *       in both stances); the wash law here covers the INTEGER tiebreaks
 *       (primary/src/rule) exactly as the plan §1.1 states it.
 *       Consequence: the OFF pre-commit segment (per-member trigger stamp
 *       lex_w(0,cat,r) + lex_one interior arms) and the ON pre-commit
 *       segment (spine trigger stamp lex_w(0,cat,min-member) + lex_one
 *       spine arms) are BOTH all-identity-like, so the fold washes both
 *       to the SAME post-commit-determined value — per-reading
 *       stance-invariance of the packing weight.
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
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════
   (c) THE WEIGHT MODEL — rigail's zero-cost wash-out law.
   ═══════════════════════════════════════════════════════════════════════ *)

(* (cost, stamp): cost mirrors the tropical primary; stamp mirrors the
   (src_idx, rule_idx) identity fields as one abstract tag. *)
Record w : Type := MkW {
  w_cost  : nat;
  w_stamp : option nat
}.

Definition w_one : w := MkW 0 None.

(* rigail `is_one` tests ONLY the primary (lex_weight.rs @534-537): every
   zero-cost weight is identity-LIKE regardless of its stamp. *)
Definition idlike (x : w) : bool := w_cost x =? 0.

(* rigail `times` (@498-527): identity-like LEFT operand ⇒ the RIGHT
   operand's fields wholesale; identity-like RIGHT (real-cost left) ⇒ the
   LEFT unchanged; two real costs ⇒ cost-add with LEFT-projected stamp. *)
Definition wtimes (a b : w) : w :=
  if idlike a then b
  else if idlike b then a
  else MkW (w_cost a + w_cost b) (w_stamp a).

(* ── The §1.1 wash-out law: a zero-cost stamp survives exactly ONE step —
      the very next composition takes the RIGHT operand wholesale. ── *)
Theorem zero_cost_stamp_washes :
  forall s x, wtimes (MkW 0 (Some s)) x = x.
Proof.
  intros s x. reflexivity.
Qed.

Theorem wtimes_one_l : forall x, wtimes w_one x = x.
Proof. reflexivity. Qed.

Lemma idlike_wtimes_l :
  forall a b, idlike a = true -> wtimes a b = b.
Proof.
  intros a b Ha. unfold wtimes. rewrite Ha. reflexivity.
Qed.

(* Fold with any identity-like seed equals fold from w_one, provided the
   segment is NONEMPTY (the final-pos Pop weight always exists, so packing
   folds are never empty past the commit). *)
Lemma fold_idlike_seed :
  forall post s1 s2,
    post <> [] ->
    idlike s1 = true ->
    idlike s2 = true ->
    fold_left wtimes post s1 = fold_left wtimes post s2.
Proof.
  intros post s1 s2 Hne Hs1 Hs2.
  destruct post as [| p rest]; [congruence |].
  simpl.
  rewrite (idlike_wtimes_l s1 p Hs1).
  rewrite (idlike_wtimes_l s2 p Hs2).
  reflexivity.
Qed.

(* An all-identity-like segment folds to an identity-like value. *)
Lemma fold_all_idlike :
  forall pre s,
    (forall x, In x pre -> idlike x = true) ->
    idlike s = true ->
    idlike (fold_left wtimes pre s) = true.
Proof.
  induction pre as [| x rest IH]; intros s Hall Hs; simpl.
  - exact Hs.
  - apply IH.
    + intros y Hy. apply Hall. right. exact Hy.
    + rewrite (idlike_wtimes_l s x); [| exact Hs].
      apply Hall. left. reflexivity.
Qed.

(* THE PREFIX-WASH THEOREM: an all-identity-like pre-commit segment
   contributes NOTHING to the fold — the result is the post-commit
   segment's own fold. *)
Theorem fold_prefix_washes :
  forall pre post,
    (forall x, In x pre -> idlike x = true) ->
    post <> [] ->
    fold_left wtimes (pre ++ post) w_one = fold_left wtimes post w_one.
Proof.
  intros pre post Hall Hne.
  rewrite fold_left_app.
  apply fold_idlike_seed; [exact Hne | | reflexivity].
  apply fold_all_idlike; [exact Hall | reflexivity].
Qed.

(* (c) PACKING-WEIGHT MEMBER-DETERMINATION / STANCE-INVARIANCE: the OFF
   pre-commit segment (per-member trigger stamp + lex_one interior arms)
   and the ON pre-commit segment (min-member spine trigger stamp +
   lex_one spine arms + the weightless commit Replace) are BOTH all-zero-
   cost, so the two folds agree — the packing weight is a function of the
   SHARED post-commit segment only (member arms + Pop + member-keyed
   coercion charges). *)
Theorem packing_weight_member_determined :
  forall (r_off r_on : nat) (offs ons post : list w),
    (forall x, In x offs -> idlike x = true) ->
    (forall x, In x ons -> idlike x = true) ->
    post <> [] ->
    fold_left wtimes ((MkW 0 (Some r_off) :: offs) ++ post) w_one
    = fold_left wtimes ((MkW 0 (Some r_on) :: ons) ++ post) w_one.
Proof.
  intros r_off r_on offs ons post Hoffs Hons Hne.
  rewrite (fold_prefix_washes (MkW 0 (Some r_off) :: offs) post);
    [| | exact Hne].
  - rewrite (fold_prefix_washes (MkW 0 (Some r_on) :: ons) post);
      [reflexivity | | exact Hne].
    intros x Hx.
    destruct Hx as [Heq | Hx']; [subst x; reflexivity | exact (Hons x Hx')].
  - intros x Hx.
    destruct Hx as [Heq | Hx']; [subst x; reflexivity | exact (Hoffs x Hx')].
Qed.

(* After the first REAL-cost element, the stamp freezes on the LEFT — the
   accumulated fields are the first real-cost step's own (the plan §1.1
   "fields freeze at the FIRST real-cost step"): real-cost anchors are
   member-keyed and stance-invariant, so freezing them is stance-neutral. *)
Theorem real_cost_left_projects :
  forall c s b,
    c <> 0 ->
    idlike b = false ->
    w_stamp (wtimes (MkW c s) b) = s.
Proof.
  intros c s b Hc Hb.
  unfold wtimes, idlike. simpl.
  destruct (c =? 0) eqn:Ec.
  - apply Nat.eqb_eq in Ec. contradiction.
  - unfold idlike in Hb. rewrite Hb. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (a)+(b) THE MACHINE — coordinates, store, transitions.
   ═══════════════════════════════════════════════════════════════════════ *)

(* Coordinates: a spine node id (the synthetic rule_at(cat, SPINE_ID, n)
   marker family) or a member coordinate (rule, pos). *)
Inductive coord : Type :=
| CSpine  (node_id : nat)
| CMember (rule : nat) (pos : nat).

Definition is_spine (c : coord) : bool :=
  match c with CSpine _ => true | CMember _ _ => false end.

(* The emitted spine table (FV-1/2's shape): chain/divergence edges between
   spine coordinates; COMMIT edges from a spine coordinate to a member
   coordinate; member-internal advances; final-pos Pop arms. *)
Record table : Type := MkTable {
  spine_edge   : nat -> nat -> bool;        (* spine node -> spine node *)
  commit_edge  : nat -> nat -> nat -> bool; (* spine node -> (rule, pos) *)
  member_edge  : nat * nat -> nat * nat -> bool;
  member_final : nat * nat -> bool          (* the final-pos Pop arm *)
}.

(* Well-formed emission: commits target REAL member rules only (below the
   synthetic spine id space — factoring.rs A9 asserts SPINE_RULE_BASE =
   0xF800 with all member rule indices far below). *)
Definition SPINE_RULE_BASE : nat := 63488.

Definition wf_table (T : table) : Prop :=
  forall n r p, commit_edge T n r p = true -> r < SPINE_RULE_BASE.

(* A machine configuration: the GSS return context u (abstract id), the
   forest fold w (kept as the LIST of composed step weights — the fold
   value is fold_left wtimes), the coordinate, and the interning STORE
   (append-only carrier list). *)
Record cfg : Type := MkCfg {
  g_u     : nat;
  g_w     : list w;
  g_coord : coord;
  g_store : list nat
}.

(* Transitions. Spine arms fold lex_one() (F1 receipts: interior,
   divergence, chain arms and the leaf-edge guarded consume are ALL
   lex_one — factoring.rs child_branch_tokens @1060-1101); the commit
   marker REPLACE itself carries no weight and touches neither u nor w
   nor the store (`weight: _` @30499; A-2). Member arms may fold ANY
   weight (post-commit machinery is member-owned). Interning APPENDS. *)
Inductive pstep (T : table) : cfg -> cfg -> Prop :=
| PSpineChain : forall u wl st n m fresh,
    spine_edge T n m = true ->
    pstep T (MkCfg u wl (CSpine n) st)
            (MkCfg u (wl ++ [w_one]) (CSpine m) (st ++ fresh))
| PCommit : forall u wl st n r p,
    commit_edge T n r p = true ->
    pstep T (MkCfg u wl (CSpine n) st)
            (MkCfg u wl (CMember r p) st)
| PMemberStep : forall u wl st r p r' p' x fresh,
    member_edge T (r, p) (r', p') = true ->
    pstep T (MkCfg u wl (CMember r p) st)
            (MkCfg u (wl ++ [x]) (CMember r' p') (st ++ fresh)).

(* ── (a) ReplacePreservesUW: the ONLY spine->member transition is the
      commit, and it is the identity on (u, w) and the store — the pure
      commit-Replace keeps everything (`weight: _` @30499; A-2). ── *)
Theorem replace_preserves_uw :
  forall T u wl st n c',
    pstep T (MkCfg u wl (CSpine n) st) c' ->
    (exists r p, g_coord c' = CMember r p) ->
    g_u c' = u /\ g_w c' = wl /\ g_store c' = st.
Proof.
  intros T u wl st n c' Hstep [r [p Hcoord]].
  inversion Hstep; subst; simpl in *.
  - discriminate Hcoord.
  - repeat split; reflexivity.
Qed.

(* ── (a) NO-CARRIER-WRITE: every transition leaves EXISTING store entries
      in place (append-only frame property) — the model has no
      store-mutating constructor, so the refuted shared-carrier restamp
      is not expressible. ── *)
Fixpoint store_prefix (s s' : list nat) : Prop :=
  match s, s' with
  | [], _ => True
  | x :: xs, y :: ys => x = y /\ store_prefix xs ys
  | _ :: _, [] => False
  end.

Lemma store_prefix_app : forall s t, store_prefix s (s ++ t).
Proof.
  induction s as [| x xs IH]; intros t; simpl.
  - exact I.
  - split; [reflexivity | apply IH].
Qed.

Lemma store_prefix_refl : forall s, store_prefix s s.
Proof.
  induction s as [| x xs IH]; simpl; [exact I | split; [reflexivity | exact IH]].
Qed.

Theorem no_carrier_write :
  forall T c c',
    pstep T c c' ->
    store_prefix (g_store c) (g_store c').
Proof.
  intros T c c' Hstep.
  inversion Hstep; subst; simpl.
  - apply store_prefix_app.
  - apply store_prefix_refl.
  - apply store_prefix_app.
Qed.

(* ── (b) COMMIT-PRECEDES-FINAL-POP over paths. ── *)

(* Reflexive-transitive closure counting COMMIT steps. *)
Inductive steps (T : table) : cfg -> cfg -> nat -> Prop :=
| StepsRefl : forall c, steps T c c 0
| StepsChain : forall c1 c2 c3 k,
    pstep T c1 c2 ->
    is_spine (g_coord c1) = true ->
    is_spine (g_coord c2) = true ->
    steps T c2 c3 k ->
    steps T c1 c3 k
| StepsCommit : forall c1 c2 c3 k,
    pstep T c1 c2 ->
    is_spine (g_coord c1) = true ->
    is_spine (g_coord c2) = false ->
    steps T c2 c3 k ->
    steps T c1 c3 (S k)
| StepsMember : forall c1 c2 c3 k,
    pstep T c1 c2 ->
    is_spine (g_coord c1) = false ->
    steps T c2 c3 k ->
    steps T c1 c3 k.

(* Member coordinates never step back to spine coordinates (the emitted
   table has no member->spine transition — commits are one-way). *)
Lemma member_stays_member :
  forall T c c',
    pstep T c c' ->
    is_spine (g_coord c) = false ->
    is_spine (g_coord c') = false.
Proof.
  intros T c c' Hstep Hm.
  inversion Hstep; subst; simpl in *; [discriminate | discriminate |].
  reflexivity.
Qed.

Lemma steps_member_no_commits :
  forall T c c' k,
    steps T c c' k ->
    is_spine (g_coord c) = false ->
    k = 0.
Proof.
  intros T c c' k H.
  induction H; intro Hm.
  - reflexivity.
  - congruence.
  - congruence.
  - apply IHsteps.
    eapply member_stays_member; [exact H | exact Hm].
Qed.

(* The Pop observation: only member coordinates at a final position emit a
   reduce packing; its KEY is the coordinate's rule. *)
Definition packing_of (T : table) (c : cfg) : option (nat * w) :=
  match g_coord c with
  | CMember r p =>
      if member_final T (r, p)
      then Some (r, fold_left wtimes (g_w c) w_one)
      else None
  | CSpine _ => None
  end.

(* EXACTLY-ONE-COMMIT: any path from a spine coordinate to a Pop passes
   exactly one commit. *)
Theorem commit_precedes_final_pop :
  forall T c c' k rk pw,
    steps T c c' k ->
    is_spine (g_coord c) = true ->
    packing_of T c' = Some (rk, pw) ->
    k = 1.
Proof.
  intros T c c' k rk pw H.
  induction H; intros Hs Hpack.
  - (* refl: a spine coordinate has no packing *)
    unfold packing_of in Hpack.
    destruct (g_coord c) eqn:Ec; [discriminate | simpl in Hs; discriminate].
  - (* spine chain: still spine *)
    apply IHsteps; assumption.
  - (* the commit: everything after is member-land with zero commits *)
    f_equal.
    eapply steps_member_no_commits; [exact H2 | exact H1].
  - (* member start contradicts the spine premise *)
    congruence.
Qed.

(* The sharp form: the committed member coordinate is what the path enters
   member-land WITH, and commits only mint wf member rules. *)
Theorem committed_rule_below_base :
  forall T c c',
    wf_table T ->
    pstep T c c' ->
    is_spine (g_coord c) = true ->
    is_spine (g_coord c') = false ->
    exists r p, g_coord c' = CMember r p /\ r < SPINE_RULE_BASE.
Proof.
  intros T c c' Hwf Hstep Hs Hm.
  inversion Hstep; subst; simpl in *.
  - discriminate.
  - exists r, p. split; [reflexivity | exact (Hwf _ _ _ H)].
  - discriminate.
Qed.

(* Member arms never change the rule component (binder.rs arms are keyed
   (result_src_idx, rule_idx, position) — the rule is fixed across a
   member body; only the COMMIT re-keys, spine->member). *)
Definition wf_member_rules (T : table) : Prop :=
  forall r p r' p', member_edge T (r, p) (r', p') = true -> r' = r.

Lemma member_rule_stable :
  forall T c c' k r p,
    wf_member_rules T ->
    steps T c c' k ->
    g_coord c = CMember r p ->
    exists p', g_coord c' = CMember r p'.
Proof.
  intros T c c' k r p Hwfm H.
  revert r p.
  induction H; intros r0 p0 Hcoord.
  - exists p0. exact Hcoord.
  - rewrite Hcoord in H0. discriminate.
  - rewrite Hcoord in H0. discriminate.
  - (* a member step: invert to learn the target coordinate *)
    inversion H; subst; simpl in *.
    + discriminate.
    + discriminate.
    + inversion Hcoord; subst.
      pose proof (Hwfm _ _ _ _ H2) as Hr; subst r'.
      apply (IHsteps r0 p').
      reflexivity.
Qed.

(* THE H9 THEOREM: every reduce packing reachable from a spine descent is
   keyed by a REAL member rule (< SPINE_RULE_BASE) — the walker's live
   debug asserts (pure-reduce packing intern twin, realize, fire) as a
   closed statement. *)
Theorem pop_key_below_base :
  forall T c c' k rk pw,
    wf_table T ->
    wf_member_rules T ->
    steps T c c' k ->
    is_spine (g_coord c) = true ->
    packing_of T c' = Some (rk, pw) ->
    rk < SPINE_RULE_BASE.
Proof.
  intros T c c' k rk pw Hwf Hwfm H.
  induction H; intros Hs Hpack.
  - unfold packing_of in Hpack.
    destruct (g_coord c) eqn:Ec; [| simpl in Hs; discriminate].
    discriminate.
  - apply IHsteps; assumption.
  - (* the commit step: learn the committed rule, chase it to the Pop *)
    destruct (committed_rule_below_base T c1 c2 Hwf H Hs H1)
      as [r [p [Hcoord Hlt]]].
    destruct (member_rule_stable T c2 c3 k r p Hwfm H2 Hcoord)
      as [p' Hcoord'].
    unfold packing_of in Hpack.
    rewrite Hcoord' in Hpack.
    destruct (member_final T (r, p')) eqn:Ef; [| discriminate].
    inversion Hpack; subst rk.
    exact Hlt.
  - congruence.
Qed.

(* ── Assumption audit — every line must print "Closed under the global
      context". ── *)
Print Assumptions zero_cost_stamp_washes.
Print Assumptions wtimes_one_l.
Print Assumptions fold_prefix_washes.
Print Assumptions packing_weight_member_determined.
Print Assumptions real_cost_left_projects.
Print Assumptions replace_preserves_uw.
Print Assumptions no_carrier_write.
Print Assumptions member_stays_member.
Print Assumptions steps_member_no_commits.
Print Assumptions commit_precedes_final_pop.
Print Assumptions committed_rule_below_base.
Print Assumptions member_rule_stable.
Print Assumptions pop_key_below_base.
