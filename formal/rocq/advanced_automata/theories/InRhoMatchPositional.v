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

(* ============================================================================
   STAGE 4 extension of obligation (i): the M-collapse σ + whole-term location.

   The M1 scope above modeled ACCEPTANCE on all-leaf patterns, where a Var leaf's σ
   is its head tag (`children_trivial`). Stage 4 closes the two gaps the campaign
   opened:

     (M-collapse) a Var leaf now binds the FULLY COLLAPSED subterm `⟦subtree⟧` (the
       `cap:` bottom-up fold of `rho_net_lower.rs::collapse_publish`), so σ is the
       POSITIONAL σ for a matched subject of ARBITRARY depth — not merely the head
       tag, which silently dropped a non-nullary subject's children (the reachable
       `Swap(Pair(A,B),_) → Pair()` soundness bug).

     (M-reflect) the driver spreads the WHOLE structurally-reflected subject term and
       the root index LOCATES the redex; `whole_term_located` is the GENERAL (nested)
       children-match instance of the host `index_never_drops_match` — the same index
       theorem, now over the full recursive positional matcher rather than the M1
       all-leaf `children_trivial`.

   Faithfulness of the emitted `Par`/spread to these folds is witnessed operationally
   by the runtime tests (`rho_net_equivalence.rs`: `m_collapse_matches_*`,
   `m_reflect_sigma_is_produced_by_the_automaton_not_the_report`,
   `nested_pattern_collapses_a_deep_non_nullary_leaf_in_rho`); this file proves the
   SERIALIZATION LOGIC (the σ the fold yields, and the index location) correct.
   Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
   ============================================================================ *)

(* The `cap:` COLLAPSE fold (`rho_net_lower.rs::collapse_publish`): a bottom-up
   reflection that rebuilds `⟦subtree⟧` from the children's already-collapsed values.
   On the abstract `Node` it reconstructs the whole subtree — information-preserving.
   (The inner fix maps the fold over the children; guarded by the child subterm.) *)
Fixpoint collapse (n : Node) : Node :=
  match n with
  | NApp op ch =>
      NApp op ((fix cmap (l : list Node) : list Node :=
                  match l with
                  | [] => []
                  | x :: xs => collapse x :: cmap xs
                  end) ch)
  end.

(* The collapse is FAITHFUL: `⟦subtree⟧` decodes to EXACTLY the subtree — no data lost.
   This is the M-collapse correctness the pre-fix head-tag capture violated. *)
Lemma collapse_faithful : forall n, collapse n = n.
Proof.
  fix IH 1. intros [op ch]. simpl. f_equal.
  induction ch as [| c ch' IHch].
  - reflexivity.
  - simpl. rewrite (IH c). f_equal. exact IHch.
Qed.

(* The PRE-M-collapse Var-leaf capture: only the head tag (an arity-0 stub). *)
Definition head_tag_only (n : Node) : Node :=
  match n with NApp op _ => NApp op [] end.

(* The bug is REACHABLE: on a non-nullary subterm the head-tag capture DROPS the
   children, so it is NOT the matched subterm (the `Pair()` witness). *)
Lemma head_tag_drops_nonnullary : forall op ch,
  ch <> [] -> head_tag_only (NApp op ch) <> NApp op ch.
Proof.
  intros op ch Hne Heq. simpl in Heq. injection Heq as Hch.
  apply Hne. symmetry. exact Hch.
Qed.

(* The GENERAL recursive positional matcher — the nested descend-then-collapse matcher (no
   longer the M1 all-leaf `children_trivial`): a structural App matches iff op + arity agree
   AND every child matches RECURSIVELY. A single fixpoint on the PATTERN `p` with an inner
   fix folding the children (each call `pmatch_rec a c` is on `a`, a subterm of `args`,
   itself a subterm of `p`) — guarded WITHOUT the mutual `with` (which Rocq 9.1's guard
   checker rejects for this nested inductive). *)
Fixpoint pmatch_rec (p : Pat) (n : Node) {struct p} : bool :=
  match p, n with
  | PVar, _ => true
  | PApp op args, NApp nop nch =>
      Nat.eqb op nop && Nat.eqb (length args) (length nch) &&
      (fix go (ps : list Pat) (ns : list Node) : bool :=
         match ps, ns with
         | [], [] => true
         | a :: ps', c :: ns' => pmatch_rec a c && go ps' ns'
         | _, _ => false
         end) args nch
  | PAcApp _ _, _ => false
  end.

(* A nested match implies the ROOT (op, arity) index would also fire — the nested matcher's
   root conjuncts ARE the M1 `children_trivial` root check, so `pmatch_rec` refines
   `pmatch children_trivial`; hence the host index theorem applies unchanged. *)
Lemma pmatch_rec_implies_trivial : forall p n,
  pmatch_rec p n = true -> pmatch children_trivial p n = true.
Proof.
  intros p n H. destruct p as [| op args | op args].
  - reflexivity.
  - destruct n as [nop nch]. simpl in H.
    (* `&&` is left-associative: H : ((op=?nop) && (len=?len)) && go = true. *)
    apply andb_true_iff in H. destruct H as [Hoa _].
    apply andb_true_iff in Hoa. destruct Hoa as [Hop Hlen].
    unfold pmatch, children_trivial. rewrite Bool.andb_true_r.
    rewrite Hop, Hlen. reflexivity.
  - simpl in H. destruct n. discriminate H.
Qed.

(* The σ extractor parameterized by the Var-leaf CAPTURE `cap`. A Var leaf binds `cap n`
   (the positional σ uses `id`; the in-Rho network uses the `cap:` collapse fold
   `collapse`); a structural App concatenates its children's σ in first-occurrence
   (left-to-right / DFS) order — the σ-receiver's formal order. The inner `go` fixpoint
   folds the children (guarded on `ps`, a subterm of `args`, itself a subterm of `p`). *)
Fixpoint sigma_gen (cap : Node -> Node) (p : Pat) (n : Node) {struct p}
  : option (list Node) :=
  match p, n with
  | PVar, _ => Some [cap n]
  | PApp op args, NApp nop nch =>
      if Nat.eqb op nop && Nat.eqb (length args) (length nch)
      then (fix go (ps : list Pat) (ns : list Node) : option (list Node) :=
              match ps, ns with
              | [], [] => Some []
              | a :: ps', c :: ns' =>
                  match sigma_gen cap a c, go ps' ns' with
                  | Some s1, Some s2 => Some (s1 ++ s2)
                  | _, _ => None
                  end
              | _, _ => None
              end) args nch
      else None
  | PAcApp _ _, _ => None
  end.

(* The POSITIONAL σ binds each Var leaf to the WHOLE matched subterm (`id`). *)
Definition sigma_pos : Pat -> Node -> option (list Node) := sigma_gen (fun n => n).
(* The IN-RHO σ binds each Var leaf to its `cap:` COLLAPSE value (`collapse`). *)
Definition sigma_rho : Pat -> Node -> option (list Node) := sigma_gen collapse.

(* The σ depends on the Var-leaf capture ONLY at the leaf: two captures that agree
   everywhere induce the same σ (the structural descent is capture-agnostic). *)
Lemma sigma_gen_ext : forall cap1 cap2,
  (forall n, cap1 n = cap2 n) ->
  forall p n, sigma_gen cap1 p n = sigma_gen cap2 p n.
Proof.
  intros cap1 cap2 Hcap. fix IH 1. intros p n.
  destruct p as [| op args | op args].
  - simpl. rewrite Hcap. reflexivity.
  - destruct n as [nop nch]. simpl.
    destruct (Nat.eqb op nop && Nat.eqb (length args) (length nch)); [| reflexivity].
    revert nch. induction args as [| a args' IHargs]; intros nch.
    + reflexivity.
    + destruct nch as [| c nch']; [ reflexivity |].
      simpl. rewrite (IH a c). rewrite (IHargs nch'). reflexivity.
  - reflexivity.
Qed.

(* ---- the children_match fold yields the POSITIONAL σ (M-collapse correctness) ---- *)

(* KEY (non-nullary σ correctness): the in-Rho σ (via the `cap:` collapse fold) EQUALS
   the positional σ (the full matched subterms) — for a matched subject of ARBITRARY
   depth, not just a nullary leaf. The Var leaf binds `collapse n = n` (faithful), and
   the structural descent is capture-agnostic. This is the exact obligation the M1 scope
   left open: a non-nullary Var subterm's σ is its whole `⟦subtree⟧`, not its head tag. *)
Theorem sigma_rho_eq_pos : forall p n, sigma_rho p n = sigma_pos p n.
Proof.
  intros p n. unfold sigma_rho, sigma_pos.
  apply sigma_gen_ext. intro m. apply collapse_faithful.
Qed.

(* The pre-fix head-tag capture is UNSOUND at a NON-nullary Var leaf: it disagrees with
   the positional σ (the arity-abstracted `Pair()` witness — the exact soundness bug the
   `cap:` collapse removed). *)
Theorem buggy_head_tag_wrong_for_nonnullary : forall op ch,
  ch <> [] -> Some [head_tag_only (NApp op ch)] <> sigma_pos PVar (NApp op ch).
Proof.
  intros op ch Hne. unfold sigma_pos. simpl. intro Heq.
  apply (head_tag_drops_nonnullary op ch Hne). simpl.
  injection Heq as Hn. rewrite Hn. reflexivity.
Qed.

(* ---- whole-term location: the root index locates a nested match (M-reflect) ---- *)

(* The automaton spreads the WHOLE structurally reflected subject and the root (op, arity)
   index LOCATES a root-rooted redex — a NESTED positional match (`pmatch_rec`, arbitrary
   depth) of a compilable pattern is dispatched by the index. Reuses the host
   `index_never_drops_match` (via `pmatch_rec_implies_trivial`), now over the full recursive
   matcher rather than M1's all-leaf `children_trivial`. *)
Corollary whole_term_located : forall p n,
  compilable p = true -> pmatch_rec p n = true -> dispatched p n = true.
Proof.
  intros p n Hc Hm.
  apply (index_never_drops_match children_trivial p n).
  - exact Hc.
  - apply pmatch_rec_implies_trivial. exact Hm.
Qed.

(* Obligation (i), STAGE 4: on a matched whole-term subject, the automaton BOTH (a)
   LOCATES the redex by the root index AND (b) binds the POSITIONAL σ (the full
   collapsed subterms), for a pattern of ARBITRARY depth. *)
Corollary inrho_stage4_locates_and_binds_positional_sigma : forall p n,
  compilable p = true -> pmatch_rec p n = true ->
  dispatched p n = true /\ sigma_rho p n = sigma_pos p n.
Proof.
  intros p n Hc Hm. split.
  - apply whole_term_located; assumption.
  - apply sigma_rho_eq_pos.
Qed.

(* ============================================================================
   STAGE 4 (locate-all + multi-firing): the automaton LOCATES EVERY redex — at ANY
   position in the subject, and multiple simultaneously (P1 Thm 6.12 / P2 Thm 2).

   `whole_term_located` above proves the root index locates a redex that is the WHOLE
   subject. The Stage-4 driver instead spreads the whole subject ONCE and co-installs a
   positional network at EVERY position whose head is a rule root — so a NESTED redex
   (a strict subterm) and MULTIPLE redexes all fire. We model the POSITION SET of a
   subject (`subnodes`, its subtree list) and prove the located-match set
   `matches_at p = filter (pmatch_rec p) (subnodes n)` is exactly the positions the
   recursive matcher accepts, that EACH is dispatched by the root index at that position
   (reusing `whole_term_located` — the SAME index theorem, now at every subnode rather
   than only the root) and binds the POSITIONAL σ there (reusing `sigma_rho_eq_pos`), and
   that MULTIPLE distinct positions are located simultaneously (a non-vacuous 2-redex
   witness). This is the executable image of the Rust `collect_redex_sites` /
   `in_rho_match_all_sites_call_par` (`rholang-codegen/src/rho_net_ruleset.rs`) — the
   host pre-filters candidate positions by head op (exactly the root-index dispatch), and
   the emitted per-position network re-does the match + σ ON the interpreter.

   Faithfulness of the emitted `∏ network_ℓ ‖ spread` to this position fold is witnessed
   operationally by `rho_net_equivalence.rs` (`nested_redex_fires_in_rho_no_replay_fallback`,
   `multiple_redexes_fire_in_rho_no_replay_fallback`, `nested_redex_in_arg_position_fires_in_rho`,
   and the `locate_all_property` positional-oracle proptest); this file proves the LOCATION
   LOGIC (which positions the index dispatches, and the σ each binds) correct.
   Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
   ============================================================================ *)

(* The POSITION SET of a subject: the subject itself plus every subtree, DFS pre-order —
   the config-tree positions the spread publishes a `loc:`/`cap:` channel for. Same nested
   `fix` shape as `collapse`/`pmatch_rec` (the recursive call `subnodes x` is on a child of
   `NApp op ch`, structurally smaller; the inner `smap` folds the child list). *)
Fixpoint subnodes (n : Node) : list Node :=
  match n with
  | NApp op ch =>
      NApp op ch :: (fix smap (l : list Node) : list Node :=
                       match l with
                       | [] => []
                       | x :: xs => subnodes x ++ smap xs
                       end) ch
  end.

(* The root subject is one of its own positions (the root `loc:ρ` channel). *)
Lemma subnodes_refl : forall n, In n (subnodes n).
Proof. intros [op ch]. simpl. left. reflexivity. Qed.

(* The LOCATED-MATCH SET at a subject: every position whose subtree the recursive matcher
   accepts (the multiset of redex sites the automaton co-installs a network at). *)
Definition matches_at (p : Pat) (n : Node) : list Node :=
  filter (fun m => pmatch_rec p m) (subnodes n).

(* SOUND: every located site is a genuine positional match at a real position. *)
Lemma matches_at_sound : forall p n m,
  In m (matches_at p n) -> In m (subnodes n) /\ pmatch_rec p m = true.
Proof. intros p n m Hin. apply filter_In in Hin. exact Hin. Qed.

(* COMPLETE: every positional match at a real position is located (no redex is dropped). *)
Lemma matches_at_complete : forall p n m,
  In m (subnodes n) -> pmatch_rec p m = true -> In m (matches_at p n).
Proof. intros p n m Hpos Hm. apply filter_In. split; assumption. Qed.

(* LOCATE-ALL DISPATCH (obligation i, generalized off the root): EVERY located redex — at
   ANY position — is dispatched by the root index AT THAT POSITION. The exact same
   `whole_term_located` index theorem, applied at each subnode rather than only the whole
   subject: the root Match at position ℓ never drops the match sitting there. *)
Theorem locate_all_dispatched : forall p n,
  compilable p = true -> forall m, In m (matches_at p n) -> dispatched p m = true.
Proof.
  intros p n Hc m Hin. apply matches_at_sound in Hin. destruct Hin as [_ Hm].
  apply whole_term_located; assumption.
Qed.

(* LOCATE-ALL σ: EVERY located redex binds the POSITIONAL σ (its full `cap:`-collapsed
   subterms) at its position — the M-collapse σ correctness, now at every site. *)
Theorem locate_all_binds_positional_sigma : forall p n m,
  In m (matches_at p n) -> sigma_rho p m = sigma_pos p m.
Proof. intros p n m _. apply sigma_rho_eq_pos. Qed.

(* The root redex (when the whole subject matches) is among the located sites — the
   root-rooted case is subsumed, not special-cased. *)
Corollary root_redex_located : forall p n,
  pmatch_rec p n = true -> In n (matches_at p n).
Proof.
  intros p n Hm. apply matches_at_complete; [ apply subnodes_refl | exact Hm ].
Qed.

(* MULTIPLE redexes located SIMULTANEOUSLY: any two (indeed any number of) distinct
   matching positions are BOTH in the located set — the co-installed sites do not
   exclude one another. *)
Theorem two_distinct_redexes_both_located : forall p n m1 m2,
  In m1 (subnodes n) -> In m2 (subnodes n) ->
  pmatch_rec p m1 = true -> pmatch_rec p m2 = true ->
  In m1 (matches_at p n) /\ In m2 (matches_at p n).
Proof.
  intros p n m1 m2 H1 H2 Hm1 Hm2.
  split; apply matches_at_complete; assumption.
Qed.

(* Non-vacuity: a concrete subject with TWO simultaneously-located redexes — the
   `Pair(Swap(A,B), Swap(C,D))` shape (two Swap children of an inert Pair). Both Swap
   positions match the arity-2 op-0 pattern; the Pair root (op 1) and the leaves do not,
   so exactly 2 sites are located. Proves the multi-firing set is genuinely > 1. *)
Definition witness_leaf (k : nat) : Node := NApp k [].
Definition witness_swap1 : Node := NApp 0 [witness_leaf 2; witness_leaf 3].
Definition witness_swap2 : Node := NApp 0 [witness_leaf 4; witness_leaf 5].
Definition witness_pair : Node := NApp 1 [witness_swap1; witness_swap2].
Definition witness_pat : Pat := PApp 0 [PVar; PVar].

Theorem multiple_redexes_locatable :
  compilable witness_pat = true /\ length (matches_at witness_pat witness_pair) = 2.
Proof. split; vm_compute; reflexivity. Qed.

(* Obligation (i), STAGE 4 LOCATE-ALL: at EVERY located position of a compilable pattern,
   the automaton BOTH LOCATES the redex (root index at that position) AND binds the
   POSITIONAL σ there — for redexes at ANY position and any number of them. *)
Corollary inrho_stage4_locates_all_and_binds_positional_sigma : forall p n,
  compilable p = true ->
  forall m, In m (matches_at p n) ->
    dispatched p m = true /\ sigma_rho p m = sigma_pos p m.
Proof.
  intros p n Hc m Hin. split.
  - apply (locate_all_dispatched p n Hc m Hin).
  - apply (locate_all_binds_positional_sigma p n m Hin).
Qed.

Print Assumptions sa_accept_sound.
Print Assumptions sa_accept_complete.
Print Assumptions sa_matches_positional.
Print Assumptions inrho_match_dispatched.
Print Assumptions inrho_no_false_root.
Print Assumptions collapse_faithful.
Print Assumptions sigma_rho_eq_pos.
Print Assumptions buggy_head_tag_wrong_for_nonnullary.
Print Assumptions whole_term_located.
Print Assumptions inrho_stage4_locates_and_binds_positional_sigma.
Print Assumptions locate_all_dispatched.
Print Assumptions locate_all_binds_positional_sigma.
Print Assumptions root_redex_located.
Print Assumptions two_distinct_redexes_both_located.
Print Assumptions multiple_redexes_locatable.
Print Assumptions inrho_stage4_locates_all_and_binds_positional_sigma.
