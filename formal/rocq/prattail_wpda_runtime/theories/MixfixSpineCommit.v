(*
 * MixfixSpineCommit: S1-FACTORING F5-2 FV extension (FV-1'' + FV-2'' +
 * FV-3b(b)/(c)'' on the MIXFIX surface) — the rhocalc Name-led send fan's
 * factored spine (plan f5_mixfix_cohorts_plan.md §1.3/§2.2/§5, red-team
 * amendments A-M1..A-M5 folded; ledger s2_stageA_ledger.md §"S1 F5-2"),
 * over the SHIPPED models (imported verbatim, never restated):
 * TrieLeafBijection (members/trie/builder), SpineSimulation (divergence
 * partition + concatenation), PureCommitFoldIntegrity (the machine +
 * weight wash law), PureCommitFoldIntegrityAccept (the fork-at-a-node
 * shape reused for the mixfix divergence forks).
 *
 * HONEST SCOPE: static tables + commit/lineage coordinates over the
 * emitted shapes — NOT a runtime GSS/descriptor bisimulation (that side
 * is covered empirically by the S1 H9 asserts + the F5-2 round-2 battery,
 * receipts scratchpad/zz_probes/logs_s1f5_2/).
 *
 * WHAT IS PROVED (per the mandate + plan §5):
 *   (1) THE MIXFIX COORDINATE WALK — `coords_of` mirrors factoring.rs
 *       `mixfix_member_items`' recorded walk (single-part + nullary: the
 *       SHIPPED eligibility domain — `build_mixfix_factoring` defers any
 *       group whose shared spine carries a second operand,
 *       `IneligibleReason::MultiOperandSharedSpine`, so single-operand
 *       coverage is exhaustive for eligible groups, not a narrowing):
 *       nullary members commit at (2, 0, depth); operand members with the
 *       operand at item index j commit at (0, 0, depth - j - 1) — the
 *       plan-§5 FV-1 coordinate law, plus walk-prefix agreement (shared
 *       item prefixes give identical spine coordinates — the spine-arm-key
 *       well-definedness behind `mixfix_spine_arm_coords`).
 *   (2) THE !/!! COHORT TRIES — build_node (the F0 builder REUSED verbatim
 *       by the shipped discovery) on the census members yields exactly the
 *       committed pin `L(()[P(0,0)[L())=>r4 L(,)=>r8] L())=>r6]`
 *       (divergence depths 1 and 2; rule 8 truncated at its rep; ZERO
 *       interior accepts — ["(",")"] is NOT a prefix of ["(",P,")"]:
 *       they diverge at index 1), leaf bijection, path law, and the
 *       spine-consumed ++ member-tail concatenation transported verbatim.
 *   (3) GUARD-DEATH PARTITION (FV-2'') — divergence_partition instantiated
 *       at both divergence depths: a death at a divergence edge kills
 *       EXACTLY the members whose own next item is that edge.
 *   (4) THE TWO-ARM CAR CONTRACT (D-3 / A-M1) as a model transition —
 *       classic's conditional GSS-replace-on-inequality and pure's
 *       unconditional `cur_sym := br_symbol` are EXTENSIONALLY EQUAL on
 *       the symbol observable; same-symbol branches (every pre-F5-2
 *       emitter — `__checked_literal_consume!` is the rg-verified sole
 *       fork-CAR emitter) perform NO GSS replace (the historical "No GSS
 *       mutation" contract preserved); a commit branch replaces the spine
 *       symbol with the member symbol ON ITS OWN CHILD ONLY (parent and
 *       sibling branches keep the spine top — each child's symbol is a
 *       function of the PARENT top and its OWN branch).
 *   (5) FV-3b(b) TRANSPORT — the mixfix machine tables (! and !!):
 *       commit_precedes_final_pop and pop_key_below_base hold on them;
 *       divergence 1 IS the F5-1 fork shape (`accept_fork_at`: spine
 *       successor + commit edge coexist) and divergence 2 is the
 *       all-commits node (`all_accepts_node`); three !-lineage receipts
 *       (x!() / x!(0) / x!(0,1)) + the !! nullary twin, each passing
 *       EXACTLY ONE commit with its packing keyed by the real member rule.
 *   (6) D-1 FULL-ADMISSION FLOOR — the spine branch's `min_l_bp >= cur_bp`
 *       gate admits iff EVERY member's own floor gate admits (no
 *       floor-blocked member is ever resurrected by the spine — the
 *       FS-M3 refutation as a theorem), with the cur_bp = 7 partial-window
 *       receipt (spine refused; the verbatim member loop admits exactly
 *       rule 8).
 *   (7) K-A FOLD-COUNT (FV-2''-note) — the per-reading consumed-fold count
 *       is stance-invariant (trigger + spine-consumed + member-tail =
 *       trigger + member items); the fan's marker-push count per attempt
 *       drops 3 -> 1 (dead-branch economy only — the F3.2 K-A count map
 *       restated, not hand-waved).
 *   (8) FV-3b(c) HONEST CARVE-OUT (the C8-mixfix channel) — the mixfix
 *       trigger stamp is REAL-COST (BP_TIER_MIXFIX = 0.20), so the F3
 *       zero-cost wash law does NOT apply to it: the fold COST total is
 *       stance-invariant (cost is additive through wtimes), but the frozen
 *       identity FIELD is the trigger stamp's own — OFF stamps the member,
 *       ON stamps the MIN member, and no single spine stamp can reproduce
 *       two distinct member stamps (the plan-§3(d) impossibility as a
 *       theorem). Elected-AST invariance under the substitution is the
 *       EMPIRICAL side (C8 A/B 40/40 INVARIANT, the one pre-classified
 *       ELECTED-W row `bitnot (a)!()` rule 6 -> rule 4 — receipts
 *       logs_s1f5_2/), cited, not proven.
 *
 * ── CROSS-REFERENCE TABLE (model ↔ the Rust it transcribes; commit
 *    8df26fbe) ──
 *
 *   `coords_of`/`walk_from`     ↔ factoring.rs `mixfix_member_items`
 *                                 (@1166-1234): coords[0] = (2,0,0); part-0
 *                                 preceding literals at (2,0,j+1); the
 *                                 operand jumps to (0, completed, 0) (the
 *                                 Unwinding-MixfixMarker re-entry); part-0
 *                                 following literals at (0, completed, j+1);
 *                                 a `*sep` repetition CUTS the walk
 *                                 (`truncated`); coords.len() == items.len()+1
 *   `mixfix_finalize`           ↔ finalize_leaf's Mixfix arm (@649-677):
 *                                 commit = mixfix_coords[leaf_depth],
 *                                 pos_map = coords[..=leaf_depth]
 *                                 (`SpinePosMap::Mixfix`)
 *   `CMixfixRun`                ↔ `MemberCommit::MixfixRun { rule_idx, kind,
 *                                 completed_idx, sub_pos }` (@205-210)
 *   cohort members              ↔ the committed P1 pin
 *                                 `rhocalc_mixfix_send_cohorts_pin_two_groups`
 *                                 (@4908-4998): `!` slice
 *                                 [(2,0,4),(6,0,6),(10,0,8)], spine
 *                                 SPINE_RULE_BASE+3 = 0xF803 = 63491
 *                                 continuing Proc's three prefix ordinals;
 *                                 `!!` [(4,0,5),(8,0,7),(12,0,9)], 0xF804 =
 *                                 63492; item codes here: 0 = L"(" ·
 *                                 1 = P(Proc,0) · 2 = L")" · 3 = L","
 *   the two-arm CAR             ↔ wpda_walker.rs classic fork-CAR arm
 *                                 (@17345-17380: conditional
 *                                 `cursor_gss_replace_top_auto` on
 *                                 `gss.node(child.node).symbol !=
 *                                 branch.symbol`) + pure fork-CAR arm
 *                                 (@31091-31110: `cur_sym: br_symbol`);
 *                                 variant rustdoc @3722-3749 (the rewritten
 *                                 two-family contract). The counterfactual
 *                                 receipts (P2-CF: pure H9 panic at the
 *                                 reduce packing intern / classic
 *                                 POutputEmpty reading LOST) are the
 *                                 runtime witnesses that both halves are
 *                                 load-bearing
 *   machine tables              ↔ the emitted prelude
 *                                 (factoring.rs `mixfix_prelude_group_arms`
 *                                 @2655-2707 + `mixfix_spine_step_arm`
 *                                 @2783+): arm (0,SPINE,2,0,0) chains "(";
 *                                 (0,SPINE,2,0,1) = divergence 1
 *                                 {operand-descent Advance FIRST (trie
 *                                 child order), rule-6/7 commit CAR};
 *                                 (0,SPINE,0,0,0) = divergence 2 {rule-4/5
 *                                 commit CAR on ")", rule-8/9 commit CAR on
 *                                 ","}; commits ride consuming edges (FS1 —
 *                                 zero epsilon branches); member positions
 *                                 in the tables are FLAT walk indices with
 *                                 the typed (kind, completed, sub_pos)
 *                                 coordinates pinned by `mixfix_finalize`
 *   D-1 floor                   ↔ `mixfix_fan_group_arm` (@2604-2643):
 *                                 guard `min_l_bp >= *cur_bp` on the ONE
 *                                 spine branch; the `_` fallback arm is the
 *                                 VERBATIM per-member loop
 *   weight model                ↔ rigail lex_weight.rs (`is_one`
 *                                 primary-only; `times` left-projection) as
 *                                 shipped in PureCommitFoldIntegrity;
 *                                 BP_TIER_MIXFIX = 0.20 (real cost) is
 *                                 modeled as any nonzero `w_cost`
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
From PrattailWpdaRuntime Require Import SpineSimulation.
From PrattailWpdaRuntime Require Import PureCommitFoldIntegrity.
From PrattailWpdaRuntime Require Import PureCommitFoldIntegrityAccept.
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════
   (1) THE MIXFIX COORDINATE WALK — `mixfix_member_items`' recorded
   member-side (kind, completed_idx, sub_pos) coordinates as a function of
   the item list. The single-part + nullary walk is the SHIPPED eligibility
   domain (MultiOperandSharedSpine defers multi-operand spines), so this
   model is exhaustive for eligible groups.
   ═══════════════════════════════════════════════════════════════════════ *)

Definition mcoord : Type := nat * nat * nat. (* (kind, completed_idx, sub_pos) *)

(* One step per consumed item: a literal increments sub_pos in the current
   kind; the (single) operand jumps to the kind-0 re-entry (0, 0, 0) — the
   Unwinding-MixfixMarker arm's `(0, part_i, 0)` at part_i = 0. *)
Fixpoint walk_from (st : mcoord) (is_op : item -> bool) (its : list item)
  : list mcoord :=
  match its with
  | [] => []
  | i :: rest =>
      let next :=
        if is_op i then (0, 0, 0)
        else match st with (k, c, s) => (k, c, S s) end
      in next :: walk_from next is_op rest
  end.

(* coords[0] = the fan-pushed entry state (2, 0, 0); coords[d] = the
   member-side coordinate AFTER consuming d post-trigger items. *)
Definition coords_of (is_op : item -> bool) (its : list item) : list mcoord :=
  (2, 0, 0) :: walk_from (2, 0, 0) is_op its.

Lemma walk_length :
  forall is_op its st, length (walk_from st is_op its) = length its.
Proof.
  intros is_op its.
  induction its as [| x rest IH]; intros [[k c] s]; simpl.
  - reflexivity.
  - destruct (is_op x); simpl; now rewrite IH.
Qed.

(* The factoring.rs invariant "coords.len() == items.len() + 1". *)
Theorem coords_of_length :
  forall is_op its, length (coords_of is_op its) = S (length its).
Proof.
  intros is_op its. unfold coords_of. simpl. now rewrite walk_length.
Qed.

Lemma walk_all_lit_nth :
  forall is_op its k c s d,
    Forall (fun i => is_op i = false) its ->
    d < length its ->
    nth_error (walk_from (k, c, s) is_op its) d = Some (k, c, s + S d).
Proof.
  intros is_op its.
  induction its as [| x rest IH]; intros k c s d Hall Hd; simpl in *.
  - lia.
  - inversion Hall; subst.
    rewrite H1.
    destruct d as [| d']; simpl.
    + f_equal. f_equal. lia.
    + rewrite (IH k c (S s) d' H2) by lia.
      f_equal. f_equal. lia.
Qed.

Lemma walk_lit_prefix_split :
  forall is_op pre rest k c s,
    Forall (fun i => is_op i = false) pre ->
    walk_from (k, c, s) is_op (pre ++ rest)
    = walk_from (k, c, s) is_op pre
      ++ walk_from (k, c, s + length pre) is_op rest.
Proof.
  intros is_op pre.
  induction pre as [| x prest IH]; intros rest k c s Hall; simpl.
  - now rewrite Nat.add_0_r.
  - inversion Hall; subst.
    rewrite H1. simpl.
    f_equal.
    rewrite (IH rest k c (S s) H2).
    replace (s + S (length prest)) with (S s + length prest) by lia.
    reflexivity.
Qed.

Lemma walk_op_head_nth :
  forall is_op op post st t,
    is_op op = true ->
    Forall (fun i => is_op i = false) post ->
    t <= length post ->
    nth_error (walk_from st is_op (op :: post)) t = Some (0, 0, t).
Proof.
  intros is_op op post st t Hop Hpost Ht.
  simpl. rewrite Hop.
  destruct t as [| t']; simpl.
  - reflexivity.
  - rewrite (walk_all_lit_nth is_op post 0 0 0 t' Hpost) by lia.
    reflexivity.
Qed.

(* ── THE COORDINATE LAWS (plan §5 FV-1: "rule 6 -> (2,0,depth); rules 4/8
      -> (0, ops-completed, following-consumed)"). ── *)

(* Nullary member: every coordinate is the kind-2 literal cursor. *)
Theorem coords_nullary_nth :
  forall is_op its d,
    Forall (fun i => is_op i = false) its ->
    d <= length its ->
    nth_error (coords_of is_op its) d = Some (2, 0, d).
Proof.
  intros is_op its d Hall Hd.
  unfold coords_of.
  destruct d as [| d']; simpl.
  - reflexivity.
  - rewrite (walk_all_lit_nth is_op its 2 0 0 d' Hall) by lia.
    reflexivity.
Qed.

(* Single-part member, pre-operand region: identical to the nullary walk —
   this is ALSO the shared-prefix agreement that keys the spine's own arms
   (nullary and operand members agree wherever their items agree). *)
Theorem coords_single_part_pre :
  forall is_op pre op post d,
    Forall (fun i => is_op i = false) pre ->
    d <= length pre ->
    nth_error (coords_of is_op (pre ++ op :: post)) d = Some (2, 0, d).
Proof.
  intros is_op pre op post d Hpre Hd.
  unfold coords_of.
  destruct d as [| d']; simpl; [reflexivity |].
  rewrite (walk_lit_prefix_split is_op pre (op :: post) 2 0 0 Hpre).
  rewrite nth_error_app1.
  - rewrite (walk_all_lit_nth is_op pre 2 0 0 d' Hpre) by lia. reflexivity.
  - rewrite walk_length. lia.
Qed.

(* Single-part member, operand at item index j = |pre|: past the operand the
   coordinate is (0, 0, following-consumed) with following-consumed =
   d - j - 1. *)
Theorem coords_single_part_post :
  forall is_op pre op post d,
    Forall (fun i => is_op i = false) pre ->
    is_op op = true ->
    Forall (fun i => is_op i = false) post ->
    length pre < d ->
    d <= length pre + 1 + length post ->
    nth_error (coords_of is_op (pre ++ op :: post)) d
    = Some (0, 0, d - length pre - 1).
Proof.
  intros is_op pre op post d Hpre Hop Hpost Hlo Hhi.
  unfold coords_of.
  destruct d as [| d']; [lia |].
  replace (S d' - length pre - 1) with (d' - length pre) by lia.
  cbn [nth_error].
  rewrite (walk_lit_prefix_split is_op pre (op :: post) 2 0 0 Hpre).
  rewrite nth_error_app2; rewrite walk_length; [| lia].
  apply walk_op_head_nth; [exact Hop | exact Hpost | lia].
Qed.

(* WALK-PREFIX AGREEMENT: the coordinate at depth d is a function of the
   first d items alone — two members sharing an item prefix share every
   spine coordinate over it (the `mixfix_spine_arm_coords` key
   well-definedness: the emitted prelude keys arms by the SHARED walk). *)
Lemma walk_nth_prefix :
  forall is_op d its its' st,
    d < length its ->
    d < length its' ->
    firstn (S d) its = firstn (S d) its' ->
    nth_error (walk_from st is_op its) d
    = nth_error (walk_from st is_op its') d.
Proof.
  intros is_op d.
  induction d as [| d' IH]; intros its its' st Hd Hd' Hfx.
  - destruct its as [| x r]; destruct its' as [| x' r']; simpl in *;
      try lia.
    inversion Hfx; subst x'.
    reflexivity.
  - destruct its as [| x r]; destruct its' as [| x' r']; simpl in *;
      try lia.
    inversion Hfx; subst x'.
    destruct (is_op x).
    + apply IH; [lia | lia | exact H1].
    + apply IH; [lia | lia | exact H1].
Qed.

Theorem coords_of_prefix_agreement :
  forall is_op d its its',
    d <= length its ->
    d <= length its' ->
    firstn d its = firstn d its' ->
    nth_error (coords_of is_op its) d
    = nth_error (coords_of is_op its') d.
Proof.
  intros is_op d its its' Hd Hd' Hfx.
  unfold coords_of.
  destruct d as [| d']; simpl; [reflexivity |].
  apply walk_nth_prefix; [lia | lia | exact Hfx].
Qed.

(* ── THE TYPED COMMIT (MemberCommit::MixfixRun, the A4-analog). ── *)

Inductive mixfix_commit : Type :=
| CMixfixRun (rule_idx kind completed_idx sub_pos : nat).

Definition mixfix_finalize (is_op : item -> bool) (m : member) (d : nat)
  : mixfix_commit :=
  match nth_error (coords_of is_op (m_items m)) d with
  | Some (k, c, s) => CMixfixRun (m_rule m) k c s
  | None => CMixfixRun (m_rule m) 0 0 0 (* unreachable for d <= |items| *)
  end.

(* Totality guard (the finalize_leaf assert @657-664 as a lemma). *)
Lemma mixfix_finalize_total :
  forall is_op m d,
    d <= length (m_items m) ->
    exists kcs, nth_error (coords_of is_op (m_items m)) d = Some kcs.
Proof.
  intros is_op m d Hd.
  destruct (nth_error (coords_of is_op (m_items m)) d) as [kcs |] eqn:E.
  - exists kcs. reflexivity.
  - apply nth_error_None in E.
    rewrite coords_of_length in E. lia.
Qed.

Theorem mixfix_commit_nullary :
  forall is_op m d,
    Forall (fun i => is_op i = false) (m_items m) ->
    d <= length (m_items m) ->
    mixfix_finalize is_op m d = CMixfixRun (m_rule m) 2 0 d.
Proof.
  intros is_op m d Hall Hd.
  unfold mixfix_finalize.
  rewrite (coords_nullary_nth is_op (m_items m) d Hall Hd).
  reflexivity.
Qed.

Theorem mixfix_commit_operand :
  forall is_op m pre op post d,
    m_items m = pre ++ op :: post ->
    Forall (fun i => is_op i = false) pre ->
    is_op op = true ->
    Forall (fun i => is_op i = false) post ->
    length pre < d ->
    d <= length pre + 1 + length post ->
    mixfix_finalize is_op m d
    = CMixfixRun (m_rule m) 0 0 (d - length pre - 1).
Proof.
  intros is_op m pre op post d Hitems Hpre Hop Hpost Hlo Hhi.
  unfold mixfix_finalize.
  rewrite Hitems.
  rewrite (coords_single_part_post is_op pre op post d Hpre Hop Hpost Hlo Hhi).
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (2) THE !/!! COHORT TRIES — census members (committed P1 pin
   `rhocalc_mixfix_send_cohorts_pin_two_groups`, factoring.rs @4908-4998).
   Item codes: 0 = L"(" · 1 = P(Proc,0) · 2 = L")" · 3 = L",".
   Slice order mirrors `mixfix_bp_name`: `!` = [r4, r6, r8],
   `!!` = [r5, r7, r9]. Rule 8/9 items are CUT at the `*sep` repetition
   (m_trunc = true — the rep runs in the member's own CollectionLoop).
   ═══════════════════════════════════════════════════════════════════════ *)

Definition is_op_code (i : item) : bool := i =? 1.

(* m_kind is irrelevant to the trie builder (only finalize_commit reads it);
   the mixfix members use THIS file's `mixfix_finalize` instead — KNullary
   here is a placeholder, exactly as MemberKind::Mixfix routes around the
   F0 finalize arms in factoring.rs. *)
Definition bang_out   : member := MkMember 4 KNullary [0; 1; 2] 3 false.
Definition bang_empty : member := MkMember 6 KNullary [0; 2] 2 false.
Definition bang_2plus : member := MkMember 8 KNullary [0; 1; 3] 3 true.

Definition bb_out   : member := MkMember 5 KNullary [0; 1; 2] 3 false.
Definition bb_empty : member := MkMember 7 KNullary [0; 2] 2 false.
Definition bb_2plus : member := MkMember 9 KNullary [0; 1; 3] 3 true.

Definition bang_members : list member := [bang_out; bang_empty; bang_2plus].
Definition bb_members   : list member := [bb_out; bb_empty; bb_2plus].

(* The committed trie pin `L(()[P(0,0)[L())=>r4 L(,)=>r8] L())=>r6]`:
   root edge "(", divergence 1 at depth-1 items (operand vs ")"),
   divergence 2 at depth-2 items (")" vs ","). *)
Definition bang_tree : tree :=
  TInterior 0
    [TInterior 1 [TLeaf 2 bang_out 3; TLeaf 3 bang_2plus 3];
     TLeaf 2 bang_empty 2].

Definition bb_tree : tree :=
  TInterior 0
    [TInterior 1 [TLeaf 2 bb_out 3; TLeaf 3 bb_2plus 3];
     TLeaf 2 bb_empty 2].

(* ZERO interior accepts: the accepts component is [] — ["(",")"] is NOT a
   prefix of ["(",P,")"] (divergence at index 1), so no member exhausts at
   an interior node. The shipped discovery keeps the exhaustion-at-interior
   check and routes any future such group to IneligibleReason::InteriorAccept
   whole-group-unfactored (accept_continue is ALWAYS false on this surface). *)
Theorem bang_cohort_tree :
  build_node 32 1 0 bang_members = Some (bang_tree, []).
Proof. vm_compute. reflexivity. Qed.

Theorem bb_cohort_tree :
  build_node 32 1 0 bb_members = Some (bb_tree, []).
Proof. vm_compute. reflexivity. Qed.

Theorem bang_leaves : leaf_rules bang_tree = [4; 8; 6].
Proof. vm_compute. reflexivity. Qed.

Theorem bb_leaves : leaf_rules bb_tree = [5; 9; 7].
Proof. vm_compute. reflexivity. Qed.

(* Leaf ↔ member bijection (FV-1 (a) transported to the cohorts). *)
Theorem bang_leaf_bijection :
  Permutation (leaf_rules bang_tree) (rules_of bang_members).
Proof.
  exact (eligible_leaves_are_members 32 1 0 bang_members bang_tree
           bang_cohort_tree).
Qed.

Theorem bb_leaf_bijection :
  Permutation (leaf_rules bb_tree) (rules_of bb_members).
Proof.
  exact (eligible_leaves_are_members 32 1 0 bb_members bb_tree
           bb_cohort_tree).
Qed.

(* Path pins: every leaf path spells the member's own item prefix of length
   leaf_depth (FV-1 (b) transported; depths 3, 3, 2). *)
Theorem bang_paths :
  leaf_entries [] bang_tree
  = [(bang_out, 3, [0; 1; 2]);
     (bang_2plus, 3, [0; 1; 3]);
     (bang_empty, 2, [0; 2])].
Proof. vm_compute. reflexivity. Qed.

Lemma bang_first_item :
  forall m, In m bang_members -> firstn 1 (m_items m) = [0].
Proof.
  intros m Hin.
  destruct Hin as [H | [H | [H | []]]]; subst m; reflexivity.
Qed.

Theorem bang_path_law :
  forall m d path,
    In (m, d, path) (leaf_entries [] bang_tree) ->
    path = firstn d (m_items m) /\ 1 <= d /\ d <= length (m_items m).
Proof.
  intros m d path Hin.
  exact (root_path_items 32 0 bang_members bang_tree [] bang_cohort_tree
           bang_first_item m d path Hin).
Qed.

(* CONCATENATION AT COMMIT (FV-2 (2) — "spine-consumed ++ member-tail =
   member items" carries verbatim): generic over any depth-1 build, then
   instantiated. *)
Theorem spine_member_concatenation :
  forall fuel edge ms t acc m d path,
    build_node fuel 1 edge ms = Some (t, acc) ->
    (forall m', In m' ms -> firstn 1 (m_items m') = [edge]) ->
    In (m, d, path) (leaf_entries [] t) ->
    path ++ skipn d (m_items m) = m_items m.
Proof.
  intros fuel edge ms t acc m d path HB Hfirst Hin.
  destruct (root_path_items fuel edge ms t acc HB Hfirst m d path Hin)
    as [Hpath [Hd1 Hd2]].
  subst path.
  apply firstn_skipn.
Qed.

Theorem bang_concatenation :
  forall m d path,
    In (m, d, path) (leaf_entries [] bang_tree) ->
    path ++ skipn d (m_items m) = m_items m.
Proof.
  intros m d path Hin.
  exact (spine_member_concatenation 32 0 bang_members bang_tree [] m d path
           bang_cohort_tree bang_first_item Hin).
Qed.

(* Post-spine remainder pins: rule 8/9 truncate at their rep (remainder in
   the member's own machinery); rules 4/5/6/7 are tail-complete at the leaf. *)
Theorem bang_remainders :
  has_remainder bang_out 3 = false
  /\ has_remainder bang_empty 2 = false
  /\ has_remainder bang_2plus 3 = true.
Proof. vm_compute. repeat split. Qed.

Theorem bb_remainders :
  has_remainder bb_out 3 = false
  /\ has_remainder bb_empty 2 = false
  /\ has_remainder bb_2plus 3 = true.
Proof. vm_compute. repeat split. Qed.

(* COMMIT COORDINATE PINS — the committed P1 values (factoring.rs
   @4954-4971): r4 = MixfixRun{4,0,0,1}, r6 = MixfixRun{6,2,0,2},
   r8 = MixfixRun{8,0,0,1}; the !! twins at rules 5/7/9. *)
Theorem bang_commits :
  mixfix_finalize is_op_code bang_out 3 = CMixfixRun 4 0 0 1
  /\ mixfix_finalize is_op_code bang_empty 2 = CMixfixRun 6 2 0 2
  /\ mixfix_finalize is_op_code bang_2plus 3 = CMixfixRun 8 0 0 1.
Proof. vm_compute. repeat split. Qed.

Theorem bb_commits :
  mixfix_finalize is_op_code bb_out 3 = CMixfixRun 5 0 0 1
  /\ mixfix_finalize is_op_code bb_empty 2 = CMixfixRun 7 2 0 2
  /\ mixfix_finalize is_op_code bb_2plus 3 = CMixfixRun 9 0 0 1.
Proof. vm_compute. repeat split. Qed.

(* The coordinate LAWS applied to the census members (not just computed):
   rule 6 is the nullary law at depth 2; rule 4 is the operand law with
   pre = ["("], operand at index 1, depth 3 ⇒ sub_pos = 3 - 1 - 1 = 1. *)
Theorem bang_empty_commit_via_law :
  mixfix_finalize is_op_code bang_empty 2 = CMixfixRun 6 2 0 2.
Proof.
  apply (mixfix_commit_nullary is_op_code bang_empty 2).
  - repeat constructor.
  - simpl. lia.
Qed.

Theorem bang_out_commit_via_law :
  mixfix_finalize is_op_code bang_out 3 = CMixfixRun 4 0 0 1.
Proof.
  change (m_items bang_out) with ([0] ++ 1 :: [2]).
  rewrite (mixfix_commit_operand is_op_code bang_out [0] 1 [2] 3);
    [reflexivity | reflexivity | repeat constructor | reflexivity
    | repeat constructor | simpl; lia | simpl; lia].
Qed.

(* The SpinePosMap::Mixfix pin (the r8 committed value @4972-4978):
   coords_at_depth = [(2,0,0); (2,0,1); (0,0,0); (0,0,1)]. *)
Theorem bang_2plus_pos_map :
  coords_of is_op_code (m_items bang_2plus)
  = [(2, 0, 0); (2, 0, 1); (0, 0, 0); (0, 0, 1)].
Proof. vm_compute. reflexivity. Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (3) GUARD-DEATH PARTITION (FV-2'' (3)) — the divergence children
   partition the live members by their next item, so a death at a
   divergence edge kills EXACTLY the members whose own per-member guards
   (`__mixfix_literal_targets` membership on the same expected text) would
   kill.
   ═══════════════════════════════════════════════════════════════════════ *)

(* Divergence 1 (depth-1 items): operand (1) vs ")" (2). *)
Theorem bang_divergence_1 :
  partition_left 1 bang_members [] []
  = ([(1, [bang_out; bang_2plus]); (2, [bang_empty])], []).
Proof. vm_compute. reflexivity. Qed.

(* Divergence 2 (depth-2 items over the operand part): ")" (2) vs "," (3). *)
Theorem bang_divergence_2 :
  partition_left 2 [bang_out; bang_2plus] [] []
  = ([(2, [bang_out]); (3, [bang_2plus])], []).
Proof. vm_compute. reflexivity. Qed.

(* A death at the ")" edge of divergence 1 kills exactly {rule 6} — the
   members whose next item is ")". *)
Theorem bang_death_div1_close_kills_exactly_r6 :
  forall m,
    In m [bang_empty]
    <-> (In m bang_members /\ nth_error (m_items m) 1 = Some 2).
Proof.
  intro m.
  apply (divergence_partition 1 bang_members
           [(1, [bang_out; bang_2plus]); (2, [bang_empty])] [] 2
           [bang_empty] bang_divergence_1).
  right. left. reflexivity.
Qed.

(* A death at the operand edge of divergence 1 kills exactly {rules 4, 8}. *)
Theorem bang_death_div1_operand_kills_exactly_r4_r8 :
  forall m,
    In m [bang_out; bang_2plus]
    <-> (In m bang_members /\ nth_error (m_items m) 1 = Some 1).
Proof.
  intro m.
  apply (divergence_partition 1 bang_members
           [(1, [bang_out; bang_2plus]); (2, [bang_empty])] [] 1
           [bang_out; bang_2plus] bang_divergence_1).
  left. reflexivity.
Qed.

(* At divergence 2: ")" kills exactly {rule 4}; "," kills exactly {rule 8}. *)
Theorem bang_death_div2_close_kills_exactly_r4 :
  forall m,
    In m [bang_out]
    <-> (In m [bang_out; bang_2plus] /\ nth_error (m_items m) 2 = Some 2).
Proof.
  intro m.
  apply (divergence_partition 2 [bang_out; bang_2plus]
           [(2, [bang_out]); (3, [bang_2plus])] [] 2 [bang_out]
           bang_divergence_2).
  left. reflexivity.
Qed.

Theorem bang_death_div2_sep_kills_exactly_r8 :
  forall m,
    In m [bang_2plus]
    <-> (In m [bang_out; bang_2plus] /\ nth_error (m_items m) 2 = Some 3).
Proof.
  intro m.
  apply (divergence_partition 2 [bang_out; bang_2plus]
           [(2, [bang_out]); (3, [bang_2plus])] [] 3 [bang_2plus]
           bang_divergence_2).
  right. left. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (4) THE TWO-ARM CAR CONTRACT (D-3 / A-M1) — the fork-branch
   ConsumeAtAndReplace symbol semantics. Symbols are modeled by their rule
   component (the spine marker = the spine id; a member marker = its rule).
   ═══════════════════════════════════════════════════════════════════════ *)

(* Classic (wpda_walker.rs @17361-17371): conditional
   `cursor_gss_replace_top_auto` on symbol INEQUALITY — the identity case
   performs NO replace (`replace_top_with_edge_id_kind` has no identity
   short-circuit; an unconditional replace would mint a new GSS node and
   perturb the ROOT-A lattice self-replace forks). *)
Definition classic_car_child_top (parent_top br_sym : nat) : nat :=
  if parent_top =? br_sym then parent_top else br_sym.

Definition classic_replace_performed (parent_top br_sym : nat) : bool :=
  negb (parent_top =? br_sym).

(* Pure (@31091-31110): the descriptor's `cur_sym` takes `br_symbol`
   unconditionally (assignment — no allocation observable exists on the
   descriptor side, so no conditional is needed). *)
Definition pure_car_child_cur_sym (br_sym : nat) : nat := br_sym.

(* THE TWO-ARM AGREEMENT: both arms yield the SAME symbol observable —
   the conditional and the assignment differ only in GSS-node allocation
   (classic), never in the committed identity. *)
Theorem two_arm_car_agree :
  forall parent_top br_sym,
    classic_car_child_top parent_top br_sym
    = pure_car_child_cur_sym br_sym.
Proof.
  intros parent_top br_sym.
  unfold classic_car_child_top, pure_car_child_cur_sym.
  destruct (parent_top =? br_sym) eqn:E.
  - apply Nat.eqb_eq in E. exact E.
  - reflexivity.
Qed.

(* Every pre-F5-2 fork-CAR emitter passes the SAME marker
   (`__checked_literal_consume!` — rg-verified sole emitter): the new
   contract is the historical "No GSS mutation" no-op there. *)
Theorem pre_f52_emitters_no_gss_mutation :
  forall top,
    classic_replace_performed top top = false
    /\ classic_car_child_top top top = top.
Proof.
  intro top.
  unfold classic_replace_performed, classic_car_child_top.
  rewrite Nat.eqb_refl.
  split; reflexivity.
Qed.

(* A COMMIT branch (member symbol ≠ spine symbol) performs the real replace
   in classic and lands the member symbol in both arms. *)
Theorem commit_branch_replaces :
  forall spine_top member_sym,
    spine_top <> member_sym ->
    classic_replace_performed spine_top member_sym = true
    /\ classic_car_child_top spine_top member_sym = member_sym.
Proof.
  intros spine_top member_sym Hneq.
  unfold classic_replace_performed, classic_car_child_top.
  destruct (spine_top =? member_sym) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - split; reflexivity.
Qed.

(* Fork application over a branch list: each child's symbol is a function
   of the PARENT's top and its OWN branch alone — a commit branch replaces
   the spine symbol on ITS child only; Advance children (the operand
   descent) and the parent keep the spine top. *)
Inductive fbranch : Type :=
| FbCAR (sym : nat)     (* ConsumeAtAndReplace {next_pos} with branch.symbol *)
| FbAdvance.            (* Advance — no symbol change (the descent branch) *)

Definition fchild_top (parent_top : nat) (b : fbranch) : nat :=
  match b with
  | FbCAR s => classic_car_child_top parent_top s
  | FbAdvance => parent_top
  end.

Definition fork_children_tops (parent_top : nat) (bs : list fbranch)
  : list nat :=
  map (fchild_top parent_top) bs.

(* Sibling isolation: child i's symbol depends only on (parent, branch i). *)
Theorem fork_child_local :
  forall parent_top bs i b,
    nth_error bs i = Some b ->
    nth_error (fork_children_tops parent_top bs) i
    = Some (fchild_top parent_top b).
Proof.
  intros parent_top bs i b H.
  unfold fork_children_tops.
  rewrite nth_error_map, H.
  reflexivity.
Qed.

(* An Advance sibling of a commit keeps the spine top verbatim. *)
Theorem advance_sibling_keeps_spine :
  forall parent_top, fchild_top parent_top FbAdvance = parent_top.
Proof. reflexivity. Qed.

(* THE EMITTED DIVERGENCE FORKS (spine id 0xF803 = 63491): divergence 1 =
   {operand-descent Advance FIRST (trie child order), rule-6 commit CAR};
   divergence 2 = {rule-4 CAR on ")", rule-8 CAR on ","}. The commit
   children carry the MEMBER markers; the descent child keeps the SPINE. *)
Theorem bang_div1_fork_tops :
  fork_children_tops 63491 [FbAdvance; FbCAR 6] = [63491; 6].
Proof. vm_compute. reflexivity. Qed.

Theorem bang_div2_fork_tops :
  fork_children_tops 63491 [FbCAR 4; FbCAR 8] = [4; 8].
Proof. vm_compute. reflexivity. Qed.

Theorem bb_div1_fork_tops :
  fork_children_tops 63492 [FbAdvance; FbCAR 7] = [63492; 7].
Proof. vm_compute. reflexivity. Qed.

Theorem bb_div2_fork_tops :
  fork_children_tops 63492 [FbCAR 5; FbCAR 9] = [5; 9].
Proof. vm_compute. reflexivity. Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (5) FV-3b(b) TRANSPORT — the mixfix machine tables. Spine node ids:
   1 = MLR{SPINE, kind 2, completed 0, sub_pos 0} (post-trigger);
   2 = MLR{SPINE, 2, 0, 1} (divergence 1); 3 = MLR{SPINE, 0, 0, 0}
   (divergence 2 — the post-operand Unwinding re-entry). Member positions
   are FLAT walk indices (the typed coordinates are pinned by
   `mixfix_finalize` above): r6 commits AT its final nullary cursor (6,2);
   r4 at (4,1) = its exhausted following (the arm's own Pop → fire);
   r8 at (8,1) then runs its rep tail (8,1)→(8,2)→(8,3) final (the
   CollectionLoop machinery, abstracted as member steps). FS1: both
   commits ride consuming edges (")" / ","); the operand descent is the
   spine edge 2→3, not a commit.
   ═══════════════════════════════════════════════════════════════════════ *)

Definition mx_spine_edge (a b : nat) : bool :=
  ((a =? 1) && (b =? 2))      (* the "(" chain consume *)
  || ((a =? 2) && (b =? 3)).  (* the operand descent + Unwinding re-entry *)

Definition mx_commit_edge (n r p : nat) : bool :=
  ((n =? 2) && (r =? 6) && (p =? 2))     (* divergence 1: ")" ⇒ r6 commit *)
  || ((n =? 3) && (r =? 4) && (p =? 1))  (* divergence 2: ")" ⇒ r4 commit *)
  || ((n =? 3) && (r =? 8) && (p =? 1)). (* divergence 2: "," ⇒ r8 commit *)

Definition mx_member_edge (a b : nat * nat) : bool :=
  match a, b with
  | (r, p), (r', p') =>
      ((r =? 8) && (p =? 1) && (r' =? 8) && (p' =? 2))
      || ((r =? 8) && (p =? 2) && (r' =? 8) && (p' =? 3))
  end.

Definition mx_member_final (a : nat * nat) : bool :=
  match a with
  | (r, p) =>
      ((r =? 6) && (p =? 2))
      || ((r =? 4) && (p =? 1))
      || ((r =? 8) && (p =? 3))
  end.

Definition mx_table : table :=
  MkTable mx_spine_edge mx_commit_edge mx_member_edge mx_member_final.

(* The !! twin (rules 5/7/9). *)
Definition mxbb_commit_edge (n r p : nat) : bool :=
  ((n =? 2) && (r =? 7) && (p =? 2))
  || ((n =? 3) && (r =? 5) && (p =? 1))
  || ((n =? 3) && (r =? 9) && (p =? 1)).

Definition mxbb_member_edge (a b : nat * nat) : bool :=
  match a, b with
  | (r, p), (r', p') =>
      ((r =? 9) && (p =? 1) && (r' =? 9) && (p' =? 2))
      || ((r =? 9) && (p =? 2) && (r' =? 9) && (p' =? 3))
  end.

Definition mxbb_member_final (a : nat * nat) : bool :=
  match a with
  | (r, p) =>
      ((r =? 7) && (p =? 2))
      || ((r =? 5) && (p =? 1))
      || ((r =? 9) && (p =? 3))
  end.

Definition mxbb_table : table :=
  MkTable mx_spine_edge mxbb_commit_edge mxbb_member_edge mxbb_member_final.

(* The A9 id-space pins (the ltb/vm_compute route — `unfold; lia` hits the
   Init.Nat.of_num_uint decimal coercion, see the ib_table_wf note in
   PureCommitFoldIntegrityAccept). *)
Theorem mixfix_spine_ids_in_spine_space :
  (SPINE_RULE_BASE <=? 63491) = true
  /\ (SPINE_RULE_BASE <=? 63492) = true
  /\ (63491 =? SPINE_RULE_BASE + 3) = true
  /\ (63492 =? SPINE_RULE_BASE + 4) = true.
Proof. vm_compute. repeat split. Qed.

(* FAILED STRATEGY (do not re-attempt): `repeat constructor` — after the
   Forall constructors it greedily attacks the `r < SPINE_RULE_BASE`
   subgoals with le_S, descending a 63488-deep constructor chain (the
   compile is OOM-killed). Apply Forall_cons/Forall_nil explicitly and
   close each bound through the boolean reflection + vm_compute route. *)
Theorem mixfix_member_rules_below_base :
  Forall (fun r => r < SPINE_RULE_BASE) [4; 5; 6; 7; 8; 9].
Proof.
  repeat apply Forall_cons; try apply Forall_nil;
    apply Nat.ltb_lt; vm_compute; reflexivity.
Qed.

Lemma mx_table_wf : wf_table mx_table.
Proof.
  unfold wf_table.
  intros n r p H.
  unfold mx_table in H; cbn in H; unfold mx_commit_edge in H.
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

Lemma mxbb_table_wf : wf_table mxbb_table.
Proof.
  unfold wf_table.
  intros n r p H.
  unfold mxbb_table in H; cbn in H; unfold mxbb_commit_edge in H.
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

Lemma mx_table_wf_member_rules : wf_member_rules mx_table.
Proof.
  unfold wf_member_rules.
  intros r p r' p' H.
  unfold mx_table in H; cbn in H; unfold mx_member_edge in H.
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

Lemma mxbb_table_wf_member_rules : wf_member_rules mxbb_table.
Proof.
  unfold wf_member_rules.
  intros r p r' p' H.
  unfold mxbb_table in H; cbn in H; unfold mxbb_member_edge in H.
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

(* DIVERGENCE 1 IS THE F5-1 FORK SHAPE: node 2 carries BOTH the spine
   successor (the operand descent) AND a commit edge (the r6 nullary
   commit) — `accept_fork_at`, with both branches existing as machine
   steps (the shipped fork theorems transport with zero new obligations). *)
Theorem mx_divergence1_is_accept_fork : accept_fork_at mx_table 2.
Proof.
  split.
  - exists 3. reflexivity.
  - exists 6, 2. reflexivity.
Qed.

(* DIVERGENCE 2 IS THE ALL-COMMITS NODE: node 3 has NO spine successor —
   every branch leaves spine-land (`all_accepts_node`). *)
Theorem mx_divergence2_all_commits : all_accepts_node mx_table 3.
Proof.
  split.
  - intro n'.
    unfold mx_table; cbn; unfold mx_spine_edge.
    reflexivity.
  - exists 4, 1. reflexivity.
Qed.

(* THE TRANSPORTED LAWS: every spine→Pop path in the mixfix tables passes
   EXACTLY ONE commit, keyed by a REAL member rule (< SPINE_RULE_BASE) —
   commit_precedes_final_pop + pop_key_below_base on the mixfix surface
   (the kind-2 exit commit at divergence 1 and the kind-0 commits at
   divergence 2 both dominate every Pop). *)
Theorem mx_any_spine_path_one_commit :
  forall c c' k rk pw,
    steps mx_table c c' k ->
    is_spine (g_coord c) = true ->
    packing_of mx_table c' = Some (rk, pw) ->
    k = 1 /\ rk < SPINE_RULE_BASE.
Proof.
  intros c c' k rk pw H Hs Hpack.
  split.
  - eapply commit_precedes_final_pop; [exact H | exact Hs | exact Hpack].
  - eapply pop_key_below_base;
      [exact mx_table_wf | exact mx_table_wf_member_rules
      | exact H | exact Hs | exact Hpack].
Qed.

Theorem mxbb_any_spine_path_one_commit :
  forall c c' k rk pw,
    steps mxbb_table c c' k ->
    is_spine (g_coord c) = true ->
    packing_of mxbb_table c' = Some (rk, pw) ->
    k = 1 /\ rk < SPINE_RULE_BASE.
Proof.
  intros c c' k rk pw H Hs Hpack.
  split.
  - eapply commit_precedes_final_pop; [exact H | exact Hs | exact Hpack].
  - eapply pop_key_below_base;
      [exact mxbb_table_wf | exact mxbb_table_wf_member_rules
      | exact H | exact Hs | exact Hpack].
Qed.

(* ── The three !-lineage receipts (explicit `steps` derivations; every
      spine arm folds lex_one = w_one — factoring.rs mixfix_spine_step_arm
      emits `weight: lex_one()` on every chain/divergence/commit edge,
      D-6). ── *)

(* x!() — the NULLARY lineage: 1 →chain "("→ 2 →COMMIT r6 (rides ")")→
   (6,2), which IS final (the member's kind-2 exit → pop→fire). *)
Theorem mx_nullary_lineage_receipt :
  steps mx_table (MkCfg 0 [] (CSpine 1) [])
                 (MkCfg 0 [w_one] (CMember 6 2) []) 1
  /\ packing_of mx_table (MkCfg 0 [w_one] (CMember 6 2) [])
     = Some (6, w_one).
Proof.
  split.
  - eapply StepsChain;
      [exact (PSpineChain mx_table 0 [] [] 1 2 [] eq_refl)
      | reflexivity | reflexivity |].
    eapply StepsCommit;
      [exact (PCommit mx_table 0 [w_one] [] 2 6 2 eq_refl)
      | reflexivity | reflexivity |].
    apply StepsRefl.
  - vm_compute. reflexivity.
Qed.

(* x!(0) — the SCALAR lineage: 1 →chain→ 2 →chain (operand descent)→ 3
   →COMMIT r4 (rides ")")→ (4,1) final (following exhausted → Pop→fire). *)
Theorem mx_scalar_lineage_receipt :
  steps mx_table (MkCfg 0 [] (CSpine 1) [])
                 (MkCfg 0 [w_one; w_one] (CMember 4 1) []) 1
  /\ packing_of mx_table (MkCfg 0 [w_one; w_one] (CMember 4 1) [])
     = Some (4, w_one).
Proof.
  split.
  - eapply StepsChain;
      [exact (PSpineChain mx_table 0 [] [] 1 2 [] eq_refl)
      | reflexivity | reflexivity |].
    eapply StepsChain;
      [exact (PSpineChain mx_table 0 [w_one] [] 2 3 [] eq_refl)
      | reflexivity | reflexivity |].
    eapply StepsCommit;
      [exact (PCommit mx_table 0 [w_one; w_one] [] 3 4 1 eq_refl)
      | reflexivity | reflexivity |].
    apply StepsRefl.
  - vm_compute. reflexivity.
Qed.

(* x!(0,1) — the POLYADIC lineage: 1 →chain→ 2 →chain→ 3 →COMMIT r8
   (rides ",")→ (8,1) →member (the rep tail)→ (8,2) →member→ (8,3) final —
   still exactly ONE commit; the post-spine remainder runs in the member's
   own machinery. *)
Theorem mx_polyadic_lineage_receipt :
  steps mx_table (MkCfg 0 [] (CSpine 1) [])
        (MkCfg 0 [w_one; w_one; w_one; w_one] (CMember 8 3) []) 1
  /\ packing_of mx_table
       (MkCfg 0 [w_one; w_one; w_one; w_one] (CMember 8 3) [])
     = Some (8, w_one).
Proof.
  split.
  - eapply StepsChain;
      [exact (PSpineChain mx_table 0 [] [] 1 2 [] eq_refl)
      | reflexivity | reflexivity |].
    eapply StepsChain;
      [exact (PSpineChain mx_table 0 [w_one] [] 2 3 [] eq_refl)
      | reflexivity | reflexivity |].
    eapply StepsCommit;
      [exact (PCommit mx_table 0 [w_one; w_one] [] 3 8 1 eq_refl)
      | reflexivity | reflexivity |].
    eapply StepsMember;
      [exact (PMemberStep mx_table 0 [w_one; w_one] [] 8 1 8 2 w_one []
                eq_refl)
      | reflexivity |].
    eapply StepsMember;
      [exact (PMemberStep mx_table 0 [w_one; w_one; w_one] [] 8 2 8 3 w_one
                [] eq_refl)
      | reflexivity |].
    apply StepsRefl.
  - vm_compute. reflexivity.
Qed.

(* x!!() — the !! nullary twin (the tables are isomorphic; one receipt
   pins the twin's coordinates). *)
Theorem mxbb_nullary_lineage_receipt :
  steps mxbb_table (MkCfg 0 [] (CSpine 1) [])
                   (MkCfg 0 [w_one] (CMember 7 2) []) 1
  /\ packing_of mxbb_table (MkCfg 0 [w_one] (CMember 7 2) [])
     = Some (7, w_one).
Proof.
  split.
  - eapply StepsChain;
      [exact (PSpineChain mxbb_table 0 [] [] 1 2 [] eq_refl)
      | reflexivity | reflexivity |].
    eapply StepsCommit;
      [exact (PCommit mxbb_table 0 [w_one] [] 2 7 2 eq_refl)
      | reflexivity | reflexivity |].
    apply StepsRefl.
  - vm_compute. reflexivity.
Qed.

(* Both branches of divergence 1 EXIST from the same configuration (the
   F5-1 fork theorem instantiated at the mixfix table). *)
Theorem mx_div1_both_branches :
  pstep mx_table (MkCfg 0 [w_one] (CSpine 2) [])
                 (MkCfg 0 ([w_one] ++ [w_one]) (CSpine 3) [])
  /\ pstep mx_table (MkCfg 0 [w_one] (CSpine 2) [])
                    (MkCfg 0 [w_one] (CMember 6 2) []).
Proof.
  exact (accept_fork_both_branches mx_table 0 [w_one] [] 2 3 6 2
           eq_refl eq_refl).
Qed.

(* The commit transition preserves (u, w, store) — ReplacePreservesUW at
   the mixfix commit (the D-3 Replace carries no weight, A-M2: commit
   edges are lex_one; the shipped theorem transports verbatim). *)
Theorem mx_commit_preserves_uw :
  forall u wl st c',
    pstep mx_table (MkCfg u wl (CSpine 2) st) c' ->
    (exists r p, g_coord c' = CMember r p) ->
    g_u c' = u /\ g_w c' = wl /\ g_store c' = st.
Proof.
  intros u wl st c' Hstep Hm.
  exact (replace_preserves_uw mx_table u wl st 2 c' Hstep Hm).
Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (6) D-1 FULL-ADMISSION FLOOR — `min_l_bp >= cur_bp` ⟺ every member's own
   `l_bp >= cur_bp`. The spine branch NEVER resurrects a floor-blocked
   member (FS-M3's refutation), and the fallback (partial windows) is the
   verbatim member loop.
   ═══════════════════════════════════════════════════════════════════════ *)

Fixpoint fold_min (h : nat) (t : list nat) : nat :=
  match t with
  | [] => h
  | x :: rest => Nat.min x (fold_min h rest)
  end.

Theorem full_admission_iff :
  forall h t cur,
    cur <= fold_min h t <-> (cur <= h /\ Forall (fun l => cur <= l) t).
Proof.
  intros h t cur.
  induction t as [| x rest IH]; simpl.
  - split; [intro H; split; [exact H | constructor] | intros [H _]; exact H].
  - split.
    + intro H.
      apply Nat.min_glb_iff in H. destruct H as [Hx Hrest].
      apply IH in Hrest. destruct Hrest as [Hh Hf].
      split; [exact Hh | constructor; assumption].
    + intros [Hh Hf]. inversion Hf; subst.
      apply Nat.min_glb; [assumption |]. apply IH. split; assumption.
Qed.

(* No floor-blocked member rides the spine: if ANY member is blocked at
   cur_bp, the spine branch is NOT admitted. *)
Theorem no_floor_blocked_resurrection :
  forall h t cur l,
    In l (h :: t) ->
    l < cur ->
    ~ cur <= fold_min h t.
Proof.
  intros h t cur l Hin Hblocked Hadm.
  apply full_admission_iff in Hadm.
  destruct Hadm as [Hh Hf].
  destruct Hin as [Heq | Hin'].
  - subst l. lia.
  - rewrite Forall_forall in Hf.
    specialize (Hf l Hin'). lia.
Qed.

(* The rhocalc floors: `!` l_bps [2; 6; 10] (min 2 = the emitted
   min_l_bp), `!!` [4; 8; 12] (min 4) — the committed P1 pins. *)
Theorem bang_min_l_bp : fold_min 2 [6; 10] = 2.
Proof. vm_compute. reflexivity. Qed.

Theorem bb_min_l_bp : fold_min 4 [8; 12] = 4.
Proof. vm_compute. reflexivity. Qed.

(* The partial-window receipt (cur_bp = 7, unreachable in the bundled
   corpus per A-M5 but the fallback is receipt-checkable): the spine is
   REFUSED and the verbatim member loop admits exactly rule 8 (l_bp 10). *)
Theorem bang_partial_window_cur7 :
  (7 <=? fold_min 2 [6; 10]) = false
  /\ map (fun l => 7 <=? l) [2; 6; 10] = [false; false; true].
Proof. vm_compute. split; reflexivity. Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (7) K-A FOLD-COUNT (FV-2''-note; the F3 red-team F8 warning: restate
   the count map, don't hand-wave). Per ACCEPTED READING the consumed-fold
   count is stance-invariant: OFF folds 1 (trigger) + |items(m)| (the
   member's own arms); ON folds 1 (trigger) + d (spine arms) +
   (|items(m)| - d) (member tail) — equal. K-A LATENESS therefore only
   DECREASES, and only on DEAD branches (members killed at a divergence
   stop consuming there instead of at their own guard).
   ═══════════════════════════════════════════════════════════════════════ *)

Theorem mixfix_fold_count_per_reading :
  forall (m : member) (d : nat),
    d <= length (m_items m) ->
    S (length (firstn d (m_items m)) + length (skipn d (m_items m)))
    = S (length (m_items m)).
Proof.
  intros m d Hd.
  f_equal.
  apply fold_count_items.
  exact Hd.
Qed.

(* The attempt-level marker-push economy: the OFF fan pushes one marker
   branch per member (3); the ON fan pushes ONE spine branch (the forced
   width-1 Fork, D-2) — the RD-U1 receipt "event_width 3 -> 1". *)
Theorem mixfix_fan_width_economy :
  length [4; 6; 8] = 3 /\ length [63491] = 1
  /\ length [5; 7; 9] = 3 /\ length [63492] = 1.
Proof. vm_compute. repeat split. Qed.

(* ═══════════════════════════════════════════════════════════════════════
   (8) FV-3b(c) HONEST CARVE-OUT — the C8-mixfix channel. The mixfix
   trigger stamp is REAL-COST (BP_TIER_MIXFIX = 0.20 ≠ 0), so the F3
   zero-cost wash does NOT erase it: the identity FIELD freezes at the
   trigger (left-projection), and OFF stamps the member where ON stamps
   the MIN member. What IS preserved: the fold's COST component (cost is
   additive through wtimes, so equal-cost triggers give equal fold costs).
   What is NOT: the frozen rule field on nullary tails (the ONE
   pre-classified ELECTED-W movement, `bitnot (a)!()` rule 6 -> rule 4,
   elected AST + reading multisets INVARIANT both arms — the empirical C8
   A/B receipt, logs_s1f5_2/, cited not proven). Payload-window packings
   stay member-determined POST-commit exactly as PureCommitFoldIntegrity
   states (packing_weight_member_determined — its all-idlike pre-commit
   premise holds on the packing channel because pending is consumed at
   EVERY fire, A-M5 §3d(3); the trigger stamp lives on the CURSOR/carrier
   channel modeled here).
   ═══════════════════════════════════════════════════════════════════════ *)

(* Cost is additive through wtimes UNCONDITIONALLY (idlike means zero
   cost, so the projections preserve the sum). *)
Theorem wtimes_cost_additive :
  forall a b, w_cost (wtimes a b) = w_cost a + w_cost b.
Proof.
  intros a b.
  unfold wtimes, idlike.
  destruct (w_cost a =? 0) eqn:Ea.
  - apply Nat.eqb_eq in Ea. simpl. lia.
  - destruct (w_cost b =? 0) eqn:Eb.
    + apply Nat.eqb_eq in Eb. simpl. lia.
    + reflexivity.
Qed.

(* FAILED STRATEGY (do not re-attempt): a closed-form
   `fold cost = acc + sum (map w_cost ws)` via fold_left Nat.add needs a
   fold_left accumulator-shift lemma the goal never actually requires —
   the C8 statement only needs fold costs to AGREE across two same-cost
   seeds, which the direct two-accumulator induction below gives without
   the arithmetic detour. *)
Lemma fold_cost_step :
  forall ws a b,
    w_cost a = w_cost b ->
    w_cost (fold_left wtimes ws a) = w_cost (fold_left wtimes ws b).
Proof.
  intros ws.
  induction ws as [| x rest IH]; intros a b Hc; simpl.
  - exact Hc.
  - apply IH.
    rewrite !wtimes_cost_additive.
    lia.
Qed.

(* THE COST-TOTAL INVARIANCE: substituting the min-member stamp for the
   member stamp at the trigger (equal 0.20 cost, different rule field)
   leaves every downstream fold COST unchanged. *)
Theorem mixfix_c8_cost_totals_invariant :
  forall (c : nat) (r_member r_min : nat) (ws : list w),
    w_cost (fold_left wtimes ws (MkW c (Some r_member)))
    = w_cost (fold_left wtimes ws (MkW c (Some r_min))).
Proof.
  intros c r_member r_min ws.
  apply fold_cost_step.
  reflexivity.
Qed.

(* THE STAMP FREEZE: a REAL-COST trigger stamp survives every later
   composition on the left (cost stays nonzero by additivity, and wtimes
   left-projects the stamp past a real-cost left operand). *)
Lemma wtimes_real_left_stamp :
  forall a b, w_cost a <> 0 -> w_stamp (wtimes a b) = w_stamp a.
Proof.
  intros a b Ha.
  unfold wtimes, idlike.
  destruct (w_cost a =? 0) eqn:Ea.
  - apply Nat.eqb_eq in Ea. contradiction.
  - destruct (w_cost b =? 0) eqn:Eb; reflexivity.
Qed.

Lemma wtimes_real_left_cost_nonzero :
  forall a b, w_cost a <> 0 -> w_cost (wtimes a b) <> 0.
Proof.
  intros a b Ha.
  rewrite wtimes_cost_additive.
  lia.
Qed.

Theorem mixfix_stamp_freezes :
  forall ws acc,
    w_cost acc <> 0 ->
    w_stamp (fold_left wtimes ws acc) = w_stamp acc.
Proof.
  intros ws.
  induction ws as [| x rest IH]; intros acc Hacc; simpl.
  - reflexivity.
  - rewrite (IH (wtimes acc x));
      [apply wtimes_real_left_stamp; exact Hacc
      | apply wtimes_real_left_cost_nonzero; exact Hacc].
Qed.

(* THE PRE-CLASSIFIED DELTA as a theorem: the ON fold carries the MIN
   member's rule field where the OFF fold carries the member's own — they
   differ exactly when the member is not the min (the nullary rows'
   ELECTED-W movement), while the costs agree (the previous theorem). *)
Theorem mixfix_c8_stamp_min_member_substitution :
  forall (c : nat) (r_member r_min : nat) (ws : list w),
    c <> 0 ->
    w_stamp (fold_left wtimes ws (MkW c (Some r_member))) = Some r_member
    /\ w_stamp (fold_left wtimes ws (MkW c (Some r_min))) = Some r_min.
Proof.
  intros c r_member r_min ws Hc.
  split; rewrite mixfix_stamp_freezes; simpl; try reflexivity; exact Hc.
Qed.

(* THE PLAN-§3(d) IMPOSSIBILITY: no single spine stamp reproduces two
   distinct member stamps — OFF stamps two consumption windows with
   per-member identities from one fork; a width-1 branch has ONE stamp. *)
Theorem single_stamp_cannot_reproduce_two_members :
  forall (s : option nat) (r1 r2 : nat),
    r1 <> r2 ->
    ~ (s = Some r1 /\ s = Some r2).
Proof.
  intros s r1 r2 Hneq [H1 H2].
  subst s.
  inversion H2.
  contradiction.
Qed.

(* The concrete rhocalc instance of the delta: the `!` cohort's nullary
   member (rule 6) folds to stamp Some 4 (the min member) under ON where
   OFF folds to Some 6 — cost equal either way (the `bitnot (a)!()`
   sign-off row's exact shape; 20 here stands for the 0.20 tier cost). *)
Theorem bang_nullary_stamp_delta_instance :
  w_stamp (fold_left wtimes [w_one; w_one] (MkW 20 (Some 6))) = Some 6
  /\ w_stamp (fold_left wtimes [w_one; w_one] (MkW 20 (Some 4))) = Some 4
  /\ w_cost (fold_left wtimes [w_one; w_one] (MkW 20 (Some 6)))
     = w_cost (fold_left wtimes [w_one; w_one] (MkW 20 (Some 4))).
Proof. vm_compute. repeat split. Qed.

(* ── Assumption audit — every line must print "Closed under the global
      context". ── *)
Print Assumptions coords_of_length.
Print Assumptions coords_nullary_nth.
Print Assumptions coords_single_part_pre.
Print Assumptions coords_single_part_post.
Print Assumptions coords_of_prefix_agreement.
Print Assumptions mixfix_finalize_total.
Print Assumptions mixfix_commit_nullary.
Print Assumptions mixfix_commit_operand.
Print Assumptions bang_cohort_tree.
Print Assumptions bb_cohort_tree.
Print Assumptions bang_leaves.
Print Assumptions bb_leaves.
Print Assumptions bang_leaf_bijection.
Print Assumptions bb_leaf_bijection.
Print Assumptions bang_paths.
Print Assumptions bang_path_law.
Print Assumptions spine_member_concatenation.
Print Assumptions bang_concatenation.
Print Assumptions bang_remainders.
Print Assumptions bb_remainders.
Print Assumptions bang_commits.
Print Assumptions bb_commits.
Print Assumptions bang_empty_commit_via_law.
Print Assumptions bang_out_commit_via_law.
Print Assumptions bang_2plus_pos_map.
Print Assumptions bang_divergence_1.
Print Assumptions bang_divergence_2.
Print Assumptions bang_death_div1_close_kills_exactly_r6.
Print Assumptions bang_death_div1_operand_kills_exactly_r4_r8.
Print Assumptions bang_death_div2_close_kills_exactly_r4.
Print Assumptions bang_death_div2_sep_kills_exactly_r8.
Print Assumptions two_arm_car_agree.
Print Assumptions pre_f52_emitters_no_gss_mutation.
Print Assumptions commit_branch_replaces.
Print Assumptions fork_child_local.
Print Assumptions advance_sibling_keeps_spine.
Print Assumptions bang_div1_fork_tops.
Print Assumptions bang_div2_fork_tops.
Print Assumptions bb_div1_fork_tops.
Print Assumptions bb_div2_fork_tops.
Print Assumptions mixfix_spine_ids_in_spine_space.
Print Assumptions mixfix_member_rules_below_base.
Print Assumptions mx_table_wf.
Print Assumptions mxbb_table_wf.
Print Assumptions mx_table_wf_member_rules.
Print Assumptions mxbb_table_wf_member_rules.
Print Assumptions mx_divergence1_is_accept_fork.
Print Assumptions mx_divergence2_all_commits.
Print Assumptions mx_any_spine_path_one_commit.
Print Assumptions mxbb_any_spine_path_one_commit.
Print Assumptions mx_nullary_lineage_receipt.
Print Assumptions mx_scalar_lineage_receipt.
Print Assumptions mx_polyadic_lineage_receipt.
Print Assumptions mxbb_nullary_lineage_receipt.
Print Assumptions mx_div1_both_branches.
Print Assumptions mx_commit_preserves_uw.
Print Assumptions full_admission_iff.
Print Assumptions no_floor_blocked_resurrection.
Print Assumptions bang_min_l_bp.
Print Assumptions bb_min_l_bp.
Print Assumptions bang_partial_window_cur7.
Print Assumptions mixfix_fold_count_per_reading.
Print Assumptions mixfix_fan_width_economy.
Print Assumptions wtimes_cost_additive.
Print Assumptions fold_cost_step.
Print Assumptions mixfix_c8_cost_totals_invariant.
Print Assumptions mixfix_stamp_freezes.
Print Assumptions mixfix_c8_stamp_min_member_substitution.
Print Assumptions single_stamp_cannot_reproduce_two_members.
Print Assumptions bang_nullary_stamp_delta_instance.
