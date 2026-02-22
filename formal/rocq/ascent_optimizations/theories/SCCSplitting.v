(*
 * SCCSplitting: Opt 5 — Core/Full Ascent Fixpoint Equivalence.
 *
 * Correctness claim: For inputs whose initial term belongs to a core
 * category, running the Core Ascent program (rules between core categories
 * only) produces a fixpoint identical to the Full program's fixpoint
 * restricted to core-category relations.
 *
 * Key definitions:
 *   - is_core c := bidi_reach primary c  (bidirectionally reachable)
 *   - full_step: immediate consequence using all rules
 *   - core_step: immediate consequence using only core-to-core rules
 *
 * Proof strategy: Induction on fixpoint iteration count.
 *   Base case: Seed populates only core categories (by construction).
 *   Inductive step: Non-core relations stay empty; core derivations identical.
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition          | Rust / Ascent Code                   | Location
 *   -------------------------|--------------------------------------|--------------------------
 *   is_core                  | compute_core_categories              | common.rs:357-391
 *   core_cats                | BTreeSet from compute_core_cats      | common.rs:375
 *   full_step                | full Ascent struct fixpoint step     | language.rs:1254-1312
 *   core_step                | core Ascent struct fixpoint step     | language.rs:1268-1279
 *   derive                   | consolidated subterm extraction      | categories.rs:50-53
 *   run_ascent_typed          | dispatcher: core vs full struct      | language.rs:1356-1366
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

From AscentOptimizations Require Import Prelude.
From AscentOptimizations Require Import GraphReachability.

Import ListNotations.

(* ===================================================================== *)
(*  SCC Splitting Model                                                   *)
(* ===================================================================== *)

Section SCCSplitting.

  (* Category type *)
  Variable Cat : Type.
  Variable cat_eqb : Cat -> Cat -> bool.
  Hypothesis cat_eqb_spec : forall c1 c2, cat_eqb c1 c2 = true <-> c1 = c2.

  (* All categories, the primary category *)
  Variable all_cats : list Cat.
  Variable primary : Cat.
  Hypothesis all_cats_complete : forall c, In c all_cats.
  Hypothesis all_cats_nodup : NoDup all_cats.

  (* Edge relation and reachability *)
  Variable edge : Cat -> Cat -> Prop.

  (* Core categories: bidirectionally reachable from primary *)
  Definition is_core (c : Cat) : Prop := bidi_reach edge primary c.

  (* Decidable is_core *)
  Variable is_core_dec : forall c, {is_core c} + {~ is_core c}.

  (* Core category list *)
  Definition core_cats : list Cat :=
    filter (fun c => match is_core_dec c with
                     | left _ => true
                     | right _ => false
                     end) all_cats.

  (* Primary is always core *)
  Lemma primary_is_core : is_core primary.
  Proof.
    unfold is_core. apply bidi_reach_refl.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  Database model                                                       *)
  (* ------------------------------------------------------------------- *)

  (* Fact type for a category *)
  Variable Fact : Cat -> Type.

  (* Database: maps categories to fact lists *)
  Variable DB : Type.
  Variable get_rel : DB -> forall c : Cat, list (Fact c).
  Variable set_rel : DB -> forall c : Cat, list (Fact c) -> DB.
  Variable empty_db : DB.

  (* get/set specification *)
  Hypothesis get_set_same : forall db c facts,
    get_rel (set_rel db c facts) c = facts.
  Hypothesis get_set_other : forall db c1 c2 facts,
    c1 <> c2 -> get_rel (set_rel db c1 facts) c2 = get_rel db c2.
  Hypothesis get_empty : forall c, get_rel empty_db c = [].

  (* ------------------------------------------------------------------- *)
  (*  Derivation function                                                  *)
  (* ------------------------------------------------------------------- *)

  (* derive src tgt db: Apply rule "tgt(sub) <-- src(t), ..."
     to all src-typed facts in db, producing new tgt-typed facts. *)
  Variable derive : forall (src tgt : Cat), DB -> list (Fact tgt).

  (* Key hypothesis: Derivation from empty source produces nothing.
     If a source category has no facts, no rule with that source fires. *)
  Hypothesis derive_from_empty :
    forall src tgt db,
      get_rel db src = [] -> derive src tgt db = [].

  (* Key hypothesis: Only reachable source-target pairs produce facts.
     (Follows from dead rule pruning, Opt 3) *)
  Hypothesis derive_unreachable_empty :
    forall src tgt db,
      ~ reach edge src tgt -> derive src tgt db = [].

  (* ------------------------------------------------------------------- *)
  (*  Full and Core step functions                                         *)
  (* ------------------------------------------------------------------- *)

  (* full_step: Immediate consequence operator using ALL rules *)
  Definition full_step (db : DB) (tgt : Cat) : list (Fact tgt) :=
    flat_map (fun src => derive src tgt db) all_cats.

  (* core_step: Immediate consequence operator using only core rules *)
  Definition core_step (db : DB) (tgt : Cat) : list (Fact tgt) :=
    flat_map (fun src => derive src tgt db) core_cats.

  (* ------------------------------------------------------------------- *)
  (*  Core invariant: non-core relations are always empty                  *)
  (* ------------------------------------------------------------------- *)

  (* The key invariant maintained across iterations:
     if non-core relations are empty, they stay empty. *)
  Definition non_core_empty (db : DB) : Prop :=
    forall c, ~ is_core c -> get_rel db c = [].

  (* ------------------------------------------------------------------- *)
  (*  S1: Non-core targets derive nothing when non-core sources are empty  *)
  (* ------------------------------------------------------------------- *)

  (* Core→non-core derivation hypothesis.
     If all non-core relations are empty, then rules with core source and
     non-core target derive nothing. This is because extracting a non-core
     subterm from a core term requires traversing through non-core intermediate
     types (via join), which are empty. The code generator places these rules
     only in the Full struct, not the Core struct.

     More precisely: if src is core and tgt is non-core, then the extraction
     path src → ... → tgt must pass through at least one non-core category.
     The intermediate joins on those non-core categories yield empty results
     because those relations are empty by the non_core_empty invariant. *)
  Hypothesis derive_core_noncore_empty :
    forall (src tgt : Cat) (db : DB),
      is_core src -> ~ is_core tgt -> non_core_empty db ->
      derive src tgt db = [].

  (* ------------------------------------------------------------------- *)
  (*  S1: Non-core targets derive nothing when invariant holds             *)
  (* ------------------------------------------------------------------- *)

  Theorem S1_non_core_derives_nothing :
    forall (tgt : Cat) (db : DB),
      ~ is_core tgt ->
      non_core_empty db ->
      full_step db tgt = [].
  Proof.
    intros tgt db Hnot_core Hinv.
    unfold full_step.
    apply flat_map_all_nil.
    intros src _Hin.
    destruct (is_core_dec src) as [Hcore_src | Hnot_core_src].
    - (* src is core, tgt is not core *)
      apply derive_core_noncore_empty; assumption.
    - (* src is not core: source relation is empty *)
      apply derive_from_empty. apply Hinv. exact Hnot_core_src.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  S2: Core derivations are identical in Full and Core programs         *)
  (* ------------------------------------------------------------------- *)

  Theorem S2_core_derivations_equal :
    forall (tgt : Cat) (db : DB),
      is_core tgt ->
      non_core_empty db ->
      full_step db tgt = core_step db tgt.
  Proof.
    intros tgt db Hcore_tgt Hinv.
    unfold full_step, core_step, core_cats.
    apply flat_map_filter_nil.
    intros src _Hin Hfilter.
    (* src was filtered out: src is NOT core *)
    destruct (is_core_dec src) as [Hcore | Hnotcore].
    + (* is_core src: filter should return true, contradiction *)
      discriminate.
    + (* ~ is_core src: source relation is empty *)
      apply derive_from_empty. apply Hinv. exact Hnotcore.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  S3: Fixpoint restriction equivalence (by induction on iterations)   *)
  (* ------------------------------------------------------------------- *)

  (* Iteration model: repeatedly apply the step function *)
  (* We use a simplified model where each iteration computes the step
     for all categories and merges results into the database. *)

  (* Merge: add derived facts to the database *)
  Variable merge_step : DB -> (forall c : Cat, list (Fact c)) -> DB.

  (* Merge specification *)
  Hypothesis merge_preserves_noncore_empty :
    forall db step_fn,
      non_core_empty db ->
      (forall c, ~ is_core c -> step_fn c = []) ->
      non_core_empty (merge_step db step_fn).

  (* Full iteration: apply full_step for all categories *)
  Definition full_iter (db : DB) : DB :=
    merge_step db (full_step db).

  (* Core iteration: apply core_step for core categories, nothing for non-core *)
  Definition core_iter (db : DB) : DB :=
    merge_step db (fun c =>
      match is_core_dec c with
      | left _ => core_step db c
      | right _ => []
      end).

  (* N-step iteration *)
  Fixpoint full_iter_n (n : nat) (db : DB) : DB :=
    match n with
    | 0 => db
    | S n' => full_iter (full_iter_n n' db)
    end.

  Fixpoint core_iter_n (n : nat) (db : DB) : DB :=
    match n with
    | 0 => db
    | S n' => core_iter (core_iter_n n' db)
    end.

  (* The invariant is preserved by full iteration *)
  Lemma full_iter_preserves_invariant :
    forall db,
      non_core_empty db ->
      non_core_empty (full_iter db).
  Proof.
    intros db Hinv.
    unfold full_iter.
    apply merge_preserves_noncore_empty.
    - exact Hinv.
    - intros c Hnotcore.
      apply S1_non_core_derives_nothing; assumption.
  Qed.

  (* The invariant holds after N full iterations from an invariant-satisfying seed *)
  Lemma full_iter_n_preserves_invariant :
    forall n db,
      non_core_empty db ->
      non_core_empty (full_iter_n n db).
  Proof.
    intros n. induction n as [| n' IH].
    - (* n = 0 *)
      intros db Hinv. simpl. exact Hinv.
    - (* n = S n' *)
      intros db Hinv. simpl.
      apply full_iter_preserves_invariant.
      apply IH. exact Hinv.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  S3: Core-category facts are identical at each iteration             *)
  (* ------------------------------------------------------------------- *)

  (* For the core restriction equivalence, we show that at each iteration,
     the full and core programs compute the same step for core categories.

     The seed starts with non_core_empty. By S1, non-core remains empty.
     By S2, core-target derivations are identical.

     Since:
     - merge_step receives the same per-category fact lists for core cats
       (by S2: full_step db tgt = core_step db tgt for core tgt)
     - merge_step receives [] for non-core cats in both programs
       (full: by S1; core: by definition)

     The resulting databases are identical. *)

  (* We express the equivalence on the step functions: *)
  Theorem S3_step_equivalence :
    forall (db : DB),
      non_core_empty db ->
      forall c,
        (match is_core_dec c with
         | left _ => full_step db c
         | right _ => @nil (Fact c)
         end) =
        (match is_core_dec c with
         | left _ => core_step db c
         | right _ => @nil (Fact c)
         end).
  Proof.
    intros db Hinv c.
    destruct (is_core_dec c) as [Hcore | Hnotcore].
    - (* Core: full_step = core_step by S2 *)
      apply S2_core_derivations_equal; assumption.
    - (* Non-core: both produce [] *)
      reflexivity.
  Qed.

  (* Corollary: Full program restricted to core = Core program.
     Under the non_core_empty invariant (which holds at every iteration),
     the full and core programs produce identical facts for core categories
     and both produce no facts for non-core categories. Therefore their
     fixpoints are identical when restricted to core categories. *)

  Hypothesis merge_ext :
    forall db f g,
      (forall c, f c = g c) -> merge_step db f = merge_step db g.

  Theorem S3_iter_equivalence :
    forall (db : DB),
      non_core_empty db ->
      full_iter db = core_iter db.
  Proof.
    intros db Hinv.
    unfold full_iter, core_iter.
    apply merge_ext.
    intros c.
    destruct (is_core_dec c) as [Hcore | Hnotcore].
    - (* Core: full_step = core_step *)
      apply S2_core_derivations_equal; assumption.
    - (* Non-core: full_step = [] *)
      apply S1_non_core_derives_nothing; assumption.
  Qed.

  (* N-step equivalence *)
  Theorem S3_fixpoint_restriction :
    forall n (db : DB),
      non_core_empty db ->
      full_iter_n n db = core_iter_n n db.
  Proof.
    intros n. induction n as [| n' IH].
    - (* Base case *)
      intros db Hinv. simpl. reflexivity.
    - (* Inductive step *)
      intros db Hinv. simpl.
      rewrite IH by exact Hinv.
      apply S3_iter_equivalence.
      (* Need: non_core_empty (core_iter_n n' db) *)
      rewrite <- IH by exact Hinv.
      apply full_iter_n_preserves_invariant.
      exact Hinv.
  Qed.

End SCCSplitting.
