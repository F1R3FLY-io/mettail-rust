(*
 * RuleConsolidation: Core equivalence theorems for Ascent rule consolidation.
 *
 * Three theorems:
 *   R1: FOR-MATCH EQUIVALENCE   — Areas 1, 2 (subterm extraction, congruence)
 *   R2: IF-MATCH EQUIVALENCE    — Areas 5, 6 (fold triggers, fold identities)
 *   R3: PAIR-MATCH EQUIVALENCE  — Area 3 (equation congruence)
 *
 * The central insight: for disjoint constructors, the flat_map over
 * N individual "if let" guards produces exactly the same multiset of
 * values as a single consolidated match expression.
 *
 * Spec-to-Code Traceability:
 *   Rocq Theorem              | Consolidation Area       | Location
 *   --------------------------|--------------------------|-----------
 *   for_match_equiv (R1)      | Areas 1, 2               | helpers.rs:45-65
 *   if_match_equiv (R2)       | Areas 5, 6               | mod.rs fold triggers
 *   pair_match_equiv (R3)     | Area 3                   | equations.rs
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Permutation.

From RuleConsolidation Require Import Prelude.

Import ListNotations.

(* =====================================================================
 * R1: FOR-MATCH EQUIVALENCE
 * =====================================================================
 *
 * This is the core theorem. It states that the flat_map of individual
 * "if let" extractions over all constructor kinds produces exactly the
 * same multiset as the single consolidated match expression.
 *
 * Concretely:
 *
 *   BEFORE (N rules):
 *     for each k_i in {k_1, ..., k_n}:
 *       tgt(sub) <-- src(t), if let Src::k_i(..) = t, sub ∈ extract(k_i, t)
 *
 *   AFTER (1 rule):
 *     tgt(sub) <-- src(t), sub ∈ match_extract(t)
 *
 * The multiset of derived facts (sub values) is the same.
 *
 * Proof strategy: Case split on classify(t).
 *   - Some k: The flat_map contributes only extract(k, t) (by disjointness
 *     and NoDup), and match_extract(t) = extract(k, t). Done.
 *   - None: The flat_map produces [] (all arms miss), and
 *     match_extract(t) = []. Done.
 * ===================================================================== *)

Section ForMatchEquiv.

  Variable T : Type.
  Variable K : Type.
  Variable V : Type.

  Variable classify : T -> option K.
  Variable extract  : K -> T -> list V.
  Variable all_kinds : list K.
  Variable eqb_K : K -> K -> bool.

  Hypothesis eqb_K_spec : forall a b : K, eqb_K a b = true <-> a = b.
  Hypothesis all_kinds_complete : forall k : K, forall t : T,
    classify t = Some k -> In k all_kinds.
  Hypothesis all_kinds_nodup : NoDup all_kinds.

  (** The consolidated match expression:
        match t { Cat::k(fields) => extract(k, t), _ => [] } *)
  Definition consolidated_extract (t : T) : list V :=
    match classify t with
    | Some k => extract k t
    | None   => []
    end.

  (** Per-kind conditional extraction, modeling "if let Cat::k(..) = t":
        if classify(t) = Some k then extract(k, t) else [] *)
  Definition per_kind (k : K) (t : T) : list V :=
    match classify t with
    | Some k' => if eqb_K k' k then extract k t else []
    | None    => []
    end.

  (** The original N rules: flat_map over all kinds. *)
  Definition all_rules (t : T) : list V :=
    flat_map (fun k => per_kind k t) all_kinds.

  (* --- Helper lemmas for per_kind --- *)

  Lemma per_kind_hit : forall t k,
    classify t = Some k -> per_kind k t = extract k t.
  Proof.
    intros t k Hcl. unfold per_kind. rewrite Hcl.
    assert (H : eqb_K k k = true) by (apply eqb_K_spec; reflexivity).
    rewrite H. reflexivity.
  Qed.

  Lemma per_kind_miss : forall t k k',
    classify t = Some k' -> k <> k' -> per_kind k t = [].
  Proof.
    intros t k k' Hcl Hne. unfold per_kind. rewrite Hcl.
    destruct (eqb_K k' k) eqn:E.
    - apply eqb_K_spec in E. subst. contradiction.
    - reflexivity.
  Qed.

  Lemma per_kind_none : forall t k,
    classify t = None -> per_kind k t = [].
  Proof.
    intros t k Hcl. unfold per_kind. rewrite Hcl. reflexivity.
  Qed.

  (* --- The main theorem --- *)

  Theorem for_match_equiv :
    forall (t : T),
      all_rules t ≡ₘ consolidated_extract t.
  Proof.
    intros t. unfold all_rules, consolidated_extract.
    destruct (classify t) as [k|] eqn:Hcl.
    - (* Case: classify t = Some k *)
      (* First, rewrite the RHS from extract k t to per_kind k t *)
      rewrite <- (per_kind_hit t k Hcl).
      (* Now: flat_map per_kind all_kinds ≡ₘ per_kind k t *)
      (* The flat_map contributes only per_kind k t for the matching kind *)
      apply flat_map_single_hit with (k0 := k).
      + exact all_kinds_nodup.
      + exact (all_kinds_complete k t Hcl).
      + intros k' Hin Hne.
        apply per_kind_miss with (k' := k); assumption.
    - (* Case: classify t = None *)
      (* All arms produce [], so flat_map produces [] *)
      rewrite flat_map_all_nil.
      + apply Permutation_refl.
      + intros k Hk. apply per_kind_none. exact Hcl.
  Qed.

End ForMatchEquiv.

(* =====================================================================
 * R2: IF-MATCH EQUIVALENCE
 * =====================================================================
 *
 * For boolean predicates (fold triggers/identities), the consolidation
 * replaces N "if let" guards with a single "if (match ... { ... })"
 * boolean predicate.
 *
 *   BEFORE: exists k in trigger_kinds, classify(t) = Some k
 *   AFTER:  match_predicate(t) = true
 *
 * where match_predicate models:
 *   match t {
 *     Cat::A(_) => true,
 *     Cat::B(_, _) => true,
 *     _ => false,
 *   }
 *
 * The predicate returns true iff classify(t) ∈ trigger_kinds.
 * ===================================================================== *)

Section IfMatchEquiv.

  Variable T : Type.
  Variable K : Type.

  Variable classify : T -> option K.
  Variable eqb_K : K -> K -> bool.

  Hypothesis eqb_K_spec : forall a b : K, eqb_K a b = true <-> a = b.

  (** The consolidated boolean predicate. *)
  Definition match_predicate (trigger_kinds : list K) (t : T) : bool :=
    match classify t with
    | Some k => existsb (eqb_K k) trigger_kinds
    | None   => false
    end.

  (** Individual "if let" guard for kind k. *)
  Definition if_let_matches (k : K) (t : T) : bool :=
    match classify t with
    | Some k' => eqb_K k' k
    | None    => false
    end.

  Theorem if_match_equiv :
    forall (trigger_kinds : list K) (t : T),
      (exists k, In k trigger_kinds /\ if_let_matches k t = true)
      <->
      match_predicate trigger_kinds t = true.
  Proof.
    intros trigger_kinds t.
    unfold match_predicate, if_let_matches.
    split.
    - (* -> : Some k matches => predicate is true *)
      intros [k [Hin Hmatch]].
      destruct (classify t) as [k'|] eqn:Hcl.
      + apply existsb_exists. exists k. split.
        * exact Hin.
        * exact Hmatch.
      + discriminate Hmatch.
    - (* <- : predicate true => some k matches *)
      intros Hpred.
      destruct (classify t) as [k'|] eqn:Hcl.
      + apply existsb_exists in Hpred.
        destruct Hpred as [k [Hin Heq]].
        exists k. split.
        * exact Hin.
        * exact Heq.
      + discriminate Hpred.
  Qed.

  (** Corollary: The boolean form directly captures the codegen pattern.
      existsb(fun k => if_let_matches k t) trigger_kinds
      = match_predicate trigger_kinds t *)
  Corollary if_match_bool_equiv :
    forall (trigger_kinds : list K) (t : T),
      existsb (fun k => if_let_matches k t) trigger_kinds
      = match_predicate trigger_kinds t.
  Proof.
    intros trigger_kinds t.
    unfold match_predicate, if_let_matches.
    destruct (classify t) as [k'|].
    - (* classify t = Some k' *)
      (* Both sides reduce to existsb (eqb_K k') trigger_kinds *)
      induction trigger_kinds as [|k ks IH].
      + reflexivity.
      + simpl. reflexivity.
    - (* classify t = None *)
      induction trigger_kinds as [|k ks IH].
      + reflexivity.
      + simpl. exact IH.
  Qed.

End IfMatchEquiv.

(* =====================================================================
 * R3: PAIR-MATCH EQUIVALENCE
 * =====================================================================
 *
 * For equation congruence (Area 3), two terms s and t are matched
 * simultaneously. The consolidated rule uses match (s, t) to extract
 * paired field values only when both terms have the same constructor.
 *
 *   BEFORE (N rules, one per constructor k):
 *     eq_cat(s, t) <-- cat(s), if let Cat::k(s_fields) = s,
 *                       cat(t), if let Cat::k(t_fields) = t,
 *                       eq_field(s_f0, t_f0), ...
 *
 *   AFTER (1 rule):
 *     eq_cat(s, t) <-- cat(s), cat(t),
 *       for (s_f0, ..., t_f0, ...) in (match (s, t) {
 *         (Cat::k1(sf0,..), Cat::k1(tf0,..)) => vec![(sf0,.., tf0,..)],
 *         ...
 *         _ => vec![],
 *       }).into_iter(),
 *       eq_field(s_f0, t_f0), ...
 *
 * The pair-match fires iff both terms have the same constructor.
 * ===================================================================== *)

Section PairMatchEquiv.

  Variable T : Type.
  Variable K : Type.
  Variable V : Type.  (* Paired extraction result *)

  Variable classify : T -> option K.
  Variable extract_pair : K -> T -> T -> list V.
  Variable all_kinds : list K.
  Variable eqb_K : K -> K -> bool.

  Hypothesis eqb_K_spec : forall a b : K, eqb_K a b = true <-> a = b.
  Hypothesis all_kinds_complete : forall k : K, forall t : T,
    classify t = Some k -> In k all_kinds.
  Hypothesis all_kinds_nodup : NoDup all_kinds.

  (** The consolidated pair-match expression. *)
  Definition pair_match_extract (s t : T) : list V :=
    match classify s, classify t with
    | Some ks, Some kt =>
        if eqb_K ks kt then extract_pair ks s t
        else []
    | _, _ => []
    end.

  (** Per-kind pair extraction for original rules. *)
  Definition per_kind_pair (k : K) (s t : T) : list V :=
    match classify s, classify t with
    | Some ks, Some kt =>
        if eqb_K ks k then
          if eqb_K kt k then extract_pair k s t
          else []
        else []
    | _, _ => []
    end.

  (** The original N per-constructor rules applied to the pair. *)
  Definition original_pair_rules (s t : T) : list V :=
    flat_map (fun k => per_kind_pair k s t) all_kinds.

  (* --- Helper lemmas --- *)

  Lemma per_kind_pair_hit : forall k s t,
    classify s = Some k -> classify t = Some k ->
    per_kind_pair k s t = extract_pair k s t.
  Proof.
    intros k s t Hcs Hct. unfold per_kind_pair. rewrite Hcs, Hct.
    assert (H : eqb_K k k = true) by (apply eqb_K_spec; reflexivity).
    rewrite H. reflexivity.
  Qed.

  Lemma per_kind_pair_miss_s : forall k k' s t,
    classify s = Some k' -> k <> k' ->
    per_kind_pair k s t = [].
  Proof.
    intros k k' s t Hcs Hne. unfold per_kind_pair. rewrite Hcs.
    destruct (classify t) as [kt|].
    - destruct (eqb_K k' k) eqn:E.
      + apply eqb_K_spec in E. subst. contradiction.
      + reflexivity.
    - reflexivity.
  Qed.

  Lemma per_kind_pair_miss_t : forall k ks kt s t,
    classify s = Some ks -> classify t = Some kt -> ks <> kt ->
    per_kind_pair k s t = [].
  Proof.
    intros k ks kt s t Hcs Hct Hne. unfold per_kind_pair. rewrite Hcs, Hct.
    destruct (eqb_K ks k) eqn:E1.
    - apply eqb_K_spec in E1. subst k.
      destruct (eqb_K kt ks) eqn:E2.
      + apply eqb_K_spec in E2. subst. contradiction.
      + reflexivity.
    - reflexivity.
  Qed.

  Lemma per_kind_pair_none_s : forall k s t,
    classify s = None -> per_kind_pair k s t = [].
  Proof.
    intros k s t Hcs. unfold per_kind_pair. rewrite Hcs. reflexivity.
  Qed.

  Lemma per_kind_pair_none_t : forall k ks s t,
    classify s = Some ks -> classify t = None -> per_kind_pair k s t = [].
  Proof.
    intros k ks s t Hcs Hct. unfold per_kind_pair. rewrite Hcs, Hct. reflexivity.
  Qed.

  (* --- The main theorem --- *)

  Theorem pair_match_equiv :
    forall (s t : T),
      original_pair_rules s t ≡ₘ pair_match_extract s t.
  Proof.
    intros s t.
    unfold original_pair_rules, pair_match_extract.
    destruct (classify s) as [ks|] eqn:Hcs;
    destruct (classify t) as [kt|] eqn:Hct.
    - (* Both Some *)
      destruct (eqb_K ks kt) eqn:Heq.
      + (* Same constructor *)
        apply eqb_K_spec in Heq. subst kt.
        (* Rewrite RHS from extract_pair to per_kind_pair *)
        rewrite <- (per_kind_pair_hit ks s t Hcs Hct).
        (* Only the arm for ks contributes *)
        apply flat_map_single_hit with (k0 := ks).
        * exact all_kinds_nodup.
        * exact (all_kinds_complete ks s Hcs).
        * intros k' Hin Hne.
          apply per_kind_pair_miss_s with (k' := ks); assumption.
      + (* Different constructors: both sides empty *)
        rewrite flat_map_all_nil.
        * apply Permutation_refl.
        * intros k Hin.
          assert (Hne : ks <> kt).
          { intro Hsub. subst. rewrite (proj2 (eqb_K_spec kt kt) eq_refl) in Heq.
            discriminate. }
          apply per_kind_pair_miss_t with (ks := ks) (kt := kt); assumption.
    - (* s = Some, t = None: both sides empty *)
      rewrite flat_map_all_nil.
      + apply Permutation_refl.
      + intros k Hin. apply per_kind_pair_none_t with (ks := ks); assumption.
    - (* s = None, t = Some: both sides empty *)
      rewrite flat_map_all_nil.
      + apply Permutation_refl.
      + intros k Hin. apply per_kind_pair_none_s. exact Hcs.
    - (* Both None: both sides empty *)
      rewrite flat_map_all_nil.
      + apply Permutation_refl.
      + intros k Hin. apply per_kind_pair_none_s. exact Hcs.
  Qed.

End PairMatchEquiv.
