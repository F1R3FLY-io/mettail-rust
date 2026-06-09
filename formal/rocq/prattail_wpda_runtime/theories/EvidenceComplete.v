(*
 * EvidenceComplete: parse-assembly disambiguation is EVIDENCE-COMPLETE — an
 * alternative leaves the live set ONLY when EVIDENCE removes it, never by a
 * heuristic. The Rust site is `from_alternatives`
 * (macros/src/gen/runtime/language.rs:722) which, for ≥2 alternatives, deduplicates
 * ONLY by `semantic_fingerprint` (observational equivalence) and "deliberately does
 * not use groundness, WFST weight, or declaration order to choose a single
 * representative from semantically distinct alternatives" (its own doc, :718) —
 * returning `Ambiguous(deduped)` when ≥2 distinct keys remain.
 *
 * Model: an alternative carries a semantic key (`semantic_fingerprint`) and a WFST
 * `weight`. `assemble` = dedup keeping the first occurrence of each key (the
 * HashSet-insert in `from_alternatives`). Proven (zero-admission):
 *   - no_valid_alternative_dropped : every distinct semantic key in the input has a
 *     representative in the output — no semantically-distinct alternative is lost.
 *   - evidence_only_removal : any input alt that is not itself in the output has a
 *     SAME-KEY representative there — i.e. removal is an observational-equivalence
 *     MERGE (evidence), never a heuristic drop.
 *   - assemble_keys_nodup : the output keys are distinct ⇒ a surviving `Ambiguous`
 *     set is genuinely ambiguous (residual ambiguity surfaced, not spurious dups).
 *   - weight_is_order_only : the kept key-set is INVARIANT under reweighting ⇒
 *     weight never decides membership (it can only order). The Rust mirror: the
 *     dedup branches on the key alone.
 *   - weight_drop_can_lose_valid_alternative : a weight-min SELECT (what
 *     `from_alternatives` refuses to do) CAN drop a semantically-distinct
 *     alternative — the negative fence (cf. `hash_only_pair_dedup_can_drop_distinct_keys`)
 *     that forbids weight-pruning at parse assembly forever.
 *
 * This is Phase EC's meta-property: weights ORDER, never PRUNE; ambiguity is
 * first-class; only EVIDENCE (here: observational equivalence; later: a rewrite to
 * Err at eval) removes an alternative.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Import ListNotations.

Section EvidenceComplete.

  (* A parse alternative: a semantic key (= `semantic_fingerprint`, the
     observational-equivalence class) and a WFST weight. *)
  Record Alt : Type := { akey : nat; aweight : nat }.

  (* `from_alternatives`' dedup: keep the FIRST alternative of each key
     (HashSet-insert semantics over the already-seen keys). *)
  Fixpoint dedup_seen (seen : list nat) (alts : list Alt) : list Alt :=
    match alts with
    | [] => []
    | a :: rest =>
        if existsb (Nat.eqb (akey a)) seen
        then dedup_seen seen rest
        else a :: dedup_seen (akey a :: seen) rest
    end.

  Definition assemble (alts : list Alt) : list Alt := dedup_seen [] alts.

  (* `existsb (Nat.eqb x)` decides membership. *)
  Lemma existsb_eqb_In : forall x l, existsb (Nat.eqb x) l = true <-> In x l.
  Proof.
    intros x l. rewrite existsb_exists. split.
    - intros [y [Hin Heq]]. apply Nat.eqb_eq in Heq. subst y. exact Hin.
    - intros Hin. exists x. split; [exact Hin | apply Nat.eqb_refl].
  Qed.

  Lemma existsb_eqb_notIn : forall x l, existsb (Nat.eqb x) l = false <-> ~ In x l.
  Proof.
    intros x l. split.
    - intros Hf Hin. apply existsb_eqb_In in Hin. rewrite Hin in Hf. discriminate.
    - intros Hni. destruct (existsb (Nat.eqb x) l) eqn:E; [|reflexivity].
      apply existsb_eqb_In in E. contradiction.
  Qed.

  (* Every key of the input is either already seen or kept in the output. *)
  Lemma dedup_seen_keys_preserved : forall alts seen k,
    In k (map akey alts) ->
    In k seen \/ In k (map akey (dedup_seen seen alts)).
  Proof.
    induction alts as [| a rest IH]; intros seen k H.
    - simpl in H. contradiction.
    - simpl in H. destruct H as [Hak | Hrest].
      + (* k = akey a *)
        subst k. destruct (existsb (Nat.eqb (akey a)) seen) eqn:E.
        * left. apply existsb_eqb_In in E. exact E.
        * right. simpl. rewrite E. simpl. left. reflexivity.
      + destruct (existsb (Nat.eqb (akey a)) seen) eqn:E.
        * (* a skipped *) simpl. rewrite E. apply IH. exact Hrest.
        * (* a kept *) simpl. rewrite E. simpl.
          destruct (IH (akey a :: seen) k Hrest) as [Hseen | Hout].
          -- destruct Hseen as [Heq | Hin].
             ++ right. left. exact Heq.
             ++ left. exact Hin.
          -- right. right. exact Hout.
  Qed.

  (* THE no-loss theorem: every distinct semantic key survives assembly. *)
  Theorem no_valid_alternative_dropped : forall alts k,
    In k (map akey alts) -> In k (map akey (assemble alts)).
  Proof.
    intros alts k H. unfold assemble.
    destruct (dedup_seen_keys_preserved alts [] k H) as [Hseen | Hout].
    - simpl in Hseen. contradiction.
    - exact Hout.
  Qed.

  (* Removal is an observational-equivalence MERGE: any input alt that is not in
     the output has a SAME-KEY representative there (evidence: same fingerprint),
     never a heuristic drop. *)
  Theorem evidence_only_removal : forall alts a,
    In a alts -> exists b, In b (assemble alts) /\ akey b = akey a.
  Proof.
    intros alts a Hin.
    assert (Hk : In (akey a) (map akey alts)) by (apply in_map; exact Hin).
    apply no_valid_alternative_dropped in Hk.
    apply in_map_iff in Hk. destruct Hk as [b [Hbk Hb]].
    exists b. split; [exact Hb | exact Hbk].
  Qed.

  (* The output keys are distinct (and absent from `seen`) ⇒ a surviving multi-alt
     `Ambiguous` set is genuinely ambiguous, not a set of spurious duplicates. *)
  Lemma dedup_seen_nodup_and_fresh : forall alts seen,
    NoDup (map akey (dedup_seen seen alts))
    /\ (forall k, In k (map akey (dedup_seen seen alts)) -> ~ In k seen).
  Proof.
    induction alts as [| a rest IH]; intros seen.
    - simpl. split; [constructor | intros k H; simpl in H; contradiction].
    - simpl. destruct (existsb (Nat.eqb (akey a)) seen) eqn:E.
      + apply IH.
      + simpl. destruct (IH (akey a :: seen)) as [Hnodup Hfresh].
        split.
        * constructor.
          -- (* akey a ∉ tail keys: tail keys are fresh wrt akey a::seen *)
             intro Hin. apply (Hfresh (akey a) Hin). left. reflexivity.
          -- exact Hnodup.
        * intros k Hk. simpl in Hk. destruct Hk as [Heq | Hin].
          -- subst k. apply existsb_eqb_notIn. exact E.
          -- intro Hseen. apply (Hfresh k Hin). right. exact Hseen.
  Qed.

  Theorem assemble_keys_nodup : forall alts,
    NoDup (map akey (assemble alts)).
  Proof. intros alts. unfold assemble. apply (dedup_seen_nodup_and_fresh alts []). Qed.

  (* Reweighting (preserving keys) does not change the kept key-set: weight is
     ORDER-ONLY, never a membership criterion. *)
  Definition reweight (f : Alt -> nat) (a : Alt) : Alt :=
    {| akey := akey a; aweight := f a |}.

  Lemma dedup_seen_weight_invariant : forall alts seen f,
    map akey (dedup_seen seen alts)
    = map akey (dedup_seen seen (map (reweight f) alts)).
  Proof.
    induction alts as [| a rest IH]; intros seen f.
    - reflexivity.
    - simpl. (* akey (reweight f a) = akey a, so the existsb test is identical *)
      destruct (existsb (Nat.eqb (akey a)) seen) eqn:E.
      + apply IH.
      + simpl. f_equal. apply IH.
  Qed.

  Theorem weight_is_order_only : forall alts f,
    map akey (assemble alts) = map akey (assemble (map (reweight f) alts)).
  Proof. intros alts f. unfold assemble. apply dedup_seen_weight_invariant. Qed.

  (* ── The negative fence: weight-selection CAN lose a valid alternative ─────── *)

  (* A weight-min SELECT (keep only the lowest-weight alt) — the heuristic
     `from_alternatives` REFUSES. *)
  Definition weight_min_select (alts : list Alt) : list Alt :=
    match alts with
    | [] => []
    | a :: rest =>
        [fold_left
           (fun best x => if Nat.ltb (aweight x) (aweight best) then x else best)
           rest a]
    end.

  (* Two semantically-distinct alternatives; the weight-min select drops one key. *)
  Theorem weight_drop_can_lose_valid_alternative :
    exists alts k,
      In k (map akey alts) /\ ~ In k (map akey (weight_min_select alts)).
  Proof.
    exists [ {| akey := 0; aweight := 5 |}; {| akey := 1; aweight := 3 |} ].
    exists 0. split.
    - simpl. left. reflexivity.
    - simpl. intro H. destruct H as [H | H]; [discriminate H | contradiction].
  Qed.

End EvidenceComplete.
