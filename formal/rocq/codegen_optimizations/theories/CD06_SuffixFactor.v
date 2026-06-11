(*
 * CD06_SuffixFactor: Right-factoring equivalence (Phase 4B, measure-first).
 *
 * The CD06 transform  A -> beta a | gamma a   ==>   A -> A' a,  A' -> beta | gamma
 * (right-factoring of a shared rule tail) is proven meaning-preserving at the
 * rule-selection level: the factored grammar selects EXACTLY the same labeled
 * alternatives, in the same order and with the same multiplicity, as the
 * original.  Language equality, per-rule soundness/completeness, and exact
 * preservation of the ambiguity degree are corollaries of one list equality.
 *
 * ======================================================================
 * VERDICT (Phase 4B M1.0 measured 2026-06-10; recorded 2026-06-11):
 * CD06 STOPS AT DIAGNOSTIC-ONLY.  The transform is NOT wired into codegen:
 * there is no suffix_trie.rs and no cost_benefit Optimization::SuffixFactoring;
 * the only runtime artifact is the I17 `cd06-shared-suffix-measure` diagnostic
 * (pipeline.rs ~3366) computed by measure_shared_nonterminal_suffixes()
 * (decision_tree.rs:1181).
 *
 * Measured shared_suffix_ratio (production grammars):
 *   calculator depth1=0.60 depth2=0.19 | rhocalc depth1=0.50 depth2=0.42
 *   | Ambient depth2=0.57 | GuardedRho depth2=0
 *
 * The depth-1 ratio is degenerate (dominated by shared close delimiters such
 * as a trailing ")").  The depth-2 ratios EXCEED the plan's 0.10 screening
 * gate, so the cheap screen alone could NOT stop CD06; the group-level
 * analysis decides: every depth-2 bucket's member rules are already
 * discriminated by DISJOINT LEADING literals (CD02 disjoint-FIRST top-down
 * dispatch), so at runtime exactly one bucket member is live BEFORE its tail
 * is parsed -- a shared tail is parsed once whether or not it is factored.
 * Right-factoring would therefore merge generated CODE for the tails
 * (code-size only) while removing ZERO parse work, at the cost of a fresh A'
 * nonterminal per bucket (grammar churn, a new dispatch surface).
 *
 * Decision: record the negative, keep the I17 measurement diagnostic, and
 * prove the transform lemma (this file) so that any future wiring -- if a
 * grammar ever exhibits NON-disjoint leading dispatch over heavy shared
 * tails -- starts from a verified transform instead of an unproven one.
 * ======================================================================
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition            | Rust Code                                 | Location
 *   ---------------------------|-------------------------------------------|------------------------------------
 *   Alt / alt_body             | RDRuleInfo { label, items }               | prattail/src/grammar/ir.rs
 *   strip_last / ends_in       | item_key() last-item bucketing            | prattail/src/decision_tree.rs:1185
 *   factored_aux / residual    | (NOT WIRED -- would-be suffix-trie split) | diagnostic-only, see verdict
 *   matching_labels_orig       | per-rule RD alternative matching          | abstract model (CD05 precedent)
 *   matching_labels_fact       | (NOT WIRED -- factored dispatch)          | diagnostic-only, see verdict
 *   factored_aux_counts_eligible | eligible counting in                    | prattail/src/decision_tree.rs:1181
 *                              |   measure_shared_nonterminal_suffixes()   |
 *   I17 diagnostic             | "cd06-shared-suffix-measure"              | prattail/src/pipeline.rs:3366
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Setoid.

Import ListNotations.

Module CD06_SuffixFactor.

(* ===================================================================== *)
(*  Word model                                                            *)
(*                                                                        *)
(*  An Item is the key of an RD syntax item (Terminal/NonTerminal -- the  *)
(*  same restriction item_key() applies: Binder/Collection/SepList items  *)
(*  have no key and make a rule ineligible).  A rule body is a Word.      *)
(* ===================================================================== *)

Definition Item := nat.
Definition Word := list Item.

Fixpoint word_eqb (xs ys : Word) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Nat.eqb x y && word_eqb xs' ys'
  | _, _ => false
  end.

Lemma word_eqb_eq : forall xs ys, word_eqb xs ys = true <-> xs = ys.
Proof.
  induction xs as [| x xs' IH]; destruct ys as [| y ys']; simpl; split;
    intro H; try reflexivity; try discriminate.
  - apply andb_prop in H as [Hx Hxs].
    apply Nat.eqb_eq in Hx. apply IH in Hxs. subst. reflexivity.
  - injection H as Hx Hxs. subst.
    rewrite Nat.eqb_refl. simpl. apply IH. reflexivity.
Qed.

(* The empty word never equals a word with a last item. *)
Lemma word_eqb_nil_app : forall (zs : Word) (z : Item),
  word_eqb [] (zs ++ [z]) = false.
Proof. intros zs z. destruct zs; reflexivity. Qed.

(* Comparing words item-by-item factors through a shared last item. *)
Lemma word_eqb_app_last : forall (xs ys : Word) (x y : Item),
  word_eqb (xs ++ [x]) (ys ++ [y]) = word_eqb xs ys && Nat.eqb x y.
Proof.
  induction xs as [| x' xs' IH]; intros ys x y; destruct ys as [| y' ys'];
    simpl.
  - rewrite andb_true_r. reflexivity.
  - destruct (ys' ++ [y]) as [| w ws] eqn:Hd.
    + exfalso. apply app_eq_nil in Hd as [_ Hd]. discriminate.
    + simpl. rewrite andb_false_r. reflexivity.
  - destruct (xs' ++ [x]) as [| w ws] eqn:Hd.
    + exfalso. apply app_eq_nil in Hd as [_ Hd]. discriminate.
    + simpl. rewrite andb_false_r. reflexivity.
  - rewrite IH. rewrite andb_assoc. reflexivity.
Qed.

(* ===================================================================== *)
(*  strip_last: split a word into (prefix, last item)                     *)
(*  Mirrors the last-item bucketing of item_key() in                      *)
(*  measure_shared_nonterminal_suffixes().                                *)
(* ===================================================================== *)

Definition strip_last (w : Word) : option (Word * Item) :=
  match rev w with
  | [] => None
  | l :: rpre => Some (rev rpre, l)
  end.

Lemma strip_last_app : forall (pre : Word) (l : Item),
  strip_last (pre ++ [l]) = Some (pre, l).
Proof.
  intros pre l. unfold strip_last.
  rewrite rev_unit. rewrite rev_involutive. reflexivity.
Qed.

Lemma strip_last_some : forall (w pre : Word) (l : Item),
  strip_last w = Some (pre, l) -> w = pre ++ [l].
Proof.
  intros w pre l H. unfold strip_last in H.
  destruct (rev w) as [| l' rpre] eqn:Hr; [discriminate|].
  injection H as Hpre Hl. subst.
  rewrite <- (rev_involutive w). rewrite Hr. simpl. reflexivity.
Qed.

Lemma strip_last_none : forall (w : Word),
  strip_last w = None -> w = [].
Proof.
  intros w H. unfold strip_last in H.
  destruct (rev w) as [| l rpre] eqn:Hr; [| discriminate].
  destruct w as [| i w']; [reflexivity|].
  simpl in Hr. apply app_eq_nil in Hr as [_ Hr]. discriminate.
Qed.

(* ===================================================================== *)
(*  Alternatives and the factoring transform                              *)
(*                                                                        *)
(*  An Alt is a labeled rule body (RDRuleInfo { label, items }).  The     *)
(*  transform, for a fixed tail item a:                                   *)
(*    - factored_aux a alts : the A' alternatives -- each eligible body   *)
(*      beta ++ [a] contributes beta under the SAME label;                *)
(*    - residual a alts     : the ineligible alternatives, UNCHANGED;     *)
(*    - the factored A is   : A -> A' a  plus the residual alternatives.  *)
(* ===================================================================== *)

Record Alt := mkAlt {
  alt_label : nat;   (* rule label / constructor id *)
  alt_body  : Word   (* the rule body's item keys, in grammar order *)
}.

Definition ends_in (a : Item) (alt : Alt) : bool :=
  match strip_last (alt_body alt) with
  | Some (_, l) => Nat.eqb l a
  | None => false
  end.

Definition factored_aux (a : Item) (alts : list Alt) : list Alt :=
  flat_map (fun alt =>
    match strip_last (alt_body alt) with
    | Some (pre, l) =>
        if Nat.eqb l a then [mkAlt (alt_label alt) pre] else []
    | None => []
    end) alts.

Definition residual (a : Item) (alts : list Alt) : list Alt :=
  filter (fun alt => negb (ends_in a alt)) alts.

(* ===================================================================== *)
(*  Matching semantics                                                    *)
(*                                                                        *)
(*  At this altitude a body matches exactly the word of its own item      *)
(*  keys: the transform only re-associates CHOICE and CONCATENATION;      *)
(*  item denotations are untouched (Abstraction Gap 1).  The list of      *)
(*  matching labels, in grammar order, is the derivation record --        *)
(*  duplicates ARE meaningful (ambiguity degree).                         *)
(* ===================================================================== *)

Definition matching_labels_orig (alts : list Alt) (w : Word) : list nat :=
  map alt_label (filter (fun alt => word_eqb (alt_body alt) w) alts).

(* Factored matching: the single rule  A -> A' a  fires iff w ends in a,
   and its derivations enumerate the A' alternatives against the stripped
   prefix; the residual alternatives match w directly, unchanged. *)
Definition matching_labels_fact (a : Item) (alts : list Alt) (w : Word)
  : list nat :=
  match strip_last w with
  | Some (pre, l) =>
      if Nat.eqb l a
      then map alt_label
             (filter (fun alt => word_eqb (alt_body alt) pre)
                     (factored_aux a alts))
           ++ map alt_label
                (filter (fun alt => word_eqb (alt_body alt) w)
                        (residual a alts))
      else map alt_label
             (filter (fun alt => word_eqb (alt_body alt) w)
                     (residual a alts))
  | None =>
      map alt_label
        (filter (fun alt => word_eqb (alt_body alt) w) (residual a alts))
  end.

(* ===================================================================== *)
(*  Supporting lemmas                                                     *)
(* ===================================================================== *)

(* If no alternative matching w ends in a, restricting to the residual
   loses nothing: the filtered match lists agree exactly. *)
Lemma residual_match_full : forall (a : Item) (alts : list Alt) (w : Word),
  (forall alt, word_eqb (alt_body alt) w = true -> ends_in a alt = false) ->
  map alt_label
    (filter (fun alt => word_eqb (alt_body alt) w) (residual a alts))
  = map alt_label (filter (fun alt => word_eqb (alt_body alt) w) alts).
Proof.
  intros a alts w Hno. induction alts as [| alt rest IH].
  - reflexivity.
  - unfold residual. simpl.
    destruct (word_eqb (alt_body alt) w) eqn:Hm.
    + rewrite (Hno alt Hm). simpl. rewrite Hm. simpl.
      f_equal. exact IH.
    + destruct (ends_in a alt) eqn:He; simpl.
      * exact IH.
      * rewrite Hm. exact IH.
Qed.

(* When w itself ends in a, NO residual alternative matches it (a residual
   alternative's body does not end in a). *)
Lemma residual_match_nil : forall (a : Item) (alts : list Alt) (pre : Word),
  filter (fun alt => word_eqb (alt_body alt) (pre ++ [a]))
         (residual a alts) = [].
Proof.
  intros a alts pre. induction alts as [| alt rest IH].
  - reflexivity.
  - unfold residual. simpl.
    destruct (ends_in a alt) eqn:He; simpl.
    + exact IH.
    + destruct (word_eqb (alt_body alt) (pre ++ [a])) eqn:Hm.
      * exfalso. apply word_eqb_eq in Hm.
        unfold ends_in in He. rewrite Hm in He.
        rewrite strip_last_app in He. rewrite Nat.eqb_refl in He.
        discriminate.
      * exact IH.
Qed.

(* The A'-side matches on the stripped prefix are EXACTLY the original
   eligible matches on the whole word, label-for-label in grammar order. *)
Lemma factored_aux_match : forall (a : Item) (alts : list Alt) (pre : Word),
  map alt_label
    (filter (fun alt => word_eqb (alt_body alt) pre) (factored_aux a alts))
  = map alt_label
      (filter (fun alt => word_eqb (alt_body alt) (pre ++ [a])) alts).
Proof.
  intros a alts pre. induction alts as [| alt rest IH].
  - reflexivity.
  - simpl.
    destruct (strip_last (alt_body alt)) as [[p l] | ] eqn:Hb.
    + destruct (Nat.eqb l a) eqn:Hl.
      * (* eligible: body = p ++ [a]; the A' alternative carries p *)
        apply Nat.eqb_eq in Hl. subst l.
        apply strip_last_some in Hb. rewrite Hb.
        rewrite word_eqb_app_last. rewrite Nat.eqb_refl.
        rewrite andb_true_r. simpl.
        destruct (word_eqb p pre) eqn:Hm; simpl.
        -- f_equal. exact IH.
        -- exact IH.
      * (* last item differs from a: cannot match pre ++ [a] *)
        apply strip_last_some in Hb. rewrite Hb.
        rewrite word_eqb_app_last. rewrite Hl. rewrite andb_false_r.
        simpl. exact IH.
    + (* empty body: cannot match the nonempty pre ++ [a] *)
      apply strip_last_none in Hb. rewrite Hb.
      rewrite word_eqb_nil_app. simpl. exact IH.
Qed.

(* ===================================================================== *)
(*  T1 (central): the factored grammar selects EXACTLY the original       *)
(*  matching rules -- same labels, same grammar order, same multiplicity. *)
(*  This subsumes rule-selection equivalence AND ambiguity preservation   *)
(*  (the derivation record is identical, not merely equal as a set).      *)
(* ===================================================================== *)

Theorem factor_eq_matching_rule : forall (a : Item) (alts : list Alt) (w : Word),
  matching_labels_fact a alts w = matching_labels_orig alts w.
Proof.
  intros a alts w. unfold matching_labels_fact, matching_labels_orig.
  destruct (strip_last w) as [[pre l] | ] eqn:Hw.
  - apply strip_last_some in Hw. subst w.
    destruct (Nat.eqb l a) eqn:Hl.
    + (* w ends in a: residual contributes nothing; A' carries everything *)
      apply Nat.eqb_eq in Hl. subst l.
      rewrite residual_match_nil. simpl. rewrite app_nil_r.
      apply factored_aux_match.
    + (* w ends in some l <> a: no matching alternative ends in a *)
      apply residual_match_full.
      intros alt Hm. apply word_eqb_eq in Hm.
      unfold ends_in. rewrite Hm. rewrite strip_last_app. exact Hl.
  - (* w = []: no matching alternative has a last item at all *)
    apply strip_last_none in Hw. subst w.
    apply residual_match_full.
    intros alt Hm. apply word_eqb_eq in Hm.
    unfold ends_in. rewrite Hm. reflexivity.
Qed.

(* ===================================================================== *)
(*  T2/T3: soundness and completeness of rule selection                   *)
(* ===================================================================== *)

(* T2: no spurious selections -- every factored match is an original match *)
Theorem factor_sound : forall (a : Item) (alts : list Alt) (w : Word) (lbl : nat),
  In lbl (matching_labels_fact a alts w) ->
  In lbl (matching_labels_orig alts w).
Proof.
  intros a alts w lbl H. rewrite factor_eq_matching_rule in H. exact H.
Qed.

(* T3: no lost selections -- every original match survives factoring *)
Theorem factor_complete : forall (a : Item) (alts : list Alt) (w : Word) (lbl : nat),
  In lbl (matching_labels_orig alts w) ->
  In lbl (matching_labels_fact a alts w).
Proof.
  intros a alts w lbl H. rewrite factor_eq_matching_rule. exact H.
Qed.

(* ===================================================================== *)
(*  T4: language equality + exact ambiguity-degree preservation           *)
(* ===================================================================== *)

Definition derives_orig (alts : list Alt) (w : Word) : Prop :=
  matching_labels_orig alts w <> [].
Definition derives_fact (a : Item) (alts : list Alt) (w : Word) : Prop :=
  matching_labels_fact a alts w <> [].

Theorem factor_language_eq : forall (a : Item) (alts : list Alt) (w : Word),
  derives_fact a alts w <-> derives_orig alts w.
Proof.
  intros a alts w. unfold derives_fact, derives_orig.
  rewrite factor_eq_matching_rule. reflexivity.
Qed.

(* The number of derivations of every word is preserved EXACTLY: the
   transform can neither collapse nor duplicate ambiguity (the
   preserve-disambiguation invariant at the transform level). *)
Theorem factor_preserves_ambiguity_degree :
  forall (a : Item) (alts : list Alt) (w : Word),
    length (matching_labels_fact a alts w)
    = length (matching_labels_orig alts w).
Proof.
  intros a alts w. rewrite factor_eq_matching_rule. reflexivity.
Qed.

(* ===================================================================== *)
(*  T5: degraded path preserved                                           *)
(*                                                                        *)
(*  Ineligible alternatives (no factorable tail: in Rust, rules whose     *)
(*  last item has no item_key() -- Binder/Collection/SepList -- or whose  *)
(*  last item differs from the bucket tail) pass through the transform    *)
(*  UNCHANGED: they are exactly the residual, with bodies untouched.      *)
(* ===================================================================== *)

Theorem degraded_path_preserved : forall (a : Item) (alts : list Alt) (alt : Alt),
  In alt alts -> ends_in a alt = false -> In alt (residual a alts).
Proof.
  intros a alts alt Hin He. unfold residual.
  apply filter_In. split; [exact Hin|]. rewrite He. reflexivity.
Qed.

(* ... and the residual contains ONLY untouched original alternatives. *)
Theorem residual_subset : forall (a : Item) (alts : list Alt) (alt : Alt),
  In alt (residual a alts) -> In alt alts /\ ends_in a alt = false.
Proof.
  intros a alts alt H. unfold residual in H.
  apply filter_In in H as [Hin Hk]. split; [exact Hin|].
  destruct (ends_in a alt); [discriminate | reflexivity].
Qed.

(* ===================================================================== *)
(*  Measurement tie-in: the A' alternative count equals the eligible      *)
(*  count -- the bucketing in measure_shared_nonterminal_suffixes()       *)
(*  counts exactly the alternatives the transform would touch.            *)
(* ===================================================================== *)

Theorem factored_aux_counts_eligible : forall (a : Item) (alts : list Alt),
  length (factored_aux a alts) = length (filter (ends_in a) alts).
Proof.
  intros a alts. induction alts as [| alt rest IH].
  - reflexivity.
  - simpl. destruct (strip_last (alt_body alt)) as [[p l] | ] eqn:Hb; simpl.
    + assert (He : ends_in a alt = (l =? a)).
      { unfold ends_in. rewrite Hb. reflexivity. }
      rewrite He. destruct (l =? a) eqn:Hl; simpl.
      * f_equal. exact IH.
      * exact IH.
    + assert (He : ends_in a alt = false).
      { unfold ends_in. rewrite Hb. reflexivity. }
      rewrite He. simpl. exact IH.
Qed.

(* ===================================================================== *)
(*  Abstraction Gaps                                                      *)
(*                                                                        *)
(*  1. Item denotations: bodies match the word of their own item keys.    *)
(*     The transform only re-associates choice/concatenation; per-item    *)
(*     sublanguages (what a NonTerminal key derives) are untouched by     *)
(*     factoring, so body-level equivalence is the faithful altitude      *)
(*     (CD05 set the same precedent with abstract suffix parsers).        *)
(*  2. One bucket at a time: the model factors a single tail item a.      *)
(*     The Rust measurement buckets by EVERY distinct tail; sequential    *)
(*     application composes because eligible sets for distinct tails are  *)
(*     disjoint (a body has one last item) and residual passes the rest   *)
(*     through verbatim (T5).                                             *)
(*  3. Epsilon prefixes: a length-1 eligible body [a] factors to an       *)
(*     epsilon A' alternative.  The model handles it uniformly; a real    *)
(*     wiring would need epsilon-alternative support (or a length >= 2    *)
(*     restriction) in RD codegen -- moot while diagnostic-only.          *)
(*  4. Depth: the model factors depth-1 tails.  The measured depth-2      *)
(*     signal corresponds to factoring twice (a two-item tail); the       *)
(*     composition argument is Gap 2's.                                   *)
(*  5. The verdict's runtime claim (leading-literal-disjoint dispatch     *)
(*     makes factoring save zero parse work) is an empirical statement    *)
(*     about CD02 dispatch on the production grammars, not a theorem of   *)
(*     this file; this file proves the transform SAFE, the measurement    *)
(*     shows it UNPROFITABLE.                                             *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  Summary of Results                                                    *)
(*                                                                        *)
(*  T1: factor_eq_matching_rule                                           *)
(*      Factored match list = original match list (labels, order,         *)
(*      multiplicity) -- unconditionally, no disjointness precondition.   *)
(*  T2: factor_sound        -- no spurious rule selections.               *)
(*  T3: factor_complete     -- no lost rule selections.                   *)
(*  T4: factor_language_eq  -- same derivable words; plus                 *)
(*      factor_preserves_ambiguity_degree (exact derivation counts).      *)
(*  T5: degraded_path_preserved / residual_subset -- ineligible           *)
(*      alternatives pass through untouched.                              *)
(*  +   factored_aux_counts_eligible -- the measurement counts exactly    *)
(*      the would-be-touched alternatives.                                *)
(*                                                                        *)
(*  All proofs are COMPLETE -- zero Admitted, zero Axioms.                *)
(* ===================================================================== *)

End CD06_SuffixFactor.
