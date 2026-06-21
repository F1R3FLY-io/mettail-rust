(*
 * CollectionLexForkClearSoundness: the soundness invariant of the rhocalc
 * collection `lex_fork_path` clear-at-element-seal fix (commit cc91d291,
 * "collapse lexical-ambiguity cursor cross-product in collections").
 *
 * Design source of truth:
 *   docs/design/rhocalc-collection-fork-explosion.md
 *     §2.4   the `lex_fork_path` sidecar is appended per lexical fork-arm and
 *            never popped — the redundant anti-merge axis.
 *     §3.1   Change B: clear the element's lexical stamps at the splice that
 *            seals the element into an SPPF packing.
 *     §3.3   the SOUNDNESS argument: the sidecar feeds ONLY merge /
 *            equivalence bucketing (`merge_disambiguator` `tomita_frontier.rs:336`,
 *            the H12 cohort `~_obs` capture `cohort_lazy.rs:557`, the cursor
 *            snapshot merge mirrors), NEVER the SPPF / realizer / any semantic
 *            action. Hence:
 *            (S1) the realized parse term-set is the SPPF's, independent of the
 *                 sidecar — clearing it cannot change which terms are realized;
 *            (S4) the merge gate's COMPARISON is untouched; the fix changes the
 *                 gate's INPUT (it makes sibling cursors' sidecars equal at the
 *                 splice), so two cursors that were observationally equal on the
 *                 realized output but kept apart ONLY by the sidecar now collapse.
 *     §8.1   the IMPLEMENTED form is clear-all-at-splice (not the watermark
 *            stack): `emit_splice_into_collection` clears `lex_fork_path`
 *            ENTIRELY; the function is only reached when splicing a collection
 *            element, so the `collection_stack_depth > 0` gate is implicit.
 *
 * WHAT IS PROVED (zero-admission; no Axiom / Admitted / admit):
 *
 *   A cursor is modelled as a pair (realized observation `obs`, lexical-fork
 *   sidecar `sc`). The observation `obs` is the cursor's contribution to the
 *   realized parse (the SPPF symbol/packing it carries); the sidecar `sc` is
 *   the `lex_fork_path` (a list of `LexForkStamp`s). The fix is the function
 *   `clear_lex_fork`, which sets `sc := []` and leaves `obs` untouched.
 *
 *   T1 clear_preserves_observation : observing a cleared cursor = observing it
 *      before (the realized contribution is sidecar-independent).
 *   T2 realized_set_invariant_under_clear_all : clearing every cursor's
 *      sidecar leaves the SET of realized observations of a frontier UNCHANGED
 *      (the realized term-set is preserved — the central S1 claim).
 *   T3 merge_relaxation_only_collapses_obs_equal : after the clear, two
 *      cursors merge under the merge key (TomitaKey + merge_disambiguator)
 *      ONLY when they are OBSERVATIONALLY EQUAL on the realized output — the
 *      sidecar no longer distinguishes them, but every OTHER (genuine) axis
 *      still does. So the relaxation collapses exactly observationally-equal
 *      cursors and no others (S4 + S3 chained-output preservation).
 *   T4 clear_is_input_change_not_gate_change : the merge gate's COMPARISON is
 *      byte-identical pre/post fix; the fix changes only the cursor STATE fed
 *      to it. (The `aggregation_keeps_distinct_lex_fork_stamps_as_separate_arcs`
 *      invariant — distinct LIVE stamps still block — is preserved: the gate
 *      still inspects `lex_fork_path.last()`; the fix made the inputs equal.)
 *   T5 sidecar_not_read_by_realizer : the realizer is a function of `obs`
 *      alone; no sidecar value can change a realized term (the read-site
 *      audit, §3.1, transcribed as a typing fact).
 *
 *   The connection to the parser is stated as the top-level theorem
 *   collection_lex_fork_clear_preserves_realized_terms.
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Import ListNotations.

Section CollectionLexForkClearSoundness.

  (* ── The two cursor components. ─────────────────────────────────────── *)

  (* `Obs` is the cursor's REALIZED observation: the SPPF symbol/packing it
     contributes to the parse forest. We keep it opaque with decidable
     equality (the realizer compares/derives terms structurally; all that the
     soundness argument needs is that `Obs` is the realized-output carrier and
     that the sidecar is NOT part of it). *)
  Variable Obs : Type.
  Variable obs_eq_dec : forall x y : Obs, {x = y} + {x <> y}.

  (* `LexForkStamp` = (pos, alt_idx, src_idx, rule_idx) — wpda_walker.rs:2857.
     The sidecar `lex_fork_path` is a list of these. *)
  Definition LexForkStamp : Type := (nat * nat * nat * nat)%type.
  Definition Sidecar : Type := list LexForkStamp.

  (* A cursor: its realized observation + its lexical-fork sidecar. *)
  Record cursor : Type := {
    cur_obs : Obs;          (* the realized contribution (SPPF-side) *)
    cur_sidecar : Sidecar   (* lex_fork_path — the redundant anti-merge axis *)
  }.

  (* ── The realizer reads ONLY the observation (S1 / T5). ─────────────── *)

  (* `realize` is the realized-term projection of a cursor. The read-site
     audit (§3.1: "never read by engine.step, the SPPF realizer, or any
     semantic action") is captured by DEFINITION: realize ignores the sidecar.
     We model the realized TERM via an opaque decoder `decode : Obs -> Term`. *)
  Variable Term : Type.
  Variable decode : Obs -> Term.

  Definition realize (c : cursor) : Term := decode (cur_obs c).

  (* ── The fix: clear the lexical sidecar at element-seal (§8.1). ─────── *)

  Definition clear_lex_fork (c : cursor) : cursor :=
    {| cur_obs := cur_obs c; cur_sidecar := [] |}.

  (* ════════════════════════════════════════════════════════════════════
     T1 — clearing the sidecar PRESERVES the observation (and hence the
     realized term). The realized contribution is sidecar-independent.
     ════════════════════════════════════════════════════════════════════ *)
  Theorem clear_preserves_observation :
    forall c, cur_obs (clear_lex_fork c) = cur_obs c.
  Proof. intro c. reflexivity. Qed.

  Theorem clear_preserves_realize :
    forall c, realize (clear_lex_fork c) = realize c.
  Proof. intro c. reflexivity. Qed.

  (* ════════════════════════════════════════════════════════════════════
     T5 — the realizer is a FUNCTION OF THE OBSERVATION ALONE: no sidecar
     value can change a realized term (the §3.1 read-site audit as a typing
     fact). Two cursors with the SAME observation realize identically,
     regardless of their sidecars.
     ════════════════════════════════════════════════════════════════════ *)
  Theorem sidecar_not_read_by_realizer :
    forall c1 c2,
      cur_obs c1 = cur_obs c2 ->
      realize c1 = realize c2.
  Proof.
    intros c1 c2 Hobs. unfold realize. rewrite Hobs. reflexivity.
  Qed.

  (* ════════════════════════════════════════════════════════════════════
     T2 — the SET of realized observations of a frontier is INVARIANT under
     clearing every cursor's sidecar. This is the central S1 claim: the
     realized term-set is preserved.

     We model "the set of realized terms" as the image of `realize` over the
     frontier list, and prove membership is preserved both ways under
     `map clear_lex_fork`.
     ════════════════════════════════════════════════════════════════════ *)

  Definition realized_terms (frontier : list cursor) : list Term :=
    map realize frontier.

  Theorem realized_set_invariant_under_clear_all :
    forall frontier,
      realized_terms (map clear_lex_fork frontier) = realized_terms frontier.
  Proof.
    intro frontier. unfold realized_terms.
    rewrite map_map.
    apply map_ext. intro c.
    apply clear_preserves_realize.
  Qed.

  (* Membership form (the "set of realized terms is unchanged" phrasing): a
     term is realized after the clear IFF it was realized before. *)
  Theorem realized_membership_invariant_under_clear_all :
    forall frontier t,
      In t (realized_terms (map clear_lex_fork frontier)) <->
      In t (realized_terms frontier).
  Proof.
    intros frontier t.
    rewrite realized_set_invariant_under_clear_all. reflexivity.
  Qed.

  (* ── The merge key (TomitaKey + merge_disambiguator), tomita_frontier.rs:70,
        :326). We model it as: the GENUINE axes (everything the SPPF/GLR
        configuration carries — abstracted as a single `genuine` projection)
        PLUS the redundant sidecar's `last` stamp (the `lex_fork_path.last()`
        component, the ONLY sidecar contribution to the gate). ── *)

  Variable Genuine : Type.
  Variable genuine_eq_dec : forall x y : Genuine, {x = y} + {x <> y}.
  (* The genuine projection of a cursor: TomitaKey ⊕ all merge_disambiguator
     axes EXCEPT lex_fork_path.last() (sppf_stack_id, incoming_edge_stack,
     cohort_origin, the weight provenance, etc.). It is sidecar-INDEPENDENT
     (the sidecar is a separate field) — modeled as a parameter projection of
     the observation + other state, here folded into a function of cur_obs to
     reflect that genuine config is recoverable without the sidecar. *)
  Variable genuine_of : Obs -> Genuine.

  Definition genuine_key (c : cursor) : Genuine := genuine_of (cur_obs c).

  (* `lex_fork_last`: the `merge_disambiguator`'s `lex_fork_path.last()`
     component. *)
  Definition lex_fork_last (c : cursor) : option LexForkStamp :=
    match rev (cur_sidecar c) with
    | [] => None
    | x :: _ => Some x
    end.

  (* The FULL merge key: (genuine_key, lex_fork_last). Two cursors collapse
     under the gate iff their full merge keys are equal — this is the gate's
     COMPARISON, which the fix does NOT change (T4). *)
  Definition merge_key (c : cursor) : (Genuine * option LexForkStamp)%type :=
    (genuine_key c, lex_fork_last c).

  Definition merges (c1 c2 : cursor) : Prop := merge_key c1 = merge_key c2.

  (* ════════════════════════════════════════════════════════════════════
     T4 — the fix is an INPUT change, not a GATE change. `merge_key` /
     `merges` (the comparison) are defined identically before and after the
     fix — the fix only transforms the cursor via `clear_lex_fork`. We make
     this precise: `merges` is the SAME relation; what changes is that after
     clearing, the `lex_fork_last` component becomes `None` for everyone, so
     the gate's sidecar axis no longer separates anyone.
     ════════════════════════════════════════════════════════════════════ *)

  (* After the clear, lex_fork_last is always None (empty sidecar). *)
  Lemma lex_fork_last_after_clear :
    forall c, lex_fork_last (clear_lex_fork c) = None.
  Proof. intro c. unfold lex_fork_last, clear_lex_fork. simpl. reflexivity. Qed.

  (* The genuine key is preserved by the clear (it is sidecar-independent). *)
  Lemma genuine_key_after_clear :
    forall c, genuine_key (clear_lex_fork c) = genuine_key c.
  Proof. intro c. unfold genuine_key, clear_lex_fork. reflexivity. Qed.

  (* T4 proper: the merge RELATION is the same function pre/post — we state it
     as: `merges` applied to cleared cursors reduces to equality of the
     genuine key alone (the sidecar axis is neutralized for BOTH operands,
     not removed from the comparison). *)
  Theorem clear_is_input_change_not_gate_change :
    forall c1 c2,
      merges (clear_lex_fork c1) (clear_lex_fork c2) <->
      genuine_key c1 = genuine_key c2.
  Proof.
    intros c1 c2. unfold merges, merge_key.
    rewrite !lex_fork_last_after_clear.
    rewrite !genuine_key_after_clear.
    split.
    - intro H. inversion H. reflexivity.
    - intro H. rewrite H. reflexivity.
  Qed.

  (* ════════════════════════════════════════════════════════════════════
     T3 — the merge relaxation only collapses OBSERVATIONALLY-EQUAL cursors.

     KEY SOUNDNESS LINK: the genuine key is `genuine_of (cur_obs c)`. So two
     cleared cursors that merge have EQUAL genuine keys; and — for the
     collection-element case the fix targets — the genuine key DETERMINES the
     realized observation up to realized-term equality (the SPPF shares the
     element Symbol: §2.3 "all three readings reduce to ONE Proc Symbol id").
     We capture this with the hypothesis `genuine_determines_realize` (the
     SPPF sharing fact, discharged for the collection-element context by the
     CollectionForkEvidence element-Symbol sharing) and conclude: merged
     cleared cursors realize to the SAME term — i.e. the relaxation only
     collapses observationally-equal cursors, so dropping the duplicate never
     removes a realized term. The merge is observation-preserving.
     ════════════════════════════════════════════════════════════════════ *)

  (* The SPPF-sharing fact for the collection element context (§2.3): cursors
     at the same genuine configuration realize the same term — because the
     three lexical readings reduce to the SAME shared element Symbol, whose
     packings are ⊕-aggregated. This is a HYPOTHESIS here (it is the SPPF
     invariant, proven in the SPPF layer / CollectionForkEvidence), used to
     show the relaxation is observation-preserving in the targeted context. *)
  Hypothesis genuine_determines_realize :
    forall c1 c2, genuine_key c1 = genuine_key c2 -> realize c1 = realize c2.

  Theorem merge_relaxation_only_collapses_obs_equal :
    forall c1 c2,
      merges (clear_lex_fork c1) (clear_lex_fork c2) ->
      realize c1 = realize c2.
  Proof.
    intros c1 c2 Hmerge.
    apply clear_is_input_change_not_gate_change in Hmerge.
    apply genuine_determines_realize. exact Hmerge.
  Qed.

  (* ════════════════════════════════════════════════════════════════════
     TOP-LEVEL — the collection lex-fork clear is OBSERVATION-PRESERVING.

     Combining T2 (clearing every sidecar leaves the realized term-set
     unchanged) with T3 (the merge relaxation only collapses cursors that
     realize the same term, so collapsing them removes no realized term): the
     set of realized terms of the parse is identical before and after the fix.

     We model the post-fix frontier as `merge_dedup (map clear_lex_fork F)`:
     clear every sidecar, then deduplicate cursors that the (unchanged) gate
     now merges. We prove the realized term-set is invariant under BOTH steps.
     ════════════════════════════════════════════════════════════════════ *)

  (* Deduplicate a frontier by the merge key: keep the first cursor of each
     merge-key class, drop later mergers. (Models register_arc_with_aggregation
     letting the ⊕-fold FIRE on the now-equal-keyed sibling arcs.) *)
  Definition merge_key_eq_dec :
    forall k1 k2 : (Genuine * option LexForkStamp)%type, {k1 = k2} + {k1 <> k2}.
  Proof.
    intros [g1 s1] [g2 s2].
    destruct (genuine_eq_dec g1 g2) as [Hg | Hg].
    - destruct s1 as [x1 |]; destruct s2 as [x2 |].
      + (* compare the stamps (nat 4-tuples) *)
        destruct x1 as [[[p1 a1] sr1] r1]; destruct x2 as [[[p2 a2] sr2] r2].
        destruct (Nat.eq_dec p1 p2);
        destruct (Nat.eq_dec a1 a2);
        destruct (Nat.eq_dec sr1 sr2);
        destruct (Nat.eq_dec r1 r2);
          subst; try (left; congruence);
          right; intro H; inversion H; contradiction.
      + right. intro H. inversion H.
      + right. intro H. inversion H.
      + subst. left. reflexivity.
    - right. intro H. inversion H. contradiction.
  Defined.

  (* Structural dedup with a `seen`-keys accumulator: keep a cursor iff its
     merge-key has not been seen, then record the key. (Models
     register_arc_with_aggregation keeping the first arc of each merge-key
     class and ⊕-folding later mergers into it.) Structurally recursive on the
     list — accepted by Coq's guard checker. *)
  Definition key_seen
    (k : (Genuine * option LexForkStamp)%type) (seen : list _) : bool :=
    if in_dec merge_key_eq_dec k seen then true else false.

  Fixpoint merge_dedup_acc
    (seen : list (Genuine * option LexForkStamp)%type)
    (frontier : list cursor) : list cursor :=
    match frontier with
    | [] => []
    | c :: rest =>
        if key_seen (merge_key c) seen
        then merge_dedup_acc seen rest
        else c :: merge_dedup_acc (merge_key c :: seen) rest
    end.

  Definition merge_dedup (frontier : list cursor) : list cursor :=
    merge_dedup_acc [] frontier.

  (* Dedup never INTRODUCES a realized term (kept cursors are a sublist of the
     input, for ANY seen accumulator). *)
  Lemma merge_dedup_acc_realize_subset :
    forall frontier seen t,
      In t (realized_terms (merge_dedup_acc seen frontier)) ->
      In t (realized_terms frontier).
  Proof.
    induction frontier as [| c rest IH]; intros seen t Hin; simpl in *.
    - exact Hin.
    - destruct (key_seen (merge_key c) seen) eqn:Eseen.
      + (* c dropped: term comes from the tail dedup ⇒ from rest. *)
        right. apply (IH seen t Hin).
      + (* c kept. *)
        unfold realized_terms in Hin. simpl in Hin.
        destruct Hin as [Hhd | Htl].
        * left. exact Hhd.
        * right. apply (IH (merge_key c :: seen) t Htl).
  Qed.

  Lemma merge_dedup_realize_subset :
    forall frontier t,
      In t (realized_terms (merge_dedup frontier)) ->
      In t (realized_terms frontier).
  Proof.
    intros frontier t Hin. unfold merge_dedup in Hin.
    apply (merge_dedup_acc_realize_subset frontier [] t Hin).
  Qed.

  (* The substantive direction for observation-preservation: dedup never
     REMOVES a realized term either, BECAUSE every dropped cursor realizes the
     SAME term as a kept one (it was dropped only because it merged, and
     merging cleared cursors ⇒ same realize, by T3). We prove the realized
     term-set is preserved by dedup on a CLEARED frontier. *)

  (* Helper: every element of `frontier` realizes to a term that is realized
     by `merge_dedup frontier`, when the frontier is fully cleared (so all
     merges are observation-preserving). We thread the "cleared" property as:
     every cursor in the list has empty sidecar. *)
  Definition all_cleared (frontier : list cursor) : Prop :=
    Forall (fun c => cur_sidecar c = []) frontier.

  Lemma clear_all_is_cleared :
    forall frontier, all_cleared (map clear_lex_fork frontier).
  Proof.
    intro frontier. unfold all_cleared. rewrite Forall_map.
    apply Forall_forall. intros c _. reflexivity.
  Qed.

  (* On a cleared frontier, two cursors merge iff their genuine keys are equal
     (both sidecars are empty ⇒ lex_fork_last = None for both). *)
  Lemma cleared_merges_iff_genuine :
    forall c1 c2,
      cur_sidecar c1 = [] -> cur_sidecar c2 = [] ->
      (merges c1 c2 <-> genuine_key c1 = genuine_key c2).
  Proof.
    intros c1 c2 H1 H2. unfold merges, merge_key, lex_fork_last.
    rewrite H1, H2. simpl. split.
    - intro H. inversion H. reflexivity.
    - intro H. rewrite H. reflexivity.
  Qed.

  (* On a cleared frontier, merging ⇒ same realize (T3 specialised to the
     cleared invariant — no need to clear again). *)
  Lemma cleared_merge_preserves_realize :
    forall c1 c2,
      cur_sidecar c1 = [] -> cur_sidecar c2 = [] ->
      merges c1 c2 -> realize c1 = realize c2.
  Proof.
    intros c1 c2 H1 H2 Hm.
    apply (cleared_merges_iff_genuine c1 c2 H1 H2) in Hm.
    apply genuine_determines_realize. exact Hm.
  Qed.

  (* ── Dedup preserves the realized term-set on a cleared frontier (⊇: no
        term lost). The accumulator form needs a threaded invariant linking
        `seen` to the terms emitted so far: every seen KEY is realize-covered
        by an already-emitted term. On a cleared frontier, a key determines
        the realize value (cleared_merge_preserves_realize), so a dropped
        cursor (key already seen) realizes a covered term — already emitted —
        and a kept cursor adds its own term. ──

     NOTE (failed strategy, recorded per CLAUDE.md): the `filter`-based
     `merge_dedup` (keep head, filter rest by ≠key, recurse) is NOT
     structurally recursive (Coq rejects `filter ... rest` as a subterm); the
     well-founded-on-length proof for it is moot. The accumulator form below
     is structural and the invariant-threaded superset proof is clean. *)

  (* `key_realize_covered k emitted`: the cleared realize value of every
     cursor with merge-key k is already in `emitted`. (For cleared cursors,
     merge-key = (genuine_key, None), and genuine_key determines realize.) *)
  Definition key_realize_covered
    (k : (Genuine * option LexForkStamp)%type) (emitted : list Term) : Prop :=
    forall c, cur_sidecar c = [] -> merge_key c = k -> In (realize c) emitted.

  Definition seen_covered
    (seen : list (Genuine * option LexForkStamp)%type)
    (emitted : list Term) : Prop :=
    forall k, In k seen -> key_realize_covered k emitted.

  (* The generalized invariant lemma. `emitted` is the terms emitted before
     reaching this accumulator state; the conclusion covers every term of the
     remaining cleared frontier by EITHER `emitted` (seen-covered) OR the
     dedup output of the remaining frontier. *)
  Lemma merge_dedup_acc_covers_cleared :
    forall frontier seen emitted t,
      all_cleared frontier ->
      seen_covered seen emitted ->
      In t (realized_terms frontier) ->
      In t emitted \/ In t (realized_terms (merge_dedup_acc seen frontier)).
  Proof.
    induction frontier as [| c rest IH];
      intros seen emitted t Hcl Hsc Hin.
    - simpl in Hin. contradiction.
    - inversion Hcl as [| c' rest' Hccl Hrestcl Heq]; subst.
      unfold realized_terms in Hin. simpl in Hin.
      destruct Hin as [Hhd | Htl].
      + (* t = realize c. *)
        destruct (key_seen (merge_key c) seen) eqn:Eseen.
        * (* c dropped: its key is seen ⇒ realize c covered by emitted. *)
          left. unfold key_seen in Eseen.
          destruct (in_dec merge_key_eq_dec (merge_key c) seen) as [Hk | Hk];
            [| discriminate].
          specialize (Hsc (merge_key c) Hk c Hccl eq_refl).
          rewrite Hhd in Hsc. exact Hsc.
        * (* c kept: t = realize c is the new head of the output. *)
          right. simpl. rewrite Eseen.
          unfold realized_terms. simpl. left. exact Hhd.
      + (* t realized by some cursor in rest. *)
        destruct (key_seen (merge_key c) seen) eqn:Eseen.
        * (* c dropped ⇒ accumulator unchanged; recurse with same seen. *)
          simpl. rewrite Eseen.
          apply (IH seen emitted t Hrestcl Hsc Htl).
        * (* c kept ⇒ emitted grows by realize c, seen grows by merge_key c.
             Recurse; reconcile the two `emitted` sets. *)
          simpl. rewrite Eseen.
          (* new emitted = realize c :: emitted; new seen covers it. *)
          assert (Hsc' : seen_covered (merge_key c :: seen)
                                      (realize c :: emitted)).
          { unfold seen_covered. intros k Hk.
            destruct Hk as [Hkhd | Hktl].
            - (* k = merge_key c: any cleared cursor c' with this key realizes
                 = realize c (cleared_merge_preserves_realize), hence in the
                 new emitted head. *)
              subst k. unfold key_realize_covered. intros c' Hc'cl Hc'k.
              left.
              apply (cleared_merge_preserves_realize c c' Hccl Hc'cl).
              unfold merges. rewrite Hc'k. reflexivity.
            - (* k ∈ seen: covered by old emitted ⊆ new emitted. *)
              unfold key_realize_covered. intros c' Hc'cl Hc'k.
              right. apply (Hsc k Hktl c' Hc'cl Hc'k). }
          destruct (IH (merge_key c :: seen) (realize c :: emitted) t
                       Hrestcl Hsc' Htl) as [Hem | Hout].
          -- (* t ∈ realize c :: emitted: either = realize c (⇒ in output
                head) or ∈ emitted (⇒ left). *)
             destruct Hem as [Heqc | Hemold].
             ++ right. unfold realized_terms. simpl. left. exact Heqc.
             ++ left. exact Hemold.
          -- (* t ∈ output of recursion ⇒ in output (it is the tail). *)
             right. unfold realized_terms. simpl. right. exact Hout.
  Qed.

  Lemma merge_dedup_realize_superset_cleared :
    forall frontier t,
      all_cleared frontier ->
      In t (realized_terms frontier) ->
      In t (realized_terms (merge_dedup frontier)).
  Proof.
    intros frontier t Hcl Hin. unfold merge_dedup.
    destruct (merge_dedup_acc_covers_cleared frontier [] [] t Hcl)
      as [Hem | Hout].
    - (* seen = [] is trivially covered by emitted = []. *)
      unfold seen_covered. intros k Hk. destruct Hk.
    - exact Hin.
    - destruct Hem.   (* In t [] is False *)
    - exact Hout.
  Qed.

  (* The clear+dedup realized term-set equality (set-membership both ways). *)
  Theorem collection_lex_fork_clear_preserves_realized_terms :
    forall frontier t,
      In t (realized_terms (merge_dedup (map clear_lex_fork frontier))) <->
      In t (realized_terms frontier).
  Proof.
    intros frontier t. split.
    - (* ⊆ : dedup-then-clear realizes a subset of clear, = original. *)
      intro Hin.
      apply merge_dedup_realize_subset in Hin.
      rewrite realized_set_invariant_under_clear_all in Hin. exact Hin.
    - (* ⊇ : every original term is realized by the cleared frontier (T2),
         and survives dedup (superset lemma, cleared invariant). *)
      intro Hin.
      rewrite <- realized_set_invariant_under_clear_all in Hin.
      apply merge_dedup_realize_superset_cleared.
      + apply clear_all_is_cleared.
      + exact Hin.
  Qed.

End CollectionLexForkClearSoundness.

(* ════════════════════════════════════════════════════════════════════════
   NON-VACUITY / INSTANTIATION SANITY: a concrete model where Obs = nat,
   Term = nat, decode = id, Genuine = nat, genuine_of = id. The SPPF-sharing
   hypothesis `genuine_determines_realize` holds because genuine_of = id =
   decode-key, so equal genuine keys ⇒ equal obs ⇒ equal realize. This shows
   the parametric section is non-vacuous and the clear+dedup theorem is a
   CLOSED instance.
   ════════════════════════════════════════════════════════════════════════ *)

Section ClearSoundnessInstance.

  Definition nat_obs_eq_dec := Nat.eq_dec.
  Definition nat_genuine_eq_dec := Nat.eq_dec.

  (* Obs = nat, Term = nat, decode = id, Genuine = nat, genuine_of = id. *)
  Let Obs := nat.
  Let Term := nat.

  (* genuine_of = id ⇒ equal genuine keys ⇒ equal observations ⇒ equal
     realize (decode = id). This discharges the SPPF-sharing hypothesis as a
     PROVED fact for the instance. *)
  Lemma nat_genuine_determines_realize :
    forall c1 c2 : cursor nat,
      genuine_key nat nat (fun o => o) c1 = genuine_key nat nat (fun o => o) c2 ->
      realize nat nat (fun o => o) c1 = realize nat nat (fun o => o) c2.
  Proof.
    intros c1 c2 H. unfold genuine_key, realize in *. simpl in *.
    rewrite H. reflexivity.
  Qed.

  (* The instantiated top-level theorem — a CLOSED instance. *)
  Theorem nat_collection_clear_preserves_realized :
    forall frontier t,
      In t (realized_terms nat nat (fun o => o)
              (merge_dedup nat nat nat_genuine_eq_dec (fun o => o)
                 (map (clear_lex_fork nat) frontier))) <->
      In t (realized_terms nat nat (fun o => o) frontier).
  Proof.
    intros frontier t.
    apply (collection_lex_fork_clear_preserves_realized_terms
             nat nat (fun o => o) nat nat_genuine_eq_dec (fun o => o)
             nat_genuine_determines_realize).
  Qed.

  (* Non-vacuity witness: a 3-element frontier (the three lexical readings of
     ONE collection element: Int/BigInt/BigRat reductions to the SAME Proc
     Symbol = same obs `42`) with DISTINCT sidecars (distinct lexical stamps).
     Pre-fix they are 3 separate cursors; clear+dedup collapses them to ONE
     while preserving the realized term {42}. *)
  Definition reading_int  : cursor nat :=
    {| cur_obs := 42; cur_sidecar := [(1, 0, 0, 7)] |}.
  Definition reading_bigi : cursor nat :=
    {| cur_obs := 42; cur_sidecar := [(1, 2, 0, 10)] |}.
  Definition reading_bigr : cursor nat :=
    {| cur_obs := 42; cur_sidecar := [(1, 2, 0, 11)] |}.

  Definition three_readings : list (cursor nat) :=
    [reading_int; reading_bigi; reading_bigr].

  (* The three readings have distinct merge keys PRE-clear (distinct
     lex_fork_last), so the gate keeps 3 arcs — the 3^N cross-product seed. *)
  Theorem three_readings_distinct_before_clear :
    merge_key nat nat (fun o => o) reading_int
      <> merge_key nat nat (fun o => o) reading_bigi.
  Proof.
    unfold merge_key, lex_fork_last, genuine_key,
      reading_int, reading_bigi. simpl.
    intro H. inversion H.
  Qed.

  (* After clear+dedup, the frontier collapses to ONE cursor and the realized
     term-set is exactly {42}. *)
  Theorem three_readings_collapse_to_one_term :
    realized_terms nat nat (fun o => o)
      (merge_dedup nat nat nat_genuine_eq_dec (fun o => o)
         (map (clear_lex_fork nat) three_readings)) = [42].
  Proof.
    vm_compute. reflexivity.
  Qed.

End ClearSoundnessInstance.

(* ════════════════════════════════════════════════════════════════════════
   ASSUMPTION AUDIT.
   ════════════════════════════════════════════════════════════════════════ *)

Print Assumptions clear_preserves_observation.
Print Assumptions realized_set_invariant_under_clear_all.
Print Assumptions merge_relaxation_only_collapses_obs_equal.
Print Assumptions clear_is_input_change_not_gate_change.
Print Assumptions sidecar_not_read_by_realizer.
Print Assumptions collection_lex_fork_clear_preserves_realized_terms.
Print Assumptions nat_collection_clear_preserves_realized.
Print Assumptions three_readings_collapse_to_one_term.
