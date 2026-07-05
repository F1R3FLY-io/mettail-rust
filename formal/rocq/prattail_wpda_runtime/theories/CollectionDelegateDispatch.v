(*
 * CollectionDelegateDispatch: FV-FIRST spec for ROOT-B — the source-committed
 * multi-length fall-through that lets a cross-cat collection projection whose
 * open token is MULTI-CHAR and lex-ambiguous (RhoCalc Pathmap `{|…|}`, open
 * `{|`) actually ENTER its source category (cat 14) instead of re-projecting
 * across the numeric cats (the SnapshotDuplicate storm).
 *
 * THE DEFECT (trace-evidenced; `Proc::parse("{|1:2|}")` fails in ALL contexts,
 * including `*@{|1:2|}` — i.e. context-INDEPENDENT, an ENTRY failure):
 *   `{|` is lex-ambiguous (`{|` len 2 — the Pathmap open — vs `{` len 1 — the
 *   PPar/Map open), so the prefix-dispatch lex-fork
 *   (`forks.rs emit_lex_fork_at_prefix_dispatch`) fires. The Pathmap projection
 *   (`CastPathmap . m:Pathmap |- m : Proc`, `CrossCatProjection{source=14}`)
 *   should fall through to normal dispatch — which owns the cat-14 `{|`
 *   collection arm (guard `state_cat_src_idx == 14`). But the fall-through gate
 *   `__fall_through` (`forks.rs:522-528`) requires `__all_alts_same_length`,
 *   which is FALSE for `{|`(len 2) vs `{`(len 1) → no fall-through → the inner
 *   `1:2` re-projects across ~6 numeric cats, never interning cat 14.
 *
 * THE FIX (this spec, ROOT-B):
 *   (1) forks.rs — a SOURCE-COMMITTED multi-length fall-through: relax the
 *       `__all_alts_same_length` requirement ONLY when the cursor is inside a
 *       CrossCatDelegate whose source == primary_src AND the primary owns a
 *       normal dispatch arm AND the primary is the maximal munch (longest alt).
 *       Unscoped multi-length (`-3` = {Minus@1, Integer@2}, `x < -c`) is
 *       byte-identical (it is NOT source-committed).
 *   (2) wpda_walker.rs — the CrossCatDelegate frame establishes
 *       `state_cat_src_idx = source`, so the normal-dispatch source-collection
 *       arm (guarded `state_cat_src_idx == source`) matches and the delegate
 *       ENTERS the source collection.
 *
 * THE MODEL mirrors `LexForkKeywordReservation.v` (Alt = kind + end-byte span;
 * `representable` = LexAltRuleKind-representable; `has_dispatch` =
 * `prefix_primary_has_dispatch_rule`) and adds the source-committed dimension
 * plus the delegate-frame source-cat establishment.
 *
 * THEOREMS (all admission-free; each audited by `Print Assumptions`, which must
 * report "Closed under the global context"):
 *   delegate_enters_source_collection         — source-committed + primary owns a
 *                                                dispatch arm + primary is max-munch
 *                                                ⇒ the fall-through fires AND the
 *                                                delegate-established state_cat =
 *                                                source makes the source-collection
 *                                                arm fire (the delegate ENTERS cat 14).
 *   multilength_source_committed_fallthrough_no_loss
 *                                              — the no-loss witness: a `{|` open
 *                                                (NOT lex-alt-representable, but
 *                                                dispatch-owning) with one shorter
 *                                                representable `{` secondary — the OLD
 *                                                decision FORKS (loses cat 14), the
 *                                                NEW decision FALLS THROUGH (recovers).
 *                                                Mirrors LexForkKeywordReservation
 *                                                buggy_lexfork_drops_collection_keyword;
 *                                                the recovered dispatch realizes the
 *                                                source term with no loss (cf.
 *                                                CollectionLexForkClearSoundness T1/T2,
 *                                                clear_preserves_observation /
 *                                                realized_set_invariant_under_clear_all).
 *   multilength_unrelated_unaffected           — regression-safety: when NOT
 *                                                source-committed the new
 *                                                fall-through equals the old one,
 *                                                so genuine multi-length
 *                                                disambiguation (`-3`, `x < -c`) is
 *                                                byte-identical (mirrors
 *                                                LexForkKeywordReservation
 *                                                multilength_guard).
 *   delegate_dispatch_no_spurious_wrap         — evidence-gated: whenever the new
 *                                                disjunct is what flips the
 *                                                decision, ALL THREE guards held
 *                                                (source-committed, dispatch-owning,
 *                                                max-munch) — never a heuristic
 *                                                fall-through.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.

Section CollectionDelegateDispatch.

  (* A lexical alternative at one DAG position: a token kind and an end-byte
     span (mirror LexForkKeywordReservation.Alt). *)
  Record Alt : Type := { akind : nat; alen : nat }.

  (* Per-language classifiers (abstracted on Section close — NOT axioms). *)
  Variable representable : nat -> bool.   (* LexAltRuleKind-representable      *)
  Variable has_dispatch  : nat -> bool.   (* prefix_primary_has_dispatch_rule  *)

  Definition primary_survived (primary : Alt) : bool := representable (akind primary).

  Definition num_branches (primary : Alt) (secs : list Alt) : nat :=
    (if representable (akind primary) then 1 else 0)
    + length (filter (fun s => representable (akind s)) secs).

  (* `__all_alts_same_length`. *)
  Definition all_same_length (primary : Alt) (secs : list Alt) : bool :=
    forallb (fun s => Nat.eqb (alen s) (alen primary)) secs.

  (* The primary is the MAXIMAL MUNCH: its end-byte span is ≥ every secondary's
     (the longest lexical alternative — `{|` over `{`). *)
  Definition is_max_munch (primary : Alt) (secs : list Alt) : bool :=
    forallb (fun s => Nat.leb (alen s) (alen primary)) secs.

  (* `__fall_through` BEFORE ROOT-B (the three relevant disjuncts; the
     crosscat-LHS disjunct is orthogonal — it is gated by the same
     all_same_length and never interacts with the source-committed flag, so it is
     elided for model clarity, exactly as LexForkKeywordReservation models the
     keyword-reservation disjunct in isolation). *)
  Definition fall_through_old (primary : Alt) (secs : list Alt) : bool :=
    Nat.eqb (num_branches primary secs) 0
    || (Nat.eqb (num_branches primary secs) 1 && primary_survived primary)
    || (has_dispatch (akind primary) && all_same_length primary secs).

  (* `__fall_through` AFTER ROOT-B: the new SOURCE-COMMITTED disjunct fires only
     when the cursor is inside a CrossCatDelegate whose source == primary_src
     (`source_committed`), the primary owns a normal dispatch arm
     (`has_dispatch`), the primary is NOT lex-alt-representable
     (`negb (representable ...)` — a collection open such as `{|` has no
     `LexAltRuleKind`; a literal/projection/keyword like `-3`'s Integer DOES, so
     this conjunct keeps `-3` forking EVEN inside a numeric-cat sub-parse), and
     the primary is the maximal munch — WITHOUT requiring all_same_length. The
     `negb representable` conjunct is the cross-language regression fence:
     `representable_primary_unaffected` proves any representable max-munch
     primary (every literal) is byte-identical. *)
  Definition fall_through_new
      (source_committed : bool) (primary : Alt) (secs : list Alt) : bool :=
    fall_through_old primary secs
    || (source_committed
        && has_dispatch (akind primary)
        && negb (representable (akind primary))
        && is_max_munch primary secs).

  (* ── Delegate-frame source-cat establishment (wpda_walker.rs:9398-9416 /
        delegate alloc 22036-22075). The CrossCatDelegate frame sets the dispatch
        category to its source, so the normal-dispatch source-collection arm
        (guard: open-token kind AND state_cat == source) matches. ── *)
  Variable source_open_kind : nat.   (* the source collection's open kind (`{|` for Pathmap) *)
  Variable source_cat : nat.         (* the delegate's source category (14 = Pathmap)        *)

  (* The delegate frame establishes state_cat = source_cat. *)
  Definition delegate_state_cat : nat := source_cat.

  (* The normal-dispatch source-collection arm fires iff the dispatched kind is
     the source's open token AND the dispatch category is the source. *)
  Definition source_collection_arm_fires (kind state_cat : nat) : bool :=
    Nat.eqb kind source_open_kind && Nat.eqb state_cat source_cat.

  (* ══════════════ delegate_enters_source_collection ══════════════
     When the cursor is source-committed, the primary owns a dispatch arm, the
     primary is the maximal munch, AND the primary IS the source's open token:
       (a) the lex-fork falls through (new disjunct), so normal dispatch runs on
           the primary kind; AND
       (b) the delegate-established state_cat = source makes the
           source-collection arm fire — the delegate ENTERS the source collection
           (cat 14), instead of re-projecting. *)
  Theorem delegate_enters_source_collection :
    forall (primary : Alt) (secs : list Alt),
      has_dispatch (akind primary) = true ->
      representable (akind primary) = false ->
      is_max_munch primary secs = true ->
      akind primary = source_open_kind ->
      fall_through_new true primary secs = true
      /\ source_collection_arm_fires (akind primary) delegate_state_cat = true.
  Proof.
    intros primary secs Hd Hr Hmm Hk. split.
    - unfold fall_through_new.
      assert (Hdisj :
        (true && has_dispatch (akind primary)
              && negb (representable (akind primary))
              && is_max_munch primary secs) = true).
      { rewrite Hd, Hr, Hmm. reflexivity. }
      rewrite Hdisj. apply orb_true_r.
    - unfold source_collection_arm_fires, delegate_state_cat.
      rewrite Hk. rewrite Nat.eqb_refl, Nat.eqb_refl. reflexivity.
  Qed.

  (* ══════════════ multilength_source_committed_fallthrough_no_loss ══════════════
     The no-loss WITNESS (non-vacuity): kind 0 = the `{|` Pathmap collection open
     — NOT lex-alt-representable but dispatch-owning, span 2; kind 1 = the `{`
     Map-projection secondary — representable, span 1. The OLD decision does NOT
     fall through (it FORKS the representable `{` secondary → re-projection, cat 14
     LOST); the NEW source-committed decision FALLS THROUGH (normal dispatch owns
     the cat-14 `{|` arm → recovered). Mirrors LexForkKeywordReservation
     buggy_lexfork_drops_collection_keyword. The recovered dispatch realizes the
     source term with no loss — cf. CollectionLexForkClearSoundness T1/T2. *)
  Theorem multilength_source_committed_fallthrough_no_loss :
    representable 0 = false ->
    representable 1 = true ->
    has_dispatch 0 = true ->
    fall_through_old {| akind := 0; alen := 2 |} [{| akind := 1; alen := 1 |}] = false
    /\ fall_through_new true
         {| akind := 0; alen := 2 |} [{| akind := 1; alen := 1 |}] = true.
  Proof.
    intros Hr0 Hr1 Hd0.
    unfold fall_through_new, fall_through_old, num_branches, primary_survived,
           all_same_length, is_max_munch.
    cbn [akind alen filter length].
    rewrite Hr0, Hr1, Hd0.
    cbn.
    split; reflexivity.
  Qed.

  (* ══════════════ multilength_unrelated_unaffected ══════════════
     Regression-safety: when the cursor is NOT source-committed, the new
     fall-through is byte-identical to the old one. The source-committed flag
     gates the entire new disjunct, so genuine multi-length disambiguation
     (`-3` = {Minus@1, Integer@2}, `x < -c`) — which is never inside a collection
     source delegate — is unperturbed. Mirrors LexForkKeywordReservation
     multilength_guard. *)
  Theorem multilength_unrelated_unaffected :
    forall (primary : Alt) (secs : list Alt),
      fall_through_new false primary secs = fall_through_old primary secs.
  Proof.
    intros primary secs. unfold fall_through_new.
    assert (Hdisj :
      (false && has_dispatch (akind primary)
             && negb (representable (akind primary))
             && is_max_munch primary secs) = false).
    { reflexivity. }
    rewrite Hdisj. apply orb_false_r.
  Qed.

  (* Even when source-committed, a NON-max-munch alternative leaves the decision
     unchanged — the fix never fires on a non-longest lexing. *)
  Theorem source_committed_non_maxmunch_unaffected :
    forall (sc : bool) (primary : Alt) (secs : list Alt),
      is_max_munch primary secs = false ->
      fall_through_new sc primary secs = fall_through_old primary secs.
  Proof.
    intros sc primary secs Hmm. unfold fall_through_new.
    rewrite Hmm. rewrite andb_false_r. apply orb_false_r.
  Qed.

  (* ══════════════ representable_primary_unaffected ══════════════
     The cross-language regression fence: a max-munch primary that IS
     lex-alt-representable (every literal/projection/keyword — e.g. `-3`'s
     Integer, even inside a numeric-cat sub-parse) leaves the decision
     byte-identical, REGARDLESS of source-commitment. The `negb representable`
     conjunct neutralizes the new disjunct for all representable primaries — so
     genuine multi-length disambiguation of literals always keeps forking. *)
  Theorem representable_primary_unaffected :
    forall (sc : bool) (primary : Alt) (secs : list Alt),
      representable (akind primary) = true ->
      fall_through_new sc primary secs = fall_through_old primary secs.
  Proof.
    intros sc primary secs Hr. unfold fall_through_new.
    assert (Hdisj :
      (sc && has_dispatch (akind primary)
          && negb (representable (akind primary))
          && is_max_munch primary secs) = false).
    { rewrite Hr.
      now destruct sc, (has_dispatch (akind primary)), (is_max_munch primary secs). }
    rewrite Hdisj. apply orb_false_r.
  Qed.

  (* ══════════════ delegate_dispatch_no_spurious_wrap ══════════════
     Evidence-gated: whenever the NEW disjunct is what flips a non-fall-through
     into a fall-through (old = false, new = true), ALL THREE guards held —
     source-committed, dispatch-owning, and max-munch. The source-committed
     fall-through is therefore never a heuristic prune: it fires only on genuine
     source-collection-open evidence (no spurious wrap of an arbitrary token). *)
  Theorem delegate_dispatch_no_spurious_wrap :
    forall (sc : bool) (primary : Alt) (secs : list Alt),
      fall_through_new sc primary secs = true ->
      fall_through_old primary secs = false ->
      sc = true
      /\ has_dispatch (akind primary) = true
      /\ representable (akind primary) = false
      /\ is_max_munch primary secs = true.
  Proof.
    intros sc primary secs Hnew Hold.
    unfold fall_through_new in Hnew. rewrite Hold in Hnew.
    rewrite orb_false_l in Hnew.
    apply andb_true_iff in Hnew. destruct Hnew as [H1 Hmm].
    apply andb_true_iff in H1. destruct H1 as [H2 Hnr].
    apply andb_true_iff in H2. destruct H2 as [Hsc Hd].
    apply negb_true_iff in Hnr.
    repeat split; assumption.
  Qed.

  (* ── `-3` regression witnesses (non-vacuity of the regression-safety claim).
        kind 0 = Minus@span1 (representable), kind 1 = Integer@span2
        (representable). NOT source-committed. The fix is INERT (new = old) and
        the OLD decision FORKS (num_branches = 2 ≠ 0/1, lengths differ) — both
        lexings are kept, exactly as before ROOT-B. ── *)
  Theorem minus_three_unaffected :
    fall_through_new false {| akind := 0; alen := 1 |} [{| akind := 1; alen := 2 |}]
      = fall_through_old {| akind := 0; alen := 1 |} [{| akind := 1; alen := 2 |}].
  Proof. apply multilength_unrelated_unaffected. Qed.

  Theorem minus_three_old_forks :
    representable 0 = true ->
    representable 1 = true ->
    fall_through_old {| akind := 0; alen := 1 |} [{| akind := 1; alen := 2 |}] = false.
  Proof.
    intros Hr0 Hr1.
    unfold fall_through_old, num_branches, primary_survived, all_same_length.
    cbn [akind alen filter length].
    rewrite Hr0, Hr1.
    cbn.
    (* num_branches = 2: first two disjuncts false; all_same_length false (2≠1)
       so the third is false regardless of has_dispatch. *)
    now rewrite andb_false_r.
  Qed.

End CollectionDelegateDispatch.

(* ═════════════════ Assumption audit — must all print
   "Closed under the global context" ═════════════════ *)
Print Assumptions delegate_enters_source_collection.
Print Assumptions multilength_source_committed_fallthrough_no_loss.
Print Assumptions multilength_unrelated_unaffected.
Print Assumptions source_committed_non_maxmunch_unaffected.
Print Assumptions representable_primary_unaffected.
Print Assumptions delegate_dispatch_no_spurious_wrap.
Print Assumptions minus_three_unaffected.
Print Assumptions minus_three_old_forks.
