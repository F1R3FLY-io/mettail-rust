(*
 * CollectionForkEvidence: the spec for the #307 ROOT-F fix — the
 * CollectionLoop post-element fork emits ONLY evidence-justified branches.
 *
 * THE DEFECT (trace-evidenced; rhocalc PPar `"{" ps.*sep("|") "}"`):
 * the generated kv_phase=0 three-way fork (collection.rs:401-472) emits,
 * UNCONDITIONALLY at every post-element position:
 *   BRANCH 1 (close)        — consumes ONE token REGARDLESS of its text
 *                             (the pseudo-close: `{0|1}` finalizes a PPar
 *                             after eating `|` at position 2 ⇒ the `{0}`
 *                             sub-multiset alternative);
 *   BRANCH 2 (sep·element)  — checked (matches the separator) — CORRECT;
 *   BRANCH 3 (bare element) — dispatches the next element with NO
 *                             separator, even for explicit-separator
 *                             grammars (`{c d}` parses as a 2-element
 *                             multiset; `{c!(p)}`'s send is split into
 *                             elements `c`, `p` that win the splice race).
 * The realize-layer cannot refute the junk: `min_terminal_span` is 0 for
 * collection rules (early-true) and the collection symbol's zero-width
 * span triggers the synthetic-node escape.
 *
 * THE FIX (this spec):
 *   G1 the close branch is a TEXT-MEMBERSHIP consume over the position's
 *      complete out-edge set (the MixfixLiteralAccounting/ROOT-A checked
 *      discipline) — emitted only when a close-labelled edge exists, one
 *      branch per matching edge, advancing along the MATCHED edge;
 *   G2 the sep branch stays checked (already correct);
 *   G3 the bare-element branch is emitted ONLY for separator-free
 *      (sep_empty) collection grammars;
 *   G4 if no branch is licensed, the cursor errors (advance-or-die) —
 *      proven safe: no licensed branch ⇒ no word of the collection
 *      continuation language from that position.
 *
 * THE MODEL: input = a lex DAG (node → labelled out-edges), elements as
 * an abstract end-relation. `loop_lang` is the collection continuation
 * language after a completed element: (sep · elem)* · close for
 * explicit-separator grammars, (elem)* · close for sep_empty grammars.
 * Theorems:
 *   T1 gated_run_iff_loop_lang — the gated machine accepts EXACTLY the
 *      language (soundness + completeness = NO-LOSS: removing the
 *      ungated branches loses no valid parse);
 *   T2 pseudo_close_overgenerates — the shipped unchecked close accepts
 *      a configuration outside the language (the `{0}` defect,
 *      non-vacuous);
 *   T3 bare_element_overgenerates — the shipped bare-element branch
 *      accepts a separator-free word outside an explicit-separator
 *      language (the `{c d}` defect, non-vacuous);
 *   T4 shipped_contains_language — the shipped machine over-generates
 *      but does not lose (the fix is REMOVING over-generation; nothing
 *      needs adding);
 *   T5 gated_subset_shipped — gating only removes branches;
 *   T6 no_branch_no_word — G4 advance-or-die is sound;
 *   T7 gated_close_lands_on_real_edge — no fabricated positions
 *      (coverage corollary: every gated finalization consumes an actual
 *      close-labelled DAG edge; the realize-layer covering-span check
 *      transcribes this obligation).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Section CollectionForkEvidence.

  (* Lex DAG: nodes are nats; out-edges are (label, target) pairs. *)
  Definition Edge : Type := (nat * nat)%type.   (* (label, target) *)
  Variable out_edges : nat -> list Edge.

  (* The collection grammar's literals. *)
  Variable l_close : nat.
  Variable l_sep   : nat.

  (* Elements abstractly: elem_spell n m = an element parse starting at
     node n ends at node m (the element sub-parser's accept relation). *)
  Variable elem_spell : nat -> nat -> Prop.

  (* Whether the grammar declares an EMPTY separator (whitespace-joined
     collections). rhocalc PPar has sep = "|" (nonempty). *)
  Variable sep_empty : bool.

  (* ── The collection CONTINUATION language after a completed element:
        (sep · elem)* · close   [explicit-separator grammars]
        (elem)* · close         [sep_empty grammars]                 ── *)

  Inductive loop_lang : nat -> nat -> Prop :=
    | ll_close : forall n t,
        In (l_close, t) (out_edges n) ->
        loop_lang n t
    | ll_sep : forall n t e m,
        sep_empty = false ->
        In (l_sep, t) (out_edges n) ->
        elem_spell t e ->
        loop_lang e m ->
        loop_lang n m
    | ll_bare : forall n e m,
        sep_empty = true ->
        elem_spell n e ->
        loop_lang e m ->
        loop_lang n m.

  (* ── The GATED machine (the fix): every branch evidence-licensed. ── *)

  Inductive gated_run : nat -> nat -> Prop :=
    | gr_close : forall n t,
        In (l_close, t) (out_edges n) ->          (* G1 checked close *)
        gated_run n t
    | gr_sep : forall n t e m,
        sep_empty = false ->
        In (l_sep, t) (out_edges n) ->            (* G2 checked sep   *)
        elem_spell t e ->
        gated_run e m ->
        gated_run n m
    | gr_bare : forall n e m,
        sep_empty = true ->                        (* G3 sep_empty-only *)
        elem_spell n e ->
        gated_run e m ->
        gated_run n m.

  (* ── The SHIPPED machine (the defect): close unchecked; bare
        unconditional. The sep branch was already checked. ── *)

  Inductive shipped_run : nat -> nat -> Prop :=
    | sr_close_unchecked : forall n l t,
        In (l, t) (out_edges n) ->                 (* ANY edge "closes" *)
        shipped_run n t
    | sr_sep : forall n t e m,
        In (l_sep, t) (out_edges n) ->
        elem_spell t e ->
        shipped_run e m ->
        shipped_run n m
    | sr_bare : forall n e m,
        elem_spell n e ->                          (* no separator gate *)
        shipped_run e m ->
        shipped_run n m.

  (* ── T1 — the gated machine accepts EXACTLY the language.
        Soundness + completeness in one: gating is NO-LOSS. ── *)
  Theorem gated_run_iff_loop_lang :
    forall n m, gated_run n m <-> loop_lang n m.
  Proof.
    intros n m. split; intro H.
    - induction H.
      + apply ll_close; assumption.
      + apply (ll_sep n t e m); assumption.
      + apply (ll_bare n e m); assumption.
    - induction H.
      + apply gr_close; assumption.
      + apply (gr_sep n t e m); assumption.
      + apply (gr_bare n e m); assumption.
  Qed.

  (* ── T4 — the shipped machine CONTAINS the language: the defect is
        pure over-generation, so the fix removes branches and adds
        nothing. ── *)
  Theorem shipped_contains_language :
    forall n m, loop_lang n m -> shipped_run n m.
  Proof.
    intros n m H. induction H.
    - apply (sr_close_unchecked n l_close t). assumption.
    - apply (sr_sep n t e m); assumption.
    - apply (sr_bare n e m); assumption.
  Qed.

  (* ── T5 — gating only removes branches (gated ⊆ shipped). ── *)
  Theorem gated_subset_shipped :
    forall n m, gated_run n m -> shipped_run n m.
  Proof.
    intros n m H. induction H.
    - apply (sr_close_unchecked n l_close t). assumption.
    - apply (sr_sep n t e m); assumption.
    - apply (sr_bare n e m); assumption.
  Qed.

  (* ── T6 — advance-or-die is SOUND: if no gated branch is licensed at
        n, then NO word of the continuation language starts at n, so
        erroring the cursor drops nothing. ── *)
  Theorem no_branch_no_word :
    forall n,
      (forall t, ~ In (l_close, t) (out_edges n)) ->
      (sep_empty = false -> forall t, ~ In (l_sep, t) (out_edges n)) ->
      (sep_empty = true -> forall e, ~ elem_spell n e) ->
      forall m, ~ loop_lang n m.
  Proof.
    intros n Hclose Hsep Hbare m H.
    inversion H; subst.
    - eapply Hclose; eassumption.
    - eapply Hsep; eassumption.
    - eapply Hbare; eassumption.
  Qed.

  (* ── T7 — every gated finalization lands on a REAL close edge: the
        end position is an actual DAG target reached by consuming the
        close literal (no fabrication; the realize-layer covering-span
        check transcribes this: a collection packing's final token IS
        the close delimiter at the symbol's end). ── *)
  Theorem gated_close_lands_on_real_edge :
    forall n m, gated_run n m ->
      exists p, In (l_close, m) (out_edges p).
  Proof.
    intros n m H. induction H.
    - exists n. assumption.
    - assumption.
    - assumption.
  Qed.

End CollectionForkEvidence.

(* ════════════════════════════════════════════════════════════════════
   DEFECT WITNESSES (non-vacuity): concrete finite instantiations where
   the shipped machine accepts configurations OUTSIDE the language.
   Labels: 0 = close ("}"), 1 = sep ("|").
   ════════════════════════════════════════════════════════════════════ *)

Section DefectWitnesses.

  (* ── T2 — PSEUDO-CLOSE: at node 0 the only out-edge is the SEPARATOR
        (input `{0|1}` after element `0`: the next token is `|`). The
        shipped unchecked close consumes it and finalizes ⇒ the `{0}`
        sub-multiset. The language admits no finalization there. ── *)

  Definition pc_edges (n : nat) : list (nat * nat) :=
    match n with
    | 0 => [(1, 1)]          (* only the sep edge `|` → node 1 *)
    | _ => []
    end.
  Definition pc_elem (_ _ : nat) : Prop := False.

  Theorem pseudo_close_overgenerates :
    shipped_run pc_edges 1 pc_elem 0 1
    /\ ~ loop_lang pc_edges 0 1 pc_elem false 0 1.
  Proof.
    split.
    - apply (sr_close_unchecked pc_edges 1 pc_elem 0 1 1).
      simpl. left. reflexivity.
    - intro H. inversion H; subst.
      + (* ll_close: needs (0, 1) ∈ [(1, 1)] — label mismatch *)
        simpl in *. intuition congruence.
      + (* ll_sep: pc_elem = False *)
        unfold pc_elem in *. contradiction.
      + (* ll_bare: sep_empty = false ≠ true *)
        discriminate.
  Qed.

  (* ── T3 — BARE ELEMENT: input `{c d}` after element `c` at node 0:
        no close edge, no sep edge at 0; an element `d` spells 0→1; the
        real close `}` is at 1. The shipped bare-element branch accepts
        (two adjacent elements, NO separator) — the explicit-separator
        language does not. ── *)

  Definition be_edges (n : nat) : list (nat * nat) :=
    match n with
    | 1 => [(0, 2)]          (* the real close `}` → node 2 *)
    | _ => []
    end.
  Definition be_elem (n m : nat) : Prop := n = 0 /\ m = 1.

  Theorem bare_element_overgenerates :
    shipped_run be_edges 1 be_elem 0 2
    /\ ~ loop_lang be_edges 0 1 be_elem false 0 2.
  Proof.
    split.
    - apply (sr_bare be_edges 1 be_elem 0 1 2).
      + split; reflexivity.
      + apply (sr_close_unchecked be_edges 1 be_elem 1 0 2).
        simpl. left. reflexivity.
    - intro H. inversion H; subst.
      + (* ll_close at 0: out_edges 0 = [] *)
        simpl in *. contradiction.
      + (* ll_sep at 0: out_edges 0 = [] *)
        simpl in *. contradiction.
      + (* ll_bare: sep_empty = false ≠ true *)
        discriminate.
  Qed.

  (* ── Sanity: the gated machine still accepts the REAL words. The
        valid continuation `| 1 }` from node 0:
        edges 0 --sep--> 1, elem 1→2, 2 --close--> 3. ── *)

  Definition ok_edges (n : nat) : list (nat * nat) :=
    match n with
    | 0 => [(1, 1)]          (* sep `|` *)
    | 2 => [(0, 3)]          (* close `}` *)
    | _ => []
    end.
  Definition ok_elem (n m : nat) : Prop := n = 1 /\ m = 2.

  Theorem gated_accepts_valid_word :
    gated_run ok_edges 0 1 ok_elem false 0 3.
  Proof.
    apply (gr_sep ok_edges 0 1 ok_elem false 0 1 2 3).
    - reflexivity.
    - simpl. left. reflexivity.
    - split; reflexivity.
    - apply (gr_close ok_edges 0 1 ok_elem false 2 3).
      simpl. left. reflexivity.
  Qed.

End DefectWitnesses.

(* ════════════════════════════════════════════════════════════════════
   ACTION SEMANTICS (red-team round-1 additions — both critics converged
   on the transcription gap): the close is not an abstract edge step, it
   is a CONSUME-AT × POP × FINALIZE. The three candidate actions:

     ConsumeAtAndReplace { next_pos } — advances along the matched edge
       but performs NO GSS mutation (a mid-rule self-advance; correct
       for ROOT-A's mixfix literals, WRONG for a collection close);
     ConsumeAndPop                    — pops + finalizes but advances
       along edge alt-0 ONLY (child_next_pos is alt-0-hardwired; wrong
       for a lattice-ambiguous close such as the rhocalc Bag `}#`);
     ConsumeAtAndPop { next_pos }     — the REQUIRED new action: pops +
       finalizes AND advances along the MATCHED edge.

   The model: a configuration is (node, frame stack). Acceptance =
   empty stack. Theorems:
     A1 replace_close_cannot_finalize — the Replace-shaped close leaves
        the frame on the stack: NO collection word is ever accepted
        (the total-regression both critics predicted, non-vacuous);
     A2 alt0_close_lands_on_wrong_target — the alt-0-pop close advances
        to a NON-close target when the close edge is not alt-0 (the
        Bag `}#` lattice-loss class, non-vacuous);
     A3 consume_at_and_pop_sound_complete — the new action accepts
        EXACTLY the close-edge relation: it pops the frame AND lands on
        the matched close target (`gated_close_pops_and_finalizes`);
     A4 advance_or_die_emits_error — the branch BUILDER returns an
        empty branch list exactly when no gated branch is licensed; the
        transcription obligation is `empty ⇒ WpdaStepAction::Error`
        (never an empty Fork, which silently deletes the cursor).
   ════════════════════════════════════════════════════════════════════ *)

Section ActionSemantics.

  Variable out_edges : nat -> list (nat * nat).
  Variable l_close : nat.

  (* Configurations: (position node, frame stack). The collection frame
     is the head; acceptance of the collection requires popping it. *)
  Definition Config : Type := (nat * list nat)%type.

  (* Matching close targets at a node — the membership discipline
     (peek_text + peek_alternatives, deduped). *)
  Definition close_targets (n : nat) : list nat :=
    map snd (filter (fun e => Nat.eqb (fst e) l_close) (out_edges n)).

  Lemma close_targets_in :
    forall n t, In t (close_targets n) <-> In (l_close, t) (out_edges n).
  Proof.
    intros n t. unfold close_targets. rewrite in_map_iff. split.
    - intros [[l' t'] [Hsnd Hin]]. simpl in Hsnd. subst t'.
      apply filter_In in Hin. destruct Hin as [Hin Heq].
      simpl in Heq. apply Nat.eqb_eq in Heq. subst l'. exact Hin.
    - intro Hin. exists (l_close, t). split; [reflexivity |].
      apply filter_In. split; [exact Hin |]. simpl. apply Nat.eqb_refl.
  Qed.

  (* ── The three action shapes as configuration steps. ── *)

  (* ConsumeAtAndReplace-shaped close: advance, NO pop. *)
  Definition replace_close_step (c c' : Config) : Prop :=
    exists t, In (l_close, t) (out_edges (fst c))
      /\ c' = (t, snd c).

  (* ConsumeAndPop-shaped close: pop, advance along edge ALT-0
     (whatever its label). *)
  Definition alt0_pop_close_step (c c' : Config) : Prop :=
    exists l0 t0 f rest,
      out_edges (fst c) = (l0, t0) :: tl (out_edges (fst c))
      /\ In (l0, t0) (out_edges (fst c))
      /\ snd c = f :: rest
      /\ c' = (t0, rest).

  (* ConsumeAtAndPop-shaped close (the fix): pop, advance along the
     MATCHED close edge. *)
  Definition consume_at_pop_close_step (c c' : Config) : Prop :=
    exists t f rest,
      In (l_close, t) (out_edges (fst c))
      /\ snd c = f :: rest
      /\ c' = (t, rest).

  (* ── A1 — the Replace-shaped close can NEVER discharge the frame:
        the stack is invariant, so a configuration with the collection
        frame on top never reaches an empty stack via close steps. ── *)
  Theorem replace_close_cannot_finalize :
    forall c c', replace_close_step c c' -> snd c' = snd c.
  Proof.
    intros c c' [t [_ Heq]]. subst c'. reflexivity.
  Qed.

  Corollary replace_close_never_accepts :
    forall c c', replace_close_step c c' ->
      snd c <> [] -> snd c' <> [].
  Proof.
    intros c c' Hstep Hne.
    rewrite (replace_close_cannot_finalize c c' Hstep).
    exact Hne.
  Qed.

  (* ── A2 — the alt-0 pop lands on a NON-close target whenever the
        close edge is not alt-0 (the `}`-vs-`}#` rhocalc-Bag lattice
        class): with out_edges 0 = [(9, 1); (l_close, 2)] (alt-0 is a
        different token), the alt-0 pop reaches node 1, which is NOT a
        close-edge target. The fabricated-position / wrong-edge class. ── *)
  Theorem alt0_close_lands_on_wrong_target :
    l_close <> 9 ->
    out_edges 0 = [(9, 1); (l_close, 2)] ->
    forall (f : nat) (c' : Config),
      alt0_pop_close_step (0, [f]) c' ->
      fst c' = 1 /\ ~ In (l_close, fst c') (out_edges 0).
  Proof.
    intros Hne Hedges f c'
      [l0 [t0 [f' [rest [Hhead [_ [Hstack Heq]]]]]]].
    simpl in Hhead. rewrite Hedges in Hhead. simpl in Hhead.
    inversion Hhead; subst.
    simpl in Hstack. inversion Hstack; subst.
    simpl. split; [reflexivity |].
    rewrite Hedges. intro Hin.
    destruct Hin as [Hin | [Hin | []]].
    - inversion Hin. apply Hne. symmetry. assumption.
    - inversion Hin.
  Qed.

  (* ── A3 — the new ConsumeAtAndPop action is sound AND complete for
        the close relation: it pops exactly one frame and lands exactly
        on a matched close target (`gated_close_pops_and_finalizes`). ── *)
  Theorem consume_at_and_pop_sound :
    forall c c', consume_at_pop_close_step c c' ->
      In (l_close, fst c') (out_edges (fst c))
      /\ (exists f, snd c = f :: snd c').
  Proof.
    intros c c' [t [f [rest [Hin [Hstack Heq]]]]]. subst c'. simpl.
    split.
    - exact Hin.
    - exists f. rewrite Hstack. reflexivity.
  Qed.

  Theorem consume_at_and_pop_complete :
    forall n t f rest,
      In (l_close, t) (out_edges n) ->
      consume_at_pop_close_step (n, f :: rest) (t, rest).
  Proof.
    intros n t f rest Hin.
    exists t, f, rest. split; [exact Hin | split; reflexivity].
  Qed.

  (* ── A4 — advance-or-die transcription: the branch BUILDER. With the
        sep targets analogous to close_targets, the gated builder emits
        the licensed branches; an EMPTY result must transcribe to
        WpdaStepAction::Error (never an empty Fork — the runtime's
        empty-ForkInto silently deletes the cursor). The theorem: the
        builder is empty iff no close-edge and no sep-edge exists (and
        bare is unlicensed) — exactly `no_branch_no_word`'s hypothesis
        set, so the Error is a DEFINITE refutation. ── *)

  Variable l_sep : nat.

  Definition sep_targets (n : nat) : list nat :=
    map snd (filter (fun e => Nat.eqb (fst e) l_sep) (out_edges n)).

  Lemma sep_targets_in :
    forall n t, In t (sep_targets n) <-> In (l_sep, t) (out_edges n).
  Proof.
    intros n t. unfold sep_targets. rewrite in_map_iff. split.
    - intros [[l' t'] [Hsnd Hin]]. simpl in Hsnd. subst t'.
      apply filter_In in Hin. destruct Hin as [Hin Heq].
      simpl in Heq. apply Nat.eqb_eq in Heq. subst l'. exact Hin.
    - intro Hin. exists (l_sep, t). split; [reflexivity |].
      apply filter_In. split; [exact Hin |]. simpl. apply Nat.eqb_refl.
  Qed.

  (* The gated branch builder for an explicit-separator grammar
     (sep_empty = false ⇒ bare unlicensed): close branches ++ sep
     branches. *)
  Definition gated_branches (n : nat) : list nat :=
    close_targets n ++ sep_targets n.

  Theorem advance_or_die_emits_error :
    forall n,
      gated_branches n = [] <->
      ((forall t, ~ In (l_close, t) (out_edges n))
       /\ (forall t, ~ In (l_sep, t) (out_edges n))).
  Proof.
    intro n. unfold gated_branches. split.
    - intro Hnil. apply app_eq_nil in Hnil.
      destruct Hnil as [Hc Hs]. split; intros t Hin.
      + apply close_targets_in in Hin. rewrite Hc in Hin. exact Hin.
      + apply sep_targets_in in Hin. rewrite Hs in Hin. exact Hin.
    - intros [Hc Hs].
      assert (Hcn : close_targets n = []).
      { destruct (close_targets n) as [| t rest] eqn:E;
          [reflexivity |].
        exfalso. apply (Hc t). apply close_targets_in.
        rewrite E. left. reflexivity. }
      assert (Hsn : sep_targets n = []).
      { destruct (sep_targets n) as [| t rest] eqn:E;
          [reflexivity |].
        exfalso. apply (Hs t). apply sep_targets_in.
        rewrite E. left. reflexivity. }
      rewrite Hcn, Hsn. reflexivity.
  Qed.

End ActionSemantics.
