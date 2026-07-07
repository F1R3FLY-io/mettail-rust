(*
 * AtQuotedBindGate: the model for the AT_QUOTED_BIND_GATE — the parse-time (C)
 * evidence gate + realize-time (B) backstop that suppress the PROVEN `@`-quoted
 * bind GRAMMAR OVER-GENERATION.
 *
 * GROUND TRUTH (trace-proven + offline-classifier-proven, `@a <- @b`):
 *   The InputBind (result category) PrefixDispatch on the sigil `@` emits a
 *   Fork whose branches are (i) the direct sigil-triggered BinderRule branches
 *   for the InputBindQuoted family (`"@" pat "<-"/"<="/… n`), AND (ii) a
 *   `PushCrossCatLhs` delegate `category_entry(Name)` that parses `@a` as one
 *   whole Name atom (NQuoteShort) and projects Name -> InputBind via the generic
 *   whole-source rules (`lhs:Name "<-" n`). Branch (ii) is the SOLE source of
 *   the whole-Name readings `InputBind(NQuoteShort a, _)` /
 *   `InputBindPersistent(NQuoteShort a, _)` / `InputBindQuery(NQuoteShort a, _)`.
 *   Measured: `@a<-@b` yields alts = 2 (one InputBindQuoted scalar KEEP, one
 *   whole-Name InputBind DROP); the whole-Name reading has NO canonical-Rholang
 *   counterpart (tree-sitter grammar.js + interpreter + 100% corpus: `@a` in a
 *   bind LHS is UNAMBIGUOUSLY a quoted pattern = the scalar InputBindQuoted).
 *   Under a `.*sep` repetition (`@a<-@b & …`) the 2-way per-segment fork
 *   compounds multiplicatively (measured branch_cursors_peak_pre_merge
 *   674@k0 -> 146011@k1), while the no-sigil control `x<-c & …` stays flat
 *   (74@k0 -> 103 constant).
 *
 * THE FIX (grammar-derived, one-sided monotone refutation of a proven
 * over-generation — the same soundness class as min_terminal_span and
 * FORROW_PROJ_GATE, per feedback_use_wpds_disambiguation_not_heuristics):
 *   (C) at the sigil PrefixDispatch, SUPPRESS the CrossCatLhs delegate branch
 *       iff (a) the dispatch sigil `σ` ALSO directly leads a sibling rule in the
 *       result category [compile-time: `sigil_leads_result_rule`] AND (b) the
 *       FIRST depth-0 whole-source trigger ahead is a BIND trigger shared by a
 *       sigil-led sibling [runtime: `prefix_at_quoted_bind_gate_evidence`, which
 *       returns false — KEEP — when a polyadic separator `,` is reached first,
 *       since no sigil-quoted polyadic sibling exists]. The direct
 *       sigil-triggered rules are untouched, so alts collapses 2 -> 1 to the
 *       scalar reading, and the gated fork emits ONE delegate not two -> the
 *       `&`-segment multiplier collapses to the linear no-sigil control.
 *   (B) at realize time, DROP a generic whole-source packing whose children[0]
 *       is a `σ`-quoted source atom — defense-in-depth, INERT under (C).
 *
 * THE MODEL: classify a dispatch of a token `t` in the result category:
 *   - SigilBind   : t = σ, σ leads a result-cat sibling, first depth-0 trigger
 *                   ahead is a bind trigger with a sigil sibling (the OVER-GEN
 *                   scenario — `@a<-@b`).
 *   - SigilPoly   : t = σ, σ leads a result-cat sibling, but the first depth-0
 *                   trigger ahead is a POLYADIC separator with NO sigil sibling
 *                   (`@a,b<-c` — the whole-source reading is legitimate).
 *   - PlainBind   : t is NOT a rule-leading sigil (e.g. an Ident-led LHS,
 *                   `x<-c`); the CrossCatLhs delegate is the only source->result
 *                   path.
 * Interpretations of the LHS at such a dispatch: IQuoted (the direct
 * sigil-triggered scalar rule, e.g. InputBindQuoted), IWhole (the whole-source
 * CrossCatLhs delegate reading, e.g. InputBind over NQuoteShort). Only SigilBind
 * admits BOTH (the over-generation); the gate removes IWhole there.
 *
 * THEOREMS (all admission-free; audited by Print Assumptions, must all print
 * "Closed under the global context"):
 *   T1 overgen_is_non_canonical  — IWhole in SigilBind is the over-generation
 *      (has a co-located IQuoted scalar sibling that is the canonical reading).
 *   T2 gate_no_legit_parse_lost  — the gate is a STRICT REFINEMENT: it removes
 *      ONLY IWhole in SigilBind; every SigilPoly / PlainBind reading and the
 *      IQuoted reading of SigilBind are preserved.
 *   T3 gate_single_valued        — after the gate, SigilBind admits EXACTLY the
 *      single IQuoted (scalar) reading.
 *   T4 gate_linear_frontier      — the gated sigil-bind fork emits ONE delegate
 *      (branch count 1), so a k-segment `.*sep` chain has multiplier 1 (LINEAR),
 *      vs the ungated multiplier 2^k (the measured explosion).
 *   T5 gate_kill_switch_identity — with the kill-switch off the gated branch set
 *      equals the ungated (baseline) set in EVERY context (byte-identical).
 *   T6 realize_inert_under_parse_gate — under (C) no whole-source packing forms
 *      in a SigilBind context, so the (B) realize drop fires 0 times there.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Section AtQuotedBindGate.

  (* ── Dispatch-context classification of a token dispatch in the result
        category (transcribed premises). ── *)
  Inductive DispatchCtx : Type :=
    | SigilBind    (* t = σ leads a result-cat sibling; first depth-0 trigger
                      ahead is a bind trigger with a sigil sibling (over-gen) *)
    | SigilPoly    (* t = σ leads a result-cat sibling; first depth-0 trigger
                      ahead is a polyadic separator with NO sigil sibling *)
    | PlainBind.   (* t is not a rule-leading sigil (Ident-led LHS, x<-c) *)

  (* ── Interpretations of the bind LHS at a dispatch. ── *)
  Inductive Interp : Type :=
    | IQuoted     (* the direct sigil-triggered scalar rule (InputBindQuoted) *)
    | IWhole.     (* the whole-source CrossCatLhs delegate reading (InputBind
                     over a σ-quoted Name — the over-generation in SigilBind) *)

  Definition interp_eqb (a b : Interp) : bool :=
    match a, b with
    | IQuoted, IQuoted | IWhole, IWhole => true
    | _, _ => false
    end.

  (* Decidable equality on Interp (a 2-element enumeration). Used by the
     membership decisions below. *)
  Definition interp_eq_dec (a b : Interp) : {a = b} + {a <> b}.
  Proof. decide equality. Defined.

  (* ── The canonical-reading fact (imported from the grammar audit: tree-sitter
        grammar.js + interpreter + 100% corpus): in a SigilBind context the
        direct sigil-triggered scalar reading IQuoted is the canonical one and
        the whole-source IWhole reading has no canonical counterpart. In a
        SigilPoly context there is NO sigil-quoted sibling (no `@`-quoted
        polyadic rule) so the whole-source IWhole reading IS the only /
        legitimate reading. PlainBind has no sigil at all — IWhole is the only
        source->result path (there is no IQuoted rule for a non-sigil LHS). ── *)
  Definition is_over_generation (i : Interp) (k : DispatchCtx) : bool :=
    match i, k with
    | IWhole, SigilBind => true
    | _, _ => false
    end.

  (* Whether a co-located IQuoted scalar sibling exists at this context (a direct
     sigil-triggered rule). True exactly in the sigil contexts. *)
  Definition has_quoted_sibling (k : DispatchCtx) : bool :=
    match k with
    | SigilBind | SigilPoly => true
    | PlainBind => false
    end.

  (* ── Branch sets per context. ── *)

  (* UNGATED (baseline): SigilBind forks BOTH the direct quoted rule and the
     whole-source delegate (the over-generation = the measured alts=2).
     SigilPoly forks ONLY the whole-source delegate (no `@`-quoted polyadic
     sibling — the direct rule does not apply). PlainBind forks ONLY the
     whole-source delegate (no sigil rule). *)
  Definition branches_ungated (k : DispatchCtx) : list Interp :=
    match k with
    | SigilBind => [IQuoted; IWhole]
    | SigilPoly => [IWhole]
    | PlainBind => [IWhole]
    end.

  (* GATED (C, kill-switch on): the whole-source delegate is SUPPRESSED in
     SigilBind ONLY — leaving the single IQuoted scalar reading. SigilPoly and
     PlainBind are untouched (their runtime evidence predicate returns false:
     the first depth-0 trigger is a polyadic stop / there is no sigil rule). *)
  Definition branches_gated (k : DispatchCtx) : list Interp :=
    match k with
    | SigilBind => [IQuoted]
    | SigilPoly => [IWhole]
    | PlainBind => [IWhole]
    end.

  (* ═════════════════════ T1: the over-generation ═════════════════════ *)
  (* In SigilBind the whole-source reading IWhole is the over-generation AND a
     co-located IQuoted scalar sibling (the canonical reading) exists. *)
  Theorem overgen_is_non_canonical :
    is_over_generation IWhole SigilBind = true
    /\ has_quoted_sibling SigilBind = true
    /\ In IQuoted (branches_ungated SigilBind).
  Proof.
    split; [reflexivity | split; [reflexivity |]].
    simpl. left. reflexivity.
  Qed.

  (* The over-generation predicate is CONFINED to IWhole-in-SigilBind: no other
     (interp, context) pair is an over-generation. In particular every SigilPoly
     / PlainBind IWhole reading is legitimate (not an over-generation). *)
  Theorem overgen_confined :
    forall i k, is_over_generation i k = true -> i = IWhole /\ k = SigilBind.
  Proof.
    intros i k H. destruct i, k; simpl in H; try discriminate; split; reflexivity.
  Qed.

  (* ═════════════════ T2: no legitimate parse lost ═════════════════ *)
  (* The gate is a STRICT REFINEMENT of the baseline: every gated reading was a
     baseline reading (monotone subset — nothing invented). *)
  Theorem gate_subset_ungated :
    forall k i, In i (branches_gated k) -> In i (branches_ungated k).
  Proof.
    intros k i H. destruct k; simpl in *.
    - (* SigilBind: [IQuoted] ⊆ [IQuoted; IWhole] *)
      destruct H as [<- | H]; [left; reflexivity | contradiction].
    - destruct H as [<- | H]; [left; reflexivity | contradiction].
    - destruct H as [<- | H]; [left; reflexivity | contradiction].
  Qed.

  (* The ONLY reading the gate removes is IWhole in SigilBind — i.e. exactly the
     over-generation, nothing else. Every legitimate reading is preserved:
     SigilPoly / PlainBind readings, and the IQuoted reading of SigilBind. *)
  Theorem gate_removes_only_overgen :
    forall k i,
      In i (branches_ungated k) -> ~ In i (branches_gated k) ->
      is_over_generation i k = true.
  Proof.
    intros k i H Hn. destruct k; simpl in *.
    - (* SigilBind: baseline [IQuoted; IWhole], gated [IQuoted]. *)
      destruct H as [<- | [<- | H]]; try contradiction.
      + exfalso; apply Hn; left; reflexivity.
      + reflexivity.
    - destruct H as [<- | H]; try contradiction.
      exfalso; apply Hn; left; reflexivity.
    - destruct H as [<- | H]; try contradiction.
      exfalso; apply Hn; left; reflexivity.
  Qed.

  (* Corollary — every LEGITIMATE (non-over-generation) baseline reading
     survives the gate. This is the no-loss statement in positive form. *)
  Theorem gate_no_legit_parse_lost :
    forall k i,
      In i (branches_ungated k) -> is_over_generation i k = false ->
      In i (branches_gated k).
  Proof.
    intros k i Hin Hlegit.
    destruct (in_dec interp_eq_dec i (branches_gated k)) as [Hyes | Hno].
    - exact Hyes.
    - exfalso.
      pose proof (gate_removes_only_overgen k i Hin Hno) as Hover.
      rewrite Hover in Hlegit. discriminate.
  Qed.

  (* ═════════════════ T3: single-valued + scalar ═════════════════ *)
  (* After the gate, SigilBind admits EXACTLY the single IQuoted scalar reading
     (`@a<-@b` -> alts = Ok(1) = InputBindQuoted). *)
  Theorem gate_single_valued :
    branches_gated SigilBind = [IQuoted].
  Proof. reflexivity. Qed.

  (* The surviving reading is the QUOTED scalar one, never the whole-source one. *)
  Theorem gate_survivor_is_quoted :
    forall i, In i (branches_gated SigilBind) -> i = IQuoted.
  Proof.
    intros i H. simpl in H. destruct H as [<- | H]; [reflexivity | contradiction].
  Qed.

  (* ═════════════════ T4: linear frontier ═════════════════ *)
  (* Branch count per context. *)
  Definition bcount_ungated (k : DispatchCtx) : nat := length (branches_ungated k).
  Definition bcount_gated (k : DispatchCtx) : nat := length (branches_gated k).

  (* The gated sigil-bind fork emits ONE delegate (the direct quoted rule); the
     ungated fork emits TWO. *)
  Theorem gated_sigilbind_singleton : bcount_gated SigilBind = 1.
  Proof. reflexivity. Qed.

  Theorem ungated_sigilbind_binary : bcount_ungated SigilBind = 2.
  Proof. reflexivity. Qed.

  (* Cursor-path multiplier of a `.*sep` chain: the product over segments of the
     number of branches emitted at each segment's dispatch context (mirrors the
     CastLexForkCrossCatLhsGap path_multiplier). *)
  Fixpoint path_multiplier (segs : list DispatchCtx) (b : DispatchCtx -> nat) : nat :=
    match segs with
    | [] => 1
    | k :: rest => b k * path_multiplier rest b
    end.

  (* A homogeneous k-segment `@a<-@b & … & @a<-@b` chain: every segment is a
     SigilBind dispatch. *)
  Definition sigilbind_chain (k : nat) : list DispatchCtx := repeat SigilBind k.

  Lemma path_multiplier_repeat :
    forall (b : DispatchCtx -> nat) k n,
      path_multiplier (repeat k n) b = (b k) ^ n.
  Proof.
    intros b k n. induction n as [| n IH]; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  (* GATED: the multiplier is 1^k = 1 — LINEAR (the frontier tracks the no-sigil
     `x<-c` control, whose per-segment branch count is likewise 1). *)
  Theorem gate_linear_frontier :
    forall k, path_multiplier (sigilbind_chain k) bcount_gated = 1.
  Proof.
    intro k. unfold sigilbind_chain.
    rewrite path_multiplier_repeat, gated_sigilbind_singleton.
    apply Nat.pow_1_l.
  Qed.

  (* UNGATED: the multiplier is 2^k — the measured multiplicative explosion
     (674@k0 -> 146011@k1 -> …). Derived from the SAME counting function, not
     asserted. *)
  Theorem ungated_frontier_exponential :
    forall k, path_multiplier (sigilbind_chain k) bcount_ungated = 2 ^ k.
  Proof.
    intro k. unfold sigilbind_chain.
    rewrite path_multiplier_repeat, ungated_sigilbind_binary. reflexivity.
  Qed.

  (* The contrast: for any chain of length >= 1 the gated frontier is STRICTLY
     below the ungated one — the gate eliminates the fork explosion. *)
  Theorem gate_strictly_below_ungated :
    forall k, 1 <= k ->
      path_multiplier (sigilbind_chain k) bcount_gated
        < path_multiplier (sigilbind_chain k) bcount_ungated.
  Proof.
    intros k Hk. rewrite gate_linear_frontier, ungated_frontier_exponential.
    destruct k as [| k]; [lia |].
    simpl. pose proof (Nat.pow_nonzero 2 k ltac:(lia)). lia.
  Qed.

  (* ═════════════════ T5: kill-switch identity ═════════════════ *)
  Section KillSwitch.

    (* The kill-switch (`AT_QUOTED_BIND_GATE`, a compile-time bool). When off,
       the emitted branch set is the UNGATED baseline in EVERY context; when on,
       it is the gated set. This models the codegen conditional that omits the
       suppression conjunct entirely when the const is false (byte-identical). *)
    Variable gate_on : bool.

    Definition branches_switched (k : DispatchCtx) : list Interp :=
      if gate_on then branches_gated k else branches_ungated k.

    (* OFF ⇒ byte-identical to baseline in every context. *)
    Theorem gate_kill_switch_identity :
      gate_on = false ->
      forall k, branches_switched k = branches_ungated k.
    Proof.
      intros Hoff k. unfold branches_switched. rewrite Hoff. reflexivity.
    Qed.

    (* ON ⇒ exactly the gated set. *)
    Theorem gate_on_is_gated :
      gate_on = true ->
      forall k, branches_switched k = branches_gated k.
    Proof.
      intros Hon k. unfold branches_switched. rewrite Hon. reflexivity.
    Qed.

  End KillSwitch.

  (* ═════════════════ T6: realize backstop inert under (C) ═════════════════ *)
  Section RealizeBackstop.

    (* Whether a whole-source packing (the (B) drop-set: InputBind /
       InputBindPersistent / InputBindQuery over a σ-quoted Name) is PRESENT in
       the realized forest at a given dispatch context. Under the parse-time (C)
       gate, the whole-source delegate is never pushed in a SigilBind context, so
       no such packing forms there. We model this by deriving presence from the
       gated branch set: a whole-source packing exists iff IWhole is a gated
       branch. *)
    Definition whole_source_packing_present (k : DispatchCtx) : bool :=
      if in_dec interp_eq_dec IWhole (branches_gated k)
      then true else false.

    (* The (B) realize drop fires at context k iff a whole-source packing is
       present AND it is an over-generation there. *)
    Definition realize_drop_fires (k : DispatchCtx) : bool :=
      whole_source_packing_present k && is_over_generation IWhole k.

    (* T6: under (C), the realize backstop fires 0 times in a SigilBind context
       (the only context where IWhole would be an over-generation) — because (C)
       already removed the whole-source delegate, so no packing is present. The
       (B) net is therefore INERT under (C). *)
    Theorem realize_inert_under_parse_gate :
      realize_drop_fires SigilBind = false.
    Proof. reflexivity. Qed.

    (* And in the legitimate contexts the realize backstop NEVER fires either
       (the whole-source reading is not an over-generation there), so (B) drops
       no legitimate packing anywhere. *)
    Theorem realize_never_drops_legit :
      realize_drop_fires SigilPoly = false /\ realize_drop_fires PlainBind = false.
    Proof. split; reflexivity. Qed.

  End RealizeBackstop.

End AtQuotedBindGate.

(* ═════════════════ Assumption audit — must all print
   "Closed under the global context" ═════════════════ *)
Print Assumptions overgen_is_non_canonical.
Print Assumptions overgen_confined.
Print Assumptions gate_subset_ungated.
Print Assumptions gate_removes_only_overgen.
Print Assumptions gate_no_legit_parse_lost.
Print Assumptions gate_single_valued.
Print Assumptions gate_survivor_is_quoted.
Print Assumptions gate_linear_frontier.
Print Assumptions ungated_frontier_exponential.
Print Assumptions gate_strictly_below_ungated.
Print Assumptions gate_kill_switch_identity.
Print Assumptions gate_on_is_gated.
Print Assumptions realize_inert_under_parse_gate.
Print Assumptions realize_never_drops_legit.
