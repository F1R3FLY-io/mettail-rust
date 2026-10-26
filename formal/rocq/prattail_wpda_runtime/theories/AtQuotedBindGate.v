(*
 * AtQuotedBindGate: the model of the AT_QUOTED_BIND_GATE evidence gate at the
 * InputBind `@` prefix dispatch. Part A models the prior implementation.
 * Part B proves its defects. Part C proves the bracket and delegation repair.
 * The final extension proves source isolation and projection-helper selection.
 *
 * REVISION 2026-10-21. Before this date the file held a hand-written
 * classification (DispatchCtx, branches_ungated, branches_gated) that described
 * the intended gate, not the code. That classification is kept below as a
 * commented-out block. Its claims were false for the running code:
 *   - It said that the CrossCatLhs delegate is the SOLE source of the whole-Name
 *     reading. Since c387f4cc the arm also pushes ungated LeadingCategory
 *     branches for rules 0, 4, 5, 7 and 8 from source Name, and each of them
 *     carries the whole-Name reading too (wpda.rs:197485-197582).
 *   - It said that the gate is correctness-complete. The evidence scan cannot
 *     return true for InputBind (category 4): since c387f4cc the bind triggers
 *     `<-` and `<=` are also structural closes (the binder closes of
 *     InputBindPolyadic and InputBindPersistentPolyadic), and the scan tests the
 *     closes before the triggers [at_quoted_gate_dead_c4].
 *   - It said that the realize-time backstop (B) removes what (C) misses. On the
 *     measured `_all` path the whole-Name InputBind survives as reading [1]
 *     (target/verification/resume-20261017/2.4-diag-merge2-cast.log:1662).
 *     Which step lets it through is not determined (inferred: the backstop does
 *     not see that packing on that path).
 *
 * THE CODE MODELLED (MeTTaIL; generated code from the snapshot
 * target/perf/tmp/generated-rholang-snapshot-20261020/wpda.rs):
 *   - [scan], [evidence_scan]: prattail/src/wpda_transitions/prefix_policy.rs:117-158
 *     (`prefix_at_quoted_bind_gate_evidence`). The token list is the tokens after
 *     the dispatch position; only `TokenKind::Fixed` tokens are inspected.
 *   - [evidence] and the tables [rho_opens], [rho_closes], [rho_rows],
 *     [rho_arms]: the generated wrapper, wpda.rs:38204-38240, emitted by
 *     macros/src/gen/runtime/wpda_codegen/kind_dispatch.rs:342-395.
 *   - [structural_delimiters]: prattail/src/wpda_rule_analysis/collection/
 *     assembly.rs:368-421 (`collect_binder_close_delimiters`,
 *     `try_collect_structural_delimiters`), through macros/src/gen/runtime/
 *     wpda_codegen/collection.rs:90-99.
 *   - [c4_at_descs], [alive_current]: the InputBind `@` arm `prefix_arm_c4_a1`,
 *     wpda.rs:197485-197582 (`unified_fork(9)`), with the fallback table
 *     [rho_projection_fallback] from wpda.rs:38287-38300 and the kill switch
 *     `AT_QUOTED_BIND_GATE = true` (macros/.../wpda_codegen/forks.rs:233).
 *   Category indices are the `WPDA_CATEGORIES` slots (wpda.rs:3-65): 0 Proc,
 *   4 InputBind, 6 Name, 9 Bool.
 *
 * MODEL BOUNDARY (stated, not proved). [yields] abstracts the rule tails of the
 * InputBind rules (languages/src/rholang.rs:1068-1146): which reading each pushed
 * branch can complete, given the first depth-0 whole-source trigger [c4_nt] over
 * the true bracket alphabet. Tests T-A3 (rule literals are bracket-balanced) and
 * T-A6 (end-to-end reading counts) bind this abstraction to the code.
 *
 * THE FIX (both edits are needed):
 *   - Edit 1': the evidence depth alphabet is the matched bracket pairs only
 *     [bracket_delimiters], [fixed_tables]. Binder closes are not brackets. A
 *     collection with a synthesized paren contributes "(" and not its keyword.
 *     An arm whose triggers are in the alphabet is dropped; for arm 9 this is
 *     behaviour-neutral [dropping_c9_is_behaviour_neutral].
 *   - Edit 2: a LeadingCategory push whose source is a gated CrossCatLhs source
 *     of the same bucket gets the same evidence conjunct [gated_sources],
 *     [alive_fixed].
 *   Neither edit alone removes the whole-Name reading
 *   [edit1_alone_leaves_whole_name], [edit2_alone_leaves_whole_name]. The first
 *   proposal for edit 1 (remove only the triggers from the closes) loses a
 *   legitimate polyadic parse [s1_edit1_loses_polyadic_parse].
 *
 * THEOREMS. Part B, about the current code: at_quoted_gate_dead_c4,
 * at_quoted_gate_dead_c9, structural_delimiters_reproduce_snapshot,
 * current_g2a_two_readings, gate_single_valued_refuted_on_current,
 * ungated_frontier_exponential, gate_premise_fails_current. Part C, about the
 * corrected code: evidence_fixed_c4_exact, gate_single_valued,
 * gate_no_legit_parse_lost (= gate_no_loss), gate_subset_ungated,
 * gate_removes_only_overgen, gate_survivor_is_quoted, overgen_is_non_canonical,
 * overgen_confined, gate_linear_frontier, gate_strictly_below_ungated,
 * gate_kill_switch_identity, gate_off_ignores_evidence, gate_on_is_gated,
 * realize_inert_under_parse_gate, drop_set_sound, realize_never_drops_legit,
 * fixed_keeps_polyadic, and the controls listed above.
 *
 * Rocq 9.1. No Admitted, no Axiom, no Parameter. Every theorem is audited by
 * Print Assumptions at the end of the file.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import String.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

(* ═══════════════════════════════════════════════════════════════════════════
   DISABLED 2026-10-21: the hand-written classification of the original model
   (its lines 82-389, kept verbatim below).

   Why it is disabled: it classified each dispatch by hand (DispatchCtx) and
   asserted the gated and ungated branch sets. It did not model the evidence
   scan, its tables, or the LeadingCategory pushes, so its theorems held while
   the code kept the over-generation (see the REVISION note in the header).
   Part A below replaces it with a transcription of the code. Interp,
   interp_eqb and interp_eq_dec are kept unchanged in Part A. The theorem names
   T1-T6 are restated over the faithful definitions in Part C.
   ═══════════════════════════════════════════════════════════════════════════
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
*)

(* ═══════════════════════ Part A: the code, transcribed ═══════════════════════ *)

(* ── A.1 Tokens and the evidence scan (prefix_policy.rs:117-158). ──
   TFixed is `TokenKind::Fixed`. Every other token kind is TOther, which the
   scan skips. The list is the tokens after the dispatch position. *)
Inductive Tok : Type := TFixed (s : string) | TOther.

Definition mem (s : string) (l : list string) : bool := existsb (String.eqb s) l.

(* One loop step of the Rust scan, in the same test order: opens, closes
   (a close at depth 0 returns false), rows, bind triggers, polyadic stops. *)
Fixpoint scan (opens closes rows binds stops : list string) (depth : nat) (ts : list Tok)
    : bool :=
  match ts with
  | [] => false
  | TOther :: rest => scan opens closes rows binds stops depth rest
  | TFixed t :: rest =>
      if mem t opens then scan opens closes rows binds stops (S depth) rest
      else if mem t closes then
        match depth with
        | O => false
        | S d => scan opens closes rows binds stops d rest
        end
      else if Nat.eqb depth 0 && mem t rows then false
      else if Nat.eqb depth 0 && mem t binds then true
      else if Nat.eqb depth 0 && mem t stops then false
      else scan opens closes rows binds stops depth rest
  end.

(* `if bind_triggers.is_empty() { return false; }`, then the loop from depth 0. *)
Definition evidence_scan (opens closes rows binds stops : list string) (ts : list Tok) : bool :=
  match binds with
  | [] => false
  | _ :: _ => scan opens closes rows binds stops 0 ts
  end.

(* ── A.2 The generated wrapper (wpda.rs:38204-38240). ── *)
Definition GateArm : Type := (nat * (list string * list string))%type.

Fixpoint arm_lookup (arms : list GateArm) (c : nat) : list string * list string :=
  match arms with
  | [] => ([], [])
  | (c', bs) :: rest => if Nat.eqb c c' then bs else arm_lookup rest c
  end.

Record ScanTables := {
  t_opens : list string;
  t_closes : list string;
  t_rows : list string;
  t_arms : list GateArm
}.

Definition evidence (tb : ScanTables) (c : nat) (ts : list Tok) : bool :=
  let '(binds, stops) := arm_lookup (t_arms tb) c in
  evidence_scan (t_opens tb) (t_closes tb) (t_rows tb) binds stops ts.

Definition rho_opens : list string := ["#{"; "("; "Set"; "["; "if"; "{"; "{|"].
Definition rho_closes : list string :=
  [")"; ":"; ";"; "<-"; "<="; "]"; "in"; "then"; "where"; "|-"; "|}"; "}"; "}#"].
Definition rho_rows : list string := [""; ";"; "|"].
Definition rho_arms : list GateArm :=
  [(0, (["!"; "!!"], ["::"])); (4, (["<-"; "<="], [","])); (9, (["("], []))].
Definition rho_tables_current : ScanTables :=
  {| t_opens := rho_opens; t_closes := rho_closes; t_rows := rho_rows; t_arms := rho_arms |}.

(* ── A.3 The delimiter derivation (assembly.rs:368-421). ──
   A collection rule adds its open token, a "(" when it has a synthesized
   paren, and its close. A binder rule adds the closes of its binder list
   loops and collection parameters ([binder_closes]). *)
Record CollShape := { cs_open : string; cs_close : string; cs_synth : bool }.

Definition structural_delimiters (shapes : list CollShape) (binder_closes : list string)
    : list string * list string :=
  ("(" :: flat_map (fun s => cs_open s :: (if cs_synth s then ["("] else [])) shapes,
   ")" :: map cs_close shapes ++ binder_closes).

(* The Rholang observations. Test T-A1 binds them to the macro output. *)
Definition rho_shapes : list CollShape :=
  [ {| cs_open := "[";   cs_close := "]";    cs_synth := false |};
    {| cs_open := "#{";  cs_close := "}#";   cs_synth := false |};
    {| cs_open := "{";   cs_close := "}";    cs_synth := false |};
    {| cs_open := "Set"; cs_close := ")";    cs_synth := true  |};
    {| cs_open := "{|";  cs_close := "|}";   cs_synth := false |};
    {| cs_open := "if";  cs_close := "then"; cs_synth := false |} ].
Definition rho_binder_closes : list string := [":"; ";"; "<-"; "<="; "in"; "where"; "|-"].

Definition set_eqb (a b : list string) : bool :=
  forallb (fun x => mem x b) a && forallb (fun x => mem x a) b.

(* ── A.4 The InputBind `@` arm (wpda.rs:197485-197582). ──
   DCross src sigil: push_crosscat_lhs(4 <- src); sigil = sigil_leads_result_rule.
   DLead rule src: push_leading_category_with_floor(4, rule, src).
   DSpine w: prefix_spine_trigger(.., w), the shared `"@" pat` spine of rules 2, 3, 6.
   DGroupRest rule: a descriptor of the spine group that pushes nothing. The
   positions of the two DGroupRest entries are inferred from the rule order. *)
Inductive Desc : Type :=
  | DCross (src : nat) (sigil : bool)
  | DLead (rule src : nat)
  | DSpine (weight_rule : nat)
  | DGroupRest (rule : nat).

Definition c4_at_descs : list Desc :=
  [DCross 6 true; DLead 0 6; DSpine 2; DGroupRest 3; DLead 4 6; DLead 5 6;
   DGroupRest 6; DLead 7 6; DLead 8 6].

(* `crosscat_lhs_has_projection_fallback`, wpda.rs:38287-38300: the
   (source, result) pairs, verbatim and in order. *)
Definition rho_projection_fallback : list (nat * nat) :=
  [(49, 0); (50, 0); (51, 0); (7, 0); (48, 0); (47, 0); (58, 0); (59, 0); (52, 0);
   (53, 0); (54, 0); (55, 0); (56, 0); (57, 0); (60, 0); (61, 0); (6, 1); (3, 2);
   (4, 5); (58, 7); (47, 7); (10, 9); (0, 14); (28, 29); (31, 34); (58, 43); (7, 43);
   (48, 43); (49, 43); (50, 43); (52, 43); (51, 43); (43, 44); (58, 47); (58, 48);
   (7, 48); (47, 48); (58, 49); (7, 49); (47, 49); (51, 49); (48, 49); (50, 49)].

Definition has_fallback (result source : nat) : bool :=
  existsb (fun p => Nat.eqb (fst p) source && Nat.eqb (snd p) result) rho_projection_fallback.

(* The push guards of the arm. ta = prefix_crosscat_lhs_trigger_ahead_scoped,
   ev = prefix_at_quoted_bind_gate_evidence, feasible =
   prefix_crosscat_one_token_feasible. gate_on is AT_QUOTED_BIND_GATE; when it
   is false the evidence conjunct folds away. *)
Definition alive_current (gate_on : bool) (cat : nat) (ta ev feasible : bool) (d : Desc) : bool :=
  match d with
  | DCross src sigil =>
      (ta || negb (has_fallback cat src)) && (if gate_on && sigil then negb ev else true)
      && feasible
  | DLead _ _ | DSpine _ => true
  | DGroupRest _ => false
  end.

(* ── A.5 Readings (the model boundary, see the header). ── *)

(* Kept unchanged from the original model. *)
Inductive Interp : Type :=
  | IQuoted     (* the direct sigil-triggered scalar rule (InputBindQuoted) *)
  | IWhole.     (* the whole-Name reading (InputBind over a quoted Name) *)

Definition interp_eqb (a b : Interp) : bool :=
  match a, b with
  | IQuoted, IQuoted | IWhole, IWhole => true
  | _, _ => false
  end.

Definition interp_eq_dec (a b : Interp) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(* The first depth-0 trigger, with the same test order as [scan]. *)
Fixpoint first_trigger (opens closes rows trig : list string) (depth : nat) (ts : list Tok)
    : option string :=
  match ts with
  | [] => None
  | TOther :: rest => first_trigger opens closes rows trig depth rest
  | TFixed t :: rest =>
      if mem t opens then first_trigger opens closes rows trig (S depth) rest
      else if mem t closes then
        match depth with
        | O => None
        | S d => first_trigger opens closes rows trig d rest
        end
      else if Nat.eqb depth 0 && mem t rows then None
      else if Nat.eqb depth 0 && mem t trig then Some t
      else first_trigger opens closes rows trig depth rest
  end.

(* The Rholang bracket pairs, plus the DDL `if`/`then` pair. *)
Definition true_opens : list string := ["("; "["; "#{"; "{"; "{|"; "if"].
Definition true_closes : list string := [")"; "]"; "}#"; "}"; "|}"; "then"].
Definition c4_binds : list string := ["<-"; "<="].
Definition c4_stops : list string := [","].
Definition c4_nt (ts : list Tok) : option string :=
  first_trigger true_opens true_closes rho_rows (c4_binds ++ c4_stops) 0 ts.

(* Which reading a pushed branch completes, given the first trigger.
   Rules 2, 3, 6: "@" pat ("<-" | "<=") n.      Rule 7: lhs "<-" n.
   Rule 0: lhs "<-" n "!?(" .. ")" (query).     Rule 8: lhs "<=" n.
   Rules 4, 5: lhs "," .. ("<-" | "<=") n.       The CrossCatLhs delegate takes
   any whole-source trigger. *)
Definition yields (query : bool) (d : Desc) (nt : option string) : option Interp :=
  match nt with
  | None => None
  | Some t =>
      match d with
      | DSpine _ => if mem t c4_binds then Some IQuoted else None
      | DCross _ _ => if mem t (c4_binds ++ c4_stops) then Some IWhole else None
      | DLead r _ =>
          if (Nat.eqb r 7 && String.eqb t "<-" && negb query)
             || (Nat.eqb r 0 && String.eqb t "<-" && query)
             || (Nat.eqb r 8 && String.eqb t "<=")
             || ((Nat.eqb r 4 || Nat.eqb r 5) && String.eqb t ",")
          then Some IWhole else None
      | DGroupRest _ => None
      end
  end.

(* The set of readings, as a duplicate-free list in a fixed order. *)
Definition canon (l : list Interp) : list Interp :=
  (if existsb (interp_eqb IQuoted) l then [IQuoted] else [])
  ++ (if existsb (interp_eqb IWhole) l then [IWhole] else []).

Definition readings (alive : Desc -> bool) (ds : list Desc) (q : bool) (nt : option string)
    : list Interp :=
  canon (flat_map (fun d => if alive d then
                              match yields q d nt with Some i => [i] | None => [] end
                            else []) ds).

(* The current code: the kill switch is on (forks.rs:233), the peek is a
   Fixed token, so one_token_feasible takes its `_ => true` arm. *)
Definition readings_current (ta q : bool) (ts : list Tok) : list Interp :=
  readings (alive_current true 4 ta (evidence rho_tables_current 4 ts) true) c4_at_descs q
    (c4_nt ts).

(* The over-generation: the whole-Name reading of a scalar bind. *)
Definition is_over_generation (i : Interp) (nt : option string) : bool :=
  match i, nt with
  | IWhole, Some t => mem t c4_binds
  | _, _ => false
  end.

Definition legit (i : Interp) (nt : option string) : bool := negb (is_over_generation i nt).

(* Tokens after the bind's `@`. Identifiers and literals are TOther. *)
Definition seg_tokens (rest : list Tok) : list Tok :=
  TOther :: TFixed "<-" :: TFixed "@" :: TOther :: rest.

(* `for(@x <- @"c" where x > 0) { .. }`
   (languages/tests/rholang_semantic_predicate_ambiguity.rs:215). *)
Definition ex_g2a : list Tok :=
  seg_tokens [TFixed "where"; TOther; TFixed ">"; TOther; TFixed ")"].

(* `for(@x, @y <- @z) { .. }` *)
Definition ex_poly : list Tok :=
  [TOther; TFixed ","; TFixed "@"; TOther; TFixed "<-"; TFixed "@"; TOther; TFixed ")"].

(* `for(@{for(a <- b ; c <- d ; e <- f){Nil}} , @z <- g){Nil}` *)
Definition ex_loss : list Tok :=
  [TFixed "{"; TFixed "for"; TFixed "("; TOther; TFixed "<-"; TOther; TFixed ";"; TOther;
   TFixed "<-"; TOther; TFixed ";"; TOther; TFixed "<-"; TOther; TFixed ")"; TFixed "{";
   TFixed "Nil"; TFixed "}"; TFixed "}"; TFixed ","; TFixed "@"; TOther; TFixed "<-";
   TOther; TFixed ")"].

(* ── A.6 Supporting lemmas. ── *)

Lemma mem_spec : forall s l, mem s l = true <-> In s l.
Proof.
  intros s l. unfold mem. rewrite existsb_exists. split.
  - intros [x [Hin Heq]]. apply String.eqb_eq in Heq. subst. exact Hin.
  - intros Hin. exists s. split; [exact Hin | apply String.eqb_refl].
Qed.

Lemma mem_app : forall t l1 l2, mem t (l1 ++ l2) = mem t l1 || mem t l2.
Proof. intros t l1 l2. unfold mem. apply existsb_app. Qed.

Lemma forallb_mem : forall f l t, forallb f l = true -> mem t l = true -> f t = true.
Proof.
  intros f l t Hall Hmem. rewrite forallb_forall in Hall. apply Hall. apply mem_spec. exact Hmem.
Qed.

Lemma set_eqb_mem : forall a b, set_eqb a b = true -> forall t, mem t a = mem t b.
Proof.
  intros a b H t. unfold set_eqb in H. apply andb_true_iff in H as [Hab Hba].
  rewrite forallb_forall in Hab, Hba.
  destruct (mem t a) eqn:Ha, (mem t b) eqn:Hb; try reflexivity.
  - apply mem_spec in Ha. specialize (Hab t Ha). cbv beta in Hab.
    rewrite Hb in Hab. discriminate Hab.
  - apply mem_spec in Hb. specialize (Hba t Hb). cbv beta in Hba.
    rewrite Ha in Hba. discriminate Hba.
Qed.

Lemma interp_eqb_true : forall a b, interp_eqb a b = true <-> a = b.
Proof. intros [] []; simpl; split; intro H; congruence. Qed.

Lemma canon_in : forall i l, In i (canon l) <-> In i l.
Proof.
  intros i l. unfold canon. rewrite in_app_iff. split.
  - intros [H | H]; revert H.
    + destruct (existsb (interp_eqb IQuoted) l) eqn:E; [| intros []].
      intros [<- | []]. apply existsb_exists in E as [x [Hx Heq]].
      apply interp_eqb_true in Heq. subst. exact Hx.
    + destruct (existsb (interp_eqb IWhole) l) eqn:E; [| intros []].
      intros [<- | []]. apply existsb_exists in E as [x [Hx Heq]].
      apply interp_eqb_true in Heq. subst. exact Hx.
  - intro H. destruct i.
    + left. assert (E : existsb (interp_eqb IQuoted) l = true)
        by (apply existsb_exists; exists IQuoted; split; [exact H | reflexivity]).
      rewrite E. simpl. left. reflexivity.
    + right. assert (E : existsb (interp_eqb IWhole) l = true)
        by (apply existsb_exists; exists IWhole; split; [exact H | reflexivity]).
      rewrite E. simpl. left. reflexivity.
Qed.

Lemma readings_in : forall alive ds q nt i,
  In i (readings alive ds q nt) <->
  exists d, In d ds /\ alive d = true /\ yields q d nt = Some i.
Proof.
  intros alive ds q nt i. unfold readings. rewrite canon_in, in_flat_map. split.
  - intros [d [Hd Hi]]. exists d. revert Hi.
    destruct (alive d) eqn:Ha; [| intros []].
    destruct (yields q d nt) as [j |] eqn:Hy; [| intros []].
    intros [<- | []].
    split; [exact Hd | split; reflexivity].
  - intros [d [Hd [Ha Hy]]]. exists d. split; [exact Hd |].
    rewrite Ha, Hy. simpl. left. reflexivity.
Qed.

Lemma readings_ext : forall a1 a2 ds q nt,
  (forall d, a1 d = a2 d) -> readings a1 ds q nt = readings a2 ds q nt.
Proof.
  intros a1 a2 ds q nt H. unfold readings. f_equal. apply flat_map_ext.
  intro d. rewrite H. reflexivity.
Qed.

Lemma readings_mono : forall a1 a2 ds q nt,
  (forall d, a1 d = true -> a2 d = true) ->
  forall i, In i (readings a1 ds q nt) -> In i (readings a2 ds q nt).
Proof.
  intros a1 a2 ds q nt H i Hin. apply readings_in in Hin as [d [Hd [Ha Hy]]].
  apply readings_in. exists d. split; [exact Hd | split; [apply H; exact Ha | exact Hy]].
Qed.

Lemma readings_none : forall alive ds q, readings alive ds q None = [].
Proof.
  intros alive ds q. unfold readings.
  assert (H : flat_map (fun d => if alive d then
                                   match yields q d None with Some i => [i] | None => [] end
                                 else []) ds = []).
  { induction ds as [| d ds IH]; [reflexivity |].
    cbn [flat_map]. rewrite IH. destruct (alive d); reflexivity. }
  rewrite H. reflexivity.
Qed.

(* A scan whose bind triggers are all opens or closes never returns true. *)
Lemma scan_dead : forall o c r b s,
  forallb (fun t => mem t o || mem t c) b = true ->
  forall d ts, scan o c r b s d ts = false.
Proof.
  intros o c r b s Hb d ts. revert d.
  induction ts as [| [t |] rest IH]; intro d; simpl.
  - reflexivity.
  - destruct (mem t o) eqn:Ho; simpl; [apply IH |].
    destruct (mem t c) eqn:Hc; simpl.
    + destruct d; simpl; [reflexivity | apply IH].
    + destruct (Nat.eqb d 0 && mem t r); simpl; [reflexivity |].
      destruct (Nat.eqb d 0 && mem t b) eqn:Hbind; simpl.
      * exfalso. apply andb_true_iff in Hbind as [_ Hmem].
        pose proof (forallb_mem _ _ _ Hb Hmem) as Hx. cbv beta in Hx.
        rewrite Ho, Hc in Hx. simpl in Hx. discriminate Hx.
      * destruct (Nat.eqb d 0 && mem t s); simpl; [reflexivity | apply IH].
  - apply IH.
Qed.

Lemma evidence_dead : forall tb c ts,
  forallb (fun t => mem t (t_opens tb) || mem t (t_closes tb)) (fst (arm_lookup (t_arms tb) c))
    = true ->
  evidence tb c ts = false.
Proof.
  intros tb c ts. unfold evidence.
  destruct (arm_lookup (t_arms tb) c) as [b s]. simpl. intro H.
  unfold evidence_scan. destruct b as [| x b']; [reflexivity |].
  apply scan_dead. exact H.
Qed.

(* The scan answers whether the first depth-0 trigger is a bind trigger. *)
Lemma scan_is_first_trigger : forall o c r b s d ts,
  scan o c r b s d ts =
  match first_trigger o c r (b ++ s) d ts with Some t => mem t b | None => false end.
Proof.
  intros o c r b s d ts. revert d.
  induction ts as [| [t |] rest IH]; intro d; simpl.
  - reflexivity.
  - destruct (mem t o); simpl; [apply IH |].
    destruct (mem t c); simpl.
    + destruct d; simpl; [reflexivity | apply IH].
    + destruct (Nat.eqb d 0); simpl.
      * destruct (mem t r); simpl; [reflexivity |].
        rewrite mem_app. destruct (mem t b) eqn:Hb; simpl.
        -- rewrite Hb. reflexivity.
        -- destruct (mem t s); simpl; [rewrite Hb; reflexivity | apply IH].
      * apply IH.
  - apply IH.
Qed.

Lemma first_trigger_ext : forall o o' c c' r r' g g' d ts,
  (forall t, mem t o = mem t o') -> (forall t, mem t c = mem t c') ->
  (forall t, mem t r = mem t r') -> (forall t, mem t g = mem t g') ->
  first_trigger o c r g d ts = first_trigger o' c' r' g' d ts.
Proof.
  intros o o' c c' r r' g g' d ts Ho Hc Hr Hg. revert d.
  induction ts as [| [t |] rest IH]; intro d; simpl.
  - reflexivity.
  - rewrite Ho, Hc, Hr, Hg.
    destruct (mem t o'); simpl; [apply IH |].
    destruct (mem t c'); simpl; [destruct d; simpl; [reflexivity | apply IH] |].
    destruct (Nat.eqb d 0 && mem t r'); simpl; [reflexivity |].
    destruct (Nat.eqb d 0 && mem t g'); simpl; [reflexivity | apply IH].
  - apply IH.
Qed.

Lemma mem_c4_binds : forall t, mem t c4_binds = true -> t = "<-" \/ t = "<=".
Proof.
  intros t H. apply mem_spec in H. simpl in H.
  destruct H as [H | [H | []]]; [left | right]; symmetry; exact H.
Qed.

Lemma filter_all_true : forall (A : Type) (f : A -> bool) l,
  (forall x, In x l -> f x = true) -> filter f l = l.
Proof.
  intros A f l H. induction l as [| x l IH]; [reflexivity |].
  simpl. rewrite (H x (or_introl eq_refl)). rewrite IH; [reflexivity |].
  intros y Hy. apply H. right. exact Hy.
Qed.

(* ═══════════════ Part B: the defect of the current code ═══════════════ *)

Theorem at_quoted_gate_dead_c4 : forall ts, evidence rho_tables_current 4 ts = false.
Proof. intro ts. apply evidence_dead. vm_compute. reflexivity. Qed.

Theorem at_quoted_gate_dead_c9 : forall ts, evidence rho_tables_current 9 ts = false.
Proof. intro ts. apply evidence_dead. vm_compute. reflexivity. Qed.

(* The derivation of A.3 reproduces the emitted tables of A.2. *)
Theorem structural_delimiters_reproduce_snapshot :
  set_eqb (fst (structural_delimiters rho_shapes rho_binder_closes)) rho_opens = true /\
  set_eqb (snd (structural_delimiters rho_shapes rho_binder_closes)) rho_closes = true.
Proof. split; vm_compute; reflexivity. Qed.

Theorem current_g2a_two_readings : forall ta, readings_current ta false ex_g2a = [IQuoted; IWhole].
Proof. intros [|]; vm_compute; reflexivity. Qed.

Theorem gate_single_valued_refuted_on_current :
  ~ (forall ta q ts t, c4_nt ts = Some t -> mem t c4_binds = true ->
       readings_current ta q ts = [IQuoted]).
Proof.
  intro H.
  assert (Hnt : c4_nt ex_g2a = Some "<-") by (vm_compute; reflexivity).
  assert (Hb : mem "<-" c4_binds = true) by (vm_compute; reflexivity).
  specialize (H false false ex_g2a "<-" Hnt Hb).
  rewrite current_g2a_two_readings in H. discriminate H.
Qed.

(* The cursor-path multiplier of a chain of segments. *)
Fixpoint path_multiplier (segs : list (list Tok)) (b : list Tok -> nat) : nat :=
  match segs with
  | [] => 1
  | s :: rest => b s * path_multiplier rest b
  end.

Lemma current_seg_two_readings : forall ta rest,
  readings_current ta false (seg_tokens rest) = [IQuoted; IWhole].
Proof.
  intros ta rest. unfold readings_current. rewrite at_quoted_gate_dead_c4.
  assert (Hnt : c4_nt (seg_tokens rest) = Some "<-") by reflexivity.
  rewrite Hnt. destruct ta; vm_compute; reflexivity.
Qed.

Theorem ungated_frontier_exponential : forall ta rests,
  path_multiplier (map seg_tokens rests) (fun ts => length (readings_current ta false ts))
  = 2 ^ length rests.
Proof.
  intros ta rests. induction rests as [| rest rests IH]; [reflexivity |].
  cbn [map path_multiplier]. rewrite current_seg_two_readings, IH. reflexivity.
Qed.

(* ═══════════════ Part C: the corrected logic ═══════════════ *)

(* ── C.1 Edit 1': the depth alphabet is the matched bracket pairs. ── *)
Definition bracket_delimiters (shapes : list CollShape) : list string * list string :=
  ("(" :: map (fun s => if cs_synth s then "(" else cs_open s) shapes,
   ")" :: map cs_close shapes).

(* An arm can fire only if its triggers are outside the alphabet and the rows. *)
Definition arm_ok (opens closes rows : list string) (a : GateArm) : bool :=
  forallb (fun t => negb (mem t opens) && negb (mem t closes) && negb (mem t rows))
    (fst (snd a) ++ snd (snd a)).

Definition gate_premise (tb : ScanTables) : bool :=
  forallb (arm_ok (t_opens tb) (t_closes tb) (t_rows tb)) (t_arms tb).

Definition fixed_tables (shapes : list CollShape) (rows : list string) (arms : list GateArm)
    : ScanTables :=
  let '(o, c) := bracket_delimiters shapes in
  {| t_opens := o; t_closes := c; t_rows := rows; t_arms := filter (arm_ok o c rows) arms |}.

Definition rho_tables_fixed : ScanTables := fixed_tables rho_shapes rho_rows rho_arms.

Definition brackets_exact (shapes : list CollShape) (tb : ScanTables) : bool :=
  let '(o, c) := bracket_delimiters shapes in set_eqb (t_opens tb) o && set_eqb (t_closes tb) c.

(* ── C.2 Edit 2: a LeadingCategory push from a gated CrossCatLhs source of
   the same bucket gets the same evidence conjunct. ── *)
Definition gated_sources (gate_on : bool) (ds : list Desc) : list nat :=
  if gate_on then flat_map (fun d => match d with DCross s true => [s] | _ => [] end) ds
  else [].

Definition alive_fixed (gate_on : bool) (ds : list Desc) (cat : nat) (ta ev feasible : bool)
    (d : Desc) : bool :=
  match d with
  | DLead _ src => if existsb (Nat.eqb src) (gated_sources gate_on ds) then negb ev else true
  | _ => alive_current gate_on cat ta ev feasible d
  end.

Definition readings_fixed (ta q : bool) (ts : list Tok) : list Interp :=
  readings (alive_fixed true c4_at_descs 4 ta (evidence rho_tables_fixed 4 ts) true) c4_at_descs
    q (c4_nt ts).

(* ── C.3 Negative controls: each edit alone, and the first proposal for
   edit 1 (remove only the triggers from the closes). ── *)
Definition trigger_union (arms : list GateArm) : list string :=
  flat_map (fun a => fst (snd a) ++ snd (snd a)) arms.

Definition rho_tables_s1 : ScanTables :=
  {| t_opens := rho_opens; t_rows := rho_rows; t_arms := rho_arms;
     t_closes := filter (fun t => negb (mem t (trigger_union rho_arms))) rho_closes |}.

Definition readings_e1_only (ta q : bool) (ts : list Tok) : list Interp :=
  readings (alive_current true 4 ta (evidence rho_tables_fixed 4 ts) true) c4_at_descs q
    (c4_nt ts).

Definition readings_e2_only (ta q : bool) (ts : list Tok) : list Interp :=
  readings (alive_fixed true c4_at_descs 4 ta (evidence rho_tables_current 4 ts) true)
    c4_at_descs q (c4_nt ts).

Definition readings_s1_e2 (ta q : bool) (ts : list Tok) : list Interp :=
  readings (alive_fixed true c4_at_descs 4 ta (evidence rho_tables_s1 4 ts) true) c4_at_descs
    q (c4_nt ts).

(* ── C.4 The tables. ── *)

Theorem gate_premise_fails_current : gate_premise rho_tables_current = false.
Proof. vm_compute. reflexivity. Qed.

Theorem fixed_tables_are_true_brackets :
  set_eqb (t_opens rho_tables_fixed) true_opens = true /\
  set_eqb (t_closes rho_tables_fixed) true_closes = true.
Proof. split; vm_compute; reflexivity. Qed.

Theorem gate_premise_holds_fixed :
  gate_premise rho_tables_fixed = true /\ brackets_exact rho_shapes rho_tables_fixed = true.
Proof. split; vm_compute; reflexivity. Qed.

Theorem brackets_exact_fails_current : brackets_exact rho_shapes rho_tables_current = false.
Proof. vm_compute. reflexivity. Qed.

Theorem brackets_exact_fails_s1 : brackets_exact rho_shapes rho_tables_s1 = false.
Proof. vm_compute. reflexivity. Qed.

(* Arm 9 is dropped, because its trigger "(" is an opener. *)
Theorem fixed_arms :
  t_arms rho_tables_fixed = [(0, (["!"; "!!"], ["::"])); (4, (c4_binds, c4_stops))].
Proof. vm_compute. reflexivity. Qed.

(* ── C.5 Category 9 is behaviour-neutral. ── *)

Theorem exempt_scan_false : forall o c r ts,
  mem "(" o = true -> evidence_scan o c r ["("] [] ts = false.
Proof.
  intros o c r ts H. unfold evidence_scan. apply scan_dead. simpl. rewrite H. reflexivity.
Qed.

Theorem dropping_c9_is_behaviour_neutral : forall ts,
  evidence rho_tables_fixed 9 ts = evidence rho_tables_current 9 ts.
Proof. intro ts. rewrite at_quoted_gate_dead_c9. reflexivity. Qed.

(* ── C.6 Exactness of the fixed evidence. ── *)

Theorem evidence_fixed_c4_exact : forall ts,
  evidence rho_tables_fixed 4 ts =
  match c4_nt ts with Some t => mem t c4_binds | None => false end.
Proof.
  intro ts.
  transitivity (scan (t_opens rho_tables_fixed) (t_closes rho_tables_fixed)
                  (t_rows rho_tables_fixed) c4_binds c4_stops 0 ts).
  { reflexivity. }
  rewrite scan_is_first_trigger. unfold c4_nt.
  rewrite (first_trigger_ext (t_opens rho_tables_fixed) true_opens
             (t_closes rho_tables_fixed) true_closes
             (t_rows rho_tables_fixed) rho_rows
             (c4_binds ++ c4_stops) (c4_binds ++ c4_stops)).
  - reflexivity.
  - apply set_eqb_mem. vm_compute. reflexivity.
  - apply set_eqb_mem. vm_compute. reflexivity.
  - intro t. reflexivity.
  - intro t. reflexivity.
Qed.

(* ── C.7 Single-valued, and no legitimate parse lost. ── *)

Theorem gate_single_valued : forall ta q ts t,
  c4_nt ts = Some t -> mem t c4_binds = true -> readings_fixed ta q ts = [IQuoted].
Proof.
  intros ta q ts t Hnt Hb.
  assert (Hev : evidence rho_tables_fixed 4 ts = true)
    by (rewrite evidence_fixed_c4_exact, Hnt; exact Hb).
  unfold readings_fixed. rewrite Hev, Hnt.
  destruct (mem_c4_binds t Hb) as [-> | ->]; destruct ta, q; vm_compute; reflexivity.
Qed.

Lemma alive_fixed_agrees_without_evidence : forall gate_on ds cat ta feasible d,
  alive_fixed gate_on ds cat ta false feasible d = alive_current gate_on cat ta false feasible d.
Proof.
  intros gate_on ds cat ta feasible [src sigil | r src | w | r]; try reflexivity.
  cbn [alive_fixed alive_current negb].
  destruct (existsb (Nat.eqb src) (gated_sources gate_on ds)); reflexivity.
Qed.

Theorem gate_no_legit_parse_lost : forall ta q ts i,
  In i (readings_current ta q ts) -> legit i (c4_nt ts) = true ->
  In i (readings_fixed ta q ts).
Proof.
  intros ta q ts i Hin Hlegit. revert Hlegit.
  destruct (c4_nt ts) as [t |] eqn:Hnt; intro Hlegit.
  - destruct (mem t c4_binds) eqn:Hb.
    + rewrite (gate_single_valued ta q ts t Hnt Hb).
      destruct i; [left; reflexivity |].
      change (negb (mem t c4_binds) = true) in Hlegit.
      rewrite Hb in Hlegit. discriminate Hlegit.
    + assert (Hev : evidence rho_tables_fixed 4 ts = false)
        by (rewrite evidence_fixed_c4_exact, Hnt; exact Hb).
      unfold readings_current in Hin. unfold readings_fixed.
      rewrite at_quoted_gate_dead_c4 in Hin. rewrite Hev.
      rewrite (readings_ext (alive_fixed true c4_at_descs 4 ta false true)
                 (alive_current true 4 ta false true)).
      * exact Hin.
      * intro d. apply alive_fixed_agrees_without_evidence.
  - unfold readings_current in Hin. rewrite Hnt, readings_none in Hin. destruct Hin.
Qed.

(* The name cited by macros/.../wpda_codegen/kind_dispatch.rs:373. *)
Theorem gate_no_loss : forall ta q ts i,
  In i (readings_current ta q ts) -> legit i (c4_nt ts) = true ->
  In i (readings_fixed ta q ts).
Proof. exact gate_no_legit_parse_lost. Qed.

(* ── C.8 The original theorem names T1-T6, over the faithful definitions. ── *)

Lemma alive_fixed_implies_current : forall gate_on ds cat ta ev feasible d,
  alive_fixed gate_on ds cat ta ev feasible d = true ->
  alive_current gate_on cat ta false feasible d = true.
Proof.
  intros gate_on ds cat ta ev feasible d. destruct d as [src sigil | r src | w | r];
    cbn [alive_fixed alive_current].
  - destruct ta, gate_on, sigil, ev, feasible, (has_fallback cat src); simpl;
      intro H; congruence.
  - intros _. reflexivity.
  - intros _. reflexivity.
  - intro H. discriminate H.
Qed.

(* The fix invents no reading. *)
Theorem gate_subset_ungated : forall ta q ts i,
  In i (readings_fixed ta q ts) -> In i (readings_current ta q ts).
Proof.
  intros ta q ts i H. unfold readings_fixed in H. unfold readings_current.
  rewrite at_quoted_gate_dead_c4.
  eapply readings_mono; [| exact H].
  intros d Hd. eapply alive_fixed_implies_current. exact Hd.
Qed.

(* The fix removes only over-generations. *)
Theorem gate_removes_only_overgen : forall ta q ts i,
  In i (readings_current ta q ts) -> ~ In i (readings_fixed ta q ts) ->
  is_over_generation i (c4_nt ts) = true.
Proof.
  intros ta q ts i Hin Hnot.
  destruct (is_over_generation i (c4_nt ts)) eqn:E; [reflexivity |].
  exfalso. apply Hnot. apply gate_no_legit_parse_lost; [exact Hin |].
  unfold legit. rewrite E. reflexivity.
Qed.

Theorem gate_survivor_is_quoted : forall ta q ts t i,
  c4_nt ts = Some t -> mem t c4_binds = true -> In i (readings_fixed ta q ts) -> i = IQuoted.
Proof.
  intros ta q ts t i Hnt Hb Hin. rewrite (gate_single_valued ta q ts t Hnt Hb) in Hin.
  destruct Hin as [<- | []]. reflexivity.
Qed.

(* T1: at a scalar bind, the whole-Name reading is an over-generation, and the
   canonical quoted reading is present in the current code. *)
Theorem overgen_is_non_canonical : forall ta q ts t,
  c4_nt ts = Some t -> mem t c4_binds = true ->
  is_over_generation IWhole (c4_nt ts) = true /\ In IQuoted (readings_current ta q ts).
Proof.
  intros ta q ts t Hnt Hb. split.
  - rewrite Hnt. exact Hb.
  - unfold readings_current. rewrite Hnt. apply readings_in. exists (DSpine 2).
    split; [simpl; right; right; left; reflexivity |].
    split; [reflexivity |].
    cbn [yields]. rewrite Hb. reflexivity.
Qed.

Theorem overgen_confined : forall i nt,
  is_over_generation i nt = true ->
  i = IWhole /\ exists t, nt = Some t /\ mem t c4_binds = true.
Proof.
  intros [] [t |] H; try discriminate H.
  split; [reflexivity |]. exists t. split; [reflexivity | exact H].
Qed.

(* T4: the gated chain is linear, the ungated chain is exponential. *)
Lemma fixed_seg_one_reading : forall ta rest, readings_fixed ta false (seg_tokens rest) = [IQuoted].
Proof. intros ta rest. apply (gate_single_valued ta false (seg_tokens rest) "<-"); reflexivity. Qed.

Theorem gate_linear_frontier : forall ta rests,
  path_multiplier (map seg_tokens rests) (fun ts => length (readings_fixed ta false ts)) = 1.
Proof.
  intros ta rests. induction rests as [| rest rests IH]; [reflexivity |].
  cbn [map path_multiplier]. rewrite fixed_seg_one_reading, IH. reflexivity.
Qed.

Theorem gate_strictly_below_ungated : forall ta rests,
  rests <> [] ->
  path_multiplier (map seg_tokens rests) (fun ts => length (readings_fixed ta false ts))
  < path_multiplier (map seg_tokens rests) (fun ts => length (readings_current ta false ts)).
Proof.
  intros ta rests Hne. rewrite gate_linear_frontier, ungated_frontier_exponential.
  destruct rests as [| r rs]; [exfalso; apply Hne; reflexivity |].
  simpl. pose proof (Nat.pow_nonzero 2 (length rs) ltac:(lia)). lia.
Qed.

(* T5: with the kill switch off, the fixed guards equal the current guards,
   and no guard reads the evidence. *)
Theorem gate_kill_switch_identity : forall ds cat ta ev feasible d,
  alive_fixed false ds cat ta ev feasible d = alive_current false cat ta ev feasible d.
Proof. intros ds cat ta ev feasible [src sigil | r src | w | r]; reflexivity. Qed.

Theorem gate_off_ignores_evidence : forall ds cat ta ev ev' feasible d,
  alive_fixed false ds cat ta ev feasible d = alive_fixed false ds cat ta ev' feasible d.
Proof. intros ds cat ta ev ev' feasible [src sigil | r src | w | r]; reflexivity. Qed.

(* With the kill switch on, a LeadingCategory push from a gated source is gated. *)
Theorem gate_on_is_gated : forall ds cat ta ev feasible r src,
  In (DCross src true) ds -> alive_fixed true ds cat ta ev feasible (DLead r src) = negb ev.
Proof.
  intros ds cat ta ev feasible r src Hin.
  assert (E : existsb (Nat.eqb src) (gated_sources true ds) = true).
  { apply existsb_exists. exists src. split; [| apply Nat.eqb_refl].
    unfold gated_sources. simpl. apply in_flat_map. exists (DCross src true).
    split; [exact Hin | simpl; left; reflexivity]. }
  cbn [alive_fixed]. rewrite E. reflexivity.
Qed.

(* T6: the realize-time backstop (B). Its drop set is the over-generation
   (wpda_walker.rs:9350-9360, `packing_is_at_quoted_bind_overgen`). *)
Definition realize_drop (nt : option string) (l : list Interp) : list Interp :=
  filter (fun i => legit i nt) l.

Theorem drop_set_sound : forall i nt, is_over_generation i nt = true -> legit i nt = false.
Proof. intros i nt H. unfold legit. rewrite H. reflexivity. Qed.

(* The drop keeps every legitimate reading of the ungated forest. *)
Theorem realize_never_drops_legit : forall ta q ts i,
  In i (readings_current ta q ts) -> legit i (c4_nt ts) = true ->
  In i (realize_drop (c4_nt ts) (readings_current ta q ts)).
Proof.
  intros ta q ts i Hin Hlegit. unfold realize_drop. apply filter_In. split; assumption.
Qed.

Lemma gated_readings_are_legit : forall ta q ts i,
  In i (readings_fixed ta q ts) -> legit i (c4_nt ts) = true.
Proof.
  intros ta q ts i Hin. destruct (c4_nt ts) as [t |] eqn:Hnt.
  - destruct (mem t c4_binds) eqn:Hb.
    + rewrite (gate_single_valued ta q ts t Hnt Hb) in Hin.
      destruct Hin as [<- | []]. reflexivity.
    + destruct i; [reflexivity |].
      change (negb (mem t c4_binds) = true). rewrite Hb. reflexivity.
  - unfold readings_fixed in Hin. rewrite Hnt, readings_none in Hin. destruct Hin.
Qed.

(* Under the fixed parse gate, no whole-Name reading forms at a scalar bind,
   and the backstop drops nothing. *)
Theorem realize_inert_under_parse_gate : forall ta q ts t,
  c4_nt ts = Some t -> mem t c4_binds = true -> ~ In IWhole (readings_fixed ta q ts).
Proof.
  intros ta q ts t Hnt Hb Hin. rewrite (gate_single_valued ta q ts t Hnt Hb) in Hin.
  destruct Hin as [H | []]. discriminate H.
Qed.

Theorem realize_drop_is_identity_under_parse_gate : forall ta q ts,
  realize_drop (c4_nt ts) (readings_fixed ta q ts) = readings_fixed ta q ts.
Proof.
  intros ta q ts. unfold realize_drop. apply filter_all_true.
  intros i Hi. apply (gated_readings_are_legit ta q ts i Hi).
Qed.

(* ── C.9 Both edits are needed; the first proposal for edit 1 is refuted. ── *)

Theorem edit1_alone_leaves_whole_name : forall ta,
  readings_e1_only ta false ex_g2a = [IQuoted; IWhole].
Proof. intros [|]; vm_compute; reflexivity. Qed.

Theorem edit2_alone_leaves_whole_name : forall ta,
  readings_e2_only ta false ex_g2a = [IQuoted; IWhole].
Proof. intros [|]; vm_compute; reflexivity. Qed.

Theorem s1_edit1_loses_polyadic_parse : forall ta,
  readings_current ta false ex_loss = [IWhole] /\ readings_s1_e2 ta false ex_loss = [].
Proof. intros [|]; split; vm_compute; reflexivity. Qed.

Theorem fixed_keeps_polyadic : forall ta,
  readings_fixed ta false ex_loss = [IWhole] /\ readings_fixed ta false ex_poly = [IWhole].
Proof. intros [|]; split; vm_compute; reflexivity. Qed.

Theorem fixed_g2a_single_reading : forall ta, readings_fixed ta false ex_g2a = [IQuoted].
Proof. intros [|]; vm_compute; reflexivity. Qed.

(* ═════════════ Assumption audit: each must print "Closed under the global context" ═════════════ *)
Print Assumptions scan_dead.
Print Assumptions scan_is_first_trigger.
Print Assumptions first_trigger_ext.
Print Assumptions at_quoted_gate_dead_c4.
Print Assumptions at_quoted_gate_dead_c9.
Print Assumptions structural_delimiters_reproduce_snapshot.
Print Assumptions current_g2a_two_readings.
Print Assumptions gate_single_valued_refuted_on_current.
Print Assumptions ungated_frontier_exponential.
Print Assumptions gate_premise_fails_current.
Print Assumptions fixed_tables_are_true_brackets.
Print Assumptions gate_premise_holds_fixed.
Print Assumptions brackets_exact_fails_current.
Print Assumptions brackets_exact_fails_s1.
Print Assumptions fixed_arms.
Print Assumptions exempt_scan_false.
Print Assumptions dropping_c9_is_behaviour_neutral.
Print Assumptions evidence_fixed_c4_exact.
Print Assumptions gate_single_valued.
Print Assumptions gate_no_legit_parse_lost.
Print Assumptions gate_no_loss.
Print Assumptions gate_subset_ungated.
Print Assumptions gate_removes_only_overgen.
Print Assumptions gate_survivor_is_quoted.
Print Assumptions overgen_is_non_canonical.
Print Assumptions overgen_confined.
Print Assumptions gate_linear_frontier.
Print Assumptions gate_strictly_below_ungated.
Print Assumptions gate_kill_switch_identity.
Print Assumptions gate_off_ignores_evidence.
Print Assumptions gate_on_is_gated.
Print Assumptions drop_set_sound.
Print Assumptions realize_never_drops_legit.
Print Assumptions realize_inert_under_parse_gate.
Print Assumptions realize_drop_is_identity_under_parse_gate.
Print Assumptions edit1_alone_leaves_whole_name.
Print Assumptions edit2_alone_leaves_whole_name.
Print Assumptions s1_edit1_loses_polyadic_parse.
Print Assumptions fixed_keeps_polyadic.
Print Assumptions fixed_g2a_single_reading.

Definition SourceGateArm : Type := ((nat * nat) * (list string * list string))%type.

Fixpoint source_arm_lookup (arms : list SourceGateArm) (result source : nat)
    : list string * list string :=
  match arms with
  | [] => ([], [])
  | ((r, s), triggers) :: rest =>
      if Nat.eqb result r && Nat.eqb source s then triggers
      else source_arm_lookup rest result source
  end.

Definition source_evidence (arms : list SourceGateArm) (result source : nat)
    (ts : list Tok) : bool :=
  let '(binds, stops) := source_arm_lookup arms result source in
  evidence_scan (t_opens rho_tables_fixed) (t_closes rho_tables_fixed)
    (t_rows rho_tables_fixed) binds stops ts.

Definition rho_source_arms : list SourceGateArm :=
  [((0, 6), (["!"; "!!"], [])); ((4, 6), (["<-"; "<="], [","]))].

Theorem foreign_source_arm_is_ignored : forall arms result source r s triggers,
  source <> s ->
  source_arm_lookup (((r, s), triggers) :: arms) result source =
  source_arm_lookup arms result source.
Proof.
  intros. simpl. assert (Nat.eqb source s = false) by (apply Nat.eqb_neq; assumption).
  rewrite H0, andb_false_r. reflexivity.
Qed.

Theorem missing_source_gate_is_inert : forall arms result source ts,
  source_arm_lookup arms result source = ([], []) ->
  source_evidence arms result source ts = false.
Proof. intros. unfold source_evidence. rewrite H. reflexivity. Qed.

Theorem input_bind_source_gate_refines_fixed : forall ts,
  source_evidence rho_source_arms 4 6 ts = evidence rho_tables_fixed 4 ts.
Proof. intros. reflexivity. Qed.

Theorem cost_signature_source_gate_is_inert : forall ts,
  source_evidence rho_source_arms 0 1 ts = false.
Proof. intros. reflexivity. Qed.

Print Assumptions foreign_source_arm_is_ignored.
Print Assumptions missing_source_gate_is_inert.
Print Assumptions input_bind_source_gate_refines_fixed.
Print Assumptions cost_signature_source_gate_is_inert.

Definition guarded_source_evidence (sigil : bool) (arms : list SourceGateArm)
    (result source : nat) (ts : list Tok) : bool :=
  sigil && source_evidence arms result source ts.

Theorem non_sigil_source_keeps_its_delegate : forall arms result source ts,
  guarded_source_evidence false arms result source ts = false.
Proof. reflexivity. Qed.

Definition projection_whole_source_reading (ts : list Tok) : list Interp :=
  if guarded_source_evidence true rho_source_arms 4 6 ts then [] else [IWhole].

Theorem projection_cannot_restore_the_rejected_whole_source : forall ta q ts t,
  c4_nt ts = Some t -> mem t c4_binds = true ->
  readings_fixed ta q ts ++ projection_whole_source_reading ts = [IQuoted].
Proof.
  intros ta q ts t Hnt Hb.
  rewrite (gate_single_valued ta q ts t Hnt Hb).
  unfold projection_whole_source_reading, guarded_source_evidence.
  rewrite input_bind_source_gate_refines_fixed, evidence_fixed_c4_exact, Hnt, Hb.
  reflexivity.
Qed.

Print Assumptions non_sigil_source_keeps_its_delegate.
Print Assumptions projection_cannot_restore_the_rejected_whole_source.


Module QualifiedGateRows.

Record GateKey := {
  result_category : nat;
  source_category : nat;
  prefix_literal : string;
  operator_literal : string
}.

Definition key_eqb (x y : GateKey) : bool :=
  Nat.eqb (result_category x) (result_category y) &&
  Nat.eqb (source_category x) (source_category y) &&
  String.eqb (prefix_literal x) (prefix_literal y) &&
  String.eqb (operator_literal x) (operator_literal y).

Lemma key_eqb_spec : forall x y, key_eqb x y = true <-> x = y.
Proof.
  intros [r s p t] [r' s' p' t']. unfold key_eqb; simpl.
  repeat rewrite andb_true_iff.
  rewrite !Nat.eqb_eq, !String.eqb_eq.
  split; [intros [[[-> ->] ->] ->]; reflexivity |].
  intro H. inversion H. repeat split; reflexivity.
Qed.

Record Candidate := {
  candidate_key : GateKey;
  whole_rule : nat;
  has_operand : bool;
  operand_matches : bool;
  continuation_matches : bool
}.

Definition qualifies (row : Candidate) : bool :=
  has_operand row && operand_matches row && continuation_matches row.

Definition covers (key : GateKey) (rule : nat) (row : Candidate) : bool :=
  key_eqb key (candidate_key row) && Nat.eqb rule (whole_rule row) && qualifies row.

Definition covered (rows : list Candidate) (key : GateKey) (rule : nat) : bool :=
  existsb (covers key rule) rows.

Definition gate (rows : list Candidate) (key : GateKey) (required : list nat) : bool :=
  negb (Nat.eqb (length required) 0) && forallb (covered rows key) required.

Theorem selected_row_has_exact_provenance : forall rows key rule,
  covered rows key rule = true ->
  exists row, In row rows /\ candidate_key row = key /\ whole_rule row = rule /\
    has_operand row = true /\ operand_matches row = true /\ continuation_matches row = true.
Proof.
  intros rows key rule H. apply existsb_exists in H.
  destruct H as [row [Hin H]]. exists row. unfold covers, qualifies in H.
  repeat rewrite andb_true_iff in H.
  destruct H as [[Hkey Hrule] [[Hop Htype] Htail]].
  apply key_eqb_spec in Hkey. apply Nat.eqb_eq in Hrule.
  repeat split; auto.
Qed.

Theorem unrelated_key_is_inert : forall row key rule,
  candidate_key row <> key -> covers key rule row = false.
Proof.
  intros row key rule H. unfold covers.
  destruct (key_eqb key (candidate_key row)) eqn:E; [|reflexivity].
  apply key_eqb_spec in E. symmetry in E. contradiction.
Qed.

Theorem nullary_rule_cannot_cover : forall key rule row,
  has_operand row = false -> covers key rule row = false.
Proof. intros. unfold covers, qualifies. rewrite H. simpl. apply andb_false_r. Qed.

Theorem foreign_operand_cannot_cover : forall key rule row,
  operand_matches row = false -> covers key rule row = false.
Proof.
  intros. unfold covers, qualifies. rewrite H, andb_false_r. simpl.
  apply andb_false_r.
Qed.

Theorem different_tail_cannot_cover : forall key rule row,
  continuation_matches row = false -> covers key rule row = false.
Proof. intros. unfold covers, qualifies. rewrite H, !andb_false_r. reflexivity. Qed.

Theorem gate_covers_every_required_rule : forall rows key required rule,
  gate rows key required = true -> In rule required -> covered rows key rule = true.
Proof.
  intros rows key required rule H Hin. unfold gate in H.
  apply andb_true_iff in H. destruct H as [_ H].
  rewrite forallb_forall in H. auto.
Qed.

Theorem uncovered_alternative_keeps_delegate : forall rows key required rule,
  In rule required -> covered rows key rule = false -> gate rows key required = false.
Proof.
  intros rows key required rule Hin Hmiss.
  destruct (gate rows key required) eqn:Hgate; [|reflexivity].
  pose proof (gate_covers_every_required_rule rows key required rule Hgate Hin).
  congruence.
Qed.

Theorem absent_family_keeps_delegate : forall rows key, gate rows key [] = false.
Proof. reflexivity. Qed.

Theorem complete_family_selects_gate : forall rows key required,
  required <> [] ->
  (forall rule, In rule required -> covered rows key rule = true) ->
  gate rows key required = true.
Proof.
  intros rows key [|r rs] Hne H; [contradiction|].
  unfold gate. simpl length. simpl negb. simpl Nat.eqb.
  apply forallb_forall. exact H.
Qed.

Definition prefix_key (prefix operator : string) : GateKey :=
  {| result_category := 0; source_category := 1;
     prefix_literal := prefix; operator_literal := operator |}.

Definition complete_row (prefix operator : string) : Candidate :=
  {| candidate_key := prefix_key prefix operator; whole_rule := 0;
     has_operand := true; operand_matches := true; continuation_matches := true |}.

Example independent_unions_invent_a_pair :
  gate [complete_row "(" "?"; complete_row "@" "!"] (prefix_key "(" "!") [0] = false.
Proof. reflexivity. Qed.

Print Assumptions key_eqb_spec.
Print Assumptions selected_row_has_exact_provenance.
Print Assumptions unrelated_key_is_inert.
Print Assumptions nullary_rule_cannot_cover.
Print Assumptions foreign_operand_cannot_cover.
Print Assumptions different_tail_cannot_cover.
Print Assumptions gate_covers_every_required_rule.
Print Assumptions uncovered_alternative_keeps_delegate.
Print Assumptions absent_family_keeps_delegate.
Print Assumptions complete_family_selects_gate.
Print Assumptions independent_unions_invent_a_pair.

End QualifiedGateRows.
