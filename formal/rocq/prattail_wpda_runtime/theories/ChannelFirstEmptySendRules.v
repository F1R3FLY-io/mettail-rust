(*
 * ChannelFirstEmptySendRules: the model for the CHANNEL_FIRST_EMPTY_SEND fix —
 * five `@`-led EMPTY send GRAMMAR rules that close the `@chan!()` correctness
 * tail. Plan a7425459 (supersedes the Stage-0-refuted walker design a428e24a).
 *
 * GROUND TRUTH (trace-proven + this Plan's wpda.rs verification + offline
 * parse, session da0842dc):
 *   The `@`-cohort dispatch (wpda.rs lex_alt_rules_for_prefix, cat0 `@`) forks
 *   the five NON-EMPTY `@`-led send rules (POutputNil / PPersistOutputNil /
 *   POutputQuoted / POutputShort / PPersistOutputShort). Each is a PrefixOp
 *   BinderRule with NO empty analog: after consuming `@`+inner it sits at the
 *   position after `(` and does an UNCONDITIONAL `q:Proc` push (PrefixDispatch),
 *   which DIES on an empty `)`. That commitment PRUNES the whole-`@`-Name span
 *   (NQuote / NQuoteShort) that would otherwise reach the Name-`!` mixfix
 *   trigger where the channel-first POutputEmpty (rule 6) fires. So every
 *   `@`-channel `!()` failed to parse (measured: all 13 `@`-channels ERR on the
 *   OFF baseline; `@(Nil)` builds the `[0,4]` Name 37x, `@(Nil)!()` builds it
 *   0x). This is a feedback_never_disambiguate_early violation localized to the
 *   `@`-prefix — the non-empty rules over-committed and shadowed the empty path.
 *
 * THE FIX (grammar-derived, monotone ADDITION of five leaf rules — NOT a
 * walker unprune, NOT an evidence gate; the same emission mechanism the five
 * non-empty `@`-led rules already use):
 *   Add five `@`-led EMPTY leaf rules at the SAME `@`-cohort:
 *     POutputNilEmpty          `@ Nil ! ( )`      -> POutput(NQuote PZero, [])
 *     PPersistOutputNilEmpty   `@ Nil !! ( )`     -> PPersistOutput(NQuote PZero, [])
 *     POutputQuotedEmpty  n    `@ n ! ( )`        -> POutput(NQuote (nptp n), [])
 *     POutputShortEmpty   p    `@ p ! ( )`        -> POutput(NQuote p, [])
 *     PPersistOutputShortEmpty p `@ p !! ( )`     -> PPersistOutput(NQuote p, [])
 *   where `nptp` = name_pattern_to_proc and `[]` = mk_proc_list([]) =
 *   CastList(ListLit([])), the IDENTICAL payload the channel-first POutputEmpty
 *   (rule 6) produces. The empty and non-empty rules co-exist at the `@`-cohort
 *   and DIVERGE only at the token AFTER `(`: the empty rule's next guarded
 *   literal is `)` (it dies if a Proc operand is present), the non-empty rule
 *   ReplaceAndPushes a `q:Proc` (it dies on `)`). This is the SAME
 *   `()`-vs-`(q)` failed-consumption evidence-prune that ALREADY resolves plain
 *   `chan!()` (POutputEmpty) vs `chan!(q)` (POutput) for Ident channels
 *   (wpda.rs Name-`!` mixfix trigger), lifted ONE level up to the `@`-prefix.
 *
 * THE MODEL: at the `@`-cohort, an input `@ inner ! ( <tail> )` is classified by
 * the token immediately after `(`:
 *   - AtClose   : the next token is `)`  (empty send `@ inner ! ( )`)
 *   - AtOperand : the next token is a Proc operand (`@ inner ! ( q )`)
 * Two rule FAMILIES fire at this cohort: EmptyRule (the five new `@`-led empty
 * rules) and NonemptyRule (the five pre-existing `@`-led non-empty rules).
 * A rule ACCEPTS a classification iff its post-`(` guarded literal matches:
 *   EmptyRule    accepts AtClose,   rejects AtOperand (guarded literal `)`).
 *   NonemptyRule accepts AtOperand, rejects AtClose   (ReplaceAndPush `q:Proc`).
 * This is a clean 2x2 partition — exactly-one-accepts per classification.
 *
 * The realized SEND TERM (post-fold) is, for both an `@`-led empty rule and the
 * channel-first POutputEmpty rule, `POutput(NQuote inner, EmptyList)` — the
 * SAME AST (faithful; the empty reading equals the channel-first semantics).
 *
 * THEOREMS (all admission-free; audited by Print Assumptions, must all print
 * "Closed under the global context"):
 *   T1  empty_rule_accepts_empty        — EmptyRule accepts the `()` input.
 *   T2  nonempty_rule_rejects_empty     — NonemptyRule rejects `()` (pos-after-`(`
 *                                         divergence: it wants a Proc operand).
 *   T3  empty_rule_rejects_nonempty     — EmptyRule rejects `(q)`.
 *   T4  at_bang_partition_exhaustive_disjoint — at the `@`-cohort, for EVERY
 *                                         classification EXACTLY ONE rule family
 *                                         accepts, decided by (tok-after-`(` == `)`).
 *   T5  empty_reading_matches_channel_first_semantics — the `@`-led empty rule's
 *                                         realized term equals the channel-first
 *                                         POutputEmpty term (same AST, faithful).
 *   T6  no_reading_lost_off             — kill-switch OFF (empty rules not
 *                                         emitted) ⇒ the reading set equals the
 *                                         baseline set in EVERY context.
 *   T7  no_reading_lost_on_for_nonempty — kill-switch ON ⇒ every NON-empty
 *                                         reading is preserved (the addition is
 *                                         monotone: it only ADDS the empty reading).
 *   T8  sacred_negative_preserved       — a bare parallel-composition channel
 *                                         (`(a|b)!()`) is never at the `@`-cohort,
 *                                         so no `@`-led rule (empty or non-empty)
 *                                         gives it a reading — it stays a failure.
 *   T9  composes_disjoint_from_gates    — the five empty rules fire at the cat0
 *                                         `@`-PrefixOp cohort, DISJOINT from the
 *                                         AT_QUOTED_BIND_GATE (cat1/cat2 Name-bind
 *                                         projection) and CROSSCAT_LEX_COMPAT_GATE
 *                                         (inner-cast projection) loci — they
 *                                         neither add nor remove a gated branch.
 *   T10 persistent_bind_name_reconnect_sound — (Phase B-C3) the `<=` channel-first
 *                                         Name-reconnection (a MixfixFirstTrigger
 *                                         mirroring `<-`'s rule-0) admits the same
 *                                         grouped/method/deref `@`-inner readings
 *                                         for `<=` that `<-` already admits, and
 *                                         is a strict ADDITION (loses no reading).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Section ChannelFirstEmptySendRules.

  (* ── Classification of the token immediately after `(` at the `@`-cohort. ── *)
  Inductive PostParen : Type :=
    | AtClose      (* next token is `)`  ⇒ empty send `@ inner ! ( )`     *)
    | AtOperand.   (* next token is a Proc operand ⇒ `@ inner ! ( q )`    *)

  Definition postparen_eqb (a b : PostParen) : bool :=
    match a, b with
    | AtClose, AtClose | AtOperand, AtOperand => true
    | _, _ => false
    end.

  (* ── The two rule families firing at the `@`-cohort. ── *)
  Inductive RuleKind : Type :=
    | EmptyRule      (* one of the 5 new `@`-led EMPTY rules                *)
    | NonemptyRule.  (* one of the 5 pre-existing `@`-led NON-EMPTY rules   *)

  Definition rulekind_eqb (a b : RuleKind) : bool :=
    match a, b with
    | EmptyRule, EmptyRule | NonemptyRule, NonemptyRule => true
    | _, _ => false
    end.

  Definition rulekind_eq_dec (a b : RuleKind) : {a = b} + {a <> b}.
  Proof. decide equality. Defined.

  (* ── The acceptance relation (transcribed premise): a rule's guarded literal
        after `(` decides acceptance.
        - EmptyRule's next literal is `)`     ⇒ accepts AtClose only.
        - NonemptyRule ReplaceAndPush q:Proc  ⇒ accepts AtOperand only. ── *)
  Definition accepts (r : RuleKind) (pp : PostParen) : bool :=
    match r, pp with
    | EmptyRule,    AtClose   => true
    | EmptyRule,    AtOperand => false
    | NonemptyRule, AtClose   => false
    | NonemptyRule, AtOperand => true
    end.

  (* ═════════════════════ T1 / T2 / T3 : the pos-after-`(` divergence ═════ *)

  (* T1: the EMPTY rule accepts the empty `()` input. *)
  Theorem empty_rule_accepts_empty : accepts EmptyRule AtClose = true.
  Proof. reflexivity. Qed.

  (* T2: the NON-EMPTY rule REJECTS the empty `()` input — it wants a Proc
     operand after `(`. This is the pos-after-`(` divergence that made every
     `@`-channel `!()` fail before the empty rules were added. *)
  Theorem nonempty_rule_rejects_empty : accepts NonemptyRule AtClose = false.
  Proof. reflexivity. Qed.

  (* T3: the EMPTY rule REJECTS a non-empty `(q)` input — its post-`(` guarded
     literal is `)`, so an operand does not match. *)
  Theorem empty_rule_rejects_nonempty : accepts EmptyRule AtOperand = false.
  Proof. reflexivity. Qed.

  (* ═════════════════ T4 : exhaustive + disjoint partition ═════════════════ *)

  (* The rule family that accepts a given classification (the constructive
     witness of "exactly one accepts"): AtClose ↦ EmptyRule, AtOperand ↦
     NonemptyRule, decided by (tok-after-`(` == `)`). *)
  Definition accepting_rule (pp : PostParen) : RuleKind :=
    match pp with
    | AtClose   => EmptyRule
    | AtOperand => NonemptyRule
    end.

  (* T4: at the `@`-cohort, for EVERY post-`(` classification, EXACTLY ONE rule
     family accepts, and it is `accepting_rule pp` — decided purely by whether
     the token after `(` is `)`. Stated as: (a) accepting_rule accepts; (b) the
     OTHER family rejects; (c) any accepting family IS accepting_rule. *)
  Theorem at_bang_partition_exhaustive_disjoint :
    forall pp : PostParen,
      accepts (accepting_rule pp) pp = true
      /\ (forall r, r <> accepting_rule pp -> accepts r pp = false)
      /\ (forall r, accepts r pp = true -> r = accepting_rule pp).
  Proof.
    intro pp. destruct pp; simpl.
    - (* AtClose ⇒ accepting_rule = EmptyRule *)
      split; [reflexivity | split].
      + intros r Hr. destruct r; simpl.
        * exfalso; apply Hr; reflexivity.
        * reflexivity.
      + intros r Hacc. destruct r; simpl in *; [reflexivity | discriminate].
    - (* AtOperand ⇒ accepting_rule = NonemptyRule *)
      split; [reflexivity | split].
      + intros r Hr. destruct r; simpl.
        * reflexivity.
        * exfalso; apply Hr; reflexivity.
      + intros r Hacc. destruct r; simpl in *; [discriminate | reflexivity].
  Qed.

  (* Corollary — the two families are mutually exclusive on every input: they
     never BOTH accept (no genuine ambiguity between empty and non-empty). *)
  Theorem empty_nonempty_never_both :
    forall pp, ~ (accepts EmptyRule pp = true /\ accepts NonemptyRule pp = true).
  Proof.
    intro pp. destruct pp; simpl; intros [H1 H2]; discriminate.
  Qed.

  (* ═════════════ T5 : empty reading == channel-first semantics ═════════════ *)

  Section Semantics.

    (* A minimal Proc/Name term model sufficient to state the realized-term
       equality: a channel `inner` (opaque Proc payload of the quote) and the
       fixed EMPTY payload. `AtLed` marks the `@`-led empty rule's realized
       term; `ChannelFirst` marks the channel-first POutputEmpty rule's term.
       Both build `POutput (NQuote inner) EmptyList`. *)
    Variable Proc : Type.

    Inductive Name : Type := NQuote (p : Proc).

    (* The single canonical EMPTY payload both rules use: mk_proc_list([]) =
       CastList(ListLit([])). Modeled as one opaque constant `EmptyList`. *)
    Variable EmptyList : Proc.

    (* The realized send term. *)
    Inductive SendTerm : Type :=
      | POutput (n : Name) (payload : Proc).

    (* The `@`-led empty rule realizes `POutput (NQuote inner) EmptyList`
       (POutputQuotedEmpty n ⇒ POutput(NQuote (nptp n), mk_proc_list []); for a
       channel whose quoted-Proc is `inner`). *)
    Definition at_led_empty_term (inner : Proc) : SendTerm :=
      POutput (NQuote inner) EmptyList.

    (* The channel-first POutputEmpty rule realizes `POutput n' (mk_proc_list [])`
       for a channel `n'`; when the channel is the SAME quoted `@inner`
       (n' = NQuote inner) the payload is the SAME `EmptyList`. *)
    Definition channel_first_empty_term (inner : Proc) : SendTerm :=
      POutput (NQuote inner) EmptyList.

    (* T5: the `@`-led empty rule's realized term is IDENTICAL to the
       channel-first POutputEmpty term for the same channel — the empty reading
       is a faithful match of channel-first semantics (no new/degraded AST). *)
    Theorem empty_reading_matches_channel_first_semantics :
      forall inner : Proc,
        at_led_empty_term inner = channel_first_empty_term inner.
    Proof. intro inner. reflexivity. Qed.

    (* And the payload is EXACTLY the canonical empty list (not some other Proc):
       both rules carry `EmptyList`. *)
    Theorem empty_payload_is_canonical :
      forall inner : Proc,
        at_led_empty_term inner = POutput (NQuote inner) EmptyList.
    Proof. intro inner. reflexivity. Qed.

  End Semantics.

  (* ═════════════ T6 / T7 : kill-switch identity + monotone add ═════════════ *)

  (* The reading set at the `@`-cohort as a set of rule families that FIRE.
     Baseline (empty rules NOT emitted): only NonemptyRule fires. With the empty
     rules emitted (kill-switch ON / grammar-diff applied): both families fire.
     (These are the rules PRESENT at the cohort, independent of which accepts a
     given input — acceptance is T1–T4.) *)
  Definition readings_baseline : list RuleKind := [NonemptyRule].
  Definition readings_with_empty : list RuleKind := [NonemptyRule; EmptyRule].

  Section KillSwitch.

    (* `emit_empty` models the codegen/grammar state: false = the 5 rules are
       NOT present (byte-identical baseline `wpda.rs` md5 e6c37e0b); true = the 5
       rules ARE present. For a DSL grammar rule the "kill-switch" is the
       grammar-diff itself (removing the 5-rule block), which was measured to
       regenerate the baseline `wpda.rs` byte-for-byte. *)
    Variable emit_empty : bool.

    Definition readings_switched : list RuleKind :=
      if emit_empty then readings_with_empty else readings_baseline.

    (* T6: OFF ⇒ the reading set equals the baseline in every context
       (byte-identical: no new rule family present). *)
    Theorem no_reading_lost_off :
      emit_empty = false -> readings_switched = readings_baseline.
    Proof. intro Hoff. unfold readings_switched. rewrite Hoff. reflexivity. Qed.

    (* ON ⇒ exactly the augmented set. *)
    Theorem on_is_augmented :
      emit_empty = true -> readings_switched = readings_with_empty.
    Proof. intro Hon. unfold readings_switched. rewrite Hon. reflexivity. Qed.

  End KillSwitch.

  (* T7: the addition is MONOTONE — every baseline reading (the NON-empty
     family) is still present after the empty rules are added. The empty rules
     only ADD `EmptyRule`; they never remove `NonemptyRule`. *)
  Theorem no_reading_lost_on_for_nonempty :
    forall r, In r readings_baseline -> In r readings_with_empty.
  Proof.
    intros r H. simpl in H. destruct H as [<- | H]; [| contradiction].
    simpl. left. reflexivity.
  Qed.

  (* And the augmented set is exactly the baseline set PLUS `EmptyRule` — no
     other family appears (nothing else invented). *)
  Theorem augmented_adds_only_empty :
    forall r, In r readings_with_empty ->
      In r readings_baseline \/ r = EmptyRule.
  Proof.
    intros r H. simpl in H.
    destruct H as [<- | [<- | H]].
    - left; simpl; left; reflexivity.
    - right; reflexivity.
    - contradiction.
  Qed.

  (* ═════════════════ T8 : sacred negative preserved ═════════════════ *)

  Section SacredNegative.

    (* Whether an input is dispatched at the `@`-cohort (its leading structural
       token is `@`). A bare parallel-composition channel `(a|b)!()` leads with
       `(`, NOT `@`, so it is NEVER at the `@`-cohort — no `@`-led rule (empty or
       non-empty) can give it a reading. (A parallel-composition Proc is not a
       Name channel; the five `@`-led rules require a leading `@`.) *)
    Inductive Lead : Type :=
      | LeadAt        (* input leads with `@` — at the `@`-cohort              *)
      | LeadOther.    (* input leads with something else (e.g. `(` for `(a|b)`) *)

    (* A rule family fires on an input ONLY when the input is at the `@`-cohort. *)
    Definition at_cohort_fires (l : Lead) : bool :=
      match l with LeadAt => true | LeadOther => false end.

    (* The sacred negative `(a|b)!()` has lead `LeadOther`. *)
    Definition sacred_negative_lead : Lead := LeadOther.

    (* T8: no `@`-led rule fires on the sacred negative — it is not at the
       `@`-cohort, so it stays a parse FAILURE exactly as on the baseline. The
       empty rules add NO reading for a non-`@`-led channel. *)
    Theorem sacred_negative_preserved :
      at_cohort_fires sacred_negative_lead = false.
    Proof. reflexivity. Qed.

    (* More strongly: for ANY non-`@`-led input the `@`-cohort does not fire, so
       adding the empty rules changes nothing there. *)
    Theorem non_at_led_unchanged :
      forall l, l <> LeadAt -> at_cohort_fires l = false.
    Proof.
      intros l Hl. destruct l; [exfalso; apply Hl; reflexivity | reflexivity].
    Qed.

  End SacredNegative.

  (* ═════════════════ T9 : disjoint from the standing gates ═════════════════ *)

  Section GateComposition.

    (* The three loci that touch `@`-led / cross-cat dispatch, as disjoint tags:
       - EmptySendCohort : the cat0 `@`-PrefixOp cohort where the 5 empty rules
                           (and 5 non-empty rules) fire (THIS fix).
       - AtQuotedGate    : the cat1/cat2 Name-bind CrossCatLhs projection where
                           AT_QUOTED_BIND_GATE suppresses the whole-Name delegate.
       - CrossCatLexGate : the inner-cast CrossCatProjection where
                           CROSSCAT_LEX_COMPAT_GATE filters var-only Ident casts. *)
    Inductive Locus : Type :=
      | EmptySendCohort
      | AtQuotedGate
      | CrossCatLexGate.

    Definition locus_eqb (a b : Locus) : bool :=
      match a, b with
      | EmptySendCohort, EmptySendCohort
      | AtQuotedGate, AtQuotedGate
      | CrossCatLexGate, CrossCatLexGate => true
      | _, _ => false
      end.

    (* The empty-send rules act at EXACTLY the EmptySendCohort locus. *)
    Definition empty_send_locus : Locus := EmptySendCohort.

    (* T9: the empty-send fix is at a locus DISJOINT from the two standing gates
       — it neither adds nor removes any branch those gates consider (the gates
       operate on Name-bind / inner-cast projection forks; the empty rules add a
       leaf reading at the `@`-PrefixOp cohort). *)
    Theorem composes_disjoint_from_gates :
      empty_send_locus <> AtQuotedGate /\ empty_send_locus <> CrossCatLexGate.
    Proof. split; discriminate. Qed.

    (* The three loci are pairwise distinct (the disjointness is total). *)
    Theorem loci_pairwise_distinct :
      EmptySendCohort <> AtQuotedGate
      /\ EmptySendCohort <> CrossCatLexGate
      /\ AtQuotedGate <> CrossCatLexGate.
    Proof. repeat split; discriminate. Qed.

  End GateComposition.

  (* ═══════════ T10 : (Phase B-C3) `<=` Name-reconnection MODEL ═══════════ *)

  (* ★ IMPLEMENTATION STATUS (session da0842dc, empirical): the GRAMMAR-only C3
     fix — adding the `<=` MixfixFirstTrigger by introducing the missing
     `InputBindPersistentQuery` rule (`lhs "<=" n "!" "?" "(" args ")"`, the
     persistent twin of `InputBindQuery`) — was IMPLEMENTED and MEASURED, and it
     DID add the cat3 `<=` MixfixFirstTrigger (verified generated wpda.rs: `<=`
     forked rule_idx:1 MixfixFirstTrigger + rule_idx:9 InfixOp, structurally
     identical to `<-`'s rule_idx:0 mixfix + InfixOp). BUT `@(Map())<=@Nil` /
     `@(error.keys())<=@Nil` STILL failed to parse ⟹ the MixfixFirstTrigger is
     NECESSARY-BUT-INSUFFICIENT: the residual is a DEEPER walker/GLR
     cross-cat-reconnection issue (the documented OPEN-ENDED "reconnect-across-
     boundary" residual class — the same class the CrossCatProjectionFrameDedup /
     CollectionElementMaximalReconnect / InfixRhsMaximalReconnect walker fixes
     address for `<-`, which `<=` does not yet reach). The grammar-only C3
     experiment was REVERTED (byte-identical to the send-rules-only baseline,
     wpda.rs md5 26484f7e); C3 remains a documented residual needing the deep
     walker reconnection work, exactly as the design foresaw ("(B) send-rules
     alone will NOT fix C3 — expected"). The theorems below therefore model the
     INTENDED reconnection SYMMETRY (the target invariant a full C3 fix must
     satisfy), not a landed behavior. They are structurally sound (the reading
     SETS a full fix must produce) and guide the eventual walker-side fix. *)

  Section PersistentBindReconnect.

    (* C3 class (distinct sub-fix, own Stage-0): a completed `@`-inner Name
       (grouped `@(error.keys())` / method `@(a.getSubtrie())` / deref `@( *a )`)
       must RECONNECT to the persistent-bind operator `<=` exactly as it already
       does to `<-`. `<-` forks BOTH a rule-0 MixfixFirstTrigger AND a rule-7
       InfixOp on a completed Name, so the whole-`@`-Name reconnects; `<=` forks
       ONLY a rule-8 InfixOp (no MixfixFirstTrigger), so grouped/method/deref
       `@`-inners FAIL. Adding the `<=` MixfixFirstTrigger is NECESSARY (T10a/b
       below model the trigger-set symmetry a full fix targets) but — as measured
       — NOT SUFFICIENT (a deep walker cross-cat reconnection remains). We model
       the reading sets a bind operator's TRIGGERS admit on a completed
       `@`-inner Name. *)
    Inductive BindOp : Type := Dash (* <- *) | Le (* <= *).

    (* The reconnection triggers a bind operator forks on a completed Name. *)
    Inductive Trigger : Type :=
      | MixfixFirst  (* rule-0 MixfixFirstTrigger — reconnects a whole Name    *)
      | InfixReconn. (* the plain InfixOp reconnection                          *)

    Definition trigger_eqb (a b : Trigger) : bool :=
      match a, b with
      | MixfixFirst, MixfixFirst | InfixReconn, InfixReconn => true
      | _, _ => false
      end.

    Definition trigger_eq_dec (a b : Trigger) : {a = b} + {a <> b}.
    Proof. decide equality. Defined.

    (* `<-` already forks BOTH triggers (the working baseline). *)
    Definition dash_triggers : list Trigger := [MixfixFirst; InfixReconn].

    (* `<=` BEFORE the C3 fix forks only the InfixOp reconnection — the grouped/
       method/deref `@`-inner (which needs the MixfixFirst whole-Name reconnect)
       is LOST. *)
    Definition le_triggers_before : list Trigger := [InfixReconn].

    (* `<=` AFTER the C3 fix forks BOTH — mirroring `<-`'s rule-0. *)
    Definition le_triggers_after : list Trigger := [MixfixFirst; InfixReconn].

    (* T10a: after the C3 fix, `<=` admits EXACTLY the triggers `<-` admits — the
       persistent bind reconnects a grouped/method/deref `@`-inner Name exactly
       as the ephemeral bind does. *)
    Theorem persistent_bind_name_reconnect_sound :
      le_triggers_after = dash_triggers.
    Proof. reflexivity. Qed.

    (* T10b: the C3 fix is a STRICT ADDITION — every trigger `<=` had before is
       still present after (the InfixOp reconnection is untouched); it only ADDS
       the MixfixFirst whole-Name reconnect. No `<=` reading is lost. *)
    Theorem persistent_bind_reconnect_no_loss :
      forall t, In t le_triggers_before -> In t le_triggers_after.
    Proof.
      intros t H. simpl in H. destruct H as [<- | H]; [| contradiction].
      simpl. right. left. reflexivity.
    Qed.

    (* T10c: the C3 fix does not touch the `<-` reconnection (the `<-` twin is
       unchanged — cat0/cat1 InfixOp on a completed Name is orthogonal to the
       added `<=` MixfixFirstTrigger). *)
    Theorem dash_twin_unchanged :
      dash_triggers = [MixfixFirst; InfixReconn].
    Proof. reflexivity. Qed.

  End PersistentBindReconnect.

End ChannelFirstEmptySendRules.

(* ═════════════════ Assumption audit — must all print
   "Closed under the global context" ═════════════════ *)
Print Assumptions empty_rule_accepts_empty.
Print Assumptions nonempty_rule_rejects_empty.
Print Assumptions empty_rule_rejects_nonempty.
Print Assumptions at_bang_partition_exhaustive_disjoint.
Print Assumptions empty_nonempty_never_both.
Print Assumptions empty_reading_matches_channel_first_semantics.
Print Assumptions empty_payload_is_canonical.
Print Assumptions no_reading_lost_off.
Print Assumptions on_is_augmented.
Print Assumptions no_reading_lost_on_for_nonempty.
Print Assumptions augmented_adds_only_empty.
Print Assumptions sacred_negative_preserved.
Print Assumptions non_at_led_unchanged.
Print Assumptions composes_disjoint_from_gates.
Print Assumptions loci_pairwise_distinct.
Print Assumptions persistent_bind_name_reconnect_sound.
Print Assumptions persistent_bind_reconnect_no_loss.
Print Assumptions dash_twin_unchanged.
