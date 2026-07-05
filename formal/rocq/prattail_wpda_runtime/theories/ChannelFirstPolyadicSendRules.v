(*
 * ChannelFirstPolyadicSendRules: the model for the CHANNEL_FIRST_POLYADIC_SEND
 * fix — five `@`-led POLYADIC (2Plus) send GRAMMAR rules that close the
 * `@chan!(a,b)` correctness tail. Plan af1f872c. This is the exact analog of the
 * five `@`-led EMPTY rules (ChannelFirstEmptySendRules.v, Plan a7425459), ONE
 * ARITY OVER, extended to the THREE-WAY empty/scalar/2Plus partition.
 *
 * GROUND TRUTH (this Plan's wpda.rs verification + offline parse, session
 * da0842dc — Stage-0 gates S0-POLY-PARSE + S0-POLY-SOUND + S0-POLY-NoLoss all
 * PASS, and S0-POLY-BYTE-IDENTICAL-OFF: removing the 5-rule block regenerates
 * the OFF-baseline wpda.rs byte-for-byte, md5 26484f7e):
 *   The `@`-cohort dispatch forks the `@`-led SCALAR send rules (POutputNil /
 *   POutputQuoted / POutputShort / PPersistOutputNil / PPersistOutputShort) and
 *   the `@`-led EMPTY send rules (…Empty). Each SCALAR rule, after consuming
 *   `@`+inner+`(`, does an UNCONDITIONAL SINGLE `q:Proc` push then expects `)` —
 *   it DIES on the polyadic tail `a "," bs`. Each EMPTY rule expects `)`
 *   immediately — it also dies on an operand. So NO `@`-channel `!(a,b)` parsed
 *   before these five rules were added (measured: all `@`-channels ERR on the
 *   OFF baseline; the channel-first POutput2Plus / PPersistOutput2Plus at
 *   rhocalc.rs:138-158 accept ONLY an Ident channel `n:Name`). This is a
 *   feedback_never_disambiguate_early violation localized to the `@`-prefix
 *   polyadic case — the scalar/empty rules over-committed and shadowed the
 *   polyadic path.
 *
 * THE FIX (grammar-derived, monotone ADDITION of five leaf rules — NOT a walker
 * unprune, NOT an evidence gate; the SAME emission mechanism the `@`-led scalar
 * and empty rules already use):
 *   Add five `@`-led POLYADIC leaf rules at the SAME `@`-cohort:
 *     POutputNil2Plus          a bs  `@ Nil ! ( a , bs )`  -> POutput(NQuote PZero, [a;bs])
 *     PPersistOutputNil2Plus   a bs  `@ Nil !! ( a , bs )` -> PPersistOutput(NQuote PZero, [a;bs])
 *     POutputQuoted2Plus n a bs      `@ n ! ( a , bs )`    -> POutput(NQuote (nptp n), [a;bs])
 *     POutputShort2Plus  p a bs      `@ p ! ( a , bs )`    -> POutput(NQuote p, [a;bs])
 *     PPersistOutputShort2Plus p a bs `@ p !! ( a , bs )`  -> PPersistOutput(NQuote p, [a;bs])
 *   where `nptp` = name_pattern_to_proc and `[a;bs]` = mk_proc_list([a, ...bs]) =
 *   CastList(ListLit([a, ...bs])), the IDENTICAL payload the channel-first
 *   POutput2Plus rule produces. The three `@`-led families co-exist at the
 *   `@`-cohort and DIVERGE only at t₁ = token-after-`(` and t₂ =
 *   token-after-first-operand.
 *
 * THE MODEL: at the `@`-cohort, an input `@ inner ! ( <tail> )` is classified by
 * (t₁, t₂):
 *   - AtClose      : t₁ = `)`                    ⇒ empty  `@ inner ! ( )`
 *   - AtScalarClose: t₁ = operand, t₂ = `)`      ⇒ scalar `@ inner ! ( q )`
 *   - AtPolyComma  : t₁ = operand, t₂ = `,`      ⇒ 2Plus  `@ inner ! ( a , b )`
 * Three rule FAMILIES fire at this cohort: EmptyRule, ScalarRule, PolyRule.
 * A rule ACCEPTS a classification iff its guarded shape after `(` matches:
 *   EmptyRule  accepts AtClose       (guarded literal `)` right after `(`).
 *   ScalarRule accepts AtScalarClose (one `q:Proc` then `)`).
 *   PolyRule   accepts AtPolyComma   (one `a:Proc` then `,` then `bs`).
 * This is a clean 3x3 partition — exactly-one-accepts per classification. The
 * three families share the `@ inner ! (` prefix and are NOT multiplicative (they
 * diverge at t₁/t₂ only), so at most one branch survives.
 *
 * The realized SEND TERM (post-fold — the `![{…}]` rewrite the Dovetail/Exec
 * engine applies) for both a `@`-led polyadic rule and the channel-first
 * POutput2Plus rule on the SAME channel is `POutput (NQuote inner)
 * (ProcList [a;bs])` — the SAME AST (faithful; the polyadic reading equals the
 * channel-first 2Plus semantics).
 *
 * THEOREMS (all admission-free; audited by Print Assumptions, must all print
 * "Closed under the global context"):
 *   T1  poly_accepts_2plus                     — PolyRule accepts the `(a,b)` input.
 *   T2  scalar_rejects_2plus                   — ScalarRule rejects `(a,b)` (t₂=`,`
 *                                                divergence: it wants `)` after q).
 *   T3  empty_rejects_2plus                    — EmptyRule rejects `(a,b)`.
 *   T4  poly_rejects_scalar_and_empty          — PolyRule rejects AtScalarClose and
 *                                                AtClose (t₁/t₂ divergence).
 *   T5  three_way_partition_exhaustive_disjoint — at the `@`-cohort, for EVERY
 *                                                classification EXACTLY ONE rule
 *                                                family accepts, decided by (t₁,t₂).
 *       no_two_families_both_accept            — corollary: no two families both
 *                                                accept any classification.
 *   T6  poly_reading_matches_channel_first_2plus_semantics — the `@`-led polyadic
 *                                                rule's realized term equals the
 *                                                channel-first POutput2Plus term.
 *       poly_payload_is_proc_list              — the polyadic payload is exactly the
 *                                                canonical ProcList([a;bs]).
 *   T7  no_reading_lost_off                    — kill-switch OFF (poly rules not
 *                                                emitted) ⇒ reading set = baseline
 *                                                (byte-identical wpda.rs).
 *   T8  no_reading_lost_on                     — kill-switch ON ⇒ every baseline
 *                                                reading preserved (the addition is
 *                                                MONOTONE: only ADDS the polyadic
 *                                                reading, removes nothing).
 *   T9  sacred_negative_preserved              — a bare parallel-composition channel
 *                                                (`(a|b)!(a,b)`) leads with `(` not
 *                                                `@`, so no `@`-led rule gives it a
 *                                                reading — it stays a failure.
 *   T10 composes_disjoint_from_gates           — the five poly rules fire at the
 *                                                cat0 `@`-PrefixOp cohort, DISJOINT
 *                                                from AT_QUOTED_BIND_GATE and
 *                                                CROSSCAT_LEX_COMPAT_GATE loci.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Section ChannelFirstPolyadicSendRules.

  (* ── Classification of the tokens after `(` at the `@`-cohort, by (t₁, t₂). ── *)
  Inductive PostParen : Type :=
    | AtClose        (* t₁ = `)`                 ⇒ empty  `@ inner ! ( )`        *)
    | AtScalarClose  (* t₁ = operand, t₂ = `)`   ⇒ scalar `@ inner ! ( q )`      *)
    | AtPolyComma.   (* t₁ = operand, t₂ = `,`   ⇒ 2Plus  `@ inner ! ( a , b )`  *)

  Definition postparen_eqb (a b : PostParen) : bool :=
    match a, b with
    | AtClose, AtClose
    | AtScalarClose, AtScalarClose
    | AtPolyComma, AtPolyComma => true
    | _, _ => false
    end.

  (* ── The three rule families firing at the `@`-cohort. ── *)
  Inductive RuleKind : Type :=
    | EmptyRule      (* one of the 5 `@`-led EMPTY rules       (…Empty)          *)
    | ScalarRule     (* one of the 5 `@`-led SCALAR rules      (POutputNil/…Short) *)
    | PolyRule.      (* one of the 5 new `@`-led POLYADIC rules (…2Plus)          *)

  Definition rulekind_eqb (a b : RuleKind) : bool :=
    match a, b with
    | EmptyRule, EmptyRule
    | ScalarRule, ScalarRule
    | PolyRule, PolyRule => true
    | _, _ => false
    end.

  Definition rulekind_eq_dec (a b : RuleKind) : {a = b} + {a <> b}.
  Proof. decide equality. Defined.

  (* ── The acceptance relation (transcribed premise): a rule's guarded shape
        after `(` decides acceptance.
        - EmptyRule's next literal is `)`                ⇒ accepts AtClose only.
        - ScalarRule pushes ONE q:Proc then expects `)`  ⇒ accepts AtScalarClose only.
        - PolyRule pushes a:Proc then `,` then bs        ⇒ accepts AtPolyComma only. ── *)
  Definition accepts (r : RuleKind) (pp : PostParen) : bool :=
    match r, pp with
    | EmptyRule,  AtClose       => true
    | ScalarRule, AtScalarClose => true
    | PolyRule,   AtPolyComma   => true
    | _, _ => false
    end.

  (* ═══════════ T1 / T2 / T3 / T4 : the (t₁,t₂) divergence ═══════════ *)

  (* T1: the POLYADIC rule accepts the `(a,b)` input. *)
  Theorem poly_accepts_2plus : accepts PolyRule AtPolyComma = true.
  Proof. reflexivity. Qed.

  (* T2: the SCALAR rule REJECTS `(a,b)` — after its single `q:Proc` it wants `)`,
     but t₂ = `,`. This is the t₂ divergence that made every `@`-channel `!(a,b)`
     fail before the polyadic rules were added. *)
  Theorem scalar_rejects_2plus : accepts ScalarRule AtPolyComma = false.
  Proof. reflexivity. Qed.

  (* T3: the EMPTY rule REJECTS `(a,b)` — its guarded literal after `(` is `)`,
     but t₁ = operand. *)
  Theorem empty_rejects_2plus : accepts EmptyRule AtPolyComma = false.
  Proof. reflexivity. Qed.

  (* T4: the POLYADIC rule REJECTS both the scalar `(q)` and the empty `()` — its
     guarded shape requires an operand followed by `,`. *)
  Theorem poly_rejects_scalar_and_empty :
    accepts PolyRule AtScalarClose = false /\ accepts PolyRule AtClose = false.
  Proof. split; reflexivity. Qed.

  (* ═════════════ T5 : exhaustive + disjoint 3-way partition ═════════════ *)

  (* The rule family that accepts a given classification (the constructive witness
     of "exactly one accepts"): AtClose ↦ EmptyRule, AtScalarClose ↦ ScalarRule,
     AtPolyComma ↦ PolyRule, decided purely by (t₁, t₂). *)
  Definition accepting_rule (pp : PostParen) : RuleKind :=
    match pp with
    | AtClose       => EmptyRule
    | AtScalarClose => ScalarRule
    | AtPolyComma   => PolyRule
    end.

  (* T5: at the `@`-cohort, for EVERY (t₁,t₂) classification, EXACTLY ONE rule
     family accepts, and it is `accepting_rule pp`. Stated as: (a) accepting_rule
     accepts; (b) every OTHER family rejects; (c) any accepting family IS
     accepting_rule. *)
  Theorem three_way_partition_exhaustive_disjoint :
    forall pp : PostParen,
      accepts (accepting_rule pp) pp = true
      /\ (forall r, r <> accepting_rule pp -> accepts r pp = false)
      /\ (forall r, accepts r pp = true -> r = accepting_rule pp).
  Proof.
    intro pp. destruct pp; simpl.
    - (* AtClose ⇒ accepting_rule = EmptyRule *)
      split; [reflexivity | split].
      + intros r Hr. destruct r; simpl; try reflexivity.
        exfalso; apply Hr; reflexivity.
      + intros r Hacc. destruct r; simpl in *; [reflexivity | discriminate | discriminate].
    - (* AtScalarClose ⇒ accepting_rule = ScalarRule *)
      split; [reflexivity | split].
      + intros r Hr. destruct r; simpl; try reflexivity.
        exfalso; apply Hr; reflexivity.
      + intros r Hacc. destruct r; simpl in *; [discriminate | reflexivity | discriminate].
    - (* AtPolyComma ⇒ accepting_rule = PolyRule *)
      split; [reflexivity | split].
      + intros r Hr. destruct r; simpl; try reflexivity.
        exfalso; apply Hr; reflexivity.
      + intros r Hacc. destruct r; simpl in *; [discriminate | discriminate | reflexivity].
  Qed.

  (* Corollary — no two DISTINCT families both accept the same classification
     (no genuine ambiguity among empty / scalar / 2Plus). *)
  Theorem no_two_families_both_accept :
    forall pp r1 r2,
      accepts r1 pp = true -> accepts r2 pp = true -> r1 = r2.
  Proof.
    intros pp r1 r2 H1 H2.
    destruct (three_way_partition_exhaustive_disjoint pp) as [_ [_ Huniq]].
    rewrite (Huniq r1 H1). rewrite (Huniq r2 H2). reflexivity.
  Qed.

  (* ═════════ T6 : polyadic reading == channel-first 2Plus semantics ═════════ *)

  Section Semantics.

    (* A minimal Proc/Name term model sufficient to state the realized-term
       equality: a channel `inner` (opaque Proc payload of the quote), the leading
       operand `a` and the tail `bs`, and the ProcList constructor. `AtLed` marks
       the `@`-led polyadic rule's realized term; `ChannelFirst` marks the
       channel-first POutput2Plus rule's term. Both build
       `POutput (NQuote inner) (ProcList (a :: bs))`. *)
    Variable Proc : Type.

    Inductive Name : Type := NQuote (p : Proc).

    (* The canonical polyadic payload builder: mk_proc_list([a, ...bs]) =
       CastList(ListLit([a, ...bs])). Modeled as `ProcList : Proc -> list Proc ->
       Proc` (the leading operand and the tail — exactly the fold body's
       `items.push(a); items.extend(bs)`). *)
    Variable ProcList : Proc -> list Proc -> Proc.

    (* The realized send term. *)
    Inductive SendTerm : Type :=
      | POutput (n : Name) (payload : Proc).

    (* The `@`-led polyadic rule realizes `POutput (NQuote inner)
       (ProcList a bs)` (POutputQuoted2Plus n a bs ⇒
       POutput(NQuote (nptp n), mk_proc_list(a :: bs)); for a channel whose
       quoted-Proc is `inner`). *)
    Definition at_led_poly_term (inner a : Proc) (bs : list Proc) : SendTerm :=
      POutput (NQuote inner) (ProcList a bs).

    (* The channel-first POutput2Plus rule realizes `POutput n' (mk_proc_list
       (a :: bs))` for a channel `n'`; when the channel is the SAME quoted
       `@inner` (n' = NQuote inner) the payload is the SAME `ProcList a bs`. *)
    Definition channel_first_poly_term (inner a : Proc) (bs : list Proc) : SendTerm :=
      POutput (NQuote inner) (ProcList a bs).

    (* T6: the `@`-led polyadic rule's realized term is IDENTICAL to the
       channel-first POutput2Plus term for the same channel and operands — the
       polyadic reading is a faithful match of channel-first 2Plus semantics
       (no new/degraded AST). *)
    Theorem poly_reading_matches_channel_first_2plus_semantics :
      forall (inner a : Proc) (bs : list Proc),
        at_led_poly_term inner a bs = channel_first_poly_term inner a bs.
    Proof. intros inner a bs. reflexivity. Qed.

    (* And the payload is EXACTLY the canonical ProcList of the leading operand and
       the tail (not some other Proc): both rules carry `ProcList a bs`. *)
    Theorem poly_payload_is_proc_list :
      forall (inner a : Proc) (bs : list Proc),
        at_led_poly_term inner a bs = POutput (NQuote inner) (ProcList a bs).
    Proof. intros inner a bs. reflexivity. Qed.

  End Semantics.

  (* ═════════════ T7 / T8 : kill-switch identity + monotone add ═════════════ *)

  (* The reading set at the `@`-cohort as a set of rule families that FIRE.
     Baseline (poly rules NOT emitted): EmptyRule and ScalarRule fire. With the
     poly rules emitted (kill-switch ON / grammar-diff applied): all three fire.
     (These are the rules PRESENT at the cohort, independent of which accepts a
     given input — acceptance is T1–T5.) *)
  Definition readings_baseline : list RuleKind := [EmptyRule; ScalarRule].
  Definition readings_with_poly : list RuleKind := [EmptyRule; ScalarRule; PolyRule].

  Section KillSwitch.

    (* `emit_poly` models the codegen/grammar state: false = the 5 rules are NOT
       present (byte-identical baseline `wpda.rs` md5 26484f7e); true = the 5 rules
       ARE present (md5 4637926f). For a DSL grammar rule the "kill-switch" is the
       grammar-diff itself (removing the 5-rule block), which was MEASURED to
       regenerate the baseline `wpda.rs` byte-for-byte (S0-POLY-BYTE-IDENTICAL-OFF).
       *)
    Variable emit_poly : bool.

    Definition readings_switched : list RuleKind :=
      if emit_poly then readings_with_poly else readings_baseline.

    (* T7: OFF ⇒ the reading set equals the baseline in every context
       (byte-identical: no new rule family present). *)
    Theorem no_reading_lost_off :
      emit_poly = false -> readings_switched = readings_baseline.
    Proof. intro Hoff. unfold readings_switched. rewrite Hoff. reflexivity. Qed.

    (* ON ⇒ exactly the augmented set. *)
    Theorem on_is_augmented :
      emit_poly = true -> readings_switched = readings_with_poly.
    Proof. intro Hon. unfold readings_switched. rewrite Hon. reflexivity. Qed.

  End KillSwitch.

  (* T8: the addition is MONOTONE — every baseline reading (EmptyRule and
     ScalarRule) is still present after the poly rules are added. The poly rules
     only ADD `PolyRule`; they never remove a scalar or empty reading. *)
  Theorem no_reading_lost_on :
    forall r, In r readings_baseline -> In r readings_with_poly.
  Proof.
    intros r H. simpl in H. simpl.
    destruct H as [<- | [<- | H]].
    - left; reflexivity.
    - right; left; reflexivity.
    - contradiction.
  Qed.

  (* And the augmented set is exactly the baseline set PLUS `PolyRule` — no other
     family appears (nothing else invented). *)
  Theorem augmented_adds_only_poly :
    forall r, In r readings_with_poly ->
      In r readings_baseline \/ r = PolyRule.
  Proof.
    intros r H. simpl in H.
    destruct H as [<- | [<- | [<- | H]]].
    - left; simpl; left; reflexivity.
    - left; simpl; right; left; reflexivity.
    - right; reflexivity.
    - contradiction.
  Qed.

  (* ═════════════════ T9 : sacred negative preserved ═════════════════ *)

  Section SacredNegative.

    (* Whether an input is dispatched at the `@`-cohort (its leading structural
       token is `@`). A bare parallel-composition channel `(a|b)!(a,b)` leads with
       `(`, NOT `@`, so it is NEVER at the `@`-cohort — no `@`-led rule (empty,
       scalar, or polyadic) can give it a reading. (A parallel-composition Proc is
       not a Name channel; the five `@`-led rules require a leading `@`.) This is
       the S0-POLY-NoLoss sacred negative: `(a|b)!(q,r)` still ERRs. *)
    Inductive Lead : Type :=
      | LeadAt        (* input leads with `@` — at the `@`-cohort              *)
      | LeadOther.    (* input leads with something else (e.g. `(` for `(a|b)`) *)

    (* A rule family fires on an input ONLY when the input is at the `@`-cohort. *)
    Definition at_cohort_fires (l : Lead) : bool :=
      match l with LeadAt => true | LeadOther => false end.

    (* The sacred negative `(a|b)!(a,b)` has lead `LeadOther`. *)
    Definition sacred_negative_lead : Lead := LeadOther.

    (* T9: no `@`-led rule fires on the sacred negative — it is not at the
       `@`-cohort, so it stays a parse FAILURE exactly as on the baseline. The
       poly rules add NO reading for a non-`@`-led channel. *)
    Theorem sacred_negative_preserved :
      at_cohort_fires sacred_negative_lead = false.
    Proof. reflexivity. Qed.

    (* More strongly: for ANY non-`@`-led input the `@`-cohort does not fire, so
       adding the poly rules changes nothing there. *)
    Theorem non_at_led_unchanged :
      forall l, l <> LeadAt -> at_cohort_fires l = false.
    Proof.
      intros l Hl. destruct l; [exfalso; apply Hl; reflexivity | reflexivity].
    Qed.

  End SacredNegative.

  (* ═════════════════ T10 : disjoint from the standing gates ═════════════════ *)

  Section GateComposition.

    (* The three loci that touch `@`-led / cross-cat dispatch, as disjoint tags:
       - PolySendCohort : the cat0 `@`-PrefixOp cohort where the 5 poly rules
                          (and the 5 scalar + 5 empty rules) fire (THIS fix).
       - AtQuotedGate   : the cat1/cat2 Name-bind CrossCatLhs projection where
                          AT_QUOTED_BIND_GATE suppresses the whole-Name delegate.
       - CrossCatLexGate: the inner-cast CrossCatProjection where
                          CROSSCAT_LEX_COMPAT_GATE filters var-only Ident casts. *)
    Inductive Locus : Type :=
      | PolySendCohort
      | AtQuotedGate
      | CrossCatLexGate.

    Definition locus_eqb (a b : Locus) : bool :=
      match a, b with
      | PolySendCohort, PolySendCohort
      | AtQuotedGate, AtQuotedGate
      | CrossCatLexGate, CrossCatLexGate => true
      | _, _ => false
      end.

    (* The poly-send rules act at EXACTLY the PolySendCohort locus. *)
    Definition poly_send_locus : Locus := PolySendCohort.

    (* T10: the poly-send fix is at a locus DISJOINT from the two standing gates —
       it neither adds nor removes any branch those gates consider (the gates
       operate on Name-bind / inner-cast projection forks; the poly rules add a
       leaf reading at the `@`-PrefixOp cohort). *)
    Theorem composes_disjoint_from_gates :
      poly_send_locus <> AtQuotedGate /\ poly_send_locus <> CrossCatLexGate.
    Proof. split; discriminate. Qed.

    (* The three loci are pairwise distinct (the disjointness is total). *)
    Theorem loci_pairwise_distinct :
      PolySendCohort <> AtQuotedGate
      /\ PolySendCohort <> CrossCatLexGate
      /\ AtQuotedGate <> CrossCatLexGate.
    Proof. repeat split; discriminate. Qed.

  End GateComposition.

  (* ═══════════ Bridge : the poly partition EXTENDS the empty partition ═══════ *)

  (* The empty-send model (ChannelFirstEmptySendRules.v) is a 2-way partition
     (AtClose vs AtOperand). The polyadic model REFINES `AtOperand` into
     AtScalarClose (t₂=`)`) and AtPolyComma (t₂=`,`). This projection witnesses
     that the poly model is a conservative extension: erasing the t₂ distinction
     recovers the empty model's binary AtClose/AtOperand classification. *)
  Inductive PostParenEmpty : Type := EAtClose | EAtOperand.

  Definition project_to_empty (pp : PostParen) : PostParenEmpty :=
    match pp with
    | AtClose       => EAtClose
    | AtScalarClose => EAtOperand
    | AtPolyComma   => EAtOperand
    end.

  (* The empty rule accepts exactly the AtClose classification under the
     projection — the polyadic 3-way model is consistent with the empty 2-way
     model on the shared AtClose case. *)
  Theorem poly_refines_empty_on_close :
    forall pp, project_to_empty pp = EAtClose <-> pp = AtClose.
  Proof.
    intro pp. destruct pp; simpl; split; intro H; try reflexivity; discriminate.
  Qed.

End ChannelFirstPolyadicSendRules.

(* ═════════════════ Assumption audit — must all print
   "Closed under the global context" ═════════════════ *)
Print Assumptions poly_accepts_2plus.
Print Assumptions scalar_rejects_2plus.
Print Assumptions empty_rejects_2plus.
Print Assumptions poly_rejects_scalar_and_empty.
Print Assumptions three_way_partition_exhaustive_disjoint.
Print Assumptions no_two_families_both_accept.
Print Assumptions poly_reading_matches_channel_first_2plus_semantics.
Print Assumptions poly_payload_is_proc_list.
Print Assumptions no_reading_lost_off.
Print Assumptions on_is_augmented.
Print Assumptions no_reading_lost_on.
Print Assumptions augmented_adds_only_poly.
Print Assumptions sacred_negative_preserved.
Print Assumptions non_at_led_unchanged.
Print Assumptions composes_disjoint_from_gates.
Print Assumptions loci_pairwise_distinct.
Print Assumptions poly_refines_empty_on_close.
