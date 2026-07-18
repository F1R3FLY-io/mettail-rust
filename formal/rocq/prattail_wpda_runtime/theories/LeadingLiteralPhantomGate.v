(*
 * LeadingLiteralPhantomGate: the model for the ROOT-C realize-time STRUCTURAL
 * backstop that rejects the single-result demand driver's grouping-close PHANTOM
 * cast packing.
 *
 * GROUND TRUTH (trace-proven, `Proc::parse_via_wpda("(str(Pathmap()))")`):
 *   The demand driver's grouping-close SYNTHESIZES an outer `ToStr`
 *   (`"str" "(" p ")"`) packing whose children = [operand] — the inner
 *   `str(Pathmap())` Symbol — with NO leading `str(` terminal child: the outer
 *   cast literal was fabricated, consuming ZERO input. The 1+4-pass
 *   `parse_structured` display fixpoint then re-synthesizes it every pass, so the
 *   `str` count grows +1/pass (1 -> 6) and overflows the stack on deep rhocalc
 *   Proc / InputBind terms (gen_rhocalc_prop::{proc,inputbind}_display).
 *
 *   Empirically (children[0]-dump across all three cast/grouping dispositions):
 *     - rhocalc `ToStr`  (`"str" "(" p ")"`, same-cat):  sound children[0] = TriggerTerminal.
 *     - calc `StrToInt`  (`"int" "(" a ")"`, cross-cat):  sound children[0] = TriggerTerminal.
 *     - lambda `App`     (`"(" f "," a ")"`, grouping):   sound children[0] = TriggerTerminal.
 *     - the phantom `ToStr`:                              children[0] = Symbol (the operand).
 *   A SOUND leading-literal packing ALWAYS realizes its leading literal as a
 *   terminal-kind first child (`Terminal` when in-span, `TriggerTerminal` when
 *   out-of-span); the phantom's first child is the operand `Symbol`.
 *
 * WHY the count-based backstop (`min_terminal_span`) cannot do this:
 *   `min_terminal_span` rejects a packing whose realize-time slack
 *   (result-span - Sigma operand-spans) is below a per-rule threshold. But whether
 *   a rule's LEADING literal is consumed IN-span (rhocalc `str`) or OUT-OF-span
 *   as a `TriggerTerminal` (calc `int`, lambda `(`) is a RUNTIME parse property,
 *   not a grammar property — so the codegen threshold formula cannot see it. For
 *   an out-of-span-leading rule the sound slack EQUALS the phantom slack (the
 *   leading literal contributes 0 to both), so NO threshold separates them: any
 *   threshold that rejects the phantom also rejects the sound parse (the measured
 *   formula-"J" lambda 10/11 regression). This file PROVES that wall (T5) and
 *   that the STRUCTURAL test crosses it (T6).
 *
 * THE FIX (grammar-derived, one-sided monotone refutation of a proven
 * over-generation — the same soundness class as `min_terminal_span` and
 * `AtQuotedBindGate`):
 *   Add engine metadata `rule_leads_with_literal` (true iff the rule's first
 *   syntax element is a `Literal`). `packing_satisfies_min_terminal_span` rejects
 *   a packing iff `rule_leads_with_literal(rule)` AND `children[0]` is a `Symbol`
 *   (not a `Terminal`/`TriggerTerminal`).
 *
 * THEOREMS (all admission-free; audited by Print Assumptions, must all print
 * "Closed under the global context"):
 *   T1 phantom_is_unsound           — a LiteralLed packing with a Symbol first
 *      child is token-unsound (the leading literal was not realized).
 *   T2 gate_rejects_iff_unsound     — the gate rejects a packing IFF it is
 *      token-unsound: the gate is EXACTLY the token-soundness predicate on
 *      leading-literal packings, not an approximation (sound AND complete).
 *   T3 gate_drops_no_sound_packing  — no sound packing is EVER rejected (the
 *      "never drop a real reading" guarantee).
 *   T4 param_led_symchild_preserved — an operand-led rule (infix `a "+" b`) whose
 *      first child IS a Symbol is NEVER rejected: the `leads_with_literal` guard
 *      is exactly what keeps the structural test from over-rejecting.
 *   T5 count_gate_wall              — NO per-rule count threshold separates the
 *      phantom from a SOUND out-of-span-leading cast (any threshold that rejects
 *      the phantom also rejects the sound parse) — the formula-"J" impossibility.
 *   T6 structural_gate_crosses_wall — the structural gate keeps the sound packing
 *      and rejects the phantom for BOTH leading dispositions (in-span AND
 *      out-of-span), independent of span arithmetic.
 *   T7 default_off_identity         — with `rule_leads_with_literal` ≡ false (the
 *      trait default) the gate rejects nothing (byte-identical codegen for
 *      grammars with no literal-led rules).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Section LeadingLiteralPhantomGate.

  (* ── A rule either LEADS WITH A LITERAL (a cast / grouping / sigil send whose
        `syntax_pattern[0]` is a `Literal`), or leads with a parameter (an infix /
        operand-led rule whose `syntax_pattern[0]` is a `Param`). This is exactly
        the grammar fact `rule_leads_with_literal` decides. ── *)
  Inductive RuleShape : Type :=
    | LiteralLed   (* syntax_pattern[0] is a Literal (cast/grouping/sigil send) *)
    | ParamLed.    (* syntax_pattern[0] is a Param (infix / operand-led rule) *)

  (* ── The kind of the packing's FIRST SPPF child, as observed at realize time. ── *)
  Inductive FirstChild : Type :=
    | TermChild    (* a `Terminal` OR `TriggerTerminal` — a realized fixed token *)
    | SymChild.    (* a nonterminal `Symbol` — an operand sub-derivation *)

  (* A packing, as seen by `packing_satisfies_min_terminal_span`: its rule's
     leading shape and its realized first-child kind. *)
  Record Packing : Type := mkPacking { shape : RuleShape ; first_child : FirstChild }.

  (* ── TOKEN-SOUNDNESS (the walker/grammar invariant, transcribed from the
        children[0] trace above):
        - A LiteralLed rule's SOUND packing realizes its leading literal as a
          terminal-kind first child (`TermChild`). A LiteralLed packing whose
          first child is a `Symbol` did NOT consume the leading literal ⇒
          TOKEN-UNSOUND (the fabricated grouping-close phantom).
        - A ParamLed rule's first child IS its leading operand (a `Symbol`),
          legitimately, so such packings are sound regardless of first-child kind.
     ── *)
  Definition sound (p : Packing) : bool :=
    match shape p, first_child p with
    | LiteralLed, SymChild => false   (* the phantom: leading literal unrealized *)
    | _, _ => true
    end.

  (* ── `rule_leads_with_literal` (codegen: true exactly for a Literal-led rule). ── *)
  Definition rll (s : RuleShape) : bool :=
    match s with LiteralLed => true | ParamLed => false end.

  (* ── THE GATE (the fix): reject a packing iff its rule leads with a literal AND
        its realized first child is a `Symbol`. This is a purely STRUCTURAL test —
        it never inspects span arithmetic. Parameterized by the leads-with-literal
        oracle so the trait default (≡ false) is expressible (T7). ── *)
  Definition gate_rejects (leads : RuleShape -> bool) (p : Packing) : bool :=
    leads (shape p)
    && match first_child p with SymChild => true | TermChild => false end.

  (* ═════════════════════ T1: the phantom is unsound ═════════════════════ *)
  Theorem phantom_is_unsound :
    sound (mkPacking LiteralLed SymChild) = false.
  Proof. reflexivity. Qed.

  (* ═════════ T2: the gate = the token-soundness predicate (sound + complete) ═════════ *)
  (* The gate rejects a packing IFF it is token-unsound. So the gate is EXACTLY
     the unsound-packing set — it drops every phantom and NOTHING else. *)
  Theorem gate_rejects_iff_unsound :
    forall p, gate_rejects rll p = negb (sound p).
  Proof. intros [s f]. destruct s, f; reflexivity. Qed.

  (* Completeness restated: every token-unsound packing is rejected. *)
  Theorem gate_rejects_every_unsound :
    forall p, sound p = false -> gate_rejects rll p = true.
  Proof.
    intros p H. rewrite gate_rejects_iff_unsound, H. reflexivity.
  Qed.

  (* ═════════════════ T3: never drop a real reading ═════════════════ *)
  Theorem gate_drops_no_sound_packing :
    forall p, sound p = true -> gate_rejects rll p = false.
  Proof.
    intros p H. rewrite gate_rejects_iff_unsound, H. reflexivity.
  Qed.

  (* ═════════════════ T4: operand-led Symbol child preserved ═════════════════ *)
  (* The KEY contrast with a naive "reject any Symbol first child": an operand-led
     rule (e.g. infix `a "+" b`, whose first child legitimately IS a Symbol) is
     NEVER rejected — the `leads_with_literal` guard confines the drop to
     literal-led rules. Without the guard this would over-reject every infix. *)
  Theorem param_led_symchild_preserved :
    gate_rejects rll (mkPacking ParamLed SymChild) = false.
  Proof. reflexivity. Qed.

  (* And ParamLed packings are always sound, so T3 already guarantees they survive
     — this is the positive form for the operand-led-with-Symbol-child case. *)
  Theorem param_led_symchild_sound :
    sound (mkPacking ParamLed SymChild) = true.
  Proof. reflexivity. Qed.

  (* ═════════════════ T5: the count-based wall (formula "J") ═════════════════ *)
  Section CountBasedWall.

    (* A LiteralLed cast `"t" "(" a ")"`. Its leading literal `t` is consumed
       either IN-span (rhocalc `str`, matched within the result span) or
       OUT-OF-span as a `TriggerTerminal` (calc cross-cat `int`, lambda grouping
       `(`). This disposition is a RUNTIME parse property, NOT codegen-derivable. *)
    Inductive LeadDisposition : Type := InSpan | OutOfSpan.

    (* Realize-time slack = (result-symbol span) - Sigma(operand-child spans), counted
       in fixed-token units. A SOUND cast's slack counts its trailing `")"` PLUS
       its leading literal WHEN in-span; an out-of-span leading trigger contributes
       0. The PHANTOM never consumed its leading `t (`, so its slack is the
       trailing `")"` only. (Canonical trigger-cast: one trailing `)`.) *)
    Definition slack_sound (d : LeadDisposition) : nat :=
      match d with
      | InSpan    => 2   (* leading literal IN-span + trailing `")"` *)
      | OutOfSpan => 1   (* leading is an out-of-span trigger; trailing `")"` only *)
      end.
    Definition slack_phantom : nat := 1.   (* trailing `")"` only; leading fabricated *)

    (* `min_terminal_span` rejects a packing iff its slack is strictly below the
       per-rule threshold `T`. *)
    Definition count_rejects (T slack : nat) : bool := Nat.ltb slack T.

    (* For IN-span leading rules a threshold DOES exist (T = 2): it rejects the
       phantom (slack 1 < 2) and keeps the sound parse (slack 2 >/< 2 → kept).
       This is why formula "J" — which counted the leading `(` as in-span — fixed
       rhocalc and calc's IN-span casts. *)
    Theorem count_gate_works_for_inspan :
      count_rejects 2 slack_phantom = true /\ count_rejects 2 (slack_sound InSpan) = false.
    Proof. split; reflexivity. Qed.

    (* THE WALL: for an OUT-OF-span leading rule the sound slack EQUALS the phantom
       slack, so ANY threshold that rejects the phantom ALSO rejects the sound
       parse. Formalized: whenever the count gate rejects the phantom at threshold
       `T`, it likewise rejects the SOUND out-of-span cast at `T`. Hence no sound
       count threshold exists for out-of-span leading rules — the measured
       formula-"J" lambda `App` regression. *)
    Theorem count_gate_wall :
      forall T : nat,
        count_rejects T slack_phantom = true ->
        count_rejects T (slack_sound OutOfSpan) = true.
    Proof.
      intros T H. unfold count_rejects, slack_phantom, slack_sound in *. exact H.
    Qed.

    (* Equivalent negative form: there is NO threshold `T` that both rejects the
       phantom and keeps the sound out-of-span cast. *)
    Theorem count_gate_no_sound_threshold_outofspan :
      ~ (exists T : nat,
            count_rejects T slack_phantom = true
            /\ count_rejects T (slack_sound OutOfSpan) = false).
    Proof.
      intros [T [Hrej Hkeep]].
      pose proof (count_gate_wall T Hrej) as Hrej2.
      rewrite Hrej2 in Hkeep. discriminate.
    Qed.

  End CountBasedWall.

  (* ═════════════════ T6: the structural gate crosses the wall ═════════════════ *)
  Section StructuralCrossesWall.

    (* The first-child kind of a SOUND leading-literal cast packing is `TermChild`
       in BOTH dispositions (the leading literal is realized as `Terminal` when
       in-span and `TriggerTerminal` when out-of-span — both `TermChild`); the
       phantom is `SymChild`. So the STRUCTURAL classification is INDEPENDENT of
       the disposition that defeats the count gate. *)
    Definition sound_cast_packing (_d : LeadDisposition) : Packing :=
      mkPacking LiteralLed TermChild.
    Definition phantom_cast_packing : Packing :=
      mkPacking LiteralLed SymChild.

    (* For BOTH dispositions the structural gate KEEPS the sound cast and REJECTS
       the phantom — the decision does not depend on `d` at all, unlike the count
       gate (T5). This is precisely the wall-crossing property. *)
    Theorem structural_gate_crosses_wall :
      forall d : LeadDisposition,
        gate_rejects rll (sound_cast_packing d) = false
        /\ gate_rejects rll phantom_cast_packing = true.
    Proof. intro d. destruct d; split; reflexivity. Qed.

    (* The sound cast packing is indeed sound and the phantom indeed unsound, in
       both dispositions (ties T6's operands back to the soundness predicate). *)
    Theorem structural_operands_wellclassified :
      forall d : LeadDisposition,
        sound (sound_cast_packing d) = true /\ sound phantom_cast_packing = false.
    Proof. intro d. destruct d; split; reflexivity. Qed.

  End StructuralCrossesWall.

  (* ═════════════════ T7: kill-switch / default identity ═════════════════ *)
  (* With the leads-with-literal oracle ≡ false (the trait default for engines
     with no literal-led rules), the gate rejects NOTHING in every context —
     byte-identical to the pre-fix realize filter. *)
  Theorem default_off_identity :
    forall p, gate_rejects (fun _ => false) p = false.
  Proof. intros [s f]. destruct s, f; reflexivity. Qed.

  (* And `rll` agrees with the grammar fact it models: true exactly on LiteralLed. *)
  Theorem rll_characterization :
    rll LiteralLed = true /\ rll ParamLed = false.
  Proof. split; reflexivity. Qed.

End LeadingLiteralPhantomGate.

(* ═════════════════ Assumption audit — must all print
   "Closed under the global context" ═════════════════ *)
Print Assumptions phantom_is_unsound.
Print Assumptions gate_rejects_iff_unsound.
Print Assumptions gate_rejects_every_unsound.
Print Assumptions gate_drops_no_sound_packing.
Print Assumptions param_led_symchild_preserved.
Print Assumptions param_led_symchild_sound.
Print Assumptions count_gate_works_for_inspan.
Print Assumptions count_gate_wall.
Print Assumptions count_gate_no_sound_threshold_outofspan.
Print Assumptions structural_gate_crosses_wall.
Print Assumptions structural_operands_wellclassified.
Print Assumptions default_off_identity.
Print Assumptions rll_characterization.
