(*
 * TriggerOwnershipLeadGate: zero-admission FV for the leading-structural-trigger
 * gate on the `emit_fire_action` walk-back `pos_match` fallback
 * (prattail/src/wpda_walker.rs, the TriggerTerminal drain predicate; the
 * grammar-derived per-rule predicate is emitted by
 * macros/src/gen/runtime/wpda_codegen/collection.rs
 * `emit_rule_has_leading_structural_trigger_lookup` and exposed via
 * `WpdaEngine::rule_has_leading_structural_trigger`).
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE DEFECT (trace-evidenced; deterministic; rhocalc category ordering
 *   Proc=0, InputBind=1, ForRow=2, Name=3):
 *
 *   `Proc::parse("@Nil!!(\"dpyl\", error <= Map(), fraction(a, Map()))")` — and
 *   the name/proc `display_parse_roundtrip` proptests that generate a nested
 *   `MUnion(PPersistOutput2Plus(NQuoteNil, …), …)` — elect a PHANTOM parse whose
 *   channel is the Name VARIABLE `NVar("Nil")` instead of the intended
 *   `NQuoteNil` (quote of the null process).  `Nil` is a reserved keyword that
 *   ALSO lexes as an identifier (`Fixed("Nil") | Ident`, per
 *   LexForkKeywordReservation.v).  The phantom's Display drops the leading `@`
 *   and renders the send channel as the bare keyword `Nil` — `Nil!!(…)` — which
 *   the grammar REJECTS (`Nil` is `PZero`, not a name variable).  So the parser
 *   returns an AST it cannot itself re-parse: `parse(display t)` FAILS for a `t`
 *   the parser produced — a SOUNDNESS violation of canonical-idempotence.
 *
 *   Root (trace `PPersistOutput2Plus` packing children):
 *     packing_correct = [ NQuoteNil@[0,2] ; a ; bs ]           (intended)
 *     packing_phantom = [ Trigger("@", owner=(Proc,POutputQuoted))@0 ;
 *                         NVar("Nil")@[1,2] ; a ; bs ]         (phantom)
 *   The `@` structural trigger is OWNED by an `@`-prefix send rule
 *   (POutputQuoted `@ n ! ( q )`), but it is swept into a
 *   PPersistOutput2Plus reduction whose surface pattern is
 *   `n "!!" "(" a "," bs ")"` — an OPERAND-LEADING rule with NO leading
 *   trigger of its own.  The walk-back drain
 *   (`emit_fire_action`, wpda_walker.rs) claimed the `@` trigger via the
 *   `pos_match` fallback:
 *     owner_match := (owner_cat, owner_rule) = (fire_cat, fire_rule)
 *     pos_match   := trigger_pos = frame_start_pos
 *     claim       := owner_match \/ pos_match
 *   For the phantom, owner_match is FALSE (owner = POutputQuoted, firing rule =
 *   PPersistOutput2Plus) but the PPersistOutput2Plus frame HAPPENS to start at
 *   the `@` position (reached via the `@`->Name cross-cat delegation), so
 *   pos_match is TRUE and the foreign `@` is stolen.  The `pos_match` fallback
 *   was introduced ONLY to repair an AMBIGUOUSLY-OWNED-BUT-CORRECTLY-POSITIONED
 *   trigger of a rule that GENUINELY begins with a trigger (the `@{map}` binder
 *   case: `@ pat <- n` vs `@ p`); its docstring CLAIMED it is "a no-op for
 *   non-prefix rules (no trigger at the frame start)".  That claim is FALSE for
 *   an operand-leading rule whose frame starts on a foreign trigger.
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE FIX (this spec):
 *   Gate the `pos_match` fallback on the firing rule GENUINELY having a leading
 *   structural trigger — its surface pattern's first `SyntaxExpr` is a
 *   `Literal` (`rule_has_leading_structural_trigger fire_cat fire_rule`).  The
 *   claim predicate becomes
 *     claim' := owner_match \/ (pos_match /\ has_lead_trigger)
 *   An operand-leading rule (`has_lead_trigger = false`, e.g.
 *   PPersistOutput2Plus) can no longer steal a foreign trigger by position; a
 *   genuine prefix rule (`has_lead_trigger = true`, e.g. the `@{map}` binder,
 *   NQuoteShort, the `int(…)` casts, Neg) keeps the fallback verbatim.
 *   Grammar-derived (first SyntaxExpr is a Literal); no per-rule / per-language
 *   hardcode.  The kill-switch env `PRATTAIL_NO_TRIGGER_LEAD_GATE` forces
 *   `has_lead_trigger := true` for every rule, restoring the prior
 *   unconditional `owner \/ pos` (labeled scientific control).
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE MODEL: a TriggerTerminal is abstracted by whether its owner matches the
 * firing rule (`owner_match : bool`) and whether it sits at the firing frame's
 * start (`pos_match : bool`).  The firing rule is abstracted by whether it
 * begins with a structural trigger (`has_lead_trigger : bool`).  `claim_old`
 * and `claim_new` are the two drain predicates.  The theorems establish:
 *   (1) the fix is a REFINEMENT of the old predicate (never claims MORE):
 *         claim_new ⇒ claim_old;
 *   (2) owner-matched triggers are UNAFFECTED (no-loss for a rule's OWN
 *         trigger): owner_match ⇒ (claim_new = claim_old = true);
 *   (3) a genuine leading-trigger rule is byte-identical (the `@{map}` repair
 *         survives): has_lead_trigger ⇒ (claim_new = claim_old);
 *   (4) the PHANTOM is eliminated: an operand-leading rule
 *         (has_lead_trigger = false) with a FOREIGN trigger
 *         (owner_match = false) at its frame start (pos_match = true) is
 *         claimed by the OLD predicate but NOT the NEW — the exact phantom
 *         configuration;
 *   (5) the kill-switch restores the old predicate exactly;
 *   (6) DOMINANCE: whenever the two predicates differ, the configuration is
 *         precisely the phantom (foreign, positioned, operand-leading) — the
 *         change is surgical, never a heuristic.
 *
 * `Print Assumptions` on every theorem must report
 * "Closed under the global context" (zero admission, Rocq 9.1).
 *)

Set Implicit Arguments.

(* A drain decision is a function of three booleans:
   - owner_match:      the trigger's owner = the firing rule
   - pos_match:        the trigger sits at the firing frame's start
   - has_lead_trigger: the firing rule genuinely begins with a structural
                       trigger (its first SyntaxExpr is a Literal). *)

Definition claim_old (owner_match pos_match : bool) : bool :=
  orb owner_match pos_match.

Definition claim_new (owner_match pos_match has_lead_trigger : bool) : bool :=
  orb owner_match (andb pos_match has_lead_trigger).

(* The kill-switch forces has_lead_trigger := true for every rule. *)
Definition claim_new_killswitch (owner_match pos_match : bool) : bool :=
  claim_new owner_match pos_match true.

(* ─── (1) REFINEMENT: the new predicate never claims MORE than the old. ─── *)
Theorem claim_new_refines_old :
  forall om pm hlt : bool,
    claim_new om pm hlt = true -> claim_old om pm = true.
Proof.
  intros om pm hlt H.
  unfold claim_new, claim_old in *.
  destruct om; destruct pm; destruct hlt; simpl in *; try reflexivity; try discriminate.
Qed.

(* ─── (2) OWNER-MATCH NO-LOSS: a rule's OWN trigger is always claimed by
       both predicates (owner_match ⇒ both true). ─── *)
Theorem owner_match_unaffected :
  forall om pm hlt : bool,
    om = true ->
    claim_new om pm hlt = true /\ claim_old om pm = true.
Proof.
  intros om pm hlt Hom.
  subst om.
  unfold claim_new, claim_old.
  simpl.
  split; reflexivity.
Qed.

(* ─── (3) GENUINE-PREFIX BYTE-IDENTITY: a rule that genuinely leads with a
       trigger behaves EXACTLY as before (the `@{map}` binder repair survives). ─── *)
Theorem lead_trigger_byte_identical :
  forall om pm : bool,
    claim_new om pm true = claim_old om pm.
Proof.
  intros om pm.
  unfold claim_new, claim_old.
  destruct om; destruct pm; simpl; reflexivity.
Qed.

(* ─── (4) PHANTOM ELIMINATED: the exact phantom configuration — a FOREIGN
       trigger (owner_match=false) at the frame START (pos_match=true) of an
       OPERAND-LEADING rule (has_lead_trigger=false) — is claimed by the OLD
       predicate but REJECTED by the NEW. ─── *)
Theorem phantom_config_dropped :
  claim_old false true = true /\ claim_new false true false = false.
Proof.
  unfold claim_old, claim_new.
  simpl.
  split; reflexivity.
Qed.

(* The phantom is the SOLE newly-rejected configuration among the drain inputs:
   claim_old = true but claim_new = false forces (false, true, false). *)
Theorem only_phantom_newly_rejected :
  forall om pm hlt : bool,
    claim_old om pm = true ->
    claim_new om pm hlt = false ->
    om = false /\ pm = true /\ hlt = false.
Proof.
  intros om pm hlt Hold Hnew.
  unfold claim_old, claim_new in *.
  destruct om; destruct pm; destruct hlt; simpl in *;
    try discriminate; repeat split; reflexivity.
Qed.

(* ─── (5) KILL-SWITCH restores the old predicate exactly. ─── *)
Theorem killswitch_restores_old :
  forall om pm : bool,
    claim_new_killswitch om pm = claim_old om pm.
Proof.
  intros om pm.
  unfold claim_new_killswitch, claim_new, claim_old.
  destruct om; destruct pm; simpl; reflexivity.
Qed.

(* ─── (6) DOMINANCE / no-heuristic: the two predicates DIFFER on an input iff
       that input is precisely the phantom (foreign, positioned,
       operand-leading). The change is surgical. ─── *)
Theorem difference_is_exactly_phantom :
  forall om pm hlt : bool,
    (claim_old om pm <> claim_new om pm hlt) <->
    (om = false /\ pm = true /\ hlt = false).
Proof.
  intros om pm hlt.
  unfold claim_old, claim_new.
  split.
  - intro Hne.
    destruct om; destruct pm; destruct hlt; simpl in *;
      try (exfalso; apply Hne; reflexivity);
      repeat split; reflexivity.
  - intros [Hom [Hpm Hhlt]].
    subst.
    simpl.
    discriminate.
Qed.

(* Corollary: whenever the two predicates agree, the drain behaviour is
   unchanged — so every non-phantom parse is byte-identical. *)
Theorem agreement_off_phantom :
  forall om pm hlt : bool,
    ~ (om = false /\ pm = true /\ hlt = false) ->
    claim_old om pm = claim_new om pm hlt.
Proof.
  intros om pm hlt Hnp.
  unfold claim_old, claim_new.
  destruct om; destruct pm; destruct hlt; simpl;
    try reflexivity;
    exfalso; apply Hnp; repeat split; reflexivity.
Qed.

(* ─── Assumption audit ───────────────────────────────────────────────── *)
Print Assumptions claim_new_refines_old.
Print Assumptions owner_match_unaffected.
Print Assumptions lead_trigger_byte_identical.
Print Assumptions phantom_config_dropped.
Print Assumptions only_phantom_newly_rejected.
Print Assumptions killswitch_restores_old.
Print Assumptions difference_is_exactly_phantom.
Print Assumptions agreement_off_phantom.
