(*
 * InfixRhsMaximalReconnect: zero-admission FV for the ROOT-D infix-operator
 * RHS MAXIMAL-EXTENT reconnection injection
 * (prattail/src/wpda_walker.rs, the InfixLoop Fork handler's FOURTH injection arm
 *  `__under_crosscat_infix_rhs`, plus the helpers
 *  `crosscat_lhs_enclosing_infix_rhs_frame` and
 *  `infix_rhs_frame_accepts_body_category`).
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE DEFECT (trace-evidenced; deterministic; category ordering
 *   Proc=0, InputBind=1, ForRow=2, Name=3):
 *
 *   `Proc::parse("Nil.set(for(){Nil} | a!(Nil), Nil)")` FAILS at the RHS send `!`
 *   ("1:22 found Ident"), while the SAME infix as a standalone term
 *   (`for(){Nil} | a!(Nil)`) SUCCEEDS, and the same method-call with a plain RHS
 *   (`Nil.set(for(){Nil} | Nil, Nil)`) or a send-LHS (`Nil.set(a!(Nil) | Nil,
 *   Nil)`) or a parenthesized infix (`Nil.set((Nil | Nil), Nil)`) all SUCCEED.
 *
 *   Root (trace `rootd_full_trace.log`; tokens Nil0 .1 set2 (3 for4 (5 )6 {7 Nil8
 *   }9 |10 a11 !12 (13 Nil14 )15 ,16 Nil17 )18): the RHS operand of the infix `|`
 *   (`PParInfix . a:Proc, b:Proc |- a "|" b`, rule 43) is dispatched under a
 *   `SymbolKind::Return` marker -> `ReturnFrame{cat_src:0, rule_idx:43}`. The RHS
 *   `a` completes as a Name (cat 3). The Name->Proc SEND extension (`a` ->
 *   `a!(Nil)`) is offered by the InfixLoop `CrossCatLhsScoped{source:3}` cross-cat
 *   -LHS delegate. The maximal `a!(Nil):Proc` (span [11,16]) DOES intern
 *   (`intern success cat=0 rule=4 symbol=81 span=[11,16]`) but its extension
 *   lineage rides the Name frame; only the SHORT `a:Name` (span [11,12]) pops
 *   back to the infix `ReturnFrame` (committed at pos 12: PParInfix children
 *   `[for(){Nil}, a]`). The enclosing `.set` MixfixMarker then sees the
 *   unconsumed `!` at pos 12 and rejects.
 *
 *   STANDALONE works because the infix `ReturnFrame{PParInfix}` is the TOP-most
 *   enclosing frame; the top-level InfixLoop re-fork pops the maximal POutput
 *   directly back and forms the LONG PParInfix [0,12] (the short one loses to
 *   trailing-token). The DECISIVE difference (PRATTAIL_DUMP_EDGESTACK):
 *     standalone edge stack @ reconnect pos:  [CrossCatLhsScoped{3} | ReturnFrame{43}]
 *     method-arg edge stack @ reconnect pos:  [CrossCatLhsScoped{3} | ReturnFrame{43} | MixfixMarker{.set}]
 *   the intervening `.set` MixfixMarker below the infix frame breaks the natural
 *   pop-back, so NO reading unwinds the maximal RHS to the infix `ReturnFrame`.
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE FIX (mirrors the PROVEN Root-B collection-element reconnection
 *   `__under_crosscat_collection_element` and the GROUP-A binder-slot-unwind, which
 *   do the SAME reconnection for `CollectionElement` / `PrefixRuleEntry{ip>0}` /
 *   `MixfixMarker` frames): a FOURTH injection arm fires when the InfixLoop Fork
 *   sits at a CategoryEntry frontier whose IMMEDIATE incoming edge is a cross-cat
 *   -LHS re-entry (`CrossCatLhsScoped`/`Reentry`) AND the nearest enclosing frame
 *   reachable THROUGH cross-cat-LHS edges is an infix-RHS `ReturnFrame{cat, rule}`
 *   AND the completed body (SPPF top) is ALREADY in a category that infix rule's
 *   operand slot accepts. It injects one `Advance -> Unwinding` branch so the
 *   MAXIMAL RHS returns to the infix `ReturnFrame` (whose pop then fires the LONG
 *   infix reading). GLR no-loss: the short-RHS reading survives.
 *
 *   `crosscat_lhs_enclosing_infix_rhs_frame` walks transparent through cross-cat
 *   -LHS edges, RETURNS on the first `ReturnFrame`, STOPS (None) on the first
 *   scope-resetting frame (`GroupingMarker` / `PrefixRuleEntry{ip>0}` /
 *   `MixfixMarker` / `CollectionElement`). This is why an infix RHS NESTED inside
 *   a fresh arg-slot / group / collection element does not wrongly reconnect to an
 *   OUTER infix operator.
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THIS MODEL abstracts the injection decision `inject : InfixCtx -> bool` and the
 * enclosing-frame walk `walk : list Edge -> option Frame`. The theorems establish:
 *   (1) inject fires IFF the exact trigger (cross-cat-LHS immediate edge ∧ walk
 *       finds an infix-RHS ReturnFrame ∧ body cat accepted) — no heuristic;
 *   (2) SHORT (pre-extension) body (cat ∉ rule operands) ⇒ no inject (the bare
 *       `a:Name` case; the fix fires ONLY at maximal extent);
 *   (3) a NON-cross-cat immediate edge ⇒ no inject (byte-identity for the
 *       kill-switch-OFF / same-cat / standalone-top-level paths);
 *   (4) the walk STOPS at a scope-resetting frame reached before a ReturnFrame
 *       (the nesting-precedence soundness — no reconnect across a re-scoping frame),
 *       for EACH of Grouping / RuleSlot / CollElem;
 *   (5) no-loss WITNESS: injecting ADDS the Unwinding reading to a branch set that
 *       already contains the short/operator readings (the short RHS survives);
 *   (6) kill-switch OFF ⇒ never inject (byte-identical control);
 *   (7) the REPAIR witness: at maximal extent (body already in an operand cat) the
 *       injection fires (offering the reconnection) — the ROOT-D `a!(Nil):Proc`
 *       under `PParInfix` (RHS operand cat Proc) case;
 *   (8) DISJOINTNESS from the collection-element arm: the fix ordering makes the
 *       infix arm inert whenever the walk would stop at a CollElem (the two arms
 *       never both claim the same frontier).
 *
 * THEOREMS (all admission-free; audited by `Print Assumptions`, which must
 *   report "Closed under the global context").
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.

Section InfixRhsMaximalReconnect.

  (* ── Edge kinds relevant to the enclosing-frame walk. ─────────────────────
     Mirrors `crate::gss::EdgeKind` cases the walk inspects. An `InfixRhs r`
     carries the infix rule id `r` (from the `ReturnFrame{cat_src, rule_idx}`
     the RHS operand was dispatched under; `cat` is folded into the accept
     predicate). `Grouping` / `RuleSlot` / `CollElem` are the scope-resetting
     frames (GroupingMarker / PrefixRuleEntry{ip>0} / MixfixMarker /
     CollectionElement). `Transparent` is a cross-cat-LHS re-entry the walk
     passes THROUGH. *)
  Inductive Edge : Type :=
    | InfixRhs   : nat -> Edge     (* ReturnFrame, infix rule id = arg        *)
    | Grouping   : Edge            (* GroupingMarker (scope reset)            *)
    | RuleSlot   : Edge            (* PrefixRuleEntry{ip>0} / MixfixMarker     *)
    | CollElem   : Edge            (* CollectionElement (scope reset)         *)
    | Transparent : Edge.          (* cross-cat-LHS reentry (passed through)  *)

  (* The enclosing-frame walk result. *)
  Inductive Frame : Type :=
    | FoundInfix : nat -> Frame    (* an infix-RHS ReturnFrame, rule id       *)
    | NoFrame    : Frame.          (* walk stopped / ran out                  *)

  (* ── `crosscat_lhs_enclosing_infix_rhs_frame` (abstract). ────────────────
     Walk the edge stack top-down: return on the first InfixRhs; stop (NoFrame)
     on the first Grouping/RuleSlot/CollElem; pass through Transparent. Mirrors
     the Rust `match` stop-set exactly. *)
  Fixpoint walk (es : list Edge) : Frame :=
    match es with
    | [] => NoFrame
    | InfixRhs r :: _ => FoundInfix r
    | Grouping   :: _ => NoFrame
    | RuleSlot   :: _ => NoFrame
    | CollElem   :: _ => NoFrame
    | Transparent :: rest => walk rest
    end.

  (* Is the IMMEDIATE (top) edge a cross-cat-LHS re-entry? In the walker this is
     `matches!(__immediate_edge, CrossCatLhsScoped | CrossCatLhsReentry)`. Here a
     cross-cat-LHS immediate edge is modeled as a leading `Transparent`. *)
  Definition immediate_is_crosscat (es : list Edge) : bool :=
    match es with
    | Transparent :: _ => true
    | _ => false
    end.

  (* ── `infix_rhs_frame_accepts_body_category` (abstract). ─────────────────
     The infix rule `r` accepts a body of category `b` iff `b` is one of its
     operand categories OR a declared single-hop coercion reaches one. Modeled
     abstractly as `accepts_rhs r b` (the Rust delegates to
     `binder_slot_accepts_body_category`, a membership check over
     `expected_input_cats` plus single-hop coercion — a pure boolean of (r,b)). *)
  Variable accepts_rhs : nat -> nat -> bool.

  (* ── The injection decision (the arm). ───────────────────────────────────
     `enabled` is the kill-switch (const && !env && !(prior arms fired)). Injects
     iff: enabled ∧ immediate edge is cross-cat-LHS ∧ walk finds InfixRhs r ∧
     the body category b is accepted by r's operand slots. *)
  Definition inject (enabled : bool) (es : list Edge) (b : nat) : bool :=
    if enabled then
      if immediate_is_crosscat es then
        match walk es with
        | FoundInfix r => accepts_rhs r b
        | NoFrame => false
        end
      else false
    else false.

  (* ══════════════ inject_iff_trigger ══════════════
     (1) The exact trigger characterization: inject fires IFF enabled AND the
     immediate edge is cross-cat-LHS AND the walk finds an InfixRhs whose rule
     accepts the body category. No heuristic, no hidden condition. *)
  Theorem inject_iff_trigger :
    forall enabled es b,
      inject enabled es b = true
      <-> (enabled = true
           /\ immediate_is_crosscat es = true
           /\ exists r, walk es = FoundInfix r /\ accepts_rhs r b = true).
  Proof.
    intros enabled es b. unfold inject. split.
    - intro H. destruct enabled; [| discriminate].
      destruct (immediate_is_crosscat es) eqn:Him; [| discriminate].
      destruct (walk es) eqn:Hw; [| discriminate].
      split; [reflexivity | split; [reflexivity | ]]. exists n. split; [reflexivity | exact H].
    - intros [He [Him [r [Hw Hacc]]]].
      rewrite He, Him, Hw. exact Hacc.
  Qed.

  (* ══════════════ short_body_no_inject ══════════════
     (2) A SHORT (pre-extension) body whose category is NOT accepted by the infix
     rule's operand slots does NOT trigger the injection — the bare `a:Name`
     (cat 3) case for `PParInfix` (operand cats Proc=0): accepts_rhs 43 3 = false,
     so no inject. The fix fires ONLY at maximal extent (body already in an
     operand cat). *)
  Theorem short_body_no_inject :
    forall enabled es r b,
      walk es = FoundInfix r ->
      accepts_rhs r b = false ->
      inject enabled es b = false.
  Proof.
    intros enabled es r b Hw Hacc. unfold inject.
    destruct enabled; [| reflexivity].
    destruct (immediate_is_crosscat es); [| reflexivity].
    rewrite Hw, Hacc. reflexivity.
  Qed.

  (* ══════════════ non_crosscat_immediate_no_inject ══════════════
     (3) When the immediate edge is NOT a cross-cat-LHS re-entry (any other
     frontier: a direct rule return, a same-category operand, a rule slot, …), the
     injection never fires — byte-identity for every non-cross-cat path (the
     same-cat infix operands & the standalone top-level natural pop-back). *)
  Theorem non_crosscat_immediate_no_inject :
    forall enabled es b,
      immediate_is_crosscat es = false ->
      inject enabled es b = false.
  Proof.
    intros enabled es b Him. unfold inject.
    destruct enabled; [| reflexivity]. rewrite Him. reflexivity.
  Qed.

  (* ══════════════ scope_reset_stops_walk ══════════════
     (4a) NESTING PRECEDENCE: a scope-resetting frame (Grouping / RuleSlot /
     CollElem) reached BEFORE any InfixRhs stops the walk — the operand belongs to
     that inner scope, not the outer infix operator, so no reconnection. Mirrors
     the stop-set of the collection / binder-resume walks. *)
  Theorem grouping_stops_walk :
    forall rest, walk (Grouping :: rest) = NoFrame.
  Proof. intro rest. reflexivity. Qed.

  Theorem ruleslot_stops_walk :
    forall rest, walk (RuleSlot :: rest) = NoFrame.
  Proof. intro rest. reflexivity. Qed.

  Theorem collelem_stops_walk :
    forall rest, walk (CollElem :: rest) = NoFrame.
  Proof. intro rest. reflexivity. Qed.

  (* ══════════════ inner_scope_no_reconnect ══════════════
     (4b) Consequence: if a scope-resetting frame precedes the (would-be)
     InfixRhs, the injection does NOT fire — an infix RHS NESTED inside a fresh
     arg-slot / group / collection element cannot wrongly reconnect the operand to
     an OUTER infix operator. Shown for EACH scope-resetting frame. *)
  Theorem inner_scope_no_reconnect_grouping :
    forall enabled rest b,
      inject enabled (Transparent :: Grouping :: rest) b = false.
  Proof.
    intros enabled rest b. unfold inject.
    destruct enabled; [| reflexivity]. simpl. reflexivity.
  Qed.

  Theorem inner_scope_no_reconnect_ruleslot :
    forall enabled rest b,
      inject enabled (Transparent :: RuleSlot :: rest) b = false.
  Proof.
    intros enabled rest b. unfold inject.
    destruct enabled; [| reflexivity]. simpl. reflexivity.
  Qed.

  Theorem inner_scope_no_reconnect_collelem :
    forall enabled rest b,
      inject enabled (Transparent :: CollElem :: rest) b = false.
  Proof.
    intros enabled rest b. unfold inject.
    destruct enabled; [| reflexivity]. simpl. reflexivity.
  Qed.

  (* ── Branch set (GLR no-loss). ────────────────────────────────────────────
     A branch set is a list of "readings"; the SHORT/operator readings are
     already present. The injection APPENDS one Unwinding reading iff it fires;
     the `already_has_unwind` guard is modeled by only appending when absent. *)
  Inductive Reading : Type :=
    | RShort          (* the short RHS / operator continuation                *)
    | RUnwind.        (* the injected "RHS complete; return it" reading       *)

  Definition reading_eqb (x y : Reading) : bool :=
    match x, y with
    | RShort, RShort => true
    | RUnwind, RUnwind => true
    | _, _ => false
    end.

  Definition has_unwind (bs : list Reading) : bool :=
    existsb (reading_eqb RUnwind) bs.

  Definition apply_inject
    (enabled : bool) (es : list Edge) (b : nat) (bs : list Reading) : list Reading :=
    if inject enabled es b && negb (has_unwind bs)
    then bs ++ [RUnwind]
    else bs.

  (* ══════════════ inject_adds_reading_no_loss ══════════════
     (5) NO-LOSS: every reading present before the injection is still present
     after — the injection only APPENDS RUnwind, never removes the short reading.
     (GLR-safe: the short-RHS reading survives alongside the maximal one.) *)
  Theorem inject_adds_reading_no_loss :
    forall enabled es b bs r,
      In r bs -> In r (apply_inject enabled es b bs).
  Proof.
    intros enabled es b bs r Hin. unfold apply_inject.
    destruct (inject enabled es b && negb (has_unwind bs)).
    - apply in_or_app. left. exact Hin.
    - exact Hin.
  Qed.

  (* ══════════════ inject_present_when_fires ══════════════
     (5b) When the injection fires (and no prior Unwind), the RUnwind reading IS
     added — the maximal-extent reconnection reading is genuinely offered. *)
  Theorem inject_present_when_fires :
    forall enabled es b bs,
      inject enabled es b = true ->
      has_unwind bs = false ->
      In RUnwind (apply_inject enabled es b bs).
  Proof.
    intros enabled es b bs Hinj Hno. unfold apply_inject.
    rewrite Hinj, Hno. simpl. apply in_or_app. right. left. reflexivity.
  Qed.

  (* ══════════════ killswitch_off_no_inject ══════════════
     (6) KILL-SWITCH OFF (enabled = false) ⇒ the injection NEVER fires, for ANY
     edge stack / body — byte-identical control (PRATTAIL_NO_INFIX_RHS_RECONNECT
     / the const gate = false). *)
  Theorem killswitch_off_no_inject :
    forall es b, inject false es b = false.
  Proof. intros es b. reflexivity. Qed.

  Theorem killswitch_off_apply_noop :
    forall es b bs, apply_inject false es b bs = bs.
  Proof.
    intros es b bs. unfold apply_inject.
    rewrite killswitch_off_no_inject. reflexivity.
  Qed.

  (* ══════════════ maximal_extent_fires_when_accepted ══════════════
     (7) The REPAIR witness: at maximal extent — cross-cat-LHS immediate edge,
     enclosing InfixRhs with rule r, body already in an accepted operand cat b —
     the injection fires (offering the reconnection). This is the ROOT-D pos-16
     `a!(Nil):Proc` (cat 0) under `PParInfix` (rule 43, RHS operand cat Proc)
     case. *)
  Theorem maximal_extent_fires_when_accepted :
    forall r b rest,
      accepts_rhs r b = true ->
      inject true (Transparent :: InfixRhs r :: rest) b = true.
  Proof.
    intros r b rest Hacc. unfold inject. simpl. exact Hacc.
  Qed.

  (* ══════════════ arm_ordering_disjoint_from_collection ══════════════
     (8) DISJOINTNESS: the Rust fix orders the infix arm AFTER the collection arm
     (`__under_crosscat_infix_rhs` guards on `!__under_crosscat_collection_element`),
     and the walk STOPS at the first CollElem. Model consequence: whenever the
     walk would reach a CollElem (i.e. a collection frame is the nearest enclosing
     scope), the infix arm does NOT fire — the two reconnection arms never both
     claim the same frontier. (`walk es = NoFrame` at a CollElem-first stack ⇒
     inject = false; combined with (4b) collelem case.) *)
  Theorem infix_arm_inert_at_collection_frontier :
    forall enabled es b,
      walk es = NoFrame ->
      inject enabled es b = false.
  Proof.
    intros enabled es b Hw. unfold inject.
    destruct enabled; [| reflexivity].
    destruct (immediate_is_crosscat es); [| reflexivity].
    rewrite Hw. reflexivity.
  Qed.

  (* ══════════════ walk_transparent_transparent ══════════════
     (9) The walk is TRANSPARENT through cross-cat-LHS re-entry edges: an infix
     `ReturnFrame` reachable only through a chain of Transparent edges IS found
     (the multi-hop cross-cat-LHS lineage the maximal RHS runs under). This is the
     look-through the reconnection requires; combined with (4) it fires only when
     NO re-scoping frame intervenes. *)
  Theorem walk_transparent_finds_infix :
    forall n r rest,
      walk (repeat Transparent n ++ InfixRhs r :: rest) = FoundInfix r.
  Proof.
    intros n r rest. induction n as [| n IH]; simpl.
    - reflexivity.
    - exact IH.
  Qed.

End InfixRhsMaximalReconnect.

(* ══════════════════════════════════════════════════════════════════════════
   Admission audit. Every theorem above must be closed under the global context
   (no Admitted, no Axiom, no Variable-as-axiom leakage — the Section discharges
   `accepts_rhs` as a universally-quantified hypothesis, NOT an axiom). *)
Print Assumptions inject_iff_trigger.
Print Assumptions short_body_no_inject.
Print Assumptions non_crosscat_immediate_no_inject.
Print Assumptions grouping_stops_walk.
Print Assumptions ruleslot_stops_walk.
Print Assumptions collelem_stops_walk.
Print Assumptions inner_scope_no_reconnect_grouping.
Print Assumptions inner_scope_no_reconnect_ruleslot.
Print Assumptions inner_scope_no_reconnect_collelem.
Print Assumptions inject_adds_reading_no_loss.
Print Assumptions inject_present_when_fires.
Print Assumptions killswitch_off_no_inject.
Print Assumptions killswitch_off_apply_noop.
Print Assumptions maximal_extent_fires_when_accepted.
Print Assumptions infix_arm_inert_at_collection_frontier.
Print Assumptions walk_transparent_finds_infix.
