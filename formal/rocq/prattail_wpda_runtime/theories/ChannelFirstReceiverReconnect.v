(*
 * ChannelFirstReceiverReconnect: zero-admission FV for the C3 / ROOT-PERSIST-`<=`
 * CHANNEL-FIRST-RECEIVER operator-shadow reconnection injection
 * (prattail/src/wpda_walker.rs, the InfixLoop Fork handler's FIFTH injection arm
 *  `__under_crosscat_channel_first_receiver`, plus the helpers
 *  `crosscat_lhs_enclosing_channel_first_receiver_frame`,
 *  `channel_first_receiver_frame_accepts_body_category`, and
 *  `channel_first_receiver_operator_is_shadowed`).
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE DEFECT (trace-evidenced; deterministic; category ordering
 *   Proc=0, InputBind=1, ForRow=2, Name=3):
 *
 *   `InputBind::parse("@(Map()) <= n")` FAILS ("1:2 found Fixed(\"(\")"), while the
 *   `<-` twin `@(Map()) <- n` SUCCEEDS (-> InputBindQuoted), and the simple-channel
 *   `<=` binds `@a <= n` / `@(a) <= n` / `@(Nil) <= n` SUCCEED
 *   (-> InputBindQuotedPersistent, handled by the four EXISTING reconnection arms).
 *   Likewise `@(error.keys()) <= n`, `@( *a) <= n` [deref; star spaced to avoid a
 *   nested Rocq comment], and the compound `@(Map() < @Nil!()) <= a` FAIL at
 *   baseline.
 *
 *   Root (trace `c3_le_trace.log` + edge-stack dump `c3_edgestack_map.log`; tokens
 *   @0 (1 Map2 (3 )4 )5 <=6 n7): the `<=` persistent-bind receiver rule
 *   `InputBindQuotedPersistent . pat:Proc, n:Name |- "@" pat "<=" n` (cat 1, rule 6)
 *   reaches its OPERATOR slot (`PrefixRuleEntry{cat_src:1, rule_idx:6, item_pos:2}`,
 *   the `<=` literal) after the `pat` channel `(Map())` completes. Because `Map()`
 *   completes via a CROSS-CAT PROJECTION cascade, the grouping-close installs a
 *   `CategoryEntryContinuation{min_bp:0}` operand continuation. At the `<=` position
 *   (pos 6) the InfixLoop Fork sits at a CategoryEntry frontier whose edge stack is
 *   EXACTLY `[CategoryEntryContinuation | PrefixRuleEntry{1,6,ip2}]` with the SPPF
 *   top ALREADY the completed `pat` (cat 0, Proc). The continuation offers `pat` to
 *   the shadowing Proc-infix rule `<=` (LtEq, rule 64) — which greedily consumes
 *   `<=` — and the receiver frame never advances past its operator literal. At EOF
 *   its guard dies (`GUARD-DIE-peek expected="<=" peek=""`, the `<=` was stolen).
 *
 *   The `<-` twin works because `<-` is NOT a Proc infix: no shadowing continuation
 *   forms, and the DIRECT binder-resume arms (immediate edge = `PrefixRuleEntry`
 *   / cross-cat-LHS) already reconnect it. The DECISIVE difference: the four
 *   existing arms fire on a cross-cat-LHS OR direct `PrefixRuleEntry{ip>0}`
 *   immediate edge and their walk STOPS on `CategoryEntryContinuation`; the `<=`
 *   case has a `CategoryEntryContinuation` immediate edge, so NONE of them fire and
 *   the shadowed receiver frame one hop below it is unreachable to them.
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE FIX (mirrors the PROVEN Root-B collection-element / ROOT-D infix-RHS /
 *   GROUP-A binder-slot-unwind reconnections, which do the SAME reconnection for
 *   `CollectionElement` / `ReturnFrame` / `PrefixRuleEntry{ip>0}` frames): a FIFTH
 *   injection arm fires when the InfixLoop Fork sits at a CategoryEntry frontier
 *   whose IMMEDIATE incoming edge is a `CategoryEntryContinuation` AND the nearest
 *   enclosing frame reachable THROUGH the continuation (+ cross-cat-LHS re-entries
 *   + the pass-through shadowing Proc-infix `ReturnFrame`) is a channel-first
 *   RECEIVER rule's mid-rule OPERATOR slot `PrefixRuleEntry{ip>0}` AND the completed
 *   body (SPPF top) fills one of that rule's operand slots AND — the KEY gate — the
 *   lookahead operator is SHADOWED by the body's category (the body category
 *   recognizes it as one of ITS OWN infix/postfix/mixfix operators, e.g. Proc
 *   recognizes `<=`). It injects one `Advance -> Unwinding` branch so the completed
 *   `pat` unwinds back to the receiver frame's OPERATOR slot (whose pop then
 *   re-consumes the shadowed operator at the operator position via
 *   `GuardedConsumeAndReplace`, advancing the receiver past `<=` to push the
 *   `n:Name` slot -> InputBindQuotedPersistent). GLR no-loss: the operator/short
 *   readings survive.
 *
 *   `crosscat_lhs_enclosing_channel_first_receiver_frame` walks transparent through
 *   `CategoryEntryContinuation` (the ONLY difference from the four existing
 *   walkers, which stop on it) + cross-cat-LHS edges + pass-through `ReturnFrame`,
 *   RETURNS on the first `PrefixRuleEntry{ip>0}` (the receiver operator slot),
 *   STOPS (None) on the first scope-resetting frame (`GroupingMarker` /
 *   `MixfixMarker` / `CollectionElement` / `PrefixRuleEntry{ip==0}`). This is why
 *   the inner `<=` of a genuine comparison `@(Err <= Map()) <- n` — under a
 *   `GroupingMarker` — does NOT reconnect (the walk stops), and a receiver operator
 *   slot NESTED inside a fresh arg-slot / group / collection element does not
 *   wrongly reconnect to an OUTER receiver.
 *
 *   The `operator_is_shadowed` gate (from `category_recognizes_operator`) is the
 *   extra predicate that makes the arm fire ONLY when the operator is genuinely
 *   shadowed by the body category (`<=` for Proc): for the `<-`/`!?` twins it is
 *   FALSE (those are not Proc operators), so the arm is INERT and the DASH-twin
 *   column is byte-identical.
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THIS MODEL abstracts the injection decision `inject : Ctx -> bool` and the
 * enclosing-frame walk `walk : list Edge -> option Frame`. The theorems establish:
 *   (1)  inject fires IFF the exact trigger (continuation immediate edge ∧ walk
 *        finds a receiver `PrefixRuleEntry{ip>0}` ∧ body cat accepted ∧ operator
 *        shadowed) — no heuristic;
 *   (2)  `only_fires_when_operator_shadowed` (RT-3/6): if the operator is NOT
 *        shadowed by the body category, no inject — the `<-`/`!?` twins are inert;
 *   (2b) `dash_twin_inert`: the concrete DASH witness (shadowed=false ⇒ no inject);
 *   (3)  `comparison_preserved_when_no_receiver_frame` (RT-2): when the walk finds
 *        NO receiver frame (a genuine top-level / in-args comparison with no
 *        enclosing `@`-receiver), no inject — the comparison reading is preserved;
 *   (4)  `non_continuation_immediate_no_inject`: a non-`CategoryEntryContinuation`
 *        immediate edge ⇒ no inject (byte-identity for the four existing arms'
 *        frontiers and every other path);
 *   (5)  `categoryentrycontinuation_walk_transparent`: the walk looks THROUGH the
 *        continuation (and multi-hop transparent lineages) to the receiver — the
 *        exact look-through the four existing walkers lack;
 *   (6)  scope-reset stops (Grouping / RuleSlot=Mixfix / CollElem /
 *        PrefixRuleEntry{ip==0}) — the nesting-precedence soundness, EACH shown,
 *        plus the `inner_scope_no_reconnect_*` consequences;
 *   (7)  `inject_adds_reading_no_loss` + `inject_present_when_fires`: no-loss GLR
 *        witness (the operator/short reading survives; the reconnection reading is
 *        offered);
 *   (8)  `pop_via_own_edge_sound` / `injected_body_is_channel_not_comparand`
 *        (RT-4): the injected Unwind pops the OWN receiver `PrefixRuleEntry` edge
 *        and the unwound symbol is the completed channel `pat` (the SPPF top the
 *        Fork already holds), NOT the comparand — the pass-through `ReturnFrame`
 *        only PASSES, the walk returns via the receiver edge BELOW it;
 *   (9)  `killswitch_off_noop`: kill-switch OFF ⇒ never inject (byte-identical);
 *   (10) `composes_with_reconnection_family` / `disjoint_from_reconnection_family`
 *        (RT-5): the fix ordering makes this arm inert whenever a prior arm fired
 *        or the immediate edge is cross-cat-LHS (the four existing arms' locus) —
 *        the five arms never both claim the same frontier;
 *   (11) `maximal_extent_fires_when_accepted_and_shadowed`: the REPAIR witness —
 *        continuation immediate edge, receiver `PrefixRuleEntry{ip>0}`, body in an
 *        accepted operand cat, operator shadowed ⇒ the injection fires (the C3
 *        `@(Map()) <= n` case).
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

Section ChannelFirstReceiverReconnect.

  (* ── Edge kinds relevant to the enclosing-frame walk. ─────────────────────
     Mirrors `crate::gss::EdgeKind` cases the walk inspects.
     - `Receiver r ip` : `PrefixRuleEntry{cat_src, rule_idx:r, item_pos:ip}`.
       `ip>0` = a mid-rule OPERATOR slot (the target: the receiver frame);
       `ip=0` = a fresh rule dispatch (scope reset). `cat` folds into `accepts`.
     - `Grouping` : GroupingMarker (scope reset — where an inner comparison lives).
     - `Mixfix`   : MixfixMarker (a fresh receiver-first / method-call arg slot;
       scope reset).
     - `CollElem` : CollectionElement (scope reset).
     - `Cont`     : CategoryEntryContinuation — the operand continuation a
       grouping-close / projection cascade installs. The IMMEDIATE trigger edge,
       AND passed THROUGH by the walk (the whole reason this fifth arm exists).
     - `Transparent` : cross-cat-LHS re-entry OR a pass-through Proc-infix
       `ReturnFrame` (the shadowing operator's return frame) — passed through. *)
  Inductive Edge : Type :=
    | Receiver    : nat -> nat -> Edge  (* PrefixRuleEntry{rule=arg1, item_pos=arg2} *)
    | Grouping    : Edge                (* GroupingMarker (scope reset)              *)
    | Mixfix      : Edge                (* MixfixMarker (scope reset)                *)
    | CollElem    : Edge                (* CollectionElement (scope reset)           *)
    | Cont        : Edge                (* CategoryEntryContinuation (trigger+thru)  *)
    | Transparent : Edge.               (* cross-cat-LHS reentry / pass-thru Return  *)

  (* The enclosing-frame walk result: a receiver rule id + its operator slot. *)
  Inductive Frame : Type :=
    | FoundReceiver : nat -> nat -> Frame  (* receiver rule id, item_pos           *)
    | NoFrame       : Frame.               (* walk stopped / ran out               *)

  (* ── `crosscat_lhs_enclosing_channel_first_receiver_frame` (abstract). ────
     Walk the edge stack top-down: return on the first `Receiver r ip` with
     `ip>0`; stop (NoFrame) on the first Grouping / Mixfix / CollElem, or a
     `Receiver _ 0` (fresh dispatch, ip=0); pass through Cont and Transparent.
     Mirrors the Rust `match` stop-set + transparent-set EXACTLY. *)
  Fixpoint walk (es : list Edge) : Frame :=
    match es with
    | [] => NoFrame
    | Receiver r ip :: rest =>
        if Nat.ltb 0 ip then FoundReceiver r ip else NoFrame
    | Grouping   :: _ => NoFrame
    | Mixfix     :: _ => NoFrame
    | CollElem   :: _ => NoFrame
    | Cont        :: rest => walk rest
    | Transparent :: rest => walk rest
    end.

  (* Is the IMMEDIATE (top) edge a `CategoryEntryContinuation`? In the walker this
     is `matches!(__immediate_edge, CategoryEntryContinuation { .. })`. *)
  Definition immediate_is_cont (es : list Edge) : bool :=
    match es with
    | Cont :: _ => true
    | _ => false
    end.

  (* Is the IMMEDIATE (top) edge a cross-cat-LHS re-entry (the four existing arms'
     locus)? Modeled as a leading `Transparent`. Used for the disjointness proof:
     this fifth arm requires `Cont`, so it NEVER shares the frontier the existing
     arms claim. *)
  Definition immediate_is_crosscat (es : list Edge) : bool :=
    match es with
    | Transparent :: _ => true
    | _ => false
    end.

  (* ── `channel_first_receiver_frame_accepts_body_category` (abstract). ─────
     The receiver rule `r` accepts a body of category `b` iff `b` is one of its
     operand categories OR a declared single-hop coercion reaches one. Modeled
     abstractly as `accepts r b` (the Rust delegates to
     `binder_slot_accepts_body_category`, a pure boolean of (r,b)). *)
  Variable accepts : nat -> nat -> bool.

  (* ── `channel_first_receiver_operator_is_shadowed` (abstract). ────────────
     Does the completed body's category `b` recognize the lookahead operator as
     one of ITS OWN infix/postfix/mixfix operators? Modeled abstractly as
     `shadowed b` (the Rust calls `category_recognizes_operator(b, lookahead)` on
     the non-empty lookahead). TRUE for (Proc, "<="); FALSE for (Proc, "<-"). *)
  Variable shadowed : nat -> bool.

  (* ── The injection decision (the fifth arm). ─────────────────────────────
     `enabled` is the kill-switch (const && !env && !(prior arms fired)). Injects
     iff: enabled ∧ immediate edge is `Cont` ∧ walk finds `FoundReceiver r ip` ∧
     the body category b is accepted by r's operand slots ∧ the operator is
     shadowed by b. *)
  Definition inject (enabled : bool) (es : list Edge) (b : nat) : bool :=
    if enabled then
      if immediate_is_cont es then
        match walk es with
        | FoundReceiver r _ => accepts r b && shadowed b
        | NoFrame => false
        end
      else false
    else false.

  (* ══════════════ inject_iff_trigger ══════════════
     (1) The exact trigger characterization: inject fires IFF enabled AND the
     immediate edge is a continuation AND the walk finds a receiver operator slot
     whose rule accepts the body AND the operator is shadowed. No heuristic, no
     hidden condition. *)
  Theorem inject_iff_trigger :
    forall enabled es b,
      inject enabled es b = true
      <-> (enabled = true
           /\ immediate_is_cont es = true
           /\ exists r ip, walk es = FoundReceiver r ip
                           /\ accepts r b = true
                           /\ shadowed b = true).
  Proof.
    intros enabled es b. unfold inject. split.
    - intro H. destruct enabled; [| discriminate].
      destruct (immediate_is_cont es) eqn:Him; [| discriminate].
      destruct (walk es) eqn:Hw; [| discriminate].
      apply andb_true_iff in H. destruct H as [Ha Hs].
      split; [reflexivity | split; [reflexivity | ]].
      exists n, n0. split; [reflexivity | split; [exact Ha | exact Hs]].
    - intros [He [Him [r [ip [Hw [Hacc Hsh]]]]]].
      rewrite He, Him, Hw. rewrite Hacc, Hsh. reflexivity.
  Qed.

  (* ══════════════ only_fires_when_operator_shadowed ══════════════
     (2) RT-3/6: when the operator is NOT shadowed by the body category, the
     injection NEVER fires — regardless of enabled / edge stack / accept. This is
     the gate that makes the arm inert for the `<-`/`!?` twins (Proc does not
     recognize `<-`/`!?` as operators ⇒ `shadowed b = false`). *)
  Theorem only_fires_when_operator_shadowed :
    forall enabled es b,
      shadowed b = false ->
      inject enabled es b = false.
  Proof.
    intros enabled es b Hsh. unfold inject.
    destruct enabled; [| reflexivity].
    destruct (immediate_is_cont es); [| reflexivity].
    destruct (walk es); [| reflexivity].
    rewrite Hsh. rewrite andb_false_r. reflexivity.
  Qed.

  (* ══════════════ dash_twin_inert ══════════════
     (2b) The concrete DASH witness: for the `@(Map()) <- n` twin — same edge
     shape (a `Cont` immediate edge with a receiver frame below), same body cat b
     — but `<-` is not a Proc operator (`shadowed b = false`), the injection is
     inert, so the twin parses byte-identically ON vs OFF. *)
  Theorem dash_twin_inert :
    forall r ip rest b,
      shadowed b = false ->
      inject true (Cont :: Receiver r ip :: rest) b = false.
  Proof.
    intros r ip rest b Hsh. apply only_fires_when_operator_shadowed. exact Hsh.
  Qed.

  (* ══════════════ comparison_preserved_when_no_receiver_frame ══════════════
     (3) RT-2: when the walk finds NO receiver frame (a genuine comparison with no
     enclosing `@`-receiver — e.g. `Err <= Map()` at top level or in an arg slot,
     where the nearest frame is a Grouping / Mixfix / CollElem / nothing), the
     injection does NOT fire, so the genuine comparison reading is preserved (no
     spurious InputBindQuotedPersistent). Even when the operator IS shadowed
     (`<=` is a Proc infix), the absence of a receiver frame keeps it inert. *)
  Theorem comparison_preserved_when_no_receiver_frame :
    forall enabled es b,
      walk es = NoFrame ->
      inject enabled es b = false.
  Proof.
    intros enabled es b Hw. unfold inject.
    destruct enabled; [| reflexivity].
    destruct (immediate_is_cont es); [| reflexivity].
    rewrite Hw. reflexivity.
  Qed.

  (* Concrete RT-2 witness: an inner comparison under a GroupingMarker (the
     `@(Err <= Map()) <- n` inner `<=`) — the walk stops at Grouping ⇒ inert. *)
  Theorem comparison_under_grouping_no_inject :
    forall enabled rest b,
      inject enabled (Cont :: Grouping :: rest) b = false.
  Proof.
    intros enabled rest b.
    apply comparison_preserved_when_no_receiver_frame. reflexivity.
  Qed.

  (* ══════════════ non_continuation_immediate_no_inject ══════════════
     (4) When the immediate edge is NOT a `CategoryEntryContinuation` (any other
     frontier: a cross-cat-LHS re-entry — the four existing arms' locus — a direct
     rule return, a same-category operand, …), the injection never fires. This is
     byte-identity for every non-continuation path AND the disjointness from the
     four existing arms (whose immediate edge is cross-cat-LHS / direct
     PrefixRuleEntry, never a bare continuation). *)
  Theorem non_continuation_immediate_no_inject :
    forall enabled es b,
      immediate_is_cont es = false ->
      inject enabled es b = false.
  Proof.
    intros enabled es b Him. unfold inject.
    destruct enabled; [| reflexivity]. rewrite Him. reflexivity.
  Qed.

  (* ══════════════ categoryentrycontinuation_walk_transparent ══════════════
     (5) The walk looks THROUGH the `CategoryEntryContinuation` (and multi-hop
     mixed Cont/Transparent lineages) to the receiver `PrefixRuleEntry{ip>0}` — the
     exact look-through the four existing walkers LACK (they stop on Cont). A
     receiver reachable through any number of Cont/Transparent edges IS found.
     `pre` is any interleaving of the transparent edges. *)
  Definition is_transparent (e : Edge) : bool :=
    match e with Cont => true | Transparent => true | _ => false end.

  Theorem walk_transparent_finds_receiver :
    forall pre r ip rest,
      forallb is_transparent pre = true ->
      0 < ip ->
      walk (pre ++ Receiver r ip :: rest) = FoundReceiver r ip.
  Proof.
    induction pre as [| e pre IH]; intros r ip rest Hpre Hip; simpl.
    - (* base: head is the receiver; ip>0 ⇒ FoundReceiver *)
      apply Nat.ltb_lt in Hip. rewrite Hip. reflexivity.
    - (* step: e is transparent (Cont or Transparent), recurse *)
      simpl in Hpre. apply andb_true_iff in Hpre. destruct Hpre as [He Hpre'].
      destruct e; simpl in He; try discriminate He.
      + (* CollElem is not transparent — excluded by He; remaining: Cont, Transparent *)
        (* (this branch unreachable: Receiver/Grouping/Mixfix/CollElem give He=false) *)
        exact (IH r ip rest Hpre' Hip).
      + exact (IH r ip rest Hpre' Hip).
  Qed.

  (* The concrete C3 edge stack `[Cont | Receiver 6 2]` walks to the receiver. *)
  Theorem c3_edgestack_finds_receiver :
    forall rest, walk (Cont :: Receiver 6 2 :: rest) = FoundReceiver 6 2.
  Proof. intro rest. reflexivity. Qed.

  (* ══════════════ scope-reset stops ══════════════
     (6) NESTING PRECEDENCE: a scope-resetting frame (Grouping / Mixfix / CollElem
     / a fresh `Receiver _ 0`) reached BEFORE any receiver operator slot stops the
     walk — the operand belongs to that inner scope, not the outer receiver rule,
     so no reconnection. Mirrors the stop-set of the four existing walks. *)
  Theorem grouping_stops_walk :
    forall rest, walk (Grouping :: rest) = NoFrame.
  Proof. intro rest. reflexivity. Qed.

  Theorem mixfix_stops_walk :
    forall rest, walk (Mixfix :: rest) = NoFrame.
  Proof. intro rest. reflexivity. Qed.

  Theorem collelem_stops_walk :
    forall rest, walk (CollElem :: rest) = NoFrame.
  Proof. intro rest. reflexivity. Qed.

  Theorem fresh_dispatch_stops_walk :
    forall r rest, walk (Receiver r 0 :: rest) = NoFrame.
  Proof. intros r rest. reflexivity. Qed.

  (* Consequences: a receiver operator slot NESTED inside a fresh arg-slot / group
     / collection element / fresh dispatch cannot wrongly reconnect. Shown for EACH
     scope-resetting frame reached through the continuation. *)
  Theorem inner_scope_no_reconnect_grouping :
    forall enabled rest b, inject enabled (Cont :: Grouping :: rest) b = false.
  Proof.
    intros. apply comparison_preserved_when_no_receiver_frame. reflexivity.
  Qed.

  Theorem inner_scope_no_reconnect_mixfix :
    forall enabled rest b, inject enabled (Cont :: Mixfix :: rest) b = false.
  Proof.
    intros. apply comparison_preserved_when_no_receiver_frame. reflexivity.
  Qed.

  Theorem inner_scope_no_reconnect_collelem :
    forall enabled rest b, inject enabled (Cont :: CollElem :: rest) b = false.
  Proof.
    intros. apply comparison_preserved_when_no_receiver_frame. reflexivity.
  Qed.

  Theorem inner_scope_no_reconnect_fresh_dispatch :
    forall enabled r rest b, inject enabled (Cont :: Receiver r 0 :: rest) b = false.
  Proof.
    intros enabled r rest b.
    apply comparison_preserved_when_no_receiver_frame. reflexivity.
  Qed.

  (* ── Branch set (GLR no-loss). ────────────────────────────────────────────
     A branch set is a list of "readings"; the operator/short readings are already
     present (the continuation's own operator-continuation branches). The injection
     APPENDS one Unwinding reading iff it fires; the `already_has_unwind` guard is
     modeled by only appending when absent. *)
  Inductive Reading : Type :=
    | ROperator       (* the shadowing-operator continuation (rule-64 LtEq)       *)
    | RUnwind.        (* the injected "channel complete; return it" reading       *)

  Definition reading_eqb (x y : Reading) : bool :=
    match x, y with
    | ROperator, ROperator => true
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
     (7) NO-LOSS: every reading present before the injection is still present
     after — the injection only APPENDS RUnwind, never removes the operator
     reading. (GLR-safe: the shadowing-operator reading survives; it is the reading
     that WINS for a genuine comparison, and loses via evidence-pruning for a
     receiver bind — but it is never removed.) *)
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
     (7b) When the injection fires (and no prior Unwind), the RUnwind reading IS
     added — the receiver-reconnection reading is genuinely offered alongside the
     operator reading. *)
  Theorem inject_present_when_fires :
    forall enabled es b bs,
      inject enabled es b = true ->
      has_unwind bs = false ->
      In RUnwind (apply_inject enabled es b bs).
  Proof.
    intros enabled es b bs Hinj Hno. unfold apply_inject.
    rewrite Hinj, Hno. simpl. apply in_or_app. right. left. reflexivity.
  Qed.

  (* ══════════════ pop_via_own_edge_sound / injected_body_is_channel ══════════════
     (8) RT-4: the injection's unwound symbol is the completed channel `pat` — the
     SPPF top the Fork already holds — and the pop returns via the receiver
     `PrefixRuleEntry{ip>0}` edge (the `Receiver r ip` the walk RETURNED), NOT via
     the pass-through Proc-infix `ReturnFrame`. We model the pass-through Return as
     a leading `Transparent` above the receiver: the walk PASSES it and returns the
     receiver edge BELOW it. Hence the frame the unwind pops is the receiver, whose
     operand slot the body `pat` fills (`accepts r b`) — the body is the channel,
     not the comparand. *)
  Theorem pop_via_own_edge_sound :
    forall r ip rest,
      0 < ip ->
      walk (Cont :: Transparent :: Receiver r ip :: rest) = FoundReceiver r ip.
  Proof.
    intros r ip rest Hip. simpl. apply Nat.ltb_lt in Hip. rewrite Hip. reflexivity.
  Qed.

  (* When the arm fires, the frame it reconnects to IS a receiver whose operand
     slot the body fills — i.e. the unwound body is a channel the receiver accepts,
     never an unrelated comparand. (Direct corollary of the trigger: firing ⇒
     `walk = FoundReceiver r ip ∧ accepts r b`.) *)
  Theorem injected_body_is_channel_not_comparand :
    forall es b,
      inject true es b = true ->
      exists r ip, walk es = FoundReceiver r ip /\ accepts r b = true.
  Proof.
    intros es b H.
    apply inject_iff_trigger in H. destruct H as [_ [_ [r [ip [Hw [Hacc _]]]]]].
    exists r, ip. split; [exact Hw | exact Hacc].
  Qed.

  (* ══════════════ killswitch_off_noop ══════════════
     (9) KILL-SWITCH OFF (enabled = false) ⇒ the injection NEVER fires, for ANY
     edge stack / body — byte-identical control (the const gate = false /
     PRATTAIL_NO_CHANNEL_FIRST_RECONNECT). *)
  Theorem killswitch_off_no_inject :
    forall es b, inject false es b = false.
  Proof. intros es b. reflexivity. Qed.

  Theorem killswitch_off_apply_noop :
    forall es b bs, apply_inject false es b bs = bs.
  Proof.
    intros es b bs. unfold apply_inject.
    rewrite killswitch_off_no_inject. reflexivity.
  Qed.

  (* ══════════════ disjoint_from_reconnection_family ══════════════
     (10) RT-5: DISJOINTNESS from the four existing arms. The Rust fix orders this
     arm AFTER them (guards on `!__under_binder_resume && !__under_crosscat_binder_resume
     && !__under_crosscat_collection_element && !__under_crosscat_infix_rhs`), and
     it requires a `Cont` immediate edge whereas the four require a cross-cat-LHS
     (`Transparent`-modeled) OR direct `PrefixRuleEntry` immediate edge. Model
     consequence: whenever the immediate edge is cross-cat-LHS (the existing arms'
     locus), THIS arm does NOT fire — the five arms never both claim the same
     frontier. *)
  Theorem disjoint_from_crosscat_arms :
    forall enabled es b,
      immediate_is_crosscat es = true ->
      inject enabled es b = false.
  Proof.
    intros enabled es b Hx.
    apply non_continuation_immediate_no_inject.
    (* immediate_is_crosscat = true ⇒ head = Transparent ⇒ immediate_is_cont = false *)
    destruct es as [| e es']; [reflexivity |].
    destruct e; simpl in Hx; try discriminate Hx; reflexivity.
  Qed.

  (* Composition: the fifth arm and the existing family are mutually exclusive on
     any given frontier — at most one immediate-edge predicate holds. *)
  Theorem cont_and_crosscat_mutually_exclusive :
    forall es,
      immediate_is_cont es = true -> immediate_is_crosscat es = false.
  Proof.
    intros es Hc. destruct es as [| e es']; [reflexivity |].
    destruct e; simpl in Hc; try discriminate Hc; reflexivity.
  Qed.

  (* ══════════════ maximal_extent_fires_when_accepted_and_shadowed ══════════════
     (11) The REPAIR witness: continuation immediate edge, enclosing receiver
     `PrefixRuleEntry{r, ip>0}`, body already in an accepted operand cat b, operator
     shadowed by b ⇒ the injection fires (offering the reconnection). This is the
     C3 `@(Map()) <= n` case: edge stack `[Cont | Receiver 6 2]`, body `Map():Proc`
     (accepted by `InputBindQuotedPersistent`'s operand slots), `<=` shadowed by
     Proc (LtEq). *)
  Theorem maximal_extent_fires_when_accepted_and_shadowed :
    forall r ip b rest,
      0 < ip ->
      accepts r b = true ->
      shadowed b = true ->
      inject true (Cont :: Receiver r ip :: rest) b = true.
  Proof.
    intros r ip b rest Hip Hacc Hsh. unfold inject. simpl.
    apply Nat.ltb_lt in Hip. rewrite Hip. rewrite Hacc, Hsh. reflexivity.
  Qed.

End ChannelFirstReceiverReconnect.

(* ══════════════════════════════════════════════════════════════════════════
   Admission audit. Every theorem above must be closed under the global context
   (no Admitted, no Axiom, no Variable-as-axiom leakage — the Section discharges
   `accepts` and `shadowed` as universally-quantified hypotheses, NOT axioms). *)
Print Assumptions inject_iff_trigger.
Print Assumptions only_fires_when_operator_shadowed.
Print Assumptions dash_twin_inert.
Print Assumptions comparison_preserved_when_no_receiver_frame.
Print Assumptions comparison_under_grouping_no_inject.
Print Assumptions non_continuation_immediate_no_inject.
Print Assumptions walk_transparent_finds_receiver.
Print Assumptions c3_edgestack_finds_receiver.
Print Assumptions grouping_stops_walk.
Print Assumptions mixfix_stops_walk.
Print Assumptions collelem_stops_walk.
Print Assumptions fresh_dispatch_stops_walk.
Print Assumptions inner_scope_no_reconnect_grouping.
Print Assumptions inner_scope_no_reconnect_mixfix.
Print Assumptions inner_scope_no_reconnect_collelem.
Print Assumptions inner_scope_no_reconnect_fresh_dispatch.
Print Assumptions inject_adds_reading_no_loss.
Print Assumptions inject_present_when_fires.
Print Assumptions pop_via_own_edge_sound.
Print Assumptions injected_body_is_channel_not_comparand.
Print Assumptions killswitch_off_no_inject.
Print Assumptions killswitch_off_apply_noop.
Print Assumptions disjoint_from_crosscat_arms.
Print Assumptions cont_and_crosscat_mutually_exclusive.
Print Assumptions maximal_extent_fires_when_accepted_and_shadowed.
