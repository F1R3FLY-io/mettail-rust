(*
 * CollectionElementMaximalReconnect: zero-admission FV for the Root-B
 * collection-element MAXIMAL-EXTENT reconnection injection
 * (prattail/src/wpda_walker.rs, the InfixLoop Fork handler's third injection arm
 *  `__under_crosscat_collection_element`, plus the helpers
 *  `crosscat_lhs_enclosing_collection_element_frame` and
 *  `collection_element_accepts_body_category`).
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE DEFECT (trace-evidenced; deterministic; category ordering
 *   Proc=0, InputBind=1, ForRow=2, Name=3):
 *
 *   `Proc::parse("a!(x, y!(z), w)")` FAILS (and `a!(x, y!(), w)`,
 *   `a!(x, y!(z), u!(v), w)`, `@a <- @b!?(x!(y), z)`), while the SAME element as
 *   the LAST rest-element (`a!(x, w, y!(z))`), or as a keyword-collection
 *   (`a!(x, Map(), w)`), or a grouped/postfix element (`a!(x, (z), w)`,
 *   `a!(x, y.union(z), w)`), all SUCCEED.
 *
 *   Root (trace `trace_rb_midsend.log`; tokens a0 !1 (2 x3 ,4 y5 !6 (7 z8 )9 ,10
 *   w11 )12): the `bs:Vec(Proc)` rest-collection element `y` is dispatched under
 *   the POutput2Plus `CollectionElement{result_src:0,rule_idx:8,acc_id:1}` frame
 *   (element category = Proc = 0). `y` completes as a Name (cat 3). The Name→Proc
 *   SEND extension (`y` → `y!(z)`) is offered by the InfixLoop `CrossCatLhsScoped
 *   {source:3}` cross-cat-LHS delegate. That extension lineage RE-SCOPES onto the
 *   Name frame and pops OUT of the collection: the maximal `y!(z):Proc` (span
 *   [5,10]) interns but with `enclosing_frame=None`, and the collection loop only
 *   ever takes the SHORT `y:Name` (span [5,6]) pop-back to the CollectionMarker.
 *   At pos 6 (the inner `!`, not the sep `,`) the collection's G1-G4 dispatch
 *   matches nothing, so the element dies; the outer `,` at pos 10 is never
 *   consumed (`ConsumeCollectionSep = 0`). The DECISIVE edge stack at pos 10 is
 *     [CrossCatLhsScoped{src:3} | CollectionElement{..} | MixfixMarker{..} | ..]
 *   with the SPPF top ALREADY in the element category (Proc) — the maximal
 *   element IS reachable to the CollectionElement THROUGH the cross-cat-LHS edge,
 *   but NO reading unwinds it back to the CollectionMarker.
 *
 *   `Map()` works because it is dispatched as a COMPLETE Proc element (the Root-A
 *   lex-fork element-category redirect) that finalizes AT the sep — no Name→Proc
 *   cross-cat extension is needed. `(z)` group / `y.union(z)` postfix / `y` var
 *   work because none needs the Name→Proc cross-cat-LHS re-scoping.
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE FIX (mirrors the PROVEN GROUP-A binder-slot-unwind-inject, wpda_walker.rs
 *   :13065, which does the SAME reconnection for `PrefixRuleEntry{item_pos>0}` /
 *   `MixfixMarker` rule arg-slots): a THIRD injection arm fires when the InfixLoop
 *   Fork sits at a CategoryEntry frontier whose IMMEDIATE incoming edge is a
 *   cross-cat-LHS re-entry (`CrossCatLhsScoped`/`Reentry`) AND the nearest
 *   enclosing frame reachable THROUGH cross-cat-LHS edges is a `CollectionElement`
 *   AND the completed body (SPPF top) is ALREADY in the collection's element
 *   category. It injects one `Advance -> Unwinding` branch so the MAXIMAL element
 *   returns to the CollectionMarker (whose pop then splices + consumes the
 *   sep/close at maximal extent). GLR no-loss: the short-element reading survives.
 *
 *   `crosscat_lhs_enclosing_collection_element_frame` walks transparent through
 *   cross-cat-LHS edges, RETURNS on the first `CollectionElement`, STOPS (None) on
 *   the first scope-resetting frame (`GroupingMarker` / `PrefixRuleEntry
 *   {item_pos>0}` / `MixfixMarker`) — the SAME stop-set as
 *   `collection_element_direct_separator`. This is why a rule/group NESTED inside
 *   a collection element does not wrongly reconnect to the OUTER collection.
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THIS MODEL abstracts the injection decision `inject : InfixCtx -> bool` and the
 * enclosing-frame walk `walk : list Edge -> option Frame`. The theorems establish:
 *   (1) inject fires IFF the exact trigger (cross-cat-LHS immediate edge ∧ walk
 *       finds a CollectionElement ∧ body cat accepted) — no heuristic;
 *   (2) SHORT (pre-extension) body (cat ∉ element accepts) ⇒ no inject (the pos-6
 *       Name case; the fix fires ONLY at maximal extent);
 *   (3) a NON-cross-cat immediate edge ⇒ no inject (byte-identity for the
 *       kill-switch-OFF / same-cat-collection paths);
 *   (4) the walk STOPS at a scope-resetting frame reached before a CollectionElement
 *       (the nesting-precedence soundness — no reconnect across a re-scoping frame);
 *   (5) no-loss WITNESS: injecting ADDS the Unwinding reading to a branch set that
 *       already contains the short/operator readings (the short element survives);
 *   (6) kill-switch OFF ⇒ never inject (byte-identical control).
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

Section CollectionElementMaximalReconnect.

  (* ── Edge kinds relevant to the enclosing-frame walk. ─────────────────────
     Mirrors `crate::gss::EdgeKind` cases the walk inspects. A `CollElem c`
     carries the collection's element category `c` (from
     `collection_spec.element_src_idx`). `Grouping` / `RuleSlot` are the
     scope-resetting frames (GroupingMarker / PrefixRuleEntry{item_pos>0} /
     MixfixMarker). `Transparent` is a cross-cat-LHS re-entry or a return frame
     the walk passes THROUGH. *)
  Inductive Edge : Type :=
    | CollElem   : nat -> Edge     (* CollectionElement, element cat = arg   *)
    | Grouping   : Edge            (* GroupingMarker (scope reset)           *)
    | RuleSlot   : Edge            (* PrefixRuleEntry{ip>0} / MixfixMarker    *)
    | Transparent : Edge.          (* cross-cat-LHS reentry / return frame    *)

  (* The enclosing-frame walk result. *)
  Inductive Frame : Type :=
    | FoundColl : nat -> Frame     (* a CollectionElement, element cat        *)
    | NoFrame   : Frame.           (* walk stopped / ran out                  *)

  (* ── `crosscat_lhs_enclosing_collection_element_frame` (abstract). ────────
     Walk the edge stack top-down: return on the first CollElem; stop (NoFrame)
     on the first Grouping/RuleSlot; pass through Transparent. Mirrors the Rust
     `match` stop-set exactly. *)
  Fixpoint walk (es : list Edge) : Frame :=
    match es with
    | [] => NoFrame
    | CollElem c :: _ => FoundColl c
    | Grouping   :: _ => NoFrame
    | RuleSlot   :: _ => NoFrame
    | Transparent :: rest => walk rest
    end.

  (* Is the IMMEDIATE (top) edge a cross-cat-LHS re-entry? In the walker this is
     `matches!(__immediate_edge, CrossCatLhsScoped | CrossCatLhsReentry)`. Here a
     cross-cat-LHS immediate edge is modeled as a leading `Transparent`
     (cross-cat-LHS reentries ARE the transparent edges the walk passes through;
     the immediate one is what the arm gates on). *)
  Definition immediate_is_crosscat (es : list Edge) : bool :=
    match es with
    | Transparent :: _ => true
    | _ => false
    end.

  (* ── `collection_element_accepts_body_category` (abstract). ───────────────
     The collection's element category `c` accepts a body of category `b` iff
     b = c OR a declared single-hop coercion b ↝ c exists. `coerces b c` mirrors
     `single_hop_coercion(b,c)` non-empty into c; `is_kv c` excludes kv-maps. *)
  Variable coerces : nat -> nat -> bool.
  Variable is_kv   : nat -> bool.

  Definition accepts (c b : nat) : bool :=
    negb (is_kv c) && (Nat.eqb b c || coerces b c).

  (* ── The injection decision (the arm). ───────────────────────────────────
     `enabled` is the kill-switch (const && !env). Injects iff:
       enabled ∧ immediate edge is cross-cat-LHS ∧ walk finds CollElem c ∧
       the body category b is accepted by c. *)
  Definition inject (enabled : bool) (es : list Edge) (b : nat) : bool :=
    if enabled then
      if immediate_is_crosscat es then
        match walk es with
        | FoundColl c => accepts c b
        | NoFrame => false
        end
      else false
    else false.

  (* ══════════════ inject_iff_trigger ══════════════
     (1) The exact trigger characterization: inject fires IFF enabled AND the
     immediate edge is cross-cat-LHS AND the walk finds a CollElem whose element
     category accepts the body. No heuristic, no hidden condition. *)
  Theorem inject_iff_trigger :
    forall enabled es b,
      inject enabled es b = true
      <-> (enabled = true
           /\ immediate_is_crosscat es = true
           /\ exists c, walk es = FoundColl c /\ accepts c b = true).
  Proof.
    intros enabled es b. unfold inject. split.
    - intro H. destruct enabled; [| discriminate].
      destruct (immediate_is_crosscat es) eqn:Him; [| discriminate].
      destruct (walk es) eqn:Hw; [| discriminate].
      split; [reflexivity | split; [reflexivity | ]]. exists n. split; [reflexivity | exact H].
    - intros [He [Him [c [Hw Hacc]]]].
      rewrite He, Him, Hw. exact Hacc.
  Qed.

  (* ══════════════ short_body_no_inject ══════════════
     (2) A SHORT (pre-extension) body whose category is NOT accepted by the
     collection's element category does NOT trigger the injection — the pos-6
     `y:Name` (cat 3) case for a `bs:Vec(Proc)` (element cat 0): accepts 0 3 =
     false (3<>0 and no Proc coercion), so no inject. The fix fires ONLY at
     maximal extent (body already in the element cat). *)
  Theorem short_body_no_inject :
    forall enabled es c b,
      walk es = FoundColl c ->
      accepts c b = false ->
      inject enabled es b = false.
  Proof.
    intros enabled es c b Hw Hacc. unfold inject.
    destruct enabled; [| reflexivity].
    destruct (immediate_is_crosscat es); [| reflexivity].
    rewrite Hw, Hacc. reflexivity.
  Qed.

  (* ══════════════ non_crosscat_immediate_no_inject ══════════════
     (3) When the immediate edge is NOT a cross-cat-LHS re-entry (any other
     frontier: a direct collection element, a same-category collection, a rule
     slot, …), the injection never fires — byte-identity for every non-cross-cat
     path (the same-cat collections & the Root-A direct-dispatch element `Map()`). *)
  Theorem non_crosscat_immediate_no_inject :
    forall enabled es b,
      immediate_is_crosscat es = false ->
      inject enabled es b = false.
  Proof.
    intros enabled es b Him. unfold inject.
    destruct enabled; [| reflexivity]. rewrite Him. reflexivity.
  Qed.

  (* ══════════════ scope_reset_stops_walk ══════════════
     (4a) NESTING PRECEDENCE: a scope-resetting frame (Grouping / RuleSlot)
     reached BEFORE any CollElem stops the walk — the operand belongs to that
     inner scope, not the outer collection, so no reconnection. Mirrors the
     stop-set of `collection_element_direct_separator`. *)
  Theorem grouping_stops_walk :
    forall rest, walk (Grouping :: rest) = NoFrame.
  Proof. intro rest. reflexivity. Qed.

  Theorem ruleslot_stops_walk :
    forall rest, walk (RuleSlot :: rest) = NoFrame.
  Proof. intro rest. reflexivity. Qed.

  (* ══════════════ inner_scope_no_reconnect ══════════════
     (4b) Consequence: if a scope-resetting frame precedes the (would-be)
     CollElem, the injection does NOT fire — a rule/group NESTED inside a
     collection element cannot wrongly reconnect the operand to the OUTER
     collection. (`es` prefixed by a Grouping ⇒ walk = NoFrame ⇒ inject = false.) *)
  Theorem inner_scope_no_reconnect :
    forall enabled rest b,
      inject enabled (Transparent :: Grouping :: rest) b = false.
  Proof.
    intros enabled rest b. unfold inject.
    destruct enabled; [| reflexivity].
    (* immediate is Transparent ⇒ crosscat true; walk skips Transparent, hits
       Grouping ⇒ NoFrame. *)
    simpl. reflexivity.
  Qed.

  (* ── Branch set (GLR no-loss). ────────────────────────────────────────────
     A branch set is a list of "readings"; the SHORT/operator readings are
     already present. The injection APPENDS one Unwinding reading iff it fires;
     the `already_has_unwind` guard is modeled by only appending when absent. *)
  Inductive Reading : Type :=
    | RShort          (* the short element / operator continuation           *)
    | RUnwind.        (* the injected "element complete; return it" reading  *)

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
     (GLR-safe: the short-element reading survives alongside the maximal one.) *)
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
     edge stack / body — byte-identical control (PRATTAIL_NO_COLL_ELEM_RECONNECT
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

  (* ══════════════ kv_collection_no_inject ══════════════
     (7) kv-collections (which carry a kv separator) are EXCLUDED: a single
     element category cannot speak for both key and value slots, so `accepts`
     is false for them ⇒ no inject. Byte-identity guard for maps. *)
  Theorem kv_collection_no_inject :
    forall enabled es c b,
      walk es = FoundColl c ->
      is_kv c = true ->
      inject enabled es b = false.
  Proof.
    intros enabled es c b Hw Hkv. unfold inject.
    destruct enabled; [| reflexivity].
    destruct (immediate_is_crosscat es); [| reflexivity].
    rewrite Hw. unfold accepts. rewrite Hkv. simpl. reflexivity.
  Qed.

  (* ══════════════ maximal_extent_fires_when_accepted ══════════════
     (8) The REPAIR witness: at maximal extent — cross-cat-LHS immediate edge,
     enclosing CollElem with element cat c, body already in cat c (b=c, non-kv) —
     the injection fires (offering the reconnection). This is the pos-10
     `y!(z):Proc` (cat 0) under `bs:Vec(Proc)` (element cat 0) case. *)
  Theorem maximal_extent_fires_when_accepted :
    forall c rest,
      is_kv c = false ->
      inject true (Transparent :: CollElem c :: rest) c = true.
  Proof.
    intros c rest Hkv. unfold inject. simpl.
    unfold accepts. rewrite Hkv, Nat.eqb_refl. reflexivity.
  Qed.

End CollectionElementMaximalReconnect.

(* ══════════════════════════════════════════════════════════════════════════
   Admission audit. Every theorem above must be closed under the global context
   (no Admitted, no Axiom, no Variable-as-axiom leakage — the Section discharges
   `lex`/`coerces`/`is_kv`/… as universally-quantified hypotheses, NOT axioms). *)
Print Assumptions inject_iff_trigger.
Print Assumptions short_body_no_inject.
Print Assumptions non_crosscat_immediate_no_inject.
Print Assumptions grouping_stops_walk.
Print Assumptions ruleslot_stops_walk.
Print Assumptions inner_scope_no_reconnect.
Print Assumptions inject_adds_reading_no_loss.
Print Assumptions inject_present_when_fires.
Print Assumptions killswitch_off_no_inject.
Print Assumptions killswitch_off_apply_noop.
Print Assumptions kv_collection_no_inject.
Print Assumptions maximal_extent_fires_when_accepted.
