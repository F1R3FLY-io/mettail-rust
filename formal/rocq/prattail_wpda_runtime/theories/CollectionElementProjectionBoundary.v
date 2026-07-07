(*
 * CollectionElementProjectionBoundary: zero-admission FV for the ROOT A fix to
 * `crosscat_projection_target_boundary` (prattail/src/wpda_walker.rs).
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE DEFECT (trace-evidenced; deterministic; category ordering
 *   Proc=0, InputBind=1, ForRow=2, Name=3):
 *
 *   `Name::parse("@{a!(Nil)}")` FAILS ("no accepting branch, found Ident" at the
 *   inner `a`), while `@{Nil}`, `@{Nil|Nil}`, `@{a+a}`, `@[Nil,Nil]`,
 *   `@{|Nil:Nil|}`, `@#{Nil}#`, `@{@a!(Nil)}` all SUCCEED.
 *
 *   `@{a!(Nil)}` = `NQuoteShort(PPar({a!(Nil)}))`. The `@` (NQuoteShort,
 *   `prefix(220)`) dispatches its Proc operand under a CrossCatProjection whose
 *   `inner_cur_bp = 220`. The `{…}` PPar collection element `a` is dispatched at
 *   floor 0 and completes as a Name (cat 3). To become `POutput = n:Name "!" …`
 *   (a Proc, cat 0) it needs the Name→Proc cross-cat send extension at `!`.
 *   `crosscat_projection_target_boundary` walks the incoming-edge stack for a
 *   projection target that also recognizes `!`; before the fix its stop-set was
 *   only {PrefixRuleEntry{item_pos>0}, MixfixMarker}, so the walk skipped PAST
 *   the `CollectionElement` frame and found the OUTER `@`-projection with
 *   `target_floor = 220`. Since Proc rejects `!` at floor 220
 *   (`target_accepts=false`) while Name accepts it at 0 (`source_accepts=true`),
 *   the boundary logic HANDS OFF (suppresses) the source's `!` consumption →
 *   `POutput` never forms → all branches drop → parse ERR. (Trace: `crosscat
 *   target-boundary source=3 target=3 pos=3 source_floor=0 target_floor=220
 *   lookahead="!" source_accepts=true target_accepts=false`.)
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THE FIX (mirrors the SAME stop-set already used by the reconnection direction,
 *   `crosscat_lhs_enclosing_collection_element_frame` /
 *   `CollectionElementMaximalReconnect.v`, and the for-body reconnection stop):
 *   add `CollectionElement` to the scope-boundary stop of the boundary walk. A
 *   bracket-delimited collection literal RE-SCOPES each element as a FRESH
 *   sub-parse at floor 0, and the brackets are SELF-DELIMITING — so an operator
 *   token an element's InfixLoop wants to consume can NEVER belong to anything
 *   OUTSIDE the brackets. The walk therefore MUST NOT hand such an operator to an
 *   outer projection; stopping at the CollectionElement frame returns `None` (no
 *   outer handoff), leaving the element's own InfixLoop to consume the operator
 *   at its element-local floor (0). The completed collection's binding to the
 *   outer projection floor is governed later, at the CollectionMarker pop, by the
 *   OUTER edge — exactly as with the for-body / infix-RHS rule-slot frames.
 *
 * ─────────────────────────────────────────────────────────────────────────
 * THIS MODEL abstracts the boundary walk `walk : list Edge -> option Target` and
 * the handoff decision `handoff`. `walk` returns the first projection Target it
 * reaches, PASSING THROUGH transparent cross-cat edges and STOPPING (None) at any
 * scope-resetting frame. The fix adds `CollElem` to that stop-set. The theorems
 * establish:
 *   (1) walk STOPS at a CollElem reached before any projection target — the fix's
 *       core: no outer target is returned through a collection element;
 *   (2) consequently the handoff never fires when a CollElem shields the source
 *       from the outer projection (the `@{a!(Nil)}` repair) — the source keeps
 *       its operator;
 *   (3) the stop is ONE-SIDED / no-loss: it can only turn a would-be handoff into
 *       "source keeps the operator"; it never removes a legitimate source parse
 *       (a bracket-interior operator is by construction element-local);
 *   (4) NESTING soundness: a scope-resetting frame (Grouping / RuleSlot / the new
 *       CollElem) reached before a target shields inner scopes — unchanged for the
 *       pre-existing stops, extended to CollElem;
 *   (5) control (stop-set WITHOUT CollElem, = PRATTAIL_NO_BOUNDARY_STOP semantics
 *       for the collection case) reproduces the pre-fix walk that DOES find the
 *       outer target through a collection element (the defect), proving the change
 *       is exactly the added stop and nothing else;
 *   (6) NON-collection stacks are byte-identical: adding CollElem to the stop-set
 *       does not alter any walk whose relevant prefix contains no CollElem.
 *
 * THEOREMS (all admission-free; audited by `Print Assumptions`, which must report
 *   "Closed under the global context").
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
Import ListNotations.

Section CollectionElementProjectionBoundary.

  (* ── Edge kinds relevant to the boundary walk. ────────────────────────────
     Mirrors the `crate::gss::EdgeKind` cases `crosscat_projection_target_boundary`
     inspects. `Proj t` is a cross-cat projection target frame carrying its
     `target_floor` `t` (from `crosscat_boundary_target_for_edge`:
     `CrossCatProjection.inner_cur_bp`, or a `CrossCatLhs*` resume_bp). `CollElem`
     is the collection-element frame (the ADDED stop). `Grouping` / `RuleSlot` are
     the pre-existing scope-resetting frames (GroupingMarker / PrefixRuleEntry
     {item_pos>0} / MixfixMarker). `Pass` is a transparent edge the walk passes
     THROUGH (a cross-cat-LHS re-entry lineage / a non-target frame). *)
  Inductive Edge : Type :=
    | Proj      : nat -> Edge      (* projection target frame, target_floor = arg *)
    | CollElem  : Edge             (* CollectionElement frame (the ADDED stop)     *)
    | Grouping  : Edge             (* GroupingMarker (pre-existing stop)           *)
    | RuleSlot  : Edge             (* PrefixRuleEntry{ip>0}/MixfixMarker (stop)    *)
    | Pass      : Edge.            (* transparent edge, walk passes through        *)

  (* The boundary walk result: the outer projection target's floor, or none. *)
  Inductive Target : Type :=
    | Found : nat -> Target        (* a projection target, its target_floor        *)
    | None_ : Target.              (* walk stopped / ran out — NO outer handoff     *)

  (* ── `crosscat_projection_target_boundary` (post-fix, abstract). ──────────
     Walk top-down: return the first Proj's floor; STOP (None_) at the first
     Grouping / RuleSlot / CollElem (the post-fix stop-set); pass through Pass.
     Mirrors the Rust `match kind { PrefixRuleEntry{ip>0} | MixfixMarker |
     CollectionElement => return None, .. }` stop, then the per-edge target
     resolution. *)
  Fixpoint walk (es : list Edge) : Target :=
    match es with
    | [] => None_
    | Proj t   :: _ => Found t
    | CollElem :: _ => None_       (* ← THE FIX: CollectionElement is a stop *)
    | Grouping :: _ => None_
    | RuleSlot :: _ => None_
    | Pass     :: rest => walk rest
    end.

  (* ── `crosscat_projection_target_boundary` (PRE-fix control, abstract). ───
     Identical EXCEPT CollElem is NOT a stop — the walk passes through it (the
     defect: it finds the OUTER projection through a collection element). This is
     the `PRATTAIL_NO_BOUNDARY_STOP=1`-for-collections control. *)
  Fixpoint walk_prefix (es : list Edge) : Target :=
    match es with
    | [] => None_
    | Proj t   :: _ => Found t
    | CollElem :: rest => walk_prefix rest   (* PRE-fix: pass through *)
    | Grouping :: _ => None_
    | RuleSlot :: _ => None_
    | Pass     :: rest => walk_prefix rest
    end.

  (* ── The handoff decision. ────────────────────────────────────────────────
     A handoff (suppress the source operator, hand it to the outer projection)
     fires iff the walk finds a target AND the target does NOT accept the operator
     at its floor while the source DOES at its own floor. `src_accepts` /
     `tgt_accepts t` mirror `source_accepts_at_source_floor` /
     `target_accepts_at_projection_floor`. When `walk = None_` there is NO target,
     so NO handoff — the source keeps its operator. *)
  Variable src_accepts : bool.        (* source accepts op at its own floor *)
  Variable tgt_accepts : nat -> bool. (* target accepts op at target_floor  *)

  Definition handoff (w : Target) : bool :=
    match w with
    | Found t => src_accepts && negb (tgt_accepts t)
    | None_ => false
    end.

  (* Post-fix and pre-fix handoff decisions. *)
  Definition handoff_postfix (es : list Edge) : bool := handoff (walk es).
  Definition handoff_prefix  (es : list Edge) : bool := handoff (walk_prefix es).

  (* ══════════════ collelem_stops_walk ══════════════
     (1) CORE: the post-fix walk STOPS at a CollElem — no outer target is ever
     returned THROUGH a collection-element frame. (`@{a!(Nil)}`: the CollElem
     shields the source Name from the outer `@`-projection.) *)
  Theorem collelem_stops_walk :
    forall rest, walk (CollElem :: rest) = None_.
  Proof. intro rest. reflexivity. Qed.

  (* And through any transparent lineage that reaches a CollElem first. *)
  Theorem collelem_stops_walk_through_pass :
    forall rest, walk (Pass :: CollElem :: rest) = None_.
  Proof. intro rest. reflexivity. Qed.

  (* ══════════════ collelem_no_handoff ══════════════
     (2) THE REPAIR: when the immediate/transparent lineage reaches a CollElem
     before any projection target, the handoff never fires — the source keeps its
     operator (the element's own InfixLoop consumes `!`, forming POutput). Holds
     for ANY src/tgt acceptance (in particular the trace's src_accepts=true,
     tgt_accepts=false, which PRE-fix produced the erroneous handoff). *)
  Theorem collelem_no_handoff :
    forall rest, handoff_postfix (CollElem :: rest) = false.
  Proof.
    intro rest. unfold handoff_postfix. rewrite collelem_stops_walk. reflexivity.
  Qed.

  Theorem collelem_no_handoff_through_pass :
    forall rest, handoff_postfix (Pass :: CollElem :: rest) = false.
  Proof.
    intro rest. unfold handoff_postfix.
    rewrite collelem_stops_walk_through_pass. reflexivity.
  Qed.

  (* ══════════════ postfix_handoff_only_via_target ══════════════
     (3a) ONE-SIDEDNESS: the post-fix handoff can fire ONLY when the walk actually
     finds a projection target. If the walk returns None_ (any stop, incl. the new
     CollElem stop), the handoff is false — the change can only ever turn a
     would-be handoff into "source keeps the operator", never the reverse. *)
  Theorem postfix_handoff_only_via_target :
    forall es, handoff_postfix es = true -> exists t, walk es = Found t.
  Proof.
    intros es H. unfold handoff_postfix, handoff in H.
    destruct (walk es) as [t|] eqn:Hw.
    - exists t. reflexivity.
    - discriminate.
  Qed.

  (* ══════════════ postfix_le_prefix_handoff ══════════════
     (3b) NO-LOSS (monotone): the post-fix handoff is a SUBSET of the pre-fix
     handoff — adding the CollElem stop only REMOVES handoffs, never adds any.
     (A removed handoff = the source now KEEPS its operator = MORE parses admitted,
     never fewer. The removed handoffs are exactly the erroneous bracket-interior
     ones.) Formally: whenever the post-fix walk finds a target, the pre-fix walk
     finds the SAME target, so post-fix handoff ⇒ pre-fix handoff. *)
  Lemma walk_found_agrees_prefix :
    forall es t, walk es = Found t -> walk_prefix es = Found t.
  Proof.
    induction es as [| e rest IH]; intros t H; simpl in *.
    - discriminate.
    - destruct e; try discriminate.
      + exact H.                    (* Proj t' : both return Found t' *)
      + apply IH; exact H.          (* Pass : recurse on both *)
  Qed.

  Theorem postfix_le_prefix_handoff :
    forall es, handoff_postfix es = true -> handoff_prefix es = true.
  Proof.
    intros es H.
    destruct (postfix_handoff_only_via_target es H) as [t Hw].
    unfold handoff_postfix in H. rewrite Hw in H.
    unfold handoff_prefix. rewrite (walk_found_agrees_prefix es t Hw). exact H.
  Qed.

  (* ══════════════ grouping/ruleslot unchanged ══════════════
     (4) The pre-existing scope-resetting stops are unchanged by the fix. *)
  Theorem grouping_stops_walk :
    forall rest, walk (Grouping :: rest) = None_.
  Proof. intro rest. reflexivity. Qed.

  Theorem ruleslot_stops_walk :
    forall rest, walk (RuleSlot :: rest) = None_.
  Proof. intro rest. reflexivity. Qed.

  (* Nesting: a scope-resetting frame before a Proj shields inner scopes (the
     for-body / grouped-operand precedence soundness, extended to CollElem). *)
  Theorem grouping_before_target_no_handoff :
    forall t rest, handoff_postfix (Grouping :: Proj t :: rest) = false.
  Proof. intros t rest. reflexivity. Qed.

  Theorem collelem_before_target_no_handoff :
    forall t rest, handoff_postfix (CollElem :: Proj t :: rest) = false.
  Proof. intros t rest. reflexivity. Qed.

  (* ══════════════ control: pre-fix finds outer target through CollElem ══════
     (5) The DEFECT witness: WITHOUT the CollElem stop, the walk passes through
     the collection element and finds the OUTER projection target — exactly the
     pre-fix behavior that stole `!` in `@{a!(Nil)}`. This pins the change to the
     single added stop. *)
  Theorem prefix_finds_target_through_collelem :
    forall t rest, walk_prefix (CollElem :: Proj t :: rest) = Found t.
  Proof. intros t rest. reflexivity. Qed.

  (* And with the trace's acceptance profile (src accepts, tgt rejects), the
     pre-fix handoff FIRES (the bug) while the post-fix does not (the fix). *)
  Theorem defect_prefix_handoff_vs_postfix :
    forall t rest,
      src_accepts = true ->
      tgt_accepts t = false ->
      handoff_prefix  (CollElem :: Proj t :: rest) = true
      /\ handoff_postfix (CollElem :: Proj t :: rest) = false.
  Proof.
    intros t rest Hs Ht. split.
    - unfold handoff_prefix. rewrite prefix_finds_target_through_collelem.
      simpl. rewrite Hs, Ht. reflexivity.
    - apply collelem_before_target_no_handoff.
  Qed.

  (* ══════════════ non_collelem_walks_agree ══════════════
     (6) BYTE-IDENTITY for non-collection stacks: on any edge stack whose walk
     never encounters a CollElem before its terminating edge, the post-fix and
     pre-fix walks coincide — the fix adds NO behavioral change outside the
     collection-element case. (Modeled: if the list has no CollElem at all, the
     two walks are equal.) *)
  Fixpoint has_collelem (es : list Edge) : bool :=
    match es with
    | [] => false
    | CollElem :: _ => true
    | _ :: rest => has_collelem rest
    end.

  Theorem non_collelem_walks_agree :
    forall es, has_collelem es = false -> walk es = walk_prefix es.
  Proof.
    induction es as [| e rest IH]; intro H; simpl in *.
    - reflexivity.
    - destruct e; simpl in H.
      + reflexivity.                       (* Proj *)
      + discriminate.                      (* CollElem : excluded by H *)
      + reflexivity.                       (* Grouping *)
      + reflexivity.                       (* RuleSlot *)
      + apply IH; exact H.                 (* Pass *)
  Qed.

  Theorem non_collelem_handoff_agree :
    forall es, has_collelem es = false -> handoff_postfix es = handoff_prefix es.
  Proof.
    intros es H. unfold handoff_postfix, handoff_prefix.
    rewrite (non_collelem_walks_agree es H). reflexivity.
  Qed.

End CollectionElementProjectionBoundary.

(* ══════════════════════════════════════════════════════════════════════════
   Admission audit. Every theorem must be closed under the global context
   (no Admitted, no Axiom; the Section discharges `src_accepts`/`tgt_accepts` as
   universally-quantified hypotheses, NOT axioms). *)
Print Assumptions collelem_stops_walk.
Print Assumptions collelem_stops_walk_through_pass.
Print Assumptions collelem_no_handoff.
Print Assumptions collelem_no_handoff_through_pass.
Print Assumptions postfix_handoff_only_via_target.
Print Assumptions walk_found_agrees_prefix.
Print Assumptions postfix_le_prefix_handoff.
Print Assumptions grouping_stops_walk.
Print Assumptions ruleslot_stops_walk.
Print Assumptions grouping_before_target_no_handoff.
Print Assumptions collelem_before_target_no_handoff.
Print Assumptions prefix_finds_target_through_collelem.
Print Assumptions defect_prefix_handoff_vs_postfix.
Print Assumptions non_collelem_walks_agree.
Print Assumptions non_collelem_handoff_agree.
