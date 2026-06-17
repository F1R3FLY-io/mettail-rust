(*
 * DeterministicPosMirror: the deterministic (singleton) self.pos mirror
 * invariant for the active Prattail WPDA runtime walker.
 *
 * This file models the position-mirror obligation behind the RC-A fix
 * committed at 971efeaf ("Fix RC-A: mirror self.pos in deterministic mode for
 * ConsumeAt* consumes"), in `prattail/src/wpda_walker.rs`
 * (`apply_action_to_cursor`).
 *
 * Background (the runtime fact this models).  In deterministic mode the walker
 * holds a SINGLE active cursor and keeps `self.pos` as a MIRROR of that
 * cursor's `cursor.pos`, so that the next non-fanout `engine.step` re-dispatches
 * at the position the cursor actually reached.  Relative-advance actions keep
 * the mirror for free because they route through `advance_cursor_pos`, which
 * does `if self.deterministic { self.pos = cursor.pos; }`.  The two ABSOLUTE
 * lattice-target consumes used for mixfix following-separators and collection
 * close/sep — `ConsumeAtAndReplace` and `ConsumeAtAndPop` (the #307 ROOT-F
 * variants) — wrote `cursor.pos = next_pos` but FORGOT the mirror.  After such a
 * separator consume (e.g. single-level `1 ? 2 : 3`: cursor.pos 3 -> 4, state
 * advanced) the next step read the STALE `self.pos` (still 3, the un-consumed
 * `:`) and dead-ended.  Ambiguous/multi-level inputs fork into `step_fanout`,
 * which reads each cursor's `cursor.pos` directly, masking the bug — only the
 * single-level unambiguous case stays in deterministic singleton mode end to
 * end.  The fix adds `if self.deterministic { self.pos = next_pos; }` after
 * each absolute write, restoring the mirror.
 *
 * We model only the walker position state needed for this obligation:
 * `self.pos`, the single active `cursor.pos`, and the deterministic flag.  The
 * full `cursor`/`config_key` model in `RuntimeModel.v` carries a per-cursor
 * `ck_pos` but has NO notion of the SEPARATE walker-global `self.pos` mirror
 * that is the entire subject of this proof, so a fresh focused record is the
 * faithful minimal model here.  We mirror RuntimeModel's style: a small record,
 * total state transformers, a `Prop`-valued invariant, preservation lemmas, an
 * explicit necessity (non-vacuity) lemma exhibiting the pre-fix break, and a
 * consequence lemma tying the invariant to the observable next-step read.
 *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

(* ------------------------------------------------------------------ *)
(* Walker position state.                                             *)
(*                                                                    *)
(*   self_pos      : the walker-global `self.pos` (the mirror).        *)
(*   cursor_pos    : the single active cursor's `cursor.pos`.          *)
(*   deterministic : the singleton fast-path flag `self.deterministic`.*)
(* ------------------------------------------------------------------ *)

Record PosState : Type := {
  self_pos : nat;
  cursor_pos : nat;
  deterministic : bool
}.

(* ------------------------------------------------------------------ *)
(* Action variants as state transformers.                            *)
(*                                                                    *)
(* Every transformer ALWAYS writes `cursor.pos`.  In deterministic    *)
(* mode it ALSO writes `self.pos` to the new cursor position (the     *)
(* mirror); in non-deterministic mode `self.pos` is irrelevant        *)
(* (forking paths read `cursor.pos` directly), so it is left          *)
(* untouched — faithfully matching every `if self.deterministic { .. }`*)
(* guard in `apply_action_to_cursor`.                                 *)
(* ------------------------------------------------------------------ *)

(* `advance_cursor_pos(cursor, k)`: relative advance.  `cursor.pos += k`;
   if deterministic then `self.pos := cursor.pos` (= old cursor_pos + k). *)
Definition advance_rel (k : nat) (s : PosState) : PosState :=
  {| self_pos := if deterministic s
                 then cursor_pos s + k
                 else self_pos s;
     cursor_pos := cursor_pos s + k;
     deterministic := deterministic s |}.

(* `ConsumeAtAndReplace` / `ConsumeAtAndPop`, FIXED (the RC-A fix).
   Absolute write `cursor.pos := n`; if deterministic then `self.pos := n`. *)
Definition consume_at (n : nat) (s : PosState) : PosState :=
  {| self_pos := if deterministic s then n else self_pos s;
     cursor_pos := n;
     deterministic := deterministic s |}.

(* `ConsumeAtAndReplace` / `ConsumeAtAndPop`, PRE-FIX (buggy).
   Absolute write `cursor.pos := n` ONLY; the mirror is FORGOTTEN, so
   `self.pos` keeps its stale value even in deterministic mode. *)
Definition consume_at_buggy (n : nat) (s : PosState) : PosState :=
  {| self_pos := self_pos s;
     cursor_pos := n;
     deterministic := deterministic s |}.

(* `ParsePredicate`: absolute write that ALREADY mirrors in deterministic mode
   (one of the sibling actions the RC-A commit cites as already-correct). *)
Definition parse_predicate (n : nat) (s : PosState) : PosState :=
  {| self_pos := if deterministic s then n else self_pos s;
     cursor_pos := n;
     deterministic := deterministic s |}.

(* `IterativeChainAbsorb` end position `e`: absolute write that ALREADY mirrors
   in deterministic mode (the other already-correct absolute sibling). *)
Definition chain_absorb (e : nat) (s : PosState) : PosState :=
  {| self_pos := if deterministic s then e else self_pos s;
     cursor_pos := e;
     deterministic := deterministic s |}.

(* ------------------------------------------------------------------ *)
(* The mirror invariant.                                             *)
(*                                                                    *)
(*   In deterministic (singleton) mode, `self.pos` equals the active  *)
(*   cursor's `cursor.pos`.  (In non-deterministic mode the next step  *)
(*   fans out and reads `cursor.pos` directly, so the invariant places *)
(*   no obligation on `self.pos`.)                                     *)
(* ------------------------------------------------------------------ *)

Definition inv (s : PosState) : Prop :=
  deterministic s = true -> self_pos s = cursor_pos s.

(* ================================================================== *)
(* Preservation: every action carrying the fix preserves `inv`.       *)
(* ================================================================== *)

Theorem consume_at_preserves_inv :
  forall s n, inv s -> inv (consume_at n s).
Proof.
  intros s n _Hinv.
  unfold inv, consume_at; simpl.
  intros Hdet.
  rewrite Hdet.
  reflexivity.
Qed.

Theorem advance_rel_preserves_inv :
  forall s k, inv s -> inv (advance_rel k s).
Proof.
  intros s k _Hinv.
  unfold inv, advance_rel; simpl.
  intros Hdet.
  rewrite Hdet.
  reflexivity.
Qed.

Theorem parse_predicate_preserves_inv :
  forall s n, inv s -> inv (parse_predicate n s).
Proof.
  intros s n _Hinv.
  unfold inv, parse_predicate; simpl.
  intros Hdet.
  rewrite Hdet.
  reflexivity.
Qed.

Theorem chain_absorb_preserves_inv :
  forall s e, inv s -> inv (chain_absorb e s).
Proof.
  intros s e _Hinv.
  unfold inv, chain_absorb; simpl.
  intros Hdet.
  rewrite Hdet.
  reflexivity.
Qed.

(* For completeness, `inv` holds unconditionally after any fixed absolute
   consume in deterministic mode: both fields become `n`. *)
Theorem consume_at_establishes_mirror :
  forall s n,
    deterministic s = true ->
    self_pos (consume_at n s) = cursor_pos (consume_at n s).
Proof.
  intros s n Hdet.
  unfold consume_at; simpl.
  rewrite Hdet.
  reflexivity.
Qed.

(* ================================================================== *)
(* Necessity / non-vacuity: the PRE-FIX absolute consume BREAKS `inv`. *)
(*                                                                    *)
(* We exhibit a concrete deterministic state satisfying `inv` and a   *)
(* target `n <> cursor_pos`, and show the buggy consume violates       *)
(* `inv`.  This is the exact `1 ? 2 : 3` scenario: deterministic mode, *)
(* mirror holds (self_pos = cursor_pos = 3), the `:` separator consume  *)
(* targets n = 4, and the un-mirrored `self.pos` (still 3) breaks the   *)
(* invariant — which is why the next step re-dispatched at the stale    *)
(* `:`.  This proves the mirror is genuinely required: the proof is not *)
(* decorative.                                                          *)
(* ================================================================== *)

Definition ternary_sep_state : PosState :=
  {| self_pos := 3; cursor_pos := 3; deterministic := true |}.

Theorem buggy_consume_breaks_inv :
  exists s n,
    deterministic s = true /\
    inv s /\
    n <> cursor_pos s /\
    ~ inv (consume_at_buggy n s).
Proof.
  exists ternary_sep_state, 4.
  split; [| split; [| split]].
  - (* deterministic ternary_sep_state = true *)
    reflexivity.
  - (* inv s: self_pos = cursor_pos = 3 holds in deterministic mode *)
    unfold inv, ternary_sep_state; simpl.
    intros _; reflexivity.
  - (* n = 4 <> cursor_pos s = 3 *)
    unfold ternary_sep_state; simpl.
    discriminate.
  - (* ~ inv (buggy): deterministic stays true, self_pos stays 3, cursor_pos
       becomes 4, so the required 3 = 4 is absurd. *)
    unfold inv, consume_at_buggy, ternary_sep_state; simpl.
    intros Hbad.
    specialize (Hbad eq_refl).
    discriminate Hbad.
Qed.

(* The FIXED consume on the SAME state does preserve `inv`, completing the
   contrast (fix is sufficient where the bug was necessary). *)
Theorem fixed_consume_preserves_inv_on_ternary :
  inv (consume_at 4 ternary_sep_state).
Proof.
  apply consume_at_preserves_inv.
  unfold ternary_sep_state, inv; simpl.
  intros _; reflexivity.
Qed.

(* ================================================================== *)
(* Consequence: the invariant determines the observable next-step read. *)
(*                                                                      *)
(* The next non-fanout `engine.step` re-dispatches at `self.pos`.  We    *)
(* model that read as `next_step_read_pos s := self_pos s` and show:     *)
(*   - under the FIX, after a separator consume to `next_pos` in          *)
(*     deterministic mode, the next step reads exactly the CONSUMED       *)
(*     position (= cursor_pos = next_pos);                                *)
(*   - under the PRE-FIX consume, that read can DIFFER from `next_pos`    *)
(*     (the stale read that caused the dead-end).                         *)
(* This ties the invariant to the observable bug.                        *)
(* ================================================================== *)

Definition next_step_read_pos (s : PosState) : nat := self_pos s.

Theorem mirror_means_next_step_reads_consumed_pos :
  forall s next_pos,
    deterministic s = true ->
    next_step_read_pos (consume_at next_pos s) = cursor_pos (consume_at next_pos s)
    /\ next_step_read_pos (consume_at next_pos s) = next_pos.
Proof.
  intros s next_pos Hdet.
  unfold next_step_read_pos, consume_at; simpl.
  rewrite Hdet.
  split; reflexivity.
Qed.

(* Pre-fix counterpart: there is a concrete deterministic state and a consume
   target `next_pos` for which the next step reads a position OTHER than the
   one just consumed — the stale `self.pos` that dead-ended `1 ? 2 : 3`. *)
Theorem buggy_next_step_reads_stale_pos :
  exists s next_pos,
    deterministic s = true /\
    inv s /\
    next_step_read_pos (consume_at_buggy next_pos s) <> next_pos /\
    next_step_read_pos (consume_at_buggy next_pos s)
      <> cursor_pos (consume_at_buggy next_pos s).
Proof.
  exists ternary_sep_state, 4.
  split; [| split; [| split]].
  - (* deterministic ternary_sep_state = true *)
    reflexivity.
  - (* inv s holds *)
    unfold inv, ternary_sep_state; simpl.
    intros _; reflexivity.
  - (* read = self_pos = 3 <> next_pos = 4 *)
    unfold next_step_read_pos, consume_at_buggy, ternary_sep_state; simpl.
    discriminate.
  - (* read = 3 <> cursor_pos = 4 *)
    unfold next_step_read_pos, consume_at_buggy, ternary_sep_state; simpl.
    discriminate.
Qed.

(* ================================================================== *)
(* Assumption audit: the three required main theorems must each be     *)
(* closed under the global context (no Admitted/admit/Axiom/Parameter).*)
(* ================================================================== *)

Print Assumptions consume_at_preserves_inv.
Print Assumptions buggy_consume_breaks_inv.
Print Assumptions mirror_means_next_step_reads_consumed_pos.
