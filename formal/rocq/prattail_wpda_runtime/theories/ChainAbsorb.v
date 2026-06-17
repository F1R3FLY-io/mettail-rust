(*
 * ChainAbsorb: abstract obligations for IterativeChainAbsorb.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From PrattailWpdaRuntime Require Import RuntimeModel.

Import ListNotations.
Local Open Scope bool_scope.

Inductive assoc : Type :=
  | LeftAssoc
  | RightAssoc
  | MixfixAssoc.

Record span : Type := {
  span_lo : nat;
  span_hi : nat
}.

Definition strictly_inside (sp : span) (pos : nat) : Prop :=
  span_lo sp < pos /\ pos < span_hi sp.

Record chain_spec : Type := {
  op_cat_src_idx : nat;
  op_rule_idx : nat;
  chain_assoc : assoc;
  step_weight : nat
}.

Fixpoint iter_weight (n step : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => step + iter_weight n' step
  end.

Lemma iter_weight_mul :
  forall n step,
    iter_weight n step = n * step.
Proof.
  induction n as [| n IH]; intros step.
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.

Inductive ordinary_chain (spec : chain_spec) : nat -> nat -> Prop :=
  | ordinary_zero :
      ordinary_chain spec 0 0
  | ordinary_step :
      forall n w,
        ordinary_chain spec n w ->
        ordinary_chain spec (S n) (step_weight spec + w).

Record absorb_result : Type := {
  ar_span : span;
  ar_weight : nat;
  ar_state : control
}.

Definition absorb_chain (spec : chain_spec) (start len : nat) : absorb_result :=
  {| ar_span := {| span_lo := start; span_hi := start + len |};
     ar_weight := iter_weight len (step_weight spec);
     ar_state := Unwinding |}.

Theorem absorb_chain_matches_ordinary_weight :
  forall spec start len,
    ordinary_chain spec len (ar_weight (absorb_chain spec start len)).
Proof.
  intros spec start len.
  induction len as [| len IH].
  - constructor.
  - simpl. constructor. exact IH.
Qed.

Theorem absorb_chain_records_span :
  forall spec start len,
    span_lo (ar_span (absorb_chain spec start len)) = start /\
    span_hi (ar_span (absorb_chain spec start len)) = start + len.
Proof.
  intros. split; reflexivity.
Qed.

Theorem absorb_chain_enters_unwinding :
  forall spec start len,
    ar_state (absorb_chain spec start len) = Unwinding.
Proof.
  intros. reflexivity.
Qed.

Definition cross_cat_allowed (intervals : list span) (pos : nat) : Prop :=
  forall sp, In sp intervals -> ~ strictly_inside sp pos.

Lemma absorbed_interval_suppresses_strict_interior :
  forall sp pos,
    strictly_inside sp pos ->
    ~ cross_cat_allowed [sp] pos.
Proof.
  intros sp pos Hinside Hallowed.
  specialize (Hallowed sp).
  assert (Hin : In sp [sp]) by (left; reflexivity).
  specialize (Hallowed Hin).
  contradiction.
Qed.

Lemma absorbed_interval_allows_left_boundary :
  forall sp,
    ~ strictly_inside sp (span_lo sp).
Proof.
  intros sp [Hlt _].
  lia.
Qed.

Lemma absorbed_interval_allows_right_boundary :
  forall sp,
    ~ strictly_inside sp (span_hi sp).
Proof.
  intros sp [_ Hlt].
  lia.
Qed.

Record interval_key : Type := {
  ik_category : nat;
  ik_rule : nat
}.

Record keyed_span : Type := {
  ks_key : interval_key;
  ks_span : span
}.

Definition keyed_cross_cat_allowed
    (intervals : list keyed_span)
    (key : interval_key)
    (pos : nat) : Prop :=
  forall entry,
    In entry intervals ->
    ks_key entry = key ->
    ~ strictly_inside (ks_span entry) pos.

Lemma keyed_absorbed_interval_suppresses_matching_strict_interior :
  forall key sp pos,
    strictly_inside sp pos ->
    ~ keyed_cross_cat_allowed
        [{| ks_key := key; ks_span := sp |}]
        key
        pos.
Proof.
  intros key sp pos Hinside Hallowed.
  specialize
    (Hallowed {| ks_key := key; ks_span := sp |}).
  assert (Hin :
    In {| ks_key := key; ks_span := sp |}
      [{| ks_key := key; ks_span := sp |}])
    by (left; reflexivity).
  specialize (Hallowed Hin eq_refl).
  contradiction.
Qed.

Lemma keyed_absorbed_interval_allows_unrelated_key :
  forall stored query sp pos,
    stored <> query ->
    keyed_cross_cat_allowed
      [{| ks_key := stored; ks_span := sp |}]
      query
      pos.
Proof.
  intros stored query sp pos Hneq entry Hin Hkey Hinside.
  destruct Hin as [Heq | []].
  subst entry.
  simpl in Hkey.
  apply Hneq.
  exact Hkey.
Qed.

(* ================================================================= *)
(*  RC-B (2026-06-17): pop-site prefix-cast wrap reconciliation.      *)
(*                                                                    *)
(*  Models the fix in `prattail/src/wpda_walker.rs`                   *)
(*  (`try_stage_prefix_cast_wrap` / `synthesize_prefix_cast_wrap_     *)
(*   cursor`): when a full-span well-typed `C_in` body rests at a     *)
(*  trigger-bearing prefix cast's structural close, and a cast        *)
(*  `C_in -> C_out` exists in the category graph, and the cast is     *)
(*  genuinely UNFIRED on this lineage, the reconciliation fires the   *)
(*  cast over the body forming `Symbol(C_out, lo, hi)`.               *)
(*                                                                    *)
(*  The two correctness obligations of design §8:                     *)
(*   (a) it fires IFF the type-witness predicate holds — so off the   *)
(*       gate the cursor set is unchanged (+0 cursors / parser        *)
(*       identity on the passing corpus, where the cast already fired *)
(*       so the `unfired` conjunct is false); and                     *)
(*   (b) it does NOT mask an ill-typed body — an ill-typed body never *)
(*       assembles the full-span well-typed `C_in` symbol the         *)
(*       predicate requires, so the predicate is false and nothing    *)
(*       fires.                                                        *)
(*                                                                    *)
(*  Zero-admission; `Print Assumptions` at the end of the section     *)
(*  reports "Closed under the global context".                        *)
(* ================================================================= *)

(* The SPPF Symbol the body cursor rests on at the cast close: its    *)
(* result category and its span `[bs_lo, bs_hi)`.                     *)
Record body_symbol : Type := {
  bs_cat : nat;
  bs_lo  : nat;
  bs_hi  : nat
}.

(* The cast frame the body sits under: the enclosing prefix-cast      *)
(* output category, the cast's input position (the trigger `lo`), and *)
(* the structural-close position past `)`. `cf_trigger_lo` is the     *)
(* result span start and `cf_close_hi` its end.                       *)
Record cast_frame : Type := {
  cf_out_cat    : nat;
  cf_trigger_lo : nat;
  cf_close_hi   : nat;
  (* The body actually rests at the structural close (the next token  *)
  (* is the cast's `)`). True on the bug path; the walker checks       *)
  (* `is_structural_close_delimiter` at drain time.                    *)
  cf_at_close   : bool
}.

(* The category-graph query the engine answers (`prefix_cast_into`):  *)
(* `Some out_rule` iff a TRIGGER-BEARING single-arg cast               *)
(* `in_cat -> out_cat` exists (e.g. `BoolToInt`). Modeled as an        *)
(* abstract decidable table parameter; the walker re-validates each   *)
(* hit, so soundness here only needs that the relation is the one the *)
(* walker keys on.                                                     *)
Definition cast_graph := nat -> nat -> option nat.

(* The result SPPF symbol of firing a cast `in -> out` over a body:   *)
(* `Symbol(out_cat, trigger_lo, close_hi)` — the WHOLE `kw "(" ... ")"`*)
(* span, NOT the body span (the trigger + brackets are accounted).    *)
Definition cast_wrap_result (out_cat lo hi : nat) : body_symbol :=
  {| bs_cat := out_cat; bs_lo := lo; bs_hi := hi |}.

(* THE TYPE-WITNESS PREDICATE (the whole gate). Fires iff:            *)
(*  1. the resting body's result cat is `C_in` (well-typed witness);  *)
(*  2. the body spans the FULL delegate body — it starts at the cast  *)
(*     trigger position and rests at the close (`bs_lo = trigger_lo`   *)
(*     and `bs_hi = close_hi - 1`... here modeled as the body covering *)
(*     `[trigger_lo, close_hi)` boundary, i.e. `bs_lo = cf_trigger_lo` *)
(*     and `bs_hi + 1 = cf_close_hi` for the single closing token);    *)
(*  3. the cursor truly rests at the structural close;                *)
(*  4. a cast `C_in -> C_out` exists in the category graph;           *)
(*  5. the cast is UNFIRED on this lineage (no existing wrap packing). *)
Definition admit_prefix_cast_wrap
    (g : cast_graph) (c_in : nat)
    (body : body_symbol) (frame : cast_frame) (fired : bool) : bool :=
  (bs_cat body =? c_in) &&
  (bs_lo body =? cf_trigger_lo frame) &&
  (S (bs_hi body) =? cf_close_hi frame) &&
  cf_at_close frame &&
  (match g c_in (cf_out_cat frame) with Some _ => true | None => false end) &&
  (negb fired).

(* The reconciliation's effect: when the gate holds, it produces      *)
(* exactly the cast-wrap result symbol (and adds NO other cursor);    *)
(* otherwise it produces nothing. `option body_symbol` models         *)
(* "resolve the one existing body into the wrapped symbol" vs "no-op".*)
Definition run_prefix_cast_wrap
    (g : cast_graph) (c_in : nat)
    (body : body_symbol) (frame : cast_frame) (fired : bool)
    : option body_symbol :=
  if admit_prefix_cast_wrap g c_in body frame fired then
    Some (cast_wrap_result (cf_out_cat frame) (cf_trigger_lo frame) (cf_close_hi frame))
  else
    None.

(* ── (Obligation a) FIRES IFF THE PREDICATE HOLDS. ──────────────── *)

Theorem prefix_cast_wrap_fires_iff_witness :
  forall g c_in body frame fired result,
    run_prefix_cast_wrap g c_in body frame fired = Some result <->
    (admit_prefix_cast_wrap g c_in body frame fired = true /\
     result = cast_wrap_result (cf_out_cat frame)
                               (cf_trigger_lo frame) (cf_close_hi frame)).
Proof.
  intros g c_in body frame fired result.
  unfold run_prefix_cast_wrap.
  destruct (admit_prefix_cast_wrap g c_in body frame fired) eqn:Hadmit.
  - split.
    + intros Hsome. inversion Hsome. split; [reflexivity | reflexivity].
    + intros [_ Hres]. rewrite Hres. reflexivity.
  - split.
    + intros Hcontra. discriminate Hcontra.
    + intros [Hcontra _]. discriminate Hcontra.
Qed.

(* +0 CURSORS / PARSER IDENTITY OFF THE GATE: when the predicate is   *)
(* false (the passing corpus — the cast already fired, so `fired =    *)
(* true` makes `negb fired = false`), the reconciliation is a no-op   *)
(* (produces None) — the cursor set is unchanged.                     *)
Theorem prefix_cast_wrap_noop_off_gate :
  forall g c_in body frame fired,
    admit_prefix_cast_wrap g c_in body frame fired = false ->
    run_prefix_cast_wrap g c_in body frame fired = None.
Proof.
  intros g c_in body frame fired Hfalse.
  unfold run_prefix_cast_wrap.
  rewrite Hfalse.
  reflexivity.
Qed.

(* The concrete passing-corpus instance: a cast that ALREADY fired    *)
(* (`fired = true`) never re-fires, regardless of every other field.  *)
(* This is the exact `+0`-cursor guarantee: the `unfired` conjunct    *)
(* `negb fired` is false, so the whole gate is false.                 *)
Theorem already_fired_cast_never_refires :
  forall g c_in body frame,
    run_prefix_cast_wrap g c_in body frame true = None.
Proof.
  intros g c_in body frame.
  apply prefix_cast_wrap_noop_off_gate.
  unfold admit_prefix_cast_wrap.
  (* `negb true = false` collapses the final conjunct, hence the AND. *)
  rewrite Bool.andb_false_r.
  reflexivity.
Qed.

(* ── (Obligation b) DOES NOT MASK AN ILL-TYPED BODY. ────────────── *)

(* An ill-typed cast body never assembles a full-span well-typed      *)
(* `C_in` symbol resting at the close: either its result cat is not   *)
(* `C_in` (no `C_in` witness — the canonical ill-typed case, e.g.     *)
(* `int(2 <= b >= 3)` whose inner `2 <= b` is `Int <= Bool`, so no    *)
(* full-span `Bool` exists), or it does not span the full delegate    *)
(* body / does not rest at the close. In every such case the gate is  *)
(* false, so nothing fires and the input correctly stays failing.     *)
Theorem ill_typed_body_wrong_cat_does_not_fire :
  forall g c_in body frame fired,
    bs_cat body <> c_in ->
    run_prefix_cast_wrap g c_in body frame fired = None.
Proof.
  intros g c_in body frame fired Hneq.
  apply prefix_cast_wrap_noop_off_gate.
  unfold admit_prefix_cast_wrap.
  assert (Hbeq : (bs_cat body =? c_in) = false).
  { apply Nat.eqb_neq. exact Hneq. }
  rewrite Hbeq. simpl. reflexivity.
Qed.

(* A body that does not span the full delegate (its left edge is not  *)
(* the cast trigger position) likewise never fires — the wrap can only *)
(* span the WHOLE `kw "(" ... ")"`, so a partial body is rejected.    *)
Theorem partial_span_body_does_not_fire :
  forall g c_in body frame fired,
    bs_lo body <> cf_trigger_lo frame ->
    run_prefix_cast_wrap g c_in body frame fired = None.
Proof.
  intros g c_in body frame fired Hneq.
  apply prefix_cast_wrap_noop_off_gate.
  unfold admit_prefix_cast_wrap.
  assert (Hbeq : (bs_lo body =? cf_trigger_lo frame) = false).
  { apply Nat.eqb_neq. exact Hneq. }
  rewrite Hbeq.
  (* The second conjunct is false; the AND collapses. *)
  rewrite Bool.andb_false_r. simpl. reflexivity.
Qed.

(* A body not resting at the structural close never fires. *)
Theorem not_at_close_does_not_fire :
  forall g c_in body frame fired,
    cf_at_close frame = false ->
    run_prefix_cast_wrap g c_in body frame fired = None.
Proof.
  intros g c_in body frame fired Hnc.
  apply prefix_cast_wrap_noop_off_gate.
  unfold admit_prefix_cast_wrap.
  rewrite Hnc.
  rewrite Bool.andb_false_r. simpl. reflexivity.
Qed.

(* When no cast `C_in -> C_out` exists in the category graph, nothing *)
(* fires (the category-graph witness conjunct is false). *)
Theorem no_cast_in_graph_does_not_fire :
  forall g c_in body frame fired,
    g c_in (cf_out_cat frame) = None ->
    run_prefix_cast_wrap g c_in body frame fired = None.
Proof.
  intros g c_in body frame fired Hnone.
  apply prefix_cast_wrap_noop_off_gate.
  unfold admit_prefix_cast_wrap.
  rewrite Hnone.
  rewrite Bool.andb_false_r. simpl. reflexivity.
Qed.

(* ── POSITIVE WITNESS (non-vacuity): the bug input DOES fire. ────── *)
(* `int(b >= 2 <= b >= 3)`: a well-typed `Bool` body (cat = 7) spans  *)
(* `[2,12)` resting at `)` (close at 13), the cast `Bool(7) -> Int(2)`*)
(* (`BoolToInt`) exists in the graph, and it is unfired. The          *)
(* reconciliation fires, forming `Int[2..]` over the WHOLE `int(...)`  *)
(* span `[0,13)`. This proves the gate is satisfiable (the fix is     *)
(* non-vacuous) and yields exactly the `BoolToInt`-shaped result.     *)
Definition calc_cast_graph : cast_graph :=
  fun c_in c_out =>
    if (c_in =? 7) && (c_out =? 2) then Some 16 else None.

Theorem rc_b_bug_input_fires_bool_to_int :
  run_prefix_cast_wrap calc_cast_graph 7
    {| bs_cat := 7; bs_lo := 0; bs_hi := 12 |}
    {| cf_out_cat := 2; cf_trigger_lo := 0; cf_close_hi := 13;
       cf_at_close := true |}
    false
  = Some {| bs_cat := 2; bs_lo := 0; bs_hi := 13 |}.
Proof.
  unfold run_prefix_cast_wrap, admit_prefix_cast_wrap, calc_cast_graph,
    cast_wrap_result.
  simpl.
  reflexivity.
Qed.

Print Assumptions prefix_cast_wrap_fires_iff_witness.
Print Assumptions prefix_cast_wrap_noop_off_gate.
Print Assumptions already_fired_cast_never_refires.
Print Assumptions ill_typed_body_wrong_cat_does_not_fire.
Print Assumptions partial_span_body_does_not_fire.
Print Assumptions not_at_close_does_not_fire.
Print Assumptions no_cast_in_graph_does_not_fire.
Print Assumptions rc_b_bug_input_fires_bool_to_int.
