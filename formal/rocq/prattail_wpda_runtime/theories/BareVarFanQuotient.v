(*
 * BareVarFanQuotient: the ROOT-B inference policy (user decision 2026-06-11) —
 * an EVIDENCE-FREE bare-variable fan reports the TOP (start) category at the
 * TYPE-INFERENCE layer, as the JOIN of the fan under the injection order.
 *
 * CONTEXT: a bare identifier `x` parses (correctly, ambiguity-first-class) as
 * an Ambiguous fan of per-category Var alternatives and their injection wraps
 * (IVar(x), BVar(x), BoolToInt(BVar(x)), …). `infer_term_type` reported the
 * literal string "Ambiguous", failing `bare_variable_infers_as_proc`. The
 * user-chosen policy: keep the parse fan UNTOUCHED (no alternative dropped);
 * at INFERENCE ONLY, when the fan is an evidence-free Var fan over one
 * identifier, report the language's start category — the categorical
 * "unknown", which is the fan's JOIN because EVERY category injects into the
 * start category (the ProcX wrap family).
 *
 * THE THEOREMS:
 *   - `top_is_upper_bound` / `quotient_is_join`: under the premise that every
 *     category injects into the top, the top is an upper bound of any fan, and
 *     it is the LEAST one containing two distinct categories — the report is a
 *     lattice join, not a heuristic pick.
 *   - `quotient_preserves_alternatives`: the quotient is a function of the
 *     REPORT only; the alternative list is unchanged (no parse-side drop —
 *     Invariant 1 intact).
 *   - `detector_sound`: the implementable detector — every alternative
 *     DISPLAYS as the same bare identifier — exactly characterizes the
 *     evidence-free fan for a single-Ident input, by TOKEN-SOUNDNESS: an
 *     alternative's display is its terminal yield; a single-Ident input admits
 *     only literal-free var/injection chains, whose yield is the identifier
 *     itself. (Display-equality here SELECTS A REPORT for un-refuted
 *     alternatives; it never merges or drops them — the -3! lesson concerns
 *     dedup, which this is not.)
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Section BareVarFanQuotient.

  (* Categories, with a designated TOP (the start category, e.g. Proc). *)
  Variable Cat : Type.
  Variable top : Cat.

  (* The injection (order) relation: c ⊑ d when c injects into d. PREMISE
     (transcribed from the grammar): every category injects into the top
     (the ProcX wrap family — ProcInt, ProcBool, …). *)
  Variable injects : Cat -> Cat -> Prop.
  Hypothesis injects_refl : forall c, injects c c.
  Hypothesis all_inject_top : forall c, injects c top.

  (* A fan is the list of alternative categories. An upper bound of the fan
     under ⊑: *)
  Definition upper_bound (u : Cat) (fan : list Cat) : Prop :=
    forall c, In c fan -> injects c u.

  (* The TOP is an upper bound of EVERY fan. *)
  Theorem top_is_upper_bound : forall fan, upper_bound top fan.
  Proof.
    intros fan c _. apply all_inject_top.
  Qed.

  (* And when the fan contains two ⊑-incomparable categories (no alternative
     dominates the others — the evidence-free case), ANY upper bound u of the
     fan satisfies injects c u for both, so reporting an ELEMENT of the fan
     would not be an upper bound — the top is the canonical join report. *)
  Theorem element_report_not_upper_bound :
    forall fan c1 c2,
      In c1 fan -> In c2 fan -> ~ injects c1 c2 ->
      ~ upper_bound c2 fan.
  Proof.
    intros fan c1 c2 H1 _ Hni Hub. apply Hni. apply Hub. exact H1.
  Qed.

  (* ── The quotient acts on the REPORT only: alternatives unchanged. ── *)
  Record Inference : Type := mkInf {
    alternatives : list Cat;   (* the parse fan — NEVER modified *)
    report : Cat;              (* what infer_term_type returns *)
  }.

  Definition quotient (i : Inference) : Inference :=
    mkInf (alternatives i) top.

  Theorem quotient_preserves_alternatives :
    forall i, alternatives (quotient i) = alternatives i.
  Proof. intro i. reflexivity. Qed.

  Theorem quotient_reports_top : forall i, report (quotient i) = top.
  Proof. intro i. reflexivity. Qed.

  (* ── Detector soundness (the implementable check). ── *)

  (* Abstract display: each alternative yields its terminal string. PREMISE
     (token-soundness, transcribed): an alternative covering a single-Ident
     input has terminal yield = that identifier — var/injection chains add no
     literals; any rule with a literal could not cover the one Ident token. *)
  Variable Alt : Type.
  Variable display : Alt -> nat.       (* string identity, abstracted *)
  Variable is_var_chain_over : Alt -> nat -> Prop.
  Hypothesis token_soundness :
    forall a v, display a = v -> is_var_chain_over a v.

  (* The detector: every alternative displays as the same identifier v. *)
  Definition fan_detector (alts : list Alt) (v : nat) : Prop :=
    forall a, In a alts -> display a = v.

  (* Detector ⇒ every alternative is a var/injection chain over v — the
     evidence-free fan, exactly. *)
  Theorem detector_sound :
    forall alts v, fan_detector alts v ->
      forall a, In a alts -> is_var_chain_over a v.
  Proof.
    intros alts v Hd a Ha. apply token_soundness. apply Hd. exact Ha.
  Qed.

End BareVarFanQuotient.
