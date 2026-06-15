(*
 * RhoGuardedCommSoundness: soundness of a Rho guarded receive whose guard is a
 * mixed structural × behavioral product (the unified guard of the symbolic-
 * predicate generalization). Composes with `GuardedCommSoundness.v` (the
 * Codex-side atomic-commit obligation) by supplying the concrete bool guard from
 * the product evaluation, and with the upstream report compiler
 * (`dovetail/formal/.../GeneratedReportCompiler.v`): only `LoweredAsDovetailRule`
 * rules reach guard coverage, so these guard-soundness theorems apply exactly to
 * the lowered, guard-covered rules.
 *
 * The guard has two legs:
 *   - a CLASSICAL structural leg (`structural_eval`), decided exactly;
 *   - a REJECT-SAFE behavioral leg (`behavioral_eval`), a SOUND under-approximation
 *     of the true behavioral property (`behavioral_true`) — it may conservatively
 *     reject (the Sat3::DontKnow / Heyting boundary) but never wrongly accept.
 * `behavioral_neg` is the reject-safe complement (also a sound under-approximation
 * of `¬behavioral_true`). These are the runtime mirrors of the Rust
 * `RejectSafeProduct` (algebra_tower.rs) and the Coq `BehavioralNegation.v`.
 *
 * Main results (zero-admission):
 *   - `comm_fires_iff` : a guarded Comm fires iff names match AND the product
 *     guard evaluates true (the firing factorization).
 *   - `comm_fires_implies_true_guard` : a fired Comm satisfies the TRUE guard
 *     (structural ∧ behavioral_true) — the reject-safe guard never wrongly admits
 *     a Comm (sound; false negatives only).
 *   - `mixed_negation_soundness` : if the asymmetric complement fires, the true
 *     product property rejects (the De Morgan reject-safety, runtime form).
 *   - `rho_complement_no_commit` : composing with
 *     `GuardedCommSoundness.failed_guard_no_commit` — when the complement fires,
 *     the guarded attempt commits nothing and consumes no facts.
 *   - `rho_guard_true_commits` : composing with
 *     `GuardedCommSoundness.true_guard_enabled_adds_output` — a satisfied guard
 *     over present premises commits and adds the output.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From RhoBridge Require Import GuardedCommSoundness.

Import ListNotations.

Section RhoGuardedCommSoundness.

  (* A substitution σ from a guarded-receive match; the guard legs and the
     name-match condition decide on it. *)
  Variable Subst : Type.
  Variable name_match : Subst -> bool.
  Variable structural_eval : Subst -> bool.
  Variable behavioral_eval : Subst -> bool.

  (* The true (semantic) behavioral property the reject-safe leg approximates. *)
  Variable behavioral_true : Subst -> bool.
  Hypothesis behavioral_sound :
    forall s, behavioral_eval s = true -> behavioral_true s = true.

  (* The reject-safe complement of the behavioral leg: a sound under-approximation
     of ¬behavioral_true (the Heyting pseudo-complement / Sat3 negation). *)
  Variable behavioral_neg : Subst -> bool.
  Hypothesis behavioral_neg_sound :
    forall s, behavioral_neg s = true -> behavioral_true s = false.

  (* The product guard's runtime evaluation (structural ∧ behavioral). *)
  Definition product_eval (s : Subst) : bool := structural_eval s && behavioral_eval s.

  (* The TRUE product property (structural ∧ behavioral_true). *)
  Definition product_true (s : Subst) : bool := structural_eval s && behavioral_true s.

  (* A guarded Comm fires iff the names match and the product guard evaluates true. *)
  Definition comm_fires (s : Subst) : bool := name_match s && product_eval s.

  Theorem comm_fires_iff : forall s,
    comm_fires s = true <-> (name_match s = true /\ product_eval s = true).
  Proof.
    intro s. unfold comm_fires. apply andb_true_iff.
  Qed.

  (* The product evaluation is SOUND w.r.t. the true property: a firing guard
     certifies the true property holds. *)
  Theorem product_eval_sound : forall s, product_eval s = true -> product_true s = true.
  Proof.
    intro s. unfold product_eval, product_true.
    rewrite !andb_true_iff. intros [Hs Hb]. split.
    - exact Hs.
    - apply behavioral_sound. exact Hb.
  Qed.

  (* Hence a fired Comm satisfies the true guard — never wrongly admits a Comm. *)
  Theorem comm_fires_implies_true_guard : forall s,
    comm_fires s = true -> name_match s = true /\ product_true s = true.
  Proof.
    intro s. intro H. apply comm_fires_iff in H. destruct H as [Hn Hp].
    split; [exact Hn | apply product_eval_sound; exact Hp].
  Qed.

  (* The asymmetric De Morgan complement: ¬structural ∨ behavioral_neg. *)
  Definition product_neg (s : Subst) : bool :=
    negb (structural_eval s) || behavioral_neg s.

  (* Reject-safety (runtime mirror of BehavioralNegation.mixed_negation_soundness):
     if the complement fires, the TRUE product property rejects. *)
  Theorem mixed_negation_soundness : forall s,
    product_neg s = true -> product_true s = false.
  Proof.
    intro s. unfold product_neg, product_true. rewrite orb_true_iff.
    intros [H | H].
    - apply negb_true_iff in H. rewrite H. reflexivity.
    - apply behavioral_neg_sound in H. rewrite H. apply andb_false_r.
  Qed.

  (* The complement firing forces the runtime guard to reject too (since
     product_eval under-approximates product_true). *)
  Theorem product_neg_forces_reject : forall s,
    product_neg s = true -> product_eval s = false.
  Proof.
    intro s. intro H.
    destruct (product_eval s) eqn:E; [|reflexivity].
    apply product_eval_sound in E.
    apply mixed_negation_soundness in H. rewrite H in E. discriminate.
  Qed.

  (* The Rho guarded rule whose bool guard is the product evaluation at σ. *)
  Definition rho_guarded_rule (premises : list Fact) (s : Subst) (output : Fact)
    : GuardedRule :=
    {| guarded_premises := premises;
       guarded_guard := product_eval s;
       guarded_output := output |}.

  (* COMPOSITION with GuardedCommSoundness.failed_guard_no_commit: when the
     asymmetric complement fires, the guarded attempt commits nothing and consumes
     no facts — the reject-safe guard never wrongly admits a Comm. *)
  Theorem rho_complement_no_commit :
    forall premises s output facts next,
      product_neg s = true ->
      guarded_attempt facts (rho_guarded_rule premises s output) next ->
      next = facts.
  Proof.
    intros premises s output facts next Hneg Hattempt.
    apply (failed_guard_no_commit facts (rho_guarded_rule premises s output) next).
    - simpl. apply product_neg_forces_reject. exact Hneg.
    - exact Hattempt.
  Qed.

  (* COMPOSITION with true_guard_enabled_adds_output: a satisfied guard over
     present premises commits and adds the output. *)
  Theorem rho_guard_true_commits :
    forall premises s output facts,
      all_present facts premises ->
      product_eval s = true ->
      exists next,
        guarded_attempt facts (rho_guarded_rule premises s output) next
        /\ In output next.
  Proof.
    intros premises s output facts Hpresent Heval.
    destruct (true_guard_enabled_adds_output facts (rho_guarded_rule premises s output))
      as [next [Hattempt Hin]].
    - simpl. exact Hpresent.
    - simpl. exact Heval.
    - exists next. split; [exact Hattempt | exact Hin].
  Qed.

End RhoGuardedCommSoundness.

Print Assumptions comm_fires_iff.
Print Assumptions comm_fires_implies_true_guard.
Print Assumptions mixed_negation_soundness.
Print Assumptions rho_complement_no_commit.
Print Assumptions rho_guard_true_commits.
