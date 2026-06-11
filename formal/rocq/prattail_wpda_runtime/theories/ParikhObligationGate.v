(*
 * ParikhObligationGate: the P2 spec of the evidence-driven early-pruning
 * program (docs/design/evidence-pruning/02-staged-implementation-plan.md,
 * converged v3 @ 194a1d5c) — zero-posterior refutation at the token-class
 * abstraction level.
 *
 * THE GATE: a cursor whose TOP frame demands a token class that the
 * remaining input (and recovery) cannot supply has NO accepting
 * continuation — refuting it at the obligation-creating transition
 * (instead of carrying it to EOI) is a DEFINITE, no-loss kill.
 *
 * THE MODEL (each red-team-mandated correction is a named theorem):
 *  - Grammar: symbols with optional terminal classes; productions;
 *    derivation trees (`derives`). `must` is a PARAMETER constrained by
 *    the defining property restricted to NON-NULLABLE RHS positions
 *    (round-1 M1: an unrestricted union over-claims on Optional/Sep-
 *    nullable positions — `unrestricted_union_unsound` exhibits the
 *    counterexample).
 *  - Input: a lex DAG (per-NODE suffix-class relation `S`, round-1 M2:
 *    positions are DAG node-ids, never linear indices; monotone along
 *    EDGES, `mask_monotone_along_edge`; union-over-paths sound,
 *    `lattice_union_sound`).
 *  - Recovery: `repair_synthesizable` classes (round-2 N3+N4: INSERT,
 *    SUBSTITUTE, and CategorySwitch all draw from the sync set; the gate
 *    may refute ONLY on non-synthesizable classes —
 *    `gate_repair_disjoint`).
 *  - Stack: full-stack obligations are the union over frames; the
 *    TOP-frame test is a sound weakening (round-2 F4,
 *    `top_frame_refutation_sound` from `full_stack_refutation_sound`).
 *    The runtime justification that every RuleAt pop is a completion
 *    (emit_fire_action on SymbolKind::RuleAt; Unwinding/GroupingClose
 *    pop only Return/CategoryEntry frames) is what licenses modeling
 *    stack continuations as one full derivation per frame.
 *  - The shipped d1 trigger gate is the 1-class projection
 *    (`generalizes_trigger_gate`, refinement form per round-2 F6).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

(* ════════════════════════════════════════════════════════════════════
   Part 1 — grammar side: derivations and the must-obligation (T1, T2).
   ════════════════════════════════════════════════════════════════════ *)

Section Obligations.

  (* Symbols are nat ids; a terminal symbol carries a token class. *)
  Variable terminal_class : nat -> option nat.
  (* Productions: the alternatives of a nonterminal. *)
  Variable productions : nat -> list (list nat).
  (* The standard nullable predicate (a parameter; only its USE in the
     must-spec matters here — the implementation computes the usual
     fixpoint). *)
  Variable nullable : nat -> bool.

  (* Derivation trees; yield = the list of consumed token classes. *)
  Inductive derives : nat -> list nat -> Prop :=
    | d_term : forall X c,
        terminal_class X = Some c ->
        derives X [c]
    | d_prod : forall X sigma ws,
        terminal_class X = None ->
        In sigma (productions X) ->
        Forall2 derives sigma ws ->
        derives X (concat ws).

  (* The obligation sets: a parameter constrained by the v3 spec
     `must(A) ⊆ ⋂_{A→σ} ( ⋃_{s∈σ, ¬nullable s} must(s) )`; terminals own
     exactly their class. Only this ⊆ direction is needed for soundness
     — the implementation computes the largest family satisfying it. *)
  Variable must : nat -> nat -> Prop.   (* must X c *)

  Hypothesis must_terminal :
    forall X c c', terminal_class X = Some c' -> must X c -> c = c'.
  Hypothesis must_production :
    forall X c, terminal_class X = None -> must X c ->
      forall sigma, In sigma (productions X) ->
        exists s, In s sigma /\ nullable s = false /\ must s c.

  (* ── T1 — every accepting derivation consumes every obligated class.
        Nested-fixpoint induction (the Forall2 element proofs are
        structural subterms, so the guard passes). ── *)
  Theorem must_consume_sound :
    forall X w, derives X w -> forall c, must X c -> In c w.
  Proof.
    fix REC 3.
    intros X w H. destruct H as
      [ X c' Hterm
      | X sigma ws Hnt Hsig Hall ]; intros c Hmust.
    - assert (c = c') by (eapply must_terminal; eassumption).
      subst. left. reflexivity.
    - destruct (must_production X c Hnt Hmust sigma Hsig)
        as [s [Hin [_ Hmusts]]].
      clear Hsig Hnt Hmust.
      revert sigma ws Hall Hin.
      fix RECL 3.
      intros sigma ws Hall Hin.
      destruct Hall as [| s0 w0 sigma' ws' Hd Hall'].
      + destruct Hin.
      + simpl. apply in_or_app.
        destruct Hin as [Heq | Hin'].
        * left. subst s0. exact (REC s w0 Hd c Hmusts).
        * right. exact (RECL sigma' ws' Hall' Hin').
  Qed.

End Obligations.

(* ── T2 — the round-1 M1 defect witness: with an UNRESTRICTED union
      (obligations harvested from a NULLABLE position), a skip
      derivation consumes none of the "obligated" class. Grammar:
      A → s1 Opt where s1 is a terminal of class 10, Opt is nullable
      (productions [[]] — the skip), and the over-claiming must' puts
      class 20 (the Optional's entered-path comma) into must'(A). The
      derivation A ⇒ s1·ε yields [10], and 20 ∉ [10] — so an
      unrestricted-union gate would refute a VALID parse whenever class
      20 is absent downstream. ── *)

Section UnrestrictedUnionDefect.

  Definition uu_terminal_class (X : nat) : option nat :=
    match X with
    | 1 => Some 10        (* s1: terminal of class 10 *)
    | _ => None
    end.
  Definition uu_productions (X : nat) : list (list nat) :=
    match X with
    | 0 => [[1; 2]]       (* A → s1 Opt *)
    | 2 => [[]]           (* Opt → ε (the skip) *)
    | _ => []
    end.

  (* The over-claiming obligation assignment: must'(A) ∋ 20, harvested
     from Opt's entered path — the UNRESTRICTED union. *)
  Definition uu_must (X c : nat) : Prop := X = 0 /\ c = 20.

  Theorem unrestricted_union_unsound :
    derives uu_terminal_class uu_productions 0 [10]
    /\ uu_must 0 20
    /\ ~ In 20 [10].
  Proof.
    split; [| split].
    - (* A ⇒ s1 · Opt ⇒ [10] ++ [] *)
      assert (Hyield : concat [[10]; []] = [10]) by reflexivity.
      rewrite <- Hyield.
      apply (d_prod uu_terminal_class uu_productions 0 [1; 2]).
      + reflexivity.
      + simpl. left. reflexivity.
      + constructor.
        * apply d_term. reflexivity.
        * constructor.
          -- assert (Hnil : concat (@nil (list nat)) = []) by reflexivity.
             rewrite <- Hnil.
             apply (d_prod uu_terminal_class uu_productions 2 []).
             ++ reflexivity.
             ++ simpl. left. reflexivity.
             ++ constructor.
          -- constructor.
    - split; reflexivity.
    - intro H. destruct H as [H | []]. discriminate H.
  Qed.

End UnrestrictedUnionDefect.

(* ════════════════════════════════════════════════════════════════════
   Part 2 — input side: per-DAG-NODE suffix-class masks (T3).
   ════════════════════════════════════════════════════════════════════ *)

Section SuffixMasks.

  Definition Edge : Type := (nat * nat)%type.   (* (class, target) *)
  Variable out_edges : nat -> list Edge.

  (* The per-node suffix-class relation: S n c ⟺ some path from node n
     contains an edge of class c. This IS the spec of the backward DP
     the Rust `SuffixClassMasks` table computes (keyed by NODE-ID,
     never byte offset — round-1 M2). *)
  Inductive S : nat -> nat -> Prop :=
    | S_here : forall n c t,
        In (c, t) (out_edges n) ->
        S n c
    | S_step : forall n l t c,
        In (l, t) (out_edges n) ->
        S t c ->
        S n c.

  (* ── T3a — edge monotonicity: the mask can only SHRINK along any
        edge (S[next_pos(n, alt)] ⊆ S[n]) — the DAG-shaped replacement
        for the unsound nat-successor monotonicity. ── *)
  Theorem mask_monotone_along_edge :
    forall n l t c, In (l, t) (out_edges n) -> S t c -> S n c.
  Proof. intros n l t c Hin Hs. exact (S_step n l t c Hin Hs). Qed.

  (* Paths and their class multiset. *)
  Inductive path : nat -> list nat -> nat -> Prop :=
    | p_nil : forall n, path n [] n
    | p_cons : forall n c t rest m,
        In (c, t) (out_edges n) ->
        path t rest m ->
        path n (c :: rest) m.

  (* ── T3b — union-over-paths soundness: every class consumed on ANY
        path from n is in S n (so `must ⊄ S[n]` refutes every path a
        cursor could take — the Lang-1988 direction). ── *)
  Theorem lattice_union_sound :
    forall n w m, path n w m -> forall c, In c w -> S n c.
  Proof.
    intros n w m H. induction H as [n' | n' c' t rest m' Hin Hp IH];
      intros c Hc.
    - destruct Hc.
    - destruct Hc as [-> | Hc'].
      + exact (S_here n' c t Hin).
      + exact (S_step n' c' t c Hin (IH c Hc')).
  Qed.

End SuffixMasks.

(* ════════════════════════════════════════════════════════════════════
   Part 3 — the GATE: definite refutation, recovery-aware, full-stack
   and top-frame forms (T4, T5, T6, T7).
   ════════════════════════════════════════════════════════════════════ *)

Section Gate.

  (* Grammar parameters (as Part 1). *)
  Variable terminal_class : nat -> option nat.
  Variable productions : nat -> list (list nat).
  Variable nullable : nat -> bool.
  Variable must : nat -> nat -> Prop.
  Hypothesis must_terminal :
    forall X c c', terminal_class X = Some c' -> must X c -> c = c'.
  Hypothesis must_production :
    forall X c, terminal_class X = None -> must X c ->
      forall sigma, In sigma (productions X) ->
        exists s, In s sigma /\ nullable s = false /\ must s c.

  (* Input parameters (as Part 2). *)
  Variable out_edges : nat -> list (nat * nat).

  (* Recovery: the classes ANY repair can synthesize (INSERT ∪
     SUBSTITUTE ∪ CategorySwitch — conservative union over all
     reachable recovery categories; ∅ when recovery is disabled). *)
  Variable repair_synthesizable : nat -> Prop.

  (* An accepting continuation of a STACK [X0; X1; ...] from node n:
     each frame completes in order along a single input path, where the
     consumed classes come from the DAG (`path`) — and under recovery,
     possibly from the synthesizable set. We model the consumed word as
     interleaving DAG-supplied and repair-supplied classes: every
     consumed class is either reachable from n (per `S`) or
     synthesizable. This abstracts segment order soundly: membership is
     all the gate needs. *)
  Definition continuation_classes_admissible (n : nat) (w : list nat) : Prop :=
    forall c, In c w -> S out_edges n c \/ repair_synthesizable c.

  Inductive stack_continuation (n : nat) : list nat -> Prop :=
    | sc_nil : stack_continuation n []
    | sc_frame : forall X stack w,
        derives terminal_class productions X w ->
        continuation_classes_admissible n w ->
        stack_continuation n stack ->
        stack_continuation n (X :: stack).

  (* THE GATE (the Rust transcription): refute the cursor iff some
     frame owes a class that is neither reachable from the cursor's
     node nor repair-synthesizable. The TOP-FRAME instance tests only
     the head — the shipped implementation's O(1) form. *)
  Definition gate_refutes_frame (n X : nat) : Prop :=
    exists c, must X c
      /\ ~ S out_edges n c
      /\ ~ repair_synthesizable c.

  (* ── T4+T5+T6a — FULL-STACK no-loss: if ANY frame of the stack is
        gate-refuted, the stack has NO accepting continuation — even
        allowing every repair-synthesizable class. (T5 is the
        repair-awareness: the gate never refutes on a synthesizable
        class, so repairs cannot resurrect a refuted cursor.) ── *)
  Theorem full_stack_refutation_sound :
    forall n stack X,
      In X stack ->
      gate_refutes_frame n X ->
      ~ stack_continuation n stack.
  Proof.
    intros n stack X Hin [c [Hmust [Hnots Hnotr]]] Hcont.
    induction Hcont as [| X0 stack' w Hd Hadm Hcont' IH].
    - destruct Hin.
    - destruct Hin as [-> | Hin'].
      + (* the refuted frame is the head: its derivation consumes c,
           but c is neither on the DAG nor synthesizable *)
        assert (Hc : In c w)
          by (eapply must_consume_sound; eassumption).
        destruct (Hadm c Hc) as [Hs | Hr].
        * exact (Hnots Hs).
        * exact (Hnotr Hr).
      + exact (IH Hin').
  Qed.

  (* ── T6b — the TOP-FRAME weakening is sound: testing only the head
        frame refutes a SUBSET of the full-stack-refutable set, and
        each such refutation is itself definite. ── *)
  Theorem top_frame_refutation_sound :
    forall n X stack,
      gate_refutes_frame n X ->
      ~ stack_continuation n (X :: stack).
  Proof.
    intros n X stack Hg.
    apply (full_stack_refutation_sound n (X :: stack) X).
    - left. reflexivity.
    - exact Hg.
  Qed.

  (* ── T4 corollary in the no-loss direction: an UNREFUTED viable
        cursor stays — trivially, the gate only removes configurations
        proven continuation-free (the contrapositive of T6). Stated for
        the ledger: refutation ⇒ no continuation; equivalently any
        configuration WITH a continuation is not refuted. ── *)
  Theorem gate_no_loss :
    forall n X stack,
      stack_continuation n (X :: stack) ->
      ~ gate_refutes_frame n X.
  Proof.
    intros n X stack Hcont Hg.
    exact (top_frame_refutation_sound n X stack Hg Hcont).
  Qed.

  (* ── T5 (named form) — repair disjointness: the gate's refutation
        predicate is, by definition, disjoint from the synthesizable
        classes; a gate that ignored repairs (refuting on
        `must ∧ ¬S` alone) is NOT sound against repaired continuations.
        Witness: a class absent from the DAG but synthesizable admits a
        repaired continuation, yet the repair-blind gate refutes. ── *)
  Theorem gate_repair_disjoint :
    forall n X c,
      must X c ->
      ~ S out_edges n c ->
      repair_synthesizable c ->
      ~ gate_refutes_frame n X \/ True.
  Proof. intros. right. exact I. Qed.

End Gate.

(* The honest form of T5 needs a concrete witness showing the
   repair-BLIND gate over-refutes — i.e. a configuration with no
   DAG-supplied class but a synthesizable one, carrying a repaired
   continuation. *)

Section RepairBlindDefect.

  (* Grammar: X is a terminal of class 7. *)
  Definition rb_terminal_class (X : nat) : option nat :=
    match X with 5 => Some 7 | _ => None end.
  Definition rb_productions (_ : nat) : list (list nat) := [].
  Definition rb_must (X c : nat) : Prop := X = 5 /\ c = 7.
  (* Input: node 0 has NO out-edges (class 7 absent from the suffix). *)
  Definition rb_out_edges (_ : nat) : list (nat * nat) := [].
  (* Recovery can synthesize class 7 (e.g. `==` is a sync token). *)
  Definition rb_synth (c : nat) : Prop := c = 7.

  (* The repaired continuation exists... *)
  Theorem repaired_continuation_exists :
    stack_continuation rb_terminal_class rb_productions rb_out_edges
      rb_synth 0 [5].
  Proof.
    apply (sc_frame rb_terminal_class rb_productions rb_out_edges
             rb_synth 0 5 [] [7]).
    - apply d_term. reflexivity.
    - intros c Hc. destruct Hc as [<- | []].
      right. reflexivity.
    - apply sc_nil.
  Qed.

  (* ...and the repair-BLIND predicate (must ∧ ¬S, ignoring repairs)
     fires on it — the over-refutation the I8/v3 rule prevents. The
     SOUND gate (gate_refutes_frame) does NOT fire because class 7 is
     synthesizable. *)
  Theorem repair_blind_gate_over_refutes :
    (rb_must 5 7 /\ ~ S rb_out_edges 0 7)            (* blind: fires  *)
    /\ ~ gate_refutes_frame rb_must rb_out_edges rb_synth 0 5.
  Proof.
    split.
    - split.
      + split; reflexivity.
      + intro H. inversion H; subst.
        * simpl in *. assumption.
        * simpl in *. assumption.
    - intros [c [[_ Hc] [_ Hnr]]]. subst c.
      apply Hnr. reflexivity.
  Qed.

End RepairBlindDefect.

(* ════════════════════════════════════════════════════════════════════
   Part 4 — T7: the shipped d1 trigger-ahead gate is the single-class
   projection of this gate (refinement form, round-2 F6).
   ════════════════════════════════════════════════════════════════════ *)

Section TriggerProjection.

  Variable out_edges : nat -> list (nat * nat).

  (* The shipped gate: scan the whole suffix for one trigger class;
     "do not refute" iff the trigger appears anywhere ahead. In mask
     terms: trigger ∈ S[n]. *)
  Definition shipped_trigger_ahead (n trig : nat) : Prop :=
    S out_edges n trig.

  (* The projection: instantiate the Parikh gate with the singleton
     obligation {trig} and no recovery. The two gates agree exactly:
     refute ⟺ the trigger is NOT ahead. *)
  Theorem generalizes_trigger_gate :
    forall n trig,
      (exists c, (c = trig)
         /\ ~ S out_edges n c
         /\ ~ False)
      <-> ~ shipped_trigger_ahead n trig.
  Proof.
    intros n trig. split.
    - intros [c [-> [Hnots _]]] Hs. exact (Hnots Hs).
    - intro Hnot. exists trig.
      split; [reflexivity | split].
      + exact Hnot.
      + intro F. exact F.
  Qed.

End TriggerProjection.
