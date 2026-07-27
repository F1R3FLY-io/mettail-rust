(*
 * MixfixLiteralAccounting: the converged spec for the ROOT-A fix (#307) —
 * every mixfix rule literal is consumed EXACTLY ONCE by a CHECKED,
 * edge-membership consume that advances along the MATCHED lattice edge.
 *
 * THE DEFECT (flip-evidenced; rholang POutput `n "!" "(" q ")"`, `x!(0)`):
 *   - the trigger arm dispatches the part-0 operand WITHOUT consuming the
 *     part's preceding literals ["("] (no "before part 0" state exists);
 *   - the following-literal run consumes ")" UNCHECKED (`_expected` is
 *     generated but never compared) — stealing enclosing delimiters or
 *     fabricating an out-of-stream position via `unwrap_or(pos + 1)`;
 *   - the correct parse is interned but the poisoned cursor fails every EOI
 *     gate.
 *
 * THE CONVERGED FIX (two adversarial critics, both reports in pgmcp #307):
 *   D1 a NEW pre-operand literal-run (kind=2) consuming
 *      parts[completed_idx].preceding with the marker UNCHANGED;
 *   D2 entered from ALL THREE trigger-emission sites;
 *   D3 every literal consume is a TEXT-MEMBERSHIP check over the position's
 *      COMPLETE out-edge set, advancing along the MATCHED edge's target
 *      (carried explicitly — the walker's generic advance is alt-0-hardwired);
 *      multi-target matches fork; mismatch (incl. vacuously at edge-less
 *      nodes) is a pure engine Error (advance-or-die);
 *   D4 the position-fabrication fallback is UNREACHABLE on the checked path.
 *
 * THE MODEL: input = a lex DAG (node -> labelled out-edges). A checked run
 * consumes a literal list by membership steps. Theorems:
 *   T1 checked_run_sound/complete — the checked run succeeds from n iff the
 *      DAG spells the literal list from n (no loss, no invention);
 *   T2 primary_equality_loses — single-token (primary-edge) equality kills a
 *      parse the DAG admits on a secondary edge (critic-2 F1, non-vacuous);
 *   T3 unchecked_accepts_mismatch — the shipped unchecked consume accepts a
 *      label-mismatched edge (the delimiter steal, non-vacuous);
 *   T4 accounting — the fixed pipeline consumes |pre|+|fol| literal tokens
 *      where the shipped consumes only |fol| (the part-0 skip, arithmetic);
 *   T5 empty_pre_passthrough — empty preceding (Tern/PAmb) consumes nothing
 *      in the new state: shipped-equivalent (zero blast radius);
 *   T6 checked_never_fabricates — a successful checked step lands on an
 *      existing DAG target (no fabricated positions);
 *   T7 fork_completeness — every distinct matching target is followed
 *      (preserve-disambiguation under pathological same-text duplication).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Section MixfixLiteralAccounting.

  (* Lex DAG: nodes are nats; out-edges are (label, target) pairs. *)
  Definition Edge : Type := (nat * nat)%type.   (* (label, target) *)
  Variable out_edges : nat -> list Edge.

  (* ── The CHECKED membership consume (D3): all matching targets. ── *)
  Definition matching_targets (n lbl : nat) : list nat :=
    map snd (filter (fun e => Nat.eqb (fst e) lbl) (out_edges n)).

  (* A checked run consumes a literal list, threading the node. SUCCESS set =
     all end nodes reachable by matching every literal in order. *)
  Fixpoint checked_run (lits : list nat) (n : nat) : list nat :=
    match lits with
    | [] => [n]
    | l :: rest =>
        flat_map (fun t => checked_run rest t) (matching_targets n l)
    end.

  (* The DAG "spells" lits from n ending at m. *)
  Inductive spells : list nat -> nat -> nat -> Prop :=
    | spells_nil : forall n, spells [] n n
    | spells_cons : forall l rest n t m,
        In (l, t) (out_edges n) -> spells rest t m -> spells (l :: rest) n m.

  Lemma matching_targets_in :
    forall n l t, In t (matching_targets n l) <-> In (l, t) (out_edges n).
  Proof.
    intros n l t. unfold matching_targets. rewrite in_map_iff. split.
    - intros [[l' t'] [Hsnd Hin]]. simpl in Hsnd. subst t'.
      apply filter_In in Hin. destruct Hin as [Hin Heq].
      simpl in Heq. apply Nat.eqb_eq in Heq. subst l'. exact Hin.
    - intro Hin. exists (l, t). split; [reflexivity |].
      apply filter_In. split; [exact Hin |]. simpl. apply Nat.eqb_refl.
  Qed.

  (* T1 — the checked run is SOUND and COMPLETE w.r.t. the DAG. *)
  Theorem checked_run_iff_spells :
    forall lits n m, In m (checked_run lits n) <-> spells lits n m.
  Proof.
    induction lits as [| l rest IH]; intros n m; simpl.
    - split.
      + intros [<- | []]. constructor.
      + intro H. inversion H; subst. left. reflexivity.
    - rewrite in_flat_map. split.
      + intros [t [Ht Hm]]. apply matching_targets_in in Ht.
        apply (spells_cons l rest n t m Ht). apply IH. exact Hm.
      + intro H. inversion H; subst. exists t. split.
        * apply matching_targets_in. assumption.
        * apply IH. assumption.
  Qed.

  (* ── T2 — primary-edge equality LOSES lattice parses (critic-2 F1). ──
     The shipped-style check compares only the PRIMARY (first) edge. *)
  Definition primary_equality_consume (n lbl : nat) : option nat :=
    match out_edges n with
    | (l0, t0) :: _ => if Nat.eqb l0 lbl then Some t0 else None
    | [] => None
    end.

  Theorem primary_equality_loses :
    forall n l0 t0 l1 t1,
      out_edges n = [(l0, t0); (l1, t1)] -> l0 <> l1 ->
      primary_equality_consume n l1 = None
      /\ In t1 (matching_targets n l1).
  Proof.
    intros n l0 t0 l1 t1 Hout Hne. split.
    - unfold primary_equality_consume. rewrite Hout.
      destruct (Nat.eqb l0 l1) eqn:E.
      + apply Nat.eqb_eq in E. contradiction.
      + reflexivity.
    - apply matching_targets_in. rewrite Hout. right. left. reflexivity.
  Qed.

  (* ── T3 — the shipped UNCHECKED consume accepts a mismatched edge (the
     enclosing-delimiter steal): it advances on the primary edge regardless
     of its label. ── *)
  Definition unchecked_consume (n : nat) : option nat :=
    match out_edges n with
    | (_, t0) :: _ => Some t0
    | [] => None
    end.

  Theorem unchecked_accepts_mismatch :
    forall n l0 t0 expected,
      out_edges n = [(l0, t0)] -> l0 <> expected ->
      unchecked_consume n = Some t0
      /\ matching_targets n expected = [].
  Proof.
    intros n l0 t0 expected Hout Hne. split.
    - unfold unchecked_consume. rewrite Hout. reflexivity.
    - unfold matching_targets. rewrite Hout. simpl.
      destruct (Nat.eqb l0 expected) eqn:E.
      + apply Nat.eqb_eq in E. contradiction.
      + reflexivity.
  Qed.

  (* ── T4 — literal ACCOUNTING (the part-0 skip, arithmetically). ── *)
  Definition fixed_literal_consumes (pre fol : list nat) : nat :=
    length pre + length fol.
  Definition shipped_literal_consumes (pre fol : list nat) : nat :=
    length fol.   (* part-0 preceding never consumed by the shipped machine *)

  Theorem accounting_gap :
    forall pre fol, pre <> [] ->
      shipped_literal_consumes pre fol < fixed_literal_consumes pre fol.
  Proof.
    intros pre fol Hne. unfold shipped_literal_consumes, fixed_literal_consumes.
    destruct pre as [| p pre']; [contradiction | simpl; lia].
  Qed.

  (* T5 — EMPTY preceding (Tern/PAmb): the new pre-operand run consumes
     nothing and the accounting matches the shipped machine exactly — zero
     blast radius on the currently-green mixfix rules. *)
  Theorem empty_pre_passthrough :
    forall fol,
      fixed_literal_consumes [] fol = shipped_literal_consumes [] fol
      /\ forall n, checked_run [] n = [n].
  Proof.
    intro fol. split; [reflexivity |]. intro n. reflexivity.
  Qed.

  (* T6 — a successful checked step never fabricates a position: every node
     it reaches is an out-edge target of the predecessor (and inductively a
     real DAG node). *)
  Theorem checked_never_fabricates :
    forall l n t, In t (matching_targets n l) -> In (l, t) (out_edges n).
  Proof. intros l n t H. apply matching_targets_in. exact H. Qed.

  (* T7 — fork completeness: EVERY distinct matching target is followed
     (no pick-one under pathological same-text duplication). *)
  Theorem fork_completeness :
    forall lits l n t,
      In (l, t) (out_edges n) ->
      forall m, In m (checked_run lits t) -> In m (checked_run (l :: lits) n).
  Proof.
    intros lits l n t Ht m Hm. simpl. apply in_flat_map.
    exists t. split; [apply matching_targets_in; exact Ht | exact Hm].
  Qed.

End MixfixLiteralAccounting.
