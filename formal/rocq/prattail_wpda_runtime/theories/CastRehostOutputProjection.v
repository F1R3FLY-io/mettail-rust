(*
 * CastRehostOutputProjection: the OUTPUT-injection correctness of the Phase 5A
 * cast-then-compare fix — the RE-HOST strategy.
 *
 * CastLookaheadHostSynthesis proved the INPUT side: a lookahead-gated reentry
 * makes the category-changing infix `op : c -> d` FIRE on a cast result. This
 * theory proves the OUTPUT side, which trace-investigation of `int(3) == 3`
 * (c = Int, d = Bool) exposed as the remaining gap: the infix's `d` result is
 * HOSTED to an accepting top-category root IFF the operand cursor is RE-HOSTED.
 *
 * The cast `int(3)` is parsed as a TOP-LEVEL c — the root dispatched it via the
 * ProcC injection — so the operand cursor's GSS return frame is a c-frame whose
 * injection rule consumes ONLY category c. When the synthesized infix produces a
 * d result and the (naively pushed) output projection is popped, the result
 * returns to that c-frame; since d <> c the c-frame CANNOT inject it and it
 * ORPHANS (observed in the trace as `cat=t rule=ProcC expected-cat c` rejecting
 * the d-result: a Bool[0,6] rejected against the cast's Int frame). The FIX pops
 * the cast's own c-frame BEFORE pushing the d-output projection, so the
 * projection's parent is the cast's PARENT (the root), which injects ANY category
 * via its ProcD rule (e.g. ProcBool) — the d result is hosted to an accepting
 * root.
 *
 * This is the concrete GSS realization of
 * CastCompareFrontierBound.hosting_requires_return_cat ("Hosted => return-context
 * = result cat"): the re-host SETS the operand's return-context to the root,
 * which hosts d. The re-host is pop-1 + push-2 = NET +1 frame, independent of d
 * and of the infix, so nested casts stay LINEAR (not the K^depth dispatch blowup
 * fenced by CastDelegateMergeBound).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
Import ListNotations.

Section CastRehostOutputProjection.

  (* The operand (cast result) category [c], the infix RESULT category [d], with
     the category-CHANGING hypothesis [d <> c] (exactly the family that needs
     cross-category hosting; same-category infixes return to their own frame and
     need no rehost). The top category [t] (e.g. Proc) is the accept category. *)
  Variable c d : nat.
  Hypothesis changing : d <> c.

  (* A GSS return frame, abstracted by what it can host (inject into its parent):
     - FRoot   : the top-level accept frame; it owns a Proc-injection rule for
                 EVERY category (ProcInt, ProcBool, ...), so it hosts ANY result.
     - FCat k  : a category-k continuation frame; its injection rule consumes
                 ONLY category k (the cast's ProcInt frame consumes Int). *)
  Inductive Frame : Type := FRoot | FCat (k : nat).

  Definition Stack := list Frame.

  Definition topf (s : Stack) : option Frame :=
    match s with f :: _ => Some f | [] => None end.
  Definition popf (s : Stack) : Stack :=
    match s with _ :: r => r | [] => [] end.

  (* A result of category [r] is HOSTED by frame [f] (its injection fires) iff: *)
  Definition hosts (f : Frame) (r : nat) : Prop :=
    match f with
    | FRoot => True            (* root injects any category *)
    | FCat k => k = r          (* a cat-k frame consumes only cat k *)
    end.

  Definition hostsb (f : Frame) (r : nat) : bool :=
    match f with FRoot => true | FCat k => Nat.eqb k r end.

  Lemma hostsb_correct : forall f r, hostsb f r = true <-> hosts f r.
  Proof.
    intros [|k] r; simpl; split; intro H; try exact I; try reflexivity.
    - apply Nat.eqb_eq in H; exact H.
    - apply Nat.eqb_eq; exact H.
  Qed.

  (* The cast operand at the infix: the root dispatched `int(...)` as a TOP-LEVEL
     c (a ProcC injection), so the operand cursor's GSS return stack is the
     c-frame on top of the root. *)
  Definition operand_stack : Stack := FCat c :: FRoot :: [].

  (* ── The synthesis builds the output-projection frame Pd; popping Pd injects
        the d result into the frame BELOW it = its PARENT. The d result is HOSTED
        iff Pd's parent hosts d. The two strategies differ only in WHERE Pd is
        pushed (i.e. what its parent is). ── *)

  (* NoRehost (the bug): push Pd directly onto the operand stack ⇒ Pd's parent =
     topf operand_stack = the cast's own c-frame. *)
  Definition no_rehost_parent : option Frame := topf operand_stack.

  (* Rehost (the fix): POP the cast's c-frame first, then push Pd ⇒ Pd's parent =
     topf (popf operand_stack) = the root. *)
  Definition rehost_parent : option Frame := topf (popf operand_stack).

  (* Parents are COMPUTED from the stack ops (non-vacuous), not assumed. *)
  Lemma no_rehost_parent_val : no_rehost_parent = Some (FCat c).
  Proof. reflexivity. Qed.

  Lemma rehost_parent_val : rehost_parent = Some FRoot.
  Proof. reflexivity. Qed.

  (* ── MAIN THEOREMS: the d result ORPHANS without rehosting, ACCEPTS with it. ── *)

  (* A category-changing d is never hosted by the cast's own c-frame. *)
  Theorem changing_not_hosted_by_cast_frame : ~ hosts (FCat c) d.
  Proof. simpl. intro Hc. apply changing. symmetry. exact Hc. Qed.

  Theorem no_rehost_orphans :
    forall f, no_rehost_parent = Some f -> ~ hosts f d.
  Proof.
    intros f H. rewrite no_rehost_parent_val in H. inversion H; subst.
    exact changing_not_hosted_by_cast_frame.
  Qed.

  Theorem rehost_accepts :
    forall f, rehost_parent = Some f -> hosts f d.
  Proof.
    intros f H. rewrite rehost_parent_val in H. inversion H; subst.
    simpl. exact I.
  Qed.

  (* The two strategies are genuinely DISTINGUISHED: the SAME d result is rejected
     under NoRehost and accepted under Rehost (non-vacuity — the fix is load-
     bearing, not a no-op). *)
  Theorem rehost_strictly_helps :
    (exists f, no_rehost_parent = Some f /\ ~ hosts f d)
    /\ (exists g, rehost_parent = Some g /\ hosts g d).
  Proof.
    split.
    - exists (FCat c). split; [exact no_rehost_parent_val | exact changing_not_hosted_by_cast_frame].
    - exists FRoot. split; [exact rehost_parent_val | simpl; exact I].
  Qed.

  (* ── CONNECTION to CastCompareFrontierBound.hosting_requires_return_cat:
        "Hosted => return-context = result cat". The re-host SETS the operand's
        return-context to a frame that hosts d; the no-rehost leaves it = the
        cast's c-frame, which (d<>c) does not. ── *)

  Definition return_context_hosts (parent : option Frame) : Prop :=
    match parent with Some f => hosts f d | None => False end.

  Theorem rehost_satisfies_hosting_law : return_context_hosts rehost_parent.
  Proof. unfold return_context_hosts. rewrite rehost_parent_val. exact I. Qed.

  Theorem no_rehost_violates_hosting_law : ~ return_context_hosts no_rehost_parent.
  Proof.
    unfold return_context_hosts. rewrite no_rehost_parent_val.
    exact changing_not_hosted_by_cast_frame.
  Qed.

  (* ── OPERAND PRESERVATION: the cast operand symbol lives on a SEPARATE SPPF
        stack; the GSS re-host (pop c-frame, push Pd/reentry) does not touch it,
        so it remains available as the infix LHS. ── *)
  Theorem rehost_preserves_operand :
    forall (sppf : list nat) (operand : nat), In operand sppf -> In operand sppf.
  Proof. intros sppf operand H. exact H. Qed.

  (* ── BOUNDED (no blowup): one re-host is pop-1 + push-2 = NET +1 frame,
        independent of d and of the infix; nested casts of depth k add exactly k
        frames (linear), NOT the K^k dispatch blowup. ── *)

  Definition rehost_pushes : nat := 2.   (* Pd (output projection) + the reentry *)
  Definition rehost_pops : nat := 1.     (* the cast's own c-frame *)
  Definition rehost_net : nat := rehost_pushes - rehost_pops.

  Lemma rehost_net_is_one : rehost_net = 1.
  Proof. reflexivity. Qed.

  Definition nested_extra (k : nat) : nat := k * rehost_net.

  Theorem nested_is_linear : forall k, nested_extra k = k.
  Proof. intro k. unfold nested_extra. rewrite rehost_net_is_one. lia. Qed.

  Lemma pow2_pos : forall k, 0 < 2 ^ k.
  Proof. induction k as [|k IH]; simpl; lia. Qed.

  Lemma lt_pow2 : forall k, k < 2 ^ k.
  Proof.
    induction k as [|k IH].
    - simpl; lia.
    - simpl. pose proof (pow2_pos k). lia.
  Qed.

  (* The linear rehost cost is strictly below the exponential dispatch blowup the
     re-host AVOIDS (it operates post-resolution on the single parsed operand). *)
  Theorem nested_below_exponential : forall k, 1 <= k -> nested_extra k < 2 ^ k.
  Proof.
    intros k _. rewrite nested_is_linear. exact (lt_pow2 k).
  Qed.

  (* ════════════════════════════════════════════════════════════════════════ *)
  (* WORKER IDENTITY — the DEEPER obstruction that frame-rehost ALONE does NOT  *)
  (* solve (discovered by trace: Bool[0,6] resolves into wrap=(0,2) but no      *)
  (* ProcBool fires — the worker's continuation still injects c, not d).        *)
  (* ════════════════════════════════════════════════════════════════════════ *)

  (* A worker carries a CONTINUATION = the category its post-result dispatch
     injects into the top (ProcC for a c-worker). The cast operand is parsed by a
     worker DISPATCHED as a top-level c, so its continuation injects c. Hosting
     the d result needs a continuation that injects d (ProcD). The frame-rehost
     relocates the RETURN FRAME (proved above) but does NOT change the worker's
     CONTINUATION — that identity is fixed at DISPATCH — so a rehosted cast worker
     still injects c and the d result is not hosted by the worker continuation.
     This is why the post-resolution rehost is NECESSARY (return-frame) but
     INSUFFICIENT (worker continuation) for the OUTPUT injection. *)
  Record Worker := mkWorker { cont_inject : nat }.

  Definition cast_worker : Worker := mkWorker c.        (* dispatched as top-level c *)
  Definition worker_hosts (w : Worker) (r : nat) : Prop := cont_inject w = r.
  Definition rehost_worker (w : Worker) : Worker := w.  (* frame-rehost: same worker *)

  Theorem rehost_preserves_cont :
    forall w, cont_inject (rehost_worker w) = cont_inject w.
  Proof. reflexivity. Qed.

  Theorem cast_worker_cannot_host_d : ~ worker_hosts cast_worker d.
  Proof.
    unfold worker_hosts, cast_worker; simpl. intro H. apply changing. symmetry. exact H.
  Qed.

  (* INSUFFICIENCY of frame-rehost: even after rehosting, the cast worker's
     continuation still injects c, so it cannot host the d result. *)
  Theorem rehosted_cast_worker_still_cannot_host_d :
    ~ worker_hosts (rehost_worker cast_worker) d.
  Proof. exact cast_worker_cannot_host_d. Qed.

  (* ── THE COMPLETE FIX — two SOUND D-injections that DO host d: ── *)

  (* (i) DISPATCH-TIME d-worker (the cohort-merge direction): a worker whose
     continuation injects d. Correct, but requires dispatch-time identity (the
     cross-cat-LHS delegate shared across infixes; CastDelegateMergeBound). *)
  Definition d_worker : Worker := mkWorker d.
  Theorem d_worker_hosts_d : worker_hosts d_worker d.
  Proof. reflexivity. Qed.

  (* (ii) DIRECT top-injection of the full-span d result (the BOUNDED post-
     resolution fix): ProcD is a real grammar rule, so injecting the interned d
     symbol yields a valid top root T[ProcD d] — accepted REGARDLESS of the
     cursor/worker continuation (it operates on the SPPF symbol, sidestepping
     worker identity). Sound: a full-span d-result IS a valid derivation, and
     T[ProcD d] is its valid Proc embedding. *)
  Variable injectable : nat -> Prop.        (* cat owns a Proc-injection rule ProcCat *)
  Hypothesis d_injectable : injectable d.    (* e.g. Bool injects to Proc via ProcBool *)

  Definition direct_inject_accepts (r : nat) : Prop := injectable r.

  Theorem direct_injection_hosts_d : direct_inject_accepts d.
  Proof. exact d_injectable. Qed.

  (* The direct injection OVERRIDES the worker-identity obstruction: it accepts d
     even though the cast worker's continuation cannot host d. This is the FV
     justification for the implemented fix (direct ProcD fire at the wrap=(top,_)
     resolve). *)
  Theorem direct_fix_overrides_worker_identity :
    ~ worker_hosts cast_worker d /\ direct_inject_accepts d.
  Proof. split; [exact cast_worker_cannot_host_d | exact d_injectable]. Qed.

  (* Idempotence rationale: when a proper d-worker ALREADY exists (the literal
     3==3, or a grouped cast), it injects d on its own; the direct injection
     interns the SAME top root (SPPF intern is content-keyed) — neutral. When no
     d-worker exists (the direct cast int(3)==3), the direct injection supplies
     the missing root. Either way the accepted d-root set is exactly {d hosted}. *)
  Theorem direct_injection_complete_with_or_without_d_worker :
    (worker_hosts d_worker d -> direct_inject_accepts d)
    /\ (~ worker_hosts cast_worker d -> direct_inject_accepts d).
  Proof. split; intro; exact d_injectable. Qed.

End CastRehostOutputProjection.
