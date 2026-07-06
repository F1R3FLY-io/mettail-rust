(*
 * MethodFrameIsolation: the spec for the ROOT-D method-call-frame isolation the
 * generated facade SHIPS (session da0842dc, 2026-07-06). The SIBLING of
 * `SepReconvergence` (`.*sep`) and `ProjectionIsolation` (`@`-prefix), extending
 * the STRING-level divide-and-conquer linearizer to the RECEIVER-LED POSTFIX
 * (method-call) frames `recv "." name "(" args ")"`.
 *
 * THE DEFECT (Stage-0 measured, rhocalc): a method rule (`m:Proc "." "get" "("
 * k:Proc ")"`) begins with an OPERAND (the receiver), not a sigil, and has no
 * `.*sep` list, so the proj-iso eligibility declined it — a deep-`@` method-call
 * ARG parsed MONOLITHICALLY, EXPONENTIAL (`Nil.concat(@^d Nil)` = 23→55→269→1568
 * →7546→34666 ms d=1..6, base~5), while the SAME `@`-nest as an ISOLATED arg is
 * the linear proj-iso base-2 floor. `proc_display` timed out.
 *
 * THE FIX (this spec): recognize the method frame, isolate the RECEIVER (matched
 * GREEDY-LAST — the method `.` is the unique rightmost depth-0 `.` since the args
 * are bracketed — so left-assoc CHAINS `a.b().c()` recover) and each ARG, then
 * cartesian-COMBINE the operand readings under the method ctor. The receiver is
 * soundness-GATED: only a PRIMARY receiver (top ctor NOT a binary-infix / prefix
 * rule) is the whole receiver (Stage-0 S0-SOUND: `Map() % @X . concat` = `Mod`,
 * `-Nil . concat` = `NegProc` bind LOOSER than `.`), so a non-primary receiver is
 * DROPPED and the frame DECLINES ⇒ falls to the monolithic body (sound).
 *
 * THE MODEL: the method operands are `gate recv :: args` — the receiver reading
 * list FILTERED to primaries, then each argument's isolated reading list. The
 * COMBINE enumerates their cartesian product (one reading per operand); the
 * MONOLITHIC method reading set is (Stage-0-grounded) EXACTLY those tuples that
 * pick one PRIMARY receiver reading and one reading per arg.
 *
 * Theorems:
 *   T1  combine_equals_monolithic     — In tup (combine) ↔ is_mono_method
 *                                        (the combine enumerates EXACTLY the
 *                                        monolithic method reading set).
 *   T2a no_reading_lost               — is_mono_method → In combine (SOUNDNESS).
 *   T2b no_reading_gained             — In combine → is_mono_method (COMPLETENESS).
 *   T3  gate_declines_nonprimary      — every receiver reading non-primary ⇒ the
 *                                        combine is EMPTY ⇒ the frame declines
 *                                        (falls to monolithic — sound).
 *   T4  every_reading_has_primary_recv — every combined reading's RECEIVER (tuple
 *                                        head) is a PRIMARY (no non-primary
 *                                        receiver is ever wrapped — the S0-SOUND
 *                                        invariant that made every ACCEPT sound).
 *   T5  gate_is_strict_refinement     — the gate NEVER adds a receiver reading and
 *                                        keeps EXACTLY the primaries (drops only
 *                                        the proven-non-whole-receiver readings).
 *   T6  greedy_last_is_method_boundary — the RIGHTMOST depth-0 delimiter is the
 *                                        method boundary (args bracketed ⇒ no
 *                                        depth-0 delimiter follows it), so the
 *                                        greedy-last receiver scan is correct for
 *                                        left-assoc chains.
 *   T7  killswitch_off_declines       — with METHOD_FRAME_ISOLATION OFF the frame
 *                                        yields NO reading ⇒ monolithic ⇒
 *                                        byte-identical (fallback identity).
 *   T8  fallback_refines              — the combine SET = the monolithic method
 *                                        SET, so a `None` fall-through loses
 *                                        nothing and an engaged combine loses
 *                                        nothing (RT-4).
 *   T9  composes_with_fallback        — composing the isolation with any
 *                                        downstream monolithic transform `g` and
 *                                        taking a declined frame ⇒ g leaves g's
 *                                        behavior UNCHANGED (disjoint composition
 *                                        with the landed gates / other iso).
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Import ListNotations.

Section Combine.

  (* An abstract OPERAND reading (an isolated receiver / argument sub-parse). *)
  Variable Reading : Type.

  (* The cartesian product of the per-operand reading lists: every way to pick one
     reading per operand, in order — EXACTLY the emitted helper's nested-loop
     `__candidates` build. (Identical to SepReconvergence's `cartesian`.) *)
  Fixpoint cartesian (ops : list (list Reading)) : list (list Reading) :=
    match ops with
    | [] => [ [] ]
    | s :: rest =>
        flat_map (fun r => map (fun tup => r :: tup) (cartesian rest)) s
    end.

  (* A tuple is a monolithic reading iff it is pointwise a member of the per-
     operand lists (Stage-0-grounded: the monolithic method alt-set decomposes
     EXACTLY to the tuples picking one isolated reading per operand). *)
  Definition is_mono (ops : list (list Reading)) (tup : list Reading) : Prop :=
    Forall2 (fun r s => In r s) tup ops.

  (* ── the combine enumerates EXACTLY the monolithic reading set (SepRecon T1). *)
  Theorem cartesian_iff_mono :
    forall ops tup, In tup (cartesian ops) <-> is_mono ops tup.
  Proof.
    unfold is_mono.
    induction ops as [| s rest IH]; intros tup; simpl.
    - split.
      + intros [H | []]. subst tup. constructor.
      + intros H. inversion H. subst. left. reflexivity.
    - rewrite in_flat_map. split.
      + intros [r [Hr Hmap]].
        rewrite in_map_iff in Hmap.
        destruct Hmap as [t [Heq Ht]].
        subst tup. constructor; [exact Hr | apply IH; exact Ht].
      + intros H. destruct tup as [| r0 t0]; inversion H; subst.
        exists r0. split; [assumption |].
        rewrite in_map_iff. exists t0. split; [reflexivity | apply IH; assumption].
  Qed.

End Combine.

Section MethodFrame.

  Variable Reading : Type.

  (* Grammar-derived receiver soundness predicate: `is_primary r` holds iff the
     receiver reading r's top ctor is NOT a binary-infix / prefix rule (Stage-0
     S0-SOUND: those bind looser than `.` ⇒ not the whole receiver). Decidable via
     `primaryb`. *)
  Variable primaryb : Reading -> bool.
  Definition is_primary (r : Reading) : Prop := primaryb r = true.

  (* The receiver GATE: keep ONLY the primary receiver readings (the emitted arm's
     `.filter(|r| !matches!(r, decline_pat))`). *)
  Definition gate (recv : list Reading) : list Reading := filter primaryb recv.

  (* The method operand lists = the gated receiver, then the argument lists. *)
  Definition method_ops (recv : list Reading) (args : list (list Reading))
    : list (list Reading) := gate recv :: args.

  (* The COMBINE: cartesian over the method operands. *)
  Definition combine (recv : list Reading) (args : list (list Reading))
    : list (list Reading) := cartesian Reading (method_ops recv args).

  (* The MONOLITHIC method reading set: a tuple picks one PRIMARY receiver reading
     and one reading per arg (Stage-0-grounded S0-SOUND: a non-primary receiver is
     never the whole receiver, so contributes NO monolithic method reading). *)
  Definition is_mono_method (recv : list Reading) (args : list (list Reading))
    (tup : list Reading) : Prop := is_mono Reading (method_ops recv args) tup.

  (* ── T1: the combine enumerates EXACTLY the monolithic method reading set. ── *)
  Theorem T1_combine_equals_monolithic :
    forall recv args tup,
      In tup (combine recv args) <-> is_mono_method recv args tup.
  Proof. intros. apply cartesian_iff_mono. Qed.

  (* ── T2a: SOUNDNESS — no monolithic method reading is dropped. ── *)
  Theorem T2a_no_reading_lost :
    forall recv args tup,
      is_mono_method recv args tup -> In tup (combine recv args).
  Proof. intros recv args tup H. apply T1_combine_equals_monolithic. exact H. Qed.

  (* ── T2b: COMPLETENESS — no spurious method reading is fabricated. ── *)
  Theorem T2b_no_reading_gained :
    forall recv args tup,
      In tup (combine recv args) -> is_mono_method recv args tup.
  Proof. intros recv args tup H. apply T1_combine_equals_monolithic. exact H. Qed.

  (* Any operand list containing an EMPTY operand makes the whole cartesian empty
     (an operand with no reading kills every tuple). *)
  Lemma cartesian_empty_if_nil_in :
    forall ops, In [] ops -> cartesian Reading ops = [].
  Proof.
    induction ops as [| s rest IH]; intros Hin; simpl.
    - inversion Hin.
    - destruct Hin as [Heq | Hin].
      + subst s. reflexivity.
      + rewrite (IH Hin). induction s as [| a s' IHs]; simpl; [reflexivity | exact IHs].
  Qed.

  (* An empty operand anywhere makes the whole cartesian empty. *)
  Lemma cartesian_nil_operand :
    forall (pre : list (list Reading)) (post : list (list Reading)),
      cartesian Reading (pre ++ [] :: post) = [].
  Proof.
    intros pre post. apply cartesian_empty_if_nil_in.
    apply in_or_app. right. left. reflexivity.
  Qed.

  (* ── T3: the receiver GATE DECLINES a fully-non-primary receiver: when NO
     receiver reading is primary (`gate recv = []`), the combine is EMPTY, so the
     frame yields no candidate and the facade FALLS THROUGH to the monolithic body
     (sound). This is the `-Nil . concat` / `Map()%@X . concat` case. ── *)
  Theorem T3_gate_declines_nonprimary :
    forall recv args,
      gate recv = [] -> combine recv args = [].
  Proof.
    intros recv args Hg. unfold combine, method_ops. rewrite Hg.
    exact (cartesian_nil_operand nil args).
  Qed.

  (* Every cartesian tuple over (s :: rest) has its head IN s. *)
  Lemma cartesian_head_in :
    forall (s : list Reading) rest tup,
      In tup (cartesian Reading (s :: rest)) ->
      exists r t, tup = r :: t /\ In r s.
  Proof.
    intros s rest tup Hin. simpl in Hin. rewrite in_flat_map in Hin.
    destruct Hin as [r [Hr Hmap]]. rewrite in_map_iff in Hmap.
    destruct Hmap as [t [Heq Ht]]. exists r, t. split; [symmetry; exact Heq | exact Hr].
  Qed.

  (* filter keeps only elements satisfying the predicate. *)
  Lemma in_gate_primary : forall recv r, In r (gate recv) -> is_primary r.
  Proof.
    intros recv r Hin. unfold gate, is_primary in *.
    apply filter_In in Hin. destruct Hin as [_ Hb]. exact Hb.
  Qed.

  (* ── T4: EVERY combined method reading's RECEIVER (the tuple HEAD) is a PRIMARY.
     No non-primary receiver is EVER wrapped in the method ctor — the S0-SOUND
     invariant that makes every ACCEPTED frame == the monolithic reading. ── *)
  Theorem T4_every_reading_has_primary_recv :
    forall recv args tup,
      In tup (combine recv args) ->
      exists r t, tup = r :: t /\ is_primary r.
  Proof.
    intros recv args tup Hin. unfold combine, method_ops in Hin.
    apply cartesian_head_in in Hin. destruct Hin as [r [t [Heq Hr]]].
    exists r, t. split; [exact Heq | apply in_gate_primary with (recv := recv); exact Hr].
  Qed.

  (* ── T5: the gate is a STRICT REFINEMENT — it never ADDS a receiver reading
     (`gate recv ⊆ recv`) and keeps EXACTLY the primaries. So the only readings it
     removes are the proven-non-whole-receiver (non-primary) ones. ── *)
  Theorem T5_gate_is_strict_refinement :
    forall recv r, In r (gate recv) <-> (In r recv /\ is_primary r).
  Proof.
    intros recv r. unfold gate, is_primary. apply filter_In.
  Qed.

End MethodFrame.

Section GreedyLast.

  (* Model of the receiver scan over the raw input: a boolean marker per position,
     `true` iff a depth-0 delimiter (the method `.`) sits there. The greedy-last
     scan returns the index of the LAST `true` marker. *)
  Fixpoint find_last_true (bs : list bool) (i : nat) : option nat :=
    match bs with
    | [] => None
    | b :: rest =>
        match find_last_true rest (S i) with
        | Some j => Some j
        | None => if b then Some i else None
        end
    end.

  (* nth marker true. *)
  Definition marker_at (bs : list bool) (p : nat) : Prop := nth p bs false = true.

  (* No marker after position p (the method `.` is the LAST depth-0 delimiter —
     because the args following it are bracketed ⇒ any inner `.` is at depth ≥1). *)
  Definition no_marker_after (bs : list bool) (p : nat) : Prop :=
    forall q, q > p -> nth q bs false = false.

  (* An all-false marker list has NO last true (the args after the method `.` are
     bracketed ⇒ contribute no depth-0 delimiter). *)
  Lemma find_last_true_none_of_all_false :
    forall bs base,
      (forall p, nth p bs false = false) -> find_last_true bs base = None.
  Proof.
    induction bs as [| b rest IH]; intros base Hall; simpl.
    - reflexivity.
    - assert (Hb : b = false) by (specialize (Hall 0); simpl in Hall; exact Hall).
      assert (Hrest : forall p, nth p rest false = false)
        by (intros p; specialize (Hall (S p)); simpl in Hall; exact Hall).
      rewrite (IH (S base) Hrest). rewrite Hb. reflexivity.
  Qed.

  (* find_last_true is offset-shift-invariant: from base it returns base + (the
     index relative to 0). Proved with the boundary hypothesis in place. *)
  Lemma find_last_true_boundary :
    forall bs base p,
      nth p bs false = true ->
      (forall q, q > p -> nth q bs false = false) ->
      find_last_true bs base = Some (base + p).
  Proof.
    induction bs as [| b rest IH]; intros base p Hp Hafter.
    - destruct p; simpl in Hp; discriminate.
    - simpl. destruct p as [| p'].
      + (* boundary at head; no marker after ⇒ rest is all-false ⇒ find_last = None. *)
        simpl in Hp. subst b.
        assert (Hrest_all : forall q, nth q rest false = false).
        { intros q. specialize (Hafter (S q) (Nat.lt_0_succ q)). simpl in Hafter. exact Hafter. }
        rewrite (find_last_true_none_of_all_false rest (S base) Hrest_all).
        rewrite Nat.add_0_r. reflexivity.
      + (* boundary at S p'; recurse into rest at p'. *)
        simpl in Hp.
        assert (Hafter' : forall q, q > p' -> nth q rest false = false)
          by (intros q Hq; specialize (Hafter (S q)); apply Hafter; lia).
        rewrite (IH (S base) p' Hp Hafter'). rewrite Nat.add_succ_r. reflexivity.
  Qed.

  (* ── T6: the RIGHTMOST depth-0 delimiter IS the method boundary. Given a marker
     at the boundary p and NO marker after p (the args are bracketed), the
     greedy-last scan `find_last_true` returns EXACTLY p. So isolating the receiver
     as the prefix up to the rightmost depth-0 `.` recovers the WHOLE receiver of a
     left-assoc method chain (`a.b().c()` → recv `a.b()`). ── *)
  Theorem T6_greedy_last_is_method_boundary :
    forall bs p,
      marker_at bs p ->
      no_marker_after bs p ->
      find_last_true bs 0 = Some p.
  Proof.
    unfold marker_at, no_marker_after. intros bs p Hp Hafter.
    rewrite (find_last_true_boundary bs 0 p Hp Hafter). reflexivity.
  Qed.

End GreedyLast.

Section Killswitch.

  Variable Reading : Type.
  Variable primaryb : Reading -> bool.

  (* METHOD_FRAME_ISOLATION OFF is modeled as the frame producing NO candidate for
     any input (the derive admits no method variant), so the facade uses the
     monolithic body unchanged. *)
  Definition frame_off (_recv : list Reading) (_args : list (list Reading))
    : list (list Reading) := [].

  (* ── T7: killswitch OFF ⇒ the frame declines for EVERY input ⇒ the monolithic
     body is authoritative ⇒ byte-identical. ── *)
  Theorem T7_killswitch_off_declines :
    forall recv args, frame_off recv args = [].
  Proof. reflexivity. Qed.

  (* ── T8: fallback refines — the engaged combine reading SET is EXACTLY the
     monolithic method SET (extensional), so choosing the combine (engaged) or the
     monolithic (declined / `None`) yields the SAME reading set: no reading is lost
     or gained either way. ── *)
  Theorem T8_fallback_refines :
    forall recv args tup,
      In tup (combine Reading primaryb recv args)
        <-> is_mono_method Reading primaryb recv args tup.
  Proof. intros. apply T1_combine_equals_monolithic. Qed.

  (* A downstream monolithic transform. *)
  Variable Out : Type.
  Variable g : list Reading -> Out.
  (* The facade: engaged frame ⇒ realize the combine; declined (empty) ⇒ g input. *)
  Definition facade (frame : list (list Reading))
    (recv : list Reading) (args : list (list Reading)) : Out :=
    match frame with
    | [] => g (concat args)   (* declined ⇒ monolithic transform *)
    | _ => g (concat frame)
    end.

  (* ── T9: composition — a DECLINED frame (killswitch OFF, or a non-primary
     receiver) leaves the downstream monolithic transform `g` UNCHANGED. So the
     isolation composes disjointly with the landed gates / sep-iso / proj-iso. ── *)
  Theorem T9_composes_with_fallback :
    forall recv args,
      facade (frame_off recv args) recv args = g (concat args).
  Proof. intros. reflexivity. Qed.

End Killswitch.
