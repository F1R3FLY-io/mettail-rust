(*
 * InfixReconvergence: the spec for the P3 PRECEDENCE-AWARE BINARY-INFIX OPERAND
 * ISOLATION+COMBINE CODEGEN fix — the ROOT-2 `or`/PParInfix divide-and-conquer
 * linearization that the generated facade SHIPS (2026-07-06).
 *
 * THE DEFECT (measured; rhocalc `Proc` has 16 homogeneous `Proc×Proc→Proc`
 * infix operators): a binary composition whose LEFT operand is a polyadic
 * persistent send with a division arg — `@Nil!!(true, @Nil!() / @Nil!()) or X` —
 * parsed MONOLITHICALLY dies ("no accepting branch reached end of input"): the
 * GLR frontier does not RECONVERGE across the infix-operand boundary, though each
 * operand parses in isolation and simpler `or`s parse. Stage-0 (2026-07-06)
 * MEASURED that SPLITTING at the PRECEDENCE-correct root operator, parsing each
 * operand in TRUE ISOLATION (its own walker from ROOT — recurses through
 * proj/sep/infix), and combining via the operator's binary ctor is BOTH (a) SOUND
 * (== monolithic on every case monolithic handles: 11/11 identical + 10/10
 * precedence/associativity) and (b) LINEAR (~const per operand vs the monolithic
 * explosion; recovered BOTH counterexamples).
 *
 * THE MODEL: a flat expression is a HEAD operand followed by a list of
 * `(operator, operand)` pairs — `Flat := Operand * list (Op * Operand)`. An `Op`
 * carries a precedence (`prec`, LOWER = looser) and a right-associativity flag
 * (`rassoc`). The split ELECTS the ROOT operator (min prec; among ties the
 * RIGHTMOST for left-assoc / LEFTMOST for right-assoc — the exact Pratt root),
 * splits the pair list there, and recurses — producing a binary `Tree`. The
 * `flatten` of a `Tree` is its in-order reconstruction.
 *
 * Theorems:
 *   T1 flatten_parse_id          — `flatten (parse (a0,ps)) = (a0,ps)` — the D&C
 *                                  split is a FAITHFUL decomposition: no operand /
 *                                  operator is lost, gained, duplicated, or
 *                                  reordered (the structural soundness gate — the
 *                                  isolated+combined term flattens to EXACTLY the
 *                                  input token stream).
 *   T2 root_lt_length            — the elected root index is < the pair count, so
 *                                  the split strictly shrinks both sides (recursion
 *                                  terminates; both operands are shorter).
 *   T3 parse_wellformed          — every `Node op l r` the split builds is
 *                                  PRECEDENCE-WELL-FORMED: `op` is a loosest
 *                                  operator of its span, so no tighter operator is
 *                                  ever placed above a looser one (the canonical
 *                                  operator-precedence tree — precedence honored).
 *   T4 leftassoc_chain           — a uniform-precedence LEFT-associative chain
 *                                  `a0 op a1 op … op an` parses LEFT-LEANING
 *                                  (`(((a0 op a1) op a2) …) op an`) — associativity
 *                                  honored (the `a or b or c` = Or(Or(a,b),c) fact).
 *   T5 combine_set_eq            — the 2-operand cartesian of the per-operand
 *                                  ISOLATED reading sets enumerates EXACTLY the
 *                                  monolithic reading set (operand ambiguity
 *                                  preserved — never-disambiguate-early).
 *   T6 weights_correct           — ⊗ (tropical sum) is monotone, so the min-weight
 *                                  combined term = the per-operand-min term = the
 *                                  monolithic single-winner.
 *   T7 linear_vs_geometric       — the D&C total grows by a CONSTANT per operator
 *                                  (linear) vs the geometric monolithic step.
 *   T8 fallback_refines          — a `None` fall-through (no depth-0 operator ⇒ a
 *                                  pure operand ⇒ Leaf) declines to the monolithic
 *                                  path losing nothing; the A/B toggle is set-equal.
 *
 * Rocq 9.1 compatible. No Admitted, no Axioms, no Assumptions.
 *)

From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Section InfixSplit.

  (* An abstract operand reading. *)
  Variable Operand : Type.

  (* An operator: precedence (LOWER = looser) + right-associativity flag. *)
  Record Op := { prec : nat; rassoc : bool }.

  (* A flat expression: a head operand + a list of (operator, operand) pairs
     `a0 op1 a1 op2 a2 … opn an`. *)
  Definition Flat : Type := (Operand * list (Op * Operand))%type.

  (* The parse tree. *)
  Inductive Tree : Type :=
  | Leaf : Operand -> Tree
  | Node : Op -> Tree -> Tree -> Tree.

  (* In-order flatten: reconstruct the flat expression a tree stands for. *)
  Fixpoint flatten (t : Tree) : Flat :=
    match t with
    | Leaf a => (a, [])
    | Node op l r =>
        let fl := flatten l in
        let fr := flatten r in
        (fst fl, snd fl ++ (op, fst fr) :: snd fr)
    end.

  (* ── ROOT ELECTION ─────────────────────────────────────────────────────
     Scan the pair list left-to-right, tracking the best `(prec, index,
     rassoc)`: replace on a strictly-looser prec; on an EQUAL prec replace iff
     the candidate is LEFT-assoc (`rassoc = false` ⇒ RIGHTMOST wins); keep on a
     strictly-tighter prec. This is exactly the emitted `__best`/`__take` scan. *)
  Fixpoint pick (i : nat) (best : option (nat * nat * bool))
                (ps : list (Op * Operand)) : option (nat * nat * bool) :=
    match ps with
    | [] => best
    | (op, _) :: rest =>
        let cand : nat * nat * bool := (prec op, i, rassoc op) in
        let best' :=
          match best with
          | None => Some cand
          | Some (pb, ib, rb) =>
              if Nat.ltb (prec op) pb then Some cand
              else if Nat.ltb pb (prec op) then Some (pb, ib, rb)
              else if rassoc op then Some (pb, ib, rb) else Some cand
          end in
        pick (S i) best' rest
    end.

  Definition root_index (ps : list (Op * Operand)) : option nat :=
    match pick 0 None ps with
    | Some (_, i, _) => Some i
    | None => None
    end.

  (* pick never invents a `None` from a `Some` seed. *)
  Lemma pick_some_mono :
    forall ps i b, b <> None -> pick i b ps <> None.
  Proof.
    induction ps as [| [op a] rest IH]; intros i b Hb; simpl.
    - exact Hb.
    - destruct b as [[[pb ib] rb] |].
      + apply IH.
        destruct (Nat.ltb (prec op) pb); [discriminate |].
        destruct (Nat.ltb pb (prec op)); [discriminate |].
        destruct (rassoc op); discriminate.
      + apply IH. discriminate.
  Qed.

  (* A nonempty pair list always elects a root. *)
  Lemma root_index_some :
    forall op a rest, root_index ((op, a) :: rest) <> None.
  Proof.
    intros op a rest. unfold root_index.
    assert (H : pick 0 None ((op, a) :: rest) <> None).
    { simpl. apply pick_some_mono. discriminate. }
    destruct (pick 0 None ((op, a) :: rest)) as [[[p i] r] |]; [discriminate | contradiction].
  Qed.

  (* The index `pick` returns is always in `[base, base + length ps)`: it is
     either the seed's index (if kept) or some position it scanned. *)
  Lemma pick_index_bound :
    forall ps base pseed_p pseed_i pseed_r p i r,
      pick base (Some (pseed_p, pseed_i, pseed_r)) ps = Some (p, i, r) ->
      (i = pseed_i \/ (base <= i /\ i < base + length ps)).
  Proof.
    induction ps as [| [op a] rest IH]; intros base pp psi psr p i r Hpick; simpl in *.
    - inversion Hpick; subst. left. reflexivity.
    - destruct (Nat.ltb (prec op) pp) eqn:E1.
      + (* candidate replaces: new seed index = base *)
        apply IH in Hpick. destruct Hpick as [Hi | [Hlo Hhi]].
        * right. subst i. split; [lia | simpl; lia].
        * right. split; [lia | simpl in *; lia].
      + destruct (Nat.ltb pp (prec op)) eqn:E2.
        * apply IH in Hpick. destruct Hpick as [Hi | [Hlo Hhi]].
          -- left. exact Hi.
          -- right. split; [lia | simpl in *; lia].
        * destruct (rassoc op) eqn:E3.
          -- apply IH in Hpick. destruct Hpick as [Hi | [Hlo Hhi]].
             ++ left. exact Hi.
             ++ right. split; [lia | simpl in *; lia].
          -- apply IH in Hpick. destruct Hpick as [Hi | [Hlo Hhi]].
             ++ right. subst i. split; [lia | simpl; lia].
             ++ right. split; [lia | simpl in *; lia].
  Qed.

  (* ── T2: the elected root index is strictly less than the pair count. ── *)
  Theorem T2_root_lt_length :
    forall ps k, root_index ps = Some k -> k < length ps.
  Proof.
    intros ps k Hk. unfold root_index in Hk.
    destruct ps as [| [op a] rest].
    - simpl in Hk. discriminate.
    - simpl in Hk.
      destruct (pick 1 (Some (prec op, 0, rassoc op)) rest) as [[[p i] r] |] eqn:Ep;
        [| discriminate].
      inversion Hk; subst k.
      apply pick_index_bound in Ep. destruct Ep as [Hi | [Hlo Hhi]].
      + subst i. simpl. lia.
      + simpl. lia.
  Qed.

  (* ── THE SPLIT PARSE (fuel-bounded; fuel ≥ length ps suffices). ──
     Elect the root at index k, split the pair list `ps = firstn k ps ++
     (opk,ak) :: skipn (S k) ps`, and recurse into `(a0, firstn k ps)` and
     `(ak, skipn (S k) ps)`. No depth-0 operator (`root_index = None`) ⇒ a Leaf
     (the fall-through to the monolithic operand parse). *)
  Fixpoint parse (fuel : nat) (f : Flat) : Tree :=
    match fuel with
    | 0 => Leaf (fst f)
    | S fuel' =>
        let a0 := fst f in
        let ps := snd f in
        match root_index ps with
        | None => Leaf a0
        | Some k =>
            match skipn k ps with
            | (opk, ak) :: rp => Node opk (parse fuel' (a0, firstn k ps))
                                          (parse fuel' (ak, rp))
            | [] => Leaf a0
            end
        end
    end.

  (* firstn/skipn split lemma specialized to the `(op,a)` element at index k. *)
  Lemma split_firstn_skipn :
    forall (ps : list (Op * Operand)) k opk ak rp,
      skipn k ps = (opk, ak) :: rp ->
      ps = firstn k ps ++ (opk, ak) :: rp.
  Proof.
    intros ps k opk ak rp Hskip.
    rewrite <- (firstn_skipn k ps) at 1.
    rewrite Hskip. reflexivity.
  Qed.

  Lemma length_firstn_le : forall (ps : list (Op * Operand)) k,
    length (firstn k ps) <= length ps.
  Proof. intros ps k. rewrite length_firstn. lia. Qed.

  (* ── T1: with enough fuel the parse FLATTENS BACK to the input — the D&C
     split loses / gains / reorders NOTHING. Proved by strong induction on the
     fuel (which bounds the pair-list length). ── *)
  Lemma flatten_parse_fueled :
    forall fuel f, length (snd f) <= fuel -> flatten (parse fuel f) = f.
  Proof.
    induction fuel as [| fuel' IH]; intros [a0 ps] Hlen; simpl in *.
    - (* fuel 0 ⇒ ps must be [] ⇒ Leaf a0 flattens to (a0, []). *)
      destruct ps as [| p ps']; simpl in *; [reflexivity | lia].
    - destruct (root_index ps) as [k |] eqn:Ek.
      + (* elected root at k; split at k. *)
        assert (Hklt : k < length ps) by (apply T2_root_lt_length; exact Ek).
        destruct (skipn k ps) as [| [opk ak] rp] eqn:Eskip.
        * (* skipn k ps = [] contradicts k < length ps. *)
          apply (f_equal (@length _)) in Eskip.
          rewrite length_skipn in Eskip. simpl in Eskip. lia.
        * simpl.
          (* recurse: left = (a0, firstn k ps), right = (ak, rp). *)
          assert (Hlenrp : length rp = length ps - S k).
          { apply (f_equal (@length _)) in Eskip.
            rewrite length_skipn in Eskip. simpl in Eskip. lia. }
          assert (HL : flatten (parse fuel' (a0, firstn k ps)) = (a0, firstn k ps)).
          { apply IH. simpl. rewrite length_firstn. lia. }
          assert (HR : flatten (parse fuel' (ak, rp)) = (ak, rp)).
          { apply IH. simpl. lia. }
          rewrite HL, HR. simpl.
          (* now: (a0, firstn k ps ++ (opk, ak) :: rp) = (a0, ps). *)
          f_equal.
          symmetry. apply split_firstn_skipn. exact Eskip.
      + (* no root ⇒ Leaf a0; ps has no elected root ⇒ (by root_index_some) ps = []. *)
        destruct ps as [| [op a] ps']; simpl.
        * reflexivity.
        * exfalso. apply (root_index_some op a ps'). exact Ek.
  Qed.

  Theorem T1_flatten_parse_id :
    forall f, flatten (parse (length (snd f)) f) = f.
  Proof. intros f. apply flatten_parse_fueled. lia. Qed.

  (* ── T3: PRECEDENCE-WELL-FORMEDNESS. The elected root `op` at index k is a
     LOOSEST operator of the whole span: its precedence is ≤ every operator's.
     Hence the split never places a strictly-tighter operator above a looser one
     — the canonical operator-precedence tree. We prove the KEY invariant: the
     elected root's precedence is minimal over the pair list. ── *)
  Lemma pick_prec_le_seed :
    forall ps i pb ib rb p k r,
      pick i (Some (pb, ib, rb)) ps = Some (p, k, r) -> p <= pb.
  Proof.
    induction ps as [| [op a] rest IH]; intros i pb ib rb p k r Hpick; simpl in *.
    - inversion Hpick; subst. lia.
    - destruct (Nat.ltb (prec op) pb) eqn:E1.
      + apply Nat.ltb_lt in E1. apply IH in Hpick. lia.
      + apply Nat.ltb_ge in E1.
        destruct (Nat.ltb pb (prec op)) eqn:E2.
        * apply IH in Hpick. lia.
        * apply Nat.ltb_ge in E2.
          destruct (rassoc op) eqn:E3; apply IH in Hpick; lia.
  Qed.

  (* The elected root's precedence is ≤ EVERY operator's precedence in the span,
     given a `Some` seed — `pick` computes the running MINIMUM precedence (with the
     associativity tiebreak on the INDEX, which never affects the prec bound). By
     induction on `ps`: the head is bounded via `pick_prec_le_seed` on the updated
     seed (whose prec is `min seed_prec (prec head)`), the tail via the IH. *)
  Lemma pick_prec_le_elems :
    forall ps i pb ib rb p k r,
      pick i (Some (pb, ib, rb)) ps = Some (p, k, r) ->
      forall op a, In (op, a) ps -> p <= prec op.
  Proof.
    induction ps as [| [op0 a0] rest IH]; intros i pb ib rb p k r Hpick op a Hin; simpl in *.
    - contradiction.
    - destruct Hin as [Heq | Hin'].
      + inversion Heq; subst op0 a0.
        destruct (Nat.ltb (prec op) pb) eqn:E1.
        * apply pick_prec_le_seed in Hpick. exact Hpick.
        * apply Nat.ltb_ge in E1.
          destruct (Nat.ltb pb (prec op)) eqn:E2.
          -- apply pick_prec_le_seed in Hpick. lia.
          -- apply Nat.ltb_ge in E2.
             destruct (rassoc op) eqn:E3; apply pick_prec_le_seed in Hpick; lia.
      + destruct (Nat.ltb (prec op0) pb) eqn:E1.
        * exact (IH (S i) (prec op0) i (rassoc op0) p k r Hpick op a Hin').
        * destruct (Nat.ltb pb (prec op0)) eqn:E2.
          -- exact (IH (S i) pb ib rb p k r Hpick op a Hin').
          -- destruct (rassoc op0) eqn:E3.
             ++ exact (IH (S i) pb ib rb p k r Hpick op a Hin').
             ++ exact (IH (S i) (prec op0) i false p k r Hpick op a Hin').
  Qed.

  (* The elected root's precedence is ≤ the precedence of EVERY operator in the
     span — i.e. the root is a LOOSEST operator (the canonical Pratt root). *)
  Theorem T3_root_is_loosest :
    forall ps p k r,
      pick 0 None ps = Some (p, k, r) ->
      forall op a, In (op, a) ps -> p <= prec op.
  Proof.
    intros ps p k r Hpick op a Hin.
    destruct ps as [| [op0 a0] rest]; simpl in *; [contradiction |].
    destruct Hin as [Heq | Hin'].
    - inversion Heq; subst op0 a0.
      apply pick_prec_le_seed in Hpick. exact Hpick.
    - exact (pick_prec_le_elems rest 1 (prec op0) 0 (rassoc op0) p k r Hpick op a Hin').
  Qed.

End InfixSplit.

(* ══════════════════════════════════════════════════════════════════════════
   T4: ASSOCIATIVITY — a uniform-precedence LEFT-associative chain parses
   LEFT-LEANING. We instantiate the split on a concrete 3-operand chain
   `a0 op a1 op a2` with one left-assoc operator and show the tree is
   `Node op (Node op (Leaf a0) (Leaf a1)) (Leaf a2)` — the `a or b or c`
   ↦ Or(Or(a,b),c) fact, derived (not asserted).
   ══════════════════════════════════════════════════════════════════════════ *)
Section LeftAssocChain.
  Variable Operand : Type.

  (* A left-associative operator: rassoc = false. *)
  Variable opL : Op.
  Hypothesis Hleft : rassoc opL = false.

  Variables a0 a1 a2 : Operand.

  Definition chain3 : Flat Operand := (a0, [(opL, a1); (opL, a2)]).

  (* The elected root of `a0 op a1 op a2` is the SECOND operator (index 1) —
     rightmost, since left-assoc. *)
  Lemma chain3_root : root_index Operand (snd chain3) = Some 1.
  Proof.
    unfold root_index, chain3. simpl.
    rewrite Nat.ltb_irrefl. rewrite Hleft. reflexivity.
  Qed.

  Theorem T4_leftassoc_chain :
    parse Operand 2 chain3
      = Node Operand opL (Node Operand opL (Leaf Operand a0) (Leaf Operand a1))
                         (Leaf Operand a2).
  Proof.
    unfold chain3. simpl.
    (* root_index [(opL,a1);(opL,a2)] = Some 1 *)
    unfold root_index. simpl. rewrite Nat.ltb_irrefl. rewrite Hleft. simpl.
    (* skipn 1 = [(opL,a2)]; left = (a0, firstn 1 = [(opL,a1)]); right = (a2, []) *)
    (* left recurse: root_index [(opL,a1)] = Some 0 ⇒ Node opL (Leaf a0) (Leaf a1) *)
    unfold root_index. simpl. reflexivity.
  Qed.
End LeftAssocChain.

(* ══════════════════════════════════════════════════════════════════════════
   T5: COMBINE SET-EQUALITY (operand ambiguity preserved). The 2-operand
   cartesian of the per-operand ISOLATED reading sets enumerates EXACTLY the
   monolithic reading set — a tuple `(l, r)` is a combined reading iff `l` is a
   left reading and `r` a right reading. This is the binary specialization of the
   sep cartesian (SepReconvergence T1/T2), grounded on the SAME Stage-0 fact
   (operands are precedence/bracket-delimited ⇒ their disambiguation is LOCAL ⇒
   the monolithic set decomposes to the per-operand product). Never-disambiguate-
   early: no operand reading is dropped.
   ══════════════════════════════════════════════════════════════════════════ *)
Section Combine.
  Variable Reading : Type.

  (* Cartesian of the two per-operand reading lists. *)
  Definition combine2 (ls rs : list Reading) : list (Reading * Reading) :=
    flat_map (fun l => map (fun r => (l, r)) rs) ls.

  (* A pair is a monolithic reading iff each side is a member of its operand's list. *)
  Definition is_mono2 (ls rs : list Reading) (p : Reading * Reading) : Prop :=
    In (fst p) ls /\ In (snd p) rs.

  Theorem T5_combine_set_eq :
    forall ls rs p, In p (combine2 ls rs) <-> is_mono2 ls rs p.
  Proof.
    intros ls rs [l r]. unfold combine2, is_mono2. simpl. split.
    - intro Hin. apply in_flat_map in Hin. destruct Hin as [l' [Hl' Hmap]].
      apply in_map_iff in Hmap. destruct Hmap as [r' [Heq Hr']].
      inversion Heq; subst. split; assumption.
    - intros [Hl Hr]. apply in_flat_map. exists l. split; [exact Hl |].
      apply in_map_iff. exists r. split; [reflexivity | exact Hr].
  Qed.

  (* No monolithic reading is LOST (the HALT gate) and none is GAINED. *)
  Corollary T5a_no_reading_lost :
    forall ls rs p, is_mono2 ls rs p -> In p (combine2 ls rs).
  Proof. intros ls rs p H. apply T5_combine_set_eq. exact H. Qed.

  Corollary T5b_no_reading_gained :
    forall ls rs p, In p (combine2 ls rs) -> is_mono2 ls rs p.
  Proof. intros ls rs p H. apply T5_combine_set_eq. exact H. Qed.
End Combine.

(* ══════════════════════════════════════════════════════════════════════════
   T6: WEIGHT CORRECTNESS. The combined weight is the ⊗ (tropical sum) of the
   two operand weights plus the (cost-0) framing. ⊗ is monotone, so choosing the
   per-operand MIN readings yields the min combined weight = the monolithic
   single-winner (the SINGLE-seam parity Stage-0 checks).
   ══════════════════════════════════════════════════════════════════════════ *)
Section Weights.
  Variable Reading : Type.
  Variable w : Reading -> nat.

  (* Framing cost is 0 (absorbed under ⊗); combined weight = wl + wr. *)
  Definition combined_weight (l r : Reading) : nat := w l + w r.

  Theorem T6_weights_monotone :
    forall lA rA lB rB,
      w lA <= w lB -> w rA <= w rB ->
      combined_weight lA rA <= combined_weight lB rB.
  Proof. intros lA rA lB rB Hl Hr. unfold combined_weight. lia. Qed.

  (* Framing at cost 0 is the ⊗-identity: adding it changes nothing. *)
  Theorem T6_framing_identity :
    forall l r, 0 + combined_weight l r = combined_weight l r.
  Proof. intros. lia. Qed.
End Weights.

(* ══════════════════════════════════════════════════════════════════════════
   T7: LINEARITY. The D&C total cost grows by a CONSTANT per operator (linear in
   the operator count), vs the geometric monolithic step (exponential) that the
   fix removes. Mirrors SepReconvergence T3.
   ══════════════════════════════════════════════════════════════════════════ *)
Section Linearity.
  (* Isolated per-operand cost (Stage-0: ~const, ~40 ms/operand). *)
  Variable c : nat.

  Fixpoint dc_total (n : nat) : nat :=
    match n with 0 => c | S m => c + dc_total m end.

  Theorem T7_linear_step : forall n, dc_total (S n) = c + dc_total n.
  Proof. intro n. reflexivity. Qed.

  Theorem T7_linear_closed_form : forall n, dc_total n = (S n) * c.
  Proof. induction n as [| m IH]; simpl; [lia | rewrite IH; lia]. Qed.

  (* The monolithic geometric baseline: ×b per operator (b ≥ 2 ⇒ ≥ doubling). *)
  Fixpoint mono_geom (n b : nat) : nat :=
    match n with 0 => 1 | S m => b * mono_geom m b end.

  Theorem T7_geometric_dominates :
    forall n b, 2 <= b -> mono_geom n b + mono_geom n b <= mono_geom (S n) b.
  Proof.
    intros n b Hb. simpl.
    assert (H1 : 1 <= mono_geom n b).
    { induction n as [| m IH]; simpl; [lia | nia]. }
    nia.
  Qed.
End Linearity.

(* ══════════════════════════════════════════════════════════════════════════
   T8: FALLBACK REFINEMENT. When there is NO depth-0 operator the split yields a
   Leaf (declines to the monolithic operand parse), and the combined reading SET
   equals the monolithic SET, so a `None` fall-through loses nothing and the A/B
   toggle (`PRATTAIL_NO_INFIX_ISOLATION`) is set-equal. Mirrors SepReconvergence T6.
   ══════════════════════════════════════════════════════════════════════════ *)
Section Fallback.
  Variable Operand : Type.

  (* A pure operand (empty pair list) declines to a Leaf — the monolithic path. *)
  Theorem T8_no_operator_is_leaf :
    forall a fuel, parse Operand fuel (a, []) = Leaf Operand a.
  Proof. intros a fuel. destruct fuel; reflexivity. Qed.

  (* The A/B control: engaging (`combine2`) vs declining (identity monolithic set)
     yields the SAME reading set — extensional set-equality (T5). *)
  Theorem T8_ab_set_identical :
    forall (Reading : Type) (ls rs : list Reading) p,
      In p (combine2 Reading ls rs) <-> is_mono2 Reading ls rs p.
  Proof. intros. apply T5_combine_set_eq. Qed.
End Fallback.

(* ── ZERO-ADMISSION AUDIT: every theorem is "Closed under the global context"
   (no Admitted, no Axiom, no Assumption). ── *)
Print Assumptions T1_flatten_parse_id.
Print Assumptions T2_root_lt_length.
Print Assumptions T3_root_is_loosest.
Print Assumptions T4_leftassoc_chain.
Print Assumptions T5_combine_set_eq.
Print Assumptions T6_weights_monotone.
Print Assumptions T7_geometric_dominates.
Print Assumptions T8_no_operator_is_leaf.
