(*
 * LogicTFairness: Fairness proofs for the LogicT fair backtracking
 * search framework.
 *
 * Models LogicStream as finite lists and proves:
 *   - Interleave fairness: alternation preserves all elements
 *   - msplit identity and mzero laws
 *   - Interleave commutativity up to reordering (Permutation)
 *
 * The key insight is that interleave(a, b) alternates elements from
 * a and b, guaranteeing that both branches are explored "fairly".
 * For finite streams (lists), this means every element from both
 * lists appears in the interleaved result, and the result is a
 * permutation of the concatenation.
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition             | Rust Code                          | Location
 *   ----------------------------|------------------------------------|--------------------------
 *   interleave                  | LogicStream::interleave()          | logict.rs
 *   msplit                      | LogicStream::msplit()              | logict.rs
 *   mzero (nil)                 | LogicStream::mzero()               | logict.rs
 *   mplus (app)                 | LogicStream::mplus()               | logict.rs
 *   LogicStream (list)          | LogicStream<T>                     | logict.rs:87
 *
 * Reference: Kiselyov, Shan, Friedman & Sabry (ICFP 2005)
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Permutation.
From Stdlib Require Import FunInd.

Import ListNotations.

(* ===================================================================== *)
(*  Stream Model: Finite Lists                                             *)
(*                                                                         *)
(*  We model LogicStream<T> as list A for the finite case.                 *)
(*  This is sufficient to prove the core fairness properties, since:       *)
(*    - Every element appears in the interleaved result                     *)
(*    - The interleaved result is a permutation of the concatenation        *)
(*    - msplit laws hold directly from list structure                       *)
(* ===================================================================== *)

Section LogicTFairness.

  Variable A : Type.

  (* ------------------------------------------------------------------- *)
  (*  Interleave: fair disjunction via alternation                         *)
  (* ------------------------------------------------------------------- *)

  (* interleave(a, b) alternates elements from a and b.
     This mirrors LogicStream::interleave() in logict.rs, which uses
     a VecDeque-based round-robin scheduler. For finite lists, this
     reduces to alternating cons from each list. *)
  (* We define interleave via a fuel-based helper to satisfy Coq's
     termination checker, since the recursive call swaps arguments. *)
  Fixpoint interleave_fuel (fuel : nat) (a b : list A) : list A :=
    match fuel with
    | O => a ++ b  (* fallback: concatenate remaining *)
    | S fuel' =>
      match a with
      | [] => b
      | x :: a' => x :: interleave_fuel fuel' b a'
      end
    end.

  Definition interleave (a b : list A) : list A :=
    interleave_fuel (length a + length b) a b.

  (* Helper: interleave_fuel with fuel >= total length behaves identically *)
  Lemma interleave_fuel_ge : forall (n m : nat) (a b : list A),
    length a + length b <= n ->
    length a + length b <= m ->
    interleave_fuel n a b = interleave_fuel m a b.
  Proof.
    intro n. induction n as [| n' IHn]; intros m a b Hn Hm.
    - (* n = 0 → both lists empty *)
      assert (length a = 0) as Ha by lia.
      assert (length b = 0) as Hb by lia.
      apply length_zero_iff_nil in Ha. apply length_zero_iff_nil in Hb.
      subst. destruct m; simpl; reflexivity.
    - destruct m as [| m'].
      + (* m = 0 → both lists empty *)
        assert (length a = 0) as Ha by lia.
        assert (length b = 0) as Hb by lia.
        apply length_zero_iff_nil in Ha. apply length_zero_iff_nil in Hb.
        subst. simpl. reflexivity.
      + destruct a as [| x a'].
        * simpl. reflexivity.
        * simpl. f_equal.
          apply IHn; simpl in *; lia.
  Qed.

  (* Unfolding lemma for interleave *)
  Lemma interleave_nil : forall (b : list A),
    interleave [] b = b.
  Proof.
    intro b. unfold interleave. simpl.
    destruct (length b) eqn:E.
    - apply length_zero_iff_nil in E. subst. reflexivity.
    - simpl. reflexivity.
  Qed.

  Lemma interleave_cons : forall (x : A) (a' b : list A),
    interleave (x :: a') b = x :: interleave b a'.
  Proof.
    intros x a' b. unfold interleave.
    simpl length at 1. rewrite Nat.add_succ_l.
    simpl interleave_fuel at 1.
    f_equal.
    apply interleave_fuel_ge; simpl; lia.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  msplit: peek at the first element + remainder                        *)
  (* ------------------------------------------------------------------- *)

  (* msplit decomposes a stream into its head and tail.
     Returns None for empty streams, Some (head, tail) otherwise.
     Mirrors LogicStream::msplit() in logict.rs. *)
  Definition msplit (s : list A) : option (A * list A) :=
    match s with
    | [] => None
    | x :: xs => Some (x, xs)
    end.

  (* ===================================================================== *)
  (*  msplit Laws                                                           *)
  (* ===================================================================== *)

  (* msplit identity: msplit of a cons is Some *)
  Theorem msplit_identity : forall (x : A) (xs : list A),
    msplit (x :: xs) = Some (x, xs).
  Proof. reflexivity. Qed.

  (* msplit mzero: msplit of empty stream is None *)
  Theorem msplit_mzero : msplit [] = None.
  Proof. reflexivity. Qed.

  (* msplit reconstruction: if msplit returns Some (h, t) then s = h :: t *)
  Theorem msplit_reconstruct : forall (s : list A) (h : A) (t : list A),
    msplit s = Some (h, t) -> s = h :: t.
  Proof.
    intros s h t Hsplit. destruct s as [| x xs].
    - discriminate.
    - simpl in Hsplit. injection Hsplit. intros Ht Hh.
      subst. reflexivity.
  Qed.

  (* ===================================================================== *)
  (*  Interleave Length                                                      *)
  (* ===================================================================== *)

  (* The length of interleave(a, b) equals the sum of lengths.
     This is the first step toward proving all elements are preserved. *)
  Lemma interleave_length_aux : forall (n : nat) (a b : list A),
    length a + length b = n ->
    length (interleave a b) = length a + length b.
  Proof.
    intro n. induction n as [| n' IH]; intros a b Hlen.
    - assert (length a = 0) as Ha by lia.
      assert (length b = 0) as Hb by lia.
      apply length_zero_iff_nil in Ha. apply length_zero_iff_nil in Hb.
      subst. rewrite interleave_nil. simpl. reflexivity.
    - destruct a as [| x a'].
      + rewrite interleave_nil. reflexivity.
      + rewrite interleave_cons. simpl.
        rewrite IH; simpl in *; lia.
  Qed.

  Theorem interleave_length : forall (a b : list A),
    length (interleave a b) = length a + length b.
  Proof.
    intros a b. apply interleave_length_aux with (n := length a + length b).
    reflexivity.
  Qed.

  (* ===================================================================== *)
  (*  Interleave Fairness: All Elements Preserved                           *)
  (*                                                                        *)
  (*  The main fairness theorem: interleave(a, b) is a permutation of      *)
  (*  a ++ b. This means every element from both branches appears in        *)
  (*  the result exactly as many times as it appears in the input.          *)
  (* ===================================================================== *)

  (* Key lemma: interleave(a, b) is a permutation of a ++ b *)
  Lemma interleave_fairness_aux : forall (n : nat) (a b : list A),
    length a + length b = n ->
    Permutation (interleave a b) (a ++ b).
  Proof.
    intro n. induction n as [| n' IH]; intros a b Hlen.
    - assert (length a = 0) as Ha by lia.
      assert (length b = 0) as Hb by lia.
      apply length_zero_iff_nil in Ha. apply length_zero_iff_nil in Hb.
      subst. rewrite interleave_nil. simpl. apply Permutation_refl.
    - destruct a as [| x a'].
      + rewrite interleave_nil. simpl. apply Permutation_refl.
      + rewrite interleave_cons. simpl.
        apply perm_skip.
        eapply Permutation_trans.
        * apply IH. simpl in *. lia.
        * apply Permutation_app_comm.
  Qed.

  Theorem interleave_fairness : forall (a b : list A),
    Permutation (interleave a b) (a ++ b).
  Proof.
    intros a b. apply interleave_fairness_aux with (n := length a + length b).
    reflexivity.
  Qed.

  (* Corollary: every element of a appears in interleave(a, b) *)
  Corollary interleave_contains_left : forall (a b : list A) (x : A),
    In x a -> In x (interleave a b).
  Proof.
    intros a b x Hin.
    apply Permutation_in with (a ++ b).
    - apply Permutation_sym. apply interleave_fairness.
    - apply in_or_app. left. exact Hin.
  Qed.

  (* Corollary: every element of b appears in interleave(a, b) *)
  Corollary interleave_contains_right : forall (a b : list A) (x : A),
    In x b -> In x (interleave a b).
  Proof.
    intros a b x Hin.
    apply Permutation_in with (a ++ b).
    - apply Permutation_sym. apply interleave_fairness.
    - apply in_or_app. right. exact Hin.
  Qed.

  (* ===================================================================== *)
  (*  Interleave Commutativity (up to reordering)                           *)
  (*                                                                        *)
  (*  interleave(a, b) and interleave(b, a) are both permutations of       *)
  (*  a ++ b, hence they are permutations of each other.                    *)
  (* ===================================================================== *)

  Theorem interleave_comm_up_to_reordering : forall (a b : list A),
    Permutation (interleave a b) (interleave b a).
  Proof.
    intros a b.
    eapply Permutation_trans.
    - apply interleave_fairness.
    - eapply Permutation_trans.
      + apply Permutation_app_comm.
      + apply Permutation_sym. apply interleave_fairness.
  Qed.

  (* ===================================================================== *)
  (*  Interleave with Empty Streams                                         *)
  (* ===================================================================== *)

  (* interleave([], b) = b *)
  Theorem interleave_nil_left : forall (b : list A),
    interleave [] b = b.
  Proof. intro b. apply interleave_nil. Qed.

  (* interleave(a, []) = a *)
  Theorem interleave_nil_right : forall (a : list A),
    interleave a [] = a.
  Proof.
    intro a. destruct a as [| x a'].
    - apply interleave_nil.
    - rewrite interleave_cons. f_equal. apply interleave_nil.
  Qed.

  (* ===================================================================== *)
  (*  mplus (concatenation) Laws                                            *)
  (* ===================================================================== *)

  (* mplus is just list concatenation (app).
     These laws mirror LogicStream::mplus() in logict.rs. *)

  (* mplus with mzero on the left is identity *)
  Theorem mplus_mzero_left : forall (s : list A),
    [] ++ s = s.
  Proof. reflexivity. Qed.

  (* mplus with mzero on the right is identity *)
  Theorem mplus_mzero_right : forall (s : list A),
    s ++ [] = s.
  Proof. apply app_nil_r. Qed.

  (* mplus is associative *)
  Theorem mplus_assoc : forall (a b c : list A),
    (a ++ b) ++ c = a ++ (b ++ c).
  Proof. intros. symmetry. apply app_assoc. Qed.

  (* ===================================================================== *)
  (*  Interleave Alternation Property                                       *)
  (*                                                                        *)
  (*  For non-empty streams, the first element of a is first in             *)
  (*  interleave(a, b), and the first element of b is second.               *)
  (*  This is the concrete "alternation" guarantee.                         *)
  (* ===================================================================== *)

  (* First element comes from the first stream *)
  Theorem interleave_first : forall (x : A) (a' b : list A),
    hd_error (interleave (x :: a') b) = Some x.
  Proof. intros. rewrite interleave_cons. reflexivity. Qed.

  (* Second element comes from the second stream (when both non-empty) *)
  Theorem interleave_second : forall (x : A) (a' : list A) (y : A) (b' : list A),
    nth_error (interleave (x :: a') (y :: b')) 1 = Some y.
  Proof.
    intros. rewrite interleave_cons.
    (* Goal: nth_error (x :: interleave (y :: b') a') 1 = Some y *)
    change (nth_error (x :: interleave (y :: b') a') 1) with
           (nth_error (interleave (y :: b') a') 0).
    rewrite interleave_cons. reflexivity.
  Qed.

  (* ===================================================================== *)
  (*  Interleave Singleton                                                  *)
  (* ===================================================================== *)

  (* interleave([x], [y]) = [x, y] *)
  Theorem interleave_singletons : forall (x y : A),
    interleave [x] [y] = [x; y].
  Proof.
    intros.
    rewrite interleave_cons.  (* x :: interleave [y] [] *)
    rewrite interleave_cons.  (* x :: y :: interleave [] [] *)
    rewrite interleave_nil.   (* x :: y :: [] *)
    reflexivity.
  Qed.

  (* ===================================================================== *)
  (*  Once (commit to first result)                                         *)
  (* ===================================================================== *)

  (* once extracts the first element if it exists.
     Mirrors LogicStream::once() in logict.rs. *)
  Definition once (s : list A) : list A :=
    match s with
    | [] => []
    | x :: _ => [x]
    end.

  (* once of non-empty returns singleton *)
  Theorem once_nonempty : forall (x : A) (xs : list A),
    once (x :: xs) = [x].
  Proof. reflexivity. Qed.

  (* once of mzero returns mzero *)
  Theorem once_mzero : once [] = [].
  Proof. reflexivity. Qed.

  (* once is idempotent *)
  Theorem once_idempotent : forall (s : list A),
    once (once s) = once s.
  Proof.
    intros s. destruct s as [| x xs].
    - reflexivity.
    - reflexivity.
  Qed.

  (* ===================================================================== *)
  (*  gnot (negation as finite failure)                                     *)
  (* ===================================================================== *)

  (* gnot succeeds (returns [()]-like value) iff the stream is empty.
     For our list model, we use a bool indicator. *)
  Definition gnot_bool (s : list A) : bool :=
    match s with
    | [] => true
    | _ :: _ => false
    end.

  Theorem gnot_mzero : gnot_bool [] = true.
  Proof. reflexivity. Qed.

  Theorem gnot_nonempty : forall (x : A) (xs : list A),
    gnot_bool (x :: xs) = false.
  Proof. reflexivity. Qed.

  (* ===================================================================== *)
  (*  ifte (soft cut / if-then-else)                                        *)
  (* ===================================================================== *)

  (* ifte s f g: if s has results, apply f to each; otherwise use g.
     Mirrors LogicStream::ifte() in logict.rs. *)
  Definition ifte (s : list A) (f : A -> list A) (g : list A) : list A :=
    match s with
    | [] => g
    | _ => flat_map f s
    end.

  (* ifte with empty stream uses fallback *)
  Theorem ifte_mzero : forall (f : A -> list A) (g : list A),
    ifte [] f g = g.
  Proof. reflexivity. Qed.

  (* ifte with non-empty stream applies f *)
  Theorem ifte_nonempty : forall (x : A) (xs : list A) (f : A -> list A) (g : list A),
    ifte (x :: xs) f g = flat_map f (x :: xs).
  Proof. reflexivity. Qed.

End LogicTFairness.

(* ===================================================================== *)
(*  Abstraction Gaps                                                      *)
(*                                                                        *)
(*  1. Eager vs lazy: Rust LogicStream<T> uses VecDeque<Branch<T>> with   *)
(*     Branch::Suspended for lazy evaluation. Rocq uses eager list A.     *)
(*     Fairness (Permutation of a ++ b) holds regardless because it       *)
(*     concerns the multiset of results, not evaluation strategy.         *)
(*  2. Suspension scheduling: Rust interleave() does round-robin on a     *)
(*     VecDeque, alternating Branch::Ready and Branch::Suspended. Rocq's  *)
(*     alternating cons captures scheduling order but not suspension.      *)
(*  3. Infinite streams: Rust supports infinite LogicStreams via           *)
(*     suspension chains. Rocq model is finite lists only.                *)
(*  4. Memory model: Rust VecDeque has amortized O(1) push/pop; Rocq     *)
(*     list has O(n) append. Complexity gap, not correctness gap.         *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  Summary of Results                                                     *)
(*                                                                         *)
(*  msplit Laws:                                                           *)
(*    1.  msplit_identity      — msplit(x :: xs) = Some (x, xs)            *)
(*    2.  msplit_mzero         — msplit([]) = None                          *)
(*    3.  msplit_reconstruct   — msplit(s) = Some(h,t) -> s = h :: t       *)
(*                                                                         *)
(*  Interleave Fairness:                                                   *)
(*    4.  interleave_length    — |interleave(a,b)| = |a| + |b|             *)
(*    5.  interleave_fairness  — Permutation(interleave(a,b), a ++ b)      *)
(*    6.  interleave_contains_left  — In x a -> In x (interleave a b)      *)
(*    7.  interleave_contains_right — In x b -> In x (interleave a b)      *)
(*                                                                         *)
(*  Interleave Properties:                                                 *)
(*    8.  interleave_comm_up_to_reordering                                 *)
(*           — Permutation(interleave(a,b), interleave(b,a))               *)
(*    9.  interleave_nil_left  — interleave([], b) = b                     *)
(*    10. interleave_nil_right — interleave(a, []) = a                     *)
(*    11. interleave_first     — hd(interleave(x::a', b)) = x              *)
(*    12. interleave_second    — nth 1 (interleave(x::a', y::b')) = y       *)
(*    13. interleave_singletons — interleave([x],[y]) = [x;y]              *)
(*                                                                         *)
(*  mplus Laws:                                                            *)
(*    14. mplus_mzero_left     — [] ++ s = s                               *)
(*    15. mplus_mzero_right    — s ++ [] = s                               *)
(*    16. mplus_assoc          — (a ++ b) ++ c = a ++ (b ++ c)             *)
(*                                                                         *)
(*  once / gnot / ifte:                                                    *)
(*    17. once_nonempty        — once(x :: xs) = [x]                       *)
(*    18. once_mzero           — once([]) = []                              *)
(*    19. once_idempotent      — once(once(s)) = once(s)                   *)
(*    20. gnot_mzero           — gnot([]) = true                            *)
(*    21. gnot_nonempty        — gnot(x :: xs) = false                      *)
(*    22. ifte_mzero           — ifte([], f, g) = g                         *)
(*    23. ifte_nonempty        — ifte(x::xs, f, g) = flat_map f (x::xs)    *)
(*                                                                         *)
(*  All proofs are COMPLETE -- zero Admitted.                               *)
(* ===================================================================== *)
