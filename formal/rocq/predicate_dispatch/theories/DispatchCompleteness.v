(*
 * DispatchCompleteness: Formal verification of the Predicate Dispatch Automaton.
 *
 * Proves three key properties of the dispatch mechanism:
 *
 *   1. Completeness: Every non-zero signature is accepted by the dispatch SFA
 *   2. Zero Rejection: The zero signature is rejected
 *   3. Base Invariant: extract_features always produces signatures with M1 and M10
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition              | Rust Code                               | Location
 *   -----------------------------|------------------------------------------|---------------------------------
 *   PredicateSignature           | PredicateSignature(u16)                 | predicate_dispatch.rs
 *   sig_contains                 | PredicateSignature::contains()          | predicate_dispatch.rs
 *   sig_union                    | PredicateSignature::union()             | predicate_dispatch.rs
 *   sig_set                      | PredicateSignature::set()               | predicate_dispatch.rs
 *   BASE_SIG                     | PredicateSignature::BASE                | predicate_dispatch.rs
 *   dispatch_accepts             | build_dispatch_sfa() + accepts()        | predicate_dispatch.rs
 *   extract_features_sig         | extract_features() .signature field     | predicate_dispatch.rs
 *   SignaturePred                | SignaturePred enum                      | predicate_dispatch.rs
 *   eval_pred                    | DispatchAlgebra::evaluate()             | predicate_dispatch.rs
 *   witness_for_has_bit          | DispatchAlgebra::witness() fast path    | predicate_dispatch.rs
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.

(* ===================================================================== *)
(*  §1 PredicateSignature — 11-bit bitvector model                       *)
(* ===================================================================== *)

(* We model the signature as a natural number (u16 in Rust).
   Bit i corresponds to module M_{i+1}.

   Domain representation:
   Rocq: nat (unbounded natural number)
   Rust:  u16 (16-bit unsigned integer)

   The Rocq proofs are valid for any nat, which is a superset of u16.
   All module bits fit in 11 bits (0..10), so u16 is sufficient.
   The Rocq proofs therefore cover the Rust domain and more.

   If future modules exceed 16 bits, the Rust type must widen but
   the Rocq proofs remain valid without change. *)

Definition PredicateSignature := nat.

(* Bit constants — matching PredicateSignature::M*_* in Rust *)
Definition M1_SYMBOLIC      := 1.     (* 1 << 0 *)
Definition M2_BUCHI         := 2.     (* 1 << 1 *)
Definition M3_AWA           := 4.     (* 1 << 2 *)
Definition M4_VPA           := 8.     (* 1 << 3 *)
Definition M5_PARITY_TREE   := 16.    (* 1 << 4 *)
Definition M6_REGISTER      := 32.    (* 1 << 5 *)
Definition M7_PROBABILISTIC := 64.    (* 1 << 6 *)
Definition M8_MULTI_TAPE    := 128.   (* 1 << 7 *)
Definition M9_MULTISET      := 256.   (* 1 << 8 *)
Definition M10_MSO          := 512.   (* 1 << 9 *)
Definition M11_TWO_WAY      := 1024.  (* 1 << 10 *)

Definition BASE_SIG := Nat.lor M1_SYMBOLIC M10_MSO.  (* 513 = 0x0201 *)

(* Verify the value is what we expect *)
Lemma base_sig_value : BASE_SIG = 513.
Proof. unfold BASE_SIG, M1_SYMBOLIC, M10_MSO. vm_compute. reflexivity. Qed.

(* Document that addition and bitwise-or coincide for disjoint bits *)
Lemma base_sig_add_equiv : M1_SYMBOLIC + M10_MSO = Nat.lor M1_SYMBOLIC M10_MSO.
Proof. vm_compute. reflexivity. Qed.

(* Bitwise operations modeled via Nat.land, Nat.lor *)
Definition sig_contains (sig module_bit : nat) : bool :=
  negb (Nat.eqb (Nat.land sig module_bit) 0).

Definition sig_union (a b : nat) : nat := Nat.lor a b.

Definition sig_set (sig module_bit : nat) : nat := Nat.lor sig module_bit.

(* ===================================================================== *)
(*  §2 Helper lemmas for bitwise operations                              *)
(* ===================================================================== *)

(* Helper: testbit of 0 is always false *)
Lemma testbit_zero : forall n, Nat.testbit 0 n = false.
Proof.
  induction n as [| n' IHn].
  - reflexivity.
  - simpl. exact IHn.
Qed.

(* Key property: Nat.lor preserves existing bits *)
Lemma lor_contains_left : forall a b bit,
  Nat.land a bit <> 0 -> Nat.land (Nat.lor a b) bit <> 0.
Proof.
  intros a b bit Ha Habs.
  apply Ha. clear Ha.
  apply Nat.bits_inj. intro n.
  rewrite Nat.land_spec, testbit_zero.
  (* Goal: Nat.testbit a n && Nat.testbit bit n = false *)
  assert (Nat.testbit (Nat.land (Nat.lor a b) bit) n = false) as H.
  { rewrite Habs. apply testbit_zero. }
  rewrite Nat.land_spec, Nat.lor_spec in H.
  (* H: (Nat.testbit a n || Nat.testbit b n) && Nat.testbit bit n = false *)
  destruct (Nat.testbit bit n) eqn:Ebit.
  - rewrite Bool.andb_true_r in H.
    apply Bool.orb_false_iff in H.
    destruct H as [Ha _]. rewrite Ha. reflexivity.
  - apply Bool.andb_false_r.
Qed.

Lemma lor_contains_right : forall a b bit,
  Nat.land b bit <> 0 -> Nat.land (Nat.lor a b) bit <> 0.
Proof.
  intros a b bit H.
  rewrite Nat.lor_comm.
  apply lor_contains_left. exact H.
Qed.

(* BASE_SIG contains M1 *)
Lemma base_contains_m1 : Nat.land BASE_SIG M1_SYMBOLIC <> 0.
Proof.
  unfold BASE_SIG, M1_SYMBOLIC, M10_MSO.
  vm_compute. discriminate.
Qed.

(* BASE_SIG contains M10 *)
Lemma base_contains_m10 : Nat.land BASE_SIG M10_MSO <> 0.
Proof.
  unfold BASE_SIG, M1_SYMBOLIC, M10_MSO.
  vm_compute. discriminate.
Qed.

(* ===================================================================== *)
(*  §3 SignaturePred — Boolean predicates over signatures                *)
(* ===================================================================== *)

Inductive SignaturePred :=
  | SPTrue  : SignaturePred
  | SPFalse : SignaturePred
  | HasBit  : nat -> SignaturePred
  | SPAnd   : SignaturePred -> SignaturePred -> SignaturePred
  | SPOr    : SignaturePred -> SignaturePred -> SignaturePred
  | SPNot   : SignaturePred -> SignaturePred.

Fixpoint eval_pred (p : SignaturePred) (sig : PredicateSignature) : bool :=
  match p with
  | SPTrue      => true
  | SPFalse     => false
  | HasBit bit  => sig_contains sig bit
  | SPAnd a b   => andb (eval_pred a sig) (eval_pred b sig)
  | SPOr a b    => orb (eval_pred a sig) (eval_pred b sig)
  | SPNot a     => negb (eval_pred a sig)
  end.

(* ===================================================================== *)
(*  §4 Dispatch SFA — acceptance model                                   *)
(* ===================================================================== *)

(* The dispatch SFA has 13 states:
   - q0 (initial)
   - q_M1 through q_M11 (accepting)
   - q_bot (rejecting)

   Transitions: q0 --HasBit(i)--> q_Mi for i in {0..10}
                q0 --not(any HasBit)--> q_bot

   A signature is accepted iff any module state is reachable,
   i.e., any bit in the signature is set. *)

Definition dispatch_accepts (sig : PredicateSignature) : bool :=
  negb (Nat.eqb sig 0).

(* Acceptance is equivalent to: exists a module bit that is set *)
Lemma dispatch_accepts_iff_nonzero : forall sig,
  dispatch_accepts sig = true <-> sig <> 0.
Proof.
  intro sig. unfold dispatch_accepts.
  split.
  - intro H. apply Bool.negb_true_iff in H.
    apply Nat.eqb_neq in H. exact H.
  - intro H. apply Bool.negb_true_iff.
    apply Nat.eqb_neq. exact H.
Qed.

(* ===================================================================== *)
(*  §4.1 Abstraction Gap: Simplified vs. SFA acceptance                  *)
(* ===================================================================== *)

(* The Rocq model uses dispatch_accepts(sig) := sig ≠ 0 as a simplified
   acceptance criterion. The Rust implementation uses a full 13-state SFA
   (build_dispatch_sfa()) with explicit transitions:
     q₀ --HasBit(i)--> q_Mi  for each i ∈ {0,...,10}
     q₀ --¬(∨ HasBit(i))--> q_⊥

   These are provably equivalent because:
   (a) sig ≠ 0 ⟹ ∃i, bit i is set ⟹ HasBit(i) transition fires ⟹ q_Mi ∈ F
   (b) sig = 0 ⟹ no bit is set ⟹ ¬(∨ HasBit(i)) fires ⟹ q_⊥ ∉ F

   The nonzero check is sound for the 11-bit domain. The SFA provides
   additional structure (per-module reachability) not modeled here. *)

(* SFA State Count Justification (not formally proven):
   - 1 initial state (q₀): required by SFA definition
   - 11 module states (q_M1..q_M11): one per module bit, all accepting
   - 1 reject state (q_⊥): catches zero-signature (no bits set)
   - Total: 13 states
   - This is NOT proven minimal. Collapsing all q_Mi into one accepting
     state would give a 3-state NFA, but per-module states are needed
     for diagnostic reporting (which module was activated). *)

(* ===================================================================== *)
(*  §5 Theorem 3.1: Completeness                                        *)
(* ===================================================================== *)

(* Every non-zero signature is accepted by the dispatch SFA. *)

Theorem dispatch_completeness : forall sig : PredicateSignature,
  sig <> 0 -> dispatch_accepts sig = true.
Proof.
  intros sig Hsig.
  apply dispatch_accepts_iff_nonzero. exact Hsig.
Qed.

(* ===================================================================== *)
(*  §6 Theorem 3.2: Zero Rejection                                      *)
(* ===================================================================== *)

(* The zero signature is rejected. *)

Theorem dispatch_zero_rejected :
  dispatch_accepts 0 = false.
Proof.
  unfold dispatch_accepts. simpl. reflexivity.
Qed.

(* ===================================================================== *)
(*  §7 Theorem 3.3: Base Module Invariant                                *)
(* ===================================================================== *)

(* Model of extract_features: starts from BASE_SIG and only adds bits.
   We model this as: the result is always BASE_SIG lor (some extra bits). *)

(* Any signature that is a union with BASE_SIG contains M1 *)
Theorem base_invariant_m1 : forall extra : nat,
  Nat.land (sig_union BASE_SIG extra) M1_SYMBOLIC <> 0.
Proof.
  intro extra.
  unfold sig_union.
  apply lor_contains_left.
  exact base_contains_m1.
Qed.

(* Any signature that is a union with BASE_SIG contains M10 *)
Theorem base_invariant_m10 : forall extra : nat,
  Nat.land (sig_union BASE_SIG extra) M10_MSO <> 0.
Proof.
  intro extra.
  unfold sig_union.
  apply lor_contains_left.
  exact base_contains_m10.
Qed.

(* Combined: extract_features output is always accepted *)
Theorem extract_features_always_accepted : forall extra : nat,
  dispatch_accepts (sig_union BASE_SIG extra) = true.
Proof.
  intro extra.
  apply dispatch_completeness.
  unfold sig_union.
  intro Heq.
  assert (Nat.land (Nat.lor BASE_SIG extra) M1_SYMBOLIC <> 0) as Hm1.
  { apply lor_contains_left. exact base_contains_m1. }
  rewrite Heq in Hm1. simpl in Hm1. contradiction.
Qed.

(* ===================================================================== *)
(*  §7.1 Trust Boundary: extract_features algorithm                      *)
(* ===================================================================== *)

(* The Rust function extract_features(expr, ctx) performs a post-order
   AST traversal of PredicateExpr, accumulating bits into a signature.

   Rocq model: We model extract_features output as sig_union BASE_SIG extra
   for some extra : nat. This captures the essential invariant:
     - extract_features initializes signature = PredicateSignature::new()
       which equals BASE (M1 | M10)
     - walk_predicate only calls signature.set(bit), i.e., sig |= bit
     - No bit-clearing operation exists

   What IS proven (Theorems base_invariant_m1, base_invariant_m10):
     - Output always contains M1 (Symbolic) and M10 (MSO)
     - Output is always non-zero (Corollary extract_features_nonzero)
     - Output is always accepted by the dispatch SFA

   What is NOT proven (trust boundary):
     - Soundness of morpheme detection (each AST pattern sets correct bits)
     - Completeness of morpheme detection (no relevant pattern is missed)
     - Correctness of cross-channel detection heuristic
     - Multi-guard heuristic (≥2 channels → M7 + M8)

   These require a formalization of PredicateExpr that is outside the scope
   of this proof. The Rust implementation validates these via 110 tests
   including proptest-based property tests. *)

(* Formal model: extract_features output is always BASE_SIG ∪ extra_bits *)
Definition extract_features_sig (extra : nat) : PredicateSignature :=
  sig_union BASE_SIG extra.

(* This is the precondition for all base invariant theorems *)
Lemma extract_features_sig_contains_base : forall extra,
  sig_contains (extract_features_sig extra) M1_SYMBOLIC = true /\
  sig_contains (extract_features_sig extra) M10_MSO = true.
Proof.
  intro extra. unfold extract_features_sig.
  split.
  - unfold sig_contains, sig_union.
    apply Bool.negb_true_iff, Nat.eqb_neq.
    apply lor_contains_left. exact base_contains_m1.
  - unfold sig_contains, sig_union.
    apply Bool.negb_true_iff, Nat.eqb_neq.
    apply lor_contains_left. exact base_contains_m10.
Qed.

(* ===================================================================== *)
(*  §8 Corollary 3.1: Non-degeneracy of extract_features                *)
(* ===================================================================== *)

(* PD01 cannot fire for extract_features output because:
   - PD01 fires when signature = BASE_SIG (only base modules)
   - But we prove that every extract_features output has BASE_SIG bits set
   - The question is whether ONLY base bits are set.
   - This depends on the formula structure, not on dispatch correctness.
   - What we CAN prove: extract_features output is never 0. *)

Corollary extract_features_nonzero : forall extra : nat,
  sig_union BASE_SIG extra <> 0.
Proof.
  intro extra.
  unfold sig_union.
  intro Heq.
  assert (Nat.land (Nat.lor BASE_SIG extra) M1_SYMBOLIC <> 0) as Hm1.
  { apply lor_contains_left. exact base_contains_m1. }
  rewrite Heq in Hm1. simpl in Hm1. contradiction.
Qed.

(* ===================================================================== *)
(*  §9 Signature algebra properties                                      *)
(* ===================================================================== *)

(* Union is commutative *)
Theorem sig_union_comm : forall a b,
  sig_union a b = sig_union b a.
Proof.
  intros. unfold sig_union. apply Nat.lor_comm.
Qed.

(* Union is associative *)
Theorem sig_union_assoc : forall a b c,
  sig_union (sig_union a b) c = sig_union a (sig_union b c).
Proof.
  intros. unfold sig_union. symmetry. apply Nat.lor_assoc.
Qed.

(* Union is idempotent *)
Theorem sig_union_idempotent : forall a,
  sig_union a a = a.
Proof.
  intro. unfold sig_union. apply Nat.lor_diag.
Qed.

(* Set is monotonic: sig_set only adds bits *)
Theorem sig_set_monotonic : forall sig bit,
  Nat.land sig bit <> 0 ->
  Nat.land (sig_set sig bit) bit <> 0.
Proof.
  intros sig bit H.
  unfold sig_set.
  apply lor_contains_left. exact H.
Qed.

(* ===================================================================== *)
(*  §10 Predicate evaluation properties                                  *)
(* ===================================================================== *)

(* SPTrue is always satisfied *)
Lemma eval_true : forall sig, eval_pred SPTrue sig = true.
Proof. reflexivity. Qed.

(* SPFalse is never satisfied *)
Lemma eval_false : forall sig, eval_pred SPFalse sig = false.
Proof. reflexivity. Qed.

(* HasBit matches sig_contains *)
Lemma eval_has_bit : forall sig bit,
  eval_pred (HasBit bit) sig = sig_contains sig bit.
Proof. reflexivity. Qed.

(* Conjunction distributes over evaluation *)
Lemma eval_and : forall p q sig,
  eval_pred (SPAnd p q) sig = andb (eval_pred p sig) (eval_pred q sig).
Proof. reflexivity. Qed.

(* Disjunction distributes over evaluation *)
Lemma eval_or : forall p q sig,
  eval_pred (SPOr p q) sig = orb (eval_pred p sig) (eval_pred q sig).
Proof. reflexivity. Qed.

(* Negation distributes over evaluation *)
Lemma eval_not : forall p sig,
  eval_pred (SPNot p) sig = negb (eval_pred p sig).
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  §11 Witness generation correctness                                   *)
(* ===================================================================== *)

(* For HasBit(i), the witness is any signature with bit i set.
   The simplest witness is the bit itself. *)

Definition witness_for_has_bit (bit : nat) : PredicateSignature := bit.

Theorem witness_satisfies_has_bit : forall bit,
  bit <> 0 ->
  eval_pred (HasBit bit) (witness_for_has_bit bit) = true.
Proof.
  intros bit Hbit.
  unfold witness_for_has_bit.
  simpl. unfold sig_contains.
  apply Bool.negb_true_iff.
  apply Nat.eqb_neq.
  rewrite Nat.land_diag. exact Hbit.
Qed.

(* ===================================================================== *)
(*  §12 Module bit distinctness                                          *)
(* ===================================================================== *)

(* All module bits are powers of 2 with distinct exponents *)
Lemma module_bits_are_powers_of_2 :
  M1_SYMBOLIC = 2^0 /\ M2_BUCHI = 2^1 /\ M3_AWA = 2^2 /\
  M4_VPA = 2^3 /\ M5_PARITY_TREE = 2^4 /\ M6_REGISTER = 2^5 /\
  M7_PROBABILISTIC = 2^6 /\ M8_MULTI_TAPE = 2^7 /\ M9_MULTISET = 2^8 /\
  M10_MSO = 2^9 /\ M11_TWO_WAY = 2^10.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* Complete pairwise distinctness: all C(11,2)=55 pairs are distinct *)
Lemma all_module_bits_distinct :
  (* M1 vs all others *)
  M1_SYMBOLIC <> M2_BUCHI /\
  M1_SYMBOLIC <> M3_AWA /\
  M1_SYMBOLIC <> M4_VPA /\
  M1_SYMBOLIC <> M5_PARITY_TREE /\
  M1_SYMBOLIC <> M6_REGISTER /\
  M1_SYMBOLIC <> M7_PROBABILISTIC /\
  M1_SYMBOLIC <> M8_MULTI_TAPE /\
  M1_SYMBOLIC <> M9_MULTISET /\
  M1_SYMBOLIC <> M10_MSO /\
  M1_SYMBOLIC <> M11_TWO_WAY /\
  (* M2 vs remaining *)
  M2_BUCHI <> M3_AWA /\
  M2_BUCHI <> M4_VPA /\
  M2_BUCHI <> M5_PARITY_TREE /\
  M2_BUCHI <> M6_REGISTER /\
  M2_BUCHI <> M7_PROBABILISTIC /\
  M2_BUCHI <> M8_MULTI_TAPE /\
  M2_BUCHI <> M9_MULTISET /\
  M2_BUCHI <> M10_MSO /\
  M2_BUCHI <> M11_TWO_WAY /\
  (* M3 vs remaining *)
  M3_AWA <> M4_VPA /\
  M3_AWA <> M5_PARITY_TREE /\
  M3_AWA <> M6_REGISTER /\
  M3_AWA <> M7_PROBABILISTIC /\
  M3_AWA <> M8_MULTI_TAPE /\
  M3_AWA <> M9_MULTISET /\
  M3_AWA <> M10_MSO /\
  M3_AWA <> M11_TWO_WAY /\
  (* M4 vs remaining *)
  M4_VPA <> M5_PARITY_TREE /\
  M4_VPA <> M6_REGISTER /\
  M4_VPA <> M7_PROBABILISTIC /\
  M4_VPA <> M8_MULTI_TAPE /\
  M4_VPA <> M9_MULTISET /\
  M4_VPA <> M10_MSO /\
  M4_VPA <> M11_TWO_WAY /\
  (* M5 vs remaining *)
  M5_PARITY_TREE <> M6_REGISTER /\
  M5_PARITY_TREE <> M7_PROBABILISTIC /\
  M5_PARITY_TREE <> M8_MULTI_TAPE /\
  M5_PARITY_TREE <> M9_MULTISET /\
  M5_PARITY_TREE <> M10_MSO /\
  M5_PARITY_TREE <> M11_TWO_WAY /\
  (* M6 vs remaining *)
  M6_REGISTER <> M7_PROBABILISTIC /\
  M6_REGISTER <> M8_MULTI_TAPE /\
  M6_REGISTER <> M9_MULTISET /\
  M6_REGISTER <> M10_MSO /\
  M6_REGISTER <> M11_TWO_WAY /\
  (* M7 vs remaining *)
  M7_PROBABILISTIC <> M8_MULTI_TAPE /\
  M7_PROBABILISTIC <> M9_MULTISET /\
  M7_PROBABILISTIC <> M10_MSO /\
  M7_PROBABILISTIC <> M11_TWO_WAY /\
  (* M8 vs remaining *)
  M8_MULTI_TAPE <> M9_MULTISET /\
  M8_MULTI_TAPE <> M10_MSO /\
  M8_MULTI_TAPE <> M11_TWO_WAY /\
  (* M9 vs remaining *)
  M9_MULTISET <> M10_MSO /\
  M9_MULTISET <> M11_TWO_WAY /\
  (* M10 vs M11 *)
  M10_MSO <> M11_TWO_WAY.
Proof.
  unfold M1_SYMBOLIC, M2_BUCHI, M3_AWA, M4_VPA, M5_PARITY_TREE,
         M6_REGISTER, M7_PROBABILISTIC, M8_MULTI_TAPE, M9_MULTISET,
         M10_MSO, M11_TWO_WAY.
  repeat split; lia.
Qed.

(* Each module bit is nonzero (a power of 2) *)
Lemma all_module_bits_nonzero :
  M1_SYMBOLIC <> 0 /\ M2_BUCHI <> 0 /\ M3_AWA <> 0 /\
  M4_VPA <> 0 /\ M5_PARITY_TREE <> 0 /\ M6_REGISTER <> 0 /\
  M7_PROBABILISTIC <> 0 /\ M8_MULTI_TAPE <> 0 /\ M9_MULTISET <> 0 /\
  M10_MSO <> 0 /\ M11_TWO_WAY <> 0.
Proof.
  unfold M1_SYMBOLIC, M2_BUCHI, M3_AWA, M4_VPA, M5_PARITY_TREE,
         M6_REGISTER, M7_PROBABILISTIC, M8_MULTI_TAPE, M9_MULTISET,
         M10_MSO, M11_TWO_WAY.
  repeat split; lia.
Qed.
