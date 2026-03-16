(*
 * AL05_ChainCollapse: Chain collapsing preserves longest-match semantics
 * for DFA-based lexing.
 *
 * Chain collapse (A-L05) detects linear state sequences in the DFA
 * (e.g., w -> wh -> whi -> whil -> while) and replaces them with a
 * single multi-byte comparison.  This file proves:
 *   1. The collapsed DFA accepts the same language as the original
 *   2. The longest-match property is preserved under chain collapse,
 *      given that no intermediate chain state is accepting
 *
 * Key preconditions from the Rust implementation:
 *   - No intermediate chain state may be an accepting state
 *     (codegen.rs:1183-1186, 1224-1226)
 *   - Chain characters correspond to singleton equivalence classes
 *     (codegen.rs:1168-1171)
 *   - Minimum chain length >= 3 is a performance heuristic, not a
 *     correctness requirement (codegen.rs:1141)
 *
 * Strategy: Rather than defining a recursive collapsed_run function
 * (which requires well-founded recursion due to the multi-byte jump),
 * we prove correctness via decomposition: chain collapse replaces a
 * sequence of single-character transitions with one multi-byte
 * comparison that consumes the same characters and reaches the same
 * state.  For longest-match, we additionally prove that no match
 * position exists at intermediate chain states (under the
 * no-intermediate-accept precondition).
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition                | Rust Code                                | Location
 *   -------------------------------|------------------------------------------|-----------------------------------------
 *   DFA (Record)                   | Dfa struct                               | prattail/src/automata/codegen.rs
 *   MultiByteChain                 | MultiByteChain struct                    | prattail/src/automata/codegen.rs:1141
 *   detect_multi_byte_chains       | detect_multi_byte_chains()               | prattail/src/automata/codegen.rs:1198
 *   chain_no_intermediate_accept   | accept state check in chain detection    | prattail/src/automata/codegen.rs:1224
 *   write_chain_tables             | write_chain_tables()                     | prattail/src/automata/codegen.rs:1890
 *   Optimization::MultiByteChain   | cost_benefit::Optimization::MultiByteChain | prattail/src/cost_benefit.rs:110
 *   OptimizationGates::multi_byte_chain | multi_byte_chain gate field         | prattail/src/cost_benefit.rs:1328
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Setoid.

Import ListNotations.

(* ===================================================================== *)
(*  DFA Model                                                              *)
(*                                                                         *)
(*  A DFA is defined by states, transitions, a start state, and accept    *)
(*  states.  Characters are modeled as nat.                                *)
(* ===================================================================== *)

Definition State := nat.
Definition Char := nat.

Record DFA := mkDFA {
  dfa_start : State;
  dfa_trans : State -> Char -> option State;
  dfa_accept : State -> bool
}.

(* Run a DFA on a string, returning the final state (if reachable) *)
Fixpoint dfa_run (d : DFA) (s : State) (input : list Char) : option State :=
  match input with
  | [] => Some s
  | c :: rest =>
    match dfa_trans d s c with
    | Some s' => dfa_run d s' rest
    | None => None
    end
  end.

(* A DFA accepts a string *)
Definition dfa_accepts (d : DFA) (input : list Char) : Prop :=
  exists s, dfa_run d (dfa_start d) input = Some s /\ dfa_accept d s = true.

(* ===================================================================== *)
(*  Chain States                                                           *)
(*                                                                         *)
(*  A chain is a linear sequence of states s0 -c0-> s1 -c1-> ... -cn-> sn *)
(*  where each intermediate state si (0 < i < n) has exactly one          *)
(*  incoming and one outgoing transition.                                   *)
(* ===================================================================== *)

(* A chain: starting state, the character sequence, ending state *)
Record Chain := mkChain {
  chain_start : State;
  chain_chars : list Char;
  chain_end : State
}.

(* ===================================================================== *)
(*  Chain Preconditions                                                    *)
(*                                                                         *)
(*  The Rust implementation enforces these preconditions during chain      *)
(*  detection (detect_multi_byte_chains in codegen.rs:1198):               *)
(*    1. No intermediate chain state is an accepting state                 *)
(*       (codegen.rs:1224-1226) — skipping accept states would violate    *)
(*       longest-match lexer semantics                                     *)
(*    2. Chain characters correspond to singleton equivalence classes      *)
(*       (codegen.rs:1168-1171) — the multi-byte comparison checks        *)
(*       concrete byte values, so each chain position must map to          *)
(*       exactly one byte                                                  *)
(*    3. Minimum chain length >= 3 is a performance heuristic, not a      *)
(*       correctness requirement (codegen.rs:1141)                         *)
(* ===================================================================== *)

(* A chain is valid in a DFA: running the DFA on chain_chars from
   chain_start yields chain_end *)
Definition chain_valid (d : DFA) (ch : Chain) : Prop :=
  dfa_run d (chain_start ch) (chain_chars ch) = Some (chain_end ch).

(* No intermediate state in the chain is an accepting state.
   This precondition is enforced by the Rust implementation:
   "Accept states cannot be intermediate chain states" (codegen.rs:1224).
   Without this, chain collapse would skip accept states and violate
   longest-match semantics. *)
Definition chain_no_intermediate_accept (d : DFA) (ch : Chain) : Prop :=
  forall k, 0 < k -> k < length (chain_chars ch) ->
  forall s, dfa_run d (chain_start ch) (firstn k (chain_chars ch)) = Some s ->
  dfa_accept d s = false.

(* ===================================================================== *)
(*  Multi-Byte Comparison Primitives                                       *)
(*                                                                         *)
(*  The runtime uses starts_with for prefix detection and drop to advance *)
(*  past the matched prefix.  We prove these correct.                     *)
(* ===================================================================== *)

(* Check if a list starts with a given prefix *)
Fixpoint starts_with (prefix input : list Char) : bool :=
  match prefix, input with
  | [], _ => true
  | _, [] => false
  | p :: ps, i :: is_ => Nat.eqb p i && starts_with ps is_
  end.

(* Drop n elements from a list *)
Fixpoint drop (n : nat) (l : list Char) : list Char :=
  match n, l with
  | 0, _ => l
  | _, [] => []
  | Datatypes.S k, _ :: rest => drop k rest
  end.

(* ===================================================================== *)
(*  Helper Lemmas                                                          *)
(* ===================================================================== *)

Lemma starts_with_correct : forall prefix input,
  starts_with prefix input = true ->
  exists suffix, input = prefix ++ suffix.
Proof.
  induction prefix as [| p ps IH].
  - intros input _. exists input. reflexivity.
  - intros input H. destruct input as [| i rest].
    + simpl in H. discriminate.
    + simpl in H. apply Bool.andb_true_iff in H as [Hpeq Hrest].
      apply Nat.eqb_eq in Hpeq. subst.
      apply IH in Hrest. destruct Hrest as [suffix Heq]. subst.
      exists suffix. reflexivity.
Qed.

(* starts_with correctly identifies a prefix *)
Lemma starts_with_self : forall (l suffix : list Char),
  starts_with l (l ++ suffix) = true.
Proof.
  induction l as [| x xs IH].
  - intros suffix. simpl. reflexivity.
  - intros suffix. simpl. rewrite Nat.eqb_refl. simpl. apply IH.
Qed.

Lemma drop_app : forall (l1 l2 : list Char),
  drop (length l1) (l1 ++ l2) = l2.
Proof.
  induction l1 as [| x xs IH].
  - intro l2. simpl. reflexivity.
  - intro l2. simpl. apply IH.
Qed.

Lemma dfa_run_app : forall d s l1 l2 s',
  dfa_run d s l1 = Some s' ->
  dfa_run d s (l1 ++ l2) = dfa_run d s' l2.
Proof.
  intros d s l1. revert s.
  induction l1 as [| c rest IH].
  - intros s l2 s' H. simpl in H. injection H as Hs. subst. simpl. reflexivity.
  - intros s l2 s' H. simpl in *.
    destruct (dfa_trans d s c) as [s'' |]; try discriminate.
    apply IH. exact H.
Qed.

(* firstn of an appended list when k <= length of first list *)
Lemma firstn_app_l : forall k (l1 l2 : list Char),
  k <= length l1 -> firstn k (l1 ++ l2) = firstn k l1.
Proof.
  induction k as [| k' IH].
  - intros l1 l2 _. simpl. reflexivity.
  - intros l1 l2 Hle.
    destruct l1 as [| x xs].
    + simpl in Hle. lia.
    + simpl. f_equal. apply IH. simpl in Hle. lia.
Qed.

(* A match at position pos from state s: running pos characters
   from s reaches an accepting state *)
Definition has_match_at_from (d : DFA) (s : State) (input : list Char) (pos : nat) : Prop :=
  exists s', dfa_run d s (firstn pos input) = Some s' /\
            dfa_accept d s' = true.

(* Acceptance of a complete input from a given state *)
Definition dfa_accepts_from (d : DFA) (s : State) (input : list Char) : Prop :=
  exists s', dfa_run d s input = Some s' /\ dfa_accept d s' = true.

(* Longest match from a given state *)
Definition longest_match_from (d : DFA) (s : State) (input : list Char) (pos : nat) : Prop :=
  has_match_at_from d s input pos /\
  forall pos', pos' > pos -> ~ has_match_at_from d s input pos'.

(* ===================================================================== *)
(*  Theorem 1: Chain Decomposition                                         *)
(*                                                                         *)
(*  The core correctness property of chain collapse: if the DFA is at     *)
(*  chain_start and the input begins with chain_chars, processing the     *)
(*  entire input through the chain is equivalent to jumping directly to   *)
(*  chain_end and processing the remaining suffix.                         *)
(*                                                                         *)
(*  This is exactly what the runtime does: detect the prefix via          *)
(*  starts_with, consume it via drop, and continue from chain_end.        *)
(* ===================================================================== *)

Theorem chain_dfa_run_decompose : forall d ch suffix,
  chain_valid d ch ->
  dfa_run d (chain_start ch) (chain_chars ch ++ suffix) =
  dfa_run d (chain_end ch) suffix.
Proof.
  intros d ch suffix Hvalid.
  apply dfa_run_app. exact Hvalid.
Qed.

(* As a corollary, the chain string itself reaches chain_end *)
Corollary chain_collapse_on_chain_string : forall d ch,
  chain_valid d ch ->
  dfa_run d (chain_start ch) (chain_chars ch) =
  Some (chain_end ch).
Proof.
  intros d ch Hvalid. exact Hvalid.
Qed.

(* Chain decomposition preserves the final state *)
Corollary chain_collapse_preserves_final_state : forall d ch suffix s_final,
  chain_valid d ch ->
  dfa_run d (chain_start ch) (chain_chars ch ++ suffix) = Some s_final ->
  dfa_run d (chain_end ch) suffix = Some s_final.
Proof.
  intros d ch suffix s_final Hvalid Hrun.
  rewrite chain_dfa_run_decompose in Hrun; assumption.
Qed.

(* ===================================================================== *)
(*  Theorem 2: Multi-Byte Comparison Correctness                           *)
(*                                                                         *)
(*  The runtime identifies chain prefixes via starts_with and advances    *)
(*  past them via drop.  We prove these correctly decompose the input.    *)
(* ===================================================================== *)

Theorem multi_byte_identifies_chain : forall ch input suffix,
  input = chain_chars ch ++ suffix ->
  length (chain_chars ch) > 0 ->
  starts_with (chain_chars ch) input = true /\
  drop (length (chain_chars ch)) input = suffix.
Proof.
  intros ch input suffix Heq Hlen.
  subst input. split.
  - apply starts_with_self.
  - apply drop_app.
Qed.

(* ===================================================================== *)
(*  Theorem 3: Collapsed Execution Equivalence                             *)
(*                                                                         *)
(*  Combining decomposition and multi-byte comparison: at chain_start,    *)
(*  if the input starts with chain_chars, the runtime's collapsed         *)
(*  execution (detect prefix, drop, jump to chain_end) produces the same  *)
(*  result as step-by-step DFA execution.                                  *)
(* ===================================================================== *)

Theorem chain_collapse_correct : forall d ch suffix,
  chain_valid d ch ->
  length (chain_chars ch) > 0 ->
  (* The runtime detects the prefix and advances *)
  starts_with (chain_chars ch) (chain_chars ch ++ suffix) = true ->
  drop (length (chain_chars ch)) (chain_chars ch ++ suffix) = suffix ->
  (* Collapsed execution (jump to chain_end, process suffix) equals
     sequential execution (process chain_chars then suffix) *)
  dfa_run d (chain_end ch) suffix =
  dfa_run d (chain_start ch) (chain_chars ch ++ suffix).
Proof.
  intros d ch suffix Hvalid Hlen _ _.
  symmetry. apply dfa_run_app. exact Hvalid.
Qed.

(* Acceptance is preserved under chain collapse *)
Theorem chain_collapse_preserves_acceptance : forall d ch suffix,
  chain_valid d ch ->
  (* If the sequential DFA accepts (chain_chars ++ suffix from chain_start) *)
  (exists s_final,
    dfa_run d (chain_start ch) (chain_chars ch ++ suffix) = Some s_final /\
    dfa_accept d s_final = true) ->
  (* Then the collapsed DFA also accepts (suffix from chain_end) *)
  exists s_final,
    dfa_run d (chain_end ch) suffix = Some s_final /\
    dfa_accept d s_final = true.
Proof.
  intros d ch suffix Hvalid [s_final [Hrun Hacc]].
  rewrite chain_dfa_run_decompose in Hrun; [| exact Hvalid].
  exists s_final. split; assumption.
Qed.

(* ===================================================================== *)
(*  Theorem 4: Longest-Match Preservation                                  *)
(*                                                                         *)
(*  The key correctness property requiring the no-intermediate-accept     *)
(*  precondition: when no intermediate chain state is accepting, no       *)
(*  match exists at intermediate chain positions.  This means the         *)
(*  collapsed execution (which jumps from chain_start to chain_end)       *)
(*  cannot miss any match that the sequential execution would have found. *)
(*                                                                         *)
(*  Precondition: chain_no_intermediate_accept (codegen.rs:1224-1226).    *)
(* ===================================================================== *)

(* Matches at intermediate positions within the chain cannot exist when
   no intermediate state is accepting *)
Theorem no_match_in_chain_interior : forall d ch suffix,
  chain_valid d ch ->
  chain_no_intermediate_accept d ch ->
  forall k, 0 < k -> k < length (chain_chars ch) ->
  ~ has_match_at_from d (chain_start ch) (chain_chars ch ++ suffix) k.
Proof.
  intros d ch suffix Hvalid Hno_accept k Hpos Hlt.
  intro Hmatch.
  destruct Hmatch as [s' [Hrun Hacc]].
  assert (Hfn : firstn k (chain_chars ch ++ suffix) = firstn k (chain_chars ch)).
  { apply firstn_app_l. lia. }
  rewrite Hfn in Hrun.
  assert (Hfalse : dfa_accept d s' = false).
  { apply (Hno_accept k Hpos Hlt s' Hrun). }
  rewrite Hfalse in Hacc. discriminate.
Qed.

(* The longest match from chain_start must be at position 0 (chain_start
   is accepting) or at position >= chain length (past the chain).
   It cannot be at an interior chain position. *)
Theorem longest_match_not_in_interior : forall d ch suffix pos,
  chain_valid d ch ->
  chain_no_intermediate_accept d ch ->
  longest_match_from d (chain_start ch) (chain_chars ch ++ suffix) pos ->
  pos = 0 \/ pos >= length (chain_chars ch).
Proof.
  intros d ch suffix pos Hvalid Hno_accept [Hmatch _].
  assert (Hdec : pos = 0 \/ (0 < pos /\ pos < length (chain_chars ch))
                  \/ pos >= length (chain_chars ch)) by lia.
  destruct Hdec as [Hz | [[Hpos Hlt] | Hge]].
  - left. exact Hz.
  - exfalso.
    exact (no_match_in_chain_interior d ch suffix Hvalid Hno_accept pos Hpos Hlt Hmatch).
  - right. exact Hge.
Qed.

(* ===================================================================== *)
(*  Corollary: Acceptance Equivalence (Biconditional)                      *)
(*                                                                         *)
(*  The collapsed DFA (which jumps from chain_start to chain_end on a     *)
(*  multi-byte match) accepts exactly the same strings as the original    *)
(*  DFA for inputs beginning with chain_chars.  This biconditional       *)
(*  follows from the chain decomposition theorem.                          *)
(* ===================================================================== *)

Theorem chain_collapse_acceptance_equiv : forall d ch suffix,
  chain_valid d ch ->
  (dfa_accepts_from d (chain_start ch) (chain_chars ch ++ suffix) <->
   dfa_accepts_from d (chain_end ch) suffix).
Proof.
  intros d ch suffix Hvalid. split.
  - (* forward: sequential accepts -> collapsed accepts *)
    intros [s_final [Hrun Hacc]].
    rewrite chain_dfa_run_decompose in Hrun; [| exact Hvalid].
    exists s_final. split; assumption.
  - (* backward: collapsed accepts -> sequential accepts *)
    intros [s_final [Hrun Hacc]].
    exists s_final. split; [| exact Hacc].
    rewrite chain_dfa_run_decompose; [exact Hrun | exact Hvalid].
Qed.

(* The contrapositive: rejection is also preserved *)
Corollary chain_collapse_rejection_equiv : forall d ch suffix,
  chain_valid d ch ->
  (~ dfa_accepts_from d (chain_start ch) (chain_chars ch ++ suffix) <->
   ~ dfa_accepts_from d (chain_end ch) suffix).
Proof.
  intros d ch suffix Hvalid.
  pose proof (chain_collapse_acceptance_equiv d ch suffix Hvalid) as [Hfwd Hrev].
  split; intros Hrej Hacc; apply Hrej; auto.
Qed.

(* ===================================================================== *)
(*  Abstraction Gaps                                                       *)
(*                                                                         *)
(*  1. Equivalence class partitioning: The Rust uses AlphabetPartition    *)
(*     to group bytes into equivalence classes.  Chain collapse only       *)
(*     operates on singleton classes (one byte per class).  The Rocq       *)
(*     model uses Char = nat directly, abstracting away the partitioning. *)
(*  2. Singleton class check: The Rust verifies each chain position is a  *)
(*     singleton class (codegen.rs:1168-1171).  This is abstracted as     *)
(*     the chain_chars being concrete byte values.                         *)
(*  3. DFA representation: The Rust Dfa uses state arrays with packed     *)
(*     transition tables.  The Rocq model uses functional transitions.    *)
(*  4. Multi-byte comparison: The Rust generates byte-string comparisons  *)
(*     with starts_with.  The Rocq model uses list prefix matching.       *)
(*  5. Trust boundary: The DFA construction (from grammar to NFA to DFA)  *)
(*     is outside the scope of this proof.  We take the DFA as given.     *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  Summary of Results                                                     *)
(*                                                                         *)
(*  T1: chain_dfa_run_decompose                                            *)
(*      Running through chain_chars then suffix from chain_start equals   *)
(*      running suffix from chain_end.  (Core decomposition lemma.)       *)
(*                                                                         *)
(*  T1a: chain_collapse_on_chain_string                                    *)
(*       Running the DFA on chain_chars alone reaches chain_end.          *)
(*                                                                         *)
(*  T1b: chain_collapse_preserves_final_state                              *)
(*       Decomposition preserves the final state.                          *)
(*                                                                         *)
(*  T2: multi_byte_identifies_chain                                        *)
(*      starts_with correctly detects chain prefixes; drop correctly      *)
(*      advances past them.                                                *)
(*                                                                         *)
(*  T3: chain_collapse_correct                                             *)
(*      Collapsed execution (detect + drop + jump) = sequential DFA run. *)
(*                                                                         *)
(*  T4: chain_collapse_preserves_acceptance                                *)
(*      If the sequential DFA accepts, the collapsed DFA also accepts.   *)
(*                                                                         *)
(*  T5: no_match_in_chain_interior                                         *)
(*      No match exists at intermediate chain positions when               *)
(*      chain_no_intermediate_accept holds.                                *)
(*                                                                         *)
(*  T6: longest_match_not_in_interior                                      *)
(*      The longest match position is either 0 or past the chain.         *)
(*                                                                         *)
(*  T7: chain_collapse_acceptance_equiv                                    *)
(*      Biconditional: original accepts from chain_start iff collapsed   *)
(*      accepts from chain_end.                                            *)
(*                                                                         *)
(*  C1: chain_collapse_rejection_equiv                                     *)
(*      Biconditional: original rejects iff collapsed rejects.           *)
(*                                                                         *)
(*  All proofs are COMPLETE -- zero Admitted.                               *)
(* ===================================================================== *)
