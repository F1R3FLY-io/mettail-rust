(*
 * AL04_MphPostLex: MPH post-lex equivalence to DFA keyword recognition.
 *
 * The MPH (Minimal Perfect Hashing) optimization (A-L04) extracts keywords
 * from the DFA into an MPH table using CHD (Compress, Hash, Displace).
 * After the DFA emits an Ident token, the MPH table is probed to
 * reclassify keywords.  This file proves:
 *   1. mph_probe(text) = Some(id) <-> dfa_classify(text) = Keyword(id)
 *   2. MPH slot assignment has no collisions on the keyword set
 *
 * The Rust implementation uses CHD with double-hashing:
 *   slot = (h1 + displacement[bucket(h1)] * h2) % table_size
 * The raw hash function (FNV-1a) is NOT injective — collision-freedom
 * is achieved via displacement values computed at compile time.  The
 * Rocq model abstracts the full CHD computation as `mph_slot`, with
 * the hypothesis `mph_slot_unique` capturing that the SLOT assignment
 * (not the raw hash) is collision-free on the keyword set.
 * Correctness additionally relies on key verification: the probe
 * checks `MPH_KEYS[slot] == text` (mph.rs:436).
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition              | Rust Code                                | Location
 *   -----------------------------|------------------------------------------|-----------------------------------------
 *   mph_probe                    | mph_probe() generated function           | prattail/src/automata/mph.rs:429
 *   dfa_classify                 | DFA lexer classify                       | prattail/src/lexer.rs
 *   keyword_set                  | keyword extraction from grammar          | prattail/src/automata/mph.rs
 *   mph_slot                     | CHD slot computation (h1+d*h2)%size      | prattail/src/automata/mph.rs:429
 *   Optimization::KeywordMph     | cost_benefit::Optimization::KeywordMph   | prattail/src/cost_benefit.rs:108
 *   OptimizationGates::keyword_mph | keyword_mph gate field                 | prattail/src/cost_benefit.rs:1327
 *   emit_mph_table               | codegen emit function                    | prattail/src/automata/codegen.rs:2126
 *
 * Rocq 9.1 compatible.
 *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Hammer Require Import Tactics.
From Stdlib Require Import Setoid.

Import ListNotations.

(* ===================================================================== *)
(*  String and Keyword Model                                               *)
(*                                                                         *)
(*  We model strings as lists of nat (byte values) and keywords as a      *)
(*  finite set of (string, token_id) pairs.                                *)
(* ===================================================================== *)

Definition Str := list nat.
Definition TokenId := nat.

(* Keyword entry: (keyword_string, token_id) *)
Record KeywordEntry := mkKw {
  kw_str : Str;
  kw_id : TokenId
}.

Definition KeywordSet := list KeywordEntry.

(* A keyword set has no duplicate strings *)
Definition no_dup_strings (K : KeywordSet) : Prop :=
  forall i j ki kj,
    nth_error K i = Some ki ->
    nth_error K j = Some kj ->
    kw_str ki = kw_str kj ->
    i = j.

(* ===================================================================== *)
(*  DFA Classifier                                                         *)
(*                                                                         *)
(*  The DFA classifier maps a string to either a keyword token or an      *)
(*  identifier token.  We model it as a function.                          *)
(* ===================================================================== *)

Inductive ClassifyResult :=
  | Keyword : TokenId -> ClassifyResult
  | Ident : ClassifyResult
  | NoMatch : ClassifyResult.

(* The DFA classifier and keyword set are parameterized within a section
   to avoid global axioms.  See Section MphProof below. *)

Section MphProof.

  Variable keyword_set : KeywordSet.
  Hypothesis kw_no_dups : no_dup_strings keyword_set.

  (* DFA classifier for this keyword set *)
  Variable dfa_classify : Str -> ClassifyResult.

  (* DFA correctly classifies keywords *)
  Hypothesis dfa_classifies_keywords : forall kw,
    In kw keyword_set ->
    dfa_classify (kw_str kw) = Keyword (kw_id kw).

  (* DFA classifies non-keywords as Ident (if they match identifier pattern) *)
  Hypothesis dfa_classifies_non_keywords : forall s,
    (forall kw, In kw keyword_set -> kw_str kw <> s) ->
    dfa_classify s <> NoMatch ->
    dfa_classify s = Ident.

  (* ===================================================================== *)
  (*  MPH Slot Computation Model                                             *)
  (*                                                                         *)
  (*  The CHD algorithm computes a slot for each keyword:                   *)
  (*    slot(key) = (h1(key) + d[bucket(h1(key))] * h2(key)) % table_size  *)
  (*  where d[] is the displacement table, computed at compile time to       *)
  (*  ensure collision-free slot assignment.  We abstract the full CHD      *)
  (*  computation as a single function `mph_slot`.                           *)
  (*                                                                         *)
  (*  The table stores (keyword_string, token_id) at each slot for          *)
  (*  verification.  The probe checks `MPH_KEYS[slot] == text` to detect   *)
  (*  non-keyword inputs that happen to hash to occupied slots.             *)
  (* ===================================================================== *)

  (* CHD slot computation: abstracts h1 + d[bucket(h1)] * h2 % table_size *)
  Variable mph_slot : Str -> nat.

  (* Slot assignment is collision-free on the keyword set.
     This is weaker than hash injectivity: the raw hash (FNV-1a) may
     collide, but the displacement table ensures distinct slots.
     CHD construction correctness is verified empirically at compile time. *)
  Hypothesis mph_slot_unique : forall ki kj,
    In ki keyword_set ->
    In kj keyword_set ->
    mph_slot (kw_str ki) = mph_slot (kw_str kj) ->
    kw_str ki = kw_str kj.

  (* MPH maps keywords to valid indices *)
  Hypothesis mph_in_range : forall kw,
    In kw keyword_set ->
    mph_slot (kw_str kw) < length keyword_set.

  (* MPH table: array indexed by hash, storing (keyword_string, token_id) *)
  Variable mph_table : nat -> option KeywordEntry.

  (* Table is populated correctly *)
  Hypothesis mph_table_populated : forall kw,
    In kw keyword_set ->
    mph_table (mph_slot (kw_str kw)) = Some kw.

  (* ===================================================================== *)
  (*  MPH Probe Function                                                    *)
  (*                                                                         *)
  (*  Mirrors mph_probe() in prattail/src/automata/mph.rs:429.             *)
  (*  1. Compute hash h = mph_slot(text)                                   *)
  (*  2. Look up mph_table[h]                                               *)
  (*  3. If entry exists and entry.string = text, return Some(entry.id)    *)
  (*  4. Otherwise return None                                              *)
  (* ===================================================================== *)

  (* String equality decision *)
  Variable str_eq_dec : forall s1 s2 : Str, {s1 = s2} + {s1 <> s2}.

  Definition mph_probe (text : Str) : option TokenId :=
    match mph_table (mph_slot text) with
    | Some entry =>
        if str_eq_dec (kw_str entry) text
        then Some (kw_id entry)
        else None
    | None => None
    end.

  (* ===================================================================== *)
  (*  Theorem 1: MPH probe agrees with DFA classification                   *)
  (*                                                                         *)
  (*  mph_probe(text) = Some(id) <-> dfa_classify(text) = Keyword(id)      *)
  (* ===================================================================== *)

  (* Additional hypothesis: table only contains keyword set entries *)
  Hypothesis mph_table_only_keywords : forall h entry,
    mph_table h = Some entry -> In entry keyword_set.

  (* Forward: if MPH probe succeeds, DFA classifies as keyword *)
  Theorem mph_probe_to_dfa : forall text id,
    mph_probe text = Some id ->
    dfa_classify text = Keyword id.
  Proof.
    intros text id Hprobe.
    unfold mph_probe in Hprobe.
    destruct (mph_table (mph_slot text)) as [entry |] eqn:Htbl; try discriminate.
    destruct (str_eq_dec (kw_str entry) text) as [Heq | Hneq]; try discriminate.
    injection Hprobe as Hid. subst id. subst text.
    assert (Hin : In entry keyword_set) by (apply mph_table_only_keywords with (h := mph_slot (kw_str entry)); exact Htbl).
    apply dfa_classifies_keywords. exact Hin.
  Qed.

  (* Reverse: if DFA classifies as keyword, MPH probe succeeds *)
  Theorem dfa_to_mph_probe : forall text id,
    dfa_classify text = Keyword id ->
    (exists kw, In kw keyword_set /\ kw_str kw = text /\ kw_id kw = id) ->
    mph_probe text = Some id.
  Proof.
    intros text id Hdfa [kw [Hin [Hstr Hid]]].
    subst text. subst id.
    unfold mph_probe.
    rewrite (mph_table_populated kw Hin).
    destruct (str_eq_dec (kw_str kw) (kw_str kw)) as [_ | Hneq].
    - reflexivity.
    - exfalso. apply Hneq. reflexivity.
  Qed.

  (* ===================================================================== *)
  (*  Theorem 2: MPH slot assignment is collision-free                       *)
  (*                                                                         *)
  (*  For any two distinct keywords, their MPH slots are distinct.         *)
  (* ===================================================================== *)

  Theorem mph_no_collisions : forall ki kj,
    In ki keyword_set ->
    In kj keyword_set ->
    kw_str ki <> kw_str kj ->
    mph_slot (kw_str ki) <> mph_slot (kw_str kj).
  Proof.
    intros ki kj Hki Hkj Hneq Hhash_eq.
    apply Hneq.
    apply mph_slot_unique; assumption.
  Qed.

  (* ===================================================================== *)
  (*  Corollary: MPH probe returns None for non-keywords                    *)
  (* ===================================================================== *)

  Corollary mph_probe_non_keyword : forall text,
    (forall kw, In kw keyword_set -> kw_str kw <> text) ->
    mph_probe text = None.
  Proof.
    intros text Hnot_kw.
    unfold mph_probe.
    destruct (mph_table (mph_slot text)) as [entry |] eqn:Htbl.
    - destruct (str_eq_dec (kw_str entry) text) as [Heq | Hneq].
      + (* entry.str = text, but text is not a keyword, contradiction *)
        exfalso.
        assert (Hin : In entry keyword_set) by (apply mph_table_only_keywords with (h := mph_slot text); exact Htbl).
        apply (Hnot_kw entry Hin). exact Heq.
      + reflexivity.
    - reflexivity.
  Qed.

  (* ===================================================================== *)
  (*  Corollary: MPH + DFA pipeline correctness                             *)
  (*                                                                         *)
  (*  The pipeline: DFA emits Ident, then MPH reclassifies.               *)
  (*  For keywords: DFA -> Ident, MPH -> Keyword(id)                       *)
  (*  For non-keywords: DFA -> Ident, MPH -> None (keep Ident)             *)
  (* ===================================================================== *)

  (* Post-lex classification: if DFA says Ident, probe MPH *)
  Definition post_lex_classify (text : Str) : ClassifyResult :=
    match mph_probe text with
    | Some id => Keyword id
    | None => Ident
    end.

  Theorem post_lex_agrees_with_dfa_on_keywords : forall kw,
    In kw keyword_set ->
    post_lex_classify (kw_str kw) = Keyword (kw_id kw).
  Proof.
    intros kw Hin.
    unfold post_lex_classify.
    unfold mph_probe.
    rewrite (mph_table_populated kw Hin).
    destruct (str_eq_dec (kw_str kw) (kw_str kw)) as [_ | Hneq].
    - reflexivity.
    - exfalso. apply Hneq. reflexivity.
  Qed.

  Theorem post_lex_ident_for_non_keywords : forall text,
    (forall kw, In kw keyword_set -> kw_str kw <> text) ->
    post_lex_classify text = Ident.
  Proof.
    intros text Hnot_kw.
    unfold post_lex_classify.
    rewrite (mph_probe_non_keyword text Hnot_kw).
    reflexivity.
  Qed.

End MphProof.

(* ===================================================================== *)
(*  Abstraction Gaps                                                       *)
(*                                                                         *)
(*  1. CHD table construction: The CHD algorithm (Compress, Hash,         *)
(*     Displace) computes displacement values to ensure collision-free     *)
(*     slot assignment.  Construction correctness is verified empirically  *)
(*     at compile time — if CHD fails to find a valid displacement table,  *)
(*     compilation fails.  The Rocq model takes collision-freedom as a    *)
(*     hypothesis (mph_slot_unique).                                       *)
(*  2. Double-hashing: The Rust uses two FNV-1a hash functions with       *)
(*     different seeds (h1, h2).  The Rocq model abstracts the full       *)
(*     CHD computation as a single function mph_slot.                      *)
(*  3. DFA→MPH pipeline: The Rust pipeline is sequential — DFA lexes     *)
(*     first, then MPH reclassifies identifiers.  The Rocq model treats  *)
(*     this as atomic (post_lex_classify).                                 *)
(*  4. Key verification: The Rust probe checks MPH_KEYS[slot] == text    *)
(*     (mph.rs:436) to reject non-keywords.  This is modeled by the      *)
(*     str_eq_dec comparison in mph_probe.                                 *)
(*  5. Table sizing: The Rust computes table_size as the smallest prime   *)
(*     >= |keywords|.  The Rocq model uses mph_in_range to bound slots   *)
(*     within table bounds.                                                *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  Summary of Results                                                     *)
(*                                                                         *)
(*  T1: mph_probe_to_dfa                                                   *)
(*      mph_probe(text) = Some(id) -> dfa_classify(text) = Keyword(id)    *)
(*                                                                         *)
(*  T2: dfa_to_mph_probe                                                   *)
(*      dfa_classify(text) = Keyword(id) /\ kw in set                     *)
(*      -> mph_probe(text) = Some(id)                                      *)
(*                                                                         *)
(*  T3: mph_no_collisions                                                  *)
(*      Distinct keywords have distinct slots.                             *)
(*                                                                         *)
(*  C1: mph_probe_non_keyword                                              *)
(*      Non-keywords get None from mph_probe.                              *)
(*                                                                         *)
(*  C2: post_lex_agrees_with_dfa_on_keywords                               *)
(*      Post-lex pipeline correctly reclassifies keywords.                 *)
(*                                                                         *)
(*  C3: post_lex_ident_for_non_keywords                                    *)
(*      Post-lex pipeline preserves Ident for non-keywords.               *)
(*                                                                         *)
(*  All proofs are COMPLETE -- zero Admitted.                               *)
(* ===================================================================== *)
