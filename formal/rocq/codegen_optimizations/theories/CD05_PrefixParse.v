(*
 * CD05_PrefixParse: Prefix parse determinism and CSE soundness.
 *
 * When multiple RD rules for a category share a common nonterminal prefix,
 * parsing the prefix once (CSE -- Common Subexpression Elimination) and
 * then dispatching on the discriminating FIRST set is equivalent to parsing
 * the prefix separately for each rule.  This file proves:
 *   1. Parsing shared prefix once produces same AST as parsing it per-branch
 *   2. CSE is sound (no lost parses) when discriminating FIRST sets are disjoint
 *   3. CSE is complete (no spurious parses)
 *
 * The Rust implementation uses FIRST sets (multiple tokens per rule) for
 * dispatch discrimination, not single tokens.  When FIRST sets overlap,
 * CSE is not applied (graceful degradation gated by `all_disjoint`).
 *
 * Spec-to-Code Traceability:
 *   Rocq Definition              | Rust Code                                | Location
 *   -----------------------------|------------------------------------------|-----------------------------------------
 *   shared_prefix                | shared_prefix_depth()                    | prattail/src/decision_tree.rs:3206
 *   prefix_cse                   | detect_prefix_cse_opportunities()        | prattail/src/decision_tree.rs:982
 *   cse_annotation               | emit_prefix_cse_annotation()             | prattail/src/decision_tree.rs:1106
 *   rd_discriminators             | first_of_rd_suffix() FIRST sets          | prattail/src/prediction.rs
 *   Optimization::PrefixCse      | cost_benefit::Optimization::PrefixCse    | prattail/src/cost_benefit.rs:134
 *   OptimizationGates::prefix_cse | prefix_cse gate field                   | prattail/src/cost_benefit.rs
 *   first_of_rd_suffix           | first_of_rd_suffix()                     | prattail/src/prediction.rs
 *   write_prefix_match_arms      | trampoline prefix dispatch               | prattail/src/trampoline.rs
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
(*  Token and AST Model                                                    *)
(* ===================================================================== *)

Definition Token := nat.

(* Simple AST: a tree with a constructor tag and children *)
Inductive AST : Type :=
  | ALeaf : Token -> AST
  | ANode : nat -> list AST -> AST.

(* Token stream *)
Definition TokenStream := list Token.

(* Parse result: the AST produced and remaining tokens *)
Definition ParseResult := option (AST * TokenStream).

(* ===================================================================== *)
(*  Parser Model                                                           *)
(*                                                                         *)
(*  A parser for a nonterminal consumes tokens and produces an AST.       *)
(*  We model parsers as functions from token streams to parse results.    *)
(* ===================================================================== *)

Definition Parser := TokenStream -> ParseResult.

(* A parser is deterministic: it produces at most one result *)
Definition parser_deterministic (p : Parser) : Prop :=
  forall ts ast1 rest1 ast2 rest2,
    p ts = Some (ast1, rest1) ->
    p ts = Some (ast2, rest2) ->
    ast1 = ast2 /\ rest1 = rest2.

(* ===================================================================== *)
(*  Rule Model                                                             *)
(*                                                                         *)
(*  An RD rule for a category consists of:                                *)
(*  - A prefix: a nonterminal parser that parses the shared prefix        *)
(*  - A discriminating FIRST set (decidable Token -> bool)                *)
(*  - A suffix: a parser for the rest of the rule                         *)
(*  - A constructor tag for building the AST                               *)
(*                                                                         *)
(*  The Rust implementation computes FIRST sets of suffix tokens          *)
(*  (multiple tokens per rule) via first_of_rd_suffix() in prediction.rs. *)
(*  The discriminator is a set, not a single token.                        *)
(* ===================================================================== *)

Record RDRule := mkRDRule {
  rd_prefix_parser : Parser;       (* parser for the shared prefix nonterminal *)
  rd_discriminators : Token -> bool; (* FIRST set of the suffix — distinguishes this rule *)
  rd_suffix_parser : Parser;       (* parser for the remainder *)
  rd_constructor : nat              (* AST constructor tag *)
}.

(* Parse a rule: parse prefix, check discriminator set, parse suffix, build AST *)
Definition parse_rule (r : RDRule) (ts : TokenStream) : ParseResult :=
  match rd_prefix_parser r ts with
  | Some (prefix_ast, rest1) =>
    match rest1 with
    | tok :: rest2 =>
      if rd_discriminators r tok
      then match rd_suffix_parser r rest2 with
           | Some (suffix_ast, rest3) =>
               Some (ANode (rd_constructor r) [prefix_ast; ALeaf tok; suffix_ast], rest3)
           | None => None
           end
      else None
    | [] => None
    end
  | None => None
  end.

(* ===================================================================== *)
(*  CSE Optimization: Parse Prefix Once                                    *)
(*                                                                         *)
(*  Instead of parsing the prefix for each rule, parse it once and then   *)
(*  dispatch on the discriminating FIRST set.                              *)
(*                                                                         *)
(*  Graceful degradation: when FIRST sets overlap (not disjoint), the     *)
(*  Rust code does not apply CSE — it falls back to per-rule parsing.     *)
(*  This is gated by the `all_disjoint` check in the Rust implementation. *)
(* ===================================================================== *)

(* Rules sharing the same prefix parser *)
Definition shared_prefix_rules (rules : list RDRule) : Prop :=
  forall r1 r2, In r1 rules -> In r2 rules ->
    forall ts, rd_prefix_parser r1 ts = rd_prefix_parser r2 ts.

(* Discriminating FIRST sets are pairwise disjoint:
   no token appears in two different rules' discriminator sets *)
Definition disjoint_discriminators (rules : list RDRule) : Prop :=
  forall r1 r2 tok, In r1 rules -> In r2 rules ->
    rd_discriminators r1 tok = true -> rd_discriminators r2 tok = true -> r1 = r2.

(* CSE parser: parse prefix once, then dispatch on discriminator set *)
Definition cse_parse (prefix : Parser) (rules : list RDRule) (ts : TokenStream) : ParseResult :=
  match prefix ts with
  | Some (prefix_ast, rest1) =>
    match rest1 with
    | tok :: rest2 =>
      (* Find the rule whose discriminator set contains tok *)
      match find (fun r => rd_discriminators r tok) rules with
      | Some r =>
        match rd_suffix_parser r rest2 with
        | Some (suffix_ast, rest3) =>
            Some (ANode (rd_constructor r) [prefix_ast; ALeaf tok; suffix_ast], rest3)
        | None => None
        end
      | None => None
      end
    | [] => None
    end
  | None => None
  end.

(* ===================================================================== *)
(*  Theorem 1: CSE parse = per-rule parse for matching rule                *)
(*                                                                         *)
(*  If rules share a prefix and a rule r matches, then CSE parse          *)
(*  produces the same AST as parsing with r directly.                     *)
(* ===================================================================== *)

(* Helper: find returns Some r when r's discriminator set contains tok *)
Lemma find_correct : forall rules tok r,
  find (fun r => rd_discriminators r tok) rules = Some r ->
  In r rules /\ rd_discriminators r tok = true.
Proof.
  induction rules as [| r' rest IH].
  - intros tok r H. simpl in H. discriminate.
  - intros tok r H. simpl in H.
    destruct (rd_discriminators r' tok) eqn:Heq.
    + injection H as Heq'. subst r'.
      split.
      * left. reflexivity.
      * exact Heq.
    + apply IH in H as [Hin Hdisc].
      split.
      * right. exact Hin.
      * exact Hdisc.
Qed.

(* Helper: if r is in rules and its discriminator set contains tok,
   find returns Some r (when discriminator sets are disjoint) *)
Lemma find_with_disjoint : forall rules r tok,
  In r rules ->
  disjoint_discriminators rules ->
  rd_discriminators r tok = true ->
  find (fun r' => rd_discriminators r' tok) rules = Some r.
Proof.
  induction rules as [| r' rest IH].
  - intros r tok Hin. destruct Hin.
  - intros r tok Hin Hdisj Hdisc.
    simpl.
    destruct (rd_discriminators r' tok) eqn:Heq.
    + (* r' matches tok *)
      destruct Hin as [Heq' | Hin].
      * subst. reflexivity.
      * (* r and r' both match tok, so by disjointness r = r' *)
        assert (Hr_eq : r = r').
        { apply (Hdisj r r' tok).
          - right. exact Hin.
          - left. reflexivity.
          - exact Hdisc.
          - exact Heq. }
        subst. reflexivity.
    + (* r' does not match tok *)
      destruct Hin as [Heq' | Hin].
      * subst. rewrite Hdisc in Heq. discriminate.
      * apply IH; try assumption.
        intros r1 r2 tok' Hr1 Hr2 Hd1 Hd2.
        apply (Hdisj r1 r2 tok' (or_intror Hr1) (or_intror Hr2) Hd1 Hd2).
Qed.

(* ===================================================================== *)
(*  Theorem 1: For the matching rule, CSE = per-rule                      *)
(* ===================================================================== *)

Theorem cse_eq_matching_rule : forall rules r prefix ts prefix_ast tok rest2,
  In r rules ->
  shared_prefix_rules rules ->
  disjoint_discriminators rules ->
  (forall ts', rd_prefix_parser r ts' = prefix ts') ->
  prefix ts = Some (prefix_ast, tok :: rest2) ->
  rd_discriminators r tok = true ->
  parse_rule r ts = cse_parse prefix rules ts.
Proof.
  intros rules r prefix ts prefix_ast tok rest2 Hin Hshared Hdisj Hprefix_eq Hparse Hdisc.
  unfold parse_rule.
  rewrite (Hprefix_eq ts).
  unfold cse_parse.
  rewrite Hparse.
  rewrite Hdisc.
  rewrite (find_with_disjoint rules r tok Hin Hdisj Hdisc).
  reflexivity.
Qed.

(* ===================================================================== *)
(*  Theorem 2: CSE is sound (no lost parses)                               *)
(*                                                                         *)
(*  If any rule in the set can parse the input, then the CSE parser       *)
(*  also parses it (provided discriminator sets are disjoint).             *)
(* ===================================================================== *)

Theorem cse_sound : forall rules r prefix ts ast rest,
  In r rules ->
  shared_prefix_rules rules ->
  disjoint_discriminators rules ->
  (forall r' ts', In r' rules -> rd_prefix_parser r' ts' = prefix ts') ->
  parse_rule r ts = Some (ast, rest) ->
  cse_parse prefix rules ts = Some (ast, rest).
Proof.
  intros rules r prefix ts ast rest Hin Hshared Hdisj Hprefix Hparse.
  unfold parse_rule in Hparse.
  destruct (rd_prefix_parser r ts) as [[pf_ast rest1] |] eqn:Hpf; try discriminate.
  destruct rest1 as [| tok rest2]; try discriminate.
  destruct (rd_discriminators r tok) eqn:Hmatch; try discriminate.
  destruct (rd_suffix_parser r rest2) as [[sf_ast rest3] |] eqn:Hsf; try discriminate.
  injection Hparse as Hast Hrest. subst ast rest.
  unfold cse_parse.
  rewrite <- (Hprefix r ts Hin). rewrite Hpf.
  rewrite (find_with_disjoint rules r tok Hin Hdisj Hmatch).
  rewrite Hsf. reflexivity.
Qed.

(* ===================================================================== *)
(*  Theorem 3: CSE is complete (no spurious parses)                        *)
(*                                                                         *)
(*  If the CSE parser produces a result, then some rule in the set would  *)
(*  produce the same result when run individually.                         *)
(* ===================================================================== *)

Theorem cse_complete : forall rules prefix ts ast rest,
  (forall r ts', In r rules -> rd_prefix_parser r ts' = prefix ts') ->
  disjoint_discriminators rules ->
  cse_parse prefix rules ts = Some (ast, rest) ->
  exists r, In r rules /\ parse_rule r ts = Some (ast, rest).
Proof.
  intros rules prefix ts ast rest Hprefix Hdisj Hcse.
  unfold cse_parse in Hcse.
  destruct (prefix ts) as [[pf_ast rest1] |] eqn:Hpf; try discriminate.
  destruct rest1 as [| tok rest2]; try discriminate.
  destruct (find (fun r => rd_discriminators r tok) rules) as [r |] eqn:Hfind; try discriminate.
  apply find_correct in Hfind as [Hin Hdisc].
  destruct (rd_suffix_parser r rest2) as [[sf_ast rest3] |] eqn:Hsf; try discriminate.
  injection Hcse as Hast Hrest. subst ast rest.
  exists r. split.
  - exact Hin.
  - unfold parse_rule.
    rewrite (Hprefix r ts Hin). rewrite Hpf.
    rewrite Hdisc.
    rewrite Hsf. reflexivity.
Qed.

(* ===================================================================== *)
(*  Abstraction Gaps                                                       *)
(*                                                                         *)
(*  1. FIRST set computation: The Rocq model takes rd_discriminators as   *)
(*     given.  The actual FIRST set computation via fixed-point iteration *)
(*     (prediction.rs:218) is outside the scope of this proof.            *)
(*  2. Graceful degradation: When FIRST sets overlap, the Rust code does  *)
(*     NOT apply CSE — it gates on `all_disjoint`.  The proof only       *)
(*     claims correctness under the disjoint_discriminators precondition. *)
(*  3. Decision tree path merging: The Rust implementation uses the       *)
(*     decision tree (decision_tree.rs:810) for the actual dispatch.      *)
(*     The `find`-based dispatch here is a simplification.                *)
(*  4. Suffix reconstruction: The Rust reconstructs suffix patterns from  *)
(*     pattern elements.  The Rocq model uses abstract suffix parsers.    *)
(*  5. Trust boundary: The prefix parser correctness (i.e., that          *)
(*     shared_prefix_rules accurately reflects the grammar) is assumed.   *)
(* ===================================================================== *)

(* ===================================================================== *)
(*  Summary of Results                                                     *)
(*                                                                         *)
(*  T1: cse_eq_matching_rule                                               *)
(*      For the matching rule, CSE parse = per-rule parse.                *)
(*                                                                         *)
(*  T2: cse_sound                                                          *)
(*      If any rule parses the input, CSE also parses it.                 *)
(*      (No lost parses when discriminator FIRST sets are disjoint.)      *)
(*                                                                         *)
(*  T3: cse_complete                                                       *)
(*      If CSE parses the input, some rule also parses it.                *)
(*      (No spurious parses.)                                              *)
(*                                                                         *)
(*  All proofs are COMPLETE -- zero Admitted.                               *)
(* ===================================================================== *)
