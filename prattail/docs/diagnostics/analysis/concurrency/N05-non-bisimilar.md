# N05: non-bisimilar

**Severity:** Warning
**Category:** analysis/concurrency
**Feature Gate:** `alternating`

## Description

Reports that two categories in the grammar are *not bisimilar* -- they have
structurally different observable behavior as determined by an alternating
automaton bisimulation game. This means the two categories cannot be freely
substituted for each other in grammar contexts, because there exists at least
one input sequence that distinguishes them.

Bisimulation is the gold standard for behavioral equivalence in process algebra
and automata theory. Two systems are bisimilar if and only if no external
observer can distinguish them through any sequence of interactions. In the
grammar context, two categories are bisimilar if they accept exactly the same
set of token sequences with the same branching structure (not just the same
flat language, but the same tree of parsing choices).

The analysis uses an *alternating automaton* to model the bisimulation game
between two categories. The game has two players:

- **Attacker (Spoiler):** Tries to demonstrate a difference between the two
  categories. Chooses transitions in one category and challenges the Defender
  to match them in the other.
- **Defender (Duplicator):** Tries to show that the categories are equivalent.
  Must find a matching transition for every Attacker move.

The categories are bisimilar if and only if the Defender has a winning strategy
from the initial position. Equivalently, the categories are *not* bisimilar if
the Attacker has a winning strategy.

### Bisimulation game diagram

The following diagram shows a bisimulation game between two categories `Proc`
and `Stmt`. The Attacker finds a distinguishing move that the Defender cannot
match:

```
  Bisimulation Game: Proc vs Stmt
  ════════════════════════════════

  Round 1:
  ┌──────────────────────────────────────────────────────────┐
  │  Position: (Proc, Stmt)                                  │
  │                                                          │
  │  Proc transitions:          Stmt transitions:            │
  │    Proc ──"send"──> Proc'     Stmt ──"send"──> Stmt'    │
  │    Proc ──"recv"──> Proc''    Stmt ──"recv"──> Stmt''   │
  │    Proc ──"par"───> Proc'''   Stmt ──"seq"───> Stmt'''  │
  │                               ^                          │
  │  Attacker chooses:            │ no "par" transition!     │
  │    Proc ──"par"──> Proc'''    │                          │
  │                               │                          │
  │  Defender must match with     │                          │
  │  Stmt ──"par"──> ???          │                          │
  │  NO MATCH FOUND!              │                          │
  └──────────────────────────────────────────────────────────┘

  Result: Attacker wins at Round 1
  Verdict: Proc and Stmt are NOT bisimilar

  Game tree:
                    (Proc, Stmt)
                     /    |    \
              "send"/  "recv"|   \"par"
                   /      |      \
        (Proc', Stmt')  (Proc'',  (Proc''', ???)
            |            Stmt'')     ^
         Defender         |          │
         matches       Defender    Attacker
                       matches     WINS
```

In this example, `Proc` has a `"par"` transition (parallel composition) that
`Stmt` lacks (it has `"seq"` instead). The Attacker exploits this difference
in Round 1, and the Defender cannot respond. The game terminates with an
Attacker victory, proving that the categories are not bisimilar.

### Formal definition

Two states q_1 and q_2 in an alternating automaton are bisimilar (q_1 ~ q_2)
if there exists a relation R such that (q_1, q_2) in R and for all (s, t) in R:

  1. forall a in Sigma, s' . (s --a--> s') implies exists t' . (t --a--> t') and (s', t') in R
  2. forall a in Sigma, t' . (t --a--> t') implies exists s' . (s --a--> s') and (s', t') in R

The bisimulation game unfolds this coinductive definition as an interactive
protocol. PraTTaIL computes the winning positions via a fixed-point
computation over the product state space:

  attacker_wins(s, t) = exists a in Sigma .
    (exists s' . s --a--> s' and forall t' . t --a--> t' implies attacker_wins(s', t'))
    or
    (exists t' . t --a--> t' and forall s' . s --a--> s' implies attacker_wins(s', t'))

The initial position (init_a, init_b) is checked: if attacker_wins(init_a, init_b)
is true, the categories are not bisimilar.

## Trigger Conditions

A warning is emitted **once per non-bisimilar pair** when **all** of the
following conditions hold:

1. The `alternating` feature is enabled.
2. The pipeline's alternating automaton module (`alternating.rs`) has been
   executed, producing an `AlternatingAnalysis`.
3. The result's `non_bisimilar_pairs` vector is non-empty.

One diagnostic is emitted for each `(cat_a, cat_b)` pair in
`non_bisimilar_pairs`.

The lint is silent when:
- The `alternating` feature is not enabled.
- No `AlternatingAnalysis` is available (analysis was not run).
- The `non_bisimilar_pairs` vector is empty (all compared categories are bisimilar).

## Example

### Grammar

```
language! {
    name: ProcLang;
    primary: Proc;

    category Proc {
        Send  = "send" "!" Chan "(" Expr ")";
        Recv  = "recv" "?" Chan "(" Name ")";
        Par   = Proc "|" Proc;
        Seq   = Proc ";" Proc;
        Zero  = "0";
    }

    category Stmt {
        SSend = "send" "!" Chan "(" Expr ")";
        SRecv = "recv" "?" Chan "(" Name ")";
        SSeq  = Stmt ";" Stmt;
        SSkip = "skip";
    }

    category Chan {
        ChanId = <ident>;
    }

    category Expr {
        native_type: Integer;
        IntLit = <int>;
    }

    category Name {
        Ident = <ident>;
    }
}
```

`Proc` has `Par` (parallel composition) and `Zero`, while `Stmt` has `SSeq`
(sequential composition) and `SSkip`. The Attacker can distinguish them by
choosing the `"|"` transition in `Proc`, which `Stmt` cannot match.

### Output

```
warning[N05] (ProcLang): categories `Proc` and `Stmt` are not bisimilar (attacker wins game)
  = hint: these categories have structurally different observable behavior
```

## Resolution

When N05 fires, the two categories have different observable behavior. The
resolution depends on the grammar author's intent:

1. **Intended difference.** If the categories are meant to model different
   constructs (e.g., processes vs. statements), the non-bisimilarity is
   expected. The warning documents the structural difference and confirms that
   the categories are not interchangeable.

2. **Unintended difference.** If the categories should be interchangeable
   (e.g., they are intended to be two representations of the same concept),
   the Attacker's winning move reveals the distinguishing rule:
   - **Missing rule:** One category lacks a transition that the other has.
     Add the missing rule to make them structurally equivalent.
   - **Extra rule:** One category has a transition that the other does not
     need. Remove it or add a corresponding rule to the other category.
   - **Different sub-categories:** The categories reference different
     sub-categories (e.g., one uses `Proc` as a child, the other uses `Stmt`).
     Unify the sub-categories or add cast rules.

3. **Refactor into a single category.** If the categories are nearly bisimilar
   and serve the same purpose, consider merging them into a single category
   with all the combined rules.

4. **Add a cast rule.** If one category is a sub-behavior of the other (all
   of its transitions are matchable in the other direction), a cast rule from
   the smaller to the larger may be appropriate, even though full bisimilarity
   does not hold.

## Hint Explanation

The hint "these categories have structurally different observable behavior"
summarizes the conclusion of the bisimulation game. The Attacker found at least
one transition in one category that the Defender could not match in the other.
This structural difference means the categories are not interchangeable:
substituting one for the other in a grammar context may change the set of
accepted inputs or the shape of the parse tree. The hint encourages the grammar
author to review whether this difference is intentional or accidental.

## Related Lints

- [N03](N03-scope-violation.md) -- Scope violations; may contribute to non-bisimilarity if one category respects scoping rules that the other violates
- [N04](N04-scope-narrowing.md) -- Scope narrowing; tightening scopes can affect bisimilarity by reducing the observable behavior of a category
- [S01](../../safety/S01-safety-violation.md) -- Safety violation; non-bisimilar categories that are incorrectly treated as interchangeable may lead to bad parser states
- [G07](../../grammar/G07-identical-rules.md) -- Identical rules within a category; structurally identical rules across categories are a precondition for bisimilarity
