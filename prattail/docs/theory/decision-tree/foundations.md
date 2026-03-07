# Decision Tree Theoretical Foundations for PraTTaIL

| Metadata   | Value      |
|------------|------------|
| Date       | 2026-03-06 |
| Updated    | 2026-03-06 |

---

## Table of Contents

- [SS1 Decision Trees as LL(k) Parse Tables](#1-decision-trees-as-llk-parse-tables)
- [SS2 Relationship to FIRST/FOLLOW](#2-relationship-to-firstfollow)
- [SS3 Determinism Theorem](#3-determinism-theorem)
- [SS4 Nonterminal Boundary Theorem](#4-nonterminal-boundary-theorem)
- [SS5 Minimum Lookahead Depth](#5-minimum-lookahead-depth)
- [SS6 Subsumption over Existing Optimizations](#6-subsumption-over-existing-optimizations)
- [SS7 PathMap Lattice Properties](#7-pathmap-lattice-properties)

---

## SS1 Decision Trees as LL(k) Parse Tables

A decision tree encodes the deterministic dispatch logic of a parser for a
syntactic category. Rather than consulting a two-dimensional LL(k) parse table
indexed by (nonterminal, lookahead tuple), PraTTaIL materializes the table as a
trie whose edges are byte-encoded token identifiers and whose leaves prescribe
parsing actions.

**Definition 1 (Decision Tree).** Let C be a syntactic category with rules
R_1, ..., R_n. A *decision tree* for C is a trie

```
    T_C : byte* -> DecisionAction
```

where:

- Each edge is labeled with a byte value b in {0, ..., 255} representing a
  token identifier from the grammar's `TokenIdMap`.
- Each internal node corresponds to a position in the lookahead sequence at
  which the parser must inspect the next token.
- Each leaf is a `DecisionAction`, which is one of:
  - `Commit(rule_index)` -- deterministically apply rule R_i.
  - `Ambiguous(candidates)` -- multiple rules remain viable; fall back to
    ordered trial or Pratt dispatch.
  - `Error` -- no rule matches; report a parse error.

The *depth* of the trie is the maximum length of any root-to-leaf path, which
corresponds to the maximum lookahead required for deterministic dispatch.

**Definition 1a (Path).** A *path* in T_C is a finite sequence of bytes
p = (b_1, b_2, ..., b_d) such that traversing edges b_1, b_2, ..., b_d from
the root reaches a node (internal or leaf) at depth d.

**Definition 1b (Encoding).** The function `encode_terminal : Terminal -> byte`
maps each terminal symbol in the grammar to its unique identifier in the
`TokenIdMap`. A rule R_i with leading terminals t_1, t_2, ..., t_m encodes to
the path (encode_terminal(t_1), encode_terminal(t_2), ..., encode_terminal(t_m))
via the function `pattern_from_rd_rule`.

---

## SS2 Relationship to FIRST/FOLLOW

The decision tree's structure is intimately related to the classical FIRST and
FOLLOW set constructions from LL parsing theory. This section establishes that
the tree's branching at depth 1 is governed exactly by the FIRST set.

**Definition 2 (FIRST Set).** For a syntactic category C with rules
R_1, ..., R_n, the FIRST set is:

```
    FIRST(C) = { t in Sigma | exists R_i, exists w in Sigma* : R_i =>* t w }
```

where Sigma is the set of terminal symbols and =>* denotes derivation in zero
or more steps.

**Definition 3 (Byte Encoding of FIRST Set).** The byte encoding of FIRST(C)
is the set:

```
    ByteFirst(C) = { encode_terminal(t) | t in FIRST(C) }
```

**Theorem 1 (FIRST Set Correspondence).** For category C with FIRST set
FIRST(C), the set of first bytes in T_C is a subset of ByteFirst(C). That is:

```
    { b_1 | (b_1, ..., b_d) is a path in T_C } `subseteq` ByteFirst(C)
```

*Proof.* We proceed by showing that every depth-1 edge label in T_C corresponds
to a terminal in FIRST(C).

Let b be a byte label on an edge from the root of T_C to some child node. By
construction of the trie, this edge was inserted during the encoding of some
rule R_i of category C.

Step 1. Rule R_i has a leading syntactic pattern. The function
`pattern_from_rd_rule` encodes this pattern into a byte sequence by applying
`encode_terminal` to each terminal in the pattern's prefix.

Step 2. The first byte b of this encoding is `encode_terminal(t_1)`, where t_1
is the first terminal symbol that rule R_i can produce. By the definition of
`encode_terminal`, this function returns the `TokenIdMap` identifier assigned to
t_1 during grammar registration.

Step 3. Since t_1 is the first terminal that R_i can derive, we have
t_1 in FIRST(R_i). Since R_i is a rule of category C, we have
FIRST(R_i) `subseteq` FIRST(C), and therefore t_1 in FIRST(C).

Step 4. By Definition 3, `encode_terminal(t_1) in ByteFirst(C)`, so b in ByteFirst(C).

Since b was an arbitrary depth-1 edge label, every such label belongs to
ByteFirst(C).

Therefore, { b_1 | (b_1, ..., b_d) is a path in T_C } `subseteq` ByteFirst(C). `square`

**Remark.** The inclusion may be strict: ByteFirst(C) may contain tokens for
which no rule was inserted into T_C (e.g., if a rule's pattern is handled
entirely by Pratt prefix dispatch rather than the RD trie).

---

## SS3 Determinism Theorem

The central property that enables backtracking elimination is that pairwise
distinct children at every branch point guarantee a unique parsing decision.

**Definition 4 (Branch Point).** A *branch point* in T_C is an internal node
with two or more children.

**Definition 5 (Pairwise Distinct Children).** An internal node v in T_C has
*pairwise distinct children* if for every pair of edges (v, b_i, u_i) and
(v, b_j, u_j) with i != j, we have b_i != b_j.

**Observation.** Since T_C is a trie, pairwise distinct children is an inherent
structural property: by definition, a trie node has at most one child per
distinct edge label. Thus, the condition in Theorem 2 is automatically satisfied
by the trie structure. The substantive question is whether the trie can be
constructed at all (i.e., whether the grammar's rules produce distinct byte
prefixes), not whether a constructed trie has duplicate edges.

**Theorem 2 (Disjoint Children implies No Backtracking).** If at every branch point in
T_C, the children's byte labels are pairwise distinct, then parsing can proceed
without save/restore backtracking.

*Proof.* We prove that at each step, the parser makes a deterministic choice
without needing to speculatively try alternatives.

**Base case (depth 0, the root).** The parser is at the root of T_C and has not
yet consumed any lookahead. It examines the current input token t and computes
b = encode_terminal(t).

- If the root has a child with edge label b, the parser descends to that child.
  By the pairwise distinctness of children (which holds by the trie property),
  there is exactly one such child. No alternative needs to be tried.
- If the root has no child with edge label b, the parser reports an error. No
  backtracking is needed because there is no viable alternative.

In neither case does the parser save its position for later restoration.

**Inductive step (depth d > 0).** Assume that the parser has deterministically
reached an internal node v at depth d without backtracking. The parser examines
the next input token t' and computes b' = encode_terminal(t').

- If v has a child with edge label b', the parser descends to that unique child
  (uniqueness guaranteed by the trie property). No save/restore is needed.
- If v is a leaf with action `Commit(rule_index)`, the parser applies the rule.
  No alternative exists to try.
- If v has no child with edge label b' and v is not a `Commit` leaf, the parser
  reports an error. Since the parser reached v deterministically (by the
  inductive hypothesis), no saved position exists to restore.

**Conclusion.** By induction on the depth of traversal, the parser never needs
to save its position or restore a previously saved position. Every step is
deterministic, and no speculative parsing occurs. Therefore, parsing proceeds
without save/restore backtracking. `square`

**Corollary 2a.** A decision tree T_C with pairwise distinct children at all
branch points enables an O(k) dispatch algorithm, where k is the depth of the
tree, since at each depth exactly one comparison and one pointer dereference are
performed.

---

## SS4 Nonterminal Boundary Theorem

When a rule's right-hand side contains a nonterminal, the parser must decide
which category to invoke. If the candidate categories have disjoint FIRST sets,
this decision can be made with a single token of lookahead.

**Definition 6 (Nonterminal Boundary).** A *nonterminal boundary* in a rule's
right-hand side is a position where the parser must choose among nonterminal
categories NT_1, ..., NT_n to parse next.

**Definition 7 (FIRST-Disjoint).** Categories NT_1, ..., NT_n are
*FIRST-disjoint* if:

```
    for all i != j : FIRST(NT_i) `cap` FIRST(NT_j) = `emptyset`
```

**Theorem 3 (FIRST-Disjoint NT Resolution).** At a nonterminal boundary where
the candidate NT categories NT_1, ..., NT_n are pairwise FIRST-disjoint,
one-token lookahead suffices for deterministic dispatch.

*Proof.* Let the parser be at a nonterminal boundary with candidates
NT_1, ..., NT_n, and let t be the next input token.

Step 1. Since NT_1, ..., NT_n are FIRST-disjoint, the sets FIRST(NT_1), ...,
FIRST(NT_n) are pairwise disjoint. Therefore, t belongs to at most one of these
sets. Formally:

```
    |{ i in {1, ..., n} | t in FIRST(NT_i) }| `leq` 1
```

We prove this by contradiction. Suppose t in FIRST(NT_i) and t in FIRST(NT_j)
for some i != j. Then t in FIRST(NT_i) `cap` FIRST(NT_j), contradicting the
FIRST-disjointness assumption that FIRST(NT_i) `cap` FIRST(NT_j) = `emptyset`.

Step 2. The parser peeks at t (without consuming it) and tests membership in
each FIRST set.

- **Case A: t in FIRST(NT_i) for exactly one i.** The parser dispatches to NT_i.
  By Step 1, this is the only viable option. No other category can derive a
  string starting with t, so the dispatch is deterministic.

- **Case B: t not in FIRST(NT_i) for any i.** No candidate category can derive a
  string starting with t. The parser reports an error. Since no candidate is
  viable, no backtracking or trial parsing is needed.

Step 3. In both cases, the decision is made by examining a single token (the
next input token t). No speculative parsing of any candidate category is
required, and no position save/restore occurs.

Therefore, one-token lookahead suffices for deterministic dispatch at a
FIRST-disjoint nonterminal boundary. `square`

**Corollary 3a.** If FIRST-disjointness holds at all nonterminal boundaries in
the grammar, then the entire parser operates with at most one token of lookahead
for nonterminal dispatch, reducing to LL(1) behavior at those positions.

---

## SS5 Minimum Lookahead Depth

Different categories may require different amounts of lookahead for deterministic
dispatch. This section formalizes the notion of minimum lookahead depth.

**Definition 8 (Minimum Lookahead Depth).** The *minimum lookahead depth* k for
category C is the smallest natural number d such that every root-to-node path in
T_C of length `leq` d satisfies one of:

1. The node is a `Commit` leaf (deterministic dispatch achieved).
2. The node is an internal branch point whose children have pairwise distinct
   byte labels (the next token resolves the ambiguity).

Formally:

```
    k = min { d in N | for all paths (b_1, ..., b_m) in T_C with m `leq` d :
              node(b_1, ..., b_m) is Commit
              `lor` children of node(b_1, ..., b_m) are pairwise distinct }
```

**Lemma 4a (Existence of Minimum Lookahead).** For any finite decision tree
T_C, the minimum lookahead depth k exists and satisfies 0 `leq` k `leq` depth(T_C).

*Proof.* Since T_C is finite, it has a finite depth d_max = depth(T_C). Every
path of length d_max terminates at a leaf, which is either a `Commit` or
`Ambiguous` action. At depth d_max, every node trivially satisfies one of the
two conditions (it is a leaf with no children to conflict, or it is a `Commit`).
Therefore, d = d_max satisfies the condition, and the minimum over a non-empty
finite set exists. `square`

**Theorem 4 (LL(k) Dispatch without Backtracking).** If the minimum lookahead
depth of T_C is k, then an LL(k) parser for C can dispatch without
backtracking.

*Proof.* We construct a parsing procedure that uses at most k tokens of
lookahead and never backtracks, then prove its correctness.

**Construction.** The parser operates as follows:

1. Starting at the root of T_C, peek at the next k input tokens
   t_1, t_2, ..., t_k (without consuming them).
2. Compute the byte sequence b_i = encode_terminal(t_i) for each i in {1, ..., k}.
3. Traverse T_C following the edges b_1, b_2, ..., b_k, stopping early if a
   `Commit` leaf is reached.

**Correctness.** We show that this procedure always reaches a deterministic
decision.

Let p = (b_1, ..., b_m) be the path traversed, where m `leq` k.

- **If a `Commit(rule_index)` leaf is reached at depth m `leq` k:** The parser
  deterministically applies rule R_{rule_index}. This is correct because
  `Commit` leaves are inserted only when a unique rule matches the prefix.

- **If an internal node v is reached at depth m < k:** By Definition 8, since
  m < k `leq` d (where d satisfies the minimum lookahead condition), node v must
  have pairwise distinct children. The parser examines b_{m+1} and descends to
  the unique matching child. This process continues until either a `Commit` leaf
  is reached or depth k is attained.

- **If depth k is reached at an internal node v:** By Definition 8 (since the
  path has length k = the minimum lookahead depth), v must satisfy one of the
  two conditions. If v is a `Commit` leaf, the decision is made. If v has
  pairwise distinct children, then examining the next token resolves the
  ambiguity -- but since we defined k as sufficient, this case means the
  children at depth k are already distinct and the dispatch completes at or
  before depth k.

In all cases, the parser makes a deterministic choice without saving or
restoring its position. Therefore, an LL(k) parser for C dispatches without
backtracking. `square`

**Corollary 4a.** The minimum lookahead depth provides an exact characterization
of the LL strength required: category C is LL(k) if and only if its decision
tree T_C has minimum lookahead depth `leq` k.

---

## SS6 Subsumption over Existing Optimizations

PraTTaIL's codebase historically employed several ad-hoc analyses to detect
deterministic dispatch opportunities. The decision tree framework unifies and
subsumes all of them.

**Theorem 5 (Subsumption).** The decision tree analysis subsumes the following
ad-hoc analyses:

- (a) `group_rd_by_dispatch_token`: Grouping rules by their first terminal.
- (b) `compute_shared_terminal_prefix`: Finding the longest common prefix of
      terminals shared by all rules of a category.
- (c) `second_token_lookahead`: Checking that rules differing in the second
      token can be distinguished by two-token lookahead.
- (d) `suffix_disjointness_check`: Verifying that after a shared prefix, the
      remaining suffixes have disjoint first tokens.
- (e) `is_deterministic_fallback_dead`: Determining that no cross-category
      fallback is reachable for a given dispatch token.

We prove each part separately.

**Proof of (a): `group_rd_by_dispatch_token`.**

*Claim:* Grouping rules by their first terminal is equivalent to enumerating the
children of the trie root.

Let R_1, ..., R_n be the rules of category C, and let t_i be the first terminal
of rule R_i. The function `group_rd_by_dispatch_token` partitions {R_1, ..., R_n}
into groups {R_i | t_i = t} for each distinct terminal t.

In the trie T_C, each rule R_i contributes a path whose first edge has label
b_i = encode_terminal(t_i). The children of the root are exactly the set of
distinct first-edge labels { b_i | i in {1, ..., n} }. Enumerating these
children and collecting the rules associated with each child yields the same
partition as `group_rd_by_dispatch_token`.

Therefore, grouping by dispatch token is equivalent to iterating trie children
at depth 1. `square`

**Proof of (b): `compute_shared_terminal_prefix`.**

*Claim:* A shared terminal prefix of length l corresponds to a chain of l
single-child nodes from the root.

The function `compute_shared_terminal_prefix` finds the longest sequence of
terminals t_1, ..., t_l such that every rule of C begins with t_1, ..., t_l.

In the trie T_C, if every rule shares the prefix (b_1, ..., b_l) where
b_j = encode_terminal(t_j), then:

- At depth 1, the root has exactly one child with label b_1 (since all rules
  agree on the first terminal).
- At depth 2, that child has exactly one child with label b_2 (since all rules
  agree on the second terminal).
- Continuing inductively, at depth j `leq` l, the node has exactly one child
  with label b_j.

A node with exactly one child is a single-child node (branching factor 1). Thus,
the shared prefix of length l corresponds to a chain of l single-child nodes.

Conversely, a chain of single-child nodes from the root of length l means every
path through the trie shares the first l edge labels, which decode to a shared
terminal prefix of length l.

Therefore, `compute_shared_terminal_prefix` computes the length of the
single-child chain from the root of T_C. `square`

**Proof of (c): `second_token_lookahead`.**

*Claim:* Two-token lookahead sufficiency is equivalent to checking that depth-2
children are pairwise distinct.

The function `second_token_lookahead` checks whether, for rules that share the
same first terminal, the second terminals are all distinct.

In the trie T_C, consider a depth-1 node v (a child of the root). The rules
routed through v all share the same first terminal. The children of v at depth 2
have edge labels corresponding to the second terminals of those rules.

`second_token_lookahead` succeeds if and only if, for each depth-1 node v, the
children of v have pairwise distinct edge labels. In the trie, this is
equivalent to requiring that v's branching factor equals its child count (i.e.,
no two rules passing through v share the same second terminal).

Since a trie inherently has distinct edge labels at each node, the check reduces
to verifying that the trie can be constructed without merging rules at depth 2
into `Ambiguous` leaves. This is precisely the condition that depth-2 children
are all distinct. `square`

**Proof of (d): `suffix_disjointness_check`.**

*Claim:* Suffix disjointness at position s is equivalent to checking that at
trie depth s, all children have distinct byte labels.

The function `suffix_disjointness_check` verifies that after consuming s
terminals of a shared prefix, the remaining rule suffixes begin with distinct
terminals.

In the trie T_C, after traversing the shared prefix of length s (a chain of
single-child nodes by part (b)), we arrive at a node v at depth s. The children
of v correspond to the first terminals of the remaining suffixes of each rule.

Suffix disjointness holds if and only if these children have pairwise distinct
byte labels. In trie terms, this means v's children enumerate without collision,
which is the standard trie property. The substantive check is whether the rules'
suffixes have distinct first tokens at position s, which corresponds exactly to
verifying that v has as many children as there are rules passing through it (no
two rules share the same (s+1)-th terminal).

Therefore, `suffix_disjointness_check` at position s is equivalent to checking
disjointness of children at trie depth s. `square`

**Proof of (e): `is_deterministic_fallback_dead`.**

*Claim:* A dead deterministic fallback for token t means no cross-category
alternative path exists, which corresponds to the absence of a fallback child
at depth 1 for byte encode_terminal(t).

The function `is_deterministic_fallback_dead` determines whether, for a given
dispatch token t, there exists a cross-category rule that could handle t if the
primary category's rules fail.

In the trie T_C, the depth-1 child for byte b = encode_terminal(t) leads to all
rules of C that begin with t. A cross-category fallback would be represented by
an additional child (or annotation on the existing child) indicating that an
alternative category could handle t.

If no such child or annotation exists -- i.e., the trie has no fallback path for
byte b -- then the deterministic fallback is dead. This is verified by the
absence of a corresponding child at depth 1 for the given token.

Conversely, if a fallback child exists, the fallback is alive, and the parser
may need to attempt cross-category dispatch.

Therefore, `is_deterministic_fallback_dead` is equivalent to checking the
absence of a fallback child at depth 1 of T_C. `square`

This completes the proof that the decision tree framework subsumes all five
ad-hoc analyses. Each analysis corresponds to a localized structural query on
the trie, and the trie provides a unified data structure from which all such
queries can be answered.

---

## SS7 PathMap Lattice Properties

The algebraic structure of decision trees enables compositional grammar
operations through lattice theory.

**Definition 9 (Lattice).** A *lattice* is a partially ordered set (L, `leq`)
in which every pair of elements a, b in L has:

- A *join* (least upper bound): a `lor` b
- A *meet* (greatest lower bound): a `land` b

**Definition 10 (DecisionAction Lattice).** The set of `DecisionAction` values
forms a lattice with the following operations:

- **Bottom (`bot`):** `Error` -- no rules match.
- **Top (`top`):** `Ambiguous({R_1, ..., R_n})` -- all rules are candidates.
- **Join (`lor`, `pjoin`):** Merge candidate lists by union.
  ```
  Commit(i) `lor` Commit(j) = Ambiguous({R_i, R_j})     if i != j
  Commit(i) `lor` Commit(i) = Commit(i)
  Ambiguous(S) `lor` Ambiguous(T) = Ambiguous(S `cup` T)
  Error `lor` x = x
  x `lor` Error = x
  ```
- **Meet (`land`, `pmeet`):** Intersect candidate lists by rule label.
  ```
  Commit(i) `land` Commit(j) = Error                     if i != j
  Commit(i) `land` Commit(i) = Commit(i)
  Ambiguous(S) `land` Ambiguous(T) = Ambiguous(S `cap` T)  (or Error if S `cap` T = `emptyset`)
  Error `land` x = Error
  x `land` Error = Error
  ```

**Lemma 7a (DecisionAction forms a lattice).** The operations `lor` and `land`
defined above satisfy the lattice axioms: commutativity, associativity,
absorption, and idempotency.

*Proof.* We verify each axiom.

**Idempotency.** For any action a:
- a `lor` a = a: If a = Commit(i), then Commit(i) `lor` Commit(i) = Commit(i).
  If a = Ambiguous(S), then Ambiguous(S) `lor` Ambiguous(S) = Ambiguous(S `cup` S) = Ambiguous(S).
  If a = Error, then Error `lor` Error = Error.
- a `land` a = a: Symmetric argument using `cap` instead of `cup`.

**Commutativity.** For any actions a, b:
- a `lor` b = b `lor` a: Follows from commutativity of set union (`cup`).
- a `land` b = b `land` a: Follows from commutativity of set intersection (`cap`).

**Associativity.** For any actions a, b, c:
- (a `lor` b) `lor` c = a `lor` (b `lor` c): Follows from associativity of `cup`.
  We verify the non-trivial case. Let a = Ambiguous(S), b = Ambiguous(T),
  c = Ambiguous(U). Then (a `lor` b) `lor` c = Ambiguous((S `cup` T) `cup` U) =
  Ambiguous(S `cup` (T `cup` U)) = a `lor` (b `lor` c). The cases involving
  Commit and Error reduce to this by treating Commit(i) as Ambiguous({R_i}) and
  Error as Ambiguous(`emptyset`) for the purpose of join.
- (a `land` b) `land` c = a `land` (b `land` c): Symmetric argument using `cap`.

**Absorption.** For any actions a, b:
- a `lor` (a `land` b) = a: We case-split.
  - If a = Error: Error `lor` (Error `land` b) = Error `lor` Error = Error = a. `checkmark`
  - If a = Commit(i), b = Commit(j) with i != j:
    a `land` b = Error, so a `lor` Error = a = Commit(i). `checkmark`
  - If a = Commit(i), b = Commit(i):
    a `land` b = Commit(i), so a `lor` Commit(i) = Commit(i) = a. `checkmark`
  - If a = Ambiguous(S), b = Ambiguous(T):
    a `land` b = Ambiguous(S `cap` T), so a `lor` Ambiguous(S `cap` T) =
    Ambiguous(S `cup` (S `cap` T)) = Ambiguous(S) = a (by the set-theoretic
    absorption law S `cup` (S `cap` T) = S). `checkmark`
  - Mixed cases (Commit/Ambiguous) reduce similarly by treating Commit(i) as
    Ambiguous({R_i}).
- a `land` (a `lor` b) = a: Symmetric argument.
  - If a = Error: Error `land` (Error `lor` b) = Error `land` b = Error = a. `checkmark`
  - If a = Ambiguous(S), b = Ambiguous(T):
    a `lor` b = Ambiguous(S `cup` T), so a `land` Ambiguous(S `cup` T) =
    Ambiguous(S `cap` (S `cup` T)) = Ambiguous(S) = a (by the set-theoretic
    absorption law S `cap` (S `cup` T) = S). `checkmark`
  - Other cases reduce similarly.

All four axioms are satisfied. Therefore, (DecisionAction, `lor`, `land`) is a
lattice with bottom Error and top Ambiguous({R_1, ..., R_n}). `square`

**Definition 11 (PathMap Lattice).** `PathMap<DecisionAction>` is the set of
all functions from byte paths to DecisionAction values. It forms a lattice by
*pointwise lifting* of the DecisionAction lattice:

```
    (f `lor` g)(p) = f(p) `lor` g(p)     for all paths p
    (f `land` g)(p) = f(p) `land` g(p)   for all paths p
```

where f(p) defaults to Error if path p is not present in f.

**Theorem 6 (PathMap Lattice).** `PathMap<DecisionAction>` forms a lattice
under join (merge candidates) and meet (intersect by rule label), enabling
algebraic composition of grammars.

*Proof.* We show that pointwise lifting of a lattice yields a lattice.

**Step 1: Pointwise lifting preserves lattice axioms.** Let (L, `lor`_L, `land`_L)
be a lattice, and let P be a set (the set of all byte paths). The set of
functions L^P = { f : P -> L } with pointwise operations:

```
    (f `lor` g)(p) = f(p) `lor`_L g(p)
    (f `land` g)(p) = f(p) `land`_L g(p)
```

is a lattice. We verify each axiom:

**Idempotency.** (f `lor` f)(p) = f(p) `lor`_L f(p) = f(p) for all p, by
idempotency in L. Therefore f `lor` f = f. Similarly for meet.

**Commutativity.** (f `lor` g)(p) = f(p) `lor`_L g(p) = g(p) `lor`_L f(p) =
(g `lor` f)(p) for all p, by commutativity in L. Similarly for meet.

**Associativity.** ((f `lor` g) `lor` h)(p) = (f(p) `lor`_L g(p)) `lor`_L h(p)
= f(p) `lor`_L (g(p) `lor`_L h(p)) = (f `lor` (g `lor` h))(p) for all p, by
associativity in L. Similarly for meet.

**Absorption.** (f `lor` (f `land` g))(p) = f(p) `lor`_L (f(p) `land`_L g(p))
= f(p) for all p, by absorption in L. Therefore f `lor` (f `land` g) = f.
Similarly for the dual absorption law.

**Step 2: Bottom and top.** The constant function `bot`(p) = Error for all p is
the bottom of PathMap (since Error is the bottom of DecisionAction). The
constant function `top`(p) = Ambiguous({R_1, ..., R_n}) for all p is the top.

**Step 3: Application to grammar composition.** Given two grammars G_1 and G_2
with decision trees T_1 and T_2 (viewed as PathMap functions), their composition
can be expressed as:

- **Union of grammars (G_1 `cup` G_2):** T_1 `lor` T_2, which merges candidate
  rule sets at each path. A path that leads to Commit(i) in T_1 and Commit(j)
  in T_2 (with i != j) becomes Ambiguous({R_i, R_j}), correctly reflecting that
  both rules are viable in the combined grammar.

- **Intersection of grammars (G_1 `cap` G_2):** T_1 `land` T_2, which retains
  only rules present in both grammars at each path. A path that leads to
  different rules in T_1 and T_2 becomes Error, correctly reflecting that the
  intersection admits no rule.

These operations are well-defined, associative, commutative, and satisfy
absorption, enabling modular grammar construction and analysis.

Therefore, `PathMap<DecisionAction>` forms a lattice under pointwise join and
meet, enabling algebraic composition of grammars. `square`

**Corollary 6a.** The lattice structure enables incremental grammar updates:
adding a rule R_new to category C corresponds to joining the existing PathMap
with a singleton PathMap containing only R_new's path, preserving all existing
dispatch decisions except where R_new introduces ambiguity.

---

## Summary of Results

| Result | Statement                                      | Significance                          |
|--------|------------------------------------------------|---------------------------------------|
| Def 1  | Decision tree as byte trie over DecisionAction | Unified data structure                |
| Thm 1  | First bytes `subseteq` ByteFirst(C)            | FIRST set governs depth-1 branching   |
| Thm 2  | Disjoint children implies no backtracking      | Core determinism guarantee            |
| Thm 3  | FIRST-disjoint NTs need 1-token lookahead      | Nonterminal dispatch                  |
| Thm 4  | LL(k) dispatch from minimum lookahead depth    | Precise lookahead characterization    |
| Thm 5  | Decision tree subsumes 5 ad-hoc analyses       | Unification of existing optimizations |
| Thm 6  | PathMap forms a lattice                        | Algebraic grammar composition         |
