# Compiler Theory Foundations

This document develops the compiler-theoretic foundations underlying PraTTaIL:
the pipeline phases of a meta-compiler, attribute grammars and their Datalog
realization, operator-precedence grammars via Pratt parsing, and the
trampoline/CPS transformation that ensures stack safety.

---

## § 1 — Pipeline Phases

### 1.1 The Classical Compiler Pipeline

A traditional compiler processes source text through a sequence of phases, each
corresponding to a level of the Chomsky hierarchy:

```
Source → Lexical Analysis → Syntactic Analysis → Semantic Analysis → Code Generation → Target
         (Type 3: DFA)     (Type 2: CFG)        (Type 1/0: attrs)   (translation)
```

- **Lexical analysis** decomposes the input character stream into tokens using a
  deterministic finite automaton (Type 3 — regular languages).
- **Syntactic analysis** organizes tokens into a parse tree using a context-free
  grammar (Type 2 — context-free languages).
- **Semantic analysis** enforces constraints beyond context-free power
  (Type 1/0 — context-sensitive properties such as type checking, scope
  resolution, and name binding).
- **Code generation** translates the annotated AST into the target language.

### 1.2 PraTTaIL as a Meta-Compiler

PraTTaIL is a **meta-compiler** (compiler-compiler): it takes a language
specification written in a higher-order logic (HOL)-style DSL and generates a
complete parser as Rust source code that implements the above pipeline.

PraTTaIL's own compile-time pipeline:

| Phase | Description                             | Source File                                               |
|-------|-----------------------------------------|-----------------------------------------------------------|
| 1     | Language spec → NFA construction        | `automata/nfa.rs`                                         |
| 2     | NFA → DFA subset construction           | `automata/subset.rs`                                      |
| 3     | DFA minimization (Hopcroft)             | `automata/minimize.rs`                                    |
| 4     | FIRST/FOLLOW set computation            | `prediction.rs`                                           |
| 5     | WFST weight assignment                  | `wfst.rs`, `pipeline.rs`                                  |
| 6     | Rust codegen: lexer + Pratt + RD parser | `codegen.rs`, `pratt.rs`, `recursive.rs`, `trampoline.rs` |

At runtime, the generated parser executes three phases:

1. **Lexing**: DFA-driven tokenization (maximal munch with priority).
2. **Parsing**: Pratt binding-power loop for expressions, recursive descent for
   structural rules (let, if-then-else, binders), with an explicit trampoline
   continuation stack for stack safety.
3. **AST construction**: de Bruijn-indexed binders via `close_term()` in the
   generated moniker code (`runtime/src/binding.rs`).

### 1.3 Correctness of the Pipeline

Each phase preserves the language recognized:

**Theorem 1.1** (Pipeline language preservation). Let L be the language defined
by a PraTTaIL specification. The generated parser accepts exactly L.

**Proof**. The proof follows from the correctness of each phase transformation:

1. Thompson's construction produces an NFA N such that L(N) = L_regex for each
   token pattern (see `01-order-theory.md` and `finite-automata.md`).
2. Subset construction produces a DFA D with L(D) = L(N) (Rabin-Scott theorem).
3. Hopcroft minimization produces D_min with L(D_min) = L(D) and |D_min|
   minimal (Myhill-Nerode theorem).
4. FIRST/FOLLOW sets are computed as least fixed points of monotone operators on
   finite lattices (Knaster-Tarski; see `prediction-and-lookahead.md`).
5. WFST weights annotate transitions but do not alter the accepted language
   (the support of a weighted automaton equals the unweighted language).
6. The generated Pratt + RD parser recognizes the CFG defined by the
   specification's rules (see § 3 below for the Pratt correctness argument). ∎

---

## § 2 — Attribute Grammars and Datalog

### 2.1 Attribute Grammars

**Definition 2.1** (Attribute Grammar; Knuth 1968). An *attribute grammar*
AG = (G, A, R) consists of:

- A context-free grammar G = (N, Σ, P, S).
- A finite set of attributes A = A_s ∪ A_i, partitioned into *synthesized*
  attributes A_s (computed bottom-up from children) and *inherited* attributes
  A_i (computed top-down from parent and siblings).
- A set of semantic rules R, one for each production, specifying how to compute
  each attribute from others.

The evaluation order is determined by the *attribute dependency graph*. An AG is
*well-defined* if this graph is acyclic for every derivation tree, guaranteeing
a unique evaluation order.

### 2.2 Datalog

**Definition 2.2** (Datalog). A Datalog program P is a finite set of
function-free Horn clauses (rules) of the form:

  H :- B₁, B₂, …, Bₙ

where H (the head) and each Bᵢ (body atoms) are positive relational atoms
over variables and constants. Negation and function symbols are excluded.

**Definition 2.3** (Immediate Consequence Operator). The *immediate consequence
operator* T_P maps a set of ground facts I to:

  T_P(I) = { Hσ ∣ (H :- B₁, …, Bₙ) ∈ P, σ a ground substitution,
              B₁σ ∈ I, …, Bₙσ ∈ I }

**Theorem 2.1** (Datalog Fixed-Point Semantics). T_P is monotone on the
complete lattice (2^(Herbrand base), ⊆). By the Knaster-Tarski fixed-point
theorem, T_P has a least fixed point lfp(T_P) computable as:

  lfp(T_P) = ⋃_{n≥0} T_P^n(∅)

**Proof**. Monotonicity: if I ⊆ J, then every ground instance of a rule body
satisfiable by I is also satisfiable by J, so T_P(I) ⊆ T_P(J). The Herbrand
base is finite (Datalog is function-free), so the lattice has finite height.
By Kleene's fixed-point theorem for monotone functions on finite lattices
(see `01-order-theory.md` § 5), iteration from ∅ reaches the least fixed point
in finitely many steps. ∎

### 2.3 Concrete Grounding: PraTTaIL's Ascent Logic Blocks

PraTTaIL's `logic {}` blocks (in `macros/src/ast/`) compile to Ascent Datalog
relations. The connection to attribute grammars is:

- **Synthesized attributes** correspond to Datalog rules whose body references
  child AST nodes and whose head produces a fact at the parent node (e.g.,
  type synthesis: `type(parent, T) :- type(child1, T1), type(child2, T2), …`).
- **Inherited attributes** correspond to rules that propagate context downward
  (e.g., scope information, expected types).
- The Ascent engine computes lfp(T_P) via **semi-naïve evaluation**, which
  avoids redundant re-derivation by tracking only newly derived facts at each
  iteration (Δ-relations).
- WFST-informed optimizations (documented in `docs/optimization/`) transform
  the generated Ascent code to exploit the grammar's WFST structure.

---

## § 3 — Pratt Parsing as Operator-Precedence Grammar

### 3.1 Operator-Precedence Grammars

**Definition 3.1** (Operator-Precedence Grammar; Floyd 1963). An
*operator-precedence grammar* (OPG) is a context-free grammar such that for
each pair of terminal symbols (a, b), at most one of the following precedence
relations holds:

- a ⋖ b  (a *yields precedence to* b; b binds tighter)
- a ≐ b  (a and b have *equal precedence*)
- a ⋗ b  (a *takes precedence over* b; a binds tighter)

OPGs are a strict subset of LR(1) grammars. They admit O(n) parsing via a
shift-reduce automaton that inspects only the stack top and the lookahead token.

### 3.2 Pratt Parsing and Binding Powers

**Definition 3.2** (Binding Power Assignment). A *binding power assignment* is
a function bp : Operators → ℕ × ℕ mapping each operator op to a pair
(lbp(op), rbp(op)), where lbp is the *left binding power* and rbp is the
*right binding power*.

**Theorem 3.1** (Pratt-Floyd Correspondence). Pratt parsing with binding powers
(lbp, rbp) encodes Floyd's precedence relations. Specifically, for operators a
and b appearing in the configuration "… a E b …" (where E is an expression):

- rbp(a) < lbp(b)  ⟹  a ⋖ b  (b binds tighter; shift)
- rbp(a) > lbp(b)  ⟹  a ⋗ b  (a binds tighter; reduce)
- rbp(a) = lbp(b)  ⟹  a ≐ b  (equal precedence)

**Proof**. We verify the correspondence by examining the Pratt parsing loop.
The generated parser (`pratt.rs`, `trampoline.rs`) executes:

```
while bp < get_lbp(peek_token()) {
    left = parse_infix(left, bp);  // led (left denotation)
}
```

where `bp` is the current minimum binding power (initially the rbp of the
operator that invoked this sub-expression parse).

**Case 1** (rbp(a) < lbp(b)): The loop condition `bp < lbp(b)` holds, so
`parse_infix` is called for b. This corresponds to a **shift**: b captures the
intervening expression E. Thus a ⋖ b.

**Case 2** (rbp(a) > lbp(b)): The loop condition fails, so the current
expression is returned to a's caller. This corresponds to a **reduce**: a
retains E as its operand. Thus a ⋗ b.

**Case 3** (rbp(a) = lbp(b)): The loop uses strict inequality (`<`), so equal
binding powers cause a reduce (left-associative behavior). By adjusting the
inequality to `≤`, we obtain right-associative behavior. Thus rbp(a) = lbp(b)
encodes equal precedence, with the choice of strict vs. non-strict inequality
determining associativity. ∎

### 3.3 Concrete Grounding: PraTTaIL's BP Assignment

PraTTaIL assigns binding powers in `binding_power.rs` via `build_bp_table()`.
Starting from a base precedence of 2, each precedence level receives a pair:

- **Left-associative**: (lbp, rbp) = (p, p+1), then p ← p+2.
  Since lbp < rbp, the Pratt loop uses rbp = p+1 for recursive calls. For two
  left-associative operators at the same level, rbp(a) = p+1 > lbp(a) = p,
  yielding a ⋗ a (left-associative self-reduction).

- **Right-associative**: (lbp, rbp) = (p+1, p), then p ← p+2.
  Since lbp > rbp, the recursive call uses rbp = p. For self-comparison,
  rbp(a) = p = lbp(a) − 1 < lbp(a), so the loop continues (shift), giving
  right-associative behavior.

- **Postfix**: lbp = postfix_prec + 1, rbp = 0 (unused; no right operand).
  Postfix operators start above the prefix gap: postfix_prec = max_infix_prec + 2.

- **Prefix**: rbp = max_infix_bp + 2 (from `prefix_bp` in `recursive.rs`).
  Prefix operators bind tighter than all infix operators.

### 3.4 Extension Beyond Classical OPGs

PraTTaIL extends classical OPGs by mixing Pratt parsing (for operator
expressions) with recursive descent (for structural syntax: `let`, `if-then-else`,
binders, collections). This combination is sound because:

1. RD rules are dispatched **before** entering the Pratt loop, based on the
   lookahead token. Each RD rule calls back into the Pratt parser for
   sub-expressions, respecting binding powers.
2. The dispatch is deterministic: FIRST set analysis (`prediction.rs`) ensures
   each token triggers at most one RD rule per category. WFST weights break
   ties when FIRST sets overlap.
3. Mixfix operators (e.g., ternary `a ? b : c`) are integrated into the Pratt
   loop with interior operands parsed at min_bp = 0 (precedence reset, like
   grouping parentheses) and the final operand at the operator's rbp.

---

## § 4 — CPS and Trampolines

### 4.1 Continuation-Passing Style

**Definition 4.1** (CPS Transformation). A program is in *continuation-passing
style* if every function f takes an explicit continuation argument k and, instead
of returning a value v, invokes k(v). Formally, for a direct-style function
f : A → B, the CPS transform is f' : A × (B → ⊥) → ⊥, where ⊥ denotes
"does not return" (all control flow is explicit in k).

CPS eliminates the implicit call stack: the continuation k encodes the entire
remaining computation. However, naively allocating closures for each k leads to
unbounded heap growth.

### 4.2 Trampolines

**Definition 4.2** (Trampoline). A *trampoline* is an iterative loop that
repeatedly invokes *thunks* (suspended computations). Each thunk returns either:

- **Done(v)**: a final value v, terminating the loop; or
- **More(t)**: the next thunk t to invoke, continuing the loop.

The trampoline converts tail-recursive CPS into bounded-stack iteration:
the call depth is O(1) regardless of input nesting depth.

### 4.3 Concrete Grounding: PraTTaIL's Trampoline

PraTTaIL's trampoline (`trampoline.rs`) materializes the CPS continuation
stack as an explicit `Vec<Frame_Cat>`:

- Each `Frame_Cat` variant encodes a return point: the operation to resume,
  the accumulated AST, and the position state. This is the *defunctionalized*
  representation of the continuation (Reynolds 1972).
- **Thread-local pooling**: each category maintains a `Cell<Vec<Frame_Cat>>`
  pool in thread-local storage. The trampoline takes the pool at entry and
  returns it at exit, recycling the allocation across parse calls.
- **Stack safety**: the explicit frame stack lives on the heap, supporting
  100,000+ nesting depth (versus ~10,000 before native stack overflow with
  recursive calls).

**Theorem 4.1** (Trampoline Correctness). The trampolined parser produces the
same AST as the recursive parser for all inputs within the recursive parser's
stack limit.

**Proof**. The trampoline is a mechanical CPS + defunctionalization of the
recursive descent parser. Each recursive call `parse_Cat(tokens, pos, bp)` is
replaced by pushing a `Frame_Cat` onto the frame stack and jumping to the
trampoline loop entry. Each return is replaced by popping the top frame and
dispatching on its variant. Since:

1. Every `Frame_Cat` variant corresponds one-to-one with a recursive call site.
2. Push/pop order is LIFO, matching the call stack discipline.
3. No computation is reordered: the frame stores the exact continuation state
   (partial AST, position, binding power) that the recursive version would hold
   on its stack frame.

The trampolined execution trace is isomorphic to the recursive trace, producing
identical AST output for identical input. ∎

### 4.4 De Bruijn Indices

**Definition 4.3** (De Bruijn Index; de Bruijn 1972). In the *de Bruijn
representation* of lambda terms, each variable occurrence is replaced by a
natural number indicating the number of enclosing binders between the
occurrence and its binding site:

- λx. x  ≡  λ. 0  (bound by the immediately enclosing λ)
- λx. λy. x  ≡  λ. λ. 1  (bound one binder away)
- λx. λy. λz. x  ≡  λ. λ. λ. 2

De Bruijn indices yield **α-equivalence for free**: two terms are α-equivalent
if and only if their de Bruijn representations are syntactically identical.

**Concrete Grounding**: The `close_term()` method in `runtime/src/binding.rs`
converts named variables to de Bruijn indices during AST construction. It
tracks binding depth via `ScopeState` and resolves each variable occurrence
to the appropriate index by counting enclosing binders.

---

## § 5 — References

- Floyd, R. W. (1963). "Syntactic analysis and operator precedence."
  *JACM*, 10(3), 316–333.
- Pratt, V. R. (1973). "Top down operator precedence." *POPL '73*, 41–51.
- Knuth, D. E. (1968). "Semantics of context-free languages." *Mathematical
  Systems Theory*, 2(2), 127–145.
- Appel, A. W. (2004). *Modern Compiler Implementation in ML*. Cambridge
  University Press.
- de Bruijn, N. G. (1972). "Lambda calculus notation with nameless dummies."
  *Indagationes Mathematicae*, 34, 381–392.
- Ceri, S., Gottlob, G., & Tanca, L. (1989). "What you always wanted to know
  about Datalog." *IEEE TKDE*, 1(1), 146–166.
- Reynolds, J. C. (1972). "Definitional interpreters for higher-order
  programming languages." *Proc. 25th ACM National Conference*, 717–740.
