# Ascent Datalog Engine: Theory and Architecture

Ascent is PraTTaIL's semantic engine. Where PathMap provides **structural indexing** (O(k) lookup and lattice algebra over syntax trees), Ascent provides **semantic closure** — computing the least fixed point of user-defined equations, rewrites, and congruence rules via Datalog evaluation.

**Prerequisites:** Basic familiarity with logic programming and fixed-point computation.

---

## 1. What is Datalog?

Datalog is a declarative query language based on Horn clauses (rules where a head is implied by a conjunction of body atoms). In PraTTaIL, Datalog rules express semantic relationships over syntax trees:

```text
eq_proc(s, t) <-- proc(s), if let Proc::PDrop(f0) = s,
                  if let Name::NQuote(p) = &**f0,
                  let t = p.clone();
```

This rule says: "for every term `s` that is a `PDrop(NQuote(p))`, `s` is equal to `p`."

### Key Properties

| Property | Implication |
|----------|-------------|
| **Monotonic** | Rules can only add facts, never retract them |
| **Finite domain** | All terms are finite syntax trees |
| **Termination** | Guaranteed: monotonic + finite domain → fixed point in finite steps |
| **Declarative** | Order of rules doesn't matter (only logical content) |

### Horn Clause Form

Every Datalog rule has the form:

```text
H(x₁,...,xₘ) :- B₁(y₁,...), B₂(y₂,...), ..., Bₙ(yₙ,...).
```

where `H` is the head (conclusion) and `B₁,...,Bₙ` are body atoms (premises). Variables in the head must appear in the body (range restriction).

---

## 2. Semi-Naive Evaluation

### Naive Evaluation

The simplest strategy: repeatedly apply all rules to all known facts until no new facts are derived.

```text
T↑0 = ∅
T↑(i+1) = T(T↑i)
T↑ω = lfp(T) = ⋃ᵢ T↑i(∅)
```

where `T` is the **immediate consequence operator** — one pass of all rules.

**Problem:** Naive evaluation re-derives existing facts every iteration. If iteration `i` derives 1000 facts but only 3 are new, it wastes work on the 997 already-known ones.

### Semi-Naive Evaluation

Semi-naive evaluation (Bancilhon 1986) tracks **delta relations** — facts derived in the *previous* iteration only:

```text
Δr⁰ = T(∅)                     -- initial derivation
rⁱ = rⁱ⁻¹ ∪ Δrⁱ⁻¹             -- accumulate
Δrⁱ = T(Δrⁱ⁻¹) ∖ rⁱ           -- only genuinely new facts
```

Each rule body is rewritten to use at least one delta relation, ensuring only new-fact combinations are explored. When `Δrⁱ = ∅`, the fixed point is reached.

### Convergence Guarantee

> **Theorem.** For a Datalog program P over a finite domain D, semi-naive evaluation terminates in at most |D|^k iterations, where k is the maximum rule arity. The result is the unique least fixed point of P.

*Proof.* Each iteration adds at least one new fact. The total number of possible facts is bounded by |D|^k × |relations|. Since facts are never retracted (monotonicity), the sequence T↑i is monotonically increasing and bounded, hence convergent. Uniqueness follows from the Knaster-Tarski theorem applied to the complete lattice of fact sets under ⊆. ∎

---

## 3. Ascent in Rust

[Ascent](https://crates.io/crates/ascent) is a Rust proc-macro that embeds Datalog in Rust. PraTTaIL generates Ascent programs during `language!` macro expansion.

### From `ascent_run!` to `ascent!` Named Struct

Early PraTTaIL used `ascent_run!`, which created a fresh anonymous struct per invocation, causing 13 monomorphizations of the same logic. The optimization to `ascent!` with a named struct reduced this to 4 (89% compile time reduction):

```rust
// Before (13 monomorphizations):
ascent_run! {
    relation proc(Proc);
    relation eq_proc(Proc, Proc);
    // ... rules ...
}

// After (4 monomorphizations):
ascent! {
    struct RhoCalcTheory;
    relation proc(Proc);
    #[ds(crate::eqrel)]
    relation eq_proc(Proc, Proc);
    // ... rules ...
}
```

### Relation Annotations

Ascent supports data structure annotations that control how relations are indexed:

| Annotation | Meaning | Used for |
|-----------|---------|----------|
| `#[ds(crate::eqrel)]` | Equivalence relation (symmetric, transitive closure) | `eq_cat` relations |
| `#[ds(crate::dual_indexed)]` | Hash index on both columns | `rw_cat`, `fold_cat` |
| (none) | Default hash set | `cat`, `step_term` |

The `eqrel` annotation is critical: it automatically maintains the equivalence closure (reflexivity, symmetry, transitivity) for equality relations, avoiding the need for explicit closure rules.

---

## 4. Why Ascent?

### Why Not Hand-Written Iteration?

Hand-written iteration (explicit loops over terms) is fragile and hard to optimize:
- No delta tracking (re-examines all terms every pass)
- No declarative specification (logic mixed with control flow)
- No automatic stratification (user must manually order computations)

### Why Not Prolog?

Prolog uses depth-first search with backtracking, which:
- Can diverge on recursive rules
- Does not compute fixed points (computes individual query answers)
- Requires cut operators for efficiency (breaking declarativeness)

### Why Not Datalog-in-SQL?

SQL-based Datalog (e.g., recursive CTEs) lacks:
- Rust type safety (terms are typed enum values, not strings)
- Compile-time code generation (macro expansion, not runtime SQL parsing)
- Custom data structure selection (`eqrel`, `dual_indexed`)

### Ascent's Advantages

1. **Declarative**: Rules specify *what* to compute, not *how*
2. **Type-safe**: Relations are typed by Rust enums (`Proc`, `Name`, etc.)
3. **Semi-naive**: Delta tracking is automatic and correct
4. **Compile-time**: Proc-macro generates optimized Rust code
5. **Extensible**: Custom relation types and data structures

---

## 5. The Generated Ascent Program

The `language!` macro generates an Ascent program with this structure:

```text
ascent! {
    struct TheoryName;

    // ── Relation declarations ──────────────────────
    relation proc(Proc);                              // Category
    #[ds(crate::eqrel)]
    relation eq_proc(Proc, Proc);                     // Equality
    #[ds(crate::dual_indexed)]
    relation rw_proc(Proc, Proc);                     // Rewrite
    #[ds(crate::dual_indexed)]
    relation fold_proc(Proc, Proc);                   // Fold (if applicable)
    relation step_term(Proc);                         // Seed
    relation ppar_contains(Proc, Proc);               // Collection projection

    // ── Category exploration rules ─────────────────
    proc(f0) <-- proc(s), if let Proc::PPar(bag) = s,
                 for f0 in bag.iter();                // Extract subterms

    // ── Reflexivity ────────────────────────────────
    eq_proc(t.clone(), t) <-- proc(t);               // ∀t. t ≡ t

    // ── Congruence ─────────────────────────────────
    eq_proc(Proc::PNew(b.clone()), Proc::PNew(c.clone()))
        <-- eq_proc(a, b), if let Proc::PNew(a_inner) = a,
            let c = /* reconstruct with b */;

    // ── User equations ─────────────────────────────
    eq_proc(s.clone(), t) <-- proc(s),
        if let Proc::PDrop(f0) = s, ...;

    // ── User rewrites ──────────────────────────────
    rw_proc(s_orig.clone(), t) <-- eq_proc(s_orig, s),
        if let Proc::Pattern(...) = s, ...;

    // ── Custom logic rules ─────────────────────────
    custom_rel(x, y) <-- ...;
}
```

The next documents detail each layer of this generated program.

---

## References

1. **Ceri, S., Gottlob, G. & Tanca, L.** (1989). "What You Always Wanted to Know About Datalog (And Never Dared to Ask)." *IEEE Transactions on Knowledge and Data Engineering* 1(1), 146-166.

2. **Bancilhon, F.** (1986). "Naive Evaluation of Recursively Defined Relations." In *On Knowledge Base Management Systems*, 165-178. — Original semi-naive evaluation algorithm.

3. **Knaster, B.** (1928). "Un théorème sur les fonctions d'ensembles." *Annales de la Société Polonaise de Mathématique* 6, 133-134. — Fixed-point theorem underlying Datalog semantics.

---

## Key Source Files

| File | Role |
|------|------|
| `macros/src/logic/relations.rs` | Relation declarations |
| `macros/src/logic/categories.rs` | Category exploration rules |
| `macros/src/logic/equations.rs` | Reflexivity + congruence + user equations |
| `macros/src/logic/rules.rs` | Unified `generate_rule_clause()` |
| `macros/src/logic/congruence.rs` | Explicit congruence rules |
| `macros/src/logic/common.rs` | Shared utilities (relation names, demand filtering) |

---

**Next:** [Relation Schema](relation-schema.md) — the generated relations and their roles.
