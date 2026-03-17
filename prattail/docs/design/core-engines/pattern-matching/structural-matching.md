# Iterative Match Engine (match_pattern.rs)

PraTTaIL generates an iterative, stack-safe pattern matching engine for each language defined via the `language!` macro. This engine matches ground terms against patterns containing free variables, extracting variable bindings for use in Ascent Datalog rules.

**Prerequisites:** [Pattern Matching Overview](overview.md)

---

## 1. MatchBindings: Per-Category Binding Vectors

The `MatchBindings` struct accumulates variable bindings during pattern matching. Each syntactic category gets its own binding vector:

```rust
// Generated for a language with types Proc, Name:
pub struct MatchBindings {
    pub proc_bindings: Vec<(String, Proc)>,
    pub name_bindings: Vec<(String, Name)>,
}

impl MatchBindings {
    pub fn empty() -> Self {
        MatchBindings {
            proc_bindings: Vec::new(),
            name_bindings: Vec::new(),
        }
    }
}
```

Bindings are stored as `(variable_name, value)` pairs. Per-category vectors provide type safety: a `Proc` variable can only bind to a `Proc` value.

---

## 2. MatchTask Enum: Heterogeneous Work Items

The work stack uses a `MatchTask` enum with one variant per category:

```rust
// Generated:
enum MatchTask {
    MatchProc(Proc, Proc),    // (ground_term, pattern)
    MatchName(Name, Name),    // (ground_term, pattern)
}
```

Each variant carries a `(ground, pattern)` pair for that category. When a `Regular` constructor has cross-category fields (e.g., `PNew(Name, Proc)`), the handler pushes tasks for both the `Name` and `Proc` sub-matches.

---

## 3. Thread-Local Pool

The work stack is pooled via thread-local storage to achieve zero steady-state allocation:

```rust
thread_local! {
    static MATCH_POOL: std::cell::Cell<Vec<MatchTask>> =
        std::cell::Cell::new(Vec::new());
}
```

### Take/Set Protocol

```text
1. Take the buffer:  stack = POOL.take()     // O(1), leaves empty Vec in Cell
2. Clear and use:    stack.clear(); stack.push(initial_task)
3. Process:          while let Some(task) = stack.pop() { ... }
4. Return buffer:    POOL.set(stack)          // O(1), preserves capacity
```

### Re-Entrancy

Collection and binder matching re-enter the match engine (calling `match_pattern` recursively). Each re-entrant call takes from the pool; if the pool is empty (outer call still holds it), a fresh `Vec` is allocated. The outermost call returns its buffer to the pool, preserving the accumulated capacity for future calls.

---

## 4. Matching Strategies by Variant

The generated engine dispatches on the pattern variant:

### Var (Free Variable)

```text
Pattern: FreeVar(x)
Action:  Bind x → ground_term in MatchBindings
Stack:   No push (immediate)
```

The simplest case: the pattern variable matches any ground term. The binding is recorded immediately.

### Literal / Nullary Constructor

```text
Pattern: Lit(42) matched against Ground: Lit(42)
Action:  Exact equality check
Stack:   No push (immediate)
Result:  Succeed if equal, fail otherwise
```

### Regular Constructor

```text
Pattern: PNew(name_pat, body_pat) matched against Ground: PNew(name_val, body_val)
Action:  Push MatchTask::MatchName(name_val, name_pat)
         Push MatchTask::MatchProc(body_val, body_pat)
Stack:   +2 tasks
```

The children are pushed onto the work stack and matched in subsequent iterations. If the constructor tags don't match, the entire match fails.

### Collection

```text
Pattern: PPar({p₁, p₂, ...}) matched against Ground: PPar({g₁, g₂, ...})
Action:  Element-wise matching via re-entrant match_pattern calls
Stack:   No push (inline loop)
```

Collections are matched inline rather than via the work stack. Each element pair `(gᵢ, pᵢ)` triggers a re-entrant `match_pattern` call. This bounds stack depth by collection size rather than nesting depth.

### Binder / MultiBinder

```text
Pattern: Lambda(x, body_pat) matched against Ground: Lambda(_, body_val)
Action:  Open scope (bind x), then re-entrant match on body
Stack:   No push (inline)
```

Binder matching opens a binding scope, then re-enters the engine for the body. Multi-binders iterate over the binder list.

---

## 5. Iterative Engine Pseudocode

```text
fn match_pattern(ground: &Cat, pattern: &Cat) → Option<MatchBindings>:
    // 1. Take pool buffer
    stack ← MATCH_POOL.take()
    stack.clear()
    bindings ← MatchBindings::empty()

    // 2. Push initial task
    stack.push(MatchTask::MatchCat(ground.clone(), pattern.clone()))

    // 3. Process work stack
    while let Some(task) = stack.pop():
        match task:
            MatchTask::MatchCat(ground, pattern) →
                match pattern:
                    FreeVar(x) →
                        bindings.cat_bindings.push((x, ground))
                    Lit(v) →
                        if ground ≠ Lit(v): return None
                    Constructor(f, args_pat) →
                        if let Constructor(f, args_ground) = ground:
                            for (g, p) in zip(args_ground, args_pat):
                                stack.push(MatchTask::MatchSubCat(g, p))
                        else:
                            MATCH_POOL.set(stack)
                            return None
                    Collection(elems_pat) →
                        // Inline element-wise matching (re-entrant)
                        ...

    // 4. Return pool buffer
    MATCH_POOL.set(stack)
    Some(bindings)
```

---

## 6. Performance Characteristics

Benchmarked against recursive matching (from the trampoline sprint):

| Metric | Improvement | Mechanism |
|--------|-------------|-----------|
| Nesting depth capacity | 100K+ (was ~10K crash) | Explicit stack vs. call stack |
| Nesting overhead | ~15% faster | No function call overhead per level |
| Infix matching | ~9% faster | Fewer allocations (TLS pool) |
| Cross-category matching | ~6% faster | Single work stack for all categories |

The work stack grows linearly with nesting depth but is bounded by term size. The TLS pool ensures the buffer capacity accumulates over time, reaching the high-water mark of the deepest term matched, then reusing that capacity for all subsequent matches.

---

## 7. Generated Code Structure

`generate_match_pattern()` (`match_pattern.rs:52-69`) produces four components:

1. **`MatchBindings` type**: Per-category binding vectors
2. **`MatchTask` enum**: One variant per category
3. **Iterative engine**: The `match_pattern_iterative()` function
4. **`impl Cat` methods**: Per-category `match_pattern()` / `match_pattern_other()` entry points

The entry points delegate to the iterative engine, which handles all categories uniformly via the `MatchTask` enum.

---

## Key Source Files

| File | Role |
|------|------|
| `macros/src/gen/term_ops/match_pattern.rs` | Match engine generation |
| `macros/src/gen/term_ops/subst.rs` | Variant classification (`FieldInfo`, `VariantKind`) |

---

**Next:** [Unification](unification.md) — Martelli-Montanari as a ConstraintTheory.
