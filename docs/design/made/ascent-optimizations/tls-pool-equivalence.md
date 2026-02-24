# Opt 2: TLS Vec Pool Iteration Equivalence

## 1. Motivation

The Ascent Datalog program extracts subterms from constructor terms using generated `match` arms. In the original (pre-Opt 2) codegen, each subterm extraction rule produced a `vec![...]` literal:

```rust
(match t {
    Cat::Add(f0, f1) => vec![f0.as_ref().clone(), f1.as_ref().clone()],
    Cat::Neg(f0)     => vec![f0.as_ref().clone()],
    _                => vec![],
}).into_iter()
```

Each `vec![]` allocates on the heap. In a fixpoint loop where rules fire repeatedly, this creates allocation pressure in the inner loop — the exact place where zero-cost iteration matters most.

**Concern:** The TLS pool reuses a buffer across calls. Does reuse preserve the exact sequence of extracted elements?

## 2. The Optimization

The TLS pool pattern replaces `vec![]` with a thread-local `Cell<Vec<T>>` that is taken, cleared, filled, and returned:

```rust
{
    thread_local! {
        static POOL: std::cell::Cell<Vec<Cat>> =
            const { std::cell::Cell::new(Vec::new()) };
    }
    let mut buf = POOL.with(|p| p.take());   // Step 1: take from pool
    buf.clear();                               // Step 2: clear prior contents
    match t {                                  // Step 3: match and push
        Cat::Add(f0, f1) => {
            buf.push(f0.as_ref().clone());
            buf.push(f1.as_ref().clone());
        },
        Cat::Neg(f0) => {
            buf.push(f0.as_ref().clone());
        },
        _ => {},
    }
    let iter_buf = std::mem::take(&mut buf);   // Step 4: take iter_buf
    POOL.with(|p| p.set(buf));                 // Step 5: return empty buf
    iter_buf
}.into_iter()
```

**Data flow:**

```
┌──────────┐   take    ┌──────────┐  clear  ┌──────┐  push   ┌──────────┐  take  ┌──────────┐
│ TLS Pool │ --------> │ buf      │ ------> │  []  │ ------> │ [v0, v1] │ ----> │ iter_buf │
│ (arb.)   │           │ (arb.)   │         │      │         │          │       │ [v0, v1] │
└──────────┘           └──────────┘         └──────┘         └──────────┘       └──────────┘
                                                                           set ↓
                                                                     ┌──────────┐
                                                                     │ TLS Pool │
                                                                     │   []     │
                                                                     └──────────┘
```

After the first call, `buf` is pre-sized and subsequent calls do zero heap allocation (only `clear` + `push` into existing capacity).

**Implementation:** `common.rs:448-482` (`generate_tls_pool_iter`).

## 3. Formal Model

The proof abstracts over terms, values, constructor kinds, and extraction.

**Definition (vec_pattern).** The original pattern models `vec![]`:

```
vec_pattern(t) :=
    match classify(t) with
    | Some k => extract_values(k, t)
    | None   => []
    end
```

**Definition (pool_pattern).** The optimized pattern models TLS pool reuse:

```
pool_pattern(pool_contents, t) :=
    let buf  := []                       (* Step 2: clear *)
    let buf' := buf ++ match classify(t) (* Step 3: push *)
                       | Some k => extract_values(k, t)
                       | None   => []
                       end
    buf'                                 (* Step 4: take iter_buf *)
```

Note: `pool_contents` is the arbitrary prior buffer contents — they are discarded by `clear`.

## 4. Theorem and Proof

**Theorem (T1: Pool Equivalence).**

> For all terms `t` and prior pool contents `pool_contents`:
>
> `pool_pattern(pool_contents, t) = vec_pattern(t)`

**Proof.** Unfold `pool_pattern` and `vec_pattern`. After the clear step, `buf = []`. Appending to `[]` is the identity on lists (`[] ++ l = l`).

Case split on `classify(t)`:

- **Case `Some k`:** Both sides reduce to `extract_values(k, t)`.

  `pool_pattern(pool_contents, t) = [] ++ extract_values(k, t) = extract_values(k, t) = vec_pattern(t)` **QED.**

- **Case `None`:** Both sides reduce to `[]`.

  `pool_pattern(pool_contents, t) = [] ++ [] = [] = vec_pattern(t)` **QED.**

**Corollary (Pool Contents Irrelevance).** For all `t`, `c1`, `c2`:

> `pool_pattern(c1, t) = pool_pattern(c2, t)`

**Proof.** By two applications of T1: both sides equal `vec_pattern(t)`. **QED.**

**Corollary (Empty Pool Special Case).** For all `t`:

> `pool_pattern([], t) = vec_pattern(t)`

**Proof.** Immediate from T1 with `pool_contents = []`. **QED.**

## 5. Concrete Instantiation

**Calculator language** (`calc_pool_equiv` in `ConcreteInstantiations.v`):

For `IntTerm` with `IntKind` classification (NumLit, Add, Sub, Mul, Div, Neg) and any extraction function, the pool pattern is equivalent to the vec pattern. This follows directly from the abstract theorem T1.

## 6. Spec-to-Code Traceability

| Rocq Definition | Rust / Ascent Code | Location |
|-----------------|-------------------|----------|
| `vec_pattern` | `vec![...]` in old subterm rules | `helpers.rs` (pre-Opt 2) |
| `pool_pattern` | `generate_tls_pool_iter` | `common.rs:448-482` |
| `classify` | match on term variant | generated match arms |
| `clear` | `buf.clear()` | `common.rs:472` |
| `push` | `buf.push(...)` | generated match arm bodies |
| `take` / `return` | `p.take()` / `p.set(buf)` | `common.rs:471`, `common.rs:478` |
| `pool_equiv` (T1) | — | `TLSPoolEquiv.v:102-114` |
| `pool_contents_irrelevant` | — | `TLSPoolEquiv.v:117-123` |
| `pool_empty_equiv` | — | `TLSPoolEquiv.v:126-131` |

## 7. Rocq Source Reference

- **File:** `formal/rocq/ascent_optimizations/theories/TLSPoolEquiv.v` (133 lines)
- **Dependencies:** `Prelude.v`
- **Section:** `TLSPoolEquivalence` (parameterized over `T`, `V`, `K`, `classify`, `extract_values`)
- **Key constructs:** `vec_pattern`, `pool_pattern`, `pool_equiv`, `pool_contents_irrelevant`, `pool_empty_equiv`
