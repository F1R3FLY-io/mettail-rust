# CEK Decomposition Bridge

## Why does this exist?

The `CekEvaluator` is a generic term-rewriting machine. It knows about
continuation frames, environments, and evaluation states -- but it does
not know the structure of any particular language's AST. The decomposition
bridge translates a language-specific AST into the evaluator's frame
vocabulary, enabling the generic CEK machine to evaluate language-specific
terms.

Without the bridge, `CekEvaluator::new("1 + 2")` treats the entire string
as an opaque control term. It transitions Ready → Reducing → Accepted in
2 steps, returning `"1 + 2"` unchanged (no frames to descend into, no
rewrite rules to apply). The bridge is what makes the evaluator aware of
the term's internal structure.

## 1. The Problem: Worked Example

Consider `CekEvaluator::new("1 + 2")` with no decomposition:

| Step | State | Control | Stack | Memo | Action |
|------|-------|---------|-------|------|--------|
| 0 | Ready | `"1 + 2"` | `[]` | `{}` | -- |
| 1 | Reducing | `"1 + 2"` | `[]` | miss `"1 + 2"` | Reduce → Accept (stack empty, no cache hit) |
| 2 | Accepted | `"1 + 2"` | `[]` | -- | Terminal |

The evaluator accepts the term as-is because it has no way to know that
`"1 + 2"` contains a binary operator with two operands. The string is
opaque.

With decomposition, the same input produces:

| Step | State | Control | Stack | Action |
|------|-------|---------|-------|--------|
| 0 | Ready | `"1 + 2"` | `[]` | decompose_into_cek pushes BinOp frame |
| -- | Reducing | `"2"` | `[BinOp(+, "1")]` | Descend into RHS |
| 1 | Reducing | `"2"` | `[BinOp(+, "1")]` | "2" is ground → Ascend |
| 2 | Reducing | `"(1 + 2)"` | `[]` | Pop BinOp, reconstruct |
| 3 | Reducing | `"(1 + 2)"` | `[]` | Cache miss, stack empty → Accept |
| 4 | Accepted | `"(1 + 2)"` | `[]` | Or: direct-eval intercepts and yields "3" |

The bridge has given the evaluator a roadmap of the term's structure.

## 2. The Solution

### 2.1 API

```rust
#[cfg(feature = "cek-runtime")]
fn decompose_into_cek(
    &self,
    term: &dyn Term,
    evaluator: &mut CekEvaluator,
) -> bool
```

**Input**: A parsed AST node and a mutable evaluator.

**Output**: `true` if the term was decomposed (frames were pushed onto the
evaluator's continuation stack); `false` if the language cannot decompose
this term shape (fallback to Ascent).

**Side effects**: Pushes `EvalFrame` variants onto `evaluator.continuation`,
sets `evaluator.control` to the innermost sub-term to evaluate first, and
transitions `evaluator.state` to `EvalState::Reducing`.

### 2.2 Decomposition Algorithm (Pseudocode)

```
decompose(term, evaluator):
    match term:
        case Literal(v):
            evaluator.set_control(display(v))
            evaluator.set_state(Reducing)

        case BinOp(op, lhs, rhs):
            evaluator.push_frame(BinOp { operator: op, lhs_display: display(lhs) })
            evaluator.set_control(display(rhs))
            evaluator.set_state(Reducing)

        case UnaryOp(op, operand):
            evaluator.push_frame(UnaryOp { operator: op })
            evaluator.set_control(display(operand))
            evaluator.set_state(Reducing)

        case Let(x, bound_expr, body):
            evaluator.push_frame(LetBody { var_name: x, body_display: display(body) })
            evaluator.set_control(display(bound_expr))
            evaluator.set_state(Reducing)

        case Par(p1, p2, ..., pn):
            evaluator.push_frame(Parallel {
                remaining: [display(p2), ..., display(pn)],
                completed: []
            })
            evaluator.set_control(display(p1))
            evaluator.set_state(Reducing)

        case Variable(name):
            evaluator.set_control(name)
            evaluator.set_state(Reducing)

        case _:
            evaluator.set_control(display(term))
            evaluator.set_state(Reducing)
```

The algorithm walks the outermost AST constructor, pushes a single frame
for the evaluation context, and focuses the control on the first sub-term
to evaluate. Recursive sub-terms are handled by the evaluator's step loop:
when it ascends from a completed sub-term, the frame's `Ascend` handler
reconstructs the compound expression and re-enters `Reducing` state.

## 3. Decomposition Rules

Formal inference rules for each AST pattern. We write `⌈t⌉` for the
display form of term `t`, `κ` for the current continuation stack, and
`c` for the control.

### 3.1 Binary Operator

```
  t = op(t₁, t₂)          infix binary operator
  ─────────────────────────────────────────────────
  κ' = κ · BinOp(op, ⌈t₁⌉),   c' = ⌈t₂⌉
```

The LHS display is captured in the frame; the evaluator focuses on the RHS.
When the RHS reaches normal form, the `Ascend` handler pops the `BinOp`
frame and reconstructs `(⌈t₁⌉ op ⌈rhs_result⌉)`.

### 3.2 Unary Operator

```
  t = op(t₁)               unary prefix operator
  ─────────────────────────────────────────────────
  κ' = κ · UnaryOp(op),    c' = ⌈t₁⌉
```

### 3.3 Let Binding

```
  t = let x = e in body
  ─────────────────────────────────────────────────
  κ' = κ · LetBody(x, ⌈body⌉),   c' = ⌈e⌉
```

When `e` evaluates to a value `v`, the `Ascend` handler binds `x → v` in
the environment and sets `c' = ⌈body⌉`.

### 3.4 Parallel Composition

```
  t = t₁ | t₂ | ... | tₙ   parallel composition
  ─────────────────────────────────────────────────
  κ' = κ · Parallel(⌈t₂⌉...⌈tₙ⌉, []),   c' = ⌈t₁⌉
```

Sub-terms are evaluated left-to-right in the single-threaded path. Each
completed sub-term is moved from `remaining` to `completed`. When all
sub-terms are evaluated, the frame reconstructs `(completed₁ | ... | completedₙ)`.

When the `green-threads` feature is enabled and the M:N runtime is active,
the evaluator may fork each sub-term as an independent green thread instead
of evaluating sequentially.

### 3.5 Match Scrutinee

```
  t = match e { arms }
  ─────────────────────────────────────────────────
  κ' = κ · MatchScrutinee(⌈arms⌉),   c' = ⌈e⌉
```

### 3.6 Rewrite Application

```
  t = rule_name(e)          named rewrite
  ─────────────────────────────────────────────────
  κ' = κ · RewriteCont(rule_name),   c' = ⌈e⌉
```

### 3.7 Literal / Variable (Base Cases)

```
  t = literal(v)            ground value
  ─────────────────────────────────────────────────
  κ' = κ,   c' = ⌈v⌉        (no frame pushed)
```

```
  t = variable(x)           free variable
  ─────────────────────────────────────────────────
  κ' = κ,   c' = x           (no frame pushed)
```

## 4. Per-Variant Table

Every `EvalFrame` variant and its corresponding AST pattern:

| EvalFrame Variant | AST Pattern | Waiting For | Ascend Action |
|------------------|-------------|-------------|---------------|
| `BinOp { operator, lhs_display }` | `op(lhs, rhs)` | RHS normal form | `c' = (lhs_display op rhs_result)` |
| `UnaryOp { operator }` | `op(operand)` | Operand normal form | `c' = (op operand_result)` |
| `MatchScrutinee { arms_display }` | `match e { arms }` | Scrutinee normal form | Pattern-match against arms |
| `LetBody { var_name, body_display }` | `let x = e in body` | Bound expression normal form | `ρ' = ρ[x → result], c' = body` |
| `Parallel { remaining, completed }` | `t₁ \| ... \| tₙ` | Current sub-term normal form | Move to next remaining or reconstruct |
| `RewriteCont { rule_name }` | `rule(e)` | RHS of rule application | Result is already the control |

## 5. Generated Code

The `language!` macro generates `decompose_into_cek` by inspecting each
`GrammarRule`'s structure at compile time. The code generator lives in
`macros/src/gen/runtime/language.rs` and dispatches to two generators:

- **`generate_cek_decompose_single`**: For single-type languages (one
  category). Downcasts the `dyn Term` to the concrete type, then matches
  on the category's enum variants.

- **`generate_cek_decompose_multi`**: For multi-type languages (multiple
  categories, wrapped in an `Inner` enum). Dispatches on the outer
  `Inner::Category(term)` variant, then matches each category's variants.

### 5.1 Code Generation Rules

For each grammar rule, the generator examines the `GrammarItem` sequence:

| GrammarItem Pattern | Frame Type | Logic |
|--------------------|-----------|-------|
| Infix rule with 2 non-terminals | `BinOp` | Capture LHS display, focus on RHS |
| Unary prefix with 1 non-terminal | `UnaryOp` | Focus on operand |
| Collection non-terminal | (no frame) | Set control to display |
| Let-like (ident + 2 non-terminals) | `LetBody` | Capture var name and body |
| Parallel composition | `Parallel` | Capture remaining sub-terms |
| Literal / no non-terminals | (no frame) | Set control to display |
| Catch-all `_` | (no frame) | Set control to display, state to Reducing |

### 5.2 Ambiguous Terms

For multi-type languages, the `Ambiguous(alts)` variant (produced by
ambiguous parses) decomposes the first alternative:

```rust
Inner::Ambiguous(alts) => {
    if let Some(first) = alts.first() {
        let sub = Term(first.clone());
        return self.decompose_into_cek(&sub, evaluator);
    }
    return false;
}
```

## 6. Failure Contract

The decomposition bridge is an explicit CEK integration point. It reports
whether a term shape was decomposed and leaves fallback policy to its caller.
Production REPL `exec` does not call this bridge before the selected runtime
backend; it asks `Language::run_default_backend_report` for a
`RuntimeBackendReport`.

### 6.1 Decomposition Returns `false`

When `decompose_into_cek` returns `false`, the term shape is not recognized
by the generated code. This happens when:

- The `dyn Term` downcast fails (wrong language type)
- The language has no CEK decomposition (default implementation returns `false`)

An explicit CEK consumer can then report "unsupported by CEK", select a
separate oracle, or stop. That policy is outside `decompose_into_cek`:

```rust
if language.decompose_into_cek(term.as_ref(), &mut evaluator) {
    // ... try run_to_completion ...
}
// Caller-owned policy for unsupported CEK decomposition.
```

### 6.2 `run_to_completion` Returns `Err`

Even after successful decomposition, the evaluator may fail:

- **Step limit exceeded**: Divergent rewrite sequence (default: 10,000 steps)
- **Observer abort**: An observer returned `CekControl::Abort`
- **Internal error**: Unexpected state transition

The error is surfaced to the explicit CEK caller. It is not a signal for the
REPL to silently fabricate an Ascent result:

```rust
match evaluator.run_to_completion(&mut obs) {
    Ok(result_str) => {
        // Parse result, display, return
    },
    Err(err) => {
        // Caller reports or handles the CEK failure explicitly.
    }
}
```

This keeps unsupported CEK coverage from being mistaken for successful
runtime-backend execution.

## 7. Integration Points

### 7.1 Environment Persistence

The `CekEvaluator` supports environment persistence across explicit CEK
sessions via `reset_with_term()`, which clears the continuation stack and trace
but preserves variable bindings and the memo cache. This enables CEK-focused
tools to model a persistent session:

```
cek> x = 5
cek> eval x + 3
CEK eval... 8
```

The ordinary REPL `exec` command instead runs the language's selected runtime
backend and stores the resulting `RuntimeBackendReport`.

### 7.2 Green Thread Fork

When the `green-threads` feature is enabled, `decompose_into_cek` for
`Parallel` frames can trigger green thread forking instead of sequential
evaluation. The `GreenThread::run_quantum()` method detects `Parallel`
frames with multiple remaining sub-terms and returns
`QuantumResult::Forked`, signaling the worker to create child threads.

## References

- Felleisen, M. & Friedman, D. P. (1986). Control operators, the SECD-machine,
  and the lambda-calculus. *Formal Description of Programming Concepts III*.
- Baader, F. & Nipkow, T. (1998). *Term Rewriting and All That*. Cambridge
  University Press.

## Source Files

| File | Content |
|------|---------|
| `prattail/src/cek_eval.rs` | `CekEvaluator`, `EvalFrame`, `EvalObserver` |
| `runtime/src/language.rs` | `Language::decompose_into_cek` trait method |
| `macros/src/gen/runtime/language.rs` | `generate_cek_decompose_single`, `generate_cek_decompose_multi` |
| `repl/src/repl.rs` | Runtime-backend report dispatch for `exec`; explicit Ascent-shaped graph stepping |
