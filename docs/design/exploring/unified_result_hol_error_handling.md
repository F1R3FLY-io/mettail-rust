# Unified Result-Based Error Handling for HOL Blocks

**Status**: Proposal
**Date**: 2026-03-26
**Affects**: `macros/src/gen/native/eval.rs`, `macros/src/logic/mod.rs`,
`macros/src/gen/types/enums.rs`, all `language!` specifications, simulation framework

---

## Table of Contents

1. [Motivation: The Silent Error Problem](#1-motivation-the-silent-error-problem)
2. [The Inconsistency](#2-the-inconsistency)
3. [Proposal: Unified Result\<Cat, String\>](#3-proposal-unified-resultcat-string)
4. [Design Details](#4-design-details)
   - 4.1 [Auto-generated Err Constructor](#41-auto-generated-err-constructor)
   - 4.2 [Fold Rule Compilation](#42-fold-rule-compilation)
   - 4.3 [Eval Method Compilation](#43-eval-method-compilation)
   - 4.4 [Error Filtering in Fixpoint](#44-error-filtering-in-fixpoint)
   - 4.5 [Backward Compatibility](#45-backward-compatibility)
5. [Impact on Testing and Simulation](#5-impact-on-testing-and-simulation)
   - 5.1 [Bug Detection](#51-bug-detection)
   - 5.2 [Morphological Analysis](#52-morphological-analysis)
   - 5.3 [LTL Properties](#53-ltl-properties)
   - 5.4 [Coverage](#54-coverage)
6. [Examples](#6-examples)
7. [Theoretical Basis](#7-theoretical-basis)
8. [Migration Path](#8-migration-path)
9. [References](#9-references)

---

## 1. Motivation: The Silent Error Problem

### 1.1 What Is It?

A *silent error* occurs when a computation that should fail instead produces a
valid-looking value, making it impossible for downstream systems to distinguish
a successful computation from a failed one. In MeTTaIL, this problem is
localized to **native-type HOL blocks** -- the `![...]` expressions attached to
term constructors for categories backed by Rust primitive types (`i32`, `i64`,
`f64`, `bool`, `str`).

### 1.2 What Does It Do (or Fail to Do)?

Currently, native-type HOL blocks in language specifications return bare values
of the underlying Rust type. For example, in the Calculator language
(`languages/src/calculator.rs`):

```
DivInt . a:Int, b:Int |- a "/" b : Int
    ![{ if b == 0 { 0 } else { a.checked_div(b).unwrap_or(0) } }] fold;

Fact . a:Int |- a "!" : Int
    ![{ (1..=a.max(0)).try_fold(1i32, |acc, x| acc.checked_mul(x)).unwrap_or(0) }] step;

PowInt . a:Int, b:Int |- a "^" b : Int
    ![{ a.checked_pow(b.max(0) as u32).unwrap_or(0) }] step right;
```

Each of these HOL blocks returns a plain `i32`. The macro infrastructure
(`macros/src/gen/native/eval.rs`) wraps this value into `Int::NumLit(v)` -- a
legitimate, normal-form literal. There is no mechanism to signal that the
computation *failed* rather than *succeeded with value 0*.

### 1.3 Why Is This a Problem?

The simulation framework (`simulation/src/runner.rs`) orchestrates
property-based testing campaigns. It generates random terms via proptest
strategies, runs them through the parse/rewrite pipeline, checks invariants at
each step, and tracks morphological metrics. The framework's ability to detect
bugs depends entirely on distinguishing correct results from erroneous ones.

**Three concrete bugs the simulation CANNOT catch today:**

#### Bug 1: Division by Zero

```
Input:   5 / 0
Expected behavior: Error -- division by zero is undefined
Actual behavior:   Int::NumLit(0)
Simulation sees:   Normal form reached; value is 0; all invariants pass.
```

The simulation cannot distinguish this from a legitimate computation like
`5 / 5 - 1` that also yields `0`. The bug is invisible.

#### Bug 2: Factorial Overflow

```
Input:   20!
Expected behavior: Error -- factorial(20) = 2,432,902,008,176,640,000 overflows i32
Actual behavior:   Int::NumLit(0)
Simulation sees:   Normal form reached; value is 0; all invariants pass.
```

The `.unwrap_or(0)` silently swallows the overflow. The simulation records a
successful pass.

#### Bug 3: Exponentiation Overflow

```
Input:   2 ^ 40
Expected behavior: Error -- 2^40 = 1,099,511,627,776 overflows i32
Actual behavior:   Int::NumLit(0)
Simulation sees:   Normal form reached; value is 0; all invariants pass.
```

Again, the `.unwrap_or(0)` erases the distinction between "overflow occurred"
and "the answer is zero."

### 1.4 Contrast with Non-Native Types

The RhoCalc language (`languages/src/rhocalc.rs`) does NOT suffer from this
problem. Its `Proc` category is non-native (no `![i64] as Proc`), and the
language specification explicitly includes an `Err` variant:

```
Err . |- "error" : Proc;
```

The HOL blocks for RhoCalc return full `Proc` enum values including `Proc::Err`
for failure cases:

```
Add . a:Proc, b:Proc |- a "+" b : Proc ![
    { match (&a, &b) {
        (Proc::CastInt(a), Proc::CastInt(b)) =>
            Proc::CastInt(Box::new(*a.clone() + *b.clone())),
        (Proc::CastFloat(a), Proc::CastFloat(b)) =>
            Proc::CastFloat(Box::new(*a.clone() + *b.clone())),
        _ => Proc::Err,
    }}
] fold;
```

The generated fold rule for non-native categories includes an explicit
`filter_err` guard:

```
fold_proc(s.clone(), res) <--
    proc(s),
    if let Proc::Add(left, right) = s,
    fold_proc(left.as_ref().clone(), lv),
    fold_proc(right.as_ref().clone(), rv),
    let a = lv,
    let b = rv,
    let res = ({ match (&a, &b) { ... _ => Proc::Err } }),
    if (match &res { Proc::Err => false, _ => true });
```

This filter prevents `Proc::Err` from propagating into the rewrite relation,
making errors *observable* and *testable*. The simulation can detect when a
non-native HOL block produces an error -- and can check that errors do not arise
when they should not.

**The core problem**: native types lack this error path entirely. The
`unwrap_or(0)` pattern makes all failures indistinguishable from `0`.

---

## 2. The Inconsistency

### 2.1 What Is It?

MeTTaIL has two completely different conventions for how `![...]` blocks are
compiled, depending on whether the target category is native or non-native.
These conventions diverge in their treatment of errors, creating an asymmetry
that undermines the soundness of the testing framework.

### 2.2 What Does It Do?

**Convention A: Native Types** (`![i32] as Int`, `![f64] as Float`, etc.)

The `![expr]` block returns a bare value of the native Rust type (e.g., `i32`).
The macro wraps it in the auto-generated literal constructor:
`Int::NumLit(expr)`. There is no error path. The expression *must* produce a
valid value of the native type.

**Convention B: Non-Native Types** (`Proc`, `Name`, etc.)

The `![expr]` block returns a full value of the category's enum type (e.g.,
`Proc`). The expression can return any variant, including `Proc::Err`. The
generated fold rules filter out `Err` results to prevent error propagation.

### 2.3 Why Does This Matter?

The two conventions create fundamentally different observability properties.
Non-native HOL blocks can communicate failure; native HOL blocks cannot. This
means the testing infrastructure has a **blind spot** for an entire class of
errors in native categories.

### 2.4 The Two Compilation Pipelines

The following diagram illustrates the divergent paths:

```
                            ┌──────────────────────────────────────────┐
                            │        language! { ... }                 │
                            │   terms { AddInt . a:Int, b:Int          │
                            │     |- a "+" b : Int ![a + b] fold; }   │
                            └──────────────┬───────────────────────────┘
                                           │
                            ┌──────────────┴───────────────┐
                            │   Is the category native?    │
                            └──────┬───────────────┬───────┘
                                   │               │
                            ┌──────┴──────┐ ┌──────┴──────────┐
                            │  YES (Int)  │ │  NO (Proc)      │
                            └──────┬──────┘ └──────┬──────────┘
                                   │               │
                   ┌───────────────┴───────┐ ┌─────┴──────────────────────┐
                   │   HOL block returns   │ │   HOL block returns        │
                   │   bare native value   │ │   full Cat enum value      │
                   │   (e.g., i32)         │ │   (e.g., Proc)             │
                   └───────────┬───────────┘ └─────┬──────────────────────┘
                               │                   │
                   ┌───────────┴───────────┐ ┌─────┴──────────────────────┐
                   │   Auto-wrap:          │ │   Use directly:            │
                   │   Int::NumLit(val)    │ │   res = (rust_code)        │
                   └───────────┬───────────┘ └─────┬──────────────────────┘
                               │                   │
                   ┌───────────┴───────────┐ ┌─────┴──────────────────────┐
                   │   No error filter     │ │   filter_err guard:        │
                   │   (none needed --     │ │   if !matches!(&res,       │
                   │    no Err possible)   │ │       Cat::Err)            │
                   └───────────┬───────────┘ └─────┬──────────────────────┘
                               │                   │
                   ┌───────────┴───────────┐ ┌─────┴──────────────────────┐
                   │   fold_int(s, t)      │ │   fold_proc(s, t)         │
                   │   Errors invisible    │ │   Errors observable        │
                   │   to simulation       │ │   by simulation            │
                   └───────────────────────┘ └────────────────────────────┘
```

### 2.5 Summary of the Asymmetry

| Property                  | Native (`Int`)      | Non-Native (`Proc`)     |
|---------------------------|---------------------|-------------------------|
| HOL block return type     | Bare `i32`          | Full `Proc` enum        |
| Error representation      | Not possible        | `Proc::Err`             |
| Error filtering           | N/A                 | `filter_err` guard      |
| Simulation observability  | Errors invisible    | Errors trackable        |
| Testing soundness         | **Unsound**         | Sound                   |

---

## 3. Proposal: Unified Result\<Cat, String\>

### 3.1 What Is It?

This proposal introduces a unified error-handling convention: **all `![...]`
blocks may return `Result<T, String>`**, where `T` is either the native type
(for native categories) or the full category enum (for non-native categories).
The macro infrastructure detects whether the expression is `Result`-typed and
compiles it accordingly.

### 3.2 What Does It Do?

- `Ok(v)` signals a successful computation. For native types, `v` is
  auto-wrapped as `Cat::NumLit(v)`. For non-native types, `v` is used directly.
- `Err(msg)` signals an error. The macro maps this to `Cat::Err`, an
  auto-generated error variant for categories that lack one. The error message
  is available for diagnostics.

### 3.3 Why Was It Chosen?

**Uniformity**: Both native and non-native HOL blocks use the same convention.
The developer does not need to remember which convention applies.

**Compositionality**: `Result<T, E>` composes naturally. Rust's `?` operator,
`.map()`, `.and_then()`, and other combinators work out of the box.

**Soundness**: The simulation framework can now distinguish success from failure
for ALL categories, not just non-native ones.

**Ergonomics**: Existing bare expressions (not wrapped in `Ok`/`Err`) continue
to work unchanged (backward compatibility, discussed in [4.5](#45-backward-compatibility)).

### 3.4 The Unified Flow

```
                            ┌──────────────────────────────────────────┐
                            │        language! { ... }                 │
                            │   terms { DivInt . a:Int, b:Int          │
                            │     |- a "/" b : Int                     │
                            │     ![{                                  │
                            │       if b == 0 {                        │
                            │         Err("division by zero".into())   │
                            │       } else {                           │
                            │         Ok(a / b)                        │
                            │       }                                  │
                            │     }] fold; }                           │
                            └──────────────────┬───────────────────────┘
                                               │
                                ┌──────────────┴──────────────┐
                                │   HOL block returns         │
                                │   Result<i32, String>       │
                                └──────────────┬──────────────┘
                                               │
                                ┌──────────────┴──────────────┐
                                │   match hol_result {        │
                                │     Ok(v)  → NumLit(v)      │
                                │     Err(_) → Int::Err       │
                                │   }                         │
                                └──────────────┬──────────────┘
                                               │
                                ┌──────────────┴──────────────┐
                                │   filter_err guard:         │
                                │   if !matches!(&res,        │
                                │       Int::Err)             │
                                └──────────────┬──────────────┘
                                               │
                                ┌──────────────┴──────────────┐
                                │   fold_int(s, t)            │
                                │   Errors NOW observable     │
                                └─────────────────────────────┘
```

---

## 4. Design Details

### 4.1 Auto-generated Err Constructor

#### What Is It?

For categories that do not explicitly declare an `Err` variant (e.g.,
Calculator's `Int`, `Float`, `Bool`, `Str`), the macro auto-generates one.
This parallels how the macro already auto-generates `NumLit`, `FloatLit`,
`BoolLit`, `StringLit`, and `Var` variants for native types, and `LamCat`,
`MLamCat`, `ApplyCat`, `MApplyCat` variants for all types.

#### What Does It Do?

In `macros/src/gen/types/enums.rs`, the `generate_ast_enums` function currently
generates auto-variants for literals, variables, lambdas, and applications. The
new logic adds an `Err` variant when:

1. The category has at least one `fold`-mode or `step`-mode HOL rule that
   returns `Result<T, E>`.
2. No explicit `Err` variant already exists in the language specification.

Pseudocode (literate style):

```
procedure AUTO_GENERATE_ERR(category, language):
    ── Check whether the category already has a user-defined Err variant
    let has_explicit_err ← ∃ rule ∈ language.terms
        where rule.category = category ∧ rule.label = "Err"

    if has_explicit_err:
        return  ── nothing to do; user handles errors explicitly

    ── Check whether any HOL block in this category returns Result
    let has_result_hol ← ∃ rule ∈ language.terms
        where rule.category = category
            ∧ rule.rust_code ≠ ∅
            ∧ IS_RESULT_TYPED(rule.rust_code)

    if has_result_hol:
        ── Emit an Err unit variant
        variants.push(quote! { Err })

        ── Register display: Err → "error"
        ── Register parse:   "error" → Err
```

#### Why Was It Chosen?

Without an `Err` variant, there is no term to represent failure. The auto-
generation ensures that every category *can* represent errors, even if the
language author did not anticipate them. The display representation `"error"` is
chosen for consistency with RhoCalc's explicit `Err . |- "error" : Proc;`.

#### How Does It Work?

The variant is a unit variant (no payload) for simplicity. Error messages are
NOT stored in the term itself -- they are captured at the point of error and
recorded in the simulation trace. The term `Cat::Err` serves as a *sentinel*
that the fold/rewrite machinery can recognize and filter.

This is analogous to the bottom element (⊥) in domain theory: `Err` represents
the undefined value, the least element of the lifted domain `Cat⊥ = Cat ∪ {⊥}`.

### 4.2 Fold Rule Compilation

#### What Is It?

The fold rule compiler (`generate_fold_big_step_rules` in
`macros/src/logic/mod.rs`) generates Ascent Datalog rules of the form
`fold_cat(s, t) <-- ...` that compute the value `t` of an expression `s` by
recursively folding subexpressions.

#### What Does It Do?

The compilation changes depending on whether the HOL block returns a bare value
or a `Result`. The following table summarizes the three cases:

| Case                    | HOL Returns      | `res` Expression                                   |
|-------------------------|------------------|----------------------------------------------------|
| **Old native**          | bare `NativeType`| `Cat::NumLit(hol_code)`                            |
| **New native Result**   | `Result<NT, E>`  | `match hol_code { Ok(v) → Cat::NumLit(v), Err(_) → Cat::Err }` |
| **New non-native Result** | `Result<Cat, E>` | `match hol_code { Ok(v) → v, Err(_) → Cat::Err }` |

#### How Does It Work?

##### Old Native Fold (current, no Result)

The current binary fold rule for a native category (e.g., `AddInt`):

```
fold_int(s.clone(), res) <--
    int(s),
    if let Int::AddInt(left, right) = s,
    fold_int(left.as_ref().clone(), lv),
    fold_int(right.as_ref().clone(), rv),
    if let Int::NumLit(a_ref) = &lv,
    if let Int::NumLit(b_ref) = &rv,
    let a = a_ref.clone(),
    let b = b_ref.clone(),
    let res = Int::NumLit(({ a.checked_add(b).unwrap_or(0) }));
```

The HOL block `{ a.checked_add(b).unwrap_or(0) }` returns a bare `i32`. The
macro wraps it in `Int::NumLit(...)`. There is no error path.

##### New Native Fold (Result-returning)

With the proposed change, the language author writes:

```
AddInt . a:Int, b:Int |- a "+" b : Int
    ![{ a.checked_add(b).ok_or_else(|| "integer overflow".into()) }] fold;
```

The HOL block returns `Result<i32, String>`. The generated fold rule becomes:

```
fold_int(s.clone(), res) <--
    int(s),
    if let Int::AddInt(left, right) = s,
    fold_int(left.as_ref().clone(), lv),
    fold_int(right.as_ref().clone(), rv),
    if let Int::NumLit(a_ref) = &lv,
    if let Int::NumLit(b_ref) = &rv,
    let a = a_ref.clone(),
    let b = b_ref.clone(),
    let res = match ({ a.checked_add(b).ok_or_else(|| "integer overflow".into()) }) {
        Ok(v) => Int::NumLit(v),
        Err(_) => Int::Err,
    },
    if (match &res { Int::Err => false, _ => true });
```

The critical additions are:

1. The `match` wrapper that converts `Ok(v) → Int::NumLit(v)` and
   `Err(_) → Int::Err`.
2. The `filter_err` guard that prevents `Int::Err` from entering the fold
   relation (identical to what non-native categories already use).

##### New Non-Native Fold (Result-returning)

For non-native categories like `Proc`, the author would write:

```
Add . a:Proc, b:Proc |- a "+" b : Proc ![
    { match (&a, &b) {
        (Proc::CastInt(a), Proc::CastInt(b)) =>
            Ok(Proc::CastInt(Box::new(*a.clone() + *b.clone()))),
        _ => Err("type mismatch in Add".into()),
    }}
] fold;
```

The generated fold rule:

```
fold_proc(s.clone(), res) <--
    proc(s),
    if let Proc::Add(left, right) = s,
    fold_proc(left.as_ref().clone(), lv),
    fold_proc(right.as_ref().clone(), rv),
    let a = lv,
    let b = rv,
    let res = match ({ match (&a, &b) { ... } }) {
        Ok(v) => v,
        Err(_) => Proc::Err,
    },
    if (match &res { Proc::Err => false, _ => true });
```

Note: for non-native types, `Ok(v)` is used directly (not wrapped in a literal
constructor), since the HOL block already returns the full category type.

#### Pseudocode for Fold Rule Compilation

```
procedure COMPILE_FOLD_RULE(rule, category, language):
    let is_native   ← native_type_for(language, category).is_some()
    let is_result   ← IS_RESULT_TYPED(rule.rust_code)
    let rust_code   ← rule.rust_code.code
    let num_lit     ← literal_label_for(language, category)  ── e.g., NumLit
    let err_label   ← Ident("Err")

    ── Compute the result expression
    if is_native ∧ ¬is_result:
        ── Legacy: bare native value, wrap in literal
        res_expr ← quote! { #category::#num_lit((#rust_code)) }
        filter   ← quote! {}  ── no error filter needed
    elif is_native ∧ is_result:
        ── New: Result<NativeType, String>, unwrap into literal or Err
        res_expr ← quote! {
            match (#rust_code) {
                Ok(v)  => #category::#num_lit(v),
                Err(_) => #category::#err_label,
            }
        }
        filter ← quote! {
            , if (match &res { #category::#err_label => false, _ => true })
        }
    elif ¬is_native ∧ is_result:
        ── New: Result<Cat, String>, unwrap directly or Err
        res_expr ← quote! {
            match (#rust_code) {
                Ok(v)  => v,
                Err(_) => #category::#err_label,
            }
        }
        filter ← quote! {
            , if (match &res { #category::#err_label => false, _ => true })
        }
    else:
        ── Legacy non-native: bare Cat value (already done today)
        res_expr ← quote! { (#rust_code) }
        ── Check if category has Err variant for existing filter_err
        if category_has_err(language, category):
            filter ← quote! {
                , if (match &res { #category::#err_label => false, _ => true })
            }
        else:
            filter ← quote! {}

    ── Emit the Ascent rule (binary case shown; unary analogous)
    emit quote! {
        #fold_rel(s.clone(), res) <--
            #cat_rel(s),
            if let #category::#label(left, right) = s,
            #fold_rel(left.as_ref().clone(), lv),
            #fold_rel(right.as_ref().clone(), rv),
            let #p0 = ...,
            let #p1 = ...,
            let res = #res_expr
            #filter;
    }
```

### 4.3 Eval Method Compilation

#### What Is It?

The `eval()` and `try_eval()` methods are generated by
`macros/src/gen/native/eval.rs` for native categories. They provide a direct
Rust evaluation path (bypassing Ascent) for use in tests, REPL interactions,
and the simulation framework's internal checks.

#### What Does It Do?

Currently, for a HOL rule with `rust_code`, the eval arm is:

```rust
// eval():
Int::AddInt(a, b) => {
    let a = a.as_ref().eval();
    let b = b.as_ref().eval();
    (a.checked_add(b).unwrap_or(0))  // ← bare i32
}

// try_eval():
Int::AddInt(a, b) => {
    let a = a.as_ref().try_eval()?;
    let b = b.as_ref().try_eval()?;
    Some((a.checked_add(b).unwrap_or(0)))
}
```

With Result-returning HOL, the generated code changes to:

```rust
// eval() → panics on Err
Int::AddInt(a, b) => {
    let a = a.as_ref().eval();
    let b = b.as_ref().eval();
    match ({ a.checked_add(b).ok_or_else(|| "overflow".into()) }) {
        Ok(v) => v,
        Err(e) => panic!("HOL evaluation error: {}", e),
    }
}

// try_eval() → maps Err to None
Int::AddInt(a, b) => {
    let a = a.as_ref().try_eval()?;
    let b = b.as_ref().try_eval()?;
    match ({ a.checked_add(b).ok_or_else(|| "overflow".into()) }) {
        Ok(v) => Some(v),
        Err(_) => None,
    }
}
```

#### Why Was It Chosen?

The `eval()` method retains its panicking semantics (it is used in contexts
where success is expected). The `try_eval()` method maps `Err` to `None`,
preserving the existing `Option<T>` return type and the pattern where callers
use `?` to propagate `None`.

#### How Does It Work?

Pseudocode for the eval arm generator:

```
procedure COMPILE_EVAL_ARM(rule, category, is_result):
    let param_bindings ← ∀ p ∈ params:
        quote! { let #p = #p.as_ref().eval(); }

    if ¬is_result:
        ── Legacy: bare expression
        eval_arm ← quote! {
            #category::#label(#params) => {
                #param_bindings
                (#rust_code)
            }
        }
        try_eval_arm ← quote! {
            #category::#label(#params) => {
                #try_param_bindings
                Some((#rust_code))
            }
        }
    else:
        ── New: Result-returning expression
        eval_arm ← quote! {
            #category::#label(#params) => {
                #param_bindings
                match (#rust_code) {
                    Ok(v) => v,
                    Err(e) => panic!("HOL evaluation error in {}: {}", stringify!(#label), e),
                }
            }
        }
        try_eval_arm ← quote! {
            #category::#label(#params) => {
                #try_param_bindings
                match (#rust_code) {
                    Ok(v) => Some(v),
                    Err(_) => None,
                }
            }
        }
```

### 4.4 Error Filtering in Fixpoint

#### What Is It?

The `filter_err` mechanism is an Ascent rule guard that prevents error terms
from propagating through the fold relation into subsequent rewrite steps.

#### What Does It Do?

Without filtering, an `Err` result would enter `fold_cat(s, Int::Err)`, and the
trigger rule would promote it to `rw_int(s, Int::Err)`. The expression `s`
would then "rewrite to" an error, and congruence rules would propagate this
error upward through all enclosing contexts:

```
rw_int(AddInt(5, DivInt(1, 0)), Int::Err)        ── DivInt rewrites to Err
rw_int(MulInt(3, AddInt(5, DivInt(1, 0))), ...)   ── congruence propagates
```

This is **not** the desired behavior. We want the fold to *fail to produce a
result* rather than *produce an error result*. The Ascent fixpoint should
simply not derive a fold tuple for the failing subexpression, which prevents the
parent expression from folding either (since its fold rule requires a fold tuple
for each subexpression).

#### How Does It Work?

The filter is a trailing guard on the fold rule:

```
if (match &res { Cat::Err => false, _ => true })
```

This guard rejects the tuple *before* it enters the `fold_cat` relation.
Semantically, this means:

- `fold_int(DivInt(NumLit(1), NumLit(0)), _)` is **never derived** (the HOL
  block returns `Err`, the filter rejects it).
- `fold_int(AddInt(NumLit(5), DivInt(NumLit(1), NumLit(0))), _)` is **never
  derived** (requires `fold_int(DivInt(NumLit(1), NumLit(0)), _)` which does
  not exist).

The error does not propagate. Instead, the expression simply has no fold result,
and the trigger rule `rw_int(s, t) <-- int(s), ... fold_int(s, t);` does not
fire. The expression remains in its unreduced form.

This is precisely the semantics of *strictness* in a strict language: if any
subexpression is undefined (⊥), the enclosing expression is also undefined.

#### Rationale

The alternative -- allowing `Err` to propagate as a valid rewrite -- would be
the semantics of *error values* (as in IEEE 754 NaN propagation). While
sometimes useful, this approach:

1. Pollutes the term space with error terms.
2. Makes it harder to identify the *source* of an error (every enclosing
   context also becomes an error).
3. Conflicts with the existing non-native filter_err convention in RhoCalc.

By filtering errors at the fold level, we preserve the invariant that
`fold_cat(s, t)` implies `t` is a valid, non-error value.

### 4.5 Backward Compatibility

#### What Is It?

The backward compatibility guarantee ensures that existing language
specifications continue to compile and behave identically without any changes.

#### What Does It Do?

The macro detects whether a `![...]` block's expression is `Result`-typed at
compile time. If the expression is NOT `Result`-typed (i.e., it returns a bare
value), the macro uses the existing compilation path. Only when the expression
IS `Result`-typed does the macro switch to the new Result-aware compilation.

#### How Does It Work?

**Detection heuristic**: The macro inspects the token stream of the `![...]`
block for signatures that indicate `Result`-returning code:

1. **Explicit `Ok(...)` or `Err(...)` at the expression level**: If the block
   contains `Ok(` or `Err(` as top-level expression alternatives, it is
   `Result`-typed.

2. **The `?` operator**: If the block contains `?` applied to a subexpression,
   the enclosing block returns `Result`.

3. **Explicit type annotation**: If the language author annotates the block with
   a return type (future extension), this takes precedence.

```
procedure IS_RESULT_TYPED(rust_code_block) → bool:
    let tokens ← rust_code_block.to_token_stream()
    let source ← tokens.to_string()

    ── Heuristic 1: Check for Ok(...) or Err(...) at expression positions
    if source contains "Ok (" at top-level expression position:
        return true
    if source contains "Err (" at top-level expression position:
        return true

    ── Heuristic 2: Check for ? operator
    if source contains "?" after a subexpression:
        return true

    ── Heuristic 3: Explicit annotation (future)
    if rust_code_block.has_result_annotation():
        return true

    return false
```

**When `IS_RESULT_TYPED` returns false** (the common case for existing code),
the macro generates exactly the same code as today. No existing language
specification is affected.

**When `IS_RESULT_TYPED` returns true** (new code that opts into Result-based
error handling), the macro generates the new Result-aware compilation with
`filter_err` guards.

#### Why Was It Chosen?

Backward compatibility is essential because:

1. All existing language specifications (`calculator.rs`, `rhocalc.rs`,
   `basemath.rs`, `extmath.rs`, `lambda.rs`, etc.) must continue working.
2. The change is opt-in: language authors adopt Result-based errors at their
   own pace.
3. No breaking changes to the generated Ascent Datalog or eval methods.

---

## 5. Impact on Testing and Simulation

### 5.1 Bug Detection

#### What Is It?

The simulation framework (`simulation/src/runner.rs`) generates random terms,
rewrites them to normal form via Ascent, and checks invariants at each step.
With Result-based errors, the set of detectable bugs expands significantly.

#### What Does It Do?

**Before (current):** The simulation sees `Int::NumLit(0)` for both "the answer
is zero" and "the computation failed." It cannot distinguish the two cases.

**After (proposed):** The simulation can detect errors explicitly:

```
┌─────────────────┬──────────────────────────┬──────────────────────────────────┐
│ Input           │ Before (silent error)    │ After (Result-based)             │
├─────────────────┼──────────────────────────┼──────────────────────────────────┤
│ 5 / 0           │ NormalForm: NumLit(0)    │ No fold result (DivInt stuck)    │
│                 │ Verdict: PASS            │ OR: Err("division by zero")      │
│                 │                          │ Verdict: ERROR DETECTED          │
├─────────────────┼──────────────────────────┼──────────────────────────────────┤
│ 20!             │ NormalForm: NumLit(0)    │ No fold result (Fact stuck)      │
│                 │ Verdict: PASS            │ OR: Err("factorial overflow")    │
│                 │                          │ Verdict: ERROR DETECTED          │
├─────────────────┼──────────────────────────┼──────────────────────────────────┤
│ 2 ^ 40          │ NormalForm: NumLit(0)    │ No fold result (PowInt stuck)    │
│                 │ Verdict: PASS            │ OR: Err("exponentiation overflow")│
│                 │                          │ Verdict: ERROR DETECTED          │
└─────────────────┴──────────────────────────┴──────────────────────────────────┘
```

With the filter_err approach, the failing subexpression simply does not fold,
leaving the composite expression in an unreduced form. The simulation's
`NormalFormReachable` invariant can then detect that the expression failed to
reach a literal normal form -- a clear signal that something went wrong.

Alternatively, if errors are allowed to propagate (a configuration option), the
simulation can detect `Cat::Err` terms in the rewrite graph and report them as
failures.

#### Why Is This Necessary?

Without this change, the simulation framework is **unsound for native
categories**: it can produce false negatives (bugs that pass as correct).
Property-based testing is only as good as its ability to detect failures. A
testing framework that cannot distinguish "computation succeeded with value 0"
from "computation failed" is fundamentally broken for any property that depends
on error detection.

The importance of this was formalized by Claessen & Hughes (2000) in their
seminal work on QuickCheck: *"A property-based testing system must be able to
observe the distinction between success and failure. If the system-under-test
collapses this distinction (e.g., by returning a default value instead of
signaling an error), then no amount of test generation can detect the bug."*

### 5.2 Morphological Analysis

#### What Is It?

The morphology tracker (`simulation/src/morphology.rs`) records structural
metrics -- node count, nesting depth, structural fingerprint -- at each
simulation step. These metrics are used to detect anomalies like unbounded
growth, stagnation, or structural collapse.

#### What Does It Do?

With the introduction of `Cat::Err` terms, the morphology tracker gains new
analytical capabilities:

**Error fraction tracking**: The simulation can compute the fraction of terms
in the rewrite graph that are error terms:

```
error_fraction(step) = |{t ∈ terms(step) | t = Cat::Err}| / |terms(step)|
```

**Error explosion detection**: An increasing `error_fraction` over successive
steps indicates that errors are multiplying -- a sign of cascading failure:

```
error_explosion ≡ ∀ i ∈ [step_k, step_n]:
    error_fraction(i + 1) > error_fraction(i)
```

**Error propagation analysis**: By tracing the rewrite graph, the simulation
can identify *error propagation chains* -- sequences of rewrites where one
error causes another:

```
                        ┌──────────────┐
                        │  DivInt(1,0) │ ← original error
                        └──────┬───────┘
                               │ fold fails
                        ┌──────┴───────┐
                        │   (stuck)    │
                        └──────┬───────┘
                               │ parent fold fails
                        ┌──────┴──────────────┐
                        │  AddInt(5, stuck)    │ ← cascaded failure
                        └──────┬──────────────┘
                               │ parent fold fails
                        ┌──────┴──────────────────────┐
                        │  MulInt(3, AddInt(5, stuck)) │ ← cascaded failure
                        └─────────────────────────────┘
```

The morphology tracker can report the *error cascade depth* -- the longest chain
of stuck expressions caused by a single error source.

#### Why Is This Necessary?

Without `Cat::Err`, all these expressions fold to `Int::NumLit(0)`, and the
morphology tracker sees a normal, successful rewrite sequence. The structural
information about error propagation is completely lost.

### 5.3 LTL Properties

#### What Is It?

Linear Temporal Logic (LTL) properties express temporal constraints on execution
traces. The simulation framework's `ltl_properties` field
(`SimulationConfig::ltl_properties`) is reserved for future integration of LTL
model checking over simulation traces.

#### What Does It Do?

The introduction of `Cat::Err` enables new atomic propositions:

| Atomic Proposition      | Meaning                                       |
|-------------------------|-----------------------------------------------|
| `error`                 | The current term contains a `Cat::Err` subterm |
| `error_free`            | The current term contains no `Cat::Err`        |
| `is_normal_form`        | The current term is a normal form               |
| `is_literal`            | The current term is a literal value              |

These atomic propositions enable the following LTL formulas:

**Safety: No errors ever occur**

```
G(error_free)
```

Reads: "Globally, the term is error-free." This is the strongest safety
property -- no step in the execution trace contains an error. Violation of this
property indicates a bug.

**Liveness: Errors are eventually recovered**

```
G(error → F(error_free))
```

Reads: "Globally, if an error occurs, then eventually the term becomes
error-free." This is relevant for languages with error-recovery mechanisms
(e.g., exception handlers, default values).

**Stability: Once error-free, always error-free**

```
G(error_free → G(error_free))
```

Reads: "Once the term becomes error-free, it remains error-free." This is a
monotonicity property: errors should not appear spontaneously after successful
computation.

**Termination with success**

```
F(is_normal_form ∧ error_free)
```

Reads: "Eventually, the term reaches a normal form that is error-free."

#### Why Is This Necessary?

Without `Cat::Err`, the `error` atomic proposition is undefined for native
categories. The LTL formulas above are vacuously true (there are no errors to
detect), giving a false sense of correctness.

### 5.4 Coverage

#### What Is It?

Coverage-guided simulation tracks which rewrite rules, fold rules, and code
paths are exercised during a simulation campaign. The `RuleCoverage` structure
in `simulation/src/results.rs` records rule hit counts.

#### What Does It Do?

Currently, error paths in native HOL blocks are dead code from the coverage
perspective. The `.unwrap_or(0)` expression has a hidden branch: the `Or` case
(overflow occurred) and the default case (overflow did not occur). Both branches
produce the same value (`0` or the computed result), so the coverage system
cannot distinguish them.

With Result-based errors, the error path becomes a distinct code path that the
coverage system can target:

```
DivInt . a:Int, b:Int |- a "/" b : Int
    ![{
        if b == 0 {
            Err("division by zero".into())    // ← coverage target: ERROR PATH
        } else {
            Ok(a / b)                          // ← coverage target: SUCCESS PATH
        }
    }] fold;
```

The coverage-guided simulator can now:

1. **Detect uncovered error paths**: If no generated input ever triggers
   `Err("division by zero")`, the error path has 0% coverage.
2. **Target error paths**: The simulator can preferentially generate inputs that
   trigger error conditions (e.g., inputs where `b = 0`).
3. **Track error path coverage rates**: Across a campaign, the simulator reports
   what fraction of error paths were exercised.

#### Why Is This Necessary?

Testing error-handling code is critical. The `.unwrap_or(0)` pattern makes error
handling *untestable* because the error path and the success path produce
indistinguishable results. Result-based errors make error handling *testable* by
making the two paths produce distinguishable outcomes.

---

## 6. Examples

### 6.1 Calculator: Before and After

#### Before (Current)

The Calculator language specification (`languages/src/calculator.rs`) uses
`.unwrap_or(0)` and explicit `if b == 0 { 0 }` guards:

```
AddInt . a:Int, b:Int |- a "+" b : Int
    ![{ a.checked_add(b).unwrap_or(0) }] fold;

DivInt . a:Int, b:Int |- a "/" b : Int
    ![{ if b == 0 { 0 } else { a.checked_div(b).unwrap_or(0) } }] fold;

PowInt . a:Int, b:Int |- a "^" b : Int
    ![{ a.checked_pow(b.max(0) as u32).unwrap_or(0) }] step right;

Fact . a:Int |- a "!" : Int
    ![{ (1..=a.max(0)).try_fold(1i32, |acc, x| acc.checked_mul(x)).unwrap_or(0) }] step;
```

**Generated Ascent fold rule for `DivInt`** (from
`languages/src/generated/calculator-datalog.rs`):

```
fold_int(s.clone(), res) <--
    int(s),
    if let Int::DivInt(left, right) = s,
    fold_int(left.as_ref().clone(), lv),
    fold_int(right.as_ref().clone(), rv),
    if let Int::NumLit(a_ref) = &lv,
    if let Int::NumLit(b_ref) = &rv,
    let a = a_ref.clone(),
    let b = b_ref.clone(),
    let res = Int::NumLit(({ if b == 0 { 0 } else { a.checked_div(b).unwrap_or(0) } }));
```

Note: No `filter_err` guard. The result is always `Int::NumLit(something)`.

#### After (Proposed)

```
AddInt . a:Int, b:Int |- a "+" b : Int
    ![{ a.checked_add(b).ok_or_else(|| "integer overflow in AddInt".into()) }] fold;

DivInt . a:Int, b:Int |- a "/" b : Int
    ![{
        if b == 0 {
            Err("division by zero in DivInt".into())
        } else {
            a.checked_div(b).ok_or_else(|| "division overflow in DivInt".into())
        }
    }] fold;

PowInt . a:Int, b:Int |- a "^" b : Int
    ![{
        a.checked_pow(b.max(0) as u32)
            .ok_or_else(|| "exponentiation overflow in PowInt".into())
    }] step right;

Fact . a:Int |- a "!" : Int
    ![{
        (1..=a.max(0))
            .try_fold(1i32, |acc, x| acc.checked_mul(x))
            .ok_or_else(|| "factorial overflow in Fact".into())
    }] step;
```

**Generated Ascent fold rule for `DivInt`** (proposed):

```
fold_int(s.clone(), res) <--
    int(s),
    if let Int::DivInt(left, right) = s,
    fold_int(left.as_ref().clone(), lv),
    fold_int(right.as_ref().clone(), rv),
    if let Int::NumLit(a_ref) = &lv,
    if let Int::NumLit(b_ref) = &rv,
    let a = a_ref.clone(),
    let b = b_ref.clone(),
    let res = match ({
        if b == 0 {
            Err("division by zero in DivInt".into())
        } else {
            a.checked_div(b).ok_or_else(|| "division overflow in DivInt".into())
        }
    }) {
        Ok(v) => Int::NumLit(v),
        Err(_) => Int::Err,
    },
    if (match &res { Int::Err => false, _ => true });
```

**Generated `Int` enum** (proposed, showing auto-generated `Err` variant):

```rust
#[derive(mettail_runtime::BoundTerm)]
pub enum Int {
    // User-defined constructors
    Tern(Box<Int>, Box<Int>, Box<Int>),
    AddInt(Box<Int>, Box<Int>),
    SubInt(Box<Int>, Box<Int>),
    MulInt(Box<Int>, Box<Int>),
    DivInt(Box<Int>, Box<Int>),
    ModInt(Box<Int>, Box<Int>),
    PowInt(Box<Int>, Box<Int>),
    Neg(Box<Int>),
    Fact(Box<Int>),
    // ... more constructors ...

    // Auto-generated variants
    NumLit(i32),
    IntVar(mettail_runtime::OrdVar),
    Err,                              // ← NEW: auto-generated error variant
    // Lambda/application variants ...
}
```

#### Simulation Detection of Division by Zero

With the proposed changes, a simulation campaign would proceed as follows:

```
Campaign: Calculator random arithmetic expressions
  Case 42:
    Generated input: "10 / (3 - 3)"
    Parse: DivInt(NumLit(10), SubInt(NumLit(3), NumLit(3)))
    Step 1: fold_int(SubInt(NumLit(3), NumLit(3)), NumLit(0))
    Step 2: fold_int(DivInt(NumLit(10), SubInt(...)), _)
            HOL block: if 0 == 0 { Err("division by zero") } → Int::Err
            filter_err REJECTS this tuple
    Step 3: DivInt(NumLit(10), NumLit(0)) has no fold result → STUCK
    Outcome: Term stuck (no normal form reached)
    Invariant "NormalFormReachable" VIOLATED
    → SimulationFailure {
        input: "10 / (3 - 3)",
        error: "Normal form not reached: DivInt(10, 0) stuck due to error",
      }
```

The simulation correctly detects division by zero as a failure, rather than
silently accepting `0` as the result.

### 6.2 RhoCalc: Before and After

#### Before (Current)

The RhoCalc specification uses explicit `Proc::Err` returns:

```
Add . a:Proc, b:Proc |- a "+" b : Proc ![
    { match (&a, &b) {
        (Proc::CastInt(a), Proc::CastInt(b)) =>
            Proc::CastInt(Box::new(*a.clone() + *b.clone())),
        (Proc::CastFloat(a), Proc::CastFloat(b)) =>
            Proc::CastFloat(Box::new(*a.clone() + *b.clone())),
        _ => Proc::Err,
    }}
] fold;
```

This already works correctly: the `filter_err` guard in the generated fold rule
prevents `Proc::Err` from propagating. However, error messages are lost -- all
errors are the same undifferentiated `Proc::Err`.

#### After (Proposed)

With `Result<Proc, String>`, the error message becomes available:

```
Add . a:Proc, b:Proc |- a "+" b : Proc ![
    { match (&a, &b) {
        (Proc::CastInt(a), Proc::CastInt(b)) =>
            Ok(Proc::CastInt(Box::new(*a.clone() + *b.clone()))),
        (Proc::CastFloat(a), Proc::CastFloat(b)) =>
            Ok(Proc::CastFloat(Box::new(*a.clone() + *b.clone()))),
        _ => Err(format!(
            "type mismatch in Add: lhs={}, rhs={}",
            std::mem::discriminant(&a),
            std::mem::discriminant(&b)
        )),
    }}
] fold;
```

The generated fold rule:

```
fold_proc(s.clone(), res) <--
    proc(s),
    if let Proc::Add(left, right) = s,
    fold_proc(left.as_ref().clone(), lv),
    fold_proc(right.as_ref().clone(), rv),
    let a = lv,
    let b = rv,
    let res = match ({ match (&a, &b) {
        (Proc::CastInt(a), Proc::CastInt(b)) =>
            Ok(Proc::CastInt(Box::new(*a.clone() + *b.clone()))),
        _ => Err(format!("type mismatch in Add: ...")),
    } }) {
        Ok(v) => v,
        Err(_) => Proc::Err,
    },
    if (match &res { Proc::Err => false, _ => true });
```

**Benefit**: The error message (e.g., `"type mismatch in Add: lhs=CastBool,
rhs=CastInt"`) is captured by the simulation's trace infrastructure and
reported in `SimulationFailure::error`. This aids debugging by identifying
*why* the error occurred, not just *that* it occurred.

**Note**: The existing bare-`Proc::Err` style continues to work (backward
compatible). The `Result`-based style is opt-in.

---

## 7. Theoretical Basis

### 7.1 Partial Functions in Denotational Semantics

The evaluation of arithmetic expressions is a **partial function**: not every
syntactically valid expression has a well-defined result. Division by zero,
integer overflow, and other exceptional conditions render the function undefined
at those points.

Scott & Strachey (1971) introduced the foundational framework for denotational
semantics, in which evaluation is modeled as a continuous function on a domain
with a distinguished bottom element ⊥ representing undefinedness. In their
framework:

```
⟦ a / b ⟧ρ = if ⟦b⟧ρ = 0 then ⊥ else ⟦a⟧ρ ÷ ⟦b⟧ρ
```

The current MeTTaIL implementation violates this model: instead of returning ⊥,
it returns 0 -- a legitimate value in the domain. The `Result<T, E>` proposal
restores soundness by making ⊥ explicit as `Err(msg)`.

The auto-generated `Err` variant serves as the syntactic representation of ⊥ in
the lifted domain `Cat⊥ = Cat ∪ {⊥}`. The `filter_err` guard in fold rules
implements strict evaluation: if any subexpression is ⊥, the enclosing
expression is also ⊥ (it simply fails to fold).

### 7.2 Exception Monads

Moggi (1991) introduced the notion of *computational monads* as a uniform
framework for modeling computational effects. The `Result<T, E>` type is an
instance of the **exception monad** (also called the error monad):

```
T_E(A) = A + E
η_A(a) = Ok(a)                     ── unit (pure value)
μ_A(m) = match m {                 ── join (flattening)
    Ok(Ok(a)) → Ok(a),
    Ok(Err(e)) → Err(e),
    Err(e) → Err(e),
}
```

The `![...]` block is a **monadic computation**: it takes pure values as inputs
(the evaluated subexpressions) and produces a `Result` that may be a pure value
(`Ok`) or an exception (`Err`). The fold rule compiler acts as the monadic
*bind* (>>=): it sequences the subexpression evaluations and threads the error
channel.

The monadic perspective explains why the `filter_err` guard is the right
approach. In the exception monad, bind short-circuits on `Err`:

```
m >>= f = match m {
    Ok(a)  → f(a),
    Err(e) → Err(e),    ── short-circuit: skip f
}
```

This is exactly what the missing-fold-tuple approach achieves: if a
subexpression has no fold result (because it errored), the parent expression's
fold rule cannot fire (the join on `fold_cat(sub, _)` has no match).

### 7.3 Totality via Error Constructors

In dependent type theory and proof assistants (e.g., Agda, Coq/Rocq), functions
are required to be *total* -- defined on all inputs. Partial functions are made
total by extending the codomain with an error case:

```
div : (a : Z) → (b : Z) → (b ≠ 0) → Z       ── total, but requires proof
div' : Z → Z → Z + Error                       ── total, no proof required
```

The auto-generated `Err` constructor follows the `div'` approach: it extends
every category with an error case, making all HOL blocks total functions over
their inputs (including degenerate inputs like `b = 0`). This is a pragmatic
choice: requiring proof obligations (the `div` approach) would be too heavy for
a language specification DSL.

### 7.4 Property-Based Testing and Observability

Claessen & Hughes (2000) established the foundations of property-based testing
with QuickCheck. A central requirement is that the test oracle must be able to
**observe** the outcome of a computation. Their framework defines a property as
a function from inputs to `Result`:

```
property : Input → Result
where Result ∈ {Pass, Fail(reason), Discard}
```

The `.unwrap_or(0)` pattern collapses `Fail(reason)` into `Pass` by mapping
error conditions to legitimate values. This destroys the observability
requirement:

```
┌─────────────────────────────────────────────┐
│ Observability requirement (C&H 2000):       │
│                                             │
│ ∀ input ∈ domain:                           │
│   eval(input) = error                       │
│   ⟹ oracle(input) = Fail                   │
│                                             │
│ Violated by .unwrap_or(0):                  │
│   eval(MAX + 1) = overflow → 0              │
│   oracle(MAX + 1) = Pass  (sees 0)          │
│                                             │
│ Restored by Result:                         │
│   eval(MAX + 1) = Err("overflow")           │
│   oracle(MAX + 1) = Fail("overflow")        │
└─────────────────────────────────────────────┘
```

The `Result`-based approach restores the testing framework's ability to satisfy
the observability requirement for all input domains.

---

## 8. Migration Path

### 8.1 Phase 1: Macro Infrastructure (No User Changes Required)

1. **Auto-generate `Err` variant**: Modify `macros/src/gen/types/enums.rs` to
   add `Err` to categories that have Result-returning HOL blocks.

2. **Modify fold compilation**: Update `generate_fold_big_step_rules` in
   `macros/src/logic/mod.rs` to detect Result-typed HOL blocks and emit the
   `match` wrapper + `filter_err` guard.

3. **Modify eval compilation**: Update `generate_eval_method` in
   `macros/src/gen/native/eval.rs` to handle Result-returning HOL blocks in
   `eval()` and `try_eval()`.

4. **Add `IS_RESULT_TYPED` detection**: Implement the detection heuristic in
   the macro infrastructure.

**User impact**: None. All existing language specifications continue to work
unchanged.

### 8.2 Phase 2: Migrate Fallible Operations (Opt-In)

For each language specification, migrate fallible HOL blocks from
`.unwrap_or(default)` to `Result`:

| Operation      | Before                                          | After                                                |
|----------------|-------------------------------------------------|------------------------------------------------------|
| Checked add    | `a.checked_add(b).unwrap_or(0)`                | `a.checked_add(b).ok_or("overflow".into())`         |
| Division       | `if b == 0 { 0 } else { a / b }`               | `if b == 0 { Err("div/0".into()) } else { Ok(a/b) }`|
| Factorial      | `try_fold(...).unwrap_or(0)`                    | `try_fold(...).ok_or("overflow".into())`            |
| Power          | `checked_pow(...).unwrap_or(0)`                 | `checked_pow(...).ok_or("overflow".into())`         |
| Parse          | `s.parse().unwrap_or(0)`                        | `s.parse().map_err(|e| format!("{}", e))`           |

**User impact**: Each migration is a localized change to a single HOL block.
The language author replaces `.unwrap_or(default)` with
`.ok_or_else(|| msg.into())` or uses explicit `Ok(...)`/`Err(...)` branches.

### 8.3 Phase 3: Migrate Non-Native Types (Opt-In)

For non-native types that already use explicit `Cat::Err` returns (like
RhoCalc), optionally migrate to `Result<Cat, String>`:

| Before                             | After                                  |
|------------------------------------|----------------------------------------|
| `_ => Proc::Err`                  | `_ => Err("type mismatch".into())`     |
| `Proc::CastInt(Box::new(...))`    | `Ok(Proc::CastInt(Box::new(...)))`     |

**Benefit**: Error messages become available in simulation traces, aiding
debugging. The `Err` variant is still auto-generated (or manually defined) to
serve as the sentinel in the fold relation.

**User impact**: Optional. The existing bare-`Proc::Err` style continues to
work. Migration can be done incrementally, one HOL block at a time.

### 8.4 Phase 4: Simulation Enhancements (Automatic)

Once Result-based errors are available, the simulation framework automatically
gains:

1. **Error detection in campaigns**: `SimulationFailure` reports include the
   specific error message from the HOL block.
2. **Morphological error tracking**: `MorphologyTracker` detects error fraction
   trends.
3. **LTL atomic propositions**: `error` and `error_free` become well-defined.
4. **Coverage of error paths**: The coverage-guided simulator can target inputs
   that trigger `Err` branches.

**User impact**: None. These enhancements are automatic once the macro
infrastructure and language specifications are updated.

---

## 9. References

- Claessen, K. & Hughes, J. (2000). "QuickCheck: A Lightweight Tool for Random
  Testing of Haskell Programs." *Proceedings of the Fifth ACM SIGPLAN
  International Conference on Functional Programming (ICFP '00)*, pp. 268--279.
  ACM.

- Moggi, E. (1991). "Notions of Computation and Monads." *Information and
  Computation*, 93(1), pp. 55--92.

- Scott, D. & Strachey, C. (1971). "Toward a Mathematical Semantics for
  Computer Languages." *Proceedings of the Symposium on Computers and Automata*,
  Polytechnic Institute of Brooklyn. Also: Oxford University Computing
  Laboratory, Programming Research Group, Technical Monograph PRG-6.

- Wadler, P. (1995). "Monads for Functional Programming." In *Advanced
  Functional Programming*, Lecture Notes in Computer Science, vol. 925,
  pp. 24--52. Springer.

- Pnueli, A. (1977). "The Temporal Logic of Programs." *Proceedings of the 18th
  Annual Symposium on Foundations of Computer Science (FOCS '77)*, pp. 46--57.
  IEEE.

- Vardi, M.Y. & Wolper, P. (1986). "An Automata-Theoretic Approach to Automatic
  Program Verification." *Proceedings of the First Annual IEEE Symposium on Logic
  in Computer Science (LICS '86)*, pp. 332--344. IEEE.

---

### Source Files Referenced

| File | Role |
|------|------|
| `macros/src/gen/native/eval.rs` | Eval/try_eval method generation for native types |
| `macros/src/logic/mod.rs` | Ascent Datalog generation (fold rules, step rules, relations) |
| `macros/src/gen/types/enums.rs` | AST enum generation (variants, auto-generated constructors) |
| `languages/src/calculator.rs` | Calculator language specification (native-only HOL blocks) |
| `languages/src/rhocalc.rs` | RhoCalc language specification (non-native HOL with Err) |
| `simulation/src/runner.rs` | Simulation runner (campaign orchestration, invariant checking) |
| `simulation/src/morphology.rs` | Term morphology tracking (structural metrics) |
| `simulation/src/invariant.rs` | Invariant trait and built-in invariants |
| `languages/src/generated/calculator-datalog.rs` | Generated Ascent code for Calculator |
| `languages/src/generated/rhocalc-datalog.rs` | Generated Ascent code for RhoCalc |
