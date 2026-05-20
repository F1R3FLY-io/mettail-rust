# Modules in Language Specifications — Design

## 1. Goal

Enable **modular language specifications** in mettail-rust so that:

1. A **module** file can declare reusable **extenders** (parameterized presentation transformers), **languages** (fully instantiated specs), **spaces** (typed channels), and eventually **process code** (Rolang programs operating on those languages).
2. A **top-level language file** (`.ro` or equivalent) can **import** modules and assemble a language from extender expressions rather than monolithic `language! { ... }` blocks.
3. Users express **what** to combine in the MeTTaIL/Rolang surface language; **how** that becomes Rust/Ascent remains an implementation detail (not Cargo/TOML in the user experience).

This design does **not** require implementing the full vision in one step. It defines phases, interfaces, and open questions so work can proceed incrementally without blocking current `language!`-based languages.

---

## 2. Problem Statement

### 2.1 Current state

Each language in `languages/src/` is a single Rust file using the `language!` proc macro:

| File | Language | Mechanism |
|------|----------|-----------|
| `rhocalc.rs` | RhoCalc | `language! { types, literals, terms, equations, rewrites, logic }` |
| `calculator.rs` | Calculator | same |
| `lambda.rs`, `ambient.rs` | Lambda, Ambient | same |

The macro parses into `LanguageDef` (`macros/src/ast/language.rs`) and generates AST types, parser, Ascent, REPL metadata, and Blockly artifacts. There is **no** import graph, no parameterized extension, and no separate module compilation unit.

Legacy `space.rs` uses an older `theory!` spelling; the supported entry point is **`language!`** only (`macros/src/lib.rs`).

### 2.2 What is missing

| Capability | GSLT (Scala) | ModuleSketch | mettail-rust today |
|------------|--------------|--------------|-------------------|
| `import` path + alias | yes | yes | no |
| Parameterized `Theory` / `extender` | yes | yes | no |
| Presentation union (`\/`) | yes | yes | no |
| `Exports` / category rename | yes | implied via extender | manual in one file |
| `Replacements` | yes | not in sketch grammar yet | manual |
| `free` / closed dependency tree | yes (partial) | not in sketch | no |
| Nested modules + `export` | partial | yes | no |
| `language foo = Ext(...)` binding | via `Theory` result | yes | `name:` in `language!` only |
| Typed **spaces** (channels) | vision | yes | no |
| Process code inside module | vision | yes (example) | N/A (Rust host only) |

### 2.3 Naming direction

The notes recommend treating **RhoCalc** as one language inside a broader **Rolang** platform: the host spec file should eventually allow **multiple language specs** in `.ro` files, not only a single embedded `rhocalc.rs`. Renaming `rhocalc.rs` → `rolang.rs` (or splitting host vs language) is a **follow-on** refactor; this design uses **Rolang** for the file/module language and keeps **RhoCalc** as a concrete language name where helpful.

---

## 3. Concepts and Terminology

| Term | Meaning |
|------|---------|
| **Presentation** | Structured description of a language fragment: exports (categories), terms, equations, rewrites, relations, literals, native types. GSLT builds presentations; mettail-rust today flattens them into `LanguageDef`. |
| **Extender** | Parameterized constructor over presentations (GSLT `Theory`). Syntax: `extender Name(params) { expr }`. Invoked as `Name(arg1, arg2)` in language expressions. |
| **Module** | Named unit in a `.module` file: imports, private/exported extenders, languages, spaces, nested modules, and (later) process code. |
| **Language binding** | Named fully built presentation, e.g. `export language fooLang = MyExtender(Module1.bar, ...)`. Becomes the type of terms allowed on a **space**. |
| **Space** | Typed channel carrying terms of a given language binding (`space id: LangExpr`). Analogous to MeTTa “spaces”: facts/terms of one spec, read/write on a channel. Not the same as C++ namespaces (similar *scoping* idea, different runtime model). |
| **`language!`** | Today’s Rust proc-macro surface for a **closed** `LanguageDef`. Long-term: one possible **lowering target** after resolving a `.ro` / module graph—not the authoritative user spec. |
| **`free`** (GSLT) | Build a presentation from a fixed dependency tree without explicit arguments (e.g. `free Rolling` → `EmptySet` → … → `Rolling`). Deferred to a later phase; see §8.3. |

**Mapping to GSLT** (`UnivAlg.module`, `Rholang.module`):

```
GSLT                    Rolang (ModuleSketch)
------                  ---------------------
Module                  module
Theory                  extender
import "X.module" as u  import "path" [as Id]
Exports { Elem => Proc }  (part of extender / exports block)
Replacements { ... }      (extender feature — phase 2+)
\/                      \/
let x = T() in ( ... )   (free / nested construction — phase 3)
```

---

## 4. User-Facing Architecture

### 4.1 Two layers (sketch)

```
┌─────────────────────────────────────────────────────────────┐
│  Layer A: Module / .ro file language (Rolang spec)          │
│  - import, module, extender, language, space, export        │
│  - Self-contained; not Cargo/TOML                           │
└───────────────────────────┬─────────────────────────────────┘
                            │ resolve + compose presentations
                            ▼
┌─────────────────────────────────────────────────────────────┐
│  Layer B: Implementation backends (pluggable)               │
│  - Today: expand to Rust + language! / codegen              │
│  - semantics <backend> in extender (default: Rust)          │
│  - Future: other targets, Ascent replacement, etc.          │
└─────────────────────────────────────────────────────────────┘
```

**Principle:** Layer A is owned by MeTTaIL. Layer B is selected per extender or project config but must not appear in the **authoring** syntax for combining modules (no “put module paths in `Cargo.toml`” for users).

### 4.2 File kinds

| Extension | Role |
|-----------|------|
| `.module` | Reusable library: extenders, exported languages, optional spaces/code |
| `.ro` | Entry file: imports + top-level module (or bare content) defining deployable language(s) |

**Convention (from sketch):** `module MyModule { ... }` identifier **must match** the filename stem (`MyModule.module`).

### 4.3 Import resolution

Imports are **filesystem-relative** (or search-path based), resolved when the Rolang toolchain loads a file—not at Rust macro expansion time by default.

```rolang
import "path/to/UnivAlg.module"
import "path/to/other.module" as M1
import {
  "path/to/A.module"
  "path/to/B.module" as B
}
```

Rules:

1. Quoted paths are logical module paths; resolver maps to `.module` files on disk.
2. If `as Alias` is omitted, the alias is the **module identifier** declared inside the file (`module UnivAlg { ... }` → `UnivAlg`).
3. Qualified references: `Alias.ExtenderName`, `Alias.Nested.SubExtender`, `Alias.languageName`.
4. Cycles: reject at load time with a clear error.
5. Conflicting aliases: require `as` (sketch already allows this).

**Open:** search path roots (project root, `METTAIL_MODULE_PATH`, sibling of importing file). Recommend: directory of importing file first, then explicit path list in a **tool** config file (not `Cargo.toml`).

---

## 5. Surface Syntax (authoritative sketch + GSLT alignment)

The normative user syntax is documented in [ModuleSketch.md](./ModuleSketch.md). Summary for implementers:

### 5.1 Module body

```rolang
module MyModule {
  export extender MyExtender(arg1, arg2) {
    { arg1 \/ arg2 }
      semantics M1.Go    // optional backend; default Rust
      types { ... }
      terms { ... }
      literals { ... }
      equations { ... }
      relations { ... }  // was logic
      rewrites { ... }
  }

  module PrivateNested { ... }           // private
  export module PublicNested { ... }     // visible to importers

  export language fooLang = MyExtender(Module1.bar, M2.Nested.SomeExtender(...))

  space foo: fooLang                      // module-private space
  export space bar: fooLang               // public space

  // Phase 4+: Rolang process code (let, for, !, etc.)
}
```

### 5.2 Extender expressions

| Form | Role |
|------|------|
| `Empty` | Empty presentation (GSLT `Empty` / `EmptySet`) |
| `e1 \/ e2` | Union of presentations (merge exports, terms, equations, rewrites) |
| `{ e }` | Grouping |
| `e types { ... }` | Add/overrides on `e` |
| `e terms { ... }` | … |
| `e literals { ... }` | … |
| `e equations { ... }` | … |
| `e relations { ... }` | … |
| `e rewrites { ... }` | … |

**Phase 1** can restrict to: base identifier, call `Ext(a, b)`, and chained suffix blocks (`types`, `terms`, …) without full `/\` or replacement algebra.

### 5.3 Language expressions

```bnf
LanguageExpr ::= PathElement ("." PathElement)* [ "(" LanguageExpr ("," LanguageExpr)* ")" ]
```

Examples:

- `fooLang` — local binding
- `Module1.bar` — imported extender applied elsewhere
- `MyExtender(Module1.bar, M2.baz)` — call chain

### 5.4 Export visibility

| Construct | Default visibility | `export` effect |
|-----------|-------------------|-----------------|
| `extender` | private | exported to importers |
| `module` (nested) | private | exported |
| `language` | n/a (binding) | must use `export language` to expose |
| `space` | private | `export space` for public channel type |

### 5.5 Embedded process code (later)

The sketch shows **labeled backticks** for embedding terms of a given language:

```rolang
let myVar <- fooLang`5` in { ... foo!(fooLang`term`) ... }
```

Triple-backtick blocks allow multiline snippets and `${var}` interpolation. This is **orthogonal** to extender composition but lives in the same module file for packaging. Parsing can reuse PraTTaIL once `fooLang` fixes the active presentation.

---

## 6. Semantic Model

### 6.1 Presentation algebra

Internally, treat each extender body and each `language = ...` rhs as building a **`Presentation`** value (working name; may become a Rust struct in `mettail-modules` or similar):

```rust
// Conceptual — not final API
struct Presentation {
    exports: ExportMap,           // category names + renames
    types: Vec<LangType>,
    literals: Option<LiteralBlock>,
    terms: Vec<GrammarRule>,
    equations: Vec<Equation>,
    rewrites: Vec<RewriteRule>,
    relations: Option<LogicBlock>,
    semantics: SemanticsTarget,   // Rust, Go, ...
}
```

**Extender application:** `ParMonoid(cm)` requires `cm` to satisfy constraints (e.g. exports `Elem`, provides monoid laws). Type checking is **presentation typing**: verify actual exports/labels match the parameter’s expected interface.

**Union (`\/`):** Merge presentations with conflict rules (GSLT-style):

- Disjoint exports: concatenate.
- Same label, compatible types: merge (later: replacements pick winner).
- Incompatible duplicate term labels without replacement: **error**.

This aligns with [theory_composition.md](./theory_composition.md) (exports, replacements, conjunction). The module design **subsumes** that document’s Rust strategy once presentations exist as data.

### 6.2 From presentation to `LanguageDef`

Lowering pipeline:

```
.module / .ro  →  parse  →  resolve imports  →  evaluate extender graph
    →  Presentation (for each export language)
    →  validate (existing validate_language)
    →  backend: language! tokens OR direct generate_all(LanguageDef)
```

Reusing `LanguageDef` avoids rewriting codegen; the new work is **front of pipeline** (parse, compose, check).

### 6.3 GSLT features — phasing

| Feature | GSLT example | Phase |
|---------|--------------|-------|
| Parameterized extender | `Theory Monoid(s: EmptySet)` | 1 |
| Extend base `s` + add blocks | `s` then `Terms { ... }` | 1 |
| `Exports { Elem => Proc }` | `ParMonoid` | 2 |
| `Replacements { [] Zero => PZero }` | `CommutativeMonoid` | 2 |
| `\/` on bases | `Rig { add \/ mult }` | 2 |
| `import` | `Rholang.module` | 1 |
| `free` / `let` chains | `FreeRholang` | 3 |
| Relations / custom logic | sketch `relations` | 2 (map to `logic`) |
| Spaces + process code | sketch § example | 4 |

### 6.4 `free` extender (deferred detail)

GSLT `Rolling.module` (not in repo snapshot) uses parameter annotations so that **free** invocation selects a default theory for each parameter (e.g. `free Rolling` expands to a tree ending in `EmptySet`). Semantics:

- **Not** the categorical free functor in full generality; “free” means **supply default actual parameters** from named extender metadata.
- Implementation: table of `(extender, param) → default extender` or explicit `free ExtName` macro expansion at compose time.

Document as **phase 3**; do not block phase 1 on correct categorical terminology.

---

## 7. Relationship to `language!` and Rust

### 7.1 Non-goals for user experience

- Users do **not** declare module dependencies in `Cargo.toml` for spec composition.
- Users do **not** need to write Rust to combine two `.module` files.

### 7.2 Acceptable Rust integration (implementation)

| Approach | Use |
|----------|-----|
| **Offline compiler** (`mettail-ro` / `mettail-module build`) | Parse `.module`, emit `generated/foo.rs` with `language! { ... }`, checked into repo or `OUT_DIR` | Recommended for phase 1 |
| **Proc-macro `include_lang!`** | Macro invokes compiler at build time; needs stable paths | phase 2 |
| **Runtime composition** | Dynamic presentations | exploratory only; see theory_composition Option A |

**Recommendation:** Start with an **offline** tool in the mettail-rust workspace:

```
languages/
  src/
    rhocalc.rs          # generated from rhocalc.ro (eventually)
  specs/                # new: hand-authored modules
    core/UnivAlg.module
    rhocalc/RhoCalc.module
```

`languages/build.rs` (or a separate binary) runs the composer before `cargo build`. Rust crate dependencies remain ordinary (Ascent, runtime); only the **spec graph** is non-Rust.

### 7.3 `semantics` clause

Sketch: `semantics M1.Go` inside extender blocks. Default: **Rust** / existing codegen.

- Phase 1: ignore or error on non-Rust except `Rust`.
- Later: plugin interface emitting alternate parsers or runtimes.

### 7.4 Capitalization

GSLT uses `Module` / `Theory`; sketch uses lowercase `module` / `extender`. **Decision:** follow [ModuleSketch.md](./ModuleSketch.md) for new syntax; provide a mechanical mapping document for GSLT importers. BNFC grammar in sketch is authoritative for the parser generator.

---

## 8. Implementation Plan

### Phase 0 — Design alignment (this document)

- [x] Capture sketch + GSLT alignment
- [ ] Review when detailed spec arrives
- [ ] User’s additional ideas (to be merged when supplied)

### Phase 1 — Module loader + minimal extender (MVP)

**Deliverables:**

1. AST for `.module` files (imports, module, extender, `language` binding) matching sketch grammar subset.
2. Import resolver + cycle detection.
3. `Presentation` struct mirroring `LanguageDef` fields (or wrap `LanguageDef`).
4. Extender: single base reference + one suffix block (`terms` only for POC).
5. CLI: `mettail-module compile path/to/Foo.module --lang bar` → prints or writes `language!` snippet.
6. Tests: port `UnivAlg.module` **Monoid** chain as extenders; assert composed output matches hand-written `calculator` fragment or small fixture.

**Out of scope:** `/\`, replacements, spaces, process code, `free`.

### Phase 2 — Composition parity with GSLT

- `\/`, `Exports`, `Replacements`
- `relations` → `logic` lowering
- `literals`, native types in extenders
- Compose `Rholang.module`-style stack; diff against monolithic `rhocalc.rs` (structural equivalence goal)

### Phase 3 — `free`, fixpoint languages, refactor entry

- `free ExtName` expansion
- Optional: split `rhocalc.rs` into generated + thin runtime Rust (`pathmap`, `receive`, …)
- Rename / introduce `rolang` host file

### Phase 4 — Spaces and process code

- `space` / `export space` typing in module AST
- Embed Rolang processes in modules (sketch `let` / `for` / channel example)
- Runtime wiring to REPL or f1r3node-style spaces (separate runtime design)

---

## 9. Component Design (mettail-rust)

### 9.1 Suggested crates / modules

| Component | Location (proposed) | Responsibility |
|-----------|---------------------|----------------|
| `rolang-parser` or `mettail-rolang` | new workspace crate | Parse `.module` / `.ro`, BNFC or hand-written per sketch |
| `mettail-present` | new or `macros/src/present/` | `Presentation`, merge, check, lower to `LanguageDef` |
| `mettail-module` | binary | CLI: resolve, compile, explain graph |
| `macros` | existing | Consume `LanguageDef` unchanged initially |
| `languages` | existing | Generated `language!` + hand-written runtime shims |

Keep **IO out of macros** initially: deterministic fixtures, no network.

### 9.2 Validation reuse

After lowering to `LanguageDef`, call existing `validate_language` (`macros/src/ast/validation.rs`) so module composition cannot produce ill-formed languages that codegen would reject anyway.

### 9.3 Testing strategy

| Level | Content |
|-------|---------|
| Unit | Import alias, cycle detection, `/\` conflicts |
| Golden | GSLT modules → composed presentation snapshot (JSON or pretty AST) |
| Integration | Composed `RhoCalc`-like spec generates parser; smoke parse terms from `repl/src/examples/` |
| Regression | Existing `cargo test --all-features --workspace` unchanged when not using modules |

Deterministic: fixed module paths in `languages/specs/test/`.

### 9.4 Migration: monolithic `rhocalc.rs`

**Strategy:** Do not delete `rhocalc.rs` until phase 2 proves equivalence.

1. Extract a **reference presentation** from current `language!` block (manual or tool-assisted).
2. Rebuild via extenders mimicking `Rholang.module` layering (`ParMonoid` → … → `RhoCalc`).
3. `diff` generated Ascent/parser artifacts against `languages/src/generated/rhocalc-*`.
4. Switch build to generated file when diff is empty or explained.

Hand-written Rust in `languages/src/rhocalc/` (runtime, wire, pathmap) **stays** as host code; only the **spec** moves to modules.

---

## 10. Example Walkthrough (GSLT → Rolang)

**UnivAlg** (simplified):

```rolang
module UnivAlg {
  export extender EmptySet() {
    Empty
      types { ... }  // Elem export — details in phase 2
  }

  export extender Monoid(s: EmptySet) {
    s
      terms {
        One . Elem ::= "1" ;
        Mult . Elem ::= "(" Elem "*" Elem ")" ;
      }
      equations { ... }
  }
  // CommutativeMonoid, Rig, ...
}
```

**Rholang layer** (from `Rholang.module`):

```rolang
import "UnivAlg.module" as u

module Rholang {
  export extender ParMonoid(cm: u.CommutativeMonoid) {
    cm
      // exports, replacements, rewrites — phase 2
  }

  export language FreeRholang = ... // phase 3: free expansion
}
```

**Consumer module** (sketch style):

```rolang
import "Rholang.module"

module App {
  export language rho = Rholang.FreeRholang
  export space main: rho
}
```

### 10.1 Example: Complex arithmetic module used by Calculator

This walkthrough shows how a **standalone** module defines complex-number syntax and semantics, and how the **Calculator** language **imports** and **composes** it—without duplicating the whole `languages/src/calculator.rs` spec in one file.

**Layout (proposed):**

```
languages/specs/
  arithmetic/
    ComplexArithmetic.module   # reusable complex-number fragment
  calculator/
    Calculator.module          # entry: base calculator + optional imports
```

**Today:** Calculator is one `language! { ... }` block (~500+ lines) in `calculator.rs` with `Proc`, scalar types (`Int`, `Float`, …), injections (`ProcInt`, `ProcFloat`, …), and arithmetic on each scalar. **Target:** scalar core stays in `Calculator.module`; complex numbers arrive via `\/` from an imported module.

---

#### Step 1 — `ComplexArithmetic.module` (library)

The module exports an extender parameterized on a **base presentation** that already provides `Float` (and, for injection into the REPL primary category, `Proc`). The extender adds a `Complex` category, literals, operations, and a `Proc` injection—mirroring how Calculator today has `ProcFloat` for floats.

```rolang
// languages/specs/arithmetic/ComplexArithmetic.module

module ComplexArithmetic {

  // Parameter: base must export Float and Proc (Calculator's scalar shell).
  export extender ComplexOnFloat(base: BaseWithFloat) {
    base
      types {
        // Pair (re, im) backed by native floats; codegen may lower to a Rust struct.
        ![mettail_runtime::Complex64] as Complex
      }
      literals {
        Complex {
          // Examples: 3+4i, 3-4i, -i, 2.5+0.5i
          pattern: r"(-?([0-9](_?[0-9])*(\.[0-9](_?[0-9])*)?|[0-9](_?[0-9])*)[+-]([0-9](_?[0-9])*(\.[0-9](_?[0-9])*)?|[0-9](_?[0-9])*)i|-?i)";
          eval: ![ { mettail_prattail::parse_complex_lit(text).map_err(|_| ()) } ]
        }
      }
      terms {
        CAdd . a:Complex, b:Complex |- a "+" b : Complex ![a + b] fold;
        CSub . a:Complex, b:Complex |- a "-" b : Complex ![a - b] fold;
        CMul . a:Complex, b:Complex |- a "*" b : Complex ![a * b] fold;
        CDiv . a:Complex, b:Complex |- a "/" b : Complex ![a / b] fold;
        CNeg . a:Complex |- "-" a : Complex ![(-a)] fold;
        CConj . a:Complex |- "conj" "(" a ")" : Complex ![a.conj()] step;
        CAbs . a:Complex |- "abs" "(" a ")" : Float ![a.norm()] step;

        // Inject into Proc so complex values mix with existing calculator terms.
        ProcComplex . z:Complex |- z : Proc ;
      }
      equations {
        // Optional: algebraic laws (e.g. neutral elements) once CZero/COne are declared.
      }
      rewrites {
        // Step rules for literals / native eval (same role as AddFloat in calculator.rs).
        (CAdd (NumLit a) (NumLit b)) => (NumLit (a + b));
        (CMul (NumLit a) (NumLit b)) => (NumLit (a * b));
      }
    }

  // Marker extender describing the parameter interface (phase 2: formal export checks).
  export extender BaseWithFloat() {
    Empty
      types {
        Proc
        ![f64] as Float
      }
  }
}
```

**Notes for implementers:**

| Piece | Role |
|-------|------|
| `ComplexOnFloat(base)` | Extends whatever language passed in (`base`), same pattern as GSLT `Theory ParMonoid(cm: u.CommutativeMonoid) { cm ... }`. |
| `base` first in body | Inherits `Proc`, `Float`, and all existing scalar terms from the argument. |
| `ProcComplex` | Same idea as `ProcFloat` / `ProcInt` in today's `calculator.rs`. |
| Literal-only complex values | `Complex { pattern, eval }` is enough for phase 1; extra constructors are optional. |
| `![mettail_runtime::Complex64]` | Illustrates native backing; exact type name is an implementation choice. |

---

#### Step 2 — `Calculator.module` (consumer)

Calculator **imports** the library and **unions** the complex extender onto a local “scalar core” extender. The exported `language` binding is what codegen lowers to `language! { name: Calculator, ... }`.

```rolang
// languages/specs/calculator/Calculator.module

import "arithmetic/ComplexArithmetic.module" as Cpx

module Calculator {

  // Scalar fragment: mirrors the bulk of today's calculator.rs (Int, Float, Bool, …).
  export extender CalcScalars() {
    Empty
      types {
        Proc
        ![i32] as Int
        ![f64] as Float
        ![bool] as Bool
        ![str] as Str
        // … UInt32, BigInt, collections, etc.
      }
      literals {
        Int { pattern: r"..."; eval: ![ ... ] }
        Float { pattern: r"..."; eval: ![ ... ] }
        // …
      }
      terms {
        ProcInt . i:Int |- i : Proc ;
        ProcFloat . f:Float |- f : Proc ;
        AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        AddFloat . a:Float, b:Float |- a "+" b : Float ![a + b] fold;
        // … remainder of scalar calculator (comparisons, lists, maps, casts, …)
      }
      rewrites {
        // … step rules for Int/Float/Bool as in calculator.rs
      }
  }

  // Full calculator = scalars ∪ complex arithmetic on floats.
  export extender CalcFull() {
    CalcScalars() \/ Cpx.ComplexOnFloat(CalcScalars())
  }

  export language Calculator = CalcFull()
}
```

**Composition diagram:**

```
CalcScalars()  ──argument──►  ComplexOnFloat(·)
       │                              │
       └─────────── \/ ───────────────┘
                         │
                         ▼
                  export language Calculator
                         │
                         ▼ (lower)
              language! { name: Calculator, ... }  →  calculator.rs (generated)
```

---

#### Step 3 — What users gain

After lowering and build, the REPL language `calculator` accepts **both** existing scalar terms and complex terms, without maintaining two separate `language!` files:

| Input (illustrative) | Meaning |
|----------------------|---------|
| `3 + 4` | Scalar `Int` (unchanged) |
| `1.5 * 2.0` | Scalar `Float` |
| `3+4i` | Complex literal |
| `(3+4i) * (1-2i)` | Complex `CMul` |
| `conj(3+4i)` | Complex `CConj` |
| `abs(3+4i)` | `CAbs` → `Float` |

Optional: a slimmer calculator that **does not** import complex numbers is a second binding in the same file or a sibling module:

```rolang
export language CalculatorScalarsOnly = CalcScalars()
```

---

#### Step 4 — Mapping to today's `calculator.rs`

| Today (`calculator.rs`) | Modular form |
|-------------------------|--------------|
| Single `language! { types, literals, terms, rewrites }` | `CalcScalars()` extender + `export language Calculator = CalcFull()` |
| All types in one block | `CalcScalars` types; `Complex` only in `ComplexArithmetic.module` |
| `ProcFloat`, `AddFloat`, … | Stay in `CalcScalars` |
| (not present) | `ProcComplex`, `CAdd`, … from `Cpx.ComplexOnFloat(...)` via `\/` |
| Rust `language!` macro | Emitted by `mettail-module compile` (§7.2) |

**Phasing:** Phase 1 can compile `Calculator.module` that only imports and calls `ComplexOnFloat` with **terms** on `Complex`; `exports` renaming and full `replacements` are not required for this example. Phase 2 adds stricter checks that `base` actually exports `Float` and `Proc` before applying `ComplexOnFloat`.

---

#### Step 5 — Alternative: complex module without union (import + call only)

If complex operations should stay **namespaced** under the import alias (no merge into one flat language), omit `\/` and reference the extender explicitly:

```rolang
import "arithmetic/ComplexArithmetic.module" as Cpx

module Calculator {
  export extender CalcScalars() { /* … */ }

  export language CalculatorWithCpx =
    Cpx.ComplexOnFloat(CalcScalars())
}
```

Here `CalculatorWithCpx` is exactly the parameterized application—useful for tests comparing “scalar-only” vs “scalar+complex” presentations without duplicating `CalcScalars` bodies.

---

## 11. Open Questions

| # | Question | Notes |
|---|----------|-------|
| 1 | Exact path resolution algorithm and config file name | Avoid Cargo.toml; consider `.mettail/config` |
| 2 | `Replacements` syntax in Rolang | GSLT has indices `[]`, `[0,1]`; not in sketch BNFC |
| 3 | BNFC vs Rust proc-macro parser for `.module` | Sketch includes BNFC; may generate parser into `rolang-parser` |
| 4 | Proc-macros reading files at compile time | `include_lang!` vs build.rs only |
| 5 | Interaction with `gslt-to-rholang` branch | May share AST; coordinate before duplicating parsers |
| 6 | Spaces runtime | Typed channels need runtime spec separate from presentation |
| 7 | `theory!` deprecation | `space.rs` legacy; document removal when `language!` + modules stable |
| 8 | Versioning / ABI of `.module` files | Semver on language bindings? |
| 9 | Detailed spec | Merge when received; may override capitalization or `free` semantics |

---

## 12. Success Criteria

**Phase 1 done when:**

- Two `.module` files import each other (acyclic) and export a `language` binding.
- Composed presentation lowers to valid `LanguageDef` and passes `validate_language`.
- CLI emits Rust that compiles in `languages` crate.
- At least one automated test ports a fragment of `UnivAlg.module`.

**Long-term done when:**

- `rhocalc.rs` spec is module-authored; runtime Rust is the only hand-maintained part.
- Users can author new languages by importing extenders without editing proc-macro Rust.
- Spaces and embedded process code type-check against `export language` bindings.

---

## 13. References

| Resource | Path |
|----------|------|
| Syntax sketch | [ModuleSketch.md](./ModuleSketch.md) |
| Theory composition (Rust options) | [theory_composition.md](./theory_composition.md) |
| Current `language!` anatomy | [docs/examples/rhocalc/01-language-spec.md](../../examples/rhocalc/01-language-spec.md) |
| GSLT UnivAlg | `~/Projects/MeTTaIL/GSLT/src/test/module/UnivAlg.module` |
| GSLT Rholang | `~/Projects/MeTTaIL/GSLT/src/test/module/Rholang.module` |
| Implemented language design example | [rhocalc-permanent-communication-design.md](../made/rhocalc-permanent-communication-design.md) |

---

## 14. Appendix — Partial grammar (from sketch)

Copied for convenience; **ModuleSketch.md** remains authoritative if they diverge.

```
File . BasicFile ::= [Import] Module ;
Module . BasicModule ::= "module" Ident "{" [ModifiedContent] "}"

Import . SingleImport ::= "import" ImportDescriptor ;
Import . BlockImport ::= "import" "{" [ImportDescriptor] "}" ;
ImportDescriptor . Simple ::= QuotedString ;
ImportDescriptor . Alias ::= QuotedString "as" Ident;

ModifiedContent . PrivateContent ::= Content ;
ModifiedContent . PublicContent ::= "export" Content;

Content . ExtenderContent ::= "extender" Ident "(" [ExtenderArg] ")" "{" ExtenderExpr "}" ;
Content . LanguageContent ::= "language" Ident "=" LanguageExpr ;
Content . SpaceContent ::= "space" Ident ":" LanguageExpr ;
Content . ModuleContent ::= Module ;

ExtenderExpr . UnionEE ::= ExtenderExpr "\/" ExtenderExpr ;
-- see ModuleSketch.md for full ExtenderExpr and LanguageExpr productions
```

---
