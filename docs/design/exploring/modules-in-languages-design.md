# Modules in Language Specifications — Design

---

## 1. Goal

Enable **modular language specifications** so that:

1. A **module** file can declare reusable **extenders** (parameterized presentation transformers), **languages** (fully instantiated specs), **spaces** (typed channels), and eventually **process code** (Rholang programs operating on those languages).
2. A **top-level** `.ro` (or equivalent) file can **import** modules and assemble a language from extender expressions rather than one monolithic spec.
3. Authors express **what** to combine in the MeTTaIL/Rholang surface language only. Lowering to parsers, rewrite engines, or runtimes is an **implementation backend** detail—and must not use Cargo or similar host build manifests for spec composition (see §7.1).

This design does **not** require implementing the full vision in one step. It defines phases, interfaces, and open questions so work can proceed incrementally without blocking current monolithic specs in existing backends.

---

## 2. Problem Statement

### 2.1 Current state (mettail-rust anchor)

Today, each language in `languages/src/` is a single host file using the `language!` proc macro—a **monolithic** spec with no import graph:

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
| Process code inside module | vision | yes (example) | host runtime only (not in module algebra) |

### 2.3 Naming direction

The notes recommend treating **RhoCalc** as one language inside a broader **Rholang** platform: `.ro` / `.module` files should eventually host **multiple language specs**, not only one embedded monolith. This design uses **Rholang** for the module/file language and keeps **RhoCalc** as a concrete language name where helpful.

---

## 3. Concepts and Terminology

| Term | Meaning |
|------|---------|
| **Presentation** | Structured description of a language fragment: exports (categories), terms, equations, rewrites, relations, literals, native types. GSLT builds presentations; mettail-rust today flattens them into `LanguageDef`. |
| **Extender** | Parameterized constructor over presentations (GSLT `Theory`). Syntax: `extender Name(params) { expr }`. Invoked as `Name(arg1, arg2)` in language expressions. |
| **Module** | Named unit in a `.module` file: imports, private/exported extenders, languages, spaces, nested modules, and (later) process code. |
| **Language binding** | Named fully built presentation, e.g. `export language fooLang = MyExtender(Module1.bar, ...)`. Becomes the type of terms allowed on a **space**. |
| **Space** | Typed channel carrying terms of a given language binding (`space id: LangExpr`). Analogous to MeTTa “spaces”: facts/terms of one spec, read/write on a channel. Not the same as C++ namespaces (similar *scoping* idea, different runtime model). |
| **Library fragment** | Reusable extender body (and nested module): contributes to composition but is not, by itself, a shipped REPL/binary language. |
| **Shipped language** | Fully composed binding (`export language L = …`) used by tools, REPL, and spaces. |
| **`free`** (GSLT) | Build a presentation from a fixed dependency tree without explicit arguments (e.g. `free Rolling` → `EmptySet` → … → `Rolling`). Deferred to a later phase; see §6.4. |

**Mapping to GSLT** (`UnivAlg.module`, `Rholang.module`):

```
GSLT                    Rholang (ModuleSketch)
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

### 4.1 Two layers

```
┌─────────────────────────────────────────────────────────────┐
│  Layer A: Rholang spec (modules / .ro)                      │
│  - import, module, extender, language, space, export        │
│  - Authors compose here only; no Cargo for spec composition │
└───────────────────────────┬─────────────────────────────────┘
                            │ resolve imports → compose presentations
                            ▼
┌─────────────────────────────────────────────────────────────┐
│  Layer B: Implementation backends (pluggable)               │
│  - semantics <backend> in extender (e.g. Rust, Go, …)         │
│  - Lowers one canonical language IR → parser, rewrites, REPL  │
└─────────────────────────────────────────────────────────────┘
```

**Principles:**

- Layer A is owned by MeTTaIL and is **backend-neutral**.
- Layer B is chosen per extender (`semantics …`) or project tooling, not in Rholang `import` syntax.
- **One normalization path** from composed modules to a single canonical language description before any backend runs—avoid duplicate composition implementations ([theory_composition.md](./theory_composition.md)).

### 4.1.1 No Cargo for Rholang authors

**Invariant:** Rholang / `.module` authors do **not** use `Cargo.toml` (or host-build manifests such as a theory DAG TOML) to decide **what** to combine. Composition is only via `import "…"`, extenders, and `export language`. Host build files may exist for framework implementers but are out of scope for spec authors.

### 4.2 File kinds

| Extension | Role |
|-----------|------|
| `.module` | Reusable library: extenders, exported languages, optional spaces/code |
| `.ro` | Entry file: imports + top-level module (or bare content) defining deployable language(s) |

**Convention (from sketch):** `module MyModule { ... }` identifier **must match** the filename stem (`MyModule.module`).

### 4.3 Import resolution

Imports are **filesystem-relative** (or search-path based), resolved when the Rholang toolchain loads a file.

```rholang
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

**Judgement syntax (HOL-style):** Terms, equations, and rewrites in module bodies should use **judgement form** (`Label . … |- … : Cat`, `=`, `~>`), not legacy BNFC `Label . Cat ::= "…"` alone. GSLT and §10 examples below may show BNFC for readability; composed specs target HOL ([hol-syntax.md](./hol-syntax.md)). **Equation and rewrite patterns** (left of `=` / `~>`) stay pure structural HOL; host-specific eval hooks attach only at declared sites (§6.5).

### 5.1 Module body

```rholang
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

  // Phase 4+: Rholang process code (let, for, !, etc.)
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

```rholang
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

This aligns with [theory_composition.md](./theory_composition.md) (exports, replacements, conjunction). The module design **subsumes** that document once composition lives in the shared `normalize` step.

### 6.2 Canonical language IR

Each `export language` names one **canonical language description** (internal IR: presentation / descriptor—fields mirror types, terms, equations, rewrites, relations, literals). Backends consume that IR; they do not define the module algebra.

Reusing one IR avoids rewriting every backend when adding modules; new work is **front of pipeline** (parse, compose, check)—see §6.3.

### 6.3 Composition pipeline (normalize)

Whether specs start as `.module` files or are produced by a host frontend, the tool chain should follow **one** merge story:

```text
  import graph (acyclic)  →  collect fragment descriptors
        →  normalize (ordered walk: extend, export, replacement, \/ )
        →  merge entry-file deltas (local types/terms/… for shipped language)
        →  validate  →  single canonical language IR  →  backend codegen
```

**Mental model:** Library fragments are **partial** specs; the shipped `export language` (plus any entry-file blocks) is the **linker** that flattens them into one spec, then a backend runs once.

**Inside `normalize` (per fragment, in dependency order):**

| Step | Effect |
|------|--------|
| Extend base | Inherit types, terms, equations, rewrites from parameter / `extends` |
| Exports | Rename categories through inherited rules (e.g. `Elem => Proc`) |
| Replacements | Override selected constructors (phase 2) |
| Union (`\/`) | Merge two presentations (e.g. `add \/ mult`) |
| Entry deltas | Append blocks that belong only to the final shipped language |

**Conflict policy:** Duplicate rule labels without an explicit replacement → **error**; policy for entry-file vs imported fragments TBD (recommend: entry-file wins on clash, with warning).

**Monolithic specs:** A single module that defines `export language L = …` without importing others remains valid (today’s one-file languages).

### 6.4 Library fragment vs shipped language

| Content | Library fragment (`export extender` / nested `module`) | Shipped language (`export language` + entry file) |
|---------|----------------------------------------------------------|---------------------------------------------------|
| Reusable algebra (Monoid, UnivAlg) | Yes | No |
| Parameterized slice reused in several languages | Yes | Rarely |
| Language name used by REPL / runtime | No | Yes |
| `import` graph | Participates as dependency | Consumes imports + composes |
| Spaces tied to a language | Optional export | Typical |
| Process code in module body | Optional (phase 4) | Optional |
| Backend `semantics` default | Per extender | Inherited / overridden at ship point |

**Rule of thumb:** If another shipped language should `import` and apply it, it belongs in a **library fragment**. What is specific to one deployed language stays in that language’s composition expression or entry-file deltas.

### 6.5 Implementation attachments (backend hooks)

Host code is **not** part of the equational pattern algebra. Backends may attach implementation at fixed **sites** only:

| Site | Pure HOL? | Typical attachment |
|------|-----------|-------------------|
| `types` (native sort) | — | Backend type or semantic model |
| `literals` (`eval`) | — | Parse literal text to value |
| `terms` (trailing eval / fold / step) | Pattern HOL; hook after | Native evaluation |
| `equations` | Yes (LHS/RHS) | No host code in patterns |
| `rewrites` (LHS / `~>` pattern) | Yes | No host code in patterns |
| `relations` / `logic` | Mixed | Backend-specific rules (e.g. custom rewrite engine relations) |
| `examples { }` (optional) | — | Surface-syntax fixtures (e.g. sample Rholang processes); **does not** change the composed algebra—tests/docs only |

The `semantics M1.Go` clause on an extender selects which backend interprets attachments. Defaults are an implementation concern, not part of Rholang composition syntax.

### 6.6 GSLT features — phasing

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

### 6.7 `free` extender (deferred detail)

GSLT `Rolling.module` (not in repo snapshot) uses parameter annotations so that **free** invocation selects a default theory for each parameter (e.g. `free Rolling` expands to a tree ending in `EmptySet`). Semantics:

- **Not** the categorical free functor in full generality; “free” means **supply default actual parameters** from named extender metadata.
- Implementation: table of `(extender, param) → default extender` or explicit `free ExtName` macro expansion at compose time.

Document as **phase 3**; do not block phase 1 on correct categorical terminology.

---

## 7. Tooling and backends

### 7.1 No Cargo for Rholang authors

See §4.1.1. Rholang authors do not use `Cargo.toml` to compose specs. They also do not need to write host-language code to merge two `.module` files.

### 7.2 Composer tool (language-neutral)

A **module compiler** (working name `mettail-module`) should:

1. Parse `.module` / `.ro` and resolve `import` (cycle-free).
2. Evaluate extender expressions → fragment descriptors.
3. Run `normalize` for each `export language` (§6.3).
4. Emit backend input (format depends on target) or canonical IR (e.g. JSON) for CI golden tests.

Suggested layout:

```
languages/specs/
  core/UnivAlg.module
  arithmetic/ComplexArithmetic.module
  calculator/Calculator.module
```

Import search path: directory of the importing file, then project roots / `METTAIL_MODULE_PATH` / tool config (not `Cargo.toml`).

### 7.3 `semantics` clause

`semantics M1.Go` (or similar) on an extender selects the **implementation backend** for attachments (§6.5). Rholang does not embed backend names in `import` paths.

### 7.4 Backends today

A backend may embed specs in a host language (e.g. mettail-rust’s `language!` macro today). That embedding is **not** the Rholang module language; it consumes the canonical IR produced after `normalize` (§6.3).

### 7.5 Capitalization

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
5. CLI: `mettail-module compile path/to/Foo.module --lang bar` → canonical IR and/or backend stub.
6. Golden tests: deterministic composed IR (hash or snapshot) per `export language`.
7. Tests: port `UnivAlg.module` **Monoid** chain; assert composed IR matches a small fixture.

**Out of scope:** `/\`, replacements, spaces, process code, `free`.

### Phase 2 — Composition parity with GSLT

- `\/`, `Exports`, `Replacements`
- `relations` → `logic` lowering
- `literals`, native types in extenders
- Compose `Rholang.module`-style stack; diff against monolithic `rhocalc.rs` (structural equivalence goal)

### Phase 3 — `free`, fixpoint languages, refactor entry

- `free ExtName` expansion
- Optional: split monolithic host encodings into composed modules + separate runtime
- Optional `.ro` entry files alongside backend-specific encodings

### Phase 4 — Spaces and process code

- `space` / `export space` typing in module AST
- Embed Rholang processes in modules (sketch `let` / `for` / channel example)
- Runtime wiring to REPL or f1r3node-style spaces (separate runtime design)

---

## 9. Component Design (tooling)

### 9.1 Suggested components (names provisional)

| Component | Responsibility |
|-----------|----------------|
| Rholang parser | Parse `.module` / `.ro` per [ModuleSketch.md](./ModuleSketch.md) / BNFC |
| Composition core | Fragment descriptors, `normalize`, validation |
| `mettail-module` CLI | Resolve imports, compile `export language`, explain graph, emit IR |
| Backend adapter(s) | Lower canonical IR to concrete tools (mettail-rust is the first) |

Keep **IO out of macros** initially: deterministic fixtures, no network.

### 9.2 Validation reuse

Validation runs on the **merged** canonical IR so composed modules cannot produce specs a backend would reject (mettail-rust reuses `validate_language` today).

### 9.3 Testing strategy

| Level | Content |
|-------|---------|
| Unit | Import alias, cycle detection, `/\` conflicts |
| Golden | GSLT modules → composed presentation snapshot (JSON or pretty AST) |
| Integration | Composed `RhoCalc`-like spec generates parser; smoke parse terms from `repl/src/examples/` |
| Regression | Existing backend tests unchanged when modules not used on a language |

Deterministic: fixed module paths in `languages/specs/test/`.

### 9.4 Migration from monolithic specs

**Strategy:** Keep the monolithic spec until composed modules reach parity (golden IR + backend behavior tests).

1. Extract a **reference presentation** from the monolithic spec (manual or tool-assisted).
2. Rebuild via extenders mimicking `Rholang.module` layering (`ParMonoid` → … → `RhoCalc`).
3. Compare composed IR and backend artifacts to the reference.
4. Switch the shipped language to module-authored sources when diff is empty or explained.

Host **runtime** code (communication, wire formats, etc.) stays outside modules; only the **algebra** moves into `.module` files.

---

## 10. Example Walkthrough (GSLT → Rholang)

Examples below use **HOL judgements** (`|- … : Cat`, `=`, `~>`) as in [hol-syntax.md](./hol-syntax.md). GSLT sources often spell the same rules with BNFC `::=`; composed Rholang modules target HOL only (§5).

### 10.0 UnivAlg (simplified)

Port of `UnivAlg.module` — algebra fragment only; `Group`, `Ring`, etc. follow the same pattern.

```rholang
module UnivAlg {

  export extender EmptySet() {
    Empty
      exports { Elem }
  }

  export extender Monoid(s: EmptySet) {
    s
      terms {
        One . |- "1" : Elem;
        Mult . a:Elem, b:Elem |- "(" a "*" b ")" : Elem;
      }
      equations {
        Assoc . |- (Mult (Mult x y) z) = (Mult x (Mult y z));
        LeftUnit . |- (Mult x (One)) = x;
        RightUnit . |- (Mult (One) x) = x;
      }
  }

  export extender CommutativeMonoid(m: Monoid) {
    m
      replacements {
        [] One.Elem => Zero . |- "0" : Elem;
        [0, 1] Mult.Elem => Plus . a:Elem, b:Elem |- "(" a "+" b ")" : Elem;
      }
      equations {
        Comm . |- (Plus x y) = (Plus y x);
      }
  }

  export extender Rig(add: CommutativeMonoid, mult: Monoid) {
    { add \/ mult }
      equations {
        DistL . |- (Mult x (Plus y z)) = (Plus (Mult x y) (Mult x z));
        DistR . |- (Mult (Plus x y) z) = (Plus (Mult x z) (Mult y z));
        AnnL . |- (Mult x (Zero)) = (Zero);
        AnnR . |- (Mult (Zero) x) = (Zero);
      }
  }

  // Group, AbelianGroup, Ring — same style as GSLT UnivAlg
}
```

### 10.0.1 Rholang process calculus layer

Port of `Rholang.module` (imports algebra, adds process constructs). Replacement right-hand sides are **HOL term judgements**, not `::=`.

```rholang
import "UnivAlg.module" as u

module Rholang {

  export extender ParMonoid(cm: u.CommutativeMonoid) {
    cm
      exports { Elem => Proc }
      replacements {
        [] Zero.Proc => PZero . |- "0" : Proc;
        [0, 1] Plus.Proc => PPar . a:Proc, b:Proc |- "{" a "|" b "}" : Proc;
      }
      rewrites {
        RPar1 . | Q:Proc, Src ~> Tgt |- (PPar {Src, Q}) ~> (PPar {Tgt, Q});
        RPar2 . | Src1 ~> Tgt1, Src2 ~> Tgt2
            |- (PPar {Src1, Src2}) ~> (PPar {Tgt1, Tgt2});
      }
  }

  export extender QuoteDropCalc(pm: ParMonoid) {
    pm
      exports { Name }
      terms {
        PDrop . n:Name |- "*" n : Proc;
        NQuote . p:Proc |- "@" p : Name;
      }
      equations {
        QuoteDrop . |- (NQuote (PDrop N)) = N;
        DropQuote . |- (PDrop (NQuote P)) = P;
      }
  }

  export extender RhoCalc(qd: QuoteDropCalc) {
    qd
      terms {
        PSend . n:Name, q:Proc |- n "!" "(" q ")" : Proc;
        PRecv . ^x.p:[Name -> Proc], n:Name
            |- "for" "(" x "<-" n ")" "{" p "}" : Proc;
      }
      rewrites {
        RComm . |- (PPar {(PRecv ^x.p n), (PSend n q)})
            ~> (subst p (NQuote q) x);
      }
  }

  export language FreeRholang = ...  // phase 3: free / default actuals
}
```

### 10.0.2 Consumer module (sketch style)

```rholang
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

**Today (mettail-rust):** Calculator is one monolithic spec (~500+ lines) with `Proc`, scalar types (`Int`, `Float`, …), injections (`ProcInt`, `ProcFloat`, …), and arithmetic on each scalar. **Target:** scalar core stays in `Calculator.module`; complex numbers arrive via `\/` from an imported module.

---

#### Step 1 — `ComplexArithmetic.module` (library)

The module exports an extender parameterized on a **base presentation** that already provides `Float` (and, for injection into the REPL primary category, `Proc`). The extender adds a `Complex` category, literals, operations, and a `Proc` injection—mirroring how Calculator today has `ProcFloat` for floats.

```rholang
// languages/specs/arithmetic/ComplexArithmetic.module

module ComplexArithmetic {

  // Parameter: base must export Float and Proc (Calculator's scalar shell).
  export extender ComplexOnFloat(base: BaseWithFloat) {
    base
      types {
        // Pair (re, im); backend chooses representation (e.g. native float pair).
        Complex
      }
      literals {
        Complex {
          // Examples: 3+4i, 3-4i, -i, 2.5+0.5i
          pattern: r"(-?([0-9](_?[0-9])*(\.[0-9](_?[0-9])*)?|[0-9](_?[0-9])*)[+-]([0-9](_?[0-9])*(\.[0-9](_?[0-9])*)?|[0-9](_?[0-9])*)i|-?i)";
          eval: /* backend: parse complex literal text */
        }
      }
      terms {
        CAdd . a:Complex, b:Complex |- a "+" b : Complex /* fold eval */;
        CSub . a:Complex, b:Complex |- a "-" b : Complex ;
        CMul . a:Complex, b:Complex |- a "*" b : Complex ;
        CDiv . a:Complex, b:Complex |- a "/" b : Complex ;
        CNeg . a:Complex |- "-" a : Complex ;
        CConj . a:Complex |- "conj" "(" a ")" : Complex ;
        CAbs . a:Complex |- "abs" "(" a ")" : Float ;

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
        Float
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
| Native `Complex` sort | Declared in `types`; backend maps to a concrete representation. |

---

#### Step 2 — `Calculator.module` (consumer)

Calculator **imports** the library and **unions** the complex extender onto a local “scalar core” extender. The exported `language` binding is the shipped language the backend consumes.

```rholang
// languages/specs/calculator/Calculator.module

import "arithmetic/ComplexArithmetic.module" as Cpx

module Calculator {

  // Scalar fragment: mirrors the bulk of today's calculator.rs (Int, Float, Bool, …).
  export extender CalcScalars() {
    Empty
      types {
        Proc
        Int
        Float
        Bool
        Str
        // … UInt32, BigInt, collections, etc.
      }
      literals {
        Int { pattern: r"..."; eval: /* backend */ }
        Float { pattern: r"..."; eval: /* backend */ }
        // …
      }
      terms {
        ProcInt . i:Int |- i : Proc ;
        ProcFloat . f:Float |- f : Proc ;
        AddInt . a:Int, b:Int |- a "+" b : Int ;
        AddFloat . a:Float, b:Float |- a "+" b : Float ;
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
                         ▼
              normalize → shipped language Calculator → backend(s)
```

---

#### Step 3 — What users gain

After composition, the shipped **Calculator** language accepts **both** scalar and complex terms without duplicating the scalar extender in every consumer module:

| Input (illustrative) | Meaning |
|----------------------|---------|
| `3 + 4` | Scalar `Int` (unchanged) |
| `1.5 * 2.0` | Scalar `Float` |
| `3+4i` | Complex literal |
| `(3+4i) * (1-2i)` | Complex `CMul` |
| `conj(3+4i)` | Complex `CConj` |
| `abs(3+4i)` | `CAbs` → `Float` |

Optional: a slimmer calculator that **does not** import complex numbers is a second binding in the same file or a sibling module:

```rholang
export language CalculatorScalarsOnly = CalcScalars()
```

---

#### Step 4 — Mapping from a monolithic spec

| Monolithic spec (one file) | Modular form |
|----------------------------|--------------|
| All types, terms, rewrites together | `CalcScalars()` + `export language Calculator = CalcFull()` |
| All types in one block | `CalcScalars` types; `Complex` only in `ComplexArithmetic.module` |
| Scalar injections / ops | Stay in `CalcScalars` |
| (not present) | `ProcComplex`, `CAdd`, … from `Cpx.ComplexOnFloat(...)` via `\/` |
| Backend lowering | `mettail-module` (or backend-specific frontend) reads composed IR |

**Phasing:** Phase 1 can compile `Calculator.module` that only imports and calls `ComplexOnFloat` with **terms** on `Complex`; `exports` renaming and full `replacements` are not required for this example. Phase 2 adds stricter checks that `base` actually exports `Float` and `Proc` before applying `ComplexOnFloat`.

---

#### Step 5 — Alternative: complex module without union (import + call only)

If complex operations should stay **namespaced** under the import alias (no merge into one flat language), omit `\/` and reference the extender explicitly:

```rholang
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
| 2 | `Replacements` syntax in Rholang | GSLT has indices `[]`, `[0,1]`; not in sketch BNFC |
| 3 | Parser generator for `.module` | BNFC in sketch; hand-written parser alternative |
| 4 | `examples { }` block | Optional surface fixtures (see §6.5); grammar TBD |
| 5 | Spaces runtime | Typed channels need runtime spec separate from presentation |
| 6 | Versioning / ABI of `.module` files | Semver on language bindings? |
| 7 | Entry-file vs import clash policy | Local delta wins vs hard error (§6.3) |
| 8 | Detailed spec | Merge when received; may override capitalization or `free` semantics |

---

## 12. Success Criteria

**Phase 1 done when:**

- Two `.module` files import each other (acyclic) and export a `language` binding.
- Composed presentation lowers to valid canonical IR and passes validation.
- Golden IR snapshot stable for a fixture language.
- At least one automated test ports a fragment of `UnivAlg.module`.

**Long-term done when:**

- Shipped languages (e.g. RhoCalc, Calculator) are module-authored; host runtime code stays separate.
- Users can author new languages by importing extenders in Rholang only.
- Spaces and embedded process code type-check against `export language` bindings.

---

## 13. Appendix — Partial grammar

BNFC-style productions for the Rholang module surface (import, module, extender, language binding). Full `ExtenderExpr` and `LanguageExpr` productions match the normative sketch in §5.

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
-- ExtenderExpr: Empty, Union (\/), grouped blocks, suffix types|terms|literals|equations|relations|rewrites
-- LanguageExpr: dotted paths with optional ( … ) application; see §5.2–5.3
```

---
