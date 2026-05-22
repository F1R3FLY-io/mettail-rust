# Module System Initial Design: The MeTTaIL Unified Specification (MUS)

**Date:** May 2026

---

## 1. Context and Goals

Design a language-agnostic module system supporting:

- Encapsulation and composition (`module`, `import`, `export`, `extender`).
- Language extension (adding `types`, `terms`, `literals`, `equations`, etc.).
- Foreign language block integration and expansion.

**Authoring surface:** Rholang in `.rho` files (not `.mts`).

---

## 1.1 Syntax and Semantics Representation Options

### ✅ Option A: GSLT (Global Syntax, Local Typing) + Macros

Syntax is global (a unified structural tree), but typing/semantics are resolved locally based on the active `extender` scope.

- **Pros:** Best support for polyglot/foreign blocks. Parse into a generic tree, then the `extender` assigns meaning.
- **Cons:** Syntax errors become type errors. Less precise parsing error messages.
- **Foreign blocks:** Parse into generic trees, passed to the foreign compiler/plugin.

### ✅ Option B: Extended BNF with Semantic Actions (Pratt/GLL)

Modules define grammar extensions mapped to AST nodes.

- **Pros:** Fast parsing. Familiar for engineers. Native fit for PraTTaIL/MeTTaIL.
- **Cons:** No proof of correctness. Semantic conflicts (e.g., overlapping rewrites) detected late.
- **Foreign blocks:** Opaque token streams and custom lexer modes (backtick islands).

### ❌ Option C: Higher-Order Logic (HOL) Embeddings

Composition as theorem proving in a proof assistant.

- **Pros:** Extreme rigor across language boundaries.
- **Cons:** High friction; proofs required to compose.

### ❌ Option D: Dependent Types / Coq (Rocq) Extraction

Modules as Coq functors/type classes; extract to implementation.

- **Pros:** Verified rewrites before compilation.
- **Cons:** Slow iteration; steep learning curve.

**Architectural recommendation:** **Option A blended with Option B** — BNF for the module spine (imports, exports, extenders) and `ExtenderExpr` blocks; language bodies resolved by the active `semantics` and extender context.

---

## 1.2 Pipeline (`.rho` entry file)

Each **`.rho` file** has the shape:

```bnf
File . BasicFile ::= [Import] Module ;
```

That is: a (possibly empty) list of imports, then **exactly one** `module { … }`.

### Step 1 — Parse

Lex and parse the `.rho` file into a surface AST (including foreign islands; see §5.2).

### Step 2 — Resolve imports

Build a **directed acyclic graph** of module dependencies. **Cycles are forbidden** (report error with import trace).

### Step 3 — Evaluate Rholang in dependency order

Evaluate the Rholang code in each graph vertex from **sources to sinks**.

Rholang is almost completely **asynchronous**, so for most cases evaluation order among independent vertices does not matter. A few **synchronous APIs** (e.g. a **registry** where lookup fails immediately if a name is missing, instead of blocking) behave better when dependencies are evaluated in **topological order** — so the compiler uses topo order by default.

### Step 4 — Assemble shipped languages

When a module contains `export language L = …` (`LanguageContent`), the **`LanguageExpr`** describes how to combine **`ExtenderContent`** blocks into a **single language spec**.

### Step 5 — Project (current backend)

For the moment, the compiler uses that assembled spec to:

1. Construct a Rust macro body analogous to `calculator.rs` or `rhocalc.rs`.
2. Generate the **parser** and **query engine** from that macro (existing MeTTaIL pipeline).

Later backends may project the same assembled spec differently.

---

## 2. Executive Summary

The **MeTTaIL Unified Specification (MUS)** is a build-time modularization framework. It moves away from monolithic `language! { … }` blocks in Rust toward layered **`.rho`** files.

**Key principles:**

1. **Extenders as functions on language specs** — An extender takes one or more language specs (presentations) and returns an extended spec. This is not the same as a programming functor; a GSLT-endofunctor picture may exist later, but how extenders act on **morphisms** between GSLTs is not yet understood.
2. **GSLT (global syntax, local typing)** — Generic structure where needed; semantics resolved in extender/`semantics` context.
3. **Build-time assembly** — Imports resolved, code evaluated, languages merged into **NTIR** (normalized theory IR) before backend projection.
4. **Island parsing** — Foreign/process code in labeled backtick regions (§5.2).

---

## 3. Core Architecture: The Layered Pipeline

The pipeline in §1.2 maps to these implementation phases:

| Phase | Responsibility | Artifact |
| :--- | :--- | :--- |
| **1. Parse** | `.rho` files; capture foreign islands. | Surface AST |
| **2. Resolve** | Import DAG; qualification; visibility; cycle check. | Resolved module graph |
| **3. Evaluate** | Run Rholang per vertex (topo order). | Evaluated module environments |
| **4. Assemble** | Apply extenders; `LanguageExpr` → single language spec. | **NTIR** |
| **5. Project** | Lower NTIR to backend (today: Rust `language!` + codegen). | Parser, query engine, etc. |

### 3.1 Normalized Theory IR (NTIR)

NTIR is the flattened language spec after extenders, exports, replacements, and unions are applied. It is **content-addressed (hashed)** for incremental rebuilds when imports are unchanged.

---

## 4. Syntax and Module Structure

### 4.1 File and module spine

```ebnf
File            ::= [Import] Module ;
Module          ::= "module" Ident "{" [ModifiedContent] "}" ;

Import          ::= "import" QuotedString ["as" Ident]
                  | "import" "{" ImportDescriptor+ "}" ;
ImportDescriptor ::= QuotedString ["as" Ident] ;

ModifiedContent ::= ["export"] Content ;
Content         ::= ExtenderDecl | LanguageDecl | SpaceDecl | NestedModule | ProcContent ;

ExtenderDecl    ::= "extender" Ident "(" [ExtenderArg] ")" "{" ExtenderExpr "}" ;
ExtenderArg     ::= Ident ;

LanguageDecl    ::= ["export"] "language" Ident "=" LanguageExpr ;
SpaceDecl       ::= ["export"] "space" Ident ":" LanguageExpr ;

LanguageExpr    ::= PathElement ("." PathElement)* ["(" LanguageExpr ("," LanguageExpr)* ")"] ;
```

### 4.2 ExtenderExpr (body of an extender)

```ebnf
ExtenderExpr    ::= ExtenderExpr "/" "\" ExtenderExpr          /* union */
                  | "{" ExtenderExpr "}"
                  | ExtenderExpr "types" "{" ... "}"
                  | ExtenderExpr "terms" "{" ... "}"
                  | ExtenderExpr "literals" "{" ... "}"
                  | ExtenderExpr "equations" "{" ... "}"
                  | ExtenderExpr "relations" "{" ... "}"
                  | ExtenderExpr "rewrites" "{" ... "}"
                  | ExtenderExpr "semantics" LanguageExpr
                  | "context" "{" String "}"
                  | "empty"
                  | Ident ["(" ExtenderExpr ("," ExtenderExpr)* ")"]  /* base or call */
                  ;
```

**`empty`** — Empty presentation (consistent keyword form; was `Empty` in early sketches).

**`semantics`** — Selects the implementation engine for this extender fragment, e.g. `semantics Rust` or a qualified `LanguageExpr` path.

**`context { String }`** — Host preamble for generated code (e.g. Rust `use` lines the embedded semantics depend on). The string uses a heredoc-style pattern:

```text
context {
  EOF,INSERT_HERE
  use std::collections::HashMap;
  use mettail_runtime::CanonicalBigInt;
  EOF
}
```

The compiler replaces **`INSERT_HERE`** with the code produced from assembling the relevant **`LanguageExpr`** (and extender bodies). That supplies an arbitrary fixed **context** around generated implementation code in whatever language the `semantics` target uses.

### 4.3 Extender semantics (not functors)

Extenders are **functions on language specs**:

- Declaration: `extender Complex(Base) { … }`
- Application: `Complex(CalcScalars())` inside a `LanguageExpr`
- At assembly time, the actual argument spec is substituted / merged into the extender body.

They are **not** described as functors unless and until a morphism-level story for GSLT composition is defined.

---

## 5. GSLT and Foreign Language Integration

### 5.1 Global syntax

Terms in extender blocks may be parsed into a **generic syntax tree (GST)** where the spine defers category assignment until normalization/evaluation in extender scope.

### 5.2 Island parsing (foreign blocks)

Islands are labeled with a **language** name (matching a `export language` or binding in scope).

#### Delimiters

**Single backticks** — short, often one-line:

```text
MyLang`some-mylang-term`
```

**Triple backticks** — multiline:

```text
MyLang```
  mylang
  code
  with
  newlines
```
```

#### Escaping (inside the island body)

The host lexer recognizes escapes so island text can contain metacharacters:

| Sequence | Meaning |
|----------|---------|
| `` \` `` | Literal backtick |
| `` \${ `` | Literal `${` (not interpolation) |
| `` \\ `` | Literal backslash |

Example:

```text
MyLang`some expression with \`backticks\`, \${dollar sign before brace}, and \\backslash\\`
```

#### Safe interpolation

Ideally, **unescaped** `${…}` in an island is parsed by the **MyLang** parser (not expanded as a raw host string). The parser builds a template with a **typed hole**: a function expecting a MyLang term that fits the production at that position.

That mirrors **safe templating** (e.g. Mike Samuel’s work on safe HTML): structured holes, not string injection, when host values are plugged in.

- **Host lexer:** classifies `` Lang`…` `` and `` Lang```…``` `` as island tokens.
- **Island processor:** delegates to the MyLang plugin; respects escapes and typed `${}` holes.
- **Nesting:** stack-based delimiter tracking for `` LangA` … LangB` … ` `` (§7.3).

---

## 6. Concrete Implementation Example: Polyglot Calculus

**Module 1: numeric base** (`numbers.rho`)

```text
module Numbers {
  export extender FloatBase() {
    empty
    semantics Rust
    types { ![f64] as Float }
    literals { Float ::= Regex("-?[0-9]+\\.[0-9]+") }
  }
}
```

**Module 2: complex extension** (`complex.rho`)

```text
import "numbers.rho" as Num

module Math {
  export extender Complex(Base) {
    { Base }
    types { ![mettail_runtime::Complex64] as Cmplx }
    terms {
      Cmplx ::= Base.Float ;
      Cmplx ::= Cmplx "+" Cmplx ;
    }
    rewrites {
      (a + bi) + (c + di) => (a+c) + (b+d)i ;
    }
  }
}
```

**Module 3: calculator composition** (`app.rho`)

```text
import "complex.rho" as M
import "numbers.rho" as N

module App {
  export language MyCalc = M.Complex(N.FloatBase())
  export space s: MyCalc
}
```

---

## 7. Stress-Testing and Resilience

### 7.1 Deep extender chain

**Scenario:** `L100 = E100(E99(…E1(Base)…))`.

- Normalization **O(total rules)**; renames batched per extender application.
- NTIR cache: fragment `E50` computed once if shared.

### 7.2 Diamond import conflict

**Scenario:** `C` imports `A` and `B`, both extending `Base` with conflicting replacements.

- **Policy:** **strict disjointness** — build error unless explicit replacement/override.

### 7.3 Polyglot island nesting

**Scenario:** `LangA` island contains `LangB` island contains `LangA`.

- Balanced `` ` `` / ``` `` tracking; escapes cannot break out of island boundaries.

### 7.4 Massive theory

**Scenario:** 10,000+ rewrite rules.

- NTIR → Ascent projection should use SCC-splitting and related optimizations so macro expansion stays within compiler limits.

---

## 8. Implementation Roadmap

### Phase 1: `mettail-spec` compiler (`.rho`)

- [ ] `.rho` parser (`[Import] Module` + `ExtenderExpr` grammar above).
- [ ] Import resolver and DAG validator (no cycles).
- [ ] Topological evaluation of module vertices.
- [ ] Extender application and `LanguageExpr` → NTIR.
- [ ] `context { … INSERT_HERE … }` + `semantics` lowering stub.

### Phase 2: Rust projection

- [ ] NTIR → `language!`-shaped Rust (calculator/rhocalc style).
- [ ] Parser and query-engine generation from projected macro.
- [ ] Rename/replacement parity tests vs monolithic specs.

### Phase 3: Polyglot islands

- [ ] Single- and triple-backtick lexing.
- [ ] Escapes `` \` ``, `` \${ ``, `` \\ ``.
- [ ] Typed-hole `${}` via language parser (safe templating).
- [ ] First non-trivial island plugin (e.g. Rholang process fragment).

---

## 9. Final Decision Table

| Feature | Selection | Rationale |
| :--- | :--- | :--- |
| **File format** | `.rho` | Rholang module entry; imports + one module |
| **Composition** | Build-time extender functions | Merge language specs before codegen |
| **Import graph** | DAG, topo evaluate | Registry and sync APIs need prior defs |
| **Grammar** | GSLT + BNF spine | Polyglot islands + precise module syntax |
| **Persistence** | NTIR (hashed) | Incremental builds |
| **Projection (now)** | Rust macro + parser/query | Reuse existing MeTTaIL codegen |
| **Host context** | `context { … INSERT_HERE … }` | `use` and deps for embedded semantics |
| **Conflict policy** | Strict disjointness | No silent label merge |
| **Islands** | `` Lang`…` `` and `` Lang```…``` `` | Short and multiline foreign code |

---
