# Module System Initial Design: The MeTTaIL Unified Specification (MUS)

**Date:** May 2026

---

## 0. Context and Goals
Design a language-agnostic module system supporting:
- Encapsulation and composition (`module`, `import`, `export`, `extender`).
- Language extension (adding `types`, `terms`, `literals`, `equations`, etc.).
- Foreign language block integration and expansion.

## 0.1 Pipeline: Parse and Dependency Graph

The pipeline begins by parsing an input **`.rho`** file. The surface grammar for a file is:

```ebnf
BasicFile ::= [Import] Module ;
```

- **`[Import]`** — zero or more import declarations (may be empty).
- **`Module`** — exactly one module definition.

The parser produces a **surface AST** for that file. The resolver then walks all `import` paths, loads each referenced `.rho` file recursively, and builds a **directed acyclic graph (DAG)** of module dependencies. **Cycles are forbidden**; any import cycle is a build-time error.

Subsequent phases (normalize, project) operate on the resolved graph and merged theories—not on raw import text alone.

### Syntax & Semantics Representation Options
### ✅ Option A: GSLT (Global Syntax, Local Typing) + Macros
Syntax is global (a unified structural tree), but typing/semantics are resolved locally based on the active `extender` scope.
- **Pros:** Best support for polyglot/foreign blocks. You parse everything into a generic tree (like S-expressions or generic AST), then the `extender` assigns meaning.
- **Cons:** Syntax errors become type errors. Less precise parsing error messages.
- **Foreign Blocks:** Trivial. Foreign blocks parse into generic trees, passed to the foreign compiler/macro.

### ✅ Option B: Extended BNF with Semantic Actions (Pratt/GLL)
Modules define pure grammar extensions mapped to AST nodes.
- **Pros:** Fast parsing. Familiar for engineers. Native fit for PraTTaIL/MeTTaIL.
- **Cons:** No proof of correctness. Semantic conflicts (e.g., overlapping rewrites) detected late (runtime).
- **Foreign Blocks:** Handled via opaque token streams and custom lexer modes (e.g., backtick interpolation).

### ❌ Option C: Higher-Order Logic (HOL) Embeddings
Syntax and semantics defined as mathematical theories in a HOL framework (like Isabelle).
- **Pros:** Extreme rigor. Module composition is theorem proving (guarantees properties across language boundaries).
- **Cons:** High friction. Requires users to write proofs to compose languages.
- **Foreign Blocks:** Embedded via semantic translation into the base logic, losing surface syntax nuances.

### ❌ Option D: Dependent Types / Coq (Rocq) Extraction
Modules are Coq functors or type classes. Syntax is verified, then extracted to Rust.
- **Pros:** Formal verification of rewrites and equations before compilation. Excellent for verifying optimizations.
- **Cons:** Slow iteration loop. Extraction can be bulky. Steep learning curve.
- **Foreign Blocks:** Requires defining a formal semantics for the foreign language in Coq, which is often infeasible.


**Architectural Recommendation:** **Option A (GSLT + Macros)** blended with **Option B**. Use BNF for the spine of the module system (imports, exports) but treat language bodies (`{...}`) as generic syntax trees resolved by the `semantics` engine.

## 1. Executive Summary
The **MeTTaIL Unified Specification (MUS)** provides a language-agnostic, build-time modularization framework. It moves away from monolithic `language! { ... }` blocks in Rust toward a layered hierarchy of `.mts` (MeTTaIL Spec) files. 

**Key Principles:**
1.  **Functor-based Composition:** Theories are "extenders" (functors) that transform base languages.
2.  **GSLT (Global Syntax, Local Typing):** Syntax is captured generically; semantics (typing, rewrites) are resolved by the active theory context.
3.  **Build-time Normalization:** Modules are resolved, merged, and normalized into a monolithic `LanguageDef` before Rust compilation, ensuring zero runtime overhead and optimal Ascent performance.
4.  **Island Parsing:** Foreign language blocks are integrated via explicit lexical boundaries.

---

## 2. Core Architecture: The Layered Pipeline

The system operates in four distinct phases:

| Phase | Responsibility | Artifact |
| :--- | :--- | :--- |
| **1. Parse** | Parse each `.rho` file as `BasicFile` (`[Import] Module`); capture foreign blocks. | Surface AST |
| **2. Resolve** | Build import DAG (acyclic; cycles = error); name qualification; visibility checks. | Resolved AST |
| **3. Normalize** | Functor application; rename propagation; union merging. | **Normalized Theory IR** |
| **4. Project** | Lowering to `LanguageDef` for existing `macros` crate. | Rust Source |

### 2.1. The Normalized Theory IR (NTIR)
The NTIR is the "Source of Truth." It is content-addressed (hashed) for incremental builds. It contains the flattened set of all types, terms, and rules after all renames and replacements have been applied.

---

## 3. Syntax & Module Structure

### 3.1. EBNF (Spine)
```ebnf
BasicFile       ::= [Import] Module ;
Module          ::= "module" Ident "{" [ModifiedContent] "}" ;
ModifiedContent ::= ["export"] (Extender | Language | Space | NestedModule) ;

Import          ::= "import" QuotedString ["as" Ident] ["{" [Ident] "}"] ;

Extender        ::= "extender" Ident "(" [Args] ")" "{" ExtenderBody "}" ;
ExtenderBody    ::= [BaseLang] (Semantics | Types | Terms | Literals | Equations | Rewrites) ;

Language        ::= "language" Ident "=" LanguageExpr ;
LanguageExpr    ::= Path ["(" [LanguageExpr] ")"] ;
```

### 3.2. Functor Semantics (Extenders)
Extenders are the primary unit of reuse.
- `extender Complex(Base) { ... }`
- When applied, `Base` is substituted with the argument language's NTIR.
- Local definitions can reference `Base.Category` to maintain structural integrity.

---

## 4. GSLT & Foreign Language Integration

### 4.1. Global Syntax
All terms in the module system are parsed into a **Generic Syntax Tree (GST)**. The GST preserves the structure and labels but defers "typing" (category assignment) until the normalization phase.

### 4.2. Island Parsing (Foreign Blocks)
Foreign blocks are captured using triple-backtick delimiters with a language label.
```text
let term = MyLang`5 + 5` in { ... }
```
- **Host Lexer:** Identifies `MyLang```...``` ` as a `ForeignIsland` token.
- **Host Parser:** Treats the island as an opaque blob to be passed to the `MyLang` plugin.
- **Interpolation:** `${expr}` is parsed by the *host* and passed as a structured segment to the island processor.

---

## 5. Concrete Implementation Example: Polyglot Calculus

**Module 1: Numeric Base**
```text
// numbers.mts
module Numbers {
  export extender FloatBase() {
    semantics Rust.Native
    types { ![f64] as Float }
    literals { Float ::= Regex("-?[0-9]+\.[0-9]+") }
  }
}
```

**Module 2: Complex Extension**
```text
// complex.mts
import "numbers.mts" as Num

module Math {
  export extender Complex(Base) {
    { Base }
    types { ![mettail_runtime::Complex64] as Cmplx }
    terms {
      Cmplx ::= Base.Float ; // Injection
      Cmplx ::= Cmplx "+" Cmplx ;
    }
    rewrites {
      (a + bi) + (c + di) => (a+c) + (b+d)i ;
    }
  }
}
```

**Module 3: Calculator Composition**
```text
// app.mts
import "complex.mts" as M
import "numbers.mts" as N

module App {
  export language MyCalc = M.Complex(N.FloatBase())
  export space s: MyCalc
}
```

---

## 6. Stress-Testing & Resilience

To ensure the MUS is "Principal Architect Grade," it must survive the following scenarios:

### 6.1. The "Deep Functor" Stress Test
**Scenario:** An extender chain 100 levels deep: `L100 = E100(E99(...E1(Base)...))`.
- **Requirement:** Normalization must be $O(N)$ where $N$ is the total number of rules. Renames must be batched and applied in a single AST pass per theory, not iteratively.
- **Resilience:** The NTIR caching must ensure that `E50` is only computed once even if used in multiple branches.

### 6.2. The "Diamond Import" Conflict
**Scenario:** `Theory C` imports `Theory A` and `Theory B`, both of which extend `Base`.
- **Requirement:** The system must detect if `A` and `B` have conflicting replacements for the same `Base` constructor.
- **Policy:** **Strict Disjointness.** Unless an explicit `replacement` or `override` is specified, label collisions result in a build-time error.

### 6.3. The "Polyglot Recursion" Stress Test
**Scenario:** `LangA` has an island of `LangB`, which has an island of `LangA`.
- **Requirement:** The parser must handle arbitrary nesting of backticks and balanced delimiters.
- **Resilience:** The "Island Parser" must use a stack-based delimiter tracker that is agnostic to the content, preventing "interpolation escape" attacks.

### 6.4. The "Massive Theory" Stress Test
**Scenario:** A theory with 10,000+ rewrite rules (e.g., a full CPU ISA spec).
- **Requirement:** The NTIR projection to Ascent must utilize the "SCC-splitting" optimization (documented in `ascent_generation.md`) to prevent the Rust compiler from hitting recursion limits during macro expansion.

---

## 7. Implementation Roadmap

### Phase 1: The `mettail-spec` Compiler
- Implement the `.mts` parser (using a simplified PraTTaIL grammar).
- Build the Import Resolver and DAG validator.
- Implement the "Extender Application" logic (NTIR generation).

### Phase 2: Macro Integration
- Create the `mettail_modules!` proc-macro.
- Hook `mettail-spec` into the `build.rs` workflow.
- Ensure `LanguageDef` projection handles renames correctly.

### Phase 3: Polyglot Islands
- Implement backtick lexing in PraTTaIL.
- Add `${}` interpolation support to the generic syntax tree.
- Build the first "Semantic Plugin" for a foreign language (e.g., RhoCalc).

---

## 8. Final Decision Table

| Feature | Selection | Rationale |
| :--- | :--- | :--- |
| **Composition** | Build-time Functors | Maximum performance; zero runtime cost. |
| **Grammar** | GSLT (Global Syntax) | Enables polyglot/foreign blocks. |
| **Persistence** | NTIR (Hashed) | Fast incremental builds for deep stacks. |
| **Integration** | `mettail_modules!` | Seamless Rust ergonomics. |
| **Conflict** | Strict Disjointness | Safety over "magic" merging. |
