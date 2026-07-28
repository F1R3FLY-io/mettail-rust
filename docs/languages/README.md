# Language Specification References

Last updated: 2026-07-27

One page per bundled `language!` specification. Each page walks its `languages/src/*.rs` block
**component by component** — what every fragment of the DSL means, what the macro generates from
it, and how the result executes — with every claim traced to a file and line in the parser, the
code generator, or the *actual generated output* under `target/generated/<lang>/`.

**What this suite is for.** The DSL is dense: a twelve-line block can expand into thirty-eight
generated modules. Reading a specification therefore requires knowing three things at once — the
surface grammar of the DSL, the semantics of the theory being declared, and the machinery each
clause switches on. The other suites cover those axes generically; these pages tie them to one
concrete, complete specification each, so you can read a real block start to finish without
guessing.

**What this suite is not.** It is neither a DSL grammar reference nor a compiler-internals
document. See [Related documents](#related-documents) for those.

---

## The roster

Every production specification in `languages/src/`. Four are transcriptions of the GSLT omnibus
paper's conformance ladder (their module headers cite `omnibus.tex` line ranges); four are native
MeTTaIL languages.

| Language | Source | Lines | Sorts | What the specification exercises | Page |
|---|---|---:|---|---|---|
| **Lambda** | `languages/src/lambda.rs` | 34 | `Term` | binders and higher-order abstract syntax, β-reduction via the `eval` meta-operator, congruence rules as reduction contexts | ✅ [lambda.md](lambda.md) |
| **Monoid** | `languages/src/monoid.rs` | 94 | `M` | GSLT omnibus **L2** — the *equations* rung: `Assoc` / `UnitL` / `UnitR` with an empty `rewrites` block; the quotient an equational theory induces | ☐ not yet written |
| **Json** | `languages/src/json.rs` | 267 | `Value`, `Field`, `![bool] as Bool`, `![CanonicalBigRat] as BigRat`, `![str] as Str` | GSLT omnibus **L1** — the *types + terms* rung: native payload carriers, `literals { }` lexer classes, collection sorts | ☐ not yet written |
| **Turing** | `languages/src/turing.rs` | 191 | `Config`, `Tape`, `State`, `Sym`, `![u32] as UInt32` | GSLT omnibus **L9** — the paper's deliberate *non*-example: a single-tape machine as a GSLT, and why that presentation is unsatisfying | ☐ not yet written |
| **Pi** | `languages/src/pi.rs` | 233 | `Proc`, `Name` | GSLT omnibus **L11** — the π-calculus: name binders, `HashBag` parallel composition with `*sep`, replication, and a documented surface delta (literal-led binder prefixes) | ☐ not yet written |
| **Ambient** | `languages/src/ambient.rs` | 75 | `Proc`, `Name` | Cardelli–Gordon mobile ambients: six structural-congruence *equations* with freshness premises (`x # N`), scope extrusion over an AC bag, and three capability rewrites with congruences | ☐ not yet written |
| **Calculator** | `languages/src/calculator.rs` | 789 | `Proc` plus the native numeric tower (`Int`, `UInt32`, `BigInt`, `BigRat`, `Fixed`, `Float`, `Bool`, `Str`) | `literals { }` with regex patterns and `eval` blocks, native `![…]` folds, numeric casts, `fold` / `step` evaluation modes | ☐ not yet written |
| **Rholang** | `languages/src/rholang.rs` | 3 242 | `Proc`, `Name`, `InputBind`, `ForRow` plus the native tower | the flagship: COMM as a rewrite, multi-binder receives, collections, guards, `options { }`, and hand-written `logic { }` | ☐ partially covered by [`../examples/rholang/01-language-spec.md`](../examples/rholang/01-language-spec.md) |

Composition fixtures (`languages/src/composition/`) and the Rholang support modules
(`languages/src/rholang/`) are not specifications in their own right; composition is documented in
[`../design/exploring/theory_composition.md`](../design/exploring/theory_composition.md) and
[`../../prattail/docs/design/architecture-overview.md`](../../prattail/docs/design/architecture-overview.md).

---

## Where to start

**If you have never read a `language!` block:** start with [lambda.md](lambda.md). It is the
smallest complete specification in the tree — one sort, two constructors, no equations, four
rewrite rules — and every construct it uses recurs, at greater scale, in every other language. Its
§5 (`terms`) and §7 (`rewrites`) are the reusable parts; read those once and the other pages become
skimmable.

**If you are looking for one specific mechanism**, the shortest path is:

| You want to understand… | Read |
|---|---|
| binders, scopes, α-equivalence, capture-avoiding substitution | [lambda.md §5.1](lambda.md#51-lam--xbodyterm---term---lam--x--body--term), [§7.1](lambda.md#71-beta----app-lam-fun-arg--eval-fun-arg) |
| how a rewrite rule's premises work | [lambda.md §7.2](lambda.md#72-the-three-congruence-rules) |
| what an *equation* is, versus a *rewrite* | [lambda.md §6](lambda.md#6-equations----the-equational-theory-e) |
| what the macro actually generates, and where it lands | [lambda.md §2](lambda.md#2-what-language-is-and-what-it-produces) |
| the DSL's full surface grammar, block by block | [`../../readme_dev.md`](../../readme_dev.md) §"Guide: defining a language theory" |

---

## The shape of every specification

For orientation while reading any page in this suite. The block order is fixed by
`impl Parse for LanguageDef`; optional blocks may be omitted entirely.

```text
language! {
    name: YourLanguage,
    extends:  [Base],   /* optional — full inheritance: types, terms, equations, rewrites, logic, guards */
    includes: [Other],  /* optional — grammar only */
    mixins:   [Frag],   /* optional — fragment grammar */
    options   { … },    /* optional — parser tuning (beam_width, dispatch, …) */
    types     { … },    /* the sorts: algebraic, native-payload, or collection */
    literals  { … },    /* optional — lexer patterns + eval blocks for literal tokens */
    terms     { … },    /* the signature and the concrete syntax */
    guards    { … },    /* optional — declared predicate dispatch */
    equations { … },    /* undirected laws */
    rewrites  { … },    /* directed reduction */
    logic     { … },    /* optional — hand-written Datalog relations */
}
```

The two rule productions, which account for most of any specification's bulk:

```text
terms:      Label . term_context |- concrete_syntax : Category [ ![rust] ] [ fold | step ] [ right ] [ prefix(N) ] [ canonical ] ;
equations:  Name  . type_context | premises |- lhs_pattern  =  rhs_pattern ;
rewrites:   Name  . type_context | premises |- lhs_pattern  ~>  rhs_pattern ;
```

`|-` is the turnstile: in `terms` it separates metasyntax (arguments and their binding structure)
from object syntax (what a programmer types); in `equations` and `rewrites` it separates the
contexts from the rule proper. Rule patterns are **abstract-syntax S-expressions**
`(Constructor arg₁ arg₂ …)`, never the concrete syntax declared by `terms`.

---

## Conventions for pages in this suite

Each page should carry, in this order:

1. **Header** — subject file, audience, and the method by which claims were verified.
2. **A table of contents** with working in-document anchors.
3. **A notation table** defining every symbol, acronym, and key term before first use.
4. **One section per block** of the specification, in the order the macro parses them, with a
   fragment-by-fragment table for each rule form the language introduces.
5. **The specification as a whole** — the $`(\Sigma, E, R)`$ triple it denotes, a concrete-syntax
   cheat-sheet drawn from a *test-pinned* corpus (never invented), and at least one worked
   reduction.
6. **A provenance table** — every claim mapped to `file:line` in the parser, the generator, the
   generated output, or a test.
7. **Gotchas** — the misreadings the page exists to prevent.

### Diagramming policy

PlantUML only (`figures/*.puml`), rendered to SVG and committed alongside the source:

```sh
plantuml -tsvg docs/languages/figures/*.puml
```

Figure files are prefixed with their language (`lambda-beta-firing.puml`) so the directory stays
navigable as pages are added. Use the house palette — `#DBEAFE` structure, `#DCFCE7` syntax and
surface, `#FCE7F3` rewrites and the host, `#EDE9FE` engine internals, `#FEF3C7` metadata and
equations, `#FEE2E2` failure — and PlantUML's `<latex>…</latex>` for mathematics in labels rather
than unicode literals.

### Mathematics in prose

GitHub-flavored Markdown delimiters: inline math is a backtick span wrapped in dollar signs, and
display math is a fenced block with the `math` info-string. Bare `$…$` and `$$…$$` are forbidden —
GitHub's CommonMark pass strips backslash escapes before MathJax parses them. `validate.sh`
enforces this.

### Validation

```sh
docs/languages/validate.sh
```

Checks fenced-block balance, math-symbol and math-delimiter conformance, PlantUML source parsing
and rendered-asset integrity, relative-link and in-document-anchor resolution, roster coverage
(every page listed here), and that every page names a specification source that still exists.

### Adding a page

1. Write `docs/languages/<module>.md`, where `<module>` matches `languages/src/<module>.rs`.
2. Put its figures in `figures/<module>-*.puml` and render them to SVG.
3. Add the page to [the roster](#the-roster) — `validate.sh` fails if it is missing.
4. Flip the language's row from ☐ to ✅.
5. Run `docs/languages/validate.sh`.

---

## Related documents

| Document | What it covers that this suite does not |
|---|---|
| [`../../readme_dev.md`](../../readme_dev.md) | the DSL block-by-block *reference*: syntax, semantics, goal, and which codegen path consumes each block |
| [`../../prattail/docs/usage/grammar-features.md`](../../prattail/docs/usage/grammar-features.md) | the complete grammar-feature catalogue: prefix/infix/mixfix rules, associativity, binding powers, collections |
| [`../architecture/rho-native-integration/27-oslf-language-to-rholang-compilation.md`](../architecture/rho-native-integration/27-oslf-language-to-rholang-compilation.md) | how a `language!` specification is compiled into an installed Rholang program via the set automaton |
| [`../architecture/rho-native-integration/19-in-rho-binder-beta-substitution.md`](../architecture/rho-native-integration/19-in-rho-binder-beta-substitution.md) | the in-Rho de-Bruijn substitution cascade that executes binder β |
| [`../architecture/dovetail/README.md`](../architecture/dovetail/README.md) | the rewrite engine itself: e-graphs, saturation, extraction, reports |
| [`../design/exploring/theory_composition.md`](../design/exploring/theory_composition.md) | `extends` / `includes` / `mixins` and the theory of language composition |
| [`../examples/rholang/`](../examples/rholang/) | the Rholang walk-through: specification, macro expansion, lexer, parser, codegen, evaluation |
| [`../design/guards-block.md`](../design/guards-block.md) | the optional `guards { }` block and predicate dispatch |
