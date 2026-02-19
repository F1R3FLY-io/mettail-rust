# Runtime query interpreter – design plan (2026-02-16)

## Goal

Support a REPL flow:

```
mettail> lang rhocalc (@languages/src/rhocalc.rs)
[language loaded]
rhocalc> step {term}
[term executed: ...]
rhocalc> query(result) <-- path(term, result), !rw_proc(result, _)
[computed: {normal forms}]
```

For every language we must support an **arbitrary rule** of the form:

- **Head**: `head(args) <--` (Ascent syntax; arrow `<--`).
- **Body**: A composite of relations from the language’s generated datalog (e.g. `path`, `rw_proc`, `proc`, `step_term` in rhocalc).
- **Result**: A `Vec` of tuples (one tuple per head-arity) corresponding to the head variables.

Parsing and syntax should be **canonical Ascent** where possible, using **ascent_syntax_export** for parsing and structure.

---

## Current state

### Engine PoC (from other workspace)

- **Location**: `engine/` (copied; ignore “holdea” naming).
- **Pipeline**: Parser (string → AST) → Planner (AST → plan) → Executor (plan + DataSource → results).
- **AST**: `Query { head: Atom, body: Vec<BodyAtom> }`; body atoms are Relation, Negation, If, FunctionCall.
- **Parser**: Custom lexer/parser for `head :- body.` (Prolog-style `:-` and `.`). Uses `holdea_core::Value` for constants.
- **Planner**: Left-to-right join order; Scan → Joins → FunctionCall → If (filters) → Negation (difference). Sound for safe, stratified queries.
- **Executor**: `DataSource::get_relation(name)` returns `Vec<(Vec<Value>, FactId)>`; uses operations (equijoin, difference, project, filter). Depends on `holdea_core::{Value, FactId}` and `engine::operations` (which use `ascent_run!` and `Value`).
- **Gaps here**: No `holdea_core` in this repo; engine `Cargo.toml` is minimal (no query deps). So the PoC is not buildable as-is; we treat it as the **reference design** and reimplement/adapt.

### MeTTaIL runtime and languages

- **Ascent run**: Each language runs `ascent_run! { include_source!(rhocalc_source); step_term(initial); #primary_relation(initial); }` and gets a struct with relations: `path`, `rw_proc`, `proc`, `step_term`, etc.
- **AscentResults**: Already has `custom_relations: HashMap<String, RelationData>` where `RelationData { param_types, tuples: Vec<Vec<String>> }`. Currently only **logic-block** relations (e.g. `path`, `trans`, `can_comm`) are extracted; **generated** relations like `rw_proc`, `proc`, `step_term` are **not** in `custom_relations`.
- **RelationData**: Tuples are stringified (e.g. `format!("{}", p)` for Proc). So “values” are strings for display; joining/filtering would be on those strings (correct for equality of terms if Display is injective enough; otherwise we need typed comparison later).

---

## Design plan

### 1. Parsing: Ascent-canonical via ascent_syntax_export

- **Input**: Single rule string, e.g. `query(result) <-- path(term, result), !rw_proc(result, _).`  
  The head relation may have any arity and types, e.g. `query(Name, Proc, Proc, Int) <-- ...`. We do **not** assume a fixed head signature; we infer it from the body.

- **Inferring head relation types from the body** (simple and correct):
  1. **Pre-parse the rule** (minimal pass): split on `<--` to get head and body; parse head as `rel(v1, v2, ...)` to get head relation name and head variable names; parse body into a list of atoms (relation name + argument lists), including negation. No full type information yet.
  2. **Schema**: The language exposes a **query schema**: for each relation name that may appear in the body, we have `param_types: Vec<String>` (e.g. `path` → `[Proc, Proc]`, `rw_proc` → `[Proc, Proc]`). This comes from the same place as `RelationData.param_types` (generated datalog / macro).
  3. **Type inference**: For each head variable `v`, find the **first positive** body atom in which `v` appears at some argument position `j`. That atom has relation name `R`; look up `schema(R)[j]` and assign that type to `v`. If a head variable never appears in any positive body atom, the query is unsafe (same as existing safety check); we can report that at this stage or at plan time.
  4. **Build the Ascent program**: Form the declaration `relation head(T1, T2, ...);` using the inferred types (e.g. `relation query(Proc);` or `relation query(Name, Proc, Proc, Int);`), then the rule string. Parse with `parse_ascent_program_text`; take the single rule from `program.rules`.

- **Mapping to engine AST**: Map Ascent AST → engine `Query`:
  - `RuleNode.head_clauses` → single `Atom` (relation name + variable/arg list).
  - `RuleNode.body_items` → `Vec<BodyAtom>`: each `BodyItemNode` → Relation (name + terms), or Negation(Relation), or If (from cond_clauses). Ascent’s body terms can be patterns (`?x`) or expressions; for this interpreter we restrict to **variable names** and **constants** (literals) where needed; ignore `include_source!` and complex expressions.
- **Output**: Engine `Query { head, body }` with variables and relation names. Use lowercase-variable convention to match engine (variables as in Ascent: identifiers in head/body).

**Correctness**: Same grammar as Ascent for rules; one rule only; reject programs with multiple rules or `include_source!` in the body. Head types are uniquely determined by body and schema (first positive occurrence per variable).

### 2. Schema: One unified set of all relations

- **Goal**: The ascent run has a single struct with one field per relation (both generated and from the logic block). We should expose **one set** of relations to the query layer: `AscentResults.custom_relations` should contain every relation in that struct, with `param_types` and `tuples`, so the query interpreter never has to distinguish “generated” vs “custom.”

- **Current gap**: Today only **logic-block** relations (from `language.logic.relations`) are extracted into `custom_relations`. The **generated** relations (from `generate_relations` + category rules: `proc`, `rw_proc`, `step_term`, `eq_*`, `*_contains`, etc.) exist on the ascent struct but are not inserted into `custom_relations`.

- **Plan – single source of truth**:
  1. **List all relations in the ascent program.** The macro already knows every relation that will be in the ascent run: (a) generated relations from `logic::relations::generate_relations` (and the same logic that produces category/projection relations), and (b) user-declared relations from `language.logic.relations`. Add a function (e.g. in `macros/src/logic/relations.rs` or `gen/runtime/language.rs`) that returns the **full list** of `(relation_name, param_types)` for the theory:
     - **Generated**: For each language type, category relation `type_lower(Type)`; eq relation `eq_type(Type, Type)`; rewrite relation `rw_type(Type, Type)`; fold relation if applicable; `step_term(primary)`; and for each collection constructor, `*_contains(Parent, Elem)`. Param types are type names (e.g. `Proc`, `Name`, `Int`).
     - **Custom**: From `language.logic.relations` (name + param_types).
  2. **Single extraction loop.** Change `generate_custom_relation_extraction` so it iterates over this **full list** (generated + custom), not only `language.logic.relations`. For each `(rel_name, param_types)` generate the same `custom_relations.insert(name, RelationData { param_types, tuples: prog.<rel_name>.iter()... })`. The ascent run struct already has a field for every relation, so `prog.<rel_name>` exists for each.
  3. **No duplicate names.** If the logic block declares a relation with the same name as a generated one (should be rare), define the rule: e.g. custom overrides generated, or the macro errors. Prefer: custom logic relation names must not clash with generated names (document reserved names).
  4. **Result**: After `run_ascent`, `custom_relations` is the single map for query schema and data: every relation name the user can use in a query is present, with `param_types` for type inference and `tuples` for execution.

- **Validation**: Before planning, check that every body relation name (after stripping negation) is in `custom_relations`; return a clear error if not.

### 3. Data source: Ascent results → rows

- **DataSource** implementation that backs the executor from **AscentResults** (and extended relations).
  - `get_relation(name)`:
    - Look up `name` in `custom_relations` (and any extended map).
    - Return rows as `Vec<Vec<String>>` (one row = one tuple of string values). No provenance/FactId.
- **Row value type**: Use **String** only for v1. Relation rows are already stringified in `RelationData.tuples`; the executor and operations use this single type for comparisons, joins, and projection. So:
  - **QueryValue = String** (type alias or newtype). Engine’s internal “Value” for the query pipeline is just `String`; no enum, no `FactId`, no provenance. Row type is `Vec<String>`; “result” type is `Vec<Vec<String>>`.
  - If we need provenance or richer values later, we can introduce a wrapper then; for correctness of joins and negation, string equality is sufficient.

**Correctness**: Rows must be in 1:1 correspondence with the ascent relation contents; column order = relation’s field order. Negation/difference uses equality on these values; string equality is consistent with “same term” if we ensure a single string representation per term.

### 4. Execution: Reuse planner + executor

- **Flow**: Parsed `Query` → **Planner::plan** → **Plan** → **Executor::execute(plan, data_source, functions, predicates)**.
- **DataSource**: Implement `AscentResultsDataSource` (or similar) that holds `AscentResults` and optional extended-relation map; `get_relation` returns rows as `Vec<Vec<String>>` (no FactId/provenance).
- **Functions/predicates**: For v1, support only **relation**, **negation**, and **if** (comparisons). No need for “let” or custom functions in the first cut; we can stub or leave empty registries.

- **Environment bindings (including current term)**  
  Queries must support the **same environment as term execution** in the REPL: short names that stand for (possibly complex) terms. This includes a special binding for the current stepped term.

  1. **Environment**: The REPL already has `list_env(env)` → `(name, display, comment)` and `pre_substitute_env(input, language, env)`, which replaces whole-word occurrences of env-bound names with their **display** string before parsing. Use the same mechanism for the **query string** before any parsing: run `pre_substitute_env(query_str, language, env)` so that e.g. `path(t, result)` when `t` is bound to `{ x | serv!(req) }` becomes `path({ x | serv!(req) }, result)` in the source that we then parse.
  2. **Current term**: The REPL sets a special environment entry **`current_term`** (or a configurable name) to the **display form of the current stepped term**. So after `step { ... }`, the REPL has a current term; when the user runs a query, the environment used for substitution includes `current_term = <display of that term>`. The user can write `path(current_term, result)` or bind it once and reuse, e.g. `save t` then `query(result) <-- path(t, result), !rw_proc(result, _)`. So:
     - Either the user uses the name `current_term` in the query and it is substituted like any other env name, or
     - The user runs `save term` (or similar) to put the current term in the env under `term`, then uses `term` in the query.
  3. **Order of operations**: (1) Take the raw query string. (2) Build env for substitution: normal REPL env + ensure `current_term` is set to the current stepped term’s display. (3) `pre_substitute_env(query_str, language, env)` → substituted string. (4) Parse (with type inference and ascent_syntax_export), plan, execute. No separate “implicit binding” step; env substitution covers both named bindings and `current_term`.

### 5. Return type: Vec of tuples

- **Executor** returns rows as `Vec<Vec<String>>` (no provenance). The **projection** step picks the head columns, so each row is the head tuple.
- **API**: `run_query(rule_str, ascent_results, env, current_term_display) -> Result<Vec<Vec<String>>, Error>`. So we return “vec of tuples” where each tuple is the head’s values (order = head args), each element a string (the term’s display form).

### 6. Remove “holdea” and fix engine

- **Remove**: All references to `holdea_core`, `FactId`, and “Holdea” in comments/docs. No provenance type in v1; row = `Vec<String>` only.
- **Value type**: Use **String** as the only row element type in the query pipeline (executor, planner, parser, operations). No enum, no FactId. Where the PoC had `Vec<Value>` or `(Vec<Value>, FactId)`, use `Vec<String>` and `Vec<Vec<String>>` for rows and results.
- **Engine Cargo.toml**: Add dependencies required for the query pipeline (parser, ast, planner, executor, operations). If operations (join, difference) use `ascent_run!`, they depend on `ascent` and operate on `Vec<String>` rows.

### 7. Phases and correctness

- **Phase 1 – Parse only**: Integrate ascent_syntax_export; infer head types from body + schema; parse single-rule string; map to engine `Query`; validate (single rule, no include_source). No execution yet.
- **Phase 2 – Schema and data**: Extend ascent result extraction so all needed relations (including `rw_proc`, `proc`, `step_term`) are available as `RelationData`. Implement DataSource over `AscentResults` (+ extended map) returning rows as `Vec<Vec<String>>`.
- **Phase 3 – Execute**: Wire Planner + Executor with the new DataSource (rows = `Vec<String>`, no FactId); apply env substitution (including `current_term`) before parse; return `Vec<Vec<String>>`. Ensure safety (safe rules, stratified negation) as in the PoC.
- **Phase 4 – REPL**: Hook `query(...) <-- ...` in the REPL: build env (REPL env + `current_term` = stepped term display), substitute query string via `pre_substitute_env`, parse, run query, print tuples.

**Correctness**:
- Parsing: Ascent grammar for one rule; reject invalid or multi-rule input.
- Safety: Only execute if query is safe (head vars in positive body) and stratified (no head in negation); engine already checks.
- Semantics: Joins and negation match the PoC (equijoin, set difference); filters (if) on comparisons. Relation contents must exactly reflect the ascent run.

---

## Crate structure and integration

### New crate: `mettail-query`

Introduce a dedicated crate for the query pipeline. The existing `engine/` PoC is **not** in the workspace today; rather than restructure engine in place, add a **new** crate `mettail-query` that either (a) is written from scratch following the design, or (b) is a copy of engine with holdea removed and String-based types, then refined. Recommendation: **new crate** so the PoC remains as reference; once stable, engine can be removed or folded in.

**Workspace**: Add `mettail-query` to root `Cargo.toml` `members` and `[workspace.dependencies]` (if needed for versioning).

**Layout**:

```
mettail-query/
├── Cargo.toml
├── src/
│   ├── lib.rs              # Public API: run_query, ParseError, etc.
│   ├── ast.rs              # Query, Atom, BodyAtom, Term, Variable (String-based)
│   ├── parse/
│   │   ├── mod.rs
│   │   ├── pre_parse.rs    # Minimal rule parser: head/body structure for type inference
│   │   └── ascent_parse.rs # Build program string, call ascent_syntax_export, map to AST
│   ├── schema.rs          # QuerySchema type (relation name → param_types); from RelationData
│   ├── planner.rs         # Plan, Step, etc. (row = Vec<String>)
│   ├── executor.rs        # Executor, DataSource trait (get_relation → Vec<Vec<String>>)
│   ├── operations/        # join, difference, project, filter (String rows; no provenance)
│   │   ├── mod.rs
│   │   ├── join.rs
│   │   ├── difference.rs
│   │   └── project.rs
│   └── data_source.rs     # AscentResultsDataSource(AscentResults), implements DataSource
```

**Dependencies** (`mettail-query/Cargo.toml`):

- `ascent_syntax_export` (parse Ascent rule)
- `ascent` (only if operations use `ascent_run!` for join/difference; otherwise pure Rust)
- `mettail-runtime` (for `AscentResults`, `RelationData`; used by `AscentResultsDataSource` and to derive schema)

**Public API** (conceptual):

- `parse_query(rule_str: &str, schema: &QuerySchema) -> Result<Query, ParseError>`
- `run_query(rule_str: &str, results: &AscentResults) -> Result<Vec<Vec<String>>, QueryError>`  
  (schema derived from `results.custom_relations` inside `run_query`, or passed in for clarity)
- `QuerySchema`: built from `AscentResults` by mapping each `custom_relations` entry to `(name, param_types)`.

**Schema source**: `QuerySchema` is derived from `AscentResults.custom_relations`: for each relation name, use `RelationData.param_types`. No separate “query schema” API on the language; once extraction is extended (Phase 2), all queryable relations are in `custom_relations` with `param_types`.

### Integration with the REPL

- **repl/Cargo.toml**: Add `mettail-query = { path = "../mettail-query" }` (or workspace dep). REPL already has `mettail-runtime`, `mettail-languages`; it gets `AscentResults` from state and env from state.

- **Query command**: When the user enters a line that is parsed as the query command (e.g. `query(result) <-- path(term, result), !rw_proc(result, _)`):
  1. **Require language and prior step**: If no language loaded or no `ascent_results()` in state, error: “Load a language and run step first.”
  2. **Build env for substitution**: Get `environment()` from state; ensure `current_term` is in the env: if there is a current term, add (or overwrite) binding `current_term` = `format!("{}", current_term)` (or use the same display the REPL uses). The REPL’s env is language-specific (`dyn Any`); the query layer only needs the **substituted string**, so the REPL calls `pre_substitute_env(query_str, language, env)` **before** calling into mettail-query. So: REPL builds env (including `current_term`), does substitution, then calls `mettail_query::run_query(substituted_str, state.ascent_results().unwrap())`.
  3. **Call**: `mettail_query::run_query(substituted_rule_str, ascent_results)`.
  4. **Schema**: `run_query` derives schema from `ascent_results.custom_relations` internally.
  5. **Output**: Print each tuple (e.g. one line per row, or formatted table).

- **Where substitution happens**: Substitution (env + `current_term`) is **REPL responsibility**; it requires `Language` and `env`. So the REPL has a helper that: takes raw query string, language, env, and optional “current term display”; augments env with `current_term` if provided; returns `pre_substitute_env(query_str, language, env)`. Then REPL calls `mettail_query::run_query(substituted, results)`.

- **State**: `ReplState` already has `ascent_results: Option<AscentResults>` and `ascent_results()`. No change needed; the query command reads from it.

### Summary of integration points

| Component    | Responsibility |
|-------------|----------------|
| **mettail-query** | Parse (with schema), plan, execute; `DataSource` over `AscentResults`; return `Vec<Vec<String>>`. |
| **repl**          | Parse “query” command; build env (REPL env + `current_term`); substitute query string; call `run_query`; print results. |
| **mettail-runtime** | `AscentResults`, `RelationData`; no change except Phase 2 (extend extraction). |
| **macros**        | Implement unified relation extraction: full list (generated + logic-block), single loop into `custom_relations`. |

---

## Considerations remaining

1. **Pre-parser for type inference**  
   We need a minimal parser that, given a rule string, returns head (relation name + variable names) and body (list of atoms with relation names and argument lists, including negation). It must handle Ascent syntax (`<--`, `,`, `!`, `_`). No types or schema required. Options: small hand-written lexer/parser, or a regex-based split and then parse head/atoms. Must be robust to whitespace and nested parens in terms (e.g. `path(foo(1), x)`). Document the grammar for this pre-parse (e.g. “head is rel(v1, v2, ...); body is comma-separated atoms; atom is optional `!` then rel(args)”).

2. **Unified relation extraction (macro)**  
   Implement the plan in **§2 Schema**: add a function that lists all relations in the ascent program (generated + logic-block) with `(name, param_types)`; then have `generate_custom_relation_extraction` iterate that full list and generate `custom_relations.insert(...)` for each. Ensure generated relation names are documented (or reserved) so user logic does not clash.

3. **Wildcard `_` in body**  
   Body atoms can use `_` (e.g. `!rw_proc(result, _)`). The pre-parser and Ascent parse must treat `_` as a distinct placeholder (not a variable). For type inference we don’t need a type for `_`. For the engine AST we can represent it as a special “wildcard” term so the planner doesn’t bind a column for it. Ensure the Ascent AST mapping produces a Term variant for wildcard and the planner/executor handle it (e.g. join/diff only on non-wildcard positions).

4. **Constants in query**  
   Body terms can be constants (e.g. literals). Pre-parser and full parse must recognize them; type inference may need to allow “constant” as a type or skip that position for head inference. Engine already has `Term::Constant(Value)`; with String-only, constants are `Term::Constant(s)` where `s` is the string form. Ensure constant parsing in the Ascent rule (numbers, quoted strings, etc.) produces a single canonical string for the executor.

5. **If-clauses (comparisons)**  
   v1 supports `if` with comparisons. The executor’s filter step needs to compare row values (strings). For string comparison, lexicographic order is fine for `>=`, `<=`, etc.; for equality we already use string eq. Predicate registry can be empty if we only support comparison filters and implement them inside the executor. No dependency on a separate “holdea” predicate system.

6. **Operations without ascent_run!**  
   The current engine’s join/difference use `ascent_run!` and `Value`. If we switch to `Vec<String>`, we can either (a) rewrite those operations to use `ascent_run!` with `Vec<String>` (ascent supports any cloneable type), or (b) implement join/difference in pure Rust (nested loops or sort-merge). (a) keeps one source of truth; (b) avoids ascent dependency in mettail-query. Design choice: prefer (b) for simplicity and to keep mettail-query’s dependency surface small, unless profiling shows need for ascent-backed join.

7. **Error reporting**  
   Parse errors (unknown relation, unsafe query, non-stratified) should point at the user’s rule string. ascent_syntax_export returns `syn::Error` with span info; we may lose span when we build the program string. Consider keeping a single-rule parse path that preserves offsets, or report “relation X not in schema” / “variable Y unbound” without line numbers for v1.

8. **REPL “query” command shape**  
   Use Ascent-style head with parens: **`query(arg1, ..., argN) <-- body.`** The REPL command parser must recognize this shape and pass the full rule string (including `query(...) <-- ...`) to the query layer.

9. **current_term when no step yet**  
   If the user types a query before running `step`, we have no `ascent_results` and possibly no current term. Fail with “Run step first” and optionally “No current term for env binding `current_term`.” If they have run step, `ascent_results` and current term are set; we inject `current_term` into env for substitution.

10. **Testing**  
    Unit tests: pre-parse, type inference, parse with ascent_syntax_export, planner, executor with a small in-memory DataSource. Integration test: run_query with a hand-built AscentResults (custom_relations with path, rw_proc). No REPL required for engine tests.

---

## Summary

| Area | Decision |
|------|----------|
| **Parse** | Pre-parse rule to get head/body; infer head relation types from body + schema (first positive occurrence per head var); build `relation head(T1,...);` + rule; parse with ascent_syntax_export; map to engine Query. |
| **Schema** | One set: all relations (generated + logic-block) in `custom_relations`. Macro: list full relation set (from generate_relations + logic.relations), then single extraction loop. Schema = custom_relations (param_types). Validate body relations before planning. |
| **Data** | DataSource over AscentResults; rows = `Vec<Vec<String>>` (RelationData tuples as string rows); no FactId, no provenance. |
| **Value type** | QueryValue = String only for v1. |
| **Environment** | Same as term execution: pre_substitute_env(query_str, language, env) before parsing; env includes REPL bindings + `current_term` = current stepped term display. |
| **Return** | Vec of head tuples: `Vec<Vec<String>>`. |
| **Engine** | Remove holdea and FactId; rows and results use `String` only; add deps; keep planner/executor/operations logic. |
| **Crate** | New crate `mettail-query`: ast, parse (pre_parse + ascent_parse), schema, planner, executor, operations, data_source. Deps: ascent_syntax_export, mettail-runtime; optional ascent if operations use it. |
| **Integration** | Add `mettail-query` to workspace; repl depends on it. Query command: substitute env + current_term in REPL, call `run_query(substituted, ascent_results)`; schema from results. |

Remaining considerations are listed in **Considerations remaining** (pre-parser, unified extraction, wildcards, constants, if-clauses, operations impl, errors, REPL command shape, current_term guard, testing).
