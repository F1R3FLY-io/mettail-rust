# Unification Premises for Pattern-Based COMM

## Goal

Enable relation-based pattern matching in rewrite premises so COMM-style rules can be guarded by unification:

```text
Comm . | pattern unifies received
     |- (PPar {(PFor n pattern body), (POutput n received), ...rest})
     ~> (PPar {(apply_pattern pattern received body), ...rest})
```

The intent is to keep "does this match?" inside Ascent/Datalog fixpoint computation, while keeping binding extraction and substitution in deterministic Rust runtime code.

## Current Baseline

Today, premise relations already participate in fixpoint scheduling via generated relation lookups. In particular:

- Congruence premise `S ~> T` is lowered to a relation query (`rw_<cat>(S, T)`).
- Premise lowering is handled through `Premise -> Condition` and `generate_condition_clauses` in `macros/src/logic/rules.rs`.
- Ascent evaluates premise relations to fixpoint before dependent rewrites fire.

This is exactly the mechanism needed for unification premises: add `unifies_<cat>(pattern, value)` and reuse the same condition-generation plumbing.

## Design Overview

The feature is split into two responsibilities:

1. **Datalog relation (`unifies_`*)** answers whether a pattern unifies with a value.
2. **Runtime function (`apply_pattern`)** computes bindings and performs substitution once a rule fires.

This mirrors existing architecture where relations express logical preconditions and Rust handles deterministic term construction/evaluation.

## Proposed Semantics

For each category `Cat` (for example `Proc`, `Name`), introduce:

```text
relation unifies_cat(Cat, Cat);
```

Read as: "`lhs` unifies with `rhs`".

High-level semantics:

- Constructor-to-constructor unification succeeds when labels match and all corresponding child positions unify.
- Pattern free variables in designated "pattern position" unify with any value at that position.
- Collection constructors unify via multiset matching (see dedicated section).
- Optional equational closure may be layered so unification sees equation-equivalent values.

## Macro and Runtime Changes


| File                                    | Change                                                                                                         |
| --------------------------------------- | -------------------------------------------------------------------------------------------------------------- |
| `macros/src/ast/language.rs`            | Add `Premise::Unification { pattern, value }` (or similarly named fields).                                     |
| `macros/src/ast/grammar.rs`             | Add/extend `TermParam` metadata to mark pattern-binder positions (if needed by codegen).                       |
| `macros/src/logic/relations.rs`         | Emit `unifies_<cat>` declarations for eligible categories.                                                     |
| `macros/src/logic/unification.rs` (new) | Auto-generate structural unification rules per constructor (parallel to congruence generation style).          |
| `macros/src/logic/rules.rs`             | Lower `Premise::Unification` to `Condition::EnvQuery`-like relation clause generation (new condition variant). |
| `macros/src/gen/term_ops/`              | Add `apply_pattern` helper for binding extraction + multi-substitution.                                        |
| `languages/src/rhocalc.rs`              | Add pattern-aware `PFor` form and COMM rewrite using unification premise.                                      |


## AST and Parsing

Extend premise syntax with an explicit unification form. Exact concrete syntax can follow one of:

- `pattern ~? received`
- `unifies(pattern, received)`
- `pattern unifies received`

Selection criteria:

- Must be unambiguous with existing `~>` and `=` judgements.
- Must parse to two identifiers/terms that are already bound in the rule context.
- Should preserve existing parser constraints for premise atoms and conjunctions.

AST addition (illustrative):

```rust
pub enum Premise {
    Freshness(FreshnessCondition),
    Congruence { source: Ident, target: Ident },
    RelationQuery { relation: Ident, args: Vec<Ident> },
    ForAll { collection: Ident, param: Ident, body: Box<Premise> },
    Unification { pattern: Ident, value: Ident },
}
```

Internal `Condition` should gain a matching variant so `generate_condition_clauses` can emit `unifies_<cat>(pattern, value)`.

## Relation Declaration and Generation

In logic relation declaration generation (`macros/src/logic/relations.rs`), emit:

- `relation unifies_proc(Proc, Proc);`
- `relation unifies_name(Name, Name);`
- etc., for categories where matching is meaningful.

Generation policy should mirror existing category filters used in congruence/equations codegen to keep behavior deterministic and compile-time bounded.

## Auto-Generated Structural Unification Rules

New module `macros/src/logic/unification.rs` generates Ascent rules for each constructor shape.

### 1) Ground constructor rule

For nullary constructors, emit direct self-match rules.

### 2) Recursive constructor rule

For constructor `C` with child fields `(f1, ..., fn)`:

```text
unifies_cat(a, b) <--
  cat(a), cat(b),
  if let Cat::C(...f1a..., ...fna...) = a,
  if let Cat::C(...f1b..., ...fnb...) = b,
  unifies_child1(f1a, f1b),
  ...
  unifies_childN(fna, fnb);
```

Where each `unifies_childK` dispatches to the corresponding category relation (`unifies_proc`, `unifies_name`, etc.).

### 3) Pattern variable wildcard rule

For designated pattern-variable positions, emit rules that allow wildcard matching:

```text
unifies_cat(a, b) <-- cat(a), cat(b), if a.is_free_var();
```

Important: this must only apply in pattern role, not symmetrically in all contexts, otherwise relation meaning degrades to near-universal matching for terms containing free vars.

### 4) Optional equational closure

If equational matching is desired, add closure rules such as:

```text
unifies_cat(a, c) <-- eq_cat(a, b), unifies_cat(b, c);
unifies_cat(a, c) <-- unifies_cat(a, b), eq_cat(b, c);
```

This yields equational pattern matching while preserving relation-based guards.

## COMM Integration

COMM rule shape:

1. LHS identifies `(PFor n pattern body)` and `(POutput n received)` in parallel with `...rest`.
2. Premise includes `unifies_proc(pattern, received)`.
3. RHS applies deterministic runtime helper:
  - `apply_pattern(pattern, received, body)` -> substituted body.
4. Result term rebuilt into `PPar` with remainder.

This keeps matching eligibility in fixpoint logic and avoids re-running expensive binder extraction unless the premise already succeeded.

## `apply_pattern` Runtime Contract

`apply_pattern(pattern, value, body)` performs:

1. Structural walk over `(pattern, value)`.
2. Binding collection map `{free_var -> matched_subterm}`.
3. Conflict check (same free var bound multiple times):
  - Either require alpha-equivalent/equal assignments.
  - Or fail deterministically (rule does not fire).
4. Capture-avoiding multi substitution into `body` using existing substitution utilities.

Recommended signature direction:

```rust
fn apply_pattern(pattern: &Proc, value: &Proc, body: &Proc) -> Option<Proc>
```

Using `Option` (or `Result`) avoids panic paths and keeps COMM RHS generation straightforward.

## Collection Pattern Matching (Hard Part)

Structural constructor matching is straightforward; multiset patterns are the complexity center.

Case: `PPar` represented as `HashBag<Proc>` with pattern elements `P1, P2, ..., Pk, ...rest`.

Required behavior:

- Each `Pi` must match a distinct element in value bag.
- Remaining elements bind to `...rest` when present.
- Bindings from each `Pi` merge consistently.

### Search strategy

Backtracking search over pattern elements:

1. Choose next unmatched pattern element.
2. Iterate candidate value elements in remaining bag.
3. Keep candidates satisfying `unifies_proc(Pi, candidate)`.
4. Remove chosen candidate from remaining bag and recurse.
5. Merge bindings; reject branch on conflict.

Ascent can encode candidate generation through `for`-style clauses, but consumed-element tracking must be explicit (for example via iterative bag removal values in intermediate bindings).

### Complexity

General multiset matching is NP-hard. Practical mitigation:

- Patterns in language rules are usually small.
- Heuristics can reduce branching:
  - Match most selective pattern elements first (fewest candidates).
  - Prefer ground constructors before free-variable patterns.
  - Early fail on arity/size constraints.

## Soundness and Directionality Notes

To avoid accidental over-approximation:

- Treat unification premise as **directional pattern matching** (pattern -> value), even if relation is syntactically binary.
- Restrict wildcard/free-var rules to pattern side only.
- Ensure relation is not used as a generic equivalence relation unless explicitly intended.

If true symmetric unification is later needed, it should be a separate relation with different rules and performance expectations.

## Rollout Plan

### Phase 1: Minimal structural unification

- Add AST + parsing + relation declaration plumbing.
- Generate unification rules for non-collection constructors.
- Add premise lowering in rule codegen.
- Add small unit tests for constructor and free-var behavior.

### Phase 2: COMM + runtime bindings

- Add `apply_pattern` runtime helper.
- Introduce/update `PFor` pattern-binder form in rhocalc.
- Implement COMM rewrite using unification premise and `apply_pattern`.
- Add end-to-end tests for successful/failed communication matches.

### Phase 3: Collection unification

- Implement `PPar`/bag matching with consumed-element tracking.
- Add ambiguity/conflict tests and backtracking coverage.
- Add stress tests for branching behavior and guardrails.

### Phase 4: Equational composition (optional)

- Add eq-closure integration with `unifies_`*.
- Verify compatibility with existing `eq_*` and `rw_*` closure behavior.

## Testing Strategy

1. **Codegen tests (macro level):**
  - Premise parse and AST mapping for unification syntax.
  - Generated Ascent includes `unifies_<cat>` clauses.
2. **Relation semantics tests:**
  - Ground constructor success/failure.
  - Recursive constructor descent.
  - Pattern free-var wildcard behavior and side restrictions.
3. **COMM integration tests (language level):**
  - Message matches pattern -> rewrite fires with expected substitution.
  - Non-matching message -> rewrite blocked.
  - Repeated variable in pattern requires consistent binding.
4. **Collection tests:**
  - Deterministic small bag matches.
  - Rest binding correctness.
  - Ambiguous branches converge to equivalent outcomes (or expected multiplicity semantics).
5. **Performance checks:**
  - Small/medium pattern sizes benchmarked to detect regressions.

## Non-Goals

- Changing Ascent engine internals.
- Replacing existing substitution or binder infrastructure.
- General-purpose higher-order unification beyond the pattern-matching use case.

## Open Questions

1. **Syntax choice:** which unification-premise syntax best fits existing language grammar?
2. **Directionality encoding:** separate `matches(pattern, value)` relation vs directional constraints on `unifies`.
3. **Conflict policy:** when a variable appears multiple times in a pattern, require strict structural equality or eq-closure equality?
4. **Collection semantics:** should multiple valid multiset matches produce multiple rewrites or deterministic single rewrite selection?
5. **Eq integration timing:** ship structural matching first, then add equational closure, or ship together behind a feature gate?

## Expected Benefits

- Reuses existing relation-premise fixpoint machinery cleanly.
- Keeps rewrite guards declarative and compositional.
- Aligns with current macro architecture (parallel to congruence generation).
- Enables expressive COMM/pattern semantics without engine-level changes.

