# Rules and Saturation

Dovetail represents rewrite rules as data. A caller supplies `RewriteRule<L>`
values over payload labels `L`.

## Where Rules Come From

In MeTTaIL integration, rules originate in the generated language inventory:

`language! specification → LanguageDef → LanguageMetadata → RewriteRule<L>`

The `language!` macro remains the source of truth for categories,
constructors, equations, rewrites, guards, and native-handler declarations.
Macro parsing produces `LanguageDef`; code generation emits typed AST
constructors and `LanguageMetadata`; the Dovetail adapter derives
`RewriteRule<L>` values from that metadata.

This distinction matters for maintenance. Dovetail should not maintain a
separate hard-coded list of language categories or constructor heads. It should
ask the generated inventory what exists, then lower that inventory into
pattern-and-rule data. A future language edit should therefore flow through the
language definition and generated metadata before reaching Dovetail.
Guarded rules follow the same path. Dovetail receives structural guard
patterns, behavioral predicate premises, typed predicate metadata, and external
coverage evidence from generated inventory. It does not infer guard meaning
from predicate names or from a backend-local list of known category heads.

## Predicate Evidence Boundary

The generalized predicate substrate is upstream of Dovetail. Its job is to
derive guard obligations from `LanguageDef`, generated type metadata, and
rewrite metadata, then classify each obligation with an evidence disposition.
Dovetail consumes that disposition; it does not re-derive symbolic automata,
tree automata, behavioral model-checking, or effective-Boolean-algebra proofs.

The intended disposition vocabulary is:

| Disposition | Meaning for Dovetail |
|---|---|
| `ExactDecidable` | the predicate has complete static or runtime-decidable evidence, such as a structural matcher, EBA/SFT proof, or exact model-checker result |
| `BoundedDecidable` | the predicate is sound and complete only under the recorded bound; Dovetail may report boundedness but must not advertise exhaustive coverage beyond that bound |
| `RejectSafeApprox` | the predicate may conservatively reject matches; Dovetail may use it only in positions where false negatives do not fabricate successful rewrites |
| `TrustedNativeGuard` | a native assertion site owns the contract; Dovetail records the checked disposition in the report and treats missing or incompatible dispositions as coverage failures |
| `MachineCheckedModel` | a machine-checked formal model discharges the guard obligation; the proof is attributed in documentation/comments, not carried as runtime data |
| `RuntimeObservation` | the Rho runtime supplies the behavioral evidence through a named observation or join contract |
| `Unknown` | production-default lowering is refused; Dovetail can still surface the uncovered obligation in a report |

This boundary keeps a separate predicate-substrate implementation
complementary to the Dovetail/Rho runtime-backend work:

`language! → LanguageDef → guard obligations → predicate dispositions → Dovetail guarded rules → DovetailRunReport`

For classical structural predicates, the upstream substrate may expose a full
Boolean algebra. For semi-decidable behavioral predicates, it must expose only a
reject-safe algebraic contract. Dovetail must therefore never reinterpret a
behavioral or mixed structural-behavioral disposition as classical complement
unless the disposition explicitly carries exact decidable evidence.

## Rule Shape

A rule has:

| Field | Meaning |
|---|---|
| `lhs` | pattern matched against e-classes |
| `rhs` | pattern instantiated under a match substitution |
| `guard` | optional structural or behavioral predicate over the match substitution |
| `evidence` | optional coverage reference for a native, theory, SFT, Rho, or external guard/handler contract |
| `label` | optional diagnostic name |

Patterns are:

`Pattern = Var(name) | App(op, args)`

A substitution maps variable names to e-classes:

`Subst : variableName ↦ EClassId`

## Search And Instantiation

Rule matching is structural over e-nodes. A variable binds to an e-class. If the
same variable appears twice, both occurrences must resolve to the same canonical
e-class.

Literate pseudocode:

```text
To match a pattern against an e-class:
  If the pattern is a variable:
    If the variable is unbound, bind it to the canonical class.
    If it is already bound to this class, keep the match.
    Otherwise reject the match.
  If the pattern is an application:
    For each e-node in the class:
      Require the same operator and arity.
      Recursively match each child pattern against the child e-class.
```

Instantiation rejects ill-formed right-hand sides:

`vars(rhs) ⊆ vars(lhs)`

If a right-hand-side variable is unbound, Dovetail adds no partial term.

Guarded instantiation is structural first, behavioral second:

```text
To apply a guarded rule:
  Match the left-hand pattern and build substitution σ.
  If structural guard matching fails, derive no fact.
  If structural matching succeeds, evaluate behavioral predicates over σ.
  If any behavioral predicate is false or unsupported, derive no fact unless
  an explicit external contract reports a covered result.
  Instantiate the right-hand side only after all covered guards pass.
```

The no-commit rule is semantic, not just operational:

`guard(σ) = false ⇒ no derived fact`

For Rho consumers, the same rule becomes no RSpace consumption on a failed
guard. For direct Dovetail consumers, it means no rewrite edge is added.

## Saturation Outcomes

Saturation has three terminal outcomes:

| Outcome | Meaning |
|---|---|
| `Converged` | an iteration produced no new merges |
| `NodeLimit` | the e-node budget refused a fresh node |
| `IterationLimit` | `max_iters` ended before convergence |

This is deliberately not a Boolean success flag. A caller must inspect the
outcome before treating extracted results as complete for a language.

## Saturation Algorithm

Literate pseudocode:

```text
To saturate an e-graph:
  For each iteration up to max_iters:
    Set the iteration merge count to zero.
    For each rewrite rule:
      Search all matches of the left-hand side.
      For each match:
        Reject the match if the right-hand side has an unbound variable.
        Instantiate the right-hand side inside the node budget.
        If the budget refuses a fresh node, return NodeLimit.
        Merge the match root with the instantiated right-hand side.
      If this rule caused merges, rebuild congruence closure.
    If the iteration caused no merges, return Converged.
  Return IterationLimit.
```

## Monotonicity

Saturation adds equality evidence; it does not replace a term with another term.

`Fᵢ ⊆ Fᵢ₊₁`

where `Fᵢ` is the set of represented equality facts after iteration `i`.

This monotonicity is why extraction can enumerate alternatives after
saturation rather than relying on saturation to choose a winner.

## Budget Discipline

`try_add_with_budget` refuses a fresh node before overshooting:

`node_count ≤ max_nodes`

An existing exact node can still be resolved after the budget is reached,
because resolving a duplicate does not grow the graph.
