# Worked Example

This example follows one tiny rewrite system through Dovetail. It is not a
language feature recommendation; it is a compact way to see how the machinery
fits together.

## Symbols Used

| Symbol | Meaning |
|---|---|
| `Z` | zero constructor |
| `S(x)` | successor constructor |
| `Add(x, y)` | addition constructor |
| `qₜ` | e-class representing term `t` |
| `w(d)` | weight of derivation `d` |
| `K(d)` | exact derivation key |

The example rules are Peano-style addition:

`Add(Z, y) → y`

`Add(S(x), y) → S(Add(x, y))`

The intended seed term is:

`Add(S(Z), S(Z))`

## Saturation Trace

Dovetail inserts the seed as exact e-nodes:

`q₀ = { Z }`

`q₁ = { S(q₀) }`

`q₂ = { Add(q₁, q₁) }`

The second rule matches the root of `q₂` with `x ↦ q₀` and `y ↦ q₁`, so the
right-hand side instantiates to:

`S(Add(q₀, q₁))`

Dovetail inserts that tree and merges it with `q₂`. On the nested addition, the
first rule matches `Add(Z, S(Z))` and merges it with `S(Z)`. After rebuild, the
root class has a derivation through:

`S(S(Z))`

No previous evidence was deleted. The root e-class now records that the seed
and the normal-looking result are equivalent.

## Extraction Trace

The extractor views each e-class as a state in a weighted tree automaton. With a
simple unit cost on each constructor, a possible ranking is:

`w(Z) = 1`

`w(S(d)) = 1 ⊗ w(d)`

`w(Add(d₁, d₂)) = 1 ⊗ w(d₁) ⊗ w(d₂)`

For a class that contains both `Add(S(Z), S(Z))` and `S(S(Z))`, extraction emits
the lower-weight derivation first. If both alternatives have the same weight,
Dovetail orders by `K(d)` but still emits both when `K(d₁) ≠ K(d₂)`.

## Literate Algorithm Walkthrough

```text
Start with the seed term Add(S(Z), S(Z)).
Assign every constructor occurrence an exact content key.
Hashcons exact e-nodes into e-classes.
Search each rewrite rule against canonical e-classes.
Instantiate each matched right-hand side under the substitution.
Merge the matched root with the instantiated right-hand side.
Rebuild canonical child links, parent links, and memo indexes.
Interpret the rebuilt e-graph as a weighted tree automaton.
Ask the checked derivation stream for all finite alternatives.
Return the derivations with terminal completeness metadata.
```

## Rust API Shape

The concrete label and pattern constructors vary by adapter, but callers should
use the checked outcome shape shown below. This is an API example, not an
algorithm.

```rust
use dovetail::extract::{ExtractionCompleteness, Extractor};
use dovetail::rules::SaturationOutcome;

let report = egraph.saturate(&rules, max_iters);
assert!(matches!(report.outcome, SaturationOutcome::Converged));

let extracted = Extractor::new(&egraph, weigh)
    .derivations(root)
    .collect_checked();

match extracted.completeness {
    ExtractionCompleteness::Complete => {
        for derivation in extracted.value {
            consume(derivation);
        }
    }
    ExtractionCompleteness::BoundedByCycleCut => {
        record_bounded_result(extracted.value);
    }
}
```

The important point is that `collect_checked` returns both the vector and the
terminal completeness status. A caller cannot confuse a finite prefix from a
cyclic search with a complete finite enumeration unless it ignores the returned
status.

## Report Boundary

After extraction, `report_from_extraction` produces a substrate-neutral report:

| Report part | Example role |
|---|---|
| `roots` | exact keys for the extracted root derivations |
| `terms` | unique derivation nodes such as `Z`, `S(Z)`, and `S(S(Z))` |
| `derivation_edges` | child links preserving order, so `Add(q₁, q₁)` keeps two child positions |
| `completeness` | `Complete` for this acyclic example |

The Rho backend may lower this report to `rhoapi::Par`; an oracle may compare
it with Ascent output; a local test may assert exact keys directly. Dovetail
does not need to know which consumer receives the report.
