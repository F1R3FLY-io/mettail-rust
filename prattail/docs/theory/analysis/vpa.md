# Visibly pushdown automata analysis

## Scope

PraTTaIL's VPA module recognizes and analyzes nested-word structure. It is used
when terminal roles are visible from the token itself: calls always push,
returns always inspect/pop, and internal tokens never touch the stack.

The module supports:

- generic semiring evaluation of a supplied word;
- exact Boolean support-language emptiness;
- exact Boolean determinization and total complement;
- synchronized intersection;
- exact Boolean language inclusion and equivalence;
- conservative control-state reachability and trimming;
- typed delimiter skip-table analysis for recovery.

It does not claim quantitative inclusion or quantitative determinization for
arbitrary idempotent semirings.

## Model

The alphabet $`\widetilde{\Sigma}`$ is the disjoint union of call,
return, and internal partitions. A VPA stores:

| Rust field | Mathematical role |
|---|---|
| `states` | finite control states $`Q`$ |
| `alphabet` | $`(\Sigma_c,\Sigma_r,\Sigma_i)`$ |
| `call_transitions` | call, pushed frame, target, and weight |
| `return_transitions` | return, observed frame, target, and weight |
| `internal_transitions` | stack-neutral target and weight |
| `initial_states` | $`Q_0`$ |
| `accepting_states` | $`F`$ |
| `initial_stack_symbol` | permanent bottom marker $`Z_0`$ |

Final-state acceptance permits residual frames. Above bottom, a return pops one
frame. At bottom, a declared return reads $`Z_0`$ without removing it.
Unknown symbols terminate all runs.

## Validation

Exact decisions call `validate()`, which rejects alphabet overlaps,
noncanonical IDs, absent state references, wrongly classified transition keys,
and nonzero calls that push the reserved bottom marker. This is necessary
because `WeightedVpa` intentionally exposes its maps for compiler
construction.

## Algorithms

### Weighted membership

`weighted_run(word)` maintains a map from concrete
`(control_state, stack)` configurations to accumulated semiring values.
Equal configurations combine with $`\oplus`$; each transition extends a
value with $`\otimes`$. After the last symbol, final weights are applied
and accepting configurations are summed.

This algorithm is exact for the supplied finite word over any `Semiring`.

### Exact emptiness

The emptiness procedure never bounds concrete stack depth. It saturates the
least well-matched relation $`B\subseteq Q\times Q`$ under identity,
internal edges, composition, and same-frame call/return wrapping. A finite
ground phase accounts for bottom returns; a finite prefix phase accounts for
unmatched calls allowed by final-state acceptance.

```text
summaries <- identity + active internal edges
repeat newly discovered composition and same-frame wrapping facts
ground <- closure(active initials, summaries + bottom returns)
prefix <- closure(ground, summaries + calls)
empty <- prefix has no active final state
```

### Determinization

The exact Alur–Madhusudan state is $`(S,R)`$, not merely a subset of
control states. $`S`$ records the well-matched relation for the current
nested factor and $`R`$ records reachable source states. Generated stack
symbols retain the caller deterministic state and call symbol. A matched return
uses one shared source frame witness in its call and return predicates.

The reachable deterministic state space is bounded by $`2^{n^2+n}`$ for
$`n=|Q|`$. A canonical dead state makes every declared transition total.

### Closure-based decisions

Complement determinizes, totalizes, and flips final states. Intersection
synchronizes product states and length-prefixed product frames. Inclusion
aligns the union alphabet before constructing
$`L(A)\cap\overline{L(B)}`$ and checking exact emptiness. Equivalence is
mutual inclusion.

### Structural reachability and trim

`reachable_states()` is deliberately a conservative graph projection: it
ignores stack feasibility and visits all stored transitions. `trim()` uses
that overapproximation, so it never removes a state merely because a particular
stack correlation was not explored. These utilities are not substitutes for
exact language emptiness.

## API and complexity

| API | Semantics | Worst-case scale |
|---|---|---:|
| `weighted_run` | fixed-word semiring value | explored concrete configurations |
| `validate` | structural preconditions | linear in representation size |
| `try_is_language_empty` | exact Boolean emptiness | polynomial finite summary saturation |
| `determinize` | exact Boolean support language | $`2^{O(n^2)}`$ states |
| `complement` | total Boolean complement | determinization dominated |
| `intersect` | Boolean product | product states/transitions |
| `check_inclusion` | exact Boolean inclusion | exponential in general |
| `check_equivalence` | mutual exact inclusion | exponential in general |
| `reachable_states` | conservative state graph | linear in stored graph |
| `trim` | remap conservative reachable graph | linear in stored graph |

`is_deterministic()` checks at most one target per stored key and one initial
state; it is a partial-determinism predicate. `determinize()` additionally
guarantees totality over the declared alphabet.

## Pipeline integration

`build_alphabet_from_syntax` classifies delimiter terminals, and
`analyze_from_bundle` constructs the canonical structured-language VPA.
`VpaAnalysis` reports:

- whether the model can enter the valid deterministic decision path;
- conflicting alphabet classifications;
- control-state count.

Recovery uses a distinct typed delimiter stack
`DelimiterClass<K>`. A closer pairs only with an opener of exactly the same
kind. Mismatches such as `(]` do not pop or produce a skip pair. No derived
analysis field treats $`|Q|`$ as a nesting-depth bound; the only recovery
ceiling is explicit caller policy.

## Example

```rust
use std::collections::HashSet;

use mettail_prattail::automata::semiring::{BooleanWeight, Semiring};
use mettail_prattail::vpa::{is_language_empty, Vpa, VpaAlphabet};

let mut vpa = Vpa::new(VpaAlphabet::new(
    HashSet::from(["call".to_string()]),
    HashSet::from(["return".to_string()]),
    HashSet::new(),
));
let start = vpa.add_state(None);
let final_state = vpa.add_state(None);
vpa.initial_states.insert(start);
vpa.accepting_states.insert(final_state);
vpa.call_transitions.insert(
    (start, "call".into()),
    vec![(final_state, "frame".into(), BooleanWeight::one())],
);

assert!(!is_language_empty(&vpa));
assert!(vpa.weighted_run(&["call"]).0); // final state, residual frame allowed
```

## Verification

- Rocq closure, reachability, determinization, and delimiter proofs are
  registered in `formal/rocq/mathematical_analyses/_CoqProject`.
- Unit tests cover construction, running, closure operations, and typed
  delimiter behavior.
- Integration tests contain adversarial old-cap, cross-gamma, bottom-return,
  invalid-input, and product-encoding examples.
- Property tests compare exact results with independent small-domain oracles.

See [the formal proof guide](../formal-verification/vpa-closure.md) and
[the determinization theory](../vpa/weighted-determinization.md).

## References

- Rajeev Alur and P. Madhusudan, “Visibly Pushdown Languages,” STOC 2004.
  [DOI: 10.1145/1007352.1007390](https://doi.org/10.1145/1007352.1007390).
- Rajeev Alur and P. Madhusudan, “Adding Nesting Structure to Words,”
  *Journal of the ACM* 56(3), 2009.
  [DOI: 10.1145/1516512.1516518](https://doi.org/10.1145/1516512.1516518).
