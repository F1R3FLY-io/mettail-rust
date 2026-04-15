# Model-Based Testing

## What Is It?

Model-based testing derives a testable state machine from a MeTTaIL language's metadata (type categories, rewrite rules, equations) and uses proptest to generate random sequences of operations over that machine. This enables exhaustive exploration of rewrite rule interactions, congruence propagation, and algebraic identities.

Located in `simulation/src/model.rs`.

## What Does It Do?

The model-based testing system:

1. **Extracts a state machine** (`LanguageStateMachine`) from the language's `LanguageMetadata`, capturing type categories, rewrite rules (base and congruence), and equations (conditional and unconditional).
2. **Generates operation sequences** (`Vec<ModelOp>`) via proptest, where each operation is either a rewrite rule application, an Ascent fixpoint run, a normal form check, or a normalization pass.
3. **Shrinks failing sequences** to the minimal sequence of operations that reproduces a failure.

## Why Was It Chosen?

### The Stateful Testing Problem

Simple property-based testing generates a single term and runs it through the pipeline. But language bugs often manifest only when **specific sequences of operations** interact:

- Applying `Comm` followed by `ParCong` might expose a bug that neither rule triggers alone.
- Running Ascent twice (after manually applying an equation) might produce a different result than running it once (non-idempotence bug).
- Normalizing before and after rewriting might yield different normal forms (confluence bug).

Model-based testing captures these interaction patterns by generating **sequences** of operations, not just single terms.

This approach was pioneered by Claessen and Hughes (2000) in QuickCheck and formalized for Erlang systems by Arts, Hughes, Johansson, and Wiger (2006) with their stateful testing framework. The key insight is: if you can describe the system as a state machine with transitions, you can generate and shrink operation sequences systematically.

### State Machine Derivation

Unlike traditional model-based testing where the user manually specifies the state machine, MeTTaIL derives it automatically from the language definition. The `LanguageMetadata` trait provides:

```
LanguageMetadata
  ├── types()     → [TypeDef]         // type categories
  ├── terms()     → [TermDef]         // term constructors
  ├── equations() → [EquationDef]     // structural congruences
  └── rewrites()  → [RewriteDef]      // rewrite rules
```

These are sufficient to build a model of the language's operational semantics.

## How Does It Work?

### LanguageStateMachine

```rust
pub struct LanguageStateMachine {
    pub categories: Vec<String>,              // type names
    pub rewrite_rules: Vec<ModelRewriteRule>,  // all rewrite rules
    pub equations: Vec<ModelEquation>,          // all equations
}
```

Construction from metadata:

```
PROCEDURE LanguageStateMachine::from_metadata(metadata) → LanguageStateMachine:
    categories ← [t.name for t in metadata.types()]

    rewrite_rules ← FOR rw in metadata.rewrites():
        ModelRewriteRule {
            name: rw.name,
            lhs_display: rw.lhs,
            rhs_display: rw.rhs,
            is_congruence: rw.premise.is_some()  // congruence iff has a premise S ~> T
        }

    equations ← FOR eq in metadata.equations():
        ModelEquation {
            lhs_display: eq.lhs,
            rhs_display: eq.rhs,
            has_conditions: !eq.conditions.is_empty()
        }

    RETURN LanguageStateMachine { categories, rewrite_rules, equations }
```

### Rewrite Rule Classification

Rewrite rules are classified into two groups:

| Class          | Has Premise? | Example                                              | Purpose                                 |
|----------------|--------------|------------------------------------------------------|-----------------------------------------|
| **Base**       | No           | `Comm: (PPar {(PInputs ns cont), ...}) ⟶ ...`        | Core computational steps                |
| **Congruence** | Yes (S ~> T) | `ParCong: (PPar {S, ...rest}) ⟶ (PPar {T, ...rest})` | Propagate rewrites into sub-expressions |

A congruence rule has a premise `S ~> T`, meaning "if S rewrites to T, then the surrounding context also rewrites." These are structural rules that push computation inward.

The distinction matters for coverage analysis: a language where only congruence rules fire (but no base rules) is not actually computing anything.

```
PROCEDURE base_rewrite_count() → usize:
    RETURN |{r ∈ rewrite_rules : ¬r.is_congruence}|

PROCEDURE unconditional_equation_count() → usize:
    RETURN |{e ∈ equations : ¬e.has_conditions}|
```

### Equation Classification

Equations are classified by their conditions:

| Class             | Has Conditions? | Example                                           |
|-------------------|-----------------|---------------------------------------------------|
| **Unconditional** | No              | `(PPar {P, {}}) = P` (parallel zero identity)     |
| **Conditional**   | Yes             | `x # P ⊢ (PNew ^x.(P)) = P` (freshness condition) |

Unconditional equations are always applicable; conditional equations require freshness or relation conditions to be satisfied.

### ModelOp: Operations in the Model

```rust
pub enum ModelOp {
    ApplyRewrite { rule_index: usize },  // apply a specific rule
    RunAscent,                            // run the Ascent fixpoint engine
    CheckNormalForm,                      // check if the term is in normal form
    Normalize,                            // normalize (beta-reduce, flatten, etc.)
}
```

### Generating Operation Sequences

The `arb_model_ops()` function produces a proptest strategy for `Vec<ModelOp>`:

```
PROCEDURE arb_model_ops(model, max_ops) → BoxedStrategy<Vec<ModelOp>>:
    num_rules ← |model.rewrite_rules|

    single_op ← IF num_rules > 0 THEN
        prop_oneof![
            3 => (0..num_rules).prop_map(|i| ApplyRewrite { rule_index: i }),
            1 => Just(RunAscent),
            1 => Just(CheckNormalForm),
            1 => Just(Normalize),
        ]
    ELSE
        prop_oneof![
            1 => Just(RunAscent),
            1 => Just(CheckNormalForm),
            1 => Just(Normalize),
        ]

    RETURN proptest::collection::vec(single_op, 1..=max_ops).boxed()
```

The weighting (3:1:1:1) biases generation toward `ApplyRewrite`, which is the most interesting operation for discovering rewrite rule interactions.

When there are no rewrite rules (e.g., a language with only equations), `ApplyRewrite` is excluded and only `RunAscent`, `CheckNormalForm`, and `Normalize` are generated.

### Shrinking Finds Minimal Failing Sequences

proptest shrinks `Vec<ModelOp>` by:

1. **Reducing vector length**: shorter sequences are tried first.
2. **Simplifying elements**: `ApplyRewrite { rule_index: 5 }` shrinks toward `rule_index: 0`.

This means a failing sequence like:

```
[RunAscent, ApplyRewrite(3), Normalize, ApplyRewrite(5), CheckNormalForm, ApplyRewrite(1)]
```

might shrink to:

```
[ApplyRewrite(1), RunAscent]
```

revealing that the bug requires only rule 1 followed by Ascent, not the full 6-step sequence.

### Example: RhoCalc State Machine

For the RhoCalc language (a process algebra), the derived state machine has:

```
Categories: [Proc, Name, Int, Float, Bool, Str]

Base Rewrite Rules:
  Comm:  (PPar {(PInputs ns cont), ...}) ⟶ (PPar {(eval cont ...), ...rest})
  Exec:  (PDrop (NQuote P)) ⟶ P

Congruence Rules:
  ParCong:  (PPar {S, ...rest}) ⟶ (PPar {T, ...rest})        [S ~> T]
  NewCong:  (PNew ^[xs].S) ⟶ (PNew ^[xs].T)                  [S ~> T]
  AddCongL: (Add S X) ⟶ (Add T X)                             [S ~> T]
  AddCongR: (Add X S) ⟶ (Add X T)                             [S ~> T]

Equations:
  Unconditional: (PPar {P, {}}) = P
  Conditional:   x # P ⊢ (PNew ^x.(P)) = P
```

A generated operation sequence might be:

```
[ApplyRewrite(0),  // Comm
 RunAscent,
 ApplyRewrite(2),  // ParCong
 CheckNormalForm,
 ApplyRewrite(1)]  // Exec
```

This tests the interaction between communication, congruence propagation, and execution rules.

### Query Methods

The `LanguageStateMachine` provides several query methods for analysis:

```rust
model.base_rewrite_count()          // number of non-congruence rules
model.unconditional_equation_count() // number of unconditional equations
model.rule_names()                   // all rule names (including None)
model.named_rules()                  // only named rules
```

These are used by the coverage system (see [coverage-guided.md](coverage-guided.md)) to determine the total rule set and identify which rules have been exercised.

## States and Transitions

In the abstract state machine view:

- **States** = terms (elements of the language's term algebra)
- **Transitions** = rewrite rule applications and normalization steps
- **Initial state** = the randomly generated input term
- **Accepting states** = normal forms (terms where no further rewrites apply)

The simulation runner explores this state machine by executing the generated operation sequence and checking invariants at each state.

## References

- Claessen, K. and Hughes, J. (2000). "QuickCheck: A Lightweight Tool for Random Testing of Haskell Programs." ACM SIGPLAN Notices, 35(9), pp. 268-279.
- Arts, T., Hughes, J., Johansson, J., and Wiger, U. (2006). "Testing Telecoms Software with Quviq QuickCheck." Proceedings of the 2006 ACM SIGPLAN Workshop on Erlang, pp. 2-10.
