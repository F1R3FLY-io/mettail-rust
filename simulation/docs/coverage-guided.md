# Coverage-Guided Strategy Generation

## What Is It?

The coverage-guided generation system tracks which rewrite rules and term constructors are exercised during simulation, computes coverage percentages, identifies uncovered rules, and enables feedback-driven test generation. Coverage data drives the iteration cycle: generate terms → simulate → collect coverage → identify gaps → adjust generation → repeat.

Located in `simulation/src/coverage.rs`.

## What Does It Do?

The coverage system provides:

1. **SimulationCoverage**: tracks rule firings and constructor hits across simulation runs, computes coverage percentages, identifies uncovered rules, and supports merging of coverage data from multiple runs.
2. **coverage_from_ascent()**: extracts coverage data from the Ascent engine's execution results.
3. **RuleCoverage** (in `results.rs`): a lighter-weight coverage tracker embedded in `CampaignResults`.

## Why Was It Chosen?

### The Coverage Gap Problem

Random testing excels at finding bugs in well-exercised code paths but may never explore rare rules. In a language like RhoCalc with 6 rewrite rules, random term generation might exercise `Comm` and `ParCong` frequently (because parallel composition is common) but never exercise `Exec` (because it requires the specific pattern `*(@ P)`).

Coverage-guided generation solves this by:
1. Measuring which rules have fired at least once.
2. Identifying the gap (rules that have never fired).
3. Biasing future term generation toward constructors that trigger the uncovered rules.

This is analogous to coverage-guided fuzzing (American Fuzzy Lop, libFuzzer), but applied to algebraic rewriting rather than machine code.

## How Does It Work?

### SimulationCoverage

```rust
pub struct SimulationCoverage {
    pub rule_firings: HashMap<String, usize>,     // rule name → firing count
    pub constructor_hits: HashMap<String, usize>,  // constructor name → hit count
    pub total_steps: usize,                        // total simulation steps
}
```

#### Recording Rewrites

```
PROCEDURE record_rewrite(rule_name):
    rule_firings[rule_name] ← rule_firings[rule_name] + 1
    total_steps ← total_steps + 1
```

#### Recording Constructors

```
PROCEDURE record_constructor(ctor_name):
    constructor_hits[ctor_name] ← constructor_hits[ctor_name] + 1
```

#### Computing Coverage

```
PROCEDURE coverage_pct(total_rules) → f64:
    IF total_rules == 0 THEN RETURN 100.0    // vacuously covered
    covered ← |rule_firings|                  // number of distinct rules fired
    RETURN (covered / total_rules) × 100.0
```

#### Identifying Uncovered Rules

```
PROCEDURE uncovered_rules(all_rules: [String]) → [String]:
    RETURN [r ∈ all_rules : r ∉ rule_firings.keys()]
```

#### Merging Coverage

Coverage from multiple simulation runs can be merged:

```
PROCEDURE merge(other: SimulationCoverage):
    FOR (rule, count) in other.rule_firings:
        rule_firings[rule] ← rule_firings[rule] + count
    FOR (ctor, count) in other.constructor_hits:
        constructor_hits[ctor] ← constructor_hits[ctor] + count
    total_steps ← total_steps + other.total_steps
```

This enables parallel simulation campaigns to contribute to a shared coverage map.

### coverage_from_ascent()

The `coverage_from_ascent()` function extracts coverage from `AscentResults`:

```
PROCEDURE coverage_from_ascent(results: AscentResults) → SimulationCoverage:
    coverage ← SimulationCoverage::new()

    // Record rule firings from rewrites
    FOR rewrite in results.rewrites:
        IF rewrite.rule_name is Some(name) THEN
            coverage.record_rewrite(name)
        ELSE
            coverage.record_rewrite("__anonymous__")

    // Record constructor hits from terms
    FOR term_info in results.all_terms:
        ctor ← extract_constructor_name(term_info.display)
        IF ctor is not empty THEN
            coverage.record_constructor(ctor)

    RETURN coverage
```

### Constructor Name Extraction

The constructor name is extracted from the term's display string using a lightweight parser:

```
PROCEDURE extract_constructor_name(display: str) → String:
    trimmed ← display.trim()
    IF trimmed is empty THEN RETURN ""

    // Strip leading '(' if present
    inner ← IF trimmed starts with '(' THEN trimmed[1..] ELSE trimmed

    first ← inner[0]

    IF first is alphabetic or '_' THEN
        // Identifier: collect alphanumeric + underscore
        RETURN inner.take_while(is_alphanumeric_or_underscore)
    ELSE IF first is digit or '-' THEN
        // Numeric literal
        RETURN inner.take_while(is_digit_or_dot)
    ELSE
        // Operator or symbol (*, @, etc.)
        RETURN String(first)
```

**Examples:**

| Display String          | Constructor Name |
|-------------------------|------------------|
| `(AddInt 3 5)`          | `AddInt`         |
| `PZero`                 | `PZero`          |
| `*(n)`                  | `*`              |
| `@({})`                 | `@`              |
| `42`                    | `42`             |
| `(PPar {PZero, PZero})` | `PPar`           |

### The Feedback Loop

The full coverage-guided generation cycle:

```
┌──────────────────────────────────────────────────────────┐
│                                                          │
│  ┌────────────┐     ┌────────────┐     ┌──────────────┐  │
│  │ Generate   │────▶│  Simulate  │────▶│  Collect     │  │
│  │ terms via  │     │  (Runner)  │     │  coverage    │  │
│  │ strategy   │     │            │     │              │  │
│  └────────────┘     └────────────┘     └──────┬───────┘  │
│       ▲                                       │          │
│       │                                       ▼          │
│  ┌─────┴──────────┐                   ┌──────────────┐   │
│  │ Adjust         │◀──────────────────│  Analyze     │   │
│  │ strategy       │                   │  gaps        │   │
│  │ (bias toward   │                   │              │   │
│  │  uncovered)    │                   └──────────────┘   │
│  └────────────────┘                                      │
│                                                          │
└──────────────────────────────────────────────────────────┘
```

1. **Generate**: use proptest strategies to produce random terms.
2. **Simulate**: run each term through the parse → rewrite pipeline via `SimulationRunner`.
3. **Collect**: extract `SimulationCoverage` from each run, merge into cumulative coverage.
4. **Analyze**: compute `uncovered_rules()` and identify constructors that appear in uncovered rules' LHS patterns.
5. **Adjust**: bias the term generation strategy toward those constructors in the next round.
6. **Repeat** until coverage target is met or budget is exhausted.

### Rule Firing Coverage

**Rule firing coverage** measures the fraction of language rules exercised at least once:

```
coverage = |{rules fired at least once}| / |{all rules in language}|
```

A campaign with 100% rule firing coverage has triggered every rewrite rule at least once. This does not guarantee correctness (a rule can fire and still produce wrong results) but guarantees that no rule is completely untested.

The `RuleCoverage` struct in `results.rs` provides this metric at the campaign level:

```rust
pub struct RuleCoverage {
    pub rules_fired: HashMap<String, usize>,
    pub total_rules: usize,
    pub coverage_pct: f64,
}
```

### Constructor Coverage

**Constructor coverage** measures how many distinct term constructors appear in the simulation traces. This is complementary to rule coverage: a language might have all rules covered but never produce a `PNew` term, meaning the `NewCong` congruence rule was tested only with synthetic inputs.

### Integration with Parser Coverage

The simulation coverage system is designed to integrate with the language's parser coverage. The parser generates test cases for each grammar production; the simulation system tests each rewrite rule. Together, they provide end-to-end coverage of the language specification.

The `SimulationRunner.run_campaign()` method automatically collects coverage:

```
// In run_campaign():
FOR entry in trace.steps:
    IF entry.operation starts with "rewrite:" THEN
        rule ← entry.operation.strip_prefix("rewrite:")
        results.coverage.record_rule(rule)
    ELSE IF entry.operation == "rewrite" THEN
        results.coverage.record_rule("(unnamed)")

// At campaign end:
total_rules ← language.metadata().rewrites().len()
results.coverage.finalize(total_rules)
```

The final coverage report includes:

```
Coverage: 8/12 rules covered (66.7%), 142 total firings
```

This tells the developer that 4 rules were never exercised, prompting targeted test generation for those rules.
