# Redex-Guided Term Generation Design

## Problem Statement

Current term generation (both exhaustive and random) produces terms without consideration of whether they contain redexes (reducible expressions). In practice, this means:

1. **Low redex density**: Most generated terms are normal forms with no available rewrites
2. **Poor test coverage**: Testing rewrite systems requires manually crafting terms with redexes
3. **Inefficient exploration**: Random generation wastes effort on irreducible terms
4. **Limited stress testing**: Hard to generate terms with multiple simultaneous redexes

### Example (Rholang)

Generated terms at depth 2:
- `0` - normal form
- `*a` - normal form
- `a!(0)` - normal form
- `for(a->x0){0}` - normal form
- `{0, 0}` - normal form
- `*@(0)` - **redex!** (can rewrite to `0`)
- `{for(a->x0){0}, a!(0)}` - **redex!** (communication)

**Observation**: Only ~2-5% of generated terms are redexes, making it hard to test rewrite systems.

## Design Goals

1. **Generate terms with guaranteed redexes** - Ensure interesting terms for testing
2. **Control redex density** - Parameter to specify minimum number of redexes
3. **Compositional approach** - Build complex terms from simple redex patterns
4. **Theory-agnostic** - Work with any theory's rewrite rules
5. **Maintain randomness** - Still produce diverse terms, not just fixed patterns

## Core Concept: Redex Patterns

A **redex pattern** is a template that matches the LHS of a rewrite rule.

### Example Patterns (Rholang)

```rust
// Communication redex
Pattern: {for(chan->x){P}, chan!(Q)}
Generates: {for(a->x0){*x0}, a!(*b)}

// Drop redex
Pattern: *@(P)
Generates: *@(a!(0))

// Nested redexes
Pattern: {for(chan->x){*@(x)}, chan!(Q)}
Generates: {for(a->x0){*@(x0)}, a!(b!(0))}
```

## Approach 1: Pattern-Based Generation

### Overview
Extract patterns from rewrite rule LHS and use them as templates for generation.

### Algorithm

```rust
fn generate_redex_at_depth(
    vars: &[String],
    depth: usize,
    max_collection_width: usize,
    rule: &RewriteRule,
    rng: &mut R
) -> Term {
    // 1. Parse the LHS pattern
    let pattern = extract_pattern(rule.left);

    // 2. Identify "holes" (pattern variables)
    let holes = find_pattern_variables(pattern);

    // 3. Generate random terms for each hole
    let mut substitutions = HashMap::new();
    for hole in holes {
        let hole_depth = allocate_depth(depth, rng);
        let term = generate_random_at_depth(vars, hole_depth, max_collection_width, rng);
        substitutions.insert(hole, term);
    }

    // 4. Substitute and return
    instantiate_pattern(pattern, substitutions)
}
```

### Advantages
- ✅ Simple and direct
- ✅ Guaranteed to produce valid redexes
- ✅ Easy to understand and implement

### Challenges
- ❌ Requires parsing/analyzing rewrite rule LHS
- ❌ Patterns with conditions (e.g., `if x # P`) are complex
- ❌ Collection patterns with `...rest` need special handling
- ❌ Shared variables across pattern require unification

## Approach 2: Forward Generation with Validation

### Overview
Generate terms normally but validate they contain redexes, regenerating if not.

### Algorithm

```rust
fn generate_with_redex(
    vars: &[String],
    depth: usize,
    max_collection_width: usize,
    min_redexes: usize,
    rng: &mut R
) -> Term {
    let max_attempts = 1000;

    for _ in 0..max_attempts {
        let term = generate_random_at_depth(vars, depth, max_collection_width, rng);

        // Check if term contains at least min_redexes
        if count_redexes(term) >= min_redexes {
            return term;
        }
    }

    // Fallback: use pattern-based generation
    generate_redex_at_depth(vars, depth, max_collection_width, pick_rule(rng), rng)
}

fn count_redexes(term: &Term) -> usize {
    // Use Ascent to check which rules match
    // Or pattern match directly
}
```

### Advantages
- ✅ Maintains randomness and diversity
- ✅ Works with existing generation infrastructure
- ✅ Can target specific redex counts

### Challenges
- ❌ May require many attempts (rejection sampling)
- ❌ Still needs redex detection mechanism
- ❌ Expensive for low-probability patterns

## Approach 3: Compositional Redex Injection

### Overview
Generate random terms and strategically inject redexes at specific positions.

### Algorithm

```rust
fn generate_with_injected_redexes(
    vars: &[String],
    depth: usize,
    max_collection_width: usize,
    num_redexes: usize,
    rng: &mut R
) -> Term {
    // 1. Generate a random "skeleton" term
    let mut term = generate_random_at_depth(vars, depth, max_collection_width, rng);

    // 2. Find positions where redexes can be injected
    let positions = find_injection_points(term, depth);

    // 3. Pick random positions and inject redexes
    for _ in 0..num_redexes {
        if let Some(pos) = positions.choose(rng) {
            let rule = pick_rule(rng);
            let redex = generate_redex_pattern(vars, rule, rng);
            term = inject_at_position(term, pos, redex);
        }
    }

    term
}
```

### Advantages
- ✅ Fine-grained control over redex count
- ✅ Can create terms with multiple redexes
- ✅ Flexible positioning

### Challenges
- ❌ Complex term traversal and mutation
- ❌ Type correctness at injection points
- ❌ May break term structure invariants

## Approach 4: Redex-First Generation (Recommended)

### Overview
Start with a redex and build outward, ensuring the redex remains present.

### Algorithm

```rust
fn generate_redex_term(
    vars: &[String],
    depth: usize,
    max_collection_width: usize,
    rng: &mut R
) -> Term {
    // 1. Pick a random rewrite rule
    let rule = pick_rule(rng);

    // 2. Allocate depth budget
    let redex_depth = rng.gen_range(0..=depth);
    let context_depth = depth - redex_depth;

    // 3. Generate the redex
    let redex = instantiate_pattern(rule.left, vars, redex_depth, rng);

    // 4. Optionally wrap in context
    if context_depth > 0 && rng.gen_bool(0.5) {
        wrap_in_context(redex, vars, context_depth, rng)
    } else {
        redex
    }
}

fn wrap_in_context(term: Term, vars: &[String], depth: usize, rng: &mut R) -> Term {
    // Choose a constructor that can contain the term
    let constructor = pick_compatible_constructor(term.category(), rng);

    match constructor {
        ParallelComposition => {
            // {term, random_other_terms}
            let n = rng.gen_range(0..=max_collection_width);
            let others = (0..n).map(|_| generate_random(...)).collect();
            PPar(bag_from([term] + others))
        }
        UnaryConstructor(op) => {
            // op(term)
            op(Box::new(term))
        }
        BinderConstructor(bind) => {
            // bind(x, term)
            let x = fresh_var();
            bind(x, Box::new(term))
        }
    }
}
```

### Advantages
- ✅ **Guaranteed redex presence** - Core redex can't be lost
- ✅ **Composable** - Can nest multiple redexes
- ✅ **Efficient** - No rejection sampling needed
- ✅ **Natural** - Builds terms "inside-out" like manual construction

### Challenges
- ⚠️ Requires classification of constructors (which can wrap which)
- ⚠️ Pattern instantiation needs careful implementation
- ⚠️ Shared variables in patterns need attention

## Implementation Plan (Approach 4)

### Phase 1: Pattern Analysis & Extraction

1. **Extract patterns from rewrite rules**
   ```rust
   struct RedexPattern {
       constructor: Ident,
       holes: Vec<(Ident, Category)>, // Variable name -> type
       constraints: Vec<Constraint>,   // Freshness, equality, etc.
   }

   fn analyze_rewrite_rule(rule: &RewriteRule) -> RedexPattern;
   ```

2. **Build pattern database**
   - Store all patterns for a theory
   - Index by category (Proc patterns, Name patterns, etc.)
   - Track complexity (depth, arity)

### Phase 2: Pattern Instantiation

1. **Generate hole fillers**
   ```rust
   fn instantiate_pattern(
       pattern: &RedexPattern,
       vars: &[String],
       depth: usize,
       rng: &mut R
   ) -> Term {
       let mut bindings = HashMap::new();

       // Generate terms for each hole
       for (var, category) in &pattern.holes {
           let hole_depth = allocate_depth(depth, rng);
           let term = Category::generate_random_at_depth(
               vars, hole_depth, max_collection_width, rng
           );
           bindings.insert(var, term);
       }

       // Apply constraints
       enforce_constraints(&mut bindings, &pattern.constraints);

       // Substitute into pattern
       substitute_pattern(pattern, bindings)
   }
   ```

2. **Handle special cases**
   - Collection patterns with `...rest`
   - Shared variables (unification)
   - Freshness conditions
   - Nested binders

### Phase 3: Context Wrapping

1. **Constructor compatibility analysis**
   ```rust
   enum ConstructorKind {
       Nullary,
       Unary { arg_type: Category },
       Binary { arg1_type: Category, arg2_type: Category },
       Collection { element_type: Category },
       Binder { body_type: Category },
   }

   fn can_wrap(constructor: &ConstructorKind, term_category: Category) -> bool;
   ```

2. **Implement wrapping strategies**
   - Random context depth allocation
   - Probability of wrapping vs. leaving bare
   - Prefer shallow contexts for visibility

### Phase 4: API Design

```rust
impl Category {
    /// Generate a term containing at least one redex
    pub fn generate_with_redex(
        vars: &[String],
        depth: usize,
        max_collection_width: usize
    ) -> Self;

    /// Generate a term with specific rule as redex
    pub fn generate_with_redex_from_rule(
        vars: &[String],
        depth: usize,
        max_collection_width: usize,
        rule_index: usize
    ) -> Self;

    /// Generate a term with multiple redexes
    pub fn generate_with_multiple_redexes(
        vars: &[String],
        depth: usize,
        max_collection_width: usize,
        num_redexes: usize
    ) -> Self;

    /// Generate a term and report which redexes it contains
    pub fn generate_with_redex_metadata(
        vars: &[String],
        depth: usize,
        max_collection_width: usize
    ) -> (Self, Vec<RedexInfo>);
}

struct RedexInfo {
    rule_index: usize,
    position: TermPath,
    can_fire: bool, // False if blocked by conditions
}
```

## Advanced Features

### 1. Multi-Redex Generation
Generate terms with multiple **non-overlapping** redexes:
```rust
{for(a->x0){*@(x0)}, a!(b!(0)), for(c->x1){0}, c!(0)}
// Contains 3 redexes: *@(x0), first communication, second communication
```

### 2. Nested Redex Generation
Generate terms where redexes contain other redexes:
```rust
for(a->x0){*@(*@(x0))}  // Outer *@ contains inner *@
```

### 3. Blocked Redex Generation
Generate terms that **look** like redexes but can't fire due to side conditions:
```rust
// If rule requires freshness: if x # P then ...
new(x, {for(a->x0){x0!(x)}, a!(0)})
// Looks like communication but x might not be fresh
```

### 4. Redex Statistics
Track which rules are being tested:
```rust
let stats = generate_test_suite(100);
// Rule 0 (communication): 45 terms
// Rule 1 (drop): 30 terms
// Rule 2 (open): 25 terms
```

## Alternative: Hybrid Approach

Combine multiple strategies:

```rust
pub enum GenerationStrategy {
    Random,                  // Existing random generation
    RedexGuaranteed,        // Approach 4 (redex-first)
    RedexInjected(usize),   // Approach 3 (inject N redexes)
    RedexValidated(usize),  // Approach 2 (reject until N redexes)
}

impl Category {
    pub fn generate_with_strategy(
        vars: &[String],
        depth: usize,
        max_collection_width: usize,
        strategy: GenerationStrategy
    ) -> Self;
}
```

## Testing & Validation

### Unit Tests
1. Generated terms are syntactically valid
2. Generated terms contain requested redexes
3. Redexes actually fire (no spurious patterns)
4. Distribution of rules is reasonably uniform

### Integration Tests
1. Generate 1000 terms with redexes
2. Run rewrite system on each
3. Verify all rewrites succeed
4. Compare coverage vs. random generation

### Performance Benchmarks
- Time to generate N terms with redexes
- Compare rejection sampling vs. pattern-based
- Memory usage for pattern database

## Implementation Priorities

1. **High Priority**: Basic pattern-based generation (Phase 1-2)
2. **Medium Priority**: Context wrapping for diversity (Phase 3)
3. **Low Priority**: Advanced features (multi-redex, nested)

## Open Questions

1. **Pattern extraction complexity**: Can we handle all pattern types automatically?
2. **Constraint solving**: How to handle complex side conditions efficiently?
3. **Distribution**: Should we bias toward certain rules or maintain uniformity?
4. **Composition**: How to ensure multiple redexes don't interfere?
5. **Performance**: Is rejection sampling actually slower than pattern instantiation?

## Related Work

- **QuickCheck**: Property-based testing with custom generators
- **AFL/LibFuzzer**: Coverage-guided fuzzing
- **Hypothesis**: Shrinking and targeted generation
- **CSmith**: Random C program generation with validity constraints

## Next Steps

1. Implement basic pattern extraction for simple rewrite rules
2. Create proof-of-concept for Rholang communication rule
3. Measure redex density improvement
4. Expand to handle collection patterns and binders
5. Integrate into test suite

---

*Document Status*: Initial design, ready for implementation
*Last Updated*: 2025-11-26

