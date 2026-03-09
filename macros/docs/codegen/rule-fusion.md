# BCG02: Deconstruction-Rewrite Chain Fusion

**Source**: [`macros/src/logic/fusion.rs`](../../src/logic/fusion.rs)

## 1. Overview / Purpose

The rule fusion module implements BCG02: detection and code generation for
fused deconstruction-rewrite chains. In the standard Ascent codegen pipeline,
a term is first deconstructed (extracting subterms into category relations),
then a separate rewrite rule matches the extracted subterm. This two-step
process creates an intermediate tuple -- the extracted subterm in the `cat`
relation -- that exists solely to trigger the rewrite rule.

BCG02 identifies chains where this intermediate tuple can be eliminated by
*fusing* the deconstruction and rewrite into a single Ascent rule. The fused
rule directly destructures the parent constructor and applies the rewrite
pattern match in one step, firing in the same Ascent iteration as the parent
deconstruction.

The fused rules are **additive**: the original unfused rules remain for
correctness. The fused rules provide an alternative, faster derivation path.

## 2. Architecture and Data Flow

```
 LanguageDef
     |
     v
 detect_fusion_candidates(language)
     |
     +---> build_subterm_map(language)
     |         |
     |         v
     |     (ctor_idx, ctor_label, parent_cat, {target_cats})
     |
     +---> collect_rewrite_lhs_info(language)
     |         |
     |         v
     |     (rewrite_idx, RewriteLhsInfo{name, constructor, category})
     |
     +---> build_constructor_consumer_map(language)
     |         |
     |         v
     |     HashMap<(category, constructor), HashSet<consumer_name>>
     |
     v
 Vec<FusionCandidate>  ──> analyze_fusion_potential()  ──> FusionReport
     |                                                         |
     |                                                         v
     |                                              emit_fusion_diagnostics()
     |                                                     (G42 lints)
     v
 generate_all_fused_rules(language)
     |
     +---> for each safe candidate:
     |         generate_fused_rule(candidate, language)
     |             |
     |             v
     |         TokenStream (fused Ascent rule)
     v
 (Vec<TokenStream>, count)
```

## 3. Key Types and Functions

### `FusionCandidate`

```rust
pub struct FusionCandidate {
    pub decon_rule_idx: usize,            // Index into language.terms
    pub decon_constructor: String,        // e.g., "PPar"
    pub parent_category: String,          // e.g., "Proc"
    pub rewrite_rule_idx: usize,          // Index into language.rewrites
    pub rewrite_name: String,             // e.g., "Exec"
    pub rewrite_lhs_constructor: String,  // e.g., "PDrop"
    pub rewrite_category: String,         // e.g., "Proc"
    pub is_safe: bool,                    // Single consumer?
    pub blocking_consumers: Vec<String>,  // Other consumers preventing fusion
}
```

### `FusionReport`

```rust
pub struct FusionReport {
    pub candidates: Vec<FusionCandidate>,
    pub safe_count: usize,
    pub blocked_count: usize,
    pub estimated_tuple_reduction: usize,
}
```

### Public API

| Function                     | Returns                         | Purpose                              |
|------------------------------|---------------------------------|--------------------------------------|
| `detect_fusion_candidates`   | `Vec<FusionCandidate>`          | Identify all candidate chains        |
| `analyze_fusion_potential`   | `FusionReport`                  | Summary with counts and estimates    |
| `emit_fusion_diagnostics`    | `()`                            | Emit G42 lint diagnostics            |
| `generate_all_fused_rules`   | `(Vec<TokenStream>, usize)`     | Generate fused Ascent rules          |

### Internal Helpers

| Function                       | Purpose                                          |
|--------------------------------|--------------------------------------------------|
| `build_subterm_map`            | Map constructors to their extracted target categories |
| `collect_rewrite_lhs_info`     | Identify non-congruence rewrites with simple LHS |
| `extract_simple_constructor_lhs` | Check if a pattern is a simple Apply             |
| `build_constructor_consumer_map` | Map (category, constructor) to consumer rule names |
| `generate_fused_rule`          | Generate a single fused Ascent rule              |

## 4. Algorithm Description

### Phase 1: Subterm Extraction Map

```
for each grammar rule (constructor) with index idx:
    parent_cat = rule.category
    target_cats = {}
    for each field in rule.term_context or rule.items:
        if field type is a known category:
            target_cats.add(field_type)
    if target_cats is non-empty:
        yield (idx, rule.label, parent_cat, target_cats)
```

This captures which constructors produce subterms of which categories during
deconstruction.

### Phase 2: Rewrite LHS Collection

```
for each rewrite rule with index idx:
    if rewrite is congruence rule: skip
    if rewrite.left is Pattern::Term(PatternTerm::Apply { constructor, .. }):
        category = language.category_of_constructor(constructor)
        yield (idx, {name, constructor, category})
```

Only simple constructor LHS patterns are eligible -- nested patterns,
collections, and metasyntax complicate fusion.

### Phase 3: Consumer Map Construction

```
consumer_map: HashMap<(category, constructor_label), HashSet<consumer_name>>

for each equation:
    collect constructor labels from LHS and RHS
    for each label:
        consumer_map[(category, label)].add("eq:<equation_name>")

for each rewrite:
    collect constructor labels from LHS and RHS
    for each label:
        consumer_map[(category, label)].add("rw:<rewrite_name>")
```

### Phase 4: Chain Matching and Safety Check

```
for each rewrite_info in rewrite_lhs_info:
    for each (decon_idx, decon_label, parent_cat, target_cats) in subterm_map:
        if rewrite_info.category NOT IN target_cats: continue
        // Chain found: deconstruction extracts to a category that the rewrite matches
        consumer_key = (rewrite_info.category, rewrite_info.constructor)
        rw_consumer_name = "rw:<rewrite_name>"
        other_consumers = consumer_map[consumer_key] - {rw_consumer_name}
        is_safe = other_consumers.is_empty()
        yield FusionCandidate { ..., is_safe, blocking_consumers: other_consumers }
```

### Safety Conditions

A chain is safe to fuse only if ALL of these hold:

1. **Single consumer**: The intermediate constructor in the category relation
   is consumed *only* by the candidate rewrite rule. No other equations,
   rewrites, or logic rules reference that constructor's subterms.

2. **No premises**: The rewrite rule has no premises (congruence rules and
   conditional rewrites are excluded).

3. **Simple LHS**: The rewrite LHS is a constructor application (possibly
   with nested patterns, but the outer constructor must be identifiable).

### The "Exec" vs "rw:Exec" Bug and Fix

The original implementation used bare rewrite names for the consumer map
check (e.g., `"Exec"`), while the consumer map stored prefixed names
(e.g., `"rw:Exec"`). This caused all candidates to appear as having
multiple consumers, blocking all fusions.

The fix was to construct the consumer name with the `rw:` prefix:

```rust
let rw_consumer_name = format!("rw:{}", rw_info.name);
```

## 5. Generated Code Patterns

### Before (unfused -- two separate rules):

```
// Step 1: Deconstruction -- extract Name subterms from PDrop
name(sub) <-- proc(t), for sub in all_subterms_proc_name(t);

// Step 2: Rewrite -- match PDrop(NQuote(P)) and produce P
rw_proc(s_orig.clone(), t) <--
    eq_proc(s_orig, s),
    if let Proc::PDrop(f0) = s,
    let f0_deref = &**f0,
    if let Name::NQuote(f0_f0) = f0_deref,
    let p = f0_f0.clone(),
    let t = p.clone().normalize();
```

The intermediate `name(sub)` tuple exists only to make `NQuote(P)` available
for the rewrite rule's pattern match.

### After (fused -- single combined rule):

```
// Fused: directly match parent constructor and apply rewrite in one step
rw_proc(s_orig.clone(), __fused_result) <--
    eq_proc(s_orig, __fused_parent),
    if let Proc::PDrop(ref __fused_f0) = __fused_parent,
    let __fused_sub = __fused_f0.as_ref().clone(),
    if let Name::NQuote(f0_f0) = __fused_sub,   // rewrite LHS matching
    let p = f0_f0.clone(),
    // BCG05 dedup guard
    if {
        use std::hash::{Hash, Hasher};
        let mut __bcg05_h = std::hash::DefaultHasher::new();
        __fused_parent.hash(&mut __bcg05_h);
        // ... epoch-scoped dedup ...
    },
    let __fused_result = (p.clone()).normalize();
```

The original unfused rules are **preserved** -- the fused rule is additive.
It provides an alternative derivation path that fires in the same iteration
as the parent deconstruction, eliminating one iteration of latency.

### Fused Rule Generation (pseudocode)

```
generate_fused_rule(candidate, language):
    parent_rule = language.terms[candidate.decon_rule_idx]
    rewrite = language.rewrites[candidate.rewrite_rule_idx]

    // Skip congruence rules and rewrites with premises
    if rewrite.is_congruence_rule() or !rewrite.premises.is_empty(): return None

    // Build parent constructor destructuring
    fields = enumerate parent_rule's field types
    matching_fields = fields where type == rewrite_category

    for each matching_field_index:
        // 1. Match via eq_parent relation
        // 2. Destructure parent constructor
        // 3. Extract the matching field
        // 4. Apply rewrite LHS pattern matching on extracted field
        // 5. BCG05 dedup guard
        // 6. Compute and normalize RHS
        yield fused Ascent rule TokenStream
```

## 6. Integration with Pipeline

### Analysis Phase (diagnostics)

Called from `mod.rs::generate_ascent_source()` at step 7:

```rust
fusion::emit_fusion_diagnostics(language, &grammar_name);
```

This runs the full detection pipeline and emits G42 diagnostics summarizing
the fusion opportunities.

### Code Generation Phase (fused rules)

Called from `mod.rs::generate_ascent_source()` at step 11:

```rust
let (fused_rules, fused_count) = fusion::generate_all_fused_rules(language);
```

The generated fused rules are appended to the raw Ascent content alongside
the original rules:

```rust
let raw_content = quote! {
    #relations
    #category_rules
    #equation_rules
    #rewrite_rules
    #fused_content      // <-- fused rules appended here
    #custom_logic
};
```

## 7. Diagnostic Emissions

| Lint ID | Name                    | Severity | Trigger                               |
|---------|-------------------------|----------|---------------------------------------|
| G42     | `rule-fusion-analysis`  | Note     | Summary of all candidates detected    |
| G42     | `rule-fusion-candidate` | Note     | Per-candidate detail (verbose only)   |
| G42     | `rule-fusion-codegen`   | Note     | Count of fused rules generated        |

The summary diagnostic includes:
- Total candidate count
- Safe vs. blocked breakdown
- Estimated tuple reduction

Per-candidate diagnostics (verbose mode via `PRATTAIL_LINT_VERBOSE=1`):
- Deconstruction constructor and parent category
- Rewrite name and category
- Status: SAFE or BLOCKED (with blocking consumer names)

## 8. Test Coverage

The module includes 7 unit tests in `fusion.rs::tests`:

| Test                                            | What it verifies                        |
|-------------------------------------------------|-----------------------------------------|
| `test_detect_simple_chain`                      | Basic PDrop/NQuote chain detection      |
| `test_detect_chain_calculator_style`            | No candidates without rewrites          |
| `test_multiple_consumers_block_fusion`           | Multiple consumers correctly block fusion |
| `test_no_candidates_without_matching_constructors` | Nullary constructors yield no candidates |
| `test_fusion_report_counts`                     | Report arithmetic (safe + blocked = total) |
| `test_fusion_report_empty_language`             | Empty language yields empty report      |
| `test_congruence_rules_excluded_from_candidates` | Congruence rewrites excluded            |

Additional integration coverage comes from the full language compilation tests
(RhoCalc, Lambda, Calculator, etc.) which exercise the fused rule generation
through actual Ascent compilation.

## 9. Source References

- **Primary source**: [`macros/src/logic/fusion.rs`](../../src/logic/fusion.rs) (~1000 lines)
- **Invocation sites**: [`macros/src/logic/mod.rs`](../../src/logic/mod.rs), lines ~194 and ~252
- **Rocq proof**: [`formal/rocq/codegen_optimizations/theories/BCG02_RuleFusion.v`](../../../formal/rocq/codegen_optimizations/theories/BCG02_RuleFusion.v)

## 10. Cross-References

- [rule-generation.md](rule-generation.md) -- `generate_rule_clause` used for LHS/RHS pattern codegen in fused rules
- [equation-system.md](equation-system.md) -- equations appear as consumers in the consumer map
- [congruence-closure.md](congruence-closure.md) -- congruence rules are explicitly excluded from fusion
- [bloom-filter.md](bloom-filter.md) -- BCG05 dedup guards are emitted inside fused rules
- [`docs/design/codegen-optimization-catalog.md`](../../../docs/design/codegen-optimization-catalog.md) -- BCG02 catalog entry
