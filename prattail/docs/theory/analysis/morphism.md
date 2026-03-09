# Theory Morphisms -- Cross-Theory Translation

| Property | Value |
|----------|-------|
| **Feature gate** | `morphisms` |
| **Source file** | `prattail/src/morphism.rs` (~1478 lines) |
| **Pipeline phase** | Cross-theory verification and proof transfer |
| **Lint codes** | M01 (`morphism-gap`), M02 (`preservation-failure`) |

## 1. Rationale

PraTTaIL grammars often define multiple theories (e.g., a base math theory and
an extended math theory). Verifying that one theory correctly extends or
refines another requires structure-preserving maps -- **theory morphisms**.
A morphism `phi: T1 -> T2` maps sorts to sorts, operations to operations,
and must preserve axioms. This enables proof transfer (a theorem in T1
becomes a theorem in T2 under translation) and modular verification.

## 2. Theoretical Foundations

### 2.1. Theory Morphisms

**Definition (Theory).** A theory `T = (Sorts, Ops, Axioms)` consists of:
- `Sorts`: named types (e.g., Nat, Bool, Expr)
- `Ops`: typed operations with input/output sorts
- `Axioms`: equations that must hold (e.g., `add(x, 0) = x`)

**Definition (Theory Morphism).** A morphism `phi: T1 -> T2` is a pair of maps:
- `phi_S: Sorts_1 -> Sorts_2` (sort map)
- `phi_O: Ops_1 -> Translations_2` (operation map)

such that for every axiom `l = r` in `T1`:
```
translate(phi, l) = translate(phi, r)   holds in T2
```

### 2.2. Translation Cases

The operation map supports three translation patterns:

| Case | Description | Example |
|------|-------------|---------|
| `Direct` | One-to-one operation rename | `add -> plus` |
| `Identity` | Same name in both theories | `mul -> mul` |
| `Compound` | Template-based expansion | `exp($1,$2) -> mul($1, pow($2))` |

### 2.3. Properties

**Theorem (Soundness).** If `phi: T1 -> T2` is a valid morphism (all axiom
translations hold) and `T1 |- t1 = t2`, then `T2 |- translate(phi, t1) = translate(phi, t2)`.

**Definition (Completeness).** A morphism is **complete** iff:
1. Every source sort has a mapping (no `MissingSort` gaps)
2. Every source operation has a translation (no `MissingOperation` gaps)
3. Every axiom's translation holds (no `FailedPreservation` gaps)

### 2.4. Gap Classification

| Gap Kind | Description | Severity |
|----------|-------------|----------|
| `MissingSort` | Source sort has no target mapping | Warning |
| `MissingOperation` | Source operation has no translation | Warning |
| `FailedPreservation` | Axiom translation does not hold | Error |

## 3. Algorithm Pseudocode

### 3.1. Term Translation

```
function translate_term(morphism: TheoryMorphism, term: string) -> string:
    if term contains '(' :
        op_name := term before '('
        args := split_args(term inside parentheses)
        translated_args := [translate_term(morphism, arg) for arg in args]

        match morphism.operation_map[op_name]:
            Direct { target_op }:
                return target_op + "(" + join(translated_args) + ")"
            Identity:
                return op_name + "(" + join(translated_args) + ")"
            Compound { template }:
                return template.replace("$1", translated_args[0])
                               .replace("$2", translated_args[1]) ...
            None:
                return op_name + "(" + join(translated_args) + ")"
    else:
        // Bare identifier (constant or variable)
        match morphism.operation_map[term]:
            Direct { target_op }: return target_op
            Identity: return term
            Compound { template }: return template
            None: return term
```

### 3.2. Gap Detection

```
function detect_gaps(morphism, axioms) -> Vec<MorphismGap>:
    gaps := []

    // (1) Missing sort mappings
    for sort in morphism.source_sorts:
        if sort.name not in morphism.sort_map:
            gaps.push(MissingSort(sort.name))

    // (2) Missing operation mappings
    for op in morphism.source_operations:
        if op.name not in morphism.operation_map:
            gaps.push(MissingOperation(op.name))

    // (3) Preservation failures
    for axiom in axioms:   // axiom = "lhs = rhs"
        lhs, rhs := split(axiom, " = ")
        tl := translate_term(morphism, lhs)
        tr := translate_term(morphism, rhs)
        if tl != tr:
            gaps.push(FailedPreservation(axiom, tl, tr))

    return gaps
```

### 3.3. Morphism Completion Suggestions

```
function suggest_morphism_completion(gaps, morphism) -> RepairSet:
    repairs := RepairSet::new()

    for gap in gaps:
        match gap.kind:
            MissingSort:
                // Look for same-name sort in target
                candidate := find(morphism.target_sorts, name == gap.name)
                if candidate:
                    suggest sort_map.insert(gap.name, candidate.name)
                else:
                    suggest sort_map.insert(gap.name, "<PLACEHOLDER>")

            MissingOperation:
                // Find arity-matching operations in target
                arity := source_op.arity()
                candidates := filter(morphism.target_operations, op.arity() == arity)
                suggest best candidate or placeholder

            FailedPreservation:
                // Suggest adding the translated equation to target theory
                suggest add_equation(translated_lhs, translated_rhs)

    return repairs
```

## 4. Complexity Analysis

| Operation | Time | Space |
|-----------|------|-------|
| `construct_morphism` | O(|Sorts| + |Ops|) | O(|Sorts| + |Ops|) |
| `translate_term` | O(|term| * max_arity) | O(|term|) |
| `verify_preservation` | O(|axiom| * |term|) | O(|term|) |
| `detect_gaps` | O(|Sorts| + |Ops| + |Axioms| * |term|) | O(|gaps|) |
| `suggest_morphism_completion` | O(|gaps| * |target_ops|) | O(|repairs|) |
| `split_args` | O(|term|) | O(|args|) |

Where: |term| = size of the largest term expression, |Sorts| and |Ops| are
theory sizes, |Axioms| = number of axioms.

## 5. Unicode Diagrams

### 5.1. Theory Morphism Structure

```
    Theory T1 (source)              Theory T2 (target)
    ─────────────────              ─────────────────
    Sorts: Nat, Bool               Sorts: Int, Boolean
    Ops:   add: Nat x Nat -> Nat   Ops:   plus: Int x Int -> Int
           neg: Nat -> Nat                negate: Int -> Int
           zero: -> Nat                   0: -> Int
    Axioms: add(x, zero) = x      Axioms: plus(x, 0) = x

              │                           │
              └────── phi: T1 -> T2 ──────┘
                         │
                sort_map: Nat -> Int, Bool -> Boolean
                op_map:   add -> plus, neg -> negate, zero -> 0
```

### 5.2. Gap Detection Flow

```
    ┌─────────────────────┐
    │  TheoryMorphism     │
    │  + source axioms    │
    └──────────┬──────────┘
               │
               v
    ┌─────────────────────┐
    │    detect_gaps()     │
    └──────────┬──────────┘
               │
      ┌────────┼────────┐
      │        │        │
      v        v        v
   Missing  Missing  Failed
   Sort     Operation Preservation
      │        │        │
      v        v        v
    ┌─────────────────────────┐
    │ suggest_morphism_       │
    │ completion()            │
    └──────────┬──────────────┘
               │
               v
    ┌─────────────────────┐
    │    RepairSet         │
    └─────────────────────┘
```

### 5.3. Translation Cases

```
    Direct:     add(x, y)  ──phi──>  plus(x, y)
                    │                    │
                    └── rename ──────────┘

    Identity:   mul(x, y)  ──phi──>  mul(x, y)
                    │                    │
                    └── unchanged ───────┘

    Compound:   exp(x, n)  ──phi──>  fold(mul, x, replicate(n, x))
                    │                    │
                    └── template ────────┘
```

## 6. PraTTaIL Integration

### 6.1. Pipeline Bridge Functions

- `construct_morphism(source_theory, target_theory, sort_map, op_map)` -- Builds
  a `TheoryMorphism`.
- `translate_term(morphism, term)` -- Translates a term string.
- `verify_preservation(morphism, axioms)` -- Checks all axiom translations.
- `detect_gaps(morphism, axioms)` -- Finds all gaps.
- `suggest_morphism_completion(gaps, morphism)` -- Generates repair suggestions.

### 6.2. Lint Emission

- **M01** (`morphism-gap`): Emitted for each `MissingSort` or `MissingOperation`
  gap. Severity: Warning.
- **M02** (`preservation-failure`): Emitted for each `FailedPreservation` gap.
  Severity: Error.

### 6.3. Repair Integration

Repair suggestions use `RepairKind::CompleteMorphism`. Each suggestion includes:
- For missing sorts: `sort_map.insert("source", "target")` code snippet.
- For missing operations: `operation_map.insert("source", TranslationCase::Direct { ... })`.
- For failed preservation: `AddEquation { lhs, rhs }` in the target theory.

Confidence depends on matching:
- Same-name sort in target: 0.9
- No candidate: 0.5
- Single arity-matching operation: 0.85
- Multiple candidates: 0.6 (with `alternative_count`)

## 7. Rust Implementation Notes

| Type | Role |
|------|------|
| `Sort` | Named sort with optional description |
| `Operation` | Named operation with input_sorts and output_sort |
| `TranslationCase` | Enum: Direct, Identity, Compound (with template) |
| `TheoryMorphism` | Full morphism: theories, sort_map, operation_map |
| `GapKind` | Enum: MissingSort, MissingOperation, FailedPreservation |
| `MorphismGap` | Gap with kind, source_name, description |
| `PreservationResult` | Vec of (axiom, translated_lhs, translated_rhs, preserved: bool) |

The `split_args` helper correctly handles nested parentheses by tracking
depth. Template substitution in `Compound` translation replaces `$1`, `$2`,
etc. with translated arguments.

## 8. Worked Example

**Source theory (BaseArith):**
```
Sorts: Num
Ops:   add: Num x Num -> Num
       mul: Num x Num -> Num
       zero: -> Num
Axioms: add(x, zero) = x
        mul(x, zero) = zero
```

**Target theory (ExtArith):**
```
Sorts: Integer
Ops:   plus: Integer x Integer -> Integer
       times: Integer x Integer -> Integer
       z: -> Integer
       succ: Integer -> Integer
```

**Morphism:**
```
sort_map:  Num -> Integer
op_map:    add -> plus, mul -> times, zero -> z
```

**Verification of axiom `add(x, zero) = x`:**
```
translate(add(x, zero)) = plus(translate(x), translate(zero))
                        = plus(x, z)
translate(x) = x

Check: plus(x, z) == x?  Only if target has axiom plus(x, z) = x.
If target has this axiom: Preserved.
If not: FailedPreservation gap -> suggest adding plus(x, z) = x to ExtArith.
```

**Gap detection:**
```
No missing sorts (Num mapped to Integer).
No missing operations (add, mul, zero all mapped).
Axiom mul(x, zero) = zero -> times(x, z) = z.
  If target lacks this: FailedPreservation.
  Repair: add equation "times(x, z) = z" to ExtArith.
```

## 9. References

1. Goguen, J.A. & Burstall, R.M. (1992).
   "Institutions: Abstract Model Theory for Specification and Programming."
   *Journal of the ACM*, 39(1), pp. 95--146.

2. Mossakowski, T. (2005).
   "Heterogeneous Specification and the Heterogeneous Tool Set."
   Habilitation thesis, University of Bremen.

3. Rabe, F. & Kohlhase, M. (2013).
   "A Scalable Module System."
   *Information and Computation*, 230, pp. 1--54.

4. Farmer, W.M. (2000).
   "An Infrastructure for Intertheory Reasoning."
   *Proc. 17th International Conference on Automated Deduction (CADE)*,
   LNCS 1831, Springer, pp. 115--131.

5. Sannella, D. & Tarlecki, A. (2012).
   *Foundations of Algebraic Specification and Formal Software Development*.
   Springer.
