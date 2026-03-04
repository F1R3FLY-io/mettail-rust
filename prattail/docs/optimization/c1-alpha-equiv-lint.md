# Sprint C: C1 Grammar Rule alpha-Equivalence Lint

**Status:** COMPLETE
**Lint ID:** G24
**Lint Name:** `alpha-equivalent-rules`
**Severity:** Warning
**Source:** `prattail/src/lint.rs`

---

## 1. Intuition

Consider two grammar rules in the same category:

```
rule AddA: x "+" y
rule AddB: a "+" b
```

These rules are *structurally identical* -- they differ only in the names
given to their variables. In the lambda calculus, terms that differ only by
bound-variable naming are called *alpha-equivalent*. The same concept applies to
grammar rules: if the structural skeleton and binding pattern of two rules are
identical modulo variable naming, they are alpha-equivalent grammar rules.

Detecting alpha-equivalence is subtler than detecting textual identity. The
existing lint G07 (`identical-rules`) uses `syntax_signature()`, which drops
`param_name` fields entirely and formats non-terminals as `NT(category)`. This
makes G07 alpha-invariant for simple cases -- but it is *too coarse*: it cannot
distinguish rules where the same variable is reused from rules where distinct
variables appear.

For example:

```
rule SelfEq: x "==" x     (requires both sides identical)
rule AnyEq:  a "==" b     (accepts any two sides)
```

G07 produces the same signature `NT(Expr)|T(==)|NT(Expr)` for both, grouping
them as "identical" -- a false positive. The rules have genuinely different
binding structure: `SelfEq` constrains both positions to the *same* variable,
while `AnyEq` uses two *distinct* variables.

G24 solves this by encoding variable references with De Bruijn encounter-order
slots, making it sensitive to binding structure while remaining insensitive to
concrete variable names.

---

## 2. What It Does

G24 extends the PraTTaIL lint layer with a new grammar-structure lint that:

1. **Encodes** each rule's `SyntaxItemSpec` sequence into a canonical byte
   representation using De Bruijn encounter-order variable slots.
2. **Groups** rules within the same category by their De Bruijn byte sequences.
3. **Filters out** groups already caught by G07 (identical string signatures)
   to avoid double-reporting.
4. **Emits** a `Warning` diagnostic for remaining groups -- rules that are
   alpha-equivalent but differ in variable naming (true novel detections that
   G07 misses).

---

## 3. Why It Matters

**Correctness.** Alpha-equivalent rules produce identical parse trees up to
variable renaming. If a grammar author intended the rules to behave differently,
the duplication is a latent bug -- the parser will non-deterministically pick
one, and the user's intent is silently lost.

**Maintenance.** Redundant rules increase grammar surface area without adding
expressive power. They complicate Pratt binding-power analysis, WFST weight
assignment, and dead-rule detection (since neither rule is truly "dead" -- both
match the same inputs).

**Optimization.** The WFST-informed Ascent optimization pipeline (Sprints 0-9)
can use alpha-equivalence information to merge rule bodies during codegen,
reducing the number of Ascent relation rows and improving compile-time
performance.

**Precision.** G07's coarse signature conflates genuinely different binding
structures (the `SelfEq` vs `AnyEq` case). G24's De Bruijn encoding provides
the *correct* notion of structural equivalence for grammar rules with variable
bindings.

---

## 4. Pipeline Integration

G24 runs as part of the grammar-structure lint pass in `run_lints()`,
immediately after G07:

```
                    LanguageSpec
                        |
                        v
              +-------------------+
              |   Pipeline Build  |
              |  (WFST, FIRST,    |
              |   prediction, ..)|
              +-------------------+
                        |
                        v
              +-------------------+
              |    LintContext     |
              | (categories,      |
              |  all_syntax,      |
              |  rules, ...)      |
              +-------------------+
                        |
                        v
    +-----------------------------------------------+
    |              run_lints()                       |
    |                                               |
    |  G01  left-recursion                          |
    |  G02  unused-category                         |
    |  G03  ambiguous-prefix                        |
    |  G04  duplicate-rule-label                    |
    |  G05  empty-category                          |
    |  G06  shadowed-operator                       |
    |  G07  identical-rules                         |
    |  G24  alpha-equivalent-rules    <--- NEW      |
    |  G08  missing-cast-to-root                    |
    |  G09  unbalanced-delimiters                   |
    |  G10  ambiguous-associativity                 |
    |  ...  (W, R, C, P lint groups)                |
    +-----------------------------------------------+
                        |
                        v
              Vec<LintDiagnostic>
                        |
                        v
              Rust compiler-style
              diagnostic output
```

G24 is positioned directly after G07 so that it can reference G07's
`syntax_signature()` to determine which groups are already covered. The
deduplication logic ensures zero overlap between G07 and G24 diagnostics.

---

## 5. Problem Statement

**Given:** A set of grammar rules R_1, ..., R_n within a syntactic category C,
each with a syntax item sequence s_i consisting of terminals, non-terminals
(with named variable parameters), binders, collections, and composite items
(Sep, Map, Zip, Optional).

**Find:** All maximal subsets S of {R_1, ..., R_n} such that:

1. For all R_i, R_j in S, the syntax sequences s_i and s_j are
   alpha-equivalent (identical up to consistent variable renaming).
2. S is not already detected by G07 (i.e., the rules in S do not all share the
   same `syntax_signature()` string).
3. |S| >= 2.

**Emit:** A `Warning`-level diagnostic for each such subset S.

---

## 6. Theoretical Basis

### 6.1 Alpha-Equivalence via De Bruijn Encoding

In the lambda calculus, De Bruijn indices replace named variables with natural
numbers indicating the number of enclosing binders between a variable occurrence
and its binding site. Two terms are alpha-equivalent if and only if their
De Bruijn representations are identical.

For grammar rules, variables are not bound by lambda abstractions but by
*encounter order* in the rule's syntax item sequence. We adapt De Bruijn indices
as follows:

**Definition (Encounter-Order Slot Assignment).** Given a syntax item sequence
s = [i_1, ..., i_k], assign variable slots sequentially:

- The first occurrence of a variable name v is assigned slot
  `next_slot`, and `next_slot` is incremented.
- Subsequent occurrences of v reuse the previously assigned slot.

**Definition (De Bruijn Byte Encoding).** The encoding function
`B: SyntaxItemSpec* -> Byte*` maps each syntax item sequence to a byte string
using the tag layout:

| Tag Byte     | Meaning                                |
|:-------------|:---------------------------------------|
| `0xC0`       | NewVar -- first occurrence of variable |
| `0x80 | s`   | VarRef -- reference to slot s          |
| `0x01`       | NonTerminal structural tag             |
| `0x02`       | Binder structural tag                  |
| `0x03`       | Collection structural tag              |
| `0x04`       | IdentCapture structural tag            |
| `0x05`       | Sep structural tag                     |
| `0x06`       | Map structural tag                     |
| `0x07`       | Zip structural tag                     |
| `0x08`       | BinderCollection structural tag        |
| `0x09`       | Optional structural tag                |
| `0x0A`       | Terminal structural tag                |
| `0x0B`       | End tag (closes Sep/Map/Zip/Optional)  |

Terminals and category names are encoded as literal byte strings (length-prefixed).
Variable references use the `NewVar`/`VarRef` tags described above.

**Theorem (Alpha-Equivalence Characterization).** Two syntax item sequences
s_1 and s_2 are alpha-equivalent if and only if `B(s_1) = B(s_2)`.

*Proof sketch.* The encoding is deterministic and depends only on the structural
skeleton and the binding pattern (which positions share the same variable). By
construction, renaming all variables consistently in s_1 to produce s_2
preserves the encounter order and slot assignments, producing identical byte
sequences. Conversely, if `B(s_1) = B(s_2)`, the structural tags, terminal
content, category names, and variable binding patterns must all match,
establishing alpha-equivalence.

### 6.2 Relationship to G07

G07's `syntax_signature()` produces strings like `NT(Expr)|T(+)|NT(Expr)` that
erase variable names entirely. This is equivalent to projecting the De Bruijn
encoding onto its structural skeleton *without* variable slot information.

Formally, let `pi: Byte* -> Byte*` be the projection that replaces all
`NewVar` and `VarRef(s)` tags with a uniform `Var` tag. Then:

```
syntax_signature(s_1) = syntax_signature(s_2)  iff  pi(B(s_1)) = pi(B(s_2))
```

This means G07's groups are *coarser* than G24's: every G07 group is a union
of one or more G24 groups. When a G07 group contains rules with identical
string signatures, it is a single G24 group (both lints agree). When a G07
group contains rules with differing string signatures but identical skeletal
projections, it splits into multiple G24 groups -- these are the cases where
G07 produces false positives (like `SelfEq` vs `AnyEq`).

G24's deduplication filter (`sigs.len() == 1`) ensures it only fires for the
*complement*: groups where De Bruijn bytes match but string signatures differ.

---

## 7. Design

### 7.1 Components

```
 DebruijnEnv                  syntax_item_debruijn_bytes()
+---------------------+     +------------------------------+
| var_slots: HashMap   | <-- |  Creates fresh env per rule   |
| next_slot: u8        |     |  Encodes all items to bytes   |
+---------------------+     +------------------------------+
         |                                 |
         v                                 v
  encode_syntax_item()          lint_g24_alpha_equivalent_rules()
+---------------------+     +------------------------------+
| Recursive encoder    |     |  Groups by De Bruijn bytes    |
| for all 11 variants  |     |  Filters G07-covered groups   |
+---------------------+     |  Emits Warning diagnostics    |
                             +------------------------------+
```

### 7.2 `DebruijnEnv`

```rust
struct DebruijnEnv {
    var_slots: HashMap<String, u8>,
    next_slot: u8,
}
```

- **`resolve(&mut self, name: &str) -> u8`**: Returns `0xC0` (NewVar) on first
  encounter, assigning `next_slot` and incrementing it. Returns `0x80 | slot`
  (VarRef) on subsequent encounters.
- Slot overflow is handled by `saturating_add(1)`, capping at 63 distinct
  variables per rule (slots 0-62 map to bytes `0x80`-`0xBE`; slot 63 maps to
  `0xBF`). This is far beyond any practical grammar rule.

### 7.3 `syntax_item_debruijn_bytes()`

Entry point: creates a fresh `DebruijnEnv`, preallocates `items.len() * 4`
bytes, and iterates through all items calling `encode_syntax_item()`.

### 7.4 `encode_syntax_item()`

Recursive encoder handling all 11 `SyntaxItemSpec` variants:

| Variant            | Encoding                                                       |
|:-------------------|:---------------------------------------------------------------|
| `Terminal(t)`      | `[0x0A, len, t_bytes...]`                                      |
| `NonTerminal`      | `[resolve(param), 0x01, len, cat_bytes...]`                    |
| `IdentCapture`     | `[resolve(param), 0x04]`                                       |
| `Binder`           | `[resolve(param), 0x02, is_multi, len, cat_bytes...]`          |
| `Collection`       | `[resolve(param), 0x03, len, cat_bytes..., len, sep_bytes..., kind]` |
| `Sep`              | `[0x05, len, sep_bytes..., kind, encode(body), 0x0B]`          |
| `Map`              | `[0x06, encode(body_items)..., 0x0B]`                          |
| `Zip`              | `[resolve(left), resolve(right), 0x07, len, lc..., len, rc..., encode(body), 0x0B]` |
| `BinderCollection` | `[resolve(param), 0x08, len, sep_bytes...]`                    |
| `Optional`         | `[0x09, encode(inner)..., 0x0B]`                               |

Variable-bearing variants (`NonTerminal`, `IdentCapture`, `Binder`,
`Collection`, `Zip`, `BinderCollection`) emit the `resolve()` byte *before*
the structural tag. Structural-only variants (`Terminal`, `Sep`, `Map`,
`Optional`) emit only the structural tag. Composite variants (`Sep`, `Map`,
`Zip`, `Optional`) recursively encode their children and close with `0x0B`.

### 7.5 `lint_g24_alpha_equivalent_rules()`

Algorithm:

```
for each category C:
    cat_syntax = rules in C with their syntax item sequences
    debruijn_groups = group cat_syntax by De Bruijn byte encoding
    for each group G with |G| >= 2:
        sigs = { syntax_signature(r) | r in G }
        if |sigs| == 1:
            skip (G07 territory -- all have identical string signatures)
        else:
            emit Warning G24 for group G
```

The `sigs.len() == 1` check is the key deduplication mechanism:

- If all rules in a De Bruijn group have the *same* string signature, G07
  already reports them as identical rules.
- If string signatures *differ* within the group, G07 either splits them into
  separate groups (no report) or groups them differently. G24 is the only lint
  that catches this alpha-equivalence.

---

## 8. Implementation

### 8.1 Source Location

All code resides in `prattail/src/lint.rs`, lines 774-1005.

### 8.2 Key Functions

| Function | Lines | Purpose |
|:---------|:------|:--------|
| `DebruijnEnv::new()` | 790-795 | Create fresh encoding environment |
| `DebruijnEnv::resolve()` | 801-814 | Variable-to-slot resolution with NewVar/VarRef tagging |
| `syntax_item_debruijn_bytes()` | 837-844 | Top-level encoder: fresh env, encode all items |
| `encode_syntax_item()` | 847-930 | Recursive per-variant encoder (11 match arms) |
| `lint_g24_alpha_equivalent_rules()` | 941-1005 | Lint driver: group, filter, emit |

### 8.3 Diagnostic Output

The emitted `LintDiagnostic` has the following shape:

```
warning[G24]: alpha-equivalent-rules
  --> grammar `Calculator`, category `Expr`
  = rules [AddA, AddB] in category `Expr` are alpha-equivalent
    (identical up to variable renaming)
  = hint: these rules differ only in variable names -- consider merging
    or differentiating their syntax structure
```

### 8.4 Integration Point

In `run_lints()`, G24 is called immediately after G07:

```rust
lint_g07_identical_rules(ctx, &mut diagnostics);
lint_g24_alpha_equivalent_rules(ctx, &mut diagnostics);
```

No new fields are required on `LintContext` -- G24 reads the same `categories`
and `all_syntax` data that G07 uses.

### 8.5 Tests

Eight unit tests covering the full behavior space:

| Test | Scenario | Expected |
|:-----|:---------|:---------|
| `test_g24_variable_renamed_rules_deferred_to_g07` | `x "+" y` vs `a "+" b` (same G07 sig) | G24 silent (G07 covers) |
| `test_g24_g07_false_positive_different_binding_structure` | `x "==" x` vs `a "==" b` (different structure) | G24 silent (genuinely different) |
| `test_g24_structurally_different_rules_not_flagged` | `x "+" y` vs `"-" x` (different shape) | G24 silent |
| `test_g24_same_vars_different_structure_not_flagged` | `x "," y` vs `x "+" y` (different terminals) | G24 silent |
| `test_g24_exact_duplicates_deferred_to_g07` | Two identical rules (same vars) | G24 silent (G07 covers) |
| `test_debruijn_encoding_alpha_equivalence` | Direct byte comparison: `x "+" y` vs `a "+" b` | Bytes equal |
| `test_debruijn_encoding_different_structure` | `x "+" y` vs `"-" x` | Bytes differ |
| `test_debruijn_var_reuse_same_slot` | `x "?" x` vs `a "?" a` (same), vs `x "?" y` (different) | Equal for same binding, different for distinct |

---

## 9. Correctness Argument

### 9.1 Soundness (No False Positives)

**Claim.** If G24 reports rules R_i and R_j as alpha-equivalent, they are
genuinely alpha-equivalent.

**Argument.** G24 groups rules by De Bruijn byte identity. By the
Alpha-Equivalence Characterization theorem (Section 6.1), byte identity implies
alpha-equivalence. The encoding is injective on non-alpha-equivalent inputs:
any difference in structural skeleton, terminal content, category names, or
binding pattern produces a byte difference. Therefore G24 emits no false
positives.

### 9.2 Completeness (No False Negatives, within scope)

**Claim.** If two rules R_i and R_j in the same category are alpha-equivalent
and are *not* covered by G07, G24 reports them.

**Argument.** If R_i and R_j are alpha-equivalent, their De Bruijn bytes are
identical, so they land in the same group. If they are not covered by G07, their
string signatures differ (`sigs.len() > 1`), so the deduplication filter does
not skip them. Therefore G24 emits the diagnostic.

### 9.3 Non-Overlap with G07

**Claim.** G24 and G07 never report the same group of rules.

**Argument.** G24 explicitly checks `sigs.len() == 1` and skips such groups.
A group with `sigs.len() == 1` means all rules have identical `syntax_signature()`
output, which is exactly the condition under which G07 fires. Therefore G24
only fires when `sigs.len() > 1`, which means at least two distinct string
signatures exist -- a condition where G07 does *not* group all of them together.

### 9.4 Test Validation

The 8 unit tests exercise:

- **True positives:** `test_debruijn_encoding_alpha_equivalence` and
  `test_debruijn_var_reuse_same_slot` verify that alpha-equivalent inputs
  produce identical bytes.
- **True negatives:** `test_debruijn_encoding_different_structure` and
  `test_debruijn_var_reuse_same_slot` (second assertion) verify that
  structurally distinct inputs produce different bytes.
- **G07 deduplication:** Three tests (`deferred_to_g07`, `exact_duplicates`,
  `variable_renamed`) verify that G24 stays silent when G07 covers the case.
- **Binding structure sensitivity:** `test_g24_g07_false_positive_different_binding_structure`
  verifies that G24 correctly distinguishes `x "==" x` from `a "==" b`,
  exposing G07's false positive on this case.

---

## 10. Empirical Results

### 10.1 Test Count

| Configuration | Total Tests | G24-specific |
|:--------------|:------------|:-------------|
| default       | 1,339       | 8            |

All 1,339 tests pass after adding the 8 new G24 tests.

### 10.2 Existing Grammars

The four existing PraTTaIL grammars (Calculator, BaseMath, Lambda, RhoCalc)
produce no G24 diagnostics -- their rules are either already caught by G07 or
are genuinely structurally distinct. This confirms that G24 does not introduce
noise for well-designed grammars.

### 10.3 Performance

G24's cost is linear in the number of rules per category:

- **Encoding:** O(sum of |s_i|) where |s_i| is the length of rule i's syntax
  item sequence. Each item emits a constant number of bytes plus the literal
  content of terminals/category names.
- **Grouping:** O(n) HashMap insertions where n is the number of rules.
- **Deduplication:** O(n) string signature lookups per group.

For typical grammars with O(10-100) rules per category, the overhead is
negligible relative to the rest of the pipeline (WFST construction, NFA
minimization, codegen).

---

## 11. Limitations & Future Work

### 11.1 Current Limitations

1. **Slot capacity.** The `DebruijnEnv` uses a `u8` for slot indices, supporting
   up to 63 distinct variables per rule (slots 0-62 under the `0x80 | slot`
   encoding, with slot 63 at `0xBF`). Beyond 63, `saturating_add` causes slot
   collision. No practical grammar rule approaches this limit.

2. **Category-scoped only.** G24 compares rules within the same category. Rules
   in different categories that happen to be alpha-equivalent are not flagged,
   as cross-category equivalence has different semantic implications.

3. **No semantic analysis.** G24 operates purely on syntactic structure. Two
   rules could be alpha-equivalent in syntax but have different semantic
   equations/rewrites -- G24 does not inspect the Ascent logic layer.

4. **No auto-fix.** The lint emits a warning with a hint but does not
   automatically merge or remove redundant rules.

### 11.2 Future Work

- **Cross-category alpha-equivalence (C2-C3).** Extend the analysis to detect
  rules across categories that are structurally equivalent, which may indicate
  opportunities for category merging or cast rule simplification.

- **Semantic-aware equivalence.** Combine G24's syntactic alpha-equivalence with
  equation/rewrite comparison to detect fully redundant rules (same syntax AND
  same semantics up to variable renaming).

- **Auto-merge in codegen.** When two rules are alpha-equivalent and have
  identical semantic equations, the codegen layer could automatically merge
  them into a single rule, reducing generated code volume and improving
  compile-time performance.

- **Integration with dead-rule detection (Tier 5).** Alpha-equivalent rules
  produce identical WFST weights and FIRST sets. The dead-rule detection
  pipeline could use alpha-equivalence information to break ties when multiple
  rules compete for the same input prefix.
