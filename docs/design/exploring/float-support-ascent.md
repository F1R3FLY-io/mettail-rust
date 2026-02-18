# Float Support in Ascent Datalog

**Status:** Implemented (Option A)  
**Context:** Enabling `![f64] as Float` (and f32) in language definitions; Float is now supported via a canonical wrapper type in the runtime so that Ascent relation types (which require `Eq` and `Hash`) are satisfied.

## Implementation (Option A)

- **Runtime:** `runtime/src/canonical_float.rs` defines `CanonicalFloat64` and `CanonicalFloat32` with canonicalization (NaN → single pattern, -0 → +0), `Eq`/`Hash`/`Ord`, `BoundTerm`, and arithmetic ops. Re-exported from `runtime/src/lib.rs`.
- **Macros:** In `macros/src/gen/types/enums.rs`, float categories use the canonical type as the literal payload and derive full `Eq`/`Hash`/`Ord`; `literal_payload_type` and `type_expr_to_field_type` return the wrapper for FloatLiteral. Parser in `macros/src/gen/syntax/parser/lalrpop.rs` wraps parsed floats with `CanonicalFloat64::from(f)` (or `CanonicalFloat32`). Display, term_gen/random, and native/eval use the wrapper; eval return type for float categories is the wrapper.
- **Languages:** Float enabled in `languages/src/calculator.rs` with `![f64] as Float`, `EqFloat`, `AddFloat`, and congruence rules. Integration test in `languages/tests/calculator.rs` (`test_float_literal_parse`) parses a float and checks the canonical wrapper.

The options and rationale below are preserved for reference.

---

## 1. Problem

Ascent Datalog stores relation tuples in indexed structures that require all relation component types to implement `Eq` and `Hash`. The standard library does not implement these traits for `f32`/`f64` because:

- Floating-point equality is not reflexive for NaN (`NaN != NaN`).
- There is no canonical total order or hash that respects IEEE 754 and is consistent across platforms.

Consequences in this codebase:

- **Per-category enums** (e.g. `Float`) already skip `Eq`/`Ord`/`Hash` for float native types in `macros/src/gen/types/enums.rs`, so a Float category enum can be generated, but:
- **Ascent relations** that mention Float (e.g. `relation eq_float(Float, Float)`, `relation float(Float)`, or custom `relation rw_weight(Proc, Int, Proc)` if we had `relation foo(Proc, Float)`) are generated for every category; Ascent’s expansion requires each relation’s tuple type to be `Eq + Hash`.
- **Multi-category inner enum** (`RhoCalcTermInner`, etc.) is derived with `Clone, PartialEq, Eq, Hash`. If one variant is `Float(Float)` and `Float` does not implement `Eq`/`Hash`, the inner enum no longer compiles.
- **Term trait** and **term_id** use `Hash` and `PartialEq`/`Eq` on the wrapped value; single-category `Term` and multi-category inner enum both require the stored type to support these traits.
- **HashBag** and any collection type used in term parameters require element type `Clone + Hash + Eq`; a constructor like `PPar(HashBag(Proc))` does not put Float in a bag, but a hypothetical `SomeBag(Float)` would.

We cannot implement `Eq`/`Hash` for `f64` in our crate (orphan rules); we need a type we control that wraps the float and implements the required traits with explicit semantics.

---

## 2. Scope

- **In scope:** Enabling Float (f32/f64) as a first-class category so that:
  - Relations `float(Float)`, `eq_float(Float, Float)`, `rw_float(Float, Float)`, and any custom logic relations using Float type compile and run.
  - Single- and multi-category languages work (inner enum, Term, term_id, equation/rewrite/congruence rules).
  - Float can appear in constructors (e.g. `CastFloat . k:Float |- k : Proc`) and in custom relations.
- **Out of scope:** Changing Ascent’s requirement for `Eq`/`Hash`; changing Rust’s stance on `f64`; supporting Float inside `HashBag`/`HashSet` in term parameters (that would require the same wrapper type as the category representation).

---

## 3. Options

### Option A: Wrapper type in runtime (recommended)

Introduce a type in `mettail_runtime` that wraps `f64` (and optionally `f32`) and implements `Eq`, `Hash`, and optionally `Ord` with documented semantics.

- **Representation:** e.g. `pub struct CanonicalFloat64(f64)` with canonicalization in constructor (e.g. normalize NaN to a single bit pattern; optionally -0 to +0).
- **Eq:** Equal if bitwise equal after canonicalization, so NaN equals NaN.
- **Hash:** Hash the canonical bit pattern (e.g. `u64`).
- **Ord:** Total order (e.g. via `ordered_float::OrderedFloat` or custom: NaN last, then numeric order).

**Pros:**

- Single point of definition; all generated code (enums, relations, inner enum, Term) uses this type.
- No change to Ascent or to relation generation logic beyond using the wrapper for float categories.
- Works for both single- and multi-category languages and for custom logic relations.
- Optional dependency (e.g. `ordered_float`) can be feature-gated if we want to avoid it.

**Cons:**

- Float equality in the theory is “canonical float” equality, not raw `PartialEq` for f64 (e.g. -0 and +0 may be equal; NaNs equal).
- One extra indirection when reading the numeric value (`.0` or accessor).

**Risks:**

- Semantics must be documented and stable (canonical form, NaN handling, -0/+0). Wrong choices can surprise users (e.g. if NaN != NaN in our type, Ascent deduplication could treat two NaN terms as distinct).
- If a language exposes raw `f64` elsewhere (e.g. in native eval blocks), conversion to/from `CanonicalFloat64` must be explicit and consistent.

**Implementation notes:**

- Category `Float` (native type f64) would be represented as the wrapper in the generated enum (e.g. `NumLit(CanonicalFloat64)` or a type alias `Float = CanonicalFloat64` in generated code). Parser and literal payload stay f64; conversion at enum construction.
- Per-category enum derives: for float categories, use the wrapper so we can keep `Eq`/`Hash`/`Ord` on the enum.
- Multi-category inner enum: no change to derives; Float variant holds the wrapper.
- Relation generation: unchanged; the wrapper type satisfies Ascent’s bounds.

---

### Option B: ordered_float (or similar) as the category type

Use `ordered_float::OrderedFloat<f64>` (or `NotNan` if we want to reject NaN) as the Rust type for the Float category.

**Pros:**

- No new type to maintain; well-used crate with clear semantics.
- Implements `Eq`, `Hash`, `Ord`; fits Ascent and inner enum.

**Cons:**

- Adds a dependency; API may not match our naming (e.g. `OrderedFloat` vs `Float` in theory).
- NotNan panics on NaN; OrderedFloat has a defined NaN ordering. We must choose and document.

**Risks:**

- Dependency stability and maintenance. If we need different semantics later, we still need a wrapper.

**Implementation notes:**

- In type generation, for float native types emit `ordered_float::OrderedFloat<f64>` (or f32) instead of `f64`; parser produces f64, then wrap at enum construction. Rest same as Option A (derives, relations, inner enum all work).

---

### Option C: Exclude float categories from Ascent

Do not generate relations for float categories (no `float(Float)`, no `eq_float`, no `rw_float`); treat Float as “non-relational” and do not allow Float in custom logic relation signatures.

**Pros:**

- No wrapper; language can still have a Float category with f64 as payload for parsing and eval.
- No dependency.

**Cons:**

- Float terms cannot participate in equality or rewrite relations; equations/rewrites that mention Float cannot be expressed in Ascent.
- Multi-category inner enum still requires Float to be `Eq`/`Hash` if Float is a variant (because the inner enum is derived with Eq/Hash). So we would have to either remove Float from the inner enum (no multi-category with Float) or still use a wrapper. So this option does not fully avoid a representation that supports Eq/Hash for Float when Float is in the term model.

**Risks:**

- Feature is incomplete and may confuse users (Float exists but “doesn’t work with Ascent”).

**Conclusion:** Option C does not remove the need for an Eq+Hash-capable representation for Float in multi-category or in any relation; at best it defers it. Not recommended as the primary approach.

---

### Option D: Separate “relation representation” for Float

Keep the category enum as `f64` (no Eq/Hash), and maintain a separate mapping (e.g. term_id or a side table) so that Ascent relations store a surrogate (e.g. integer id) for Float terms; look up the actual Float when reading relations back.

**Pros:**

- Theory-level Float remains raw f64 if desired.

**Cons:**

- Large change: relation generation, seeding, and extraction would need to know about Float and use surrogates; custom logic relations that mention Float would need to work with surrogates or a different API.
- Two representations for the same concept; easy to get out of sync and harder to reason about.

**Risks:**

- Complexity and bug surface; custom logic blocks would need clear semantics (do they see floats or ids?). Not recommended unless we have a hard requirement to avoid any wrapper type.

---

## 4. Recommendation

**Option A (wrapper in runtime)** is the preferred direction:

- Minimal conceptual and generated-code impact: one type, one set of semantics, used everywhere Float appears in types (category enum, inner enum, relations).
- No mandatory new dependency if we implement a small canonical-float wrapper ourselves; we can still consider `ordered_float` for the Ord implementation or as an optional alternative.
- Aligns with existing pattern (e.g. OrdVar wrapping Var for Hash/Ord); Float is another “language value” that needs to live in Ascent and in Term.

**Alternative:** If we prefer to avoid maintaining our own float semantics, **Option B** (ordered_float) is a reasonable alternative with the same architecture (wrapper used as the category type); we then document and stick to that crate’s semantics (including NaN and -0/+0).

**Decision to document:** Choose and document (1) NaN handling (e.g. all NaN equal, single canonical NaN), (2) -0 vs +0, (3) whether Ord is required for Float (e.g. for HashBag(Float) or sorting). If we never put Float in HashBag, Ord is optional but useful for deterministic ordering in debug/output.

---

## 5. Implementation outline (Option A)

1. **Runtime**
   - Add `CanonicalFloat64` (and optionally `CanonicalFloat32`) in `mettail_runtime`: wrap f64, canonicalize in constructor (NaN → one bit pattern; optionally -0 → +0), implement `Clone`, `PartialEq`, `Eq`, `Hash`, `PartialOrd`, `Ord`, `Debug`, `Display`, and `BoundTerm` as needed. Provide `From<f64>` and accessor (e.g. `.get()`) for use in native eval and display.

2. **Macros – type generation**
   - In `gen/types/enums.rs`: for a category with native type f32/f64, use the canonical float type as the literal variant payload (and anywhere the category is used as a type). Remove the “omit Eq/Ord/Hash for float” branch for the category enum so the Float enum derives the same as others (the payload type now implements Eq/Hash).
   - Ensure literal construction in parser and in generated code converts `f64` → canonical type when building enum variants.

3. **Macros – runtime / Term**
   - Single-category: if the only category is Float, the term wrapper’s `.0` is the Float enum (which now has Eq/Hash). No change to Term/term_id beyond type.
   - Multi-category: inner enum already derives Eq/Hash; Float variant now holds the wrapper type, so no change to derives.

4. **Macros – logic**
   - Relations already generated per category; no change. Float category relations (float(Float), eq_float(Float, Float), rw_float(Float, Float), fold_float if applicable) will use the wrapper type and satisfy Ascent.
   - Custom logic relations that use Float in their signature work as-is because the parameter type is the category type (now the wrapper).

5. **Parsing / display**
   - Parser produces f64 from FloatLiteral; action code constructs the canonical wrapper and stores it in the enum variant. Display uses the wrapper’s Display or `.get()` to show the number.

6. **Tests**
   - Unit tests for canonical type (Eq, Hash, Ord, NaN, -0).
   - At least one language (e.g. calculator or a small stub) with Float category: parsing, equations/rewrites involving Float, and Ascent run (relations populated, no compile errors).

7. **Documentation**
   - Document the wrapper’s semantics (NaN, -0, ordering) in the runtime and in the language author guide (e.g. “Float in theories uses canonical float equality”).

---

## 6. Summary

| Option | Effort | Risk | Use when |
|--------|--------|------|----------|
| A – Wrapper in runtime | Medium | Low (if semantics fixed) | Default: full Float support with one clear representation. |
| B – ordered_float | Low | Low | Prefer to avoid maintaining float semantics. |
| C – Exclude from Ascent | Low | High (incomplete feature, inner enum still blocks) | Not recommended. |
| D – Surrogate in relations | High | High | Only if raw f64 in theory is a hard requirement. |

The blocker for Float today is Ascent’s `Eq`/`Hash` requirement on relation types; the same requirement appears in the multi-category inner enum and Term. Using a single wrapper type (our own or from `ordered_float`) for the Float category everywhere resolves the blocker with minimal structural change and keeps the design consistent and maintainable.
