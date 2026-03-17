# Alpha-Equivalence via De Bruijn Canonicalization

PraTTaIL uses De Bruijn-style variable numbering to canonicalize patterns for alpha-equivalence detection. Two patterns that differ only in variable names produce identical byte sequences, enabling PathMap trie operations to automatically group alpha-equivalent patterns.

**Prerequisites:** [Foundations](../triemaps-that-match/foundations.md), [Pattern Indexing](../triemaps-that-match/pattern-indexing.md)

---

## 1. The Problem

Consider two equation rules:

```text
f(x, y) == g(x, y)
f(a, b) == g(a, b)
```

These are alpha-equivalent: they have the same structure, differing only in variable names. The pattern trie must recognize them as identical to avoid:
- Duplicate trie entries (wasted space)
- Missed alpha-equivalence groups (incorrect stratification)
- False subsumption negatives (identical rules not detected)

---

## 2. De Bruijn's Solution (1972)

N. G. de Bruijn proposed replacing variable names with indices encoding the *binding distance*: how many binders one must traverse outward to reach the variable's binding site.

For closed lambda terms:

```text
λx. λy. x(y)    →    λ. λ. 1(0)
λa. λb. a(b)    →    λ. λ. 1(0)     (identical!)
```

The index `0` refers to the innermost binder, `1` to the next one out, etc.

---

## 3. PraTTaIL's Adaptation: Introduction-Order Numbering

PraTTaIL uses a variation on De Bruijn indices: instead of *binding distance*, variables are numbered by **introduction order** in left-to-right pre-order traversal.

### EncodingEnv

The encoding environment (`pattern_codec.rs:73-122`) tracks variable slots:

```rust
struct EncodingEnv {
    var_slots: HashMap<String, u8>,  // name → slot index
    next_slot: u8,                   // next available slot
}
```

- First variable encountered → slot 0
- Second distinct variable → slot 1
- Repeated variable → same slot as first occurrence

### Variable Resolution

```rust
fn resolve_var(&mut self, name: &str) -> (bool, u8) {
    if let Some(&slot) = self.var_slots.get(name) {
        (false, slot)    // Previously seen: emit VarRef(slot)
    } else {
        let slot = self.next_slot;
        self.next_slot += 1;
        self.var_slots.insert(name.to_string(), slot);
        (true, slot)     // First occurrence: emit NewVar
    }
}
```

### Encoding Output

| First occurrence | Byte emitted | Tag |
|-----------------|-------------|-----|
| Yes | `0xC0` (NewVar) | Introduce fresh variable |
| No | `0x80 \| slot` (VarRef) | Reference to previously introduced variable |

---

## 4. Tag Byte Layout

The full encoding uses a MORK-compatible 2-bit prefix scheme:

```text
 Bits     Range           Tag             Description
 ──────   ────────────    ──────────      ───────────────────────
 0b00     0x00-0x3F       Arity(a)        Constructor with a children
 0b01     0x40-0x4B       Extension       PraTTaIL-specific (collections, lambdas, ...)
 0b10     0x80-0xBF       VarRef(i)       Reference to i-th introduced variable
 0b11_00  0xC0            NewVar          Introduce a fresh variable
 0b11_xx  0xC1-0xFE       SymbolSize(s)   Next s bytes are a constructor name
 0b11_11  0xFF            ExtTag          Reserved for future use
```

### 2-Bit Prefix Decoding

```text
Given byte b:
  if (b & 0xC0) == 0x00:  Arity tag,    arity = b
  if (b & 0xC0) == 0x40:  Extension tag, kind = b & 0x3F
  if (b & 0xC0) == 0x80:  VarRef tag,   slot = b & 0x3F
  if b == 0xC0:           NewVar
  if b >= 0xC1 && b <= 0xFE:  SymbolSize, size = b - 0xC0
  if b == 0xFF:           ExtTag (reserved)
```

### Encoding a Constructor Application

`f(x, y)` where `f` has 2 children:

```text
Step 1: Arity(2)                    → 0x02
Step 2: SymbolSize(1)               → 0xC1
Step 3: Symbol bytes "f"            → 0x66
Step 4: x is new (slot 0)           → 0xC0 (NewVar)
Step 5: y is new (slot 1)           → 0xC0 (NewVar)

Result: [0x02, 0xC1, 0x66, 0xC0, 0xC0]
```

`f(a, b)` produces the same bytes (names erased, same structure):

```text
[0x02, 0xC1, 0x66, 0xC0, 0xC0]    (identical!)
```

### Encoding a Repeated Variable

`f(x, x)`:

```text
Step 1: Arity(2)                    → 0x02
Step 2: SymbolSize(1)               → 0xC1
Step 3: Symbol bytes "f"            → 0x66
Step 4: x is new (slot 0)           → 0xC0 (NewVar)
Step 5: x already seen (slot 0)     → 0x80 (VarRef(0))

Result: [0x02, 0xC1, 0x66, 0xC0, 0x80]
```

This differs from `f(x, y)` because `0x80 ≠ 0xC0` — correctly distinguishing repeated from fresh variables.

---

## 5. Binder Handling

Lambda patterns require scope management to correctly handle shadowing:

```rust
fn introduce_binder(&mut self, name: &str) -> (u8, Option<u8>) {
    let prev = self.var_slots.get(name).copied();
    let slot = self.next_slot;
    self.next_slot += 1;
    self.var_slots.insert(name.to_string(), slot);
    (slot, prev)
}

fn restore_binder(&mut self, name: &str, prev: Option<u8>) {
    match prev {
        Some(old_slot) => { self.var_slots.insert(name.to_string(), old_slot); }
        None => { self.var_slots.remove(name); }
    }
    self.next_slot -= 1;
}
```

This ensures that `λx.f(x)` and `λy.f(y)` produce identical bytes:

```text
λx.f(x):  [0x48, slot₀, 0x01, 0xC1, 0x66, 0x80|slot₀]
λy.f(y):  [0x48, slot₀, 0x01, 0xC1, 0x66, 0x80|slot₀]  (identical!)
```

The binder's name is erased; only its slot index matters.

---

## 6. MORK Compatibility

MORK (`/home/dylon/Workspace/f1r3fly.io/MORK/expr/src/lib.rs`) uses the identical 2-bit prefix scheme:

| Prefix | MORK | PraTTaIL | Compatible? |
|--------|------|----------|:-----------:|
| `0b00` | Arity | Arity | Yes |
| `0b10` | VarRef | VarRef | Yes |
| `0b11_00` | NewVar | NewVar | Yes |
| `0b11_xx` | SymbolSize | SymbolSize | Yes |
| `0b01` | — | Extensions (0x40-0x4B) | PraTTaIL-only |

PraTTaIL adds the `0b01` extension range (0x40-0x4B) for collections, lambdas, substitutions, maps, and zips. These tags do not exist in MORK, which has a simpler expression language. The core encoding (Arity, VarRef, NewVar, SymbolSize) is byte-compatible.

---

## 7. Alpha-Equivalence Guarantee

> **Theorem.** For patterns `p` and `q` over the same grammar,
> `encode(p) = encode(q)` if and only if `p ≡α q`.

### Proof

**(⇒) If `encode(p) = encode(q)` then `p ≡α q`.**

The encoding deterministically traverses the pattern in pre-order, emitting bytes that depend only on:
1. The constructor structure (Arity, SymbolSize, symbol bytes)
2. Whether each variable is a first occurrence (NewVar) or a reference (VarRef(slot))
3. The introduction order of variables

If `encode(p) = encode(q)`, then at every position in the traversal, `p` and `q` have the same constructor (or variable introduction/reference) with the same structure. They can differ only in the *names* assigned to variables at introduction sites. Any bijection mapping `p`'s variable names to `q`'s (preserving introduction order) witnesses alpha-equivalence.

**(⇐) If `p ≡α q` then `encode(p) = encode(q)`.**

By definition, `p ≡α q` means there exists a bijection on variable names such that `p` and `q` are syntactically identical under that bijection. The encoding erases variable names and assigns slots by introduction order. Since the bijection preserves introduction order (it maps the i-th introduced variable in `p` to the i-th in `q`), every NewVar and VarRef byte matches. Constructor structure is preserved exactly. Therefore the byte sequences are identical.  ∎

---

## 8. Connection to the Paper (§4)

Peyton Jones & Graf (§4) address alpha-equivalence using:

| Paper concept | PraTTaIL equivalent |
|---------------|-------------------|
| `DBEnv` | `EncodingEnv` |
| `BoundKey` | `u8` slot index (0-63) |
| `AlphaExpr` | Byte sequence from `pattern_to_debruijn_bytes()` |
| De Bruijn leveling | Introduction-order numbering |
| `lookupBE` / `insertBE` | `resolve_var()` / `introduce_binder()` |

The paper uses De Bruijn *levels* (counting from the outermost binder inward) rather than De Bruijn *indices* (counting from the innermost binder outward). PraTTaIL's introduction-order numbering is equivalent to levels for the purpose of alpha-equivalence: both assign a canonical index to each binding site that is independent of the variable name.

---

## 9. Size Estimation and Preallocation

The encoding preallocates the output buffer using a conservative size estimate (`pattern_codec.rs:127-166`):

```rust
fn estimate_size(pat: &Pattern) -> usize {
    match pat {
        Pattern::Term(t) => estimate_size_term(t),
        Pattern::Collection { elements, rest, .. } =>
            2 + elements.iter().map(estimate_size).sum::<usize>()
              + if rest.is_some() { 2 } else { 1 },
        // ...
    }
}
```

This avoids repeated reallocation during encoding. The estimate is an upper bound; the actual encoding may be shorter (e.g., when variable references are 1 byte instead of the 2-byte estimate for their first occurrence).

---

## References

1. **de Bruijn, N. G.** (1972). "Lambda calculus notation with nameless dummies, a tool for automatic formula manipulation." *Indagationes Mathematicae* 75(5), 381-392.

---

## Key Source Files

| File | Lines | Role |
|------|-------|------|
| `macros/src/logic/pattern_codec.rs` | 1-400 | Encoding: `EncodingEnv`, `pattern_to_debruijn_bytes()`, tag constants |
| `macros/src/logic/pattern_trie.rs` | 313-337 | Consumer: `find_alpha_equivalent_groups()` |

---

**Next:** [Synergy](../synergy.md) — how PathMap and Ascent complement each other.
