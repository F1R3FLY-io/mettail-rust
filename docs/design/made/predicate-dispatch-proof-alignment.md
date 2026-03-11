# Predicate Dispatch: Rocq Proof ↔ Rust Implementation Alignment Audit

## Summary

The Predicate Dispatch Automaton (Sprints 1–6) produced a Rocq formal verification
proof at `formal/rocq/predicate_dispatch/theories/DispatchCompleteness.v` covering
10 definitions, 15 lemmas, 11 theorems, and 1 corollary — all with zero `Admitted`.
The Rust implementation is in `prattail/src/predicate_dispatch.rs` (~2100 lines, 110 tests).

This audit identified 7 alignment gaps, applied 7 fixes (4 Rocq, 1 Rust, 2 documentation-only),
and documented all trust boundaries explicitly.

**Date**: 2026-03-10
**Scope**: 1 Rocq proof × 1 Rust module

---

## Findings Table

| # | Component | Issue | Severity | Fix Target | Status |
|---|-----------|-------|----------|------------|--------|
| 1 | `BASE_SIG` | Uses `+` (arithmetic) instead of `Nat.lor` (bitwise) | Medium | Rocq | FIXED |
| 2 | Module bit distinctness | Only 12 of C(11,2)=55 pairs proven | Low | Rocq | FIXED |
| 3 | `dispatch_accepts` | Simplified `negb(sig=0)` doesn't model SFA transitions | Medium | Rocq (document) | DOCUMENTED |
| 4 | `witness` generation | Rocq: direct construction; Rust: brute-force search | Low | Rust (optimize) | FIXED |
| 5 | `extract_features` | Not modeled in Rocq — major abstraction gap | High | Rocq + doc | DOCUMENTED |
| 6 | SFA state count | 13 states documented but not proven | Low | Rocq (document) | DOCUMENTED |
| 7 | `PredicateSignature` domain | Rocq uses `nat` (unbounded); Rust uses `u16` (bounded) | Low | Rocq (document) | DOCUMENTED |

---

## Detailed Findings

### Fix 1: `BASE_SIG` — `Nat.lor` instead of `+`

**Line**: `DispatchCompleteness.v` §1 (was line 53)

**Before**: `Definition BASE_SIG := M1_SYMBOLIC + M10_MSO.`
**After**: `Definition BASE_SIG := Nat.lor M1_SYMBOLIC M10_MSO.`

**Rationale**: Aligns with Rust's `Self::M1_SYMBOLIC | Self::M10_MSO`. Using `+` is only
correct for disjoint bits — `Nat.lor` is robust against future bit-position changes.

**Added lemmas**:
- `base_sig_value`: confirms `BASE_SIG = 513`
- `base_sig_add_equiv`: documents `+` = `lor` for these specific disjoint bits

**Impact**: All downstream proofs (`base_contains_m1`, `base_contains_m10`,
`extract_features_always_accepted`, `extract_features_nonzero`) use `vm_compute`
and produce identical results since the value is still 513.

---

### Fix 2: Complete Module Bit Distinctness

**Section**: §12

**Before**: `all_module_bits_distinct` listed only 12 inequality pairs.

**After**: All C(11,2) = 55 pairwise inequality conjuncts, plus a new
`module_bits_are_powers_of_2` lemma proving each module constant equals `2^k`
for distinct `k ∈ {0,...,10}`.

**Proof**: `unfold` all constants + `repeat split; lia`.

---

### Fix 3: `dispatch_accepts` Abstraction Gap (Documented)

**Section**: §4.1 (new)

The Rocq model uses `dispatch_accepts(sig) := sig ≠ 0`. The Rust uses a full 13-state
SFA (`build_dispatch_sfa()`) with per-module transitions. A structured comment documents:

- Equivalence argument: `sig ≠ 0 ⟺ ∃i, HasBit(i) fires ⟺ q_Mi ∈ F`
- The SFA provides per-module diagnostic reporting not modeled in Rocq

---

### Fix 4: Rust `witness()` Optimization

**File**: `predicate_dispatch.rs`, `DispatchAlgebra::witness()`

**Before**: Brute-force search over all 2^11 signatures for every predicate.

**After**: Fast paths for `True`, `False`, and `HasBit(bit)`:
- `True` → `Some(PredicateSignature::new())`
- `False` → `None`
- `HasBit(bit)` → `Some(from_raw(bit))` if `bit ≠ 0`, else `None`
- Compound predicates fall through to brute-force

**Alignment**: Matches Rocq's `witness_for_has_bit` theorem which proves
`Nat.land bit bit ≠ 0` (via `Nat.land_diag`) — the bit itself is the witness.
Traceability row added to Rocq header: `witness_for_has_bit → DispatchAlgebra::witness() fast path`.

---

### Fix 5: `extract_features` Trust Boundary (Documented)

**Section**: §7.1 (new)

Added both a structured comment and a formal definition:

- `extract_features_sig(extra) := sig_union BASE_SIG extra`
- `extract_features_sig_contains_base`: proves output always contains M1 and M10

**Trust boundary** (what is NOT proven):
- Soundness of morpheme detection
- Completeness of morpheme detection
- Cross-channel detection heuristic
- Multi-guard heuristic (≥2 channels → M7 + M8)

These are validated by 110 Rust tests including proptest-based property tests.

---

### Fix 6: SFA State Count (Documented)

**Section**: §4.1

Structured comment documenting:
- 1 initial state (q₀), 11 module states (q_M1..q_M11), 1 reject state (q_⊥) = 13 total
- Not proven minimal — per-module states needed for diagnostic reporting

---

### Fix 7: `nat` vs `u16` Domain (Documented)

**Section**: §1

Structured comment documenting:
- Rocq uses `nat` (unbounded); Rust uses `u16` (16-bit)
- All module bits fit in 11 bits, so `u16` is sufficient
- Rocq proofs are valid for any `nat` ⊇ `u16` — remain valid without change if Rust widens

---

## Spec-to-Code Traceability (Updated)

| Rocq Definition | Rust Code | Location |
|----------------|-----------|----------|
| `PredicateSignature` | `PredicateSignature(u16)` | predicate_dispatch.rs |
| `sig_contains` | `PredicateSignature::contains()` | predicate_dispatch.rs |
| `sig_union` | `PredicateSignature::union()` | predicate_dispatch.rs |
| `sig_set` | `PredicateSignature::set()` | predicate_dispatch.rs |
| `BASE_SIG` | `PredicateSignature::BASE` | predicate_dispatch.rs |
| `dispatch_accepts` | `build_dispatch_sfa() + accepts()` | predicate_dispatch.rs |
| `extract_features_sig` | `extract_features() .signature field` | predicate_dispatch.rs |
| `SignaturePred` | `SignaturePred` enum | predicate_dispatch.rs |
| `eval_pred` | `DispatchAlgebra::evaluate()` | predicate_dispatch.rs |
| `witness_for_has_bit` | `DispatchAlgebra::witness()` fast path | predicate_dispatch.rs |

---

## Abstraction Gap Summary

| Gap | Rocq Model | Rust Implementation | Why Sound |
|-----|-----------|---------------------|-----------|
| Acceptance | `sig ≠ 0` | 13-state SFA | Equivalent for 11-bit domain |
| `extract_features` | `sig_union BASE_SIG extra` | Post-order AST walk | Invariant: only `set()` (bit-or), never clear |
| `nat` vs `u16` | Unbounded | 16-bit | Rocq proofs cover superset of Rust domain |
| Witness | Direct construction | Fast path + brute-force fallback | Fast path matches theorem exactly |

---

## Verification

```bash
# 1. Compile Rocq proof (zero errors, zero Admitted)
cd formal/rocq/predicate_dispatch
systemd-run --user --scope -p MemoryMax=126G -p CPUQuota=1800% \
  -p IOWeight=30 -p TasksMax=200 make -j1

# 2. Run predicate dispatch Rust tests
cargo test -p prattail --features prattail/predicate-dispatch -- predicate_dispatch

# 3. Full regression
cargo test --workspace --all-features
```
