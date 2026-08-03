//! Decimal fixed-point values for use in category enums and Ascent relations.
//!
//! A value is `(unscaled, places)` representing `unscaled / 10^places`.
//! Uses [`CanonicalBigInt`] for the unscaled payload so the pair is `Copy`.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Add, BitAnd, BitOr, BitXor, Div, Mul, Neg, Rem, Sub};

use moniker::{BoundTerm, Var};
use num_bigint::BigInt;
use num_rational::Ratio;
use num_traits::Zero;

use crate::CanonicalBigInt;

/// Decimal fixed-point: exact value `unscaled / 10^places`.
#[derive(Clone, Copy)]
pub struct CanonicalFixedPoint {
    unscaled: CanonicalBigInt,
    places: u32,
}

fn pow10(p: u32) -> BigInt {
    BigInt::from(10u32).pow(p)
}

impl CanonicalFixedPoint {
    /// Constructs from unscaled integer and decimal place count, then normalizes.
    pub fn new(unscaled: BigInt, places: u32) -> Self {
        Self::from_raw(CanonicalBigInt::from(unscaled), places)
    }

    fn from_raw(unscaled: CanonicalBigInt, places: u32) -> Self {
        let mut s = Self { unscaled, places };
        s.normalize_in_place();
        s
    }

    /// Only collapse true zero to `0p0`. Do not strip trailing decimal zeros: `100p1` (ten with
    /// scale 1) must stay distinct from `10p0` for literal-backed scale, while `+`/`-`/`*`/`/`
    /// still align operands by `max(places)`.
    fn normalize_in_place(&mut self) {
        if self.unscaled.get().is_zero() {
            self.places = 0;
        }
    }

    pub(crate) fn value_ratio(&self) -> Ratio<BigInt> {
        Ratio::new(self.unscaled.get().clone(), pow10(self.places))
    }

    #[inline]
    pub fn unscaled(&self) -> &BigInt {
        self.unscaled.get()
    }

    #[inline]
    pub fn places(&self) -> u32 {
        self.places
    }

    /// Deterministic canonical byte serialization that agrees with [`Eq`]: two
    /// `CanonicalFixedPoint`s are equal iff their canonical bytes are equal. It keys on the raw
    /// `(unscaled, places)` pair — **exactly** what `PartialEq`/`Hash` key on since work item
    /// #200 — as `framed(unscaled.to_signed_bytes_le()) ++ places.to_le_bytes()`.
    ///
    /// # Why this is injective, and therefore satisfies the contract
    ///
    /// `dovetail/src/key.rs:96-104` requires `write_content` to be *injective up to
    /// observational equivalence* — a biconditional over an exact `Vec<u8>`, not a hash:
    /// `a == b  ⟺  a.to_canonical_bytes() == b.to_canonical_bytes()`.
    /// `BigInt::to_signed_bytes_le` is the MINIMAL two's-complement encoding and hence a
    /// bijection on `BigInt` (the same property [`CanonicalBigInt::to_canonical_bytes`] already
    /// relies on). The 8-byte little-endian length frame stops the mantissa from aliasing into
    /// the `places` field, and `places` is fixed-width (4 B). Decoding is therefore
    /// unambiguous — read 8, read that many, read 4 — so the composite is injective on
    /// `(unscaled, places)`, which is precisely the new `Eq`.
    ///
    /// # ⚠ WHAT THIS USED TO KEY ON, AND WHY IT CHANGED
    ///
    /// Until work item #200 (2026-07-30) the body keyed on
    /// [`value_ratio`](Self::value_ratio) and this doc comment read, verbatim:
    ///
    /// > **Critically, this keys on [`value_ratio`](Self::value_ratio) — the reduced rational
    /// > `unscaled / 10^places` — exactly as `PartialEq`/`Hash` do, NOT on the raw
    /// > `(unscaled, places)` pair.** Using the raw pair (or `Debug`, which renders the raw
    /// > pair) would give two `Eq`-equal values (e.g. `15p1` and `150p2`, both `3/2`) distinct
    /// > bytes and break the `SemanticHash`↔`Eq` agreement that the Dovetail e-graph relies on
    /// > to dedup.
    ///
    /// Two things were wrong with that, and they are independent:
    ///
    /// 1. **The mechanism was mis-named.** The Dovetail e-graph does **not** dedup on the
    ///    content key. `dovetail/src/egraph.rs` says of `content_key` explicitly that it "does
    ///    NOT participate in hashcons identity"; the hashcons is `memo: HashMap<ENode<L>,
    ///    EClassId>` (`egraph.rs:188`) and `ENode<L>` *derives* `PartialEq`/`Hash`
    ///    (`egraph.rs:32-36`), so the dedup key is `L`'s own — i.e. this type's `Eq`/`Hash`,
    ///    never these bytes. The content key serves AC keys, extraction and reporting. The old
    ///    conclusion ("must agree with `Eq`") was right; its stated reason was not.
    ///    ⚠ Commit `7baf0136`'s message claims it corrected this text. It did not — the
    ///    correction landed only in `languages/tests/fixedpoint_scale_dedup_ab.rs`'s module
    ///    doc. This is that correction, in the product file.
    /// 2. **`places` IS part of identity.** Keying `Eq` on the reduced rational made the
    ///    hashcons collapse `7.00p2` with `7.0p1`, so a scale-reading operator computed from
    ///    whichever spelling the source text happened to mention first — witnessed in the
    ///    consensus lane by `languages/tests/fixedpoint_scale_dedup_rholang.rs`. Work item
    ///    #200 ruled `Eq`/`Hash`/`Ord` onto `(unscaled, places)`, and the agreement obligation
    ///    then carries this method along with them.
    ///
    /// The value-keyed form did not disappear — it is
    /// [`to_rational_canonical_bytes`](Self::to_rational_canonical_bytes), which still has one
    /// live consumer with the opposite requirement.
    pub fn to_canonical_bytes(&self) -> Vec<u8> {
        let u = self.unscaled.get().to_signed_bytes_le();
        let mut out = Vec::with_capacity(u.len() + 12);
        out.extend_from_slice(&(u.len() as u64).to_le_bytes());
        out.extend_from_slice(&u);
        out.extend_from_slice(&self.places.to_le_bytes());
        out
    }

    /// Canonical bytes keyed on the **VALUE** — the length-framed reduced `(numer, denom)` of
    /// `unscaled / 10^places`. Byte-identical to [`CanonicalBigRat::to_canonical_bytes`] for an
    /// equal value, and that is the whole point.
    ///
    /// # Why this exists separately from [`to_canonical_bytes`](Self::to_canonical_bytes)
    ///
    /// The two methods have **contradictory** requirements because they have different
    /// consumers, and no single method can serve both:
    ///
    /// | consumer | coordinate | needs |
    /// |---|---|---|
    /// | op-enum `SemanticHash` content key | `macros/src/gen/runtime/dovetail_report/op_enum.rs:141-146` | agreement with `Eq` ⇒ the **raw pair** |
    /// | realize-frontier fingerprint | `macros/src/gen/term_ops/semantic_hash.rs:795-807` | **value** unification with `CanonicalBigRat` |
    ///
    /// The second is load-bearing, not incidental. A numeric literal read from ONE source token
    /// can reach a category through several transparent lossless promotion casts
    /// (`Fixed → BigRat` among them), and if the two readings fingerprint differently the
    /// realize frontier fans out: `k` literals with `m` transparent reps each give `m^k`
    /// alternatives — the measured `3^4 = 81` for `Map().set(1,10).set(2,20)`, with a
    /// memcg-OOM at 20k-ternary attributed to the class (see `semantic_hash.rs`'s own
    /// derivation). Unifying `Fixed(1.5p1)` with `BigRat(3/2)` collapses that fan, and it is
    /// SOUND there because the realize-dedup only ever compares alternatives spanning the SAME
    /// source tokens — so it never merges two distinct values.
    ///
    /// ★ Note the two collisions are genuinely different animals: this one is *wanted* (same
    /// token, two category readings); the one work item #200 removed was *unwanted* (two
    /// different tokens, equal value).
    pub fn to_rational_canonical_bytes(&self) -> Vec<u8> {
        let r = self.value_ratio();
        let n = r.numer().to_signed_bytes_le();
        let d = r.denom().to_signed_bytes_le();
        let mut out = Vec::with_capacity(n.len() + d.len() + 16);
        out.extend_from_slice(&(n.len() as u64).to_le_bytes());
        out.extend_from_slice(&n);
        out.extend_from_slice(&(d.len() as u64).to_le_bytes());
        out.extend_from_slice(&d);
        out
    }
}

impl Default for CanonicalFixedPoint {
    /// Zero fixed-point (`0p0`).
    fn default() -> Self {
        Self::from_raw(CanonicalBigInt::default(), 0)
    }
}

impl CanonicalFixedPoint {
    /// Align both operands to `P = max(places_a, places_b)`; returns scaled unscaled values.
    fn align_pair(a: Self, b: Self) -> (BigInt, BigInt, u32) {
        let p = a.places.max(b.places);
        let scale_a = pow10(p - a.places);
        let scale_b = pow10(p - b.places);
        let ua = a.unscaled.get() * scale_a;
        let ub = b.unscaled.get() * scale_b;
        (ua, ub, p)
    }

    /// Shifted integer division: `(ua * 10^P) / ub` at common scale `P`.
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        let (ua, ub, p) = Self::align_pair(self, rhs);
        if ub.is_zero() {
            return None;
        }
        let numer = ua * pow10(p);
        let q = numer / ub;
        Some(Self::from_raw(CanonicalBigInt::from(q), p))
    }

    /// Remainder on the aligned unscaled integers, at the shared scale `P`: `ua % ub`, truncated
    /// toward zero so the sign follows the DIVIDEND (as `BigInt`'s and Rust's `i64`'s `%` do).
    ///
    /// # Upstream is the definition
    ///
    /// This matches upstream Rholang's `combine_mod` `GFixedPoint` arm exactly —
    /// `f1r3node-rust-mettail/rholang/src/rust/interpreter/reduce.rs:3460-3470`:
    ///
    /// ```text
    /// let ua = bytes_to_bigint(&fp1.unscaled);
    /// let ub = bytes_to_bigint(&fp2.unscaled);
    /// let remainder = &ua % &ub;
    /// make_fixedpoint_expr(GFixedPoint { unscaled: …, scale: fp1.scale }, "%")
    /// ```
    ///
    /// ⇒ remainder on the unscaled integers, scale preserved. ★ Note the exact remainder ALWAYS
    /// fits this type: `/` must approximate (`10.0/3.0` is not representable at any finite scale),
    /// but `%` never must, because `ua % ub` is an integer no wider than `ua`.
    ///
    /// # ⚠ WHAT THIS USED TO COMPUTE, AND WHY IT WAS WRONG
    ///
    /// Until 2026-07-30 the body was:
    ///
    /// ```text
    /// let q = (ua.clone() * pow10(p)) / &ub;     // ← scaled quotient
    /// let rem = ua - (q * &ub) / pow10(p);       // ← then divided back down
    /// ```
    ///
    /// That is `a − trunc_p(a/b)·b`, which expands to `(a/b − trunc_p(a/b))·b = ε·b` with
    /// `0 ≤ ε < 10⁻ᵖ` — **the truncation error of the division, scaled by the divisor.** A
    /// residual, not a remainder. Its magnitude is bounded by `|b|·10⁻ᵖ`, so it tends to ZERO as
    /// precision grows, which no remainder does. Measured consequences:
    ///
    /// | input | superseded | correct (= upstream) |
    /// |---|---|---|
    /// | `7.00p2 % 3.00p2` | `0.01p2` | `1.00p2` |
    /// | `10.0p1 % 3.0p1`  | `0.1p1`  | `1.0p1`  |
    /// | `7.50p2 % 2.00p2` | `0p0`    | `1.50p2` |
    ///
    /// The `7.50 % 2.00` row shows the mechanism plainly: `7.50/2.00 = 3.75` is EXACT at two
    /// places, so `ε = 0` and the old code returned zero for a division that leaves remainder
    /// `1.50`.
    ///
    /// ## Why "copy+paste" is the diagnosis
    ///
    /// Compare [`checked_div`](Self::checked_div) directly above: there `let numer = ua * pow10(p)`
    /// is **essential**, because a quotient must be computed at scale to have fractional digits at
    /// all. `checked_rem` copied that line and then bolted on a compensating `/ pow10(p)` to make
    /// the units balance. The round trip exists ONLY to undo a factor that should never have been
    /// introduced — deleting both is the whole fix.
    ///
    /// The copy is recorded upstream of the code, in the design note
    /// `docs/design/exploring/ieee754-fixed-point.md` §4.4(5), which derived `%` by substituting
    /// item (4)'s SHIFTED quotient into the C99 identity `(a/b)·b + a%b == a`. That identity is
    /// C99 §6.5.5's, and it is stated for INTEGER division; item (4)'s `q` is a `p`-places
    /// fixed-point number, not an integer, so the substitution is invalid. The note has been
    /// corrected alongside this function, because it would otherwise regenerate the defect.
    ///
    /// ## ★★ The decisive defect — RE-DERIVED 2026-07-30, because its original argument no
    /// longer holds
    ///
    /// **The superseded argument, verbatim:**
    ///
    /// > [`PartialEq`], [`Hash`] and [`to_canonical_bytes`](Self::to_canonical_bytes) all key on
    /// > [`value_ratio`](Self::value_ratio) — the reduced rational — because keying on the raw
    /// > `(unscaled, places)` pair would break the `SemanticHash`↔`Eq` agreement the Dovetail
    /// > e-graph relies on to dedup. So `places` is NOT part of a value's identity, and
    /// > `7.00p2 == 7.0p1`. But the superseded `%` READ `places`: it answered `0.01` for the
    /// > first spelling and `0.1` for the second. **Equal inputs, unequal outputs.** Whatever
    /// > else it was, it was not a function on the equivalence classes this type declares.
    ///
    /// ⚠ **That argument is DEAD as of work item #200.** `places` IS part of identity now, so
    /// `7.00p2 ≠ 7.0p1`, and the two spellings are no longer "equal inputs". Read literally,
    /// the superseded `%` WOULD be a function on the new equivalence classes — the raw pair
    /// determines its answer. So this paragraph, unamended, is an argument for putting the
    /// residual-valued `%` BACK. It is not. Do not.
    ///
    /// **What condemns the superseded `%` now is simpler and stronger: it did not compute a
    /// remainder, and upstream defines what a remainder is.** Upstream's `combine_mod`
    /// `GFixedPoint` arm (`reduce.rs:3460-3470`, quoted above) is `&ua % &ub` on the unscaled
    /// integers with `scale: fp1.scale`, and upstream requires `fp1.scale == fp2.scale`, so at
    /// equal scales this function and upstream's are the SAME function — a floor obligation,
    /// not a taste. The superseded body computed `ε·b`, the division's own truncation residual,
    /// which is not upstream's answer at ANY scale: `7.50p2 % 2.00p2` returned `0p0` where
    /// upstream returns `1.50p2`, because `7.50/2.00 = 3.75` is exact at two places and so
    /// `ε = 0`. A quantity that tends to zero as precision grows is not a remainder.
    ///
    /// Pinned by `tests::remainder_is_invariant_under_the_places_spelling`, itself re-derived
    /// alongside this text.
    ///
    /// # The identity that no longer holds — and why that is correct, not a loss
    ///
    /// `checked_div(a,b)·b + checked_rem(a,b) == a` is now FALSE (`3.3·3.0 + 1.0 = 10.9 ≠ 10.0`),
    /// and it was true before. That is not a regression: the division identity
    /// `q·b + r == a` is a theorem about the **integer** (truncated) quotient, and
    /// [`checked_div`](Self::checked_div) does not return that — it returns the quotient carried to
    /// `p` fractional places, which is a different (and deliberately approximating) operation. The
    /// old pairing satisfied the identity only because the old `%` was defined as "whatever makes
    /// `checked_div` exact", i.e. as the division's own error term. The identity that holds now is
    /// `trunc(a/b)·b + (a % b) == a`, asserted in `tests::div_mod_example` and
    /// `tests::div_mod_with_negatives`. ★ Upstream claims no such identity between its `/` and `%`
    /// either, which is why it has no such test.
    ///
    /// `/` is deliberately NOT changed here; only `%` moved.
    pub fn checked_rem(self, rhs: Self) -> Option<Self> {
        let (ua, ub, p) = Self::align_pair(self, rhs);
        if ub.is_zero() {
            return None;
        }
        let rem = ua % ub;
        Some(Self::from_raw(CanonicalBigInt::from(rem), p))
    }

    fn bitwise_aligned<F>(a: Self, b: Self, op: F) -> Self
    where
        F: FnOnce(BigInt, BigInt) -> BigInt,
    {
        let p = a.places.max(b.places);
        let scale_a = pow10(p - a.places);
        let scale_b = pow10(p - b.places);
        let ia = a.unscaled.get() * scale_a;
        let ib = b.unscaled.get() * scale_b;
        let r = op(ia, ib);
        Self::from_raw(CanonicalBigInt::from(r), p)
    }
}

/// ★ IDENTITY IS THE RAW `(unscaled, places)` PAIR — work item #200, 2026-07-30.
///
/// Ruled by the owner, verbatim: *"Key Eq/Hash/Ord on (unscaled, places)"*.
///
/// # What this replaced, verbatim
///
/// ```text
/// impl PartialEq for CanonicalFixedPoint {
///     fn eq(&self, other: &Self) -> bool { self.value_ratio() == other.value_ratio() }
/// }
/// impl Ord for CanonicalFixedPoint {
///     fn cmp(&self, other: &Self) -> std::cmp::Ordering {
///         self.value_ratio().cmp(&other.value_ratio())
///     }
/// }
/// impl Hash for CanonicalFixedPoint {
///     fn hash<H: Hasher>(&self, state: &mut H) {
///         let r = self.value_ratio();
///         r.numer().hash(state);
///         r.denom().hash(state);
///     }
/// }
/// ```
///
/// # Why it had to move
///
/// `ENode<L>` derives `PartialEq`/`Hash` (`dovetail/src/egraph.rs:32-36`), so the e-graph
/// hashcons `memo: HashMap<ENode<L>, EClassId>` (`:188`) keys a `Fixed` literal leaf on THIS
/// impl. `EGraph::add` (`:292-295`) returns the existing class on a memo hit and never inserts
/// the incoming node, so a class kept only the FIRST-INSERTED `places`. The generated fold then
/// reads its operand out of the e-CLASS, not the source term — so `/`, `&`, `|` and `bitnot`
/// computed from whichever spelling of an equal value the program happened to mention first.
/// Witnessed in the consensus lane: `languages/tests/fixedpoint_scale_dedup_rholang.rs`
/// measures `((7.0p1 - 7.0p1) - (3.0p1 - 3.0p1)) + (7.00p2 / 3.00p2)` as `2.3p1` and the same
/// two summands SWAPPED as `2.33p2`. `23/10 ≠ 233/100`.
///
/// ★ It also brings `==` INTO agreement with upstream, which it previously breached: upstream's
/// `combine_eq` (`f1r3node-rust-mettail/rholang/src/rust/interpreter/reduce.rs:3733-3749`) is
/// structural `Par` equality over `GFixedPoint { unscaled, scale }` and answers **`false`** for
/// `7.00p2 == 7.0p1`, where mettail answered **`true`**; and `Set(7.00p2, 7.0p1)` is a
/// TWO-element set upstream (`models/src/rust/sorted_par_hash_set.rs:14-24` is a
/// `HashSet<Par>`) where mettail made it one.
///
/// ⚠ **Residual, NOT closed by this change:** [`normalize_in_place`](Self::normalize_in_place)
/// still collapses true zero to `0p0` where upstream's `make_fixedpoint_expr`
/// (`reduce.rs:9668-9675`) does not, so `0.00p2 == 0.0p1` remains `true` here and `false`
/// upstream. Recorded, not repaired — it is a third change and needs its own ruling.
impl PartialEq for CanonicalFixedPoint {
    fn eq(&self, other: &Self) -> bool {
        // `places` first: a `u32` compare is far cheaper than a `BigInt` compare and
        // discriminates most unequal pairs outright.
        self.places == other.places && self.unscaled.get() == other.unscaled.get()
    }
}

impl Eq for CanonicalFixedPoint {}

impl PartialOrd for CanonicalFixedPoint {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Lexicographic on `(value_ratio(), places)` — **not** on `(unscaled, places)`.
///
/// # The consistency obligation, discharged
///
/// Rust requires `a.cmp(&b) == Equal  ⟺  a == b`. With `Eq` on the raw pair:
///
/// | case | `cmp` says | `eq` says | consistent? |
/// |---|---|---|---|
/// | `value_ratio` differs | not `Equal` (ratios decide) | `false` — equal pairs would force equal ratios, so unequal ratios force unequal pairs | ✓ |
/// | `value_ratio` equal, `places` equal | `Equal` | `true` — `u_a/10^p == u_b/10^p ⇒ u_a == u_b` | ✓ |
/// | `value_ratio` equal, `places` differ | not `Equal` (tie-break decides) | `false` | ✓ |
///
/// All three cases agree, so the obligation holds.
///
/// # ⚠ Why NOT plain lexicographic `(unscaled, places)`
///
/// It would not be an ORDER ON NUMBERS. `1.0p1` is `(10, 1)` and `0.99p2` is `(99, 2)`, so
/// comparing mantissas first gives `10 < 99` ⇒ `1.0p1 < 0.99p2`, which is false as arithmetic.
/// Pinned by `tests::ord_is_numeric_first_then_places`.
///
/// # ⚠ KNOWN RESIDUAL — the `places` tie-break leaks a non-numeric answer
///
/// `7.00p2 > 7.0p1` is **`true`** under this `Ord` (equal value, `places` 2 > 1), and as
/// arithmetic that is nonsense. The tie-break exists ONLY to satisfy Rust's totality
/// requirement and to give `BTreeMap`/`sort` a total order; it is not meant to be observable
/// from a program.
///
/// **Its named resolution is upstream's scale-equality refusal** — the SIXTH refusal site,
/// `compare_fixed_points` (`reduce.rs:9772-9783`, reached from `combine_relop` `:3188`), which
/// refuses a mixed-scale comparison outright with `op: "cmp"`. Once that precondition is
/// adopted (work item #186), the four language-level ordering relops refuse before this
/// tie-break is ever reachable, and the invariant to pin is: *no language-level ordering
/// comparison may observe the `places` tie-break.* That work is a separate, owner-blocked
/// change (it turns on a `Mul` scale-rule decision that neither ruling authorises) and is
/// deliberately NOT made here. Until it lands, the leak is REAL and is recorded rather than
/// hidden.
impl Ord for CanonicalFixedPoint {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.value_ratio()
            .cmp(&other.value_ratio())
            .then_with(|| self.places.cmp(&other.places))
    }
}

/// Agrees with [`PartialEq`] by construction: the same two fields, in the same order.
impl Hash for CanonicalFixedPoint {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.unscaled.get().hash(state);
        self.places.hash(state);
    }
}

impl fmt::Debug for CanonicalFixedPoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Fixed({}/{})", self.unscaled.get(), pow10(self.places))
    }
}

impl fmt::Display for CanonicalFixedPoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let u = self.unscaled.get();
        let p = self.places as usize;
        if p == 0 {
            return write!(f, "{}p0", u);
        }
        let us = u.to_string();
        let neg = us.starts_with('-');
        let digits = if neg { &us[1..] } else { &us[..] };
        if digits.len() <= p {
            let pad = p - digits.len();
            let frac: String = std::iter::repeat_n('0', pad)
                .chain(digits.chars())
                .collect();
            if neg {
                write!(f, "-0.{frac}p{}", self.places)
            } else {
                write!(f, "0.{frac}p{}", self.places)
            }
        } else {
            let split = digits.len() - p;
            let (int_part, frac_part) = digits.split_at(split);
            if neg {
                write!(f, "-{int_part}.{frac_part}p{}", self.places)
            } else {
                write!(f, "{int_part}.{frac_part}p{}", self.places)
            }
        }
    }
}

impl BoundTerm<String> for CanonicalFixedPoint {
    fn term_eq(&self, other: &Self) -> bool {
        self.eq(other)
    }

    fn close_term(
        &mut self,
        _state: moniker::ScopeState,
        _on_free: &impl moniker::OnFreeFn<String>,
    ) {
    }

    fn open_term(
        &mut self,
        _state: moniker::ScopeState,
        _on_bound: &impl moniker::OnBoundFn<String>,
    ) {
    }

    fn visit_vars(&self, _on_var: &mut impl FnMut(&Var<String>)) {}

    fn visit_mut_vars(&mut self, _on_var: &mut impl FnMut(&mut Var<String>)) {}
}

impl Add for CanonicalFixedPoint {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let (ua, ub, p) = Self::align_pair(self, rhs);
        Self::from_raw(CanonicalBigInt::from(ua + ub), p)
    }
}

impl Sub for CanonicalFixedPoint {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        let (ua, ub, p) = Self::align_pair(self, rhs);
        Self::from_raw(CanonicalBigInt::from(ua - ub), p)
    }
}

impl Mul for CanonicalFixedPoint {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        let numer = self.unscaled.get() * rhs.unscaled.get();
        let places = self.places + rhs.places;
        Self::from_raw(CanonicalBigInt::from(numer), places)
    }
}

impl Div for CanonicalFixedPoint {
    type Output = Self;
    fn div(self, rhs: Self) -> Self {
        self.checked_div(rhs)
            .expect("fixed-point division by zero or overflow path")
    }
}

impl Rem for CanonicalFixedPoint {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self {
        self.checked_rem(rhs)
            .expect("fixed-point remainder: division by zero")
    }
}

impl Neg for CanonicalFixedPoint {
    type Output = Self;
    fn neg(self) -> Self {
        Self::from_raw(CanonicalBigInt::from(-self.unscaled.get().clone()), self.places)
    }
}

impl BitAnd for CanonicalFixedPoint {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self {
        Self::bitwise_aligned(self, rhs, |a, b| a & b)
    }
}

impl BitOr for CanonicalFixedPoint {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        Self::bitwise_aligned(self, rhs, |a, b| a | b)
    }
}

impl BitXor for CanonicalFixedPoint {
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self {
        Self::bitwise_aligned(self, rhs, |a, b| a ^ b)
    }
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::Hasher;

    use super::*;

    fn fp(s_int: i64, s_frac: i64, places: u32) -> CanonicalFixedPoint {
        // helper: value (s_int * 10^p + s_frac) / 10^p for small tests (s_frac < 10^p)
        let ten_p = 10i64.pow(places);
        let u = BigInt::from(s_int) * BigInt::from(ten_p) + BigInt::from(s_frac);
        CanonicalFixedPoint::new(u, places)
    }

    fn hash_val(x: &CanonicalFixedPoint) -> u64 {
        let mut h = DefaultHasher::new();
        x.hash(&mut h);
        h.finish()
    }

    /// The TRUNCATED INTEGER quotient `trunc(a/b)`, as an integer-valued fixed point
    /// (`places = 0`).
    ///
    /// ★ This is the quotient `checked_rem`'s remainder pairs with, and it is NOT what
    /// [`CanonicalFixedPoint::checked_div`] returns. `checked_div` carries the quotient to `p`
    /// fractional places (`10.0p1 / 3.0p1 == 3.3p1`); the division identity
    /// `q·b + r == a` holds for the INTEGER quotient only. Written out here so the two tests
    /// below can name the distinction instead of implying it.
    fn integer_quotient(a: CanonicalFixedPoint, b: CanonicalFixedPoint) -> CanonicalFixedPoint {
        let (ua, ub, _p) = CanonicalFixedPoint::align_pair(a, b);
        CanonicalFixedPoint::new(ua / ub, 0)
    }

    /// ★ RE-DERIVED 2026-07-30 — NOT re-blessed. `%` is the remainder on the ALIGNED UNSCALED
    /// INTEGERS (upstream's definition, `reduce.rs:3460-3470`), so `10.0p1 % 3.0p1` aligns to
    /// `ua = 100`, `ub = 30` and answers `100 % 30 = 10` at `places = 1` — the value **1.0**.
    ///
    /// **The identity that HOLDS** is against the TRUNCATED INTEGER quotient:
    ///   `trunc(a/b)·b + (a % b) == a`, i.e. `3·3.0 + 1.0 == 10.0`. ✓
    ///
    /// **The identity that NO LONGER HOLDS** is against `checked_div`'s quotient:
    ///   `(a/b)·b + (a % b) == a`, i.e. `3.3·3.0 + 1.0 == 10.9 ≠ 10.0`. ✗
    ///
    /// The second is asserted as an INEQUALITY deliberately. It is exactly the identity the
    /// superseded `checked_rem` satisfied (it returned `0.1p1`, and `3.3·3.0 + 0.1 == 10.0`), so
    /// reverting the `checked_rem` fix turns THIS row red rather than letting the residual-valued
    /// `%` back in as a "restored invariant". `/` is unchanged and its pin below is untouched.
    #[test]
    fn div_mod_example() {
        let a = fp(10, 0, 1);
        let b = fp(3, 0, 1);
        let q = a.checked_div(b).expect("div");
        let r = a.checked_rem(b).expect("rem");

        // `/` is NOT changed: the quotient is still carried to `p` places.
        assert_eq!(q.unscaled(), &BigInt::from(33));
        assert_eq!(q.places(), 1);

        // `%` is the remainder on the aligned unscaled integers, at the shared scale.
        assert_eq!(
            r.unscaled(),
            &BigInt::from(10),
            "`10.0p1 % 3.0p1` aligns to `100 % 30 = 10`; unscaled `1` would be `0.1p1`, the \
             truncation residual of the division, not a remainder",
        );
        assert_eq!(r.places(), 1, "upstream preserves the operand scale");
        assert_eq!(r.to_string(), "1.0p1");

        // THE IDENTITY THAT HOLDS: against the truncated integer quotient.
        let q_int = integer_quotient(a, b);
        assert_eq!(q_int.unscaled(), &BigInt::from(3), "trunc(10/3) == 3");
        assert_eq!(
            q_int * b + r,
            a,
            "`trunc(a/b)·b + (a % b) == a` — the division identity the exact remainder satisfies",
        );

        // THE IDENTITY THAT DOES NOT: against the p-places quotient. `3.3·3.0 + 1.0 == 10.9`.
        assert_ne!(
            q * b + r,
            a,
            "`(a/b)·b + (a % b) == a` holds only for the p-PLACES quotient paired with the \
             p-places truncation RESIDUAL — the superseded behaviour. If this row passes, \
             `checked_rem` has been reverted to computing `ε·b`.",
        );
        assert_eq!(
            (q * b + r).to_string(),
            "10.90p2",
            "the pairing is off by exactly the residual the old `%` returned (0.1·3.0 = 0.30… \
             precisely: 9.90 + 1.0 = 10.90 versus a = 10.0)",
        );
    }

    /// ★ RE-DERIVED 2026-07-30 — NOT re-blessed. `BigInt`'s `%` truncates toward zero, so the
    /// sign of the remainder follows the DIVIDEND, matching Rust's `i64 %` and therefore matching
    /// upstream's `GInt` row (`lhs % rhs`) and its `GFixedPoint` row (`&ua % &ub`) alike.
    ///
    /// The identity asserted for every row is `trunc(a/b)·b + (a % b) == a` — the same one
    /// [`div_mod_example`] establishes, now over all four sign combinations. ⚠ The originally
    /// pinned operand pair (`-1.00p2 % 0.25p2`) is kept as the first row but measures NO sign
    /// behaviour: `25` divides `100` exactly, so its remainder is identically zero. That is why
    /// the four `±7 % ±3` rows were added — the old pin could not have caught a sign error.
    #[test]
    fn div_mod_with_negatives() {
        // Row 0: the originally pinned pair. Exact division ⇒ remainder is EXACTLY ZERO, which
        // normalizes to `0p0`. Retained for continuity, not for coverage.
        let a = CanonicalFixedPoint::new(BigInt::from(-100), 2);
        let b = CanonicalFixedPoint::new(BigInt::from(25), 2);
        let r = a.checked_rem(b).expect("r");
        assert!(
            r.unscaled().is_zero(),
            "-1.00p2 / 0.25p2 is exact (-4), so the remainder is 0 and this row cannot detect a \
             sign defect",
        );
        assert_eq!(r.places(), 0, "true zero normalizes to `0p0`");
        let q_int = integer_quotient(a, b);
        assert_eq!(q_int.unscaled(), &BigInt::from(-4));
        assert_eq!(q_int * b + r, a, "`trunc(a/b)·b + (a % b) == a`");

        // Rows 1-4: every sign combination, checked against `i64 %` — the carrier upstream's
        // `GInt` row uses, so agreement here is agreement with upstream on sign.
        for (ai, bi) in [(7i64, 3i64), (-7, 3), (7, -3), (-7, -3)] {
            let a = CanonicalFixedPoint::new(BigInt::from(ai) * 100, 2);
            let b = CanonicalFixedPoint::new(BigInt::from(bi) * 100, 2);
            let r = a.checked_rem(b).expect("rem");
            let want = CanonicalFixedPoint::new(BigInt::from(ai % bi) * 100, 2);
            assert_eq!(
                r,
                want,
                "`{ai}.00p2 % {bi}.00p2` must equal `{}` — the value of `{ai}i64 % {bi}i64`, \
                 truncated toward zero with the sign of the dividend",
                ai % bi,
            );
            let q_int = integer_quotient(a, b);
            assert_eq!(
                q_int * b + r,
                a,
                "`trunc(a/b)·b + (a % b) == a` must hold at signs ({ai}, {bi})",
            );
        }
    }

    /// ★ SCALE INVARIANCE OF THE REMAINDER'S **VALUE** — the law the superseded `checked_rem`
    /// broke, and which nothing checked.
    ///
    /// ⚠⚠ RE-DERIVED 2026-07-30 (work item #200). **This test's thesis inverted, and the whole
    /// argument had to be rebuilt.** The superseded doc read, verbatim:
    ///
    /// > `PartialEq`, `Hash` and `to_canonical_bytes` all key on `value_ratio()` (see the doc
    /// > comment on [`CanonicalFixedPoint::to_canonical_bytes`], which explains that keying on
    /// > the raw `(unscaled, places)` pair would break the `SemanticHash`↔`Eq` agreement the
    /// > Dovetail e-graph relies on). `places` is therefore NOT part of a value's identity:
    /// > `7.00p2 == 7.0p1 == 7p0`.
    /// >
    /// > An operation on this type must consequently be a function on those equivalence
    /// > classes — **equal inputs, equal outputs.** `%` was not.
    ///
    /// **Every premise of that paragraph is now false.** `places` IS part of identity, the
    /// three spellings are NOT equal, and the superseded `%` — which reads only the raw pair —
    /// *is* a function on the new equivalence classes. ★ Left unamended, this test would read
    /// as a licence to restore the residual-valued `%` as a bug fix. It is not.
    ///
    /// **What the repair rests on instead — and it is stronger, because it is a floor
    /// obligation rather than an internal-consistency argument.** Upstream's `combine_mod`
    /// `GFixedPoint` arm (`reduce.rs:3460-3470`) computes `&ua % &ub` on the unscaled integers,
    /// preserving `fp1.scale`, and it requires `fp1.scale == fp2.scale`. At equal scales this
    /// function is therefore upstream's function, exactly. The superseded body computed the
    /// division's truncation residual `ε·b`, which agrees with upstream at NO scale:
    ///
    /// | spelling | superseded `%` (a residual) | this `%` (= upstream) |
    /// |---|---|---|
    /// | `7.00p2 % 3.00p2` | `0.01p2` | `1.00p2` |
    /// | `7.0p1 % 3.0p1`   | `0.1p1`  | `1.0p1`  |
    /// | `7p0 % 3p0`       | `1p0`    | `1p0`    |
    /// | `7.50p2 % 2.00p2` | `0p0`    | `1.50p2` |
    ///
    /// The last row is the mechanism in one line: `7.50/2.00 = 3.75` is EXACT at two places, so
    /// `ε = 0` and the old code returned zero for a division leaving remainder `1.50`.
    ///
    /// **What this test still pins, and why it is still worth pinning.** The three spellings
    /// denote the same two numbers, so a correct `%` must answer the same NUMBER for all three
    /// — `value_ratio()`-equal, even though no longer `Eq`-equal. That is precisely the property
    /// the residual lacked (it answered three different numbers), so the test still catches a
    /// revert. It now says so on `value_ratio()` rather than on `Eq`.
    #[test]
    fn remainder_is_invariant_under_the_places_spelling() {
        let spellings = [
            ("7.00p2 % 3.00p2", 700, 300, 2u32),
            ("7.0p1 % 3.0p1", 70, 30, 1),
            ("7p0 % 3p0", 7, 3, 0),
        ];
        let one = CanonicalFixedPoint::new(BigInt::from(1), 0);

        // PREMISE, asserted rather than assumed: the operands denote the same two NUMBERS…
        let seven = CanonicalFixedPoint::new(BigInt::from(7), 0);
        let three = CanonicalFixedPoint::new(BigInt::from(3), 0);
        for (label, ua, ub, p) in spellings {
            let a = CanonicalFixedPoint::new(BigInt::from(ua), p);
            let b = CanonicalFixedPoint::new(BigInt::from(ub), p);
            assert_eq!(
                a.value_ratio(),
                seven.value_ratio(),
                "the dividend of `{label}` is the NUMBER 7",
            );
            assert_eq!(
                b.value_ratio(),
                three.value_ratio(),
                "the divisor of `{label}` is the NUMBER 3",
            );
            // …and are nonetheless DISTINCT VALUES for `p != 0`, which is the #200 ruling.
            if p != 0 {
                assert_ne!(
                    a, seven,
                    "`{label}`'s dividend is not `Eq` to `7p0` — identity is \
                                      the raw `(unscaled, places)` pair since work item #200"
                );
            }
        }

        let mut results = Vec::with_capacity(spellings.len());
        for (label, ua, ub, p) in spellings {
            let a = CanonicalFixedPoint::new(BigInt::from(ua), p);
            let b = CanonicalFixedPoint::new(BigInt::from(ub), p);
            let r = a.checked_rem(b).expect("rem");
            assert_eq!(
                r.value_ratio(),
                one.value_ratio(),
                "`{label}` must be the NUMBER 1. The superseded `%` answered `0.01`, `0.1` and \
                 `1` for these three spellings — three different numbers for one division, \
                 because it returned the division's truncation residual `ε·b` instead of \
                 upstream's `ua % ub`",
            );
            assert_eq!(r.places(), p, "`{label}` preserves the operand scale, as upstream does");
            results.push((label, r));
        }

        // The consequence, restated on the method that still carries the VALUE key. ★ Note the
        // deliberate split introduced by work item #200: `to_rational_canonical_bytes` unifies
        // these three (and unifies a `Fixed` with an equal `BigRat`, which the realize-frontier
        // dedup needs), while `to_canonical_bytes` separates them (which the op-enum content
        // key needs, to agree with `Eq`). Both directions are asserted so neither can drift.
        let (first_label, first) = results[0];
        for &(label, r) in &results[1..] {
            assert_eq!(
                r.to_rational_canonical_bytes(),
                first.to_rational_canonical_bytes(),
                "`{label}` and `{first_label}` are the same NUMBER, so the VALUE-keyed bytes \
                 must agree",
            );
            assert_ne!(
                r.to_canonical_bytes(),
                first.to_canonical_bytes(),
                "…while the IDENTITY-keyed bytes must differ, because `{label}` and \
                 `{first_label}` are distinct values since work item #200",
            );
            assert_ne!(hash_val(&r), hash_val(&first), "`Hash` follows `Eq`, so it separates too");
        }
    }

    #[test]
    fn checked_div_rem_by_zero() {
        let a = fp(1, 0, 0);
        let z = fp(0, 0, 0);
        assert!(a.checked_div(z).is_none());
        assert!(a.checked_rem(z).is_none());
    }

    #[test]
    fn normalize_zero() {
        let z = CanonicalFixedPoint::new(BigInt::from(0), 5);
        assert!(z.unscaled.get().is_zero());
        assert_eq!(z.places(), 0);
    }

    #[test]
    fn display_zero_and_integer_p0() {
        let z = CanonicalFixedPoint::new(BigInt::from(0), 0);
        assert_eq!(z.to_string(), "0p0");
        let n = CanonicalFixedPoint::new(BigInt::from(-42), 0);
        assert_eq!(n.to_string(), "-42p0");
    }

    #[test]
    fn display_padding_frac_only() {
        // unscaled 5, places 2 → 0.05p2
        let x = CanonicalFixedPoint::new(BigInt::from(5), 2);
        assert_eq!(x.to_string(), "0.05p2");
        let y = CanonicalFixedPoint::new(BigInt::from(-3), 3);
        assert_eq!(y.to_string(), "-0.003p3");
    }

    #[test]
    fn display_int_and_frac_parts() {
        let x = CanonicalFixedPoint::new(BigInt::from(12345), 3);
        assert_eq!(x.to_string(), "12.345p3");
    }

    /// ★ RE-DERIVED 2026-07-30 (work item #200) — this assertion INVERTED.
    ///
    /// It read `assert_eq!(a, b)` under the name `eq_same_rational_different_places`, pinning
    /// that the reduced rational alone decided identity. `places` is part of identity now, so
    /// `10.0p1` and `10p0` are DISTINCT despite denoting the same number — which is exactly
    /// what upstream's structural `GFixedPoint` equality already said (`reduce.rs:3733-3749`).
    #[test]
    fn eq_distinguishes_same_rational_at_different_places() {
        let a = CanonicalFixedPoint::new(BigInt::from(100), 1);
        let b = CanonicalFixedPoint::new(BigInt::from(10), 0);
        assert_ne!(a, b, "same value, different `places` ⇒ DISTINCT since work item #200");
        assert_eq!(
            a.value_ratio(),
            b.value_ratio(),
            "…while still denoting the same number — the distinction is of identity, not of value",
        );
        assert_ne!(a.to_string(), b.to_string());
    }

    #[test]
    fn ord_and_partial_ord() {
        let a = fp(1, 0, 0);
        let b = fp(2, 0, 0);
        assert_eq!(a.cmp(&b), Ordering::Less);
        assert_eq!(b.cmp(&a), Ordering::Greater);
        assert_eq!(a.partial_cmp(&b), Some(Ordering::Less));
    }

    /// ★ `Ord` compares the NUMBER first and only then breaks ties on `places`. The naive
    /// lexicographic `(unscaled, places)` shape — the obvious reading of the ruling's words —
    /// is REJECTED here by counterexample, so it cannot be reintroduced as a simplification.
    #[test]
    fn ord_is_numeric_first_then_places() {
        let one_p1 = CanonicalFixedPoint::new(BigInt::from(10), 1); // 1.0
        let point99_p2 = CanonicalFixedPoint::new(BigInt::from(99), 2); // 0.99

        assert_eq!(
            one_p1.cmp(&point99_p2),
            Ordering::Greater,
            "1.0 > 0.99. Lexicographic `(unscaled, places)` would compare mantissas 10 vs 99 \
             and answer Less — an order on spellings, not on numbers",
        );
        assert_eq!(point99_p2.cmp(&one_p1), Ordering::Less, "antisymmetry");

        // The tie-break, asserted so the KNOWN RESIDUAL is visible rather than latent. See the
        // `Ord` impl's doc: its named resolution is upstream's scale-equality refusal at the
        // relops (`reduce.rs:9772-9783`), which is a separate, owner-blocked change.
        let seven_p2 = CanonicalFixedPoint::new(BigInt::from(700), 2);
        let seven_p1 = CanonicalFixedPoint::new(BigInt::from(70), 1);
        assert_eq!(seven_p2.value_ratio(), seven_p1.value_ratio(), "premise: equal VALUE",);
        assert_eq!(
            seven_p2.cmp(&seven_p1),
            Ordering::Greater,
            "⚠ KNOWN RESIDUAL: equal value, so only the `places` tie-break can decide, and it \
             answers `7.00p2 > 7.0p1` — not a numeric fact. It exists to make `Ord` TOTAL. Its \
             resolution is the relops' scale-equality precondition, not a different `Ord`.",
        );
    }

    /// ★ The consistency obligation Rust states for `Ord`, checked over a scale matrix rather
    /// than argued: `a.cmp(&b) == Equal  ⟺  a == b`, for every ordered pair.
    #[test]
    fn cmp_equal_iff_eq_over_a_scale_matrix() {
        // Six values spanning: same value at three scales, a neighbouring value, a negative,
        // and zero (which `normalize_in_place` forces to `p0`).
        let matrix = [
            ("7p0", CanonicalFixedPoint::new(BigInt::from(7), 0)),
            ("7.0p1", CanonicalFixedPoint::new(BigInt::from(70), 1)),
            ("7.00p2", CanonicalFixedPoint::new(BigInt::from(700), 2)),
            ("6.99p2", CanonicalFixedPoint::new(BigInt::from(699), 2)),
            ("-7.0p1", CanonicalFixedPoint::new(BigInt::from(-70), 1)),
            ("0p0", CanonicalFixedPoint::new(BigInt::from(0), 3)),
        ];
        for (la, a) in &matrix {
            for (lb, b) in &matrix {
                assert_eq!(
                    a.cmp(b) == Ordering::Equal,
                    a == b,
                    "`cmp == Equal ⟺ ==` must hold for ({la}, {lb})",
                );
                // Hash agreement rides on the same pair, so check it in the same sweep.
                if a == b {
                    assert_eq!(hash_val(a), hash_val(b), "Eq ⇒ equal hash ({la}, {lb})");
                    assert_eq!(
                        a.to_canonical_bytes(),
                        b.to_canonical_bytes(),
                        "Eq ⇒ equal canonical bytes ({la}, {lb})",
                    );
                } else {
                    assert_ne!(
                        a.to_canonical_bytes(),
                        b.to_canonical_bytes(),
                        "`to_canonical_bytes` is a BICONDITIONAL over an exact `Vec<u8>` \
                         (dovetail/src/key.rs:96-104), so distinct values must write distinct \
                         bytes too ({la}, {lb})",
                    );
                }
            }
        }
    }

    /// ★ RE-DERIVED 2026-07-30 (work item #200) — this assertion INVERTED.
    ///
    /// It read `assert_eq!(hash_val(&x), hash_val(&y))` for `10.0p1` / `10p0`. `Hash` must
    /// agree with `Eq`, and `Eq` now separates them, so the hashes must differ too. ⚠ Note the
    /// obligation is only one-directional (`Eq ⇒ equal hash`); a hash COLLISION between unequal
    /// values would be legal. `assert_ne!` is nonetheless the right pin here, because the two
    /// hashes are built from genuinely different field streams and an accidental collision on
    /// `DefaultHasher` would itself be worth knowing about.
    #[test]
    fn hash_matches_eq() {
        let x = CanonicalFixedPoint::new(BigInt::from(100), 1);
        let y = CanonicalFixedPoint::new(BigInt::from(10), 0);
        assert_ne!(x, y, "premise: distinct since work item #200");
        assert_ne!(hash_val(&x), hash_val(&y), "distinct identity ⇒ distinct hash stream");
        let z = fp(1, 0, 0);
        assert_ne!(hash_val(&x), hash_val(&z));
    }

    /// ★ RE-DERIVED 2026-07-30 (work item #200). The round-trip row moved from `assert_eq!` to
    /// a value-level assertion, and the reason is worth stating because it is a NEW consequence
    /// of the ruling that nothing else records.
    ///
    /// It read `assert_eq!(s - half, one)`. `align_pair` returns at `max(places)`, so
    /// `(1p0 + 0.5p1) - 0.5p1` is `1.0p1 = (10, 1)`, not `1p0 = (1, 0)`. Under the old
    /// value-keyed `Eq` those were the same value and the round trip closed. Under identity on
    /// the raw pair they are distinct, so:
    ///
    /// ⚠ **`+` and `-` are no longer inverse AT THE LEVEL OF IDENTITY when the operand scales
    /// differ.** `(x + y) - y` denotes the same NUMBER as `x` but is a different VALUE, and
    /// therefore hashes differently, keys a `Map` differently, and occupies its own e-class.
    ///
    /// **Its named resolution is upstream's scale-equality refusal** (work item #186): once
    /// `+`/`-` refuse mixed scales, `max(places)` can only ever equal both operands' `places`,
    /// the widening disappears, and the round trip closes again at the identity level. That is
    /// a separate, owner-blocked change and is deliberately NOT made here — so this residual is
    /// REAL today and is pinned rather than hidden.
    #[test]
    fn add_sub_misaligned_places() {
        let one = fp(1, 0, 0);
        let half = fp(0, 5, 1);
        let s = one + half;
        let expected = fp(1, 5, 1);
        assert_eq!(s, expected, "1p0 + 0.5p1 == 1.5p1, at p1 on both sides — identity holds");

        let back = s - half;
        assert_eq!(back.value_ratio(), one.value_ratio(), "the round trip recovers the NUMBER 1",);
        assert_ne!(
            back, one,
            "⚠ …but not the VALUE `1p0`: `align_pair` widened to p1, so the result is `1.0p1`. \
             `+`/`-` are not identity-inverse across mixed scales. Closed by the scale-equality \
             precondition (work item #186), not by this ruling.",
        );
        assert_eq!(back.places(), 1, "the widened scale is where it came from");
    }

    #[test]
    fn mul_sums_places() {
        let a = fp(2, 0, 1);
        let b = fp(3, 0, 1);
        let p = a * b;
        assert_eq!(p.places(), 2);
        assert_eq!(p, fp(6, 0, 2));
    }

    #[test]
    fn neg_flips_unscaled_keeps_places() {
        let x = fp(3, 3, 1);
        let n = -x;
        assert_eq!(n.unscaled.get(), &BigInt::from(-33));
        assert_eq!(n.places(), 1);
        assert_eq!(-(-x), x);
    }

    #[test]
    fn bitwise_and_aligned() {
        let a = CanonicalFixedPoint::new(BigInt::from(12), 1);
        let b = CanonicalFixedPoint::new(BigInt::from(10), 1);
        let c = a & b;
        assert_eq!(c.unscaled.get(), &BigInt::from(8));
        assert_eq!(c.places(), 1);
    }

    #[test]
    fn bitwise_misaligned_places() {
        let a = CanonicalFixedPoint::new(BigInt::from(15), 0);
        let b = CanonicalFixedPoint::new(BigInt::from(14), 1);
        let c = a & b;
        // 15p0 → 150p1 aligned; 150 & 14 = 6
        assert_eq!(c.unscaled.get(), &BigInt::from(6));
        assert_eq!(c.places(), 1);
    }

    #[test]
    fn bitwise_or_xor() {
        let a = fp(5, 0, 0);
        let b = fp(3, 0, 0);
        assert_eq!(a | b, fp(7, 0, 0));
        assert_eq!(a ^ b, fp(6, 0, 0));
    }

    #[test]
    fn bitwise_negative_unscaled() {
        let a = CanonicalFixedPoint::new(BigInt::from(-4), 0);
        let b = CanonicalFixedPoint::new(BigInt::from(2), 0);
        let c = a & b;
        assert_eq!(c.unscaled.get(), &(BigInt::from(-4) & BigInt::from(2)));
    }
}
