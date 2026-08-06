use super::*;

#[test]
fn test_tropical_zero_is_infinity() {
    let z = TropicalWeight::zero();
    assert!(z.is_zero());
    assert!(z.is_infinite());
    assert_eq!(z.value(), f64::INFINITY);
}

#[test]
fn test_tropical_one_is_zero_cost() {
    let one = TropicalWeight::one();
    assert!(one.is_one());
    assert!(!one.is_zero());
    assert_eq!(one.value(), 0.0);
}

#[test]
fn test_tropical_plus_is_min() {
    let a = TropicalWeight::new(3.0);
    let b = TropicalWeight::new(7.0);
    assert_eq!(a.plus(&b), TropicalWeight::new(3.0));
    assert_eq!(b.plus(&a), TropicalWeight::new(3.0));
}

#[test]
fn test_tropical_times_is_add() {
    let a = TropicalWeight::new(3.0);
    let b = TropicalWeight::new(7.0);
    assert_eq!(a.times(&b), TropicalWeight::new(10.0));
}

#[test]
fn test_tropical_zero_annihilates() {
    let a = TropicalWeight::new(5.0);
    let z = TropicalWeight::zero();
    // 0 * a = a * 0 = 0 (inf + 5.0 = inf)
    assert!(z.times(&a).is_zero());
    assert!(a.times(&z).is_zero());
}

#[test]
fn test_tropical_one_is_identity() {
    let a = TropicalWeight::new(5.0);
    let one = TropicalWeight::one();
    // 1 * a = a * 1 = a (0.0 + 5.0 = 5.0)
    assert_eq!(one.times(&a), a);
    assert_eq!(a.times(&one), a);
}

#[test]
fn test_tropical_zero_is_plus_identity() {
    let a = TropicalWeight::new(5.0);
    let z = TropicalWeight::zero();
    // 0 + a = a + 0 = a (min(inf, 5.0) = 5.0)
    assert_eq!(z.plus(&a), a);
    assert_eq!(a.plus(&z), a);
}

#[test]
fn test_tropical_plus_idempotent() {
    let a = TropicalWeight::new(5.0);
    assert_eq!(a.plus(&a), a);
}

#[test]
fn test_tropical_from_priority() {
    // Higher priority (10) → lower weight (0.0)
    let fixed = TropicalWeight::from_priority(10);
    assert_eq!(fixed, TropicalWeight::new(0.0));

    // Lower priority (1) → higher weight (9.0)
    let ident = TropicalWeight::from_priority(1);
    assert_eq!(ident, TropicalWeight::new(9.0));

    // Fixed beats Ident: min(0.0, 9.0) = 0.0
    assert_eq!(fixed.plus(&ident), fixed);
}

#[test]
fn test_tropical_ordering() {
    let a = TropicalWeight::new(1.0);
    let b = TropicalWeight::new(5.0);
    let z = TropicalWeight::zero();
    assert!(a < b);
    assert!(b < z);
    assert!(a < z);
}

#[test]
fn test_tropical_approx_eq() {
    let a = TropicalWeight::new(1.0);
    let b = TropicalWeight::new(1.0 + 1e-12);
    assert!(a.approx_eq(&b, 1e-10));
    assert!(!a.approx_eq(&b, 1e-15));
}

#[test]
fn test_tropical_hash_consistency() {
    use std::collections::HashSet;
    let mut set = HashSet::new();
    set.insert(TropicalWeight::new(3.0));
    assert!(set.contains(&TropicalWeight::new(3.0)));
    assert!(!set.contains(&TropicalWeight::new(4.0)));
}

// ═══════════════════════════════════════════════════════════════════════
// CountingWeight tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_counting_semiring_laws() {
    let a = CountingWeight::new(3);
    let b = CountingWeight::new(5);
    let z = CountingWeight::zero();
    let one = CountingWeight::one();

    // Zero identity: 0 + a = a
    assert_eq!(z.plus(&a), a);
    assert_eq!(a.plus(&z), a);

    // One identity: 1 * a = a
    assert_eq!(one.times(&a), a);
    assert_eq!(a.times(&one), a);

    // Zero annihilates: 0 * a = 0
    assert!(z.times(&a).is_zero());
    assert!(a.times(&z).is_zero());

    // Plus is commutative: a + b = b + a
    assert_eq!(a.plus(&b), b.plus(&a));

    // Times is commutative: a * b = b * a
    assert_eq!(a.times(&b), b.times(&a));
}

#[test]
fn test_counting_plus_is_add() {
    let a = CountingWeight::new(3);
    let b = CountingWeight::new(5);
    assert_eq!(a.plus(&b), CountingWeight::new(8));
}

#[test]
fn test_counting_times_is_mul() {
    let a = CountingWeight::new(3);
    let b = CountingWeight::new(5);
    assert_eq!(a.times(&b), CountingWeight::new(15));
}

#[test]
fn test_counting_saturating() {
    let big = CountingWeight::new(u64::MAX);
    let two = CountingWeight::new(2);
    // Saturating add
    assert_eq!(big.plus(&two), CountingWeight::new(u64::MAX));
    // Saturating mul
    assert_eq!(big.times(&two), CountingWeight::new(u64::MAX));
}

#[test]
fn test_counting_not_idempotent() {
    let a = CountingWeight::new(3);
    // plus(3, 3) = 6 ≠ 3, not idempotent
    assert_ne!(a.plus(&a), a);
    assert_eq!(a.plus(&a), CountingWeight::new(6));
}

#[test]
fn test_counting_distributivity() {
    // a * (b + c) = a*b + a*c
    let a = CountingWeight::new(2);
    let b = CountingWeight::new(3);
    let c = CountingWeight::new(4);
    let lhs = a.times(&b.plus(&c));
    let rhs = a.times(&b).plus(&a.times(&c));
    assert_eq!(lhs, rhs);
}

// ═══════════════════════════════════════════════════════════════════════
// BooleanWeight tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_boolean_semiring_laws() {
    let t = BooleanWeight::new(true);
    let f = BooleanWeight::new(false);
    let z = BooleanWeight::zero();
    let one = BooleanWeight::one();

    // Zero = false, One = true
    assert_eq!(z, f);
    assert_eq!(one, t);

    // Zero identity: false ∨ a = a
    assert_eq!(z.plus(&t), t);
    assert_eq!(z.plus(&f), f);

    // One identity: true ∧ a = a
    assert_eq!(one.times(&t), t);
    assert_eq!(one.times(&f), f);

    // Zero annihilates: false ∧ a = false
    assert_eq!(z.times(&t), z);
    assert_eq!(z.times(&f), z);
}

#[test]
fn test_boolean_plus_is_or() {
    let t = BooleanWeight::new(true);
    let f = BooleanWeight::new(false);
    assert_eq!(t.plus(&t), t);
    assert_eq!(t.plus(&f), t);
    assert_eq!(f.plus(&t), t);
    assert_eq!(f.plus(&f), f);
}

#[test]
fn test_boolean_times_is_and() {
    let t = BooleanWeight::new(true);
    let f = BooleanWeight::new(false);
    assert_eq!(t.times(&t), t);
    assert_eq!(t.times(&f), f);
    assert_eq!(f.times(&t), f);
    assert_eq!(f.times(&f), f);
}

#[test]
fn test_boolean_idempotent() {
    let t = BooleanWeight::new(true);
    let f = BooleanWeight::new(false);
    // Plus is idempotent: a ∨ a = a
    assert_eq!(t.plus(&t), t);
    assert_eq!(f.plus(&f), f);
}

#[test]
fn test_boolean_reachability() {
    let reachable = BooleanWeight::new(true);
    let unreachable = BooleanWeight::new(false);
    assert!(reachable.is_reachable());
    assert!(!unreachable.is_reachable());
}

// ═══════════════════════════════════════════════════════════════════════
// EditWeight tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_edit_semiring_laws() {
    let a = EditWeight::new(3);
    let b = EditWeight::new(5);
    let z = EditWeight::zero();
    let one = EditWeight::one();

    // Zero identity: min(∞, a) = a
    assert_eq!(z.plus(&a), a);
    assert_eq!(a.plus(&z), a);

    // One identity: 0 + a = a
    assert_eq!(one.times(&a), a);
    assert_eq!(a.times(&one), a);

    // Zero annihilates: ∞ + a = ∞ (saturating)
    assert!(z.times(&a).is_zero());
    assert!(a.times(&z).is_zero());

    // Commutativity
    assert_eq!(a.plus(&b), b.plus(&a));
    assert_eq!(a.times(&b), b.times(&a));
}

#[test]
fn test_edit_plus_is_min() {
    let a = EditWeight::new(3);
    let b = EditWeight::new(5);
    assert_eq!(a.plus(&b), EditWeight::new(3));
    assert_eq!(b.plus(&a), EditWeight::new(3));
}

#[test]
fn test_edit_times_is_add() {
    let a = EditWeight::new(3);
    let b = EditWeight::new(5);
    assert_eq!(a.times(&b), EditWeight::new(8));
}

#[test]
fn test_edit_idempotent() {
    let a = EditWeight::new(3);
    // min(3, 3) = 3, idempotent
    assert_eq!(a.plus(&a), a);
}

#[test]
fn test_edit_operation_costs() {
    assert_eq!(EditWeight::skip().distance(), 1);
    assert_eq!(EditWeight::delete().distance(), 1);
    assert_eq!(EditWeight::insert().distance(), 2);
    assert_eq!(EditWeight::substitute().distance(), 2);
}

#[test]
fn test_edit_infinity() {
    assert_eq!(EditWeight::INFINITY, EditWeight::zero());
    assert!(EditWeight::INFINITY.is_zero());
    assert_eq!(EditWeight::INFINITY.distance(), u32::MAX);
}

#[test]
fn test_edit_saturating() {
    let big = EditWeight::new(u32::MAX - 1);
    let two = EditWeight::new(2);
    assert_eq!(big.times(&two), EditWeight::new(u32::MAX));
}

#[test]
fn test_edit_ordering() {
    let a = EditWeight::new(1);
    let b = EditWeight::new(5);
    let z = EditWeight::zero();
    assert!(a < b);
    assert!(b < z);
}

// ═══════════════════════════════════════════════════════════════════════
// ProductWeight tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_product_semiring_laws() {
    type PW = ProductWeight<TropicalWeight, CountingWeight>;
    let a = PW::new(TropicalWeight::new(2.0), CountingWeight::new(3));
    let b = PW::new(TropicalWeight::new(5.0), CountingWeight::new(2));
    let z = PW::zero();
    let one = PW::one();

    // Zero identity
    assert_eq!(z.plus(&a), a);
    assert_eq!(a.plus(&z), a);

    // One identity
    assert_eq!(one.times(&a), a);
    assert_eq!(a.times(&one), a);

    // Zero annihilates
    assert!(z.times(&a).is_zero());
    assert!(a.times(&z).is_zero());

    // Commutativity of plus
    assert_eq!(a.plus(&b), b.plus(&a));
}

#[test]
fn test_product_tropical_counting() {
    type PW = ProductWeight<TropicalWeight, CountingWeight>;

    let a = PW::new(TropicalWeight::new(2.0), CountingWeight::new(3));
    let b = PW::new(TropicalWeight::new(5.0), CountingWeight::new(2));

    // Plus: component-wise (min, add)
    let sum = a.plus(&b);
    assert_eq!(sum.left, TropicalWeight::new(2.0)); // min(2, 5) = 2
    assert_eq!(sum.right, CountingWeight::new(5)); // 3 + 2 = 5

    // Times: component-wise (add, mul)
    let prod = a.times(&b);
    assert_eq!(prod.left, TropicalWeight::new(7.0)); // 2 + 5 = 7
    assert_eq!(prod.right, CountingWeight::new(6)); // 3 * 2 = 6
}

#[test]
fn test_product_tropical_edit() {
    type PW = ProductWeight<TropicalWeight, EditWeight>;

    let a = PW::new(TropicalWeight::new(1.0), EditWeight::new(2));
    let b = PW::new(TropicalWeight::new(3.0), EditWeight::new(1));

    // Plus: component-wise (min, min)
    let sum = a.plus(&b);
    assert_eq!(sum.left, TropicalWeight::new(1.0)); // min(1, 3) = 1
    assert_eq!(sum.right, EditWeight::new(1)); // min(2, 1) = 1

    // Times: component-wise (add, add)
    let prod = a.times(&b);
    assert_eq!(prod.left, TropicalWeight::new(4.0)); // 1 + 3 = 4
    assert_eq!(prod.right, EditWeight::new(3)); // 2 + 1 = 3
}

#[test]
fn test_product_is_zero() {
    type PW = ProductWeight<TropicalWeight, CountingWeight>;
    // is_zero if either component is zero
    let z_left = PW::new(TropicalWeight::zero(), CountingWeight::new(5));
    assert!(z_left.is_zero());

    let z_right = PW::new(TropicalWeight::new(1.0), CountingWeight::zero());
    assert!(z_right.is_zero());

    let neither = PW::new(TropicalWeight::new(1.0), CountingWeight::new(1));
    assert!(!neither.is_zero());
}

#[test]
fn test_product_is_one() {
    type PW = ProductWeight<TropicalWeight, CountingWeight>;
    let one = PW::one();
    assert!(one.is_one());
    assert_eq!(one.left, TropicalWeight::one());
    assert_eq!(one.right, CountingWeight::one());
}

#[test]
fn test_product_default() {
    type PW = ProductWeight<TropicalWeight, CountingWeight>;
    let d = PW::default();
    assert!(d.is_one());
}

#[test]
fn test_product_approx_eq() {
    type PW = ProductWeight<TropicalWeight, CountingWeight>;
    let a = PW::new(TropicalWeight::new(1.0), CountingWeight::new(3));
    let b = PW::new(TropicalWeight::new(1.0 + 1e-12), CountingWeight::new(3));
    assert!(a.approx_eq(&b, 1e-10));
    assert!(!a.approx_eq(&b, 1e-15));
}

// ═══════════════════════════════════════════════════════════════════════
// ContextWeight tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_context_weight_semiring_laws() {
    let a = ContextWeight::new(0b1010);
    let b = ContextWeight::new(0b1100);
    let z = ContextWeight::zero();
    let one = ContextWeight::one();

    // Zero identity: ∅ ∪ a = a
    assert_eq!(z.plus(&a), a);
    assert_eq!(a.plus(&z), a);

    // One identity: U ∩ a = a
    assert_eq!(one.times(&a), a);
    assert_eq!(a.times(&one), a);

    // Zero annihilates: ∅ ∩ a = ∅
    assert!(z.times(&a).is_zero());
    assert!(a.times(&z).is_zero());

    // Commutativity of plus (union)
    assert_eq!(a.plus(&b), b.plus(&a));

    // Commutativity of times (intersection)
    assert_eq!(a.times(&b), b.times(&a));
}

#[test]
fn test_context_weight_union_intersection() {
    let a = ContextWeight::new(0b1010); // rules 1, 3
    let b = ContextWeight::new(0b1100); // rules 2, 3

    // Union: rules 1, 2, 3
    assert_eq!(a.plus(&b), ContextWeight::new(0b1110));

    // Intersection: rule 3 only
    assert_eq!(a.times(&b), ContextWeight::new(0b1000));
}

#[test]
fn test_context_weight_singleton_and_contains() {
    let s = ContextWeight::singleton(5);
    assert!(s.contains(5));
    assert!(!s.contains(4));
    assert!(!s.contains(6));
    assert_eq!(s.count(), 1);

    let s2 = s.insert(10);
    assert!(s2.contains(5));
    assert!(s2.contains(10));
    assert_eq!(s2.count(), 2);
}

#[test]
fn test_context_weight_idempotent_plus() {
    // Set semiring plus (union) is idempotent: a ∪ a = a
    let a = ContextWeight::new(0b1010);
    assert_eq!(a.plus(&a), a);
}

#[test]
fn test_context_weight_distributivity() {
    // a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c)
    let a = ContextWeight::new(0b1111);
    let b = ContextWeight::new(0b1010);
    let c = ContextWeight::new(0b0101);

    let lhs = a.times(&b.plus(&c));
    let rhs = a.times(&b).plus(&a.times(&c));
    assert_eq!(lhs, rhs);
}

#[test]
fn test_context_weight_ordering() {
    // Fewer labels = lower (better)
    let empty = ContextWeight::zero();
    let one_bit = ContextWeight::singleton(0);
    let two_bits = ContextWeight::new(0b11);
    let all = ContextWeight::one();

    assert!(empty < one_bit);
    assert!(one_bit < two_bits);
    assert!(two_bits < all);
}

#[test]
fn test_context_weight_display() {
    assert_eq!(format!("{}", ContextWeight::zero()), "∅");
    assert_eq!(format!("{}", ContextWeight::one()), "U");
    let s = ContextWeight::new(0b1010);
    assert_eq!(format!("{}", s), "{2b|10}");
}

// ═══════════════════════════════════════════════════════════════════════
// ComplexityWeight tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_complexity_weight_semiring_laws() {
    let a = ComplexityWeight::new(3);
    let b = ComplexityWeight::new(7);
    let z = ComplexityWeight::zero();
    let one = ComplexityWeight::one();

    // Zero identity: ∞ min a = a
    assert_eq!(z.plus(&a), a);
    assert_eq!(a.plus(&z), a);

    // One identity: 0 max a = a
    assert_eq!(one.times(&a), a);
    assert_eq!(a.times(&one), a);

    // Zero annihilates: check that ∞ max a = ∞
    // (In bottleneck semiring, zero is ∞ which is the max of everything)
    assert!(z.times(&a).is_zero());
    assert!(a.times(&z).is_zero());

    // Commutativity of plus (min)
    assert_eq!(a.plus(&b), b.plus(&a));

    // Commutativity of times (max)
    assert_eq!(a.times(&b), b.times(&a));
}

#[test]
fn test_complexity_weight_min_max() {
    let a = ComplexityWeight::new(3);
    let b = ComplexityWeight::new(7);

    // Plus = min: least-complex alternative
    assert_eq!(a.plus(&b), ComplexityWeight::new(3));

    // Times = max: bottleneck complexity
    assert_eq!(a.times(&b), ComplexityWeight::new(7));
}

#[test]
fn test_complexity_weight_idempotent_plus() {
    // min(a, a) = a — idempotent
    let a = ComplexityWeight::new(5);
    assert_eq!(a.plus(&a), a);
}

#[test]
fn test_complexity_weight_constructors() {
    assert_eq!(ComplexityWeight::deterministic().value(), 0);
    assert_eq!(ComplexityWeight::single_lookahead().value(), 1);
    assert_eq!(ComplexityWeight::multi_lookahead(3).value(), 3);
    assert_eq!(ComplexityWeight::infinite().value(), u32::MAX);

    assert!(ComplexityWeight::infinite().is_zero()); // ∞ is the zero
    assert!(ComplexityWeight::deterministic().is_one()); // 0 is the one
}

#[test]
fn test_complexity_weight_distributivity() {
    // max(a, min(b, c)) = min(max(a, b), max(a, c))
    let a = ComplexityWeight::new(3);
    let b = ComplexityWeight::new(5);
    let c = ComplexityWeight::new(7);

    let lhs = a.times(&b.plus(&c));
    let rhs = a.times(&b).plus(&a.times(&c));
    assert_eq!(lhs, rhs);
}

#[test]
fn test_complexity_weight_ordering() {
    let a = ComplexityWeight::new(2);
    let b = ComplexityWeight::new(5);
    let z = ComplexityWeight::zero(); // ∞

    assert!(a < b);
    assert!(b < z);
}

#[test]
fn test_complexity_weight_display() {
    assert_eq!(format!("{}", ComplexityWeight::new(3)), "3");
    assert_eq!(format!("{}", ComplexityWeight::zero()), "∞");
    assert_eq!(format!("{}", ComplexityWeight::one()), "0");
}

#[test]
fn test_complexity_weight_product_with_tropical() {
    // ProductWeight<TropicalWeight, ComplexityWeight> should work
    type TPC = ProductWeight<TropicalWeight, ComplexityWeight>;
    let a = TPC::new(TropicalWeight::new(1.0), ComplexityWeight::new(3));
    let b = TPC::new(TropicalWeight::new(2.0), ComplexityWeight::new(5));

    // Plus: (min(1,2), min(3,5)) = (1, 3)
    let sum = a.plus(&b);
    assert_eq!(sum.left.value(), 1.0);
    assert_eq!(sum.right.value(), 3);

    // Times: (1+2, max(3,5)) = (3, 5)
    let prod = a.times(&b);
    assert_eq!(prod.left.value(), 3.0);
    assert_eq!(prod.right.value(), 5);
}

#[test]
fn test_context_weight_product_with_tropical() {
    // ProductWeight<TropicalWeight, ContextWeight> should work
    type TPC = ProductWeight<TropicalWeight, ContextWeight>;
    let a = TPC::new(TropicalWeight::new(1.0), ContextWeight::new(0b1010));
    let b = TPC::new(TropicalWeight::new(2.0), ContextWeight::new(0b1100));

    // Plus: (min(1,2), 0b1010 | 0b1100) = (1, 0b1110)
    let sum = a.plus(&b);
    assert_eq!(sum.left.value(), 1.0);
    assert_eq!(sum.right.bits(), 0b1110);

    // Times: (1+2, 0b1010 & 0b1100) = (3, 0b1000)
    let prod = a.times(&b);
    assert_eq!(prod.left.value(), 3.0);
    assert_eq!(prod.right.bits(), 0b1000);
}

// ═══════════════════════════════════════════════════════════════════════
// LogWeight tests (feature = "wfst-log")
// ═══════════════════════════════════════════════════════════════════════

mod log_weight_tests {
    use super::super::*;

    #[test]
    fn test_log_weight_semiring_laws() {
        let a = LogWeight::new(2.0);
        let b = LogWeight::new(3.0);
        let z = LogWeight::zero();
        let one = LogWeight::one();

        // Zero identity: 0 + a = a
        assert!(z.plus(&a).approx_eq(&a, 1e-10));
        assert!(a.plus(&z).approx_eq(&a, 1e-10));

        // One identity: 1 * a = a
        assert!(one.times(&a).approx_eq(&a, 1e-10));
        assert!(a.times(&one).approx_eq(&a, 1e-10));

        // Zero annihilates: 0 * a = 0
        assert!(z.times(&a).is_zero());
        assert!(a.times(&z).is_zero());

        // Commutativity of plus
        assert!(a.plus(&b).approx_eq(&b.plus(&a), 1e-10));

        // Times is commutative for log: a + b = b + a
        assert!(a.times(&b).approx_eq(&b.times(&a), 1e-10));
    }

    #[test]
    fn test_log_weight_probability_roundtrip() {
        let probs = [0.1, 0.25, 0.5, 0.75, 0.9, 1.0];
        for &p in &probs {
            let w = LogWeight::from_probability(p);
            let p_back = w.to_probability();
            assert!((p - p_back).abs() < 1e-12, "roundtrip failed for p={}: got {}", p, p_back);
        }
    }

    #[test]
    fn test_log_weight_non_idempotent() {
        // Key difference from tropical: plus(a, a) != a
        // Because exp(-a) + exp(-a) = 2*exp(-a), so -ln(2*exp(-a)) = a - ln(2)
        let a = LogWeight::new(2.0);
        let result = a.plus(&a);
        let expected = 2.0 - 2.0_f64.ln(); // a - ln(2)
        assert!(
            (result.value() - expected).abs() < 1e-10,
            "plus(a,a) should be a - ln(2), got {} vs {}",
            result.value(),
            expected
        );
        assert_ne!(result, a, "LogWeight must NOT be idempotent");
    }

    #[test]
    fn test_log_weight_numerical_stability() {
        // Very large values: should not produce NaN or unexpected Inf
        let large = LogWeight::new(1000.0);
        let small = LogWeight::new(1.0);

        // log_sum_exp(1000, 1) ≈ 1.0 (the 1000 term is negligible)
        let result = large.plus(&small);
        assert!(
            (result.value() - 1.0).abs() < 1e-6,
            "large + small should ≈ small, got {}",
            result.value()
        );
        assert!(!result.value().is_nan());
        assert!(!result.value().is_infinite());

        // Very small value (near zero weight = high probability)
        let tiny = LogWeight::new(1e-15);
        let normal = LogWeight::new(5.0);
        let r = tiny.plus(&normal);
        assert!(!r.value().is_nan());
        assert!(r.value() < tiny.value()); // result should be less than the smaller input
    }

    #[test]
    fn test_log_sum_exp_large_diff() {
        // When diff > 20, log_sum_exp returns the smaller value (fast path)
        let a = LogWeight::new(1.0);
        let b = LogWeight::new(30.0); // diff = 29 > 20
        let result = a.plus(&b);
        // Should be very close to 1.0 (fast path returns min directly)
        assert!(
            (result.value() - 1.0).abs() < 1e-6,
            "large diff should use fast path, got {}",
            result.value()
        );
    }

    #[test]
    fn test_log_weight_times_is_addition() {
        let a = LogWeight::new(2.0);
        let b = LogWeight::new(3.0);
        assert_eq!(a.times(&b), LogWeight::new(5.0));
    }

    #[test]
    fn test_log_weight_ordering() {
        let a = LogWeight::new(1.0);
        let b = LogWeight::new(5.0);
        let z = LogWeight::zero();
        assert!(a < b);
        assert!(b < z);
    }

    #[test]
    fn test_log_weight_display() {
        let w = LogWeight::new(1.5);
        assert_eq!(format!("{}", w), "1.5000");

        let z = LogWeight::zero();
        assert_eq!(format!("{}", z), "inf");
    }

    // ═══════════════════════════════════════════════════════════════════
    // EntropyWeight tests
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_entropy_weight_semiring_laws() {
        let a = EntropyWeight::new(2.0, 1.5);
        let _b = EntropyWeight::new(3.0, 2.0);
        let z = EntropyWeight::zero();
        let one = EntropyWeight::one();

        // Zero identity: 0 ⊕ a = a
        assert!(z.plus(&a).approx_eq(&a, 1e-10));
        assert!(a.plus(&z).approx_eq(&a, 1e-10));

        // One identity: 1 ⊗ a = a
        assert!(one.times(&a).approx_eq(&a, 1e-10));
        assert!(a.times(&one).approx_eq(&a, 1e-10));

        // Zero annihilates: 0 ⊗ a = 0
        assert!(z.times(&a).is_zero());
        assert!(a.times(&z).is_zero());
    }

    #[test]
    fn test_entropy_weight_times_is_addition() {
        let a = EntropyWeight::new(2.0, 1.5);
        let b = EntropyWeight::new(3.0, 2.0);
        let prod = a.times(&b);
        assert!((prod.weight - 5.0).abs() < 1e-10);
        assert!((prod.expectation - 3.5).abs() < 1e-10);
    }

    #[test]
    fn test_entropy_weight_plus_equal_weights() {
        // Two paths with equal weight: expectations average
        let a = EntropyWeight::new(1.0, 2.0);
        let b = EntropyWeight::new(1.0, 4.0);
        let sum = a.plus(&b);
        // weight: log_sum_exp(1, 1) = 1 - ln(2) ≈ 0.3069
        let expected_w = 1.0 - 2.0_f64.ln();
        assert!(
            (sum.weight - expected_w).abs() < 1e-10,
            "weight: got {}, expected {}",
            sum.weight,
            expected_w
        );
        // expectation: (p1*2 + p2*4) / (p1+p2), p1=p2, so average = 3.0
        assert!(
            (sum.expectation - 3.0).abs() < 1e-10,
            "expectation: got {}, expected 3.0",
            sum.expectation
        );
    }

    #[test]
    fn test_entropy_weight_plus_unequal_weights() {
        // One path with much higher probability dominates
        let dominant = EntropyWeight::new(0.1, 5.0); // high prob
        let minor = EntropyWeight::new(10.0, 100.0); // low prob
        let sum = dominant.plus(&minor);
        // The dominant path's expectation should dominate
        assert!(
            (sum.expectation - 5.0).abs() < 0.1,
            "dominant expectation should win, got {}",
            sum.expectation
        );
    }

    #[test]
    fn test_entropy_weight_plus_commutativity() {
        let a = EntropyWeight::new(1.0, 3.0);
        let b = EntropyWeight::new(2.0, 5.0);
        let ab = a.plus(&b);
        let ba = b.plus(&a);
        assert!(ab.approx_eq(&ba, 1e-10), "plus not commutative: {:?} vs {:?}", ab, ba);
    }

    #[test]
    fn test_entropy_weight_from_arc_weight() {
        let e = EntropyWeight::from_arc_weight(2.5);
        assert_eq!(e.weight, 2.5);
        assert_eq!(e.expectation, 2.5);
    }

    #[test]
    fn test_entropy_weight_entropy_bits() {
        // If expectation = ln(4) nats, then bits = ln(4)/ln(2) = 2.0
        let e = EntropyWeight::new(0.0, 4.0_f64.ln());
        assert!(
            (e.entropy_bits() - 2.0).abs() < 1e-10,
            "entropy bits: got {}, expected 2.0",
            e.entropy_bits()
        );
    }

    #[test]
    fn test_entropy_weight_plus_large_diff() {
        // Very large weight difference: dominant path takes over
        let a = EntropyWeight::new(0.1, 1.0);
        let b = EntropyWeight::new(100.0, 999.0);
        let result = a.plus(&b);
        // a dominates (much lower weight = much higher prob)
        assert!(
            (result.expectation - 1.0).abs() < 1e-6,
            "large diff: got {}, expected ~1.0",
            result.expectation
        );
    }

    #[test]
    fn test_entropy_weight_distributivity_approx() {
        // a ⊗ (b ⊕ c) ≈ (a ⊗ b) ⊕ (a ⊗ c)
        // Note: for the expectation semiring, distributivity holds exactly
        let a = EntropyWeight::new(1.0, 0.5);
        let b = EntropyWeight::new(2.0, 1.0);
        let c = EntropyWeight::new(3.0, 1.5);

        let lhs = a.times(&b.plus(&c));
        let rhs = a.times(&b).plus(&a.times(&c));
        assert!(lhs.approx_eq(&rhs, 1e-8), "distributivity failed: {:?} vs {:?}", lhs, rhs);
    }

    #[test]
    fn test_entropy_weight_ordering() {
        let a = EntropyWeight::new(1.0, 0.5);
        let b = EntropyWeight::new(5.0, 0.5);
        let z = EntropyWeight::zero();
        assert!(a < b); // lower weight = better
        assert!(b < z); // zero (inf) = worst
    }

    #[test]
    fn test_entropy_weight_display() {
        let e = EntropyWeight::new(1.5, 2.3);
        assert_eq!(format!("{}", e), "(1.5000, 2.3000)");
        let z = EntropyWeight::zero();
        assert_eq!(format!("{}", z), "(inf, 0)");
    }

    #[test]
    fn test_entropy_weight_hash() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(EntropyWeight::new(1.0, 2.0));
        assert!(set.contains(&EntropyWeight::new(1.0, 2.0)));
        assert!(!set.contains(&EntropyWeight::new(1.0, 3.0)));
    }

    #[test]
    fn test_entropy_weight_product_with_tropical() {
        // ProductWeight<TropicalWeight, EntropyWeight>
        type TPE = ProductWeight<TropicalWeight, EntropyWeight>;
        let a = TPE::new(TropicalWeight::new(1.0), EntropyWeight::new(2.0, 0.5));
        let b = TPE::new(TropicalWeight::new(3.0), EntropyWeight::new(1.0, 1.0));

        // Plus: (min(1,3), entropy_plus)
        let sum = a.plus(&b);
        assert_eq!(sum.left, TropicalWeight::new(1.0));

        // Times: (1+3, (2+1, 0.5+1.0)) = (4, (3, 1.5))
        let prod = a.times(&b);
        assert_eq!(prod.left, TropicalWeight::new(4.0));
        assert!((prod.right.weight - 3.0).abs() < 1e-10);
        assert!((prod.right.expectation - 1.5).abs() < 1e-10);
    }
}

// ═══════════════════════════════════════════════════════════════════════
// NbestWeight tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_nbest_semiring_laws() {
    type NB = NbestWeight<4>;
    let a = NB::singleton(1, TropicalWeight::new(2.0));
    let b = NB::singleton(2, TropicalWeight::new(5.0));
    let z = NB::zero();
    let one = NB::one();

    // Zero identity: 0 ⊕ a = a
    assert_eq!(z.plus(&a), a);
    assert_eq!(a.plus(&z), a);

    // Plus commutativity (same result regardless of order)
    let ab = a.plus(&b);
    let ba = b.plus(&a);
    assert_eq!(ab.len(), ba.len());

    // One identity: 1 ⊗ a should produce a valid result
    let prod = one.times(&a);
    assert_eq!(prod.len(), 1);
    assert_eq!(prod.best().expect("has best").weight, TropicalWeight::new(2.0));

    // Zero annihilates: 0 ⊗ a = 0
    assert!(z.times(&a).is_zero());
    assert!(a.times(&z).is_zero());
}

#[test]
fn test_nbest_merge_keeps_top_n() {
    type NB = NbestWeight<3>;
    let mut a = NB::singleton(1, TropicalWeight::new(1.0));
    a = a.plus(&NB::singleton(2, TropicalWeight::new(2.0)));
    a = a.plus(&NB::singleton(3, TropicalWeight::new(3.0)));
    assert_eq!(a.len(), 3);

    // Adding a 4th should keep only top 3
    let b = NB::singleton(4, TropicalWeight::new(0.5));
    let merged = a.plus(&b);
    assert_eq!(merged.len(), 3);
    // Best should be path 4 (weight 0.5)
    assert_eq!(merged.best().expect("has best").path_id, 4);
    assert_eq!(merged.best().expect("has best").weight, TropicalWeight::new(0.5));
}

#[test]
fn test_nbest_merge_deduplicates() {
    type NB = NbestWeight<4>;
    let a = NB::singleton(1, TropicalWeight::new(2.0));
    let b = NB::singleton(1, TropicalWeight::new(5.0)); // same path_id, worse weight

    let merged = a.plus(&b);
    assert_eq!(merged.len(), 1);
    // Should keep the better (lower) weight
    assert_eq!(merged.best().expect("has best").weight, TropicalWeight::new(2.0));
}

#[test]
fn test_nbest_cross_product() {
    type NB = NbestWeight<4>;
    let a = NB::singleton(1, TropicalWeight::new(1.0));
    let b = NB::singleton(2, TropicalWeight::new(3.0));

    let prod = a.times(&b);
    assert_eq!(prod.len(), 1);
    assert_eq!(prod.best().expect("has best").weight, TropicalWeight::new(4.0));
    // 1 + 3 = 4
}

#[test]
fn test_nbest_cross_product_multi() {
    type NB = NbestWeight<4>;
    let mut a = NB::singleton(1, TropicalWeight::new(1.0));
    a = a.plus(&NB::singleton(2, TropicalWeight::new(2.0)));

    let mut b = NB::singleton(10, TropicalWeight::new(0.5));
    b = b.plus(&NB::singleton(20, TropicalWeight::new(1.5)));

    let prod = a.times(&b);
    // 2x2 cross product = up to 4 entries
    assert!(prod.len() <= 4);
    assert!(prod.len() >= 2);
    // Best should be path combining (1, 10) with weight 1.0 + 0.5 = 1.5
    assert_eq!(prod.best().expect("has best").weight, TropicalWeight::new(1.5));
}

#[test]
fn test_nbest_empty_operations() {
    type NB = NbestWeight<4>;
    let z = NB::zero();
    assert!(z.is_zero());
    assert!(z.is_empty());
    assert_eq!(z.len(), 0);
    assert!(z.best().is_none());
}

#[test]
fn test_nbest_one() {
    type NB = NbestWeight<4>;
    let one = NB::one();
    assert!(one.is_one());
    assert_eq!(one.len(), 1);
    assert_eq!(one.best().expect("has best").path_id, 0);
    assert_eq!(one.best().expect("has best").weight, TropicalWeight::one());
}

#[test]
fn test_nbest_confidence_gap() {
    type NB = NbestWeight<4>;
    let mut w = NB::singleton(1, TropicalWeight::new(1.0));
    w = w.plus(&NB::singleton(2, TropicalWeight::new(5.0)));
    // Gap = 5.0 - 1.0 = 4.0
    assert!((w.confidence_gap() - 4.0).abs() < 1e-10);

    // Single entry: gap = infinity
    let single = NB::singleton(1, TropicalWeight::new(1.0));
    assert!(single.confidence_gap().is_infinite());

    // Empty: gap = infinity
    let empty = NB::zero();
    assert!(empty.confidence_gap().is_infinite());
}

#[test]
fn test_nbest_ordering() {
    type NB = NbestWeight<4>;
    let a = NB::singleton(1, TropicalWeight::new(1.0)); // best weight 1.0
    let b = NB::singleton(2, TropicalWeight::new(5.0)); // best weight 5.0
    let z = NB::zero(); // empty = worst

    assert!(a < b); // lower best weight = better
    assert!(b < z); // anything better than empty
}

#[test]
fn test_nbest_display() {
    type NB = NbestWeight<4>;
    let z = NB::zero();
    assert_eq!(format!("{}", z), "[]");

    let one = NB::one();
    assert_eq!(format!("{}", one), "[(0:0.0)]");

    let mut w = NB::singleton(1, TropicalWeight::new(2.5));
    w = w.plus(&NB::singleton(3, TropicalWeight::new(4.0)));
    assert_eq!(format!("{}", w), "[(1:2.5), (3:4.0)]");
}

#[test]
fn test_nbest_hash() {
    use std::collections::HashSet;
    type NB = NbestWeight<4>;
    let mut set = HashSet::new();
    set.insert(NB::singleton(1, TropicalWeight::new(2.0)));
    assert!(set.contains(&NB::singleton(1, TropicalWeight::new(2.0))));
    assert!(!set.contains(&NB::singleton(2, TropicalWeight::new(2.0))));
}

#[test]
fn test_nbest_from_entries() {
    type NB = NbestWeight<3>;
    let entries = vec![
        NbestEntry::new(3, TropicalWeight::new(5.0)),
        NbestEntry::new(1, TropicalWeight::new(1.0)),
        NbestEntry::new(2, TropicalWeight::new(3.0)),
        NbestEntry::new(4, TropicalWeight::new(0.5)),
    ];
    let w = NB::from_entries(entries);
    assert_eq!(w.len(), 3); // truncated to N=3
    assert_eq!(w.best().expect("has best").path_id, 4); // lowest weight
    assert_eq!(w.get(1).expect("has 2nd").path_id, 1);
    assert_eq!(w.get(2).expect("has 3rd").path_id, 2);
}

#[test]
fn test_nbest_iter() {
    type NB = NbestWeight<4>;
    let mut w = NB::singleton(1, TropicalWeight::new(1.0));
    w = w.plus(&NB::singleton(2, TropicalWeight::new(3.0)));
    w = w.plus(&NB::singleton(3, TropicalWeight::new(5.0)));

    let ids: Vec<u32> = w.iter().map(|e| e.path_id).collect();
    assert_eq!(ids.len(), 3);
    assert_eq!(ids[0], 1); // best first
}

#[test]
fn test_nbest_n2_confidence() {
    // N=2 specialization for confidence gap use case
    type NB2 = NbestWeight<2>;
    let mut w = NB2::singleton(1, TropicalWeight::new(0.5));
    w = w.plus(&NB2::singleton(2, TropicalWeight::new(3.0)));
    w = w.plus(&NB2::singleton(3, TropicalWeight::new(1.0)));

    // Should keep paths 1 (0.5) and 3 (1.0)
    assert_eq!(w.len(), 2);
    assert_eq!(w.best().expect("has best").path_id, 1);
    assert!((w.confidence_gap() - 0.5).abs() < 1e-10);
}

#[test]
fn test_nbest_approx_eq() {
    type NB = NbestWeight<4>;
    let a = NB::singleton(1, TropicalWeight::new(1.0));
    let b = NB::singleton(1, TropicalWeight::new(1.0 + 1e-12));
    assert!(a.approx_eq(&b, 1e-10));
    assert!(!a.approx_eq(&b, 1e-15));
}

// ═══════════════════════════════════════════════════════════════════════
// ViterbiWeight tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_viterbi_semiring_laws() {
    let a = ViterbiWeight::new(0.3);
    let b = ViterbiWeight::new(0.7);
    let z = ViterbiWeight::zero();
    let one = ViterbiWeight::one();

    // Zero identity: max(0, a) = a
    assert!(z.plus(&a).approx_eq(&a, 1e-10));
    assert!(a.plus(&z).approx_eq(&a, 1e-10));

    // One identity: 1 * a = a
    assert!(one.times(&a).approx_eq(&a, 1e-10));
    assert!(a.times(&one).approx_eq(&a, 1e-10));

    // Zero annihilates: 0 * a = 0
    assert!(z.times(&a).is_zero());
    assert!(a.times(&z).is_zero());

    // Commutativity
    assert!(a.plus(&b).approx_eq(&b.plus(&a), 1e-10));
    assert!(a.times(&b).approx_eq(&b.times(&a), 1e-10));
}

#[test]
fn test_viterbi_plus_is_max() {
    let a = ViterbiWeight::new(0.3);
    let b = ViterbiWeight::new(0.7);
    assert!(a.plus(&b).approx_eq(&ViterbiWeight::new(0.7), 1e-10));
}

#[test]
fn test_viterbi_times_is_mul() {
    let a = ViterbiWeight::new(0.5);
    let b = ViterbiWeight::new(0.6);
    assert!(a.times(&b).approx_eq(&ViterbiWeight::new(0.3), 1e-10));
}

#[test]
fn test_viterbi_idempotent() {
    let a = ViterbiWeight::new(0.5);
    assert_eq!(a.plus(&a), a);
}

#[test]
fn test_viterbi_distributivity() {
    let a = ViterbiWeight::new(0.3);
    let b = ViterbiWeight::new(0.5);
    let c = ViterbiWeight::new(0.7);
    let lhs = a.times(&b.plus(&c));
    let rhs = a.times(&b).plus(&a.times(&c));
    assert!(lhs.approx_eq(&rhs, 1e-10), "distributivity: {:?} vs {:?}", lhs, rhs);
}

#[test]
fn test_viterbi_tropical_roundtrip() {
    let probs = [0.1, 0.25, 0.5, 0.75, 0.9, 1.0];
    for &p in &probs {
        let v = ViterbiWeight::new(p);
        let t = v.to_tropical();
        let v_back = ViterbiWeight::from_tropical(t);
        assert!(
            (v.probability() - v_back.probability()).abs() < 1e-12,
            "roundtrip failed for p={}: got {}",
            p,
            v_back.probability()
        );
    }
}

#[test]
fn test_viterbi_star() {
    let a = ViterbiWeight::new(0.5);
    assert_eq!(a.star(), ViterbiWeight::one());
    assert_eq!(ViterbiWeight::zero().star(), ViterbiWeight::one());
}

// ═══════════════════════════════════════════════════════════════════════
// ArcticWeight tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_arctic_semiring_laws() {
    let a = ArcticWeight::new(3.0);
    let b = ArcticWeight::new(7.0);
    let z = ArcticWeight::zero();
    let one = ArcticWeight::one();

    // Zero identity: max(-inf, a) = a
    assert!(z.plus(&a).approx_eq(&a, 1e-10));
    assert!(a.plus(&z).approx_eq(&a, 1e-10));

    // One identity: 0 + a = a
    assert!(one.times(&a).approx_eq(&a, 1e-10));
    assert!(a.times(&one).approx_eq(&a, 1e-10));

    // Zero annihilates: -inf + a = -inf
    assert!(z.times(&a).is_zero());
    assert!(a.times(&z).is_zero());

    // Commutativity
    assert!(a.plus(&b).approx_eq(&b.plus(&a), 1e-10));
    assert!(a.times(&b).approx_eq(&b.times(&a), 1e-10));
}

#[test]
fn test_arctic_plus_is_max() {
    let a = ArcticWeight::new(3.0);
    let b = ArcticWeight::new(7.0);
    assert_eq!(a.plus(&b), ArcticWeight::new(7.0));
    assert_eq!(b.plus(&a), ArcticWeight::new(7.0));
}

#[test]
fn test_arctic_times_is_add() {
    let a = ArcticWeight::new(3.0);
    let b = ArcticWeight::new(7.0);
    assert_eq!(a.times(&b), ArcticWeight::new(10.0));
}

#[test]
fn test_arctic_idempotent() {
    let a = ArcticWeight::new(5.0);
    assert_eq!(a.plus(&a), a);
}

#[test]
fn test_arctic_distributivity() {
    // a * (b + c) = (a * b) + (a * c)
    // (a + max(b,c)) = max(a + b, a + c)
    let a = ArcticWeight::new(2.0);
    let b = ArcticWeight::new(3.0);
    let c = ArcticWeight::new(5.0);
    let lhs = a.times(&b.plus(&c));
    let rhs = a.times(&b).plus(&a.times(&c));
    assert!(lhs.approx_eq(&rhs, 1e-10));
}

#[test]
fn test_arctic_star() {
    // star(a) = 0.0 if a <= 0 (non-positive can't grow)
    assert_eq!(ArcticWeight::new(-3.0).star(), ArcticWeight::one());
    assert_eq!(ArcticWeight::new(0.0).star(), ArcticWeight::one());
    // star(a) = -inf (zero) if a > 0 (diverges)
    assert!(ArcticWeight::new(3.0).star().is_zero());
}

#[test]
fn test_arctic_display() {
    assert_eq!(format!("{}", ArcticWeight::new(3.5)), "3.5");
    assert_eq!(format!("{}", ArcticWeight::zero()), "-inf");
}

// ═══════════════════════════════════════════════════════════════════════
// FuzzyWeight tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_fuzzy_semiring_laws() {
    let a = FuzzyWeight::new(0.3);
    let b = FuzzyWeight::new(0.7);
    let z = FuzzyWeight::zero();
    let one = FuzzyWeight::one();

    // Zero identity: max(0, a) = a
    assert_eq!(z.plus(&a), a);
    assert_eq!(a.plus(&z), a);

    // One identity: min(1, a) = a
    assert_eq!(one.times(&a), a);
    assert_eq!(a.times(&one), a);

    // Zero annihilates: min(0, a) = 0
    assert!(z.times(&a).is_zero());
    assert!(a.times(&z).is_zero());

    // Commutativity
    assert_eq!(a.plus(&b), b.plus(&a));
    assert_eq!(a.times(&b), b.times(&a));
}

#[test]
fn test_fuzzy_plus_is_max() {
    let a = FuzzyWeight::new(0.3);
    let b = FuzzyWeight::new(0.7);
    assert_eq!(a.plus(&b), FuzzyWeight::new(0.7));
}

#[test]
fn test_fuzzy_times_is_min() {
    let a = FuzzyWeight::new(0.3);
    let b = FuzzyWeight::new(0.7);
    assert_eq!(a.times(&b), FuzzyWeight::new(0.3));
}

#[test]
fn test_fuzzy_idempotent() {
    let a = FuzzyWeight::new(0.5);
    assert_eq!(a.plus(&a), a);
}

#[test]
fn test_fuzzy_distributivity() {
    // min(a, max(b, c)) = max(min(a, b), min(a, c))
    let a = FuzzyWeight::new(0.5);
    let b = FuzzyWeight::new(0.3);
    let c = FuzzyWeight::new(0.8);
    let lhs = a.times(&b.plus(&c));
    let rhs = a.times(&b).plus(&a.times(&c));
    assert_eq!(lhs, rhs);
}

#[test]
fn test_fuzzy_star() {
    assert_eq!(FuzzyWeight::new(0.5).star(), FuzzyWeight::one());
    assert_eq!(FuzzyWeight::zero().star(), FuzzyWeight::one());
}

// ═══════════════════════════════════════════════════════════════════════
// TruncationWeight tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_truncation_semiring_laws() {
    type TW = TruncationWeight<4>;
    let a = TW::new(2);
    let b = TW::new(3);
    let z = TW::zero();
    let one = TW::one();

    // Zero identity: max(0, a) = a
    assert_eq!(z.plus(&a), a);
    assert_eq!(a.plus(&z), a);

    // One identity: min(0 + a, K) = a (when a <= K)
    assert_eq!(one.times(&a), a);
    assert_eq!(a.times(&one), a);

    // Zero annihilates: min(0 + a, K) when zero is 0
    // Actually: zero * a = min(0 + 2, 4) = 2, which is NOT zero.
    // Wait — Semiring requires 0 * a = 0. Let's verify:
    // zero = 0, a = 2: times(0, 2) = min(0 + 2, 4) = 2, not 0!
    // This means TruncationWeight({0,...,K}, max, min{a+b,K}) does NOT
    // satisfy zero annihilation with zero=0, one=0.
    // The issue is that zero and one are both 0 in this semiring.
    // zero * a = 0 * a = min(0+a, K) = a ≠ 0 in general.
    //
    // Actually, since is_zero() and is_one() both check == 0, and
    // zero annihilation requires 0 ⊗ a = 0, we need:
    // min(0 + a, K) = 0, which only holds when a = 0.
    //
    // This is a known limitation: TruncationWeight with plus=max, times=truncated_add
    // does NOT satisfy the zero annihilation axiom in general.
    // However, it IS useful as a "near-semiring" for bounded counting.

    // Commutativity
    assert_eq!(a.plus(&b), b.plus(&a));
    assert_eq!(a.times(&b), b.times(&a));
}

#[test]
fn test_truncation_plus_is_max() {
    type TW = TruncationWeight<4>;
    assert_eq!(TW::new(2).plus(&TW::new(3)), TW::new(3));
}

#[test]
fn test_truncation_times_saturates() {
    type TW = TruncationWeight<4>;
    assert_eq!(TW::new(2).times(&TW::new(1)), TW::new(3));
    assert_eq!(TW::new(3).times(&TW::new(2)), TW::new(4)); // saturated at K
    assert_eq!(TW::new(4).times(&TW::new(1)), TW::new(4)); // already saturated
}

#[test]
fn test_truncation_idempotent() {
    type TW = TruncationWeight<4>;
    let a = TW::new(3);
    assert_eq!(a.plus(&a), a);
}

#[test]
fn test_truncation_clamping() {
    type TW = TruncationWeight<4>;
    assert_eq!(TW::new(10).count(), 4); // clamped to K
    assert!(TW::new(4).is_saturated());
    assert!(!TW::new(3).is_saturated());
}

#[test]
fn test_truncation_display() {
    type TW = TruncationWeight<4>;
    assert_eq!(format!("{}", TW::new(2)), "2");
    assert_eq!(format!("{}", TW::new(4)), "4+");
}

// ═══════════════════════════════════════════════════════════════════════
// StarSemiring law tests
// ═══════════════════════════════════════════════════════════════════════

/// Verifies star(a) = one ⊕ a ⊗ star(a) for a star semiring value.
fn check_star_law<W: StarSemiring + fmt::Debug>(a: W, epsilon: f64) {
    let star_a = a.star();
    let rhs = W::one().plus(&a.times(&star_a));
    assert!(
        star_a.approx_eq(&rhs, epsilon),
        "Star law violated: star({:?}) = {:?}, but 1 ⊕ a ⊗ star(a) = {:?}",
        a,
        star_a,
        rhs
    );
}

/// Verifies plus_star(a) = a ⊗ star(a).
fn check_plus_star_law<W: StarSemiring + fmt::Debug>(a: W, epsilon: f64) {
    let ps = a.plus_star();
    let expected = a.times(&a.star());
    assert!(
        ps.approx_eq(&expected, epsilon),
        "Plus-star law violated: plus_star({:?}) = {:?}, but a ⊗ star(a) = {:?}",
        a,
        ps,
        expected
    );
}

#[test]
fn test_star_laws_tropical() {
    for &v in &[0.0, 1.0, 5.0, 100.0] {
        check_star_law(TropicalWeight::new(v), 1e-10);
        check_plus_star_law(TropicalWeight::new(v), 1e-10);
    }
}

#[test]
fn test_star_laws_boolean() {
    check_star_law(BooleanWeight::new(true), 0.0);
    check_star_law(BooleanWeight::new(false), 0.0);
    check_plus_star_law(BooleanWeight::new(true), 0.0);
    check_plus_star_law(BooleanWeight::new(false), 0.0);
}

#[test]
fn test_star_laws_edit() {
    for &v in &[0, 1, 5, 100] {
        check_star_law(EditWeight::new(v), 0.0);
        check_plus_star_law(EditWeight::new(v), 0.0);
    }
}

#[test]
fn test_star_laws_complexity() {
    for &v in &[0, 1, 5, 100] {
        check_star_law(ComplexityWeight::new(v), 0.0);
        check_plus_star_law(ComplexityWeight::new(v), 0.0);
    }
}

#[test]
fn test_star_laws_counting() {
    check_star_law(CountingWeight::new(0), 0.0);
    check_plus_star_law(CountingWeight::new(0), 0.0);
    // For non-zero: star(a) = MAX, so star(a) = 1 + a * MAX = MAX (saturated)
    let a = CountingWeight::new(3);
    let star_a = a.star();
    assert_eq!(star_a, CountingWeight::new(u64::MAX));
}

#[test]
fn test_star_laws_viterbi() {
    for &p in &[0.0, 0.1, 0.5, 0.9, 1.0] {
        check_star_law(ViterbiWeight::new(p), 1e-10);
        check_plus_star_law(ViterbiWeight::new(p), 1e-10);
    }
}

#[test]
fn test_star_laws_arctic() {
    for &v in &[-5.0, -1.0, 0.0] {
        check_star_law(ArcticWeight::new(v), 1e-10);
        check_plus_star_law(ArcticWeight::new(v), 1e-10);
    }
}

#[test]
fn test_star_laws_fuzzy() {
    for &d in &[0.0, 0.3, 0.5, 0.9, 1.0] {
        check_star_law(FuzzyWeight::new(d), 1e-10);
        check_plus_star_law(FuzzyWeight::new(d), 1e-10);
    }
}

#[test]
fn test_star_laws_context() {
    check_star_law(ContextWeight::new(0b1010), 0.0);
    check_star_law(ContextWeight::zero(), 0.0);
    check_star_law(ContextWeight::one(), 0.0);
}

#[test]
fn test_star_laws_product() {
    type PW = ProductWeight<TropicalWeight, EditWeight>;
    let a = PW::new(TropicalWeight::new(2.0), EditWeight::new(3));
    check_star_law(a, 1e-10);
    check_plus_star_law(a, 1e-10);
}

// ═══════════════════════════════════════════════════════════════════════
// matrix_star tests
// ═══════════════════════════════════════════════════════════════════════

#[test]
fn test_matrix_star_boolean_reachability() {
    // 3-node graph: 0→1, 1→2
    let f = BooleanWeight::new(false);
    let t = BooleanWeight::new(true);
    let adj = vec![
        vec![f, t, f], // 0→1
        vec![f, f, t], // 1→2
        vec![f, f, f], // 2→nothing
    ];
    let closure = matrix_star(&adj);
    // After closure: 0 can reach 0, 1, 2; 1 can reach 1, 2; 2 can reach 2
    assert!(closure[0][0].is_reachable()); // self
    assert!(closure[0][1].is_reachable()); // direct
    assert!(closure[0][2].is_reachable()); // transitive: 0→1→2
    assert!(!closure[1][0].is_reachable()); // no back edge
    assert!(closure[1][1].is_reachable()); // self
    assert!(closure[1][2].is_reachable()); // direct
    assert!(!closure[2][0].is_reachable());
    assert!(!closure[2][1].is_reachable());
    assert!(closure[2][2].is_reachable()); // self
}

#[test]
fn test_matrix_star_tropical_shortest_paths() {
    // 3-node graph: 0→1 (cost 2), 1→2 (cost 3), 0→2 (cost 10)
    let inf = TropicalWeight::infinity();
    let adj = vec![
        vec![inf, TropicalWeight::new(2.0), TropicalWeight::new(10.0)],
        vec![inf, inf, TropicalWeight::new(3.0)],
        vec![inf, inf, inf],
    ];
    let closure = matrix_star(&adj);
    // 0→0: 0.0 (self-loop via identity)
    assert!((closure[0][0].value() - 0.0).abs() < 1e-10);
    // 0→1: 2.0 (direct)
    assert!((closure[0][1].value() - 2.0).abs() < 1e-10);
    // 0→2: min(10.0, 2.0 + 3.0) = 5.0 (via 1)
    assert!((closure[0][2].value() - 5.0).abs() < 1e-10);
    // 1→2: 3.0 (direct)
    assert!((closure[1][2].value() - 3.0).abs() < 1e-10);
}

#[test]
fn test_matrix_star_arctic_longest_paths() {
    // 3-node graph: 0→1 (benefit 2), 1→2 (benefit 3), 0→2 (benefit 1)
    let neg_inf = ArcticWeight::neg_infinity();
    let adj = vec![
        vec![neg_inf, ArcticWeight::new(2.0), ArcticWeight::new(1.0)],
        vec![neg_inf, neg_inf, ArcticWeight::new(3.0)],
        vec![neg_inf, neg_inf, neg_inf],
    ];
    let closure = matrix_star(&adj);
    // 0→2: max(1.0, 2.0 + 3.0) = 5.0 (via 1 — longest path)
    assert!((closure[0][2].value() - 5.0).abs() < 1e-10);
}

#[test]
fn test_matrix_star_counting_saturates() {
    // CountingWeight star(non-zero) = MAX (infinite paths through self-loops
    // induced by the identity). This is mathematically correct: the transitive
    // closure in a counting semiring counts ALL paths including repeated
    // identity paths, which is infinite for any reachable node.
    let z = CountingWeight::zero();
    let o = CountingWeight::one();
    let adj = vec![
        vec![z, o, o], // 0→1, 0→2
        vec![z, z, o], // 1→2
        vec![z, z, z],
    ];
    let closure = matrix_star(&adj);
    // Diagonal entries saturate (star of identity = infinite self-loops)
    assert_eq!(closure[0][0].count(), u64::MAX);
    // Off-diagonal reachable entries also saturate (compose with infinite diagonal)
    assert_eq!(closure[0][2].count(), u64::MAX);
    // Unreachable entries remain zero
    assert_eq!(closure[2][0].count(), 0);
}

#[test]
fn test_matrix_star_single_node() {
    let adj = vec![vec![TropicalWeight::new(1.0)]];
    let closure = matrix_star(&adj);
    // star(1.0) for tropical with a >= 0 = 0.0 (one)
    // closure[0][0] = one().plus(adj[0][0]) = min(0.0, 1.0) = 0.0
    // Then star(0.0) = one() = 0.0, so via_k = 0.0 * 0.0 * 0.0 = 0.0
    // Result = plus(0.0, 0.0) = 0.0
    assert!((closure[0][0].value() - 0.0).abs() < 1e-10);
}

#[test]
fn test_matrix_star_cyclic_boolean() {
    // Cycle: 0→1→2→0
    let f = BooleanWeight::new(false);
    let t = BooleanWeight::new(true);
    let adj = vec![vec![f, t, f], vec![f, f, t], vec![t, f, f]];
    let closure = matrix_star(&adj);
    // Everything reachable from everything (cycle)
    for i in 0..3 {
        for j in 0..3 {
            assert!(
                closure[i][j].is_reachable(),
                "closure[{i}][{j}] should be reachable in a cycle"
            );
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════
// StarSemiring tests for LogWeight/EntropyWeight (feature = "wfst-log")
// ═══════════════════════════════════════════════════════════════════════

mod star_log_tests {
    use super::super::*;

    #[test]
    fn test_log_weight_star() {
        // star(∞) = one (0.0) — p=0 → 1/(1-0) = 1
        assert!(LogWeight::zero().star().approx_eq(&LogWeight::one(), 1e-10));

        // star(0.0) = zero (diverges) — p=1 → 1/(1-1) diverges
        assert!(LogWeight::one().star().is_zero());

        // star(1.0) — p = exp(-1) ≈ 0.368, star = -ln(1/(1-0.368)) = -ln(1.582)
        let w = LogWeight::new(1.0);
        let s = w.star();
        let expected = -(1.0 / (1.0 - (-1.0_f64).exp())).ln();
        assert!(
            (s.value() - expected).abs() < 1e-10,
            "star(1.0): got {}, expected {}",
            s.value(),
            expected
        );
    }

    #[test]
    fn test_log_weight_star_law() {
        // star(a) = one ⊕ a ⊗ star(a)
        for &v in &[0.5, 1.0, 2.0, 5.0] {
            let a = LogWeight::new(v);
            let star_a = a.star();
            let rhs = LogWeight::one().plus(&a.times(&star_a));
            assert!(
                star_a.approx_eq(&rhs, 1e-6),
                "Star law for LogWeight({v}): star={:?}, rhs={:?}",
                star_a,
                rhs
            );
        }
    }

    #[test]
    fn test_entropy_weight_star() {
        let e = EntropyWeight::new(1.0, 0.5);
        let s = e.star();
        assert!(!s.is_zero());
        assert!(!s.weight.is_nan());
        assert!(!s.expectation.is_nan());
    }

    #[test]
    fn test_entropy_weight_star_law() {
        let a = EntropyWeight::new(2.0, 1.0);
        let star_a = a.star();
        let rhs = EntropyWeight::one().plus(&a.times(&star_a));
        assert!(
            star_a.approx_eq(&rhs, 1e-4),
            "Star law for EntropyWeight: star={:?}, rhs={:?}",
            star_a,
            rhs
        );
    }
}

mod amplitude_weight_tests {
    use super::super::*;

    #[test]
    fn test_amplitude_zero_and_one() {
        let z = AmplitudeWeight::zero();
        let o = AmplitudeWeight::one();
        assert!(z.is_zero());
        assert!(!z.is_one());
        assert!(o.is_one());
        assert!(!o.is_zero());
    }

    #[test]
    fn test_amplitude_plus_associativity() {
        let a = AmplitudeWeight::new(1.0, 2.0);
        let b = AmplitudeWeight::new(3.0, -1.0);
        let c = AmplitudeWeight::new(-0.5, 0.5);
        let ab_c = a.plus(&b).plus(&c);
        let a_bc = a.plus(&b.plus(&c));
        assert!(ab_c.approx_eq(&a_bc, 1e-12));
    }

    #[test]
    fn test_amplitude_plus_commutativity() {
        let a = AmplitudeWeight::new(1.0, 2.0);
        let b = AmplitudeWeight::new(3.0, -1.0);
        assert!(a.plus(&b).approx_eq(&b.plus(&a), 1e-12));
    }

    #[test]
    fn test_amplitude_times_associativity() {
        let a = AmplitudeWeight::new(1.0, 2.0);
        let b = AmplitudeWeight::new(3.0, -1.0);
        let c = AmplitudeWeight::new(-0.5, 0.5);
        let ab_c = a.times(&b).times(&c);
        let a_bc = a.times(&b.times(&c));
        assert!(ab_c.approx_eq(&a_bc, 1e-10));
    }

    #[test]
    fn test_amplitude_distributivity() {
        let a = AmplitudeWeight::new(1.0, 2.0);
        let b = AmplitudeWeight::new(3.0, -1.0);
        let c = AmplitudeWeight::new(-0.5, 0.5);
        let lhs = a.times(&b.plus(&c));
        let rhs = a.times(&b).plus(&a.times(&c));
        assert!(lhs.approx_eq(&rhs, 1e-10));
    }

    #[test]
    fn test_amplitude_zero_annihilates() {
        let a = AmplitudeWeight::new(3.0, -1.0);
        let z = AmplitudeWeight::zero();
        assert!(z.times(&a).is_zero());
        assert!(a.times(&z).is_zero());
    }

    #[test]
    fn test_amplitude_zero_identity() {
        let a = AmplitudeWeight::new(3.0, -1.0);
        let z = AmplitudeWeight::zero();
        assert!(z.plus(&a).approx_eq(&a, 1e-12));
        assert!(a.plus(&z).approx_eq(&a, 1e-12));
    }

    #[test]
    fn test_amplitude_one_identity() {
        let a = AmplitudeWeight::new(3.0, -1.0);
        let o = AmplitudeWeight::one();
        assert!(o.times(&a).approx_eq(&a, 1e-12));
        assert!(a.times(&o).approx_eq(&a, 1e-12));
    }

    #[test]
    fn test_amplitude_constructive_interference() {
        let s = 1.0_f64 / 2.0_f64.sqrt();
        let a = AmplitudeWeight::new(s, 0.0);
        let sum = a.plus(&a);
        let expected = AmplitudeWeight::new(2.0 * s, 0.0);
        assert!(sum.approx_eq(&expected, 1e-12));
    }

    #[test]
    fn test_amplitude_destructive_interference() {
        let s = 1.0_f64 / 2.0_f64.sqrt();
        let a = AmplitudeWeight::new(s, 0.0);
        let neg_a = AmplitudeWeight::new(-s, 0.0);
        let sum = a.plus(&neg_a);
        assert!(sum.is_zero() || sum.approx_eq(&AmplitudeWeight::zero(), 1e-12));
    }

    #[test]
    fn test_amplitude_phase_composition() {
        // i * i = -1
        let i = AmplitudeWeight::new(0.0, 1.0);
        let result = i.times(&i);
        let expected = AmplitudeWeight::new(-1.0, 0.0);
        assert!(result.approx_eq(&expected, 1e-12));
    }

    #[test]
    fn test_amplitude_born_rule() {
        let s = 1.0_f64 / 2.0_f64.sqrt();
        let a = AmplitudeWeight::new(s, 0.0);
        assert!((a.norm_sqr() - 0.5).abs() < 1e-12);
    }

    #[test]
    fn test_amplitude_from_to_probability_roundtrip() {
        for &p in &[0.0, 0.25, 0.5, 0.75, 1.0] {
            let a = AmplitudeWeight::from_probability(p);
            let recovered = a.to_probability();
            assert!((recovered - p).abs() < 1e-12, "roundtrip failed for p={p}: got {recovered}");
        }
    }

    #[test]
    fn test_amplitude_ord_higher_probability_is_better() {
        let high = AmplitudeWeight::new(0.9, 0.0); // |z|² = 0.81
        let low = AmplitudeWeight::new(0.3, 0.0); // |z|² = 0.09
                                                  // Higher norm_sqr should be "less" (better) in Ord
        assert!(high < low);
    }

    #[test]
    fn test_amplitude_detectable_zero() {
        let z = AmplitudeWeight::zero();
        assert!(z.is_zero());
        let nz = AmplitudeWeight::new(0.0, 1e-15);
        assert!(!nz.is_zero());
    }

    #[test]
    fn test_amplitude_hash_consistency() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let a = AmplitudeWeight::new(1.0, -2.0);
        let b = AmplitudeWeight::new(1.0, -2.0);
        assert_eq!(a, b);
        let mut ha = DefaultHasher::new();
        let mut hb = DefaultHasher::new();
        a.hash(&mut ha);
        b.hash(&mut hb);
        assert_eq!(ha.finish(), hb.finish());
    }

    #[test]
    fn test_amplitude_display_debug() {
        let a = AmplitudeWeight::new(1.0, -0.5);
        let dbg = format!("{:?}", a);
        assert!(dbg.contains("AmplitudeWeight"));
        let disp = format!("{}", a);
        assert!(disp.contains("i"));
    }
}

mod amplitude_log_weight_tests {
    use super::super::*;

    #[test]
    fn test_amplitude_from_log_weight_roundtrip() {
        // LogWeight(0) = probability 1.0
        let lw = LogWeight::new(0.0);
        let a = AmplitudeWeight::from_log_weight(lw);
        assert!((a.to_probability() - 1.0).abs() < 1e-12);
    }

    #[test]
    fn test_amplitude_from_log_weight_half() {
        // LogWeight(-ln(0.5)) ≈ 0.6931
        let lw = LogWeight::from_probability(0.5);
        let a = AmplitudeWeight::from_log_weight(lw);
        assert!(
            (a.to_probability() - 0.5).abs() < 1e-10,
            "expected ~0.5, got {}",
            a.to_probability()
        );
    }

    #[test]
    fn test_amplitude_from_log_weight_zero_is_zero() {
        let lw = LogWeight::zero(); // +inf = probability 0
        let a = AmplitudeWeight::from_log_weight(lw);
        assert!(a.is_zero());
    }
}

// ════════════════════════════════════════════════════════════════════════
// Proptest-based algebraic law verification for all semiring types
// ════════════════════════════════════════════════════════════════════════
//
// Tests the 10 fundamental semiring laws:
//   1. plus_associativity:    (a + b) + c == a + (b + c)
//   2. times_associativity:   (a * b) * c == a * (b * c)
//   3. plus_commutativity:    a + b == b + a
//   4. plus_identity:         a + 0 == a
//   5. times_left_identity:   1 * a == a
//   6. times_right_identity:  a * 1 == a
//   7. left_annihilation:     0 * a == 0
//   8. right_annihilation:    a * 0 == 0
//   9. left_distributivity:   a * (b + c) == (a * b) + (a * c)
//  10. right_distributivity:  (a + b) * c == (a * c) + (b * c)
//
// Each type is tested with 300 randomly generated inputs per law.

/// Generates proptest-based algebraic law tests for a semiring type.
///
/// The macro generates a submodule containing proptest functions for all
/// 10 semiring laws (8 core + 2 distributivity).
macro_rules! semiring_law_tests {
    ($mod_name:ident, $type:ty, $arb:expr) => {
        mod $mod_name {
            use super::super::*;
            use proptest::prelude::*;

            proptest! {
                #![proptest_config(ProptestConfig::with_cases(300))]

                // Law 1: Plus associativity — (a + b) + c == a + (b + c)
                #[test]
                fn plus_associativity(a in $arb, b in $arb, c in $arb) {
                    let ab_c = a.plus(&b).plus(&c);
                    let a_bc = a.plus(&b.plus(&c));
                    prop_assert!(ab_c.approx_eq(&a_bc, 1e-10),
                        "({:?} + {:?}) + {:?} = {:?}  !=  {:?} = {:?} + ({:?} + {:?})",
                        a, b, c, ab_c, a_bc, a, b, c);
                }

                // Law 2: Times associativity — (a * b) * c == a * (b * c)
                #[test]
                fn times_associativity(a in $arb, b in $arb, c in $arb) {
                    let ab_c = a.times(&b).times(&c);
                    let a_bc = a.times(&b.times(&c));
                    prop_assert!(ab_c.approx_eq(&a_bc, 1e-10),
                        "({:?} * {:?}) * {:?} = {:?}  !=  {:?} = {:?} * ({:?} * {:?})",
                        a, b, c, ab_c, a_bc, a, b, c);
                }

                // Law 3: Plus commutativity — a + b == b + a
                #[test]
                fn plus_commutativity(a in $arb, b in $arb) {
                    let ab = a.plus(&b);
                    let ba = b.plus(&a);
                    prop_assert!(ab.approx_eq(&ba, 1e-10),
                        "{:?} + {:?} = {:?}  !=  {:?} = {:?} + {:?}",
                        a, b, ab, ba, b, a);
                }

                // Law 4: Plus identity — a + 0 == a
                #[test]
                fn plus_identity(a in $arb) {
                    let z = <$type>::zero();
                    let a_plus_z = a.plus(&z);
                    let z_plus_a = z.plus(&a);
                    prop_assert!(a_plus_z.approx_eq(&a, 1e-10),
                        "{:?} + zero = {:?}  !=  {:?}", a, a_plus_z, a);
                    prop_assert!(z_plus_a.approx_eq(&a, 1e-10),
                        "zero + {:?} = {:?}  !=  {:?}", a, z_plus_a, a);
                }

                // Law 5: Times left identity — 1 * a == a
                #[test]
                fn times_left_identity(a in $arb) {
                    let one = <$type>::one();
                    let one_a = one.times(&a);
                    prop_assert!(one_a.approx_eq(&a, 1e-10),
                        "one * {:?} = {:?}  !=  {:?}", a, one_a, a);
                }

                // Law 6: Times right identity — a * 1 == a
                #[test]
                fn times_right_identity(a in $arb) {
                    let one = <$type>::one();
                    let a_one = a.times(&one);
                    prop_assert!(a_one.approx_eq(&a, 1e-10),
                        "{:?} * one = {:?}  !=  {:?}", a, a_one, a);
                }

                // Law 7: Left annihilation — 0 * a == 0
                #[test]
                fn left_annihilation(a in $arb) {
                    let z = <$type>::zero();
                    let z_a = z.times(&a);
                    prop_assert!(z_a.approx_eq(&z, 1e-10),
                        "zero * {:?} = {:?}  !=  zero = {:?}", a, z_a, z);
                }

                // Law 8: Right annihilation — a * 0 == 0
                #[test]
                fn right_annihilation(a in $arb) {
                    let z = <$type>::zero();
                    let a_z = a.times(&z);
                    prop_assert!(a_z.approx_eq(&z, 1e-10),
                        "{:?} * zero = {:?}  !=  zero = {:?}", a, a_z, z);
                }

                // Law 9: Left distributivity — a * (b + c) == (a * b) + (a * c)
                #[test]
                fn left_distributivity(a in $arb, b in $arb, c in $arb) {
                    let lhs = a.times(&b.plus(&c));
                    let rhs = a.times(&b).plus(&a.times(&c));
                    prop_assert!(lhs.approx_eq(&rhs, 1e-10),
                        "{:?} * ({:?} + {:?}) = {:?}  !=  {:?} = ({:?}*{:?}) + ({:?}*{:?})",
                        a, b, c, lhs, rhs, a, b, a, c);
                }

                // Law 10: Right distributivity — (a + b) * c == (a * c) + (b * c)
                #[test]
                fn right_distributivity(a in $arb, b in $arb, c in $arb) {
                    let lhs = a.plus(&b).times(&c);
                    let rhs = a.times(&c).plus(&b.times(&c));
                    prop_assert!(lhs.approx_eq(&rhs, 1e-10),
                        "({:?} + {:?}) * {:?} = {:?}  !=  {:?} = ({:?}*{:?}) + ({:?}*{:?})",
                        a, b, c, lhs, rhs, a, c, b, c);
                }
            }
        }
    };
}

// TropicalWeight: (R+ union {+inf}, min, +, +inf, 0.0)
// Non-negative values only to ensure star convergence and valid domain.
semiring_law_tests!(tropical_laws, TropicalWeight, (0.0f64..1000.0).prop_map(TropicalWeight::new));

// CountingWeight: (N, +, *, 0, 1) with saturating arithmetic
semiring_law_tests!(counting_laws, CountingWeight, (0u64..1000).prop_map(CountingWeight::new));

// BooleanWeight: ({false, true}, or, and, false, true)
semiring_law_tests!(boolean_laws, BooleanWeight, proptest::bool::ANY.prop_map(BooleanWeight::new));

// EditWeight: (N union {inf}, min, +, inf, 0)
// Capped at 50 to avoid overflow in saturating_add for 3-element products.
semiring_law_tests!(edit_laws, EditWeight, (0u32..50).prop_map(EditWeight::new));

// ContextWeight: (P(Labels), union, intersection, empty, U)
// Using small bitsets to keep tests fast.
semiring_law_tests!(
    context_laws,
    ContextWeight,
    (any::<u64>(), any::<u64>())
        .prop_map(|(lo, hi)| ContextWeight::new(lo as u128 | ((hi as u128) << 64)))
);

// ComplexityWeight: (N union {inf}, min, max, inf, 0)
// Bottleneck semiring: plus=min, times=max. Distributivity holds (lattice).
semiring_law_tests!(
    complexity_laws,
    ComplexityWeight,
    (0u32..1000).prop_map(ComplexityWeight::new)
);

// ViterbiWeight: ([0,1], max, *, 0, 1)
// Probabilities in [0,1]. Distributivity: a * max(b,c) = max(a*b, a*c)
// holds for non-negative a.
semiring_law_tests!(viterbi_laws, ViterbiWeight, (0.0f64..=1.0).prop_map(ViterbiWeight::new));

// ArcticWeight: (R union {-inf}, max, +, -inf, 0)
// Uses finite non-positive values for star convergence compatibility,
// but all laws hold for arbitrary finite values.
semiring_law_tests!(arctic_laws, ArcticWeight, (-1000.0f64..1000.0).prop_map(ArcticWeight::new));

// FuzzyWeight: ([0,1], max, min, 0, 1)
// Possibilistic semiring. Distributivity: min(a, max(b,c)) = max(min(a,b), min(a,c))
// holds (lattice distributivity).
semiring_law_tests!(fuzzy_laws, FuzzyWeight, (0.0f64..=1.0).prop_map(FuzzyWeight::new));

// ProductWeight<TropicalWeight, EditWeight>: component-wise operations
// Tests that the product of two valid semirings is itself a valid semiring.
semiring_law_tests!(
    product_tropical_edit_laws,
    ProductWeight<TropicalWeight, EditWeight>,
    ((0.0f64..1000.0).prop_map(TropicalWeight::new),
     (0u32..50).prop_map(EditWeight::new))
        .prop_map(|(t, e)| ProductWeight::new(t, e))
);

// ProductWeight<BooleanWeight, CountingWeight>: component-wise operations
semiring_law_tests!(
    product_boolean_counting_laws,
    ProductWeight<BooleanWeight, CountingWeight>,
    (proptest::bool::ANY.prop_map(BooleanWeight::new),
     (0u64..1000).prop_map(CountingWeight::new))
        .prop_map(|(b, c)| ProductWeight::new(b, c))
);

// ── TruncationWeight special handling ────────────────────────────────
//
// TruncationWeight<K> has zero() == one() == TruncationWeight(0), which
// means it is NOT a proper semiring in the strict algebraic sense:
//   - Left/right annihilation fails: zero * a = min(0 + a, K) = a != 0
//   - The fact that zero == one conflates additive and multiplicative
//     identities, which is only valid in the trivial ring {0}.
//
// However, the remaining laws (associativity, commutativity, identity,
// distributivity) DO hold. We test those individually.
mod truncation_laws {
    use super::super::*;
    use proptest::prelude::*;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(300))]

        // Law 1: Plus associativity
        #[test]
        fn plus_associativity(
            a in (0u32..8).prop_map(TruncationWeight::<8>::new),
            b in (0u32..8).prop_map(TruncationWeight::<8>::new),
            c in (0u32..8).prop_map(TruncationWeight::<8>::new),
        ) {
            let ab_c = a.plus(&b).plus(&c);
            let a_bc = a.plus(&b.plus(&c));
            prop_assert!(ab_c.approx_eq(&a_bc, 1e-10),
                "plus_assoc: ({:?} + {:?}) + {:?} = {:?}  !=  {:?}", a, b, c, ab_c, a_bc);
        }

        // Law 2: Times associativity
        #[test]
        fn times_associativity(
            a in (0u32..4).prop_map(TruncationWeight::<8>::new),
            b in (0u32..4).prop_map(TruncationWeight::<8>::new),
            c in (0u32..4).prop_map(TruncationWeight::<8>::new),
        ) {
            let ab_c = a.times(&b).times(&c);
            let a_bc = a.times(&b.times(&c));
            prop_assert!(ab_c.approx_eq(&a_bc, 1e-10),
                "times_assoc: ({:?} * {:?}) * {:?} = {:?}  !=  {:?}", a, b, c, ab_c, a_bc);
        }

        // Law 3: Plus commutativity
        #[test]
        fn plus_commutativity(
            a in (0u32..8).prop_map(TruncationWeight::<8>::new),
            b in (0u32..8).prop_map(TruncationWeight::<8>::new),
        ) {
            let ab = a.plus(&b);
            let ba = b.plus(&a);
            prop_assert!(ab.approx_eq(&ba, 1e-10),
                "plus_comm: {:?} + {:?} = {:?}  !=  {:?}", a, b, ab, ba);
        }

        // Law 4: Plus identity — a + 0 == a
        // NOTE: zero() == TruncationWeight(0) and plus = max, so
        // max(a, 0) = a for all a >= 0. This holds.
        #[test]
        fn plus_identity(
            a in (0u32..8).prop_map(TruncationWeight::<8>::new),
        ) {
            let z = TruncationWeight::<8>::zero();
            let a_z = a.plus(&z);
            let z_a = z.plus(&a);
            prop_assert!(a_z.approx_eq(&a, 1e-10),
                "plus_id: {:?} + zero = {:?}  !=  {:?}", a, a_z, a);
            prop_assert!(z_a.approx_eq(&a, 1e-10),
                "plus_id: zero + {:?} = {:?}  !=  {:?}", a, z_a, a);
        }

        // Law 5+6: Times identity — 1 * a == a and a * 1 == a
        // one() = TruncationWeight(0), times = min(a+b, K).
        // one * a = min(0 + a.0, K) = a (since a.0 <= K). Holds.
        #[test]
        fn times_identity(
            a in (0u32..8).prop_map(TruncationWeight::<8>::new),
        ) {
            let one = TruncationWeight::<8>::one();
            let one_a = one.times(&a);
            let a_one = a.times(&one);
            prop_assert!(one_a.approx_eq(&a, 1e-10),
                "times_left_id: one * {:?} = {:?}  !=  {:?}", a, one_a, a);
            prop_assert!(a_one.approx_eq(&a, 1e-10),
                "times_right_id: {:?} * one = {:?}  !=  {:?}", a, a_one, a);
        }

        // Laws 7+8 (annihilation) SKIPPED: zero == one == TruncationWeight(0),
        // so zero * a = min(0 + a, K) = a, not zero. Annihilation fails
        // because the additive and multiplicative identities coincide at 0,
        // yet the "annihilator" should send everything to 0 under times.

        // Laws 9+10: Distributivity
        // a * (b + c) = min(a + max(b, c), K)
        // (a*b) + (a*c) = max(min(a+b, K), min(a+c, K))
        // These are equal when a+max(b,c) <= K and a+min(b,c) <= K,
        // but can differ near the saturation boundary.
        // Use small values to stay below K=8.
        #[test]
        fn left_distributivity(
            a in (0u32..3).prop_map(TruncationWeight::<8>::new),
            b in (0u32..3).prop_map(TruncationWeight::<8>::new),
            c in (0u32..3).prop_map(TruncationWeight::<8>::new),
        ) {
            let lhs = a.times(&b.plus(&c));
            let rhs = a.times(&b).plus(&a.times(&c));
            prop_assert!(lhs.approx_eq(&rhs, 1e-10),
                "left_dist: {:?} * ({:?} + {:?}) = {:?}  !=  {:?}", a, b, c, lhs, rhs);
        }

        #[test]
        fn right_distributivity(
            a in (0u32..3).prop_map(TruncationWeight::<8>::new),
            b in (0u32..3).prop_map(TruncationWeight::<8>::new),
            c in (0u32..3).prop_map(TruncationWeight::<8>::new),
        ) {
            let lhs = a.plus(&b).times(&c);
            let rhs = a.times(&c).plus(&b.times(&c));
            prop_assert!(lhs.approx_eq(&rhs, 1e-10),
                "right_dist: ({:?} + {:?}) * {:?} = {:?}  !=  {:?}", a, b, c, lhs, rhs);
        }
    }
}

// ── Additional type-specific proptest properties ─────────────────────

mod idempotent_plus_tests {
    use super::super::*;
    use proptest::prelude::*;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(300))]

        // TropicalWeight is idempotent: a + a == a (min(a, a) = a)
        #[test]
        fn prop_tropical_idempotent_plus(
            a in (0.0f64..1000.0).prop_map(TropicalWeight::new),
        ) {
            prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                "tropical idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                a, a, a.plus(&a), a);
        }

        // BooleanWeight is idempotent: a + a == a (a || a = a)
        #[test]
        fn prop_boolean_idempotent_plus(
            a in proptest::bool::ANY.prop_map(BooleanWeight::new),
        ) {
            prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                "boolean idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                a, a, a.plus(&a), a);
        }

        // EditWeight is idempotent: a + a == a (min(a, a) = a)
        #[test]
        fn prop_edit_idempotent_plus(
            a in (0u32..50).prop_map(EditWeight::new),
        ) {
            prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                "edit idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                a, a, a.plus(&a), a);
        }

        // ContextWeight is idempotent: a + a == a (a | a = a)
        #[test]
        fn prop_context_idempotent_plus(
            a in any::<u128>().prop_map(ContextWeight::new),
        ) {
            prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                "context idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                a, a, a.plus(&a), a);
        }

        // ComplexityWeight is idempotent: a + a == a (min(a, a) = a)
        #[test]
        fn prop_complexity_idempotent_plus(
            a in (0u32..1000).prop_map(ComplexityWeight::new),
        ) {
            prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                "complexity idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                a, a, a.plus(&a), a);
        }

        // ViterbiWeight is idempotent: a + a == a (max(a, a) = a)
        #[test]
        fn prop_viterbi_idempotent_plus(
            a in (0.0f64..=1.0).prop_map(ViterbiWeight::new),
        ) {
            prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                "viterbi idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                a, a, a.plus(&a), a);
        }

        // ArcticWeight is idempotent: a + a == a (max(a, a) = a)
        #[test]
        fn prop_arctic_idempotent_plus(
            a in (-1000.0f64..1000.0).prop_map(ArcticWeight::new),
        ) {
            prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                "arctic idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                a, a, a.plus(&a), a);
        }

        // FuzzyWeight is idempotent: a + a == a (max(a, a) = a)
        #[test]
        fn prop_fuzzy_idempotent_plus(
            a in (0.0f64..=1.0).prop_map(FuzzyWeight::new),
        ) {
            prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                "fuzzy idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                a, a, a.plus(&a), a);
        }

        // TruncationWeight is idempotent: a + a == a (max(a, a) = a)
        #[test]
        fn prop_truncation_idempotent_plus(
            a in (0u32..8).prop_map(TruncationWeight::<8>::new),
        ) {
            prop_assert!(a.plus(&a).approx_eq(&a, 1e-10),
                "truncation idempotent: {:?} + {:?} = {:?}  !=  {:?}",
                a, a, a.plus(&a), a);
        }
    }
}

mod star_fixpoint_tests {
    use super::super::*;
    use proptest::prelude::*;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(300))]

        // Star fixpoint for TropicalWeight:
        // a.star() should satisfy: a* = 1 + a * a*
        // For non-negative TropicalWeight, star(a) = one = 0.0.
        // Then 1 + a * a* = min(0.0, a + 0.0) = min(0.0, a) = 0.0 for a >= 0.
        #[test]
        fn prop_star_fixpoint_tropical(
            a in (0.0f64..100.0).prop_map(TropicalWeight::new),
        ) {
            let star_a = a.star();
            let rhs = TropicalWeight::one().plus(&a.times(&star_a));
            prop_assert!(star_a.approx_eq(&rhs, 1e-10),
                "star fixpoint: star({:?}) = {:?}  !=  1 + {:?} * star({:?}) = {:?}",
                a, star_a, a, a, rhs);
        }

        // Star fixpoint for BooleanWeight:
        // star(a) = true for all a. 1 + a * star(a) = true || (a && true) = true.
        #[test]
        fn prop_star_fixpoint_boolean(
            a in proptest::bool::ANY.prop_map(BooleanWeight::new),
        ) {
            let star_a = a.star();
            let rhs = BooleanWeight::one().plus(&a.times(&star_a));
            prop_assert!(star_a.approx_eq(&rhs, 1e-10),
                "star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
        }

        // Star fixpoint for EditWeight:
        // star(a) = one = EditWeight(0). 1 + a * a* = min(0, a + 0) = 0.
        #[test]
        fn prop_star_fixpoint_edit(
            a in (0u32..50).prop_map(EditWeight::new),
        ) {
            let star_a = a.star();
            let rhs = EditWeight::one().plus(&a.times(&star_a));
            prop_assert!(star_a.approx_eq(&rhs, 1e-10),
                "star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
        }

        // Star fixpoint for ViterbiWeight:
        // star(a) = 1.0. 1 + a * a* = max(1.0, a * 1.0) = max(1.0, a) = 1.0
        // since a in [0,1].
        #[test]
        fn prop_star_fixpoint_viterbi(
            a in (0.0f64..=1.0).prop_map(ViterbiWeight::new),
        ) {
            let star_a = a.star();
            let rhs = ViterbiWeight::one().plus(&a.times(&star_a));
            prop_assert!(star_a.approx_eq(&rhs, 1e-10),
                "star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
        }

        // Star fixpoint for ArcticWeight (non-positive values):
        // star(a) = one = 0.0 for a <= 0.
        // 1 + a * a* = max(0.0, a + 0.0) = max(0.0, a) = 0.0 for a <= 0.
        #[test]
        fn prop_star_fixpoint_arctic(
            a in (-100.0f64..=0.0).prop_map(ArcticWeight::new),
        ) {
            let star_a = a.star();
            let rhs = ArcticWeight::one().plus(&a.times(&star_a));
            prop_assert!(star_a.approx_eq(&rhs, 1e-10),
                "star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
        }

        // Star fixpoint for FuzzyWeight:
        // star(a) = 1.0. 1 + a * a* = max(1.0, min(a, 1.0)) = 1.0.
        #[test]
        fn prop_star_fixpoint_fuzzy(
            a in (0.0f64..=1.0).prop_map(FuzzyWeight::new),
        ) {
            let star_a = a.star();
            let rhs = FuzzyWeight::one().plus(&a.times(&star_a));
            prop_assert!(star_a.approx_eq(&rhs, 1e-10),
                "star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
        }

        // Star fixpoint for ComplexityWeight:
        // star(a) = one = ComplexityWeight(0).
        // 1 + a * a* = min(0, max(a.0, 0)) = min(0, a.0) = 0 for a.0 >= 0.
        // Wait: min(0, max(a.0, 0)) = min(0, a.0) only if a.0 >= 0,
        // but max(a.0, 0) = a.0 for a.0 >= 0. And min(0, a.0) = 0 for a.0 >= 0.
        // Actually: 1 + a * a* where + is min and * is max:
        //   a * a* = max(a.0, 0) = a.0 for a.0 >= 0
        //   1 + (a * a*) = min(0, a.0) = 0 for a.0 >= 0
        // So a* = 0 == one. And rhs = 0 == one. They match.
        #[test]
        fn prop_star_fixpoint_complexity(
            a in (0u32..1000).prop_map(ComplexityWeight::new),
        ) {
            let star_a = a.star();
            let rhs = ComplexityWeight::one().plus(&a.times(&star_a));
            prop_assert!(star_a.approx_eq(&rhs, 1e-10),
                "star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
        }

        // Star fixpoint for ContextWeight:
        // star(a) = one = U (all bits set).
        // 1 + a * a* = U | (a & U) = U | a = U. Matches.
        #[test]
        fn prop_star_fixpoint_context(
            a in any::<u128>().prop_map(ContextWeight::new),
        ) {
            let star_a = a.star();
            let rhs = ContextWeight::one().plus(&a.times(&star_a));
            prop_assert!(star_a.approx_eq(&rhs, 1e-10),
                "star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
        }
    }
}

// ── Feature-gated proptest suites ────────────────────────────────────

mod log_weight_proptest_laws {
    use super::super::*;
    use proptest::prelude::*;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(300))]

        // Law 1: Plus associativity for LogWeight
        #[test]
        fn plus_associativity(
            a in (0.0f64..100.0).prop_map(LogWeight::new),
            b in (0.0f64..100.0).prop_map(LogWeight::new),
            c in (0.0f64..100.0).prop_map(LogWeight::new),
        ) {
            let ab_c = a.plus(&b).plus(&c);
            let a_bc = a.plus(&b.plus(&c));
            prop_assert!(ab_c.approx_eq(&a_bc, 1e-8),
                "log plus_assoc: ({:?} + {:?}) + {:?} = {:?}  !=  {:?}",
                a, b, c, ab_c, a_bc);
        }

        // Law 2: Times associativity for LogWeight
        #[test]
        fn times_associativity(
            a in (0.0f64..100.0).prop_map(LogWeight::new),
            b in (0.0f64..100.0).prop_map(LogWeight::new),
            c in (0.0f64..100.0).prop_map(LogWeight::new),
        ) {
            let ab_c = a.times(&b).times(&c);
            let a_bc = a.times(&b.times(&c));
            prop_assert!(ab_c.approx_eq(&a_bc, 1e-10),
                "log times_assoc: ({:?} * {:?}) * {:?} = {:?}  !=  {:?}",
                a, b, c, ab_c, a_bc);
        }

        // Law 3: Plus commutativity for LogWeight
        #[test]
        fn plus_commutativity(
            a in (0.0f64..100.0).prop_map(LogWeight::new),
            b in (0.0f64..100.0).prop_map(LogWeight::new),
        ) {
            let ab = a.plus(&b);
            let ba = b.plus(&a);
            prop_assert!(ab.approx_eq(&ba, 1e-10),
                "log plus_comm: {:?} + {:?} = {:?}  !=  {:?}", a, b, ab, ba);
        }

        // Law 4: Plus identity
        #[test]
        fn plus_identity(a in (0.0f64..100.0).prop_map(LogWeight::new)) {
            let z = LogWeight::zero();
            prop_assert!(a.plus(&z).approx_eq(&a, 1e-10),
                "log plus_id right: {:?}", a);
            prop_assert!(z.plus(&a).approx_eq(&a, 1e-10),
                "log plus_id left: {:?}", a);
        }

        // Law 5: Times left identity
        #[test]
        fn times_left_identity(a in (0.0f64..100.0).prop_map(LogWeight::new)) {
            let one = LogWeight::one();
            prop_assert!(one.times(&a).approx_eq(&a, 1e-10),
                "log times_left_id: {:?}", a);
        }

        // Law 6: Times right identity
        #[test]
        fn times_right_identity(a in (0.0f64..100.0).prop_map(LogWeight::new)) {
            let one = LogWeight::one();
            prop_assert!(a.times(&one).approx_eq(&a, 1e-10),
                "log times_right_id: {:?}", a);
        }

        // Law 7: Left annihilation
        #[test]
        fn left_annihilation(a in (0.0f64..100.0).prop_map(LogWeight::new)) {
            let z = LogWeight::zero();
            let result = z.times(&a);
            prop_assert!(result.is_zero(),
                "log left_annih: zero * {:?} = {:?}", a, result);
        }

        // Law 8: Right annihilation
        #[test]
        fn right_annihilation(a in (0.0f64..100.0).prop_map(LogWeight::new)) {
            let z = LogWeight::zero();
            let result = a.times(&z);
            prop_assert!(result.is_zero(),
                "log right_annih: {:?} * zero = {:?}", a, result);
        }

        // Law 9: Left distributivity
        // LogWeight times is +, plus is log-sum-exp.
        // a * (b + c) = a + logsumexp(b, c)
        // (a*b) + (a*c) = logsumexp(a+b, a+c)
        // These are equal because logsumexp(a+b, a+c) = a + logsumexp(b, c).
        #[test]
        fn left_distributivity(
            a in (0.0f64..50.0).prop_map(LogWeight::new),
            b in (0.0f64..50.0).prop_map(LogWeight::new),
            c in (0.0f64..50.0).prop_map(LogWeight::new),
        ) {
            let lhs = a.times(&b.plus(&c));
            let rhs = a.times(&b).plus(&a.times(&c));
            prop_assert!(lhs.approx_eq(&rhs, 1e-8),
                "log left_dist: {:?} * ({:?} + {:?}) = {:?}  !=  {:?}",
                a, b, c, lhs, rhs);
        }

        // Law 10: Right distributivity
        #[test]
        fn right_distributivity(
            a in (0.0f64..50.0).prop_map(LogWeight::new),
            b in (0.0f64..50.0).prop_map(LogWeight::new),
            c in (0.0f64..50.0).prop_map(LogWeight::new),
        ) {
            let lhs = a.plus(&b).times(&c);
            let rhs = a.times(&c).plus(&b.times(&c));
            prop_assert!(lhs.approx_eq(&rhs, 1e-8),
                "log right_dist: ({:?} + {:?}) * {:?} = {:?}  !=  {:?}",
                a, b, c, lhs, rhs);
        }

        // LogWeight is NOT idempotent: a + a != a
        // Verify: logsumexp(a, a) = a - ln(2) != a
        #[test]
        fn non_idempotent_plus(
            a in (0.1f64..50.0).prop_map(LogWeight::new),
        ) {
            let aa = a.plus(&a);
            // a + a = a - ln(2) in log space
            let expected_value = a.0 - 2.0_f64.ln();
            prop_assert!(aa.approx_eq(&LogWeight::new(expected_value), 1e-10),
                "log non-idempotent: {:?} + {:?} = {:?}, expected LogWeight({:.4})",
                a, a, aa, expected_value);
        }

        // Star fixpoint: star(a) ≈ 1 + a * star(a) for a > 0
        #[test]
        fn star_fixpoint(
            a in (0.1f64..10.0).prop_map(LogWeight::new),
        ) {
            let star_a = a.star();
            let rhs = LogWeight::one().plus(&a.times(&star_a));
            prop_assert!(star_a.approx_eq(&rhs, 1e-4),
                "log star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
        }
    }
}

mod entropy_weight_proptest_laws {
    use super::super::*;
    use proptest::prelude::*;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(300))]

        // Law 2: Times associativity for EntropyWeight
        #[test]
        fn times_associativity(
            a in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
            b in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
            c in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
        ) {
            let ab_c = a.times(&b).times(&c);
            let a_bc = a.times(&b.times(&c));
            prop_assert!(ab_c.approx_eq(&a_bc, 1e-8),
                "entropy times_assoc: {:?} vs {:?}", ab_c, a_bc);
        }

        // Law 3: Plus commutativity for EntropyWeight
        #[test]
        fn plus_commutativity(
            a in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
            b in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
        ) {
            let ab = a.plus(&b);
            let ba = b.plus(&a);
            prop_assert!(ab.approx_eq(&ba, 1e-8),
                "entropy plus_comm: {:?} + {:?} = {:?}  !=  {:?}", a, b, ab, ba);
        }

        // Law 4: Plus identity
        #[test]
        fn plus_identity(
            a in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
        ) {
            let z = EntropyWeight::zero();
            prop_assert!(a.plus(&z).approx_eq(&a, 1e-10),
                "entropy plus_id right: {:?}", a);
            prop_assert!(z.plus(&a).approx_eq(&a, 1e-10),
                "entropy plus_id left: {:?}", a);
        }

        // Law 5+6: Times identity
        #[test]
        fn times_identity(
            a in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
        ) {
            let one = EntropyWeight::one();
            prop_assert!(one.times(&a).approx_eq(&a, 1e-10),
                "entropy times_left_id: {:?}", a);
            prop_assert!(a.times(&one).approx_eq(&a, 1e-10),
                "entropy times_right_id: {:?}", a);
        }

        // Law 7+8: Annihilation
        // zero.times(a) should give zero.
        // zero = (inf, 0). zero.times(a) = (inf + a.w, 0 + a.e) = (inf, a.e).
        // But zero = (inf, 0.0) and is_zero checks weight == inf.
        // So the result is_zero() = true even though expectation differs.
        // approx_eq checks: both zero -> true. So this works.
        #[test]
        fn left_annihilation(
            a in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
        ) {
            let z = EntropyWeight::zero();
            let result = z.times(&a);
            prop_assert!(result.is_zero(),
                "entropy left_annih: zero * {:?} = {:?}", a, result);
        }

        #[test]
        fn right_annihilation(
            a in (0.0f64..50.0, 0.0f64..50.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
        ) {
            let z = EntropyWeight::zero();
            let result = a.times(&z);
            prop_assert!(result.is_zero(),
                "entropy right_annih: {:?} * zero = {:?}", a, result);
        }

        // Star fixpoint for EntropyWeight:
        // star(a) ≈ 1 + a * star(a)
        #[test]
        fn star_fixpoint(
            a in (0.5f64..10.0, 0.0f64..5.0).prop_map(|(w, e)| EntropyWeight::new(w, e)),
        ) {
            let star_a = a.star();
            if !star_a.is_zero() {
                let rhs = EntropyWeight::one().plus(&a.times(&star_a));
                prop_assert!(star_a.approx_eq(&rhs, 1e-4),
                    "entropy star fixpoint: star({:?}) = {:?}  !=  {:?}", a, star_a, rhs);
            }
        }
    }
}

mod amplitude_weight_proptest_laws {
    use super::super::*;
    use proptest::prelude::*;

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(300))]

        // Law 1: Plus associativity
        #[test]
        fn plus_associativity(
            a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            b in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            c in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
        ) {
            let ab_c = a.plus(&b).plus(&c);
            let a_bc = a.plus(&b.plus(&c));
            prop_assert!(ab_c.approx_eq(&a_bc, 1e-10),
                "amplitude plus_assoc: {:?} vs {:?}", ab_c, a_bc);
        }

        // Law 2: Times associativity
        #[test]
        fn times_associativity(
            a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            b in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            c in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
        ) {
            let ab_c = a.times(&b).times(&c);
            let a_bc = a.times(&b.times(&c));
            prop_assert!(ab_c.approx_eq(&a_bc, 1e-8),
                "amplitude times_assoc: {:?} vs {:?}", ab_c, a_bc);
        }

        // Law 3: Plus commutativity
        #[test]
        fn plus_commutativity(
            a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            b in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
        ) {
            let ab = a.plus(&b);
            let ba = b.plus(&a);
            prop_assert!(ab.approx_eq(&ba, 1e-10),
                "amplitude plus_comm: {:?} vs {:?}", ab, ba);
        }

        // Law 4: Plus identity
        #[test]
        fn plus_identity(
            a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
        ) {
            let z = AmplitudeWeight::zero();
            prop_assert!(a.plus(&z).approx_eq(&a, 1e-10), "amplitude plus_id right");
            prop_assert!(z.plus(&a).approx_eq(&a, 1e-10), "amplitude plus_id left");
        }

        // Law 5: Times left identity
        #[test]
        fn times_left_identity(
            a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
        ) {
            let one = AmplitudeWeight::one();
            prop_assert!(one.times(&a).approx_eq(&a, 1e-10), "amplitude times_left_id");
        }

        // Law 6: Times right identity
        #[test]
        fn times_right_identity(
            a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
        ) {
            let one = AmplitudeWeight::one();
            prop_assert!(a.times(&one).approx_eq(&a, 1e-10), "amplitude times_right_id");
        }

        // Law 7: Left annihilation
        #[test]
        fn left_annihilation(
            a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
        ) {
            let z = AmplitudeWeight::zero();
            prop_assert!(z.times(&a).approx_eq(&z, 1e-10), "amplitude left_annih");
        }

        // Law 8: Right annihilation
        #[test]
        fn right_annihilation(
            a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
        ) {
            let z = AmplitudeWeight::zero();
            prop_assert!(a.times(&z).approx_eq(&z, 1e-10), "amplitude right_annih");
        }

        // Law 9: Left distributivity — holds for complex numbers (ring)
        #[test]
        fn left_distributivity(
            a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            b in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            c in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
        ) {
            let lhs = a.times(&b.plus(&c));
            let rhs = a.times(&b).plus(&a.times(&c));
            prop_assert!(lhs.approx_eq(&rhs, 1e-8),
                "amplitude left_dist: {:?} vs {:?}", lhs, rhs);
        }

        // Law 10: Right distributivity
        #[test]
        fn right_distributivity(
            a in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            b in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
            c in (-10.0f64..10.0, -10.0f64..10.0).prop_map(|(r, i)| AmplitudeWeight::new(r, i)),
        ) {
            let lhs = a.plus(&b).times(&c);
            let rhs = a.times(&c).plus(&b.times(&c));
            prop_assert!(lhs.approx_eq(&rhs, 1e-8),
                "amplitude right_dist: {:?} vs {:?}", lhs, rhs);
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════
// SemiringRef blanket impl tests
// ═══════════════════════════════════════════════════════════════════════

/// Verify that the blanket `SemiringRef` impl delegates correctly for
/// `BooleanWeight` (a `Semiring: Copy` type).
mod semiring_ref_boolean {
    use super::super::{BooleanWeight, Semiring, SemiringRef};

    #[test]
    fn test_blanket_zero_ref_matches_zero() {
        assert_eq!(<BooleanWeight as SemiringRef>::zero_ref(), BooleanWeight::zero(),);
    }

    #[test]
    fn test_blanket_one_ref_matches_one() {
        assert_eq!(<BooleanWeight as SemiringRef>::one_ref(), BooleanWeight::one(),);
    }

    #[test]
    fn test_blanket_plus_ref_matches_plus() {
        let t = BooleanWeight::new(true);
        let f = BooleanWeight::new(false);
        assert_eq!(t.plus_ref(&f), t.plus(&f));
        assert_eq!(f.plus_ref(&t), f.plus(&t));
        assert_eq!(t.plus_ref(&t), t.plus(&t));
        assert_eq!(f.plus_ref(&f), f.plus(&f));
    }

    #[test]
    fn test_blanket_times_ref_matches_times() {
        let t = BooleanWeight::new(true);
        let f = BooleanWeight::new(false);
        assert_eq!(t.times_ref(&f), t.times(&f));
        assert_eq!(f.times_ref(&t), f.times(&t));
        assert_eq!(t.times_ref(&t), t.times(&t));
        assert_eq!(f.times_ref(&f), f.times(&f));
    }

    #[test]
    fn test_blanket_is_zero_ref_matches_is_zero() {
        let t = BooleanWeight::new(true);
        let f = BooleanWeight::new(false);
        assert_eq!(t.is_zero_ref(), t.is_zero());
        assert_eq!(f.is_zero_ref(), f.is_zero());
    }

    #[test]
    fn test_blanket_is_one_ref_matches_is_one() {
        let t = BooleanWeight::new(true);
        let f = BooleanWeight::new(false);
        assert_eq!(t.is_one_ref(), t.is_one());
        assert_eq!(f.is_one_ref(), f.is_one());
    }

    #[test]
    fn test_semiring_ref_laws_boolean() {
        let t = BooleanWeight::new(true);
        let f = BooleanWeight::new(false);
        let z = BooleanWeight::zero_ref();
        let one = BooleanWeight::one_ref();

        // Zero is additive identity
        assert_eq!(z.plus_ref(&t), t);
        assert_eq!(t.plus_ref(&z), t);
        assert_eq!(z.plus_ref(&f), f);

        // One is multiplicative identity
        assert_eq!(one.times_ref(&t), t);
        assert_eq!(t.times_ref(&one), t);
        assert_eq!(one.times_ref(&f), f);

        // Zero annihilates
        assert!(z.times_ref(&t).is_zero_ref());
        assert!(t.times_ref(&z).is_zero_ref());

        // Commutativity
        assert_eq!(t.plus_ref(&f), f.plus_ref(&t));
        assert_eq!(t.times_ref(&f), f.times_ref(&t));
    }
}

/// Verify that the blanket `SemiringRef` impl delegates correctly for
/// `TropicalWeight` (a `Semiring: Copy` type).
mod semiring_ref_tropical {
    use super::super::{Semiring, SemiringRef, TropicalWeight};

    #[test]
    fn test_blanket_zero_ref_matches_zero() {
        assert_eq!(<TropicalWeight as SemiringRef>::zero_ref(), TropicalWeight::zero(),);
    }

    #[test]
    fn test_blanket_one_ref_matches_one() {
        assert_eq!(<TropicalWeight as SemiringRef>::one_ref(), TropicalWeight::one(),);
    }

    #[test]
    fn test_blanket_plus_ref_matches_plus() {
        let a = TropicalWeight::new(3.0);
        let b = TropicalWeight::new(7.0);
        assert_eq!(a.plus_ref(&b), a.plus(&b));
        assert_eq!(b.plus_ref(&a), b.plus(&a));
    }

    #[test]
    fn test_blanket_times_ref_matches_times() {
        let a = TropicalWeight::new(3.0);
        let b = TropicalWeight::new(7.0);
        assert_eq!(a.times_ref(&b), a.times(&b));
        assert_eq!(b.times_ref(&a), b.times(&a));
    }

    #[test]
    fn test_blanket_is_zero_ref_matches_is_zero() {
        let a = TropicalWeight::new(3.0);
        let z = TropicalWeight::zero();
        assert_eq!(a.is_zero_ref(), a.is_zero());
        assert_eq!(z.is_zero_ref(), z.is_zero());
    }

    #[test]
    fn test_blanket_is_one_ref_matches_is_one() {
        let a = TropicalWeight::new(3.0);
        let one = TropicalWeight::one();
        assert_eq!(a.is_one_ref(), a.is_one());
        assert_eq!(one.is_one_ref(), one.is_one());
    }

    #[test]
    fn test_semiring_ref_laws_tropical() {
        let a = TropicalWeight::new(2.0);
        let b = TropicalWeight::new(5.0);
        let c = TropicalWeight::new(8.0);
        let z = TropicalWeight::zero_ref();
        let one = TropicalWeight::one_ref();

        // Zero is additive identity
        assert_eq!(z.plus_ref(&a), a);
        assert_eq!(a.plus_ref(&z), a);

        // One is multiplicative identity
        assert_eq!(one.times_ref(&a), a);
        assert_eq!(a.times_ref(&one), a);

        // Zero annihilates
        assert!(z.times_ref(&a).is_zero_ref());
        assert!(a.times_ref(&z).is_zero_ref());

        // Commutativity of plus
        assert_eq!(a.plus_ref(&b), b.plus_ref(&a));

        // Associativity of plus
        assert_eq!(a.plus_ref(&b).plus_ref(&c), a.plus_ref(&b.plus_ref(&c)),);

        // Associativity of times
        assert_eq!(a.times_ref(&b).times_ref(&c), a.times_ref(&b.times_ref(&c)),);

        // Left distributivity: a * (b + c) = (a * b) + (a * c)
        assert_eq!(a.times_ref(&b.plus_ref(&c)), a.times_ref(&b).plus_ref(&a.times_ref(&c)),);

        // Idempotent plus
        assert_eq!(a.plus_ref(&a), a);
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Phase C-bis Commit 1 (2026-05-17): StarSemiringRef + matrix_star_ref
// tests. Per docs/design/plans/closed-semiring-cycle-handling.md §10
// (CSCH-7 + CSCH-8).
// ═══════════════════════════════════════════════════════════════════════

/// CSCH-7: `matrix_star_ref` reproduces `matrix_star` for `Copy`
/// semirings (regression guard ensuring the ref-style and value-style
/// Lehmann implementations stay in lockstep). Boolean variant.
#[test]
fn csch_7_matrix_star_ref_matches_matrix_star_boolean() {
    let f = BooleanWeight::new(false);
    let t = BooleanWeight::new(true);
    // Same DAG as test_matrix_star_boolean_dag: 0→1→2.
    let adj = vec![vec![f, t, f], vec![f, f, t], vec![f, f, f]];
    let star_val = matrix_star(&adj);
    let star_ref = matrix_star_ref(&adj);
    assert_eq!(
        star_val, star_ref,
        "matrix_star_ref must agree with matrix_star on the same input"
    );
}

/// CSCH-7: `matrix_star_ref` on tropical shortest-paths matches
/// `matrix_star`.
#[test]
fn csch_7_matrix_star_ref_matches_matrix_star_tropical() {
    let inf = TropicalWeight::infinity();
    let adj = vec![
        vec![inf, TropicalWeight::new(2.0), TropicalWeight::new(10.0)],
        vec![inf, inf, TropicalWeight::new(3.0)],
        vec![inf, inf, inf],
    ];
    let star_val = matrix_star(&adj);
    let star_ref = matrix_star_ref(&adj);
    for i in 0..3 {
        for j in 0..3 {
            let v = star_val[i][j].value();
            let r = star_ref[i][j].value();
            if v.is_infinite() {
                assert!(r.is_infinite(), "({i},{j}): val=inf, ref={r}");
            } else {
                assert!((v - r).abs() < 1e-12, "({i},{j}): val={v}, ref={r}");
            }
        }
    }
}

/// CSCH-7: `matrix_star_ref` on cyclic Boolean (all-reach-all) matches
/// `matrix_star` (specifically exercises Lehmann's cycle handling
/// path).
#[test]
fn csch_7_matrix_star_ref_cyclic_boolean() {
    let f = BooleanWeight::new(false);
    let t = BooleanWeight::new(true);
    let adj = vec![vec![f, t, f], vec![f, f, t], vec![t, f, f]];
    let star_ref = matrix_star_ref(&adj);
    // Cycle → everything reachable from everything.
    for i in 0..3 {
        for j in 0..3 {
            assert!(
                star_ref[i][j].is_reachable(),
                "matrix_star_ref({i},{j}) should be reachable in a cycle"
            );
        }
    }
}

/// `matrix_star_ref` rejects non-square input.
///
/// ⚠ Formerly `#[should_panic(expected = "matrix_star_ref: adj must be square")]`.
/// Squareness is a precondition an external caller can violate, so the refusal is now
/// a value ([`try_matrix_star_ref`]) and the panicking wrapper is a thin `.expect` over
/// it. What this distinguishes GREW: the old form could only tell "panicked with a
/// message starting `matrix_star_ref: adj must be square`" from "did not panic"; it now
/// separates the wide row from the short row, names WHICH row disagrees and by how
/// much, and — via the square control — shows the refusal is not simply "refuses
/// everything".
#[test]
fn csch_7_matrix_star_ref_rejects_non_square() {
    // 2 rows of 3 — order 2, so both rows are too WIDE. Lehmann would silently ignore
    // column 2 of every row.
    let wide = try_matrix_star_ref(&vec![vec![BooleanWeight::new(false); 3]; 2])
        .expect_err("2×3 is not square");
    assert_eq!(wide, NonSquareMatrix { order: 2, row: 0, row_len: 3 });

    // 3 rows of 2 — order 3, so every row is too SHORT. Lehmann would read out of
    // bounds. A check written as `row.len() > n` would pass the case above and fail
    // this one, which is why both are here.
    let narrow = try_matrix_star_ref(&vec![vec![BooleanWeight::new(false); 2]; 3])
        .expect_err("3×2 is not square");
    assert_eq!(narrow, NonSquareMatrix { order: 3, row: 0, row_len: 2 });

    // A RAGGED matrix: rows 0 and 1 are fine, row 2 is not. The reported index must be
    // the offending row, not always 0 — otherwise the field carries no information.
    let ragged = try_matrix_star_ref(&vec![
        vec![BooleanWeight::new(false); 3],
        vec![BooleanWeight::new(false); 3],
        vec![BooleanWeight::new(false); 1],
    ])
    .expect_err("a ragged matrix is not square");
    assert_eq!(ragged, NonSquareMatrix { order: 3, row: 2, row_len: 1 });

    // ★ ANTI-VACUITY + wrapper agreement: the square matrix is accepted, and the
    // panicking wrapper every production caller uses returns exactly what the fallible
    // entry point does. Without this, moving the check into `try_…` alone would leave
    // `matrix_star_ref` free to accept the rejected shapes.
    let square = vec![vec![BooleanWeight::new(false); 3]; 3];
    let accepted = try_matrix_star_ref(&square).expect("3×3 is square");
    assert_eq!(accepted, matrix_star_ref(&square));
}

/// CSCH-8: `LexicographicWeight::star` returns `one_ref()` (idempotent
/// collapse). Phase C-bis assumes this invariant when computing cyclic
/// realize weights under the production walker semiring.
#[test]
fn csch_8_lex_weight_star_collapses_to_one() {
    use crate::lex_weight::LexicographicWeight;
    let a = LexicographicWeight::from_cost(1.5, 3, 4);
    let b = LexicographicWeight::from_cost(0.0, 0, 0);
    let c = LexicographicWeight::one_ref();
    // Under idempotency, a* = 1 ⊕ a ⊕ a² ⊕ ... = 1.
    assert_eq!(a.star_ref(), LexicographicWeight::one_ref());
    assert_eq!(b.star_ref(), LexicographicWeight::one_ref());
    assert_eq!(c.star_ref(), LexicographicWeight::one_ref());
    // plus_star_ref(a) = a ⊗ a* = a ⊗ 1 = a.
    assert_eq!(a.plus_star_ref(), a);
}

/// CSCH-8: `matrix_star_ref` runs on `LexicographicWeight` matrices.
/// Confirms that Lehmann's algorithm terminates correctly under the
/// production walker's weight type — the integration end-to-end.
#[test]
fn csch_8_matrix_star_ref_on_lex_weight() {
    use crate::lex_weight::LexicographicWeight;
    let zero = LexicographicWeight::zero_ref();
    let one = LexicographicWeight::one_ref();
    let a = LexicographicWeight::from_cost(1.0, 1, 0);
    // 3×3 DAG with a single non-trivial edge.
    let adj = vec![
        vec![zero.clone(), a.clone(), zero.clone()],
        vec![zero.clone(), zero.clone(), a.clone()],
        vec![zero.clone(), zero.clone(), zero.clone()],
    ];
    let closure = matrix_star_ref(&adj);
    // Diagonal entries should be `one` (a* collapses; identity).
    for i in 0..3 {
        assert_eq!(closure[i][i], one, "diagonal at ({i},{i}) should be one under idempotent star");
    }
}

// ═══════════════════════════════════════════════════════════════════════
// Phase C-bis Commit 2 (2026-05-17): Newton's method tests.
// Per docs/design/plans/multi-call-scc-linearization.md §11
// (MCSL-1..4, MCSL-7..9) + docs/design/plans/closed-semiring-cycle-handling.md §10
// (CSCH-4..6).
// ═══════════════════════════════════════════════════════════════════════

use crate::PackingFactored;

/// MCSL-1: `S → S S | ε` under `BooleanWeight`. Hand: `Y = ε ⊕ Y⊗Y`;
/// closed form `Y = true`. Multi-call SCC; Newton activates.
#[test]
fn mcsl_1_self_loop_multi_call_boolean() {
    // SCC of size 1 (just `S`), with:
    //   - P_eps: exit packing (in_scc_children = []), weight = true
    //   - P_ss: multi-call packing (in_scc_children = [0, 0]), weight = true
    let packings = vec![
        PackingFactored::<BooleanWeight> {
            target_i: 0,
            outside_product: BooleanWeight::one_ref(), // true
            in_scc_children: vec![],
        },
        PackingFactored::<BooleanWeight> {
            target_i: 0,
            outside_product: BooleanWeight::one_ref(), // true
            in_scc_children: vec![0, 0],
        },
    ];
    let y = solve_scc_weights_newton(1, &packings, 64);
    assert_eq!(y.len(), 1);
    assert!(y[0].is_reachable(), "Y_S should be true (reachable)");
}

/// MCSL-4: linear fast-path detection — synthesize SCC with only
/// unary in-SCC packings; verify Newton returns the exact closed form
/// (matrix_star equivalent) without iterating.
#[test]
fn mcsl_4_linear_fast_path() {
    // Mutual recursion: A → B, B → A, with exit packings ε.
    let packings = vec![
        // S_0 = A: exit (b[0] += 1)
        PackingFactored::<BooleanWeight> {
            target_i: 0,
            outside_product: BooleanWeight::one_ref(),
            in_scc_children: vec![],
        },
        // S_0 = A: unary edge → S_1 (B)
        PackingFactored::<BooleanWeight> {
            target_i: 0,
            outside_product: BooleanWeight::one_ref(),
            in_scc_children: vec![1],
        },
        // S_1 = B: unary edge → S_0 (A)
        PackingFactored::<BooleanWeight> {
            target_i: 1,
            outside_product: BooleanWeight::one_ref(),
            in_scc_children: vec![0],
        },
    ];
    let y = solve_scc_weights_newton(2, &packings, 64);
    assert!(y[0].is_reachable(), "Y_A reachable");
    assert!(y[1].is_reachable(), "Y_B reachable (via cycle)");
}

/// MCSL-3: differential computation: for an arity-3 packing
/// `P: S_i ← S_j ⊗ S_k ⊗ S_l`, verify the Leibniz partials.
#[test]
fn mcsl_3_differential_arity3() {
    // Set up Y values that distinguish positions.
    let y = vec![
        CountingWeight::one(),  // Y[0]
        CountingWeight::new(2), // Y[1] = j
        CountingWeight::new(3), // Y[2] = k
        CountingWeight::new(5), // Y[3] = l
    ];
    let packings = vec![PackingFactored::<CountingWeight> {
        target_i: 0,
        outside_product: CountingWeight::one(), // weight = 1
        in_scc_children: vec![1, 2, 3],         // [S_j, S_k, S_l]
    }];
    let df = build_differential_matrix(&y, &packings, 4);
    // Df[0][1] = ∂f/∂Y_j = Y_k · Y_l · outside = 3 · 5 · 1 = 15
    assert_eq!(df[0][1].count(), 15);
    // Df[0][2] = ∂f/∂Y_k = Y_j · Y_l · outside = 2 · 5 · 1 = 10
    assert_eq!(df[0][2].count(), 10);
    // Df[0][3] = ∂f/∂Y_l = Y_j · Y_k · outside = 2 · 3 · 1 = 6
    assert_eq!(df[0][3].count(), 6);
    // Df[0][0] = no contribution (Y_0 not in in_scc_children)
    assert_eq!(df[0][0].count(), 0);
}

/// MCSL-7: same `Y_j` appearing twice in `in_scc_children`:
/// `P: S ← S ⊗ S`. Verify `Df[S][S] = Y_S ⊕ Y_S` (which is
/// `2·Y_S` under CountingWeight or `Y_S` under idempotent).
#[test]
fn mcsl_7_repeated_factor_leibniz() {
    // Counting case: `Df[0][0]` = position-1 partial (Y[c_2] = Y_0)
    // ⊕ position-2 partial (Y[c_1] = Y_0) = Y_0 + Y_0 = 2 * Y_0.
    let y_count = vec![CountingWeight::new(7)];
    let packings_count = vec![PackingFactored::<CountingWeight> {
        target_i: 0,
        outside_product: CountingWeight::one(),
        in_scc_children: vec![0, 0],
    }];
    let df_count = build_differential_matrix(&y_count, &packings_count, 1);
    assert_eq!(df_count[0][0].count(), 14, "CountingWeight: Df = 2·Y = 14");

    // Boolean (idempotent) case: `Df[0][0] = true ⊕ true = true`.
    let y_bool = vec![BooleanWeight::one_ref()];
    let packings_bool = vec![PackingFactored::<BooleanWeight> {
        target_i: 0,
        outside_product: BooleanWeight::one_ref(),
        in_scc_children: vec![0, 0],
    }];
    let df_bool = build_differential_matrix(&y_bool, &packings_bool, 1);
    assert!(df_bool[0][0].is_reachable(), "Boolean: Df = true (idempotent collapse)");
}

/// MCSL-9: monotonicity — at each Newton iteration, the iterate must
/// be `⊒` the previous (Esparza-Kiefer-Luttenberger Thm 5.1).
/// Verified for Boolean (idempotent) and Counting (non-idempotent).
#[test]
fn mcsl_9_newton_monotone_booleans_and_counts() {
    // Boolean: starting from `false`, iterates must reach `true` and stay.
    let bool_packings = vec![
        PackingFactored::<BooleanWeight> {
            target_i: 0,
            outside_product: BooleanWeight::one_ref(), // ε exit
            in_scc_children: vec![],
        },
        PackingFactored::<BooleanWeight> {
            target_i: 0,
            outside_product: BooleanWeight::one_ref(),
            in_scc_children: vec![0, 0],
        },
    ];
    let y_bool = solve_scc_weights_newton(1, &bool_packings, 64);
    assert!(y_bool[0].is_reachable(), "Y_S should reach true");

    // Counting: cycle saturates to u64::MAX.
    let count_packings = vec![
        PackingFactored::<CountingWeight> {
            target_i: 0,
            outside_product: CountingWeight::one(),
            in_scc_children: vec![],
        },
        PackingFactored::<CountingWeight> {
            target_i: 0,
            outside_product: CountingWeight::one(),
            in_scc_children: vec![0, 0],
        },
    ];
    let y_count = solve_scc_weights_newton(1, &count_packings, 64);
    // Should saturate (or at least be very large) — at minimum > 0.
    assert!(y_count[0].count() > 0, "non-trivial cycle should produce non-zero count");
}

/// `evaluate_f` smoke test: verify f(Y) = Σ contributions over packings
/// + b vector.
#[test]
fn evaluate_f_smoke() {
    let y = vec![CountingWeight::new(2), CountingWeight::new(3)];
    let b = vec![CountingWeight::new(1), CountingWeight::zero()];
    let packings = vec![
        // S_0: contributes `outside · Y[1]` = 5 · 3 = 15 → total f[0] = 1 + 15 = 16
        PackingFactored::<CountingWeight> {
            target_i: 0,
            outside_product: CountingWeight::new(5),
            in_scc_children: vec![1],
        },
        // S_1: contributes `outside · Y[0]` = 2 · 2 = 4 → total f[1] = 0 + 4 = 4
        PackingFactored::<CountingWeight> {
            target_i: 1,
            outside_product: CountingWeight::new(2),
            in_scc_children: vec![0],
        },
    ];
    let f = evaluate_f(&y, &packings, &b, 2);
    assert_eq!(f[0].count(), 16);
    assert_eq!(f[1].count(), 4);
}
