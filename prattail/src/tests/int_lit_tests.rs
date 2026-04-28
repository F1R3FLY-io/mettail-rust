use crate::{parse_int_lit, IntLit, Suffix};
use num_bigint::BigInt;

// Per the contract documented at parse_int_lit (int_lit.rs:303-315): when
// `default_suffix` is None, the result is the NARROWEST type that fits via
// the cascade i32 → u32 → i64 → u64 → i128 → u128 → BigInt. These tests
// verify that bound-tightening behaviour for small values (which fit in i32).

#[test]
fn parses_narrowest_fit_decimal() {
    assert_eq!(parse_int_lit("0", None).unwrap(), IntLit::I32(0));
    assert_eq!(parse_int_lit("23", None).unwrap(), IntLit::I32(23));
    assert_eq!(parse_int_lit("1_000_000", None).unwrap(), IntLit::I32(1_000_000));
    // Values exceeding i32::MAX skip to the next-widest fit.
    assert_eq!(
        parse_int_lit("3_000_000_000", None).unwrap(),
        IntLit::U32(3_000_000_000),
    );
    assert_eq!(
        parse_int_lit("9_999_999_999", None).unwrap(),
        IntLit::I64(9_999_999_999),
    );
}

#[test]
fn parses_radix_prefixes() {
    // Small values fit i32 under the narrowest-fit cascade.
    assert_eq!(parse_int_lit("0b1010", None).unwrap(), IntLit::I32(10));
    assert_eq!(parse_int_lit("0o77", None).unwrap(), IntLit::I32(63));
    assert_eq!(parse_int_lit("0xFF", None).unwrap(), IntLit::I32(255));
    assert_eq!(parse_int_lit("0xFF_FF", None).unwrap(), IntLit::I32(65535));
}

#[test]
fn parses_signed_suffixes() {
    assert_eq!(parse_int_lit("-128i8", None).unwrap(), IntLit::I8(-128));
    assert!(parse_int_lit("-129i8", None).is_err());

    assert_eq!(parse_int_lit("127i8", None).unwrap(), IntLit::I8(127));
    assert!(parse_int_lit("128i8", None).is_err());

    assert_eq!(parse_int_lit("-32768i16", None).unwrap(), IntLit::I16(-32768));
    assert!(parse_int_lit("-32769i16", None).is_err());

    assert_eq!(parse_int_lit("32767i16", None).unwrap(), IntLit::I16(32767));
    assert!(parse_int_lit("32768i16", None).is_err());

    assert_eq!(parse_int_lit("-2147483648i32", None).unwrap(), IntLit::I32(i32::MIN));
    assert!(parse_int_lit("-2147483649i32", None).is_err());

    assert_eq!(parse_int_lit("2147483647i32", None).unwrap(), IntLit::I32(2_147_483_647));
    assert!(parse_int_lit("2147483648i32", None).is_err());

    assert_eq!(parse_int_lit("-9223372036854775808i64", None).unwrap(), IntLit::I64(i64::MIN));
    assert!(parse_int_lit("-9223372036854775809i64", None).is_err());

    assert_eq!(
        parse_int_lit("9223372036854775807i64", None).unwrap(),
        IntLit::I64(9_223_372_036_854_775_807)
    );
    assert!(parse_int_lit("9223372036854775808i64", None).is_err());

    assert_eq!(
        parse_int_lit("-170141183460469231731687303715884105728i128", None).unwrap(),
        IntLit::I128(i128::MIN)
    );
    assert!(parse_int_lit("-170141183460469231731687303715884105729i128", None).is_err());

    assert_eq!(
        parse_int_lit("170141183460469231731687303715884105727i128", None).unwrap(),
        IntLit::I128(i128::MAX)
    );
}

#[test]
fn parses_unsigned_suffixes() {
    assert_eq!(parse_int_lit("255u8", None).unwrap(), IntLit::U8(255));
    assert!(parse_int_lit("256u8", None).is_err());

    assert_eq!(parse_int_lit("65535u16", None).unwrap(), IntLit::U16(65535));
    assert!(parse_int_lit("65536u16", None).is_err());

    assert_eq!(parse_int_lit("4294967295u32", None).unwrap(), IntLit::U32(4_294_967_295));
    assert!(parse_int_lit("4294967296u32", None).is_err());

    assert_eq!(
        parse_int_lit("18446744073709551615u64", None).unwrap(),
        IntLit::U64(18_446_744_073_709_551_615)
    );
    assert!(parse_int_lit("18446744073709551616u64", None).is_err());

    assert_eq!(parse_int_lit("0xFFu32", None).unwrap(), IntLit::U32(255));
    assert_eq!(parse_int_lit("0b1010u16", None).unwrap(), IntLit::U16(10));
}

#[test]
fn parses_bigint_n_suffix() {
    match parse_int_lit("123n", None).unwrap() {
        IntLit::BigInt(v) => assert_eq!(v.to_string(), "123"),
        other => panic!("expected BigInt, got {other:?}"),
    }

    // Accept radix prefixes for BigInt, too.
    match parse_int_lit("0xFFn", None).unwrap() {
        IntLit::BigInt(v) => assert_eq!(v.to_string(), "255"),
        other => panic!("expected BigInt, got {other:?}"),
    }
}

#[test]
fn parses_very_large_bigint_values() {
    let huge_dec = "12345678901234567890123456789012345678901234567890n";
    match parse_int_lit(huge_dec, None).unwrap() {
        IntLit::BigInt(v) => {
            assert_eq!(v.to_string(), "12345678901234567890123456789012345678901234567890")
        },
        other => panic!("expected BigInt, got {other:?}"),
    }

    let huge_hex = "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFn";
    match parse_int_lit(huge_hex, None).unwrap() {
        IntLit::BigInt(v) => {
            assert_eq!(v.to_string(), "1461501637330902918203684832716283019655932542975")
        },
        other => panic!("expected BigInt, got {other:?}"),
    }
}

#[test]
fn bigint_default_suffix_is_respected() {
    match parse_int_lit("42", Some(Suffix::BigInt)).unwrap() {
        IntLit::BigInt(v) => assert_eq!(v.to_string(), "42"),
        other => panic!("expected BigInt, got {other:?}"),
    }

    // Explicit suffix must win over provided default suffix.
    match parse_int_lit("42n", Some(Suffix::I32)).unwrap() {
        IntLit::BigInt(v) => assert_eq!(v.to_string(), "42"),
        other => panic!("expected BigInt, got {other:?}"),
    }
}

#[test]
fn invalid_bigint_digits_fail() {
    assert!(parse_int_lit("0b102n", None).is_err());
    assert!(parse_int_lit("0xGFn", None).is_err());
    assert!(parse_int_lit("n", None).is_err());
}

#[test]
fn r_suffix_is_not_an_integer_literal() {
    assert!(parse_int_lit("1r", None).is_err());
}

#[test]
fn calculator_int_literal_uses_i32_default_suffix() {
    assert_eq!(parse_int_lit("7", Some(Suffix::I32)).unwrap(), IntLit::I32(7));
}

#[test]
fn strict_integer_conversions_do_not_cross_types() {
    let u = parse_int_lit("12u32", None).unwrap();
    assert_eq!(u.to_u32(), Some(12));
    assert_eq!(u.to_i32(), None);

    let i = parse_int_lit("12i32", None).unwrap();
    assert_eq!(i.to_i32(), Some(12));
    assert_eq!(i.to_u32(), None);

    let b = parse_int_lit("12n", None).unwrap();
    assert_eq!(b.to_i32(), None);
    assert_eq!(b.to_u32(), None);
}

// B11/B12: lossless conversions across every IntLit variant. These exist
// because narrowest-fit produces variants like I32 / U32 / I64 / U64 / I128 /
// U128 / BigInt depending on the value, and the codegen-emitted action body
// must work uniformly without losing precision (any drop is reported as
// "WPDS produced no result"). Each method is variant-aware so widening never
// drops bits and narrowing rejects only on actual overflow.

#[test]
fn to_bigint_is_lossless_across_all_variants() {
    // Bare unsuffixed integers go through narrowest-fit, so the variant
    // depends on the value. Each case must round-trip into a BigInt with
    // matching value.
    for (text, expected) in [
        ("0", "0"),
        ("23", "23"),
        ("3000000000", "3000000000"),
        ("9999999999", "9999999999"),
        ("18446744073709551615", "18446744073709551615"), // u64::MAX → I128 in cascade
        ("170141183460469231731687303715884105727", "170141183460469231731687303715884105727"), // i128::MAX → U128 in cascade
        ("340282366920938463463374607431768211455", "340282366920938463463374607431768211455"), // u128::MAX → BigInt
    ] {
        let lit = parse_int_lit(text, None).unwrap();
        assert_eq!(
            lit.to_bigint().unwrap(),
            expected.parse::<BigInt>().unwrap(),
            "to_bigint differs for {text:?} (variant {lit:?})",
        );
    }

    // Suffixed variants: each variant maps directly.
    assert_eq!(parse_int_lit("-128i8", None).unwrap().to_bigint().unwrap(), BigInt::from(-128));
    assert_eq!(parse_int_lit("255u8", None).unwrap().to_bigint().unwrap(), BigInt::from(255));
    assert_eq!(parse_int_lit("65535u16", None).unwrap().to_bigint().unwrap(), BigInt::from(65535));
}

#[test]
fn as_i128_is_lossless_across_all_variants() {
    // i128::MAX with explicit suffix → IntLit::I128.
    let big = parse_int_lit("170141183460469231731687303715884105727i128", None).unwrap();
    assert_eq!(big.as_i128(), Some(i128::MAX));

    // i128::MIN.
    let neg = parse_int_lit("-170141183460469231731687303715884105728i128", None).unwrap();
    assert_eq!(neg.as_i128(), Some(i128::MIN));

    // u64::MAX should fit in i128.
    let u64m = parse_int_lit("18446744073709551615u64", None).unwrap();
    assert_eq!(u64m.as_i128(), Some(u64::MAX as i128));

    // u128::MAX does NOT fit in i128.
    let u128m = parse_int_lit("340282366920938463463374607431768211455u128", None).unwrap();
    assert_eq!(u128m.as_i128(), None);

    // BigInt path: large value > i128::MAX must reject; small value succeeds.
    let bi_big = parse_int_lit("999999999999999999999999999999999999999999n", None).unwrap();
    assert_eq!(bi_big.as_i128(), None);
    let bi_small = parse_int_lit("42n", None).unwrap();
    assert_eq!(bi_small.as_i128(), Some(42));
}

#[test]
fn as_u64_is_lossless_for_unsigned_in_range() {
    // u64::MAX with explicit suffix.
    let u64m = parse_int_lit("18446744073709551615u64", None).unwrap();
    assert_eq!(u64m.as_u64(), Some(u64::MAX));

    // u32::MAX widens to u64.
    let u32m = parse_int_lit("4294967295u32", None).unwrap();
    assert_eq!(u32m.as_u64(), Some(u32::MAX as u64));

    // i64 positive value.
    let i_pos = parse_int_lit("42i64", None).unwrap();
    assert_eq!(i_pos.as_u64(), Some(42));

    // i64 negative value rejected.
    let i_neg = parse_int_lit("-1i64", None).unwrap();
    assert_eq!(i_neg.as_u64(), None);

    // u128 value > u64::MAX rejected; in-range succeeds.
    let u128_big = parse_int_lit("340282366920938463463374607431768211455u128", None).unwrap();
    assert_eq!(u128_big.as_u64(), None);
    let u128_small = parse_int_lit("100u128", None).unwrap();
    assert_eq!(u128_small.as_u64(), Some(100));

    // BigInt path.
    let bi = parse_int_lit("999999999999999999999n", None).unwrap();
    assert_eq!(bi.as_u64(), None);
}

#[test]
fn as_u128_is_lossless_across_all_variants() {
    // u128::MAX.
    let u128m = parse_int_lit("340282366920938463463374607431768211455u128", None).unwrap();
    assert_eq!(u128m.as_u128(), Some(u128::MAX));

    // u64::MAX widens to u128.
    let u64m = parse_int_lit("18446744073709551615u64", None).unwrap();
    assert_eq!(u64m.as_u128(), Some(u64::MAX as u128));

    // i128 positive widens.
    let i_pos = parse_int_lit("100i128", None).unwrap();
    assert_eq!(i_pos.as_u128(), Some(100));

    // Negative rejected.
    let i_neg = parse_int_lit("-1i64", None).unwrap();
    assert_eq!(i_neg.as_u128(), None);

    // BigInt > u128::MAX rejected.
    let bi_big = parse_int_lit("999999999999999999999999999999999999999999n", None).unwrap();
    assert_eq!(bi_big.as_u128(), None);
}
