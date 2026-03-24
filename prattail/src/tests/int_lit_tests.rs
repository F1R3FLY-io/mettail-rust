use crate::{parse_int_lit, IntLit, Suffix};

#[test]
fn parses_default_i64_decimal() {
    assert_eq!(parse_int_lit("0", None).unwrap(), IntLit::I64(0));
    assert_eq!(parse_int_lit("23", None).unwrap(), IntLit::I64(23));
    assert_eq!(parse_int_lit("1_000_000", None).unwrap(), IntLit::I64(1_000_000));
}

#[test]
fn parses_radix_prefixes() {
    assert_eq!(parse_int_lit("0b1010", None).unwrap(), IntLit::I64(10));
    assert_eq!(parse_int_lit("0o77", None).unwrap(), IntLit::I64(63));
    assert_eq!(parse_int_lit("0xFF", None).unwrap(), IntLit::I64(255));
    assert_eq!(parse_int_lit("0xFF_FF", None).unwrap(), IntLit::I64(65535));
}

#[test]
fn parses_signed_suffixes() {
    assert_eq!(parse_int_lit("127i8", None).unwrap(), IntLit::I8(127));
    assert!(parse_int_lit("128i8", None).is_err());

    assert_eq!(parse_int_lit("32767i16", None).unwrap(), IntLit::I16(32767));
    assert!(parse_int_lit("32768i16", None).is_err());

    assert_eq!(parse_int_lit("2147483647i32", None).unwrap(), IntLit::I32(2_147_483_647));
    assert!(parse_int_lit("2147483648i32", None).is_err());

    assert_eq!(
        parse_int_lit("9223372036854775807i64", None).unwrap(),
        IntLit::I64(9_223_372_036_854_775_807)
    );
    assert!(parse_int_lit("9223372036854775808i64", None).is_err());

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
