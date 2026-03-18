use crate::{parse_int_lit, IntLit};

#[test]
fn parses_default_i64_decimal() {
    assert_eq!(parse_int_lit("0").unwrap(), IntLit::I64(0));
    assert_eq!(parse_int_lit("23").unwrap(), IntLit::I64(23));
    assert_eq!(parse_int_lit("1_000_000").unwrap(), IntLit::I64(1_000_000));
}

#[test]
fn parses_radix_prefixes() {
    assert_eq!(parse_int_lit("0b1010").unwrap(), IntLit::I64(10));
    assert_eq!(parse_int_lit("0o77").unwrap(), IntLit::I64(63));
    assert_eq!(parse_int_lit("0xFF").unwrap(), IntLit::I64(255));
    assert_eq!(parse_int_lit("0xFF_FF").unwrap(), IntLit::I64(65535));
}

#[test]
fn parses_signed_suffixes() {
    assert_eq!(parse_int_lit("127i8").unwrap(), IntLit::I8(127));
    assert!(parse_int_lit("128i8").is_err());

    assert_eq!(parse_int_lit("32767i16").unwrap(), IntLit::I16(32767));
    assert!(parse_int_lit("32768i16").is_err());

    assert_eq!(parse_int_lit("2147483647i32").unwrap(), IntLit::I32(2_147_483_647));
    assert!(parse_int_lit("2147483648i32").is_err());

    assert_eq!(
        parse_int_lit("9223372036854775807i64").unwrap(),
        IntLit::I64(9_223_372_036_854_775_807)
    );
    assert!(parse_int_lit("9223372036854775808i64").is_err());

    assert_eq!(
        parse_int_lit("170141183460469231731687303715884105727i128").unwrap(),
        IntLit::I128(i128::MAX)
    );
}

#[test]
fn parses_unsigned_suffixes() {
    assert_eq!(parse_int_lit("255u8").unwrap(), IntLit::U8(255));
    assert!(parse_int_lit("256u8").is_err());

    assert_eq!(parse_int_lit("65535u16").unwrap(), IntLit::U16(65535));
    assert!(parse_int_lit("65536u16").is_err());

    assert_eq!(parse_int_lit("4294967295u32").unwrap(), IntLit::U32(4_294_967_295));
    assert!(parse_int_lit("4294967296u32").is_err());

    assert_eq!(
        parse_int_lit("18446744073709551615u64").unwrap(),
        IntLit::U64(18_446_744_073_709_551_615)
    );

    assert_eq!(parse_int_lit("0xFFu32").unwrap(), IntLit::U32(255));
    assert_eq!(parse_int_lit("0b1010u16").unwrap(), IntLit::U16(10));
}

#[test]
fn parses_bigint_n_suffix() {
    match parse_int_lit("123n").unwrap() {
        IntLit::BigInt(v) => assert_eq!(v.to_string(), "123"),
        other => panic!("expected BigInt, got {other:?}"),
    }

    // Accept radix prefixes for BigInt, too.
    match parse_int_lit("0xFFn").unwrap() {
        IntLit::BigInt(v) => assert_eq!(v.to_string(), "255"),
        other => panic!("expected BigInt, got {other:?}"),
    }
}

#[test]
fn parses_bigrat_stub_r_suffix() {
    // Stub should lex as a distinct token (not split into `1` then `r`).
    match parse_int_lit("1r").unwrap() {
        IntLit::BigRatStub(v) => assert_eq!(v.to_string(), "1"),
        other => panic!("expected BigRatStub, got {other:?}"),
    }
}

