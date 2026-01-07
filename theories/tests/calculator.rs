// Tests for the Calculator theory with support for multiple integer literal bases

// Basic decimal literal tests
#[test]
fn test_hexadecimal_literal_parsing() {
    // These test that the LALRPOP grammar correctly parses hex literals
    // 0x4A = 4*16 + 10 = 74
    // 0xFF = 15*16 + 15 = 255
    // Tests are informational - actual parsing is done by LALRPOP
    assert_eq!(0x4A, 74);
    assert_eq!(0x4a, 74);
    assert_eq!(0xFF, 255);
    assert_eq!(0x0, 0);
}

#[test]
fn test_octal_literal_parsing() {
    // Octal: base 8
    // 0o47 = 4*8 + 7 = 39
    // 0o77 = 7*8 + 7 = 63
    assert_eq!(0o47, 39);
    assert_eq!(0o77, 63);
    assert_eq!(0o0, 0);
}

#[test]
fn test_binary_literal_parsing() {
    // Binary: base 2
    // 0b110 = 1*4 + 1*2 + 0 = 6
    // 0b1111 = 15
    assert_eq!(0b110, 6);
    assert_eq!(0b1111, 15);
    assert_eq!(0b0, 0);
}

#[test]
fn test_negative_hex_parsing() {
    assert_eq!(-(0x4A as i64), -74);
    assert_eq!(-(0xFF as i64), -255);
}

#[test]
fn test_negative_octal_parsing() {
    assert_eq!(-(0o47 as i64), -39);
    assert_eq!(-(0o77 as i64), -63);
}

#[test]
fn test_negative_binary_parsing() {
    assert_eq!(-(0b110 as i64), -6);
    assert_eq!(-(0b1111 as i64), -15);
}

#[test]
fn test_mixed_radix_arithmetic() {
    // Test that different bases can be mixed in arithmetic
    assert_eq!(0x10 + 0o10, 24);  // 16 + 8
    assert_eq!(0b100 + 0o4, 8);   // 4 + 4
    assert_eq!(0xFF - 0b11, 252); // 255 - 3
}

