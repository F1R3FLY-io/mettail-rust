//! Byte-framed semantic-key hasher for generated term identity.
//!
//! Generated languages write semantic identity through Rust's [`Hasher`]
//! interface. This hasher records the write stream as framed bytes rather than
//! reducing it to `u64`, so callers can use the resulting vector as an exact
//! key for deduplication and runtime reports.

use std::hash::Hasher;

/// Exact byte-key hasher compatible with generated `semantic_hash` methods.
#[derive(Default, Debug, Clone)]
pub struct FramedSemanticKeyHasher {
    bytes: Vec<u8>,
}

impl FramedSemanticKeyHasher {
    /// Return the exact framed byte stream written so far.
    pub fn into_key(self) -> Vec<u8> {
        self.bytes
    }

    fn push_raw(&mut self, tag: u8, payload: &[u8]) {
        self.bytes.push(tag);
        self.bytes
            .extend_from_slice(&(payload.len() as u64).to_le_bytes());
        self.bytes.extend_from_slice(payload);
    }

    fn push_fixed(&mut self, tag: u8, payload: &[u8]) {
        self.bytes.push(tag);
        self.bytes.extend_from_slice(payload);
    }
}

impl Hasher for FramedSemanticKeyHasher {
    fn finish(&self) -> u64 {
        let mut h = 0xcbf29ce484222325u64;
        for b in &self.bytes {
            h ^= u64::from(*b);
            h = h.wrapping_mul(0x100000001b3);
        }
        h
    }

    fn write(&mut self, bytes: &[u8]) {
        self.push_raw(0, bytes);
    }

    fn write_u8(&mut self, i: u8) {
        self.push_fixed(1, &[i]);
    }

    fn write_u16(&mut self, i: u16) {
        self.push_fixed(2, &i.to_le_bytes());
    }

    fn write_u32(&mut self, i: u32) {
        self.push_fixed(3, &i.to_le_bytes());
    }

    fn write_u64(&mut self, i: u64) {
        self.push_fixed(4, &i.to_le_bytes());
    }

    fn write_u128(&mut self, i: u128) {
        self.push_fixed(5, &i.to_le_bytes());
    }

    fn write_usize(&mut self, i: usize) {
        self.push_fixed(6, &(i as u128).to_le_bytes());
    }

    fn write_i8(&mut self, i: i8) {
        self.push_fixed(7, &i.to_le_bytes());
    }

    fn write_i16(&mut self, i: i16) {
        self.push_fixed(8, &i.to_le_bytes());
    }

    fn write_i32(&mut self, i: i32) {
        self.push_fixed(9, &i.to_le_bytes());
    }

    fn write_i64(&mut self, i: i64) {
        self.push_fixed(10, &i.to_le_bytes());
    }

    fn write_i128(&mut self, i: i128) {
        self.push_fixed(11, &i.to_le_bytes());
    }

    fn write_isize(&mut self, i: isize) {
        self.push_fixed(12, &(i as i128).to_le_bytes());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raw_writes_are_length_framed() {
        let mut lhs = FramedSemanticKeyHasher::default();
        lhs.write(b"ab");

        let mut rhs = FramedSemanticKeyHasher::default();
        rhs.write(b"a");
        rhs.write(b"b");

        assert_ne!(lhs.into_key(), rhs.into_key());
    }

    #[test]
    fn typed_primitive_writes_are_tagged() {
        let mut raw = FramedSemanticKeyHasher::default();
        raw.write(&[1]);

        let mut typed = FramedSemanticKeyHasher::default();
        typed.write_u8(1);

        assert_ne!(raw.into_key(), typed.into_key());
    }
}
