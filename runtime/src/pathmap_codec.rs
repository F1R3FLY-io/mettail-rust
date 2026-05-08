//! Path segment codec for pathmap crate integration.
//!
//! This module provides deterministic encoding for multi-segment paths into a
//! single byte key consumed by the `pathmap` crate.

/// Segment delimiter byte used in encoded keys.
pub const SEGMENT_DELIM: u8 = 0xFF;
/// Escape byte used to encode literal delimiter bytes inside segments.
pub const ESCAPE_BYTE: u8 = 0xFE;

/// Flatten byte segments into one key using delimiter + escaping.
///
/// Encoding rules:
/// - `SEGMENT_DELIM` inside segment is escaped as `ESCAPE_BYTE, 0x01`
/// - `ESCAPE_BYTE` inside segment is escaped as `ESCAPE_BYTE, 0x00`
/// - Segment boundaries are marked with trailing `SEGMENT_DELIM`
pub fn flatten_segments(segments: &[Vec<u8>]) -> Vec<u8> {
    let mut out = Vec::new();
    for segment in segments {
        for byte in segment {
            match *byte {
                ESCAPE_BYTE => {
                    out.push(ESCAPE_BYTE);
                    out.push(0x00);
                },
                SEGMENT_DELIM => {
                    out.push(ESCAPE_BYTE);
                    out.push(0x01);
                },
                b => out.push(b),
            }
        }
        out.push(SEGMENT_DELIM);
    }
    out
}

/// Restore flattened key back into path segments.
///
/// Invalid or truncated escape sequences are preserved as literal bytes to keep
/// decoding total and deterministic.
pub fn unflatten_segments(flattened: &[u8]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut current = Vec::new();
    let mut i = 0;
    while i < flattened.len() {
        let byte = flattened[i];
        if byte == SEGMENT_DELIM {
            out.push(std::mem::take(&mut current));
            i += 1;
            continue;
        }
        if byte == ESCAPE_BYTE {
            if i + 1 >= flattened.len() {
                current.push(ESCAPE_BYTE);
                i += 1;
                continue;
            }
            match flattened[i + 1] {
                0x00 => current.push(ESCAPE_BYTE),
                0x01 => current.push(SEGMENT_DELIM),
                other => {
                    current.push(ESCAPE_BYTE);
                    current.push(other);
                },
            }
            i += 2;
            continue;
        }
        current.push(byte);
        i += 1;
    }
    if !current.is_empty() {
        out.push(current);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{flatten_segments, unflatten_segments, ESCAPE_BYTE, SEGMENT_DELIM};

    #[test]
    fn round_trip_plain_segments() {
        let segments = vec![b"foo".to_vec(), b"bar".to_vec(), b"baz".to_vec()];
        let encoded = flatten_segments(&segments);
        assert_eq!(unflatten_segments(&encoded), segments);
    }

    #[test]
    fn round_trip_escape_and_delimiter_bytes() {
        let segments = vec![
            vec![1, 2, ESCAPE_BYTE, 3],
            vec![9, SEGMENT_DELIM, 10],
            vec![ESCAPE_BYTE, SEGMENT_DELIM],
        ];
        let encoded = flatten_segments(&segments);
        assert_eq!(unflatten_segments(&encoded), segments);
    }
}
