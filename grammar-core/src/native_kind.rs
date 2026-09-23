//! Original native-kind classifier and ordered promotion tables.
//!
//! Relocated intact from ast::language::NativeKind. Only the syntactic wrapper
//! remains in AST: it observes Type::Path's last Ident spelling and calls
//! from_last_path_segment. This module has no AST/syn dependency, carrier
//! inference, canonical-schema alias policy, or new promotion algorithm.
//! NativeKindProjection.v and frozen original tests cover the source boundary.

/// Typed classification of a category's native Rust type.
///
/// Drives the "shared token-family variant" mapping used when desugaring
/// `literals { ... }` entries: every category whose `NativeKind` returns the
/// same `standard_token_variant()` shares one `Token::<name>(payload)` enum
/// variant.
///
/// String comparisons are confined to the single `from_last_path_segment` constructor;
/// all downstream dispatch is by typed `match`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NativeKind {
    Int8,
    Int16,
    Int32,
    Int64,
    Int128,
    Isize,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    UInt128,
    Usize,
    Float32,
    Float64,
    Bool,
    /// `str` or `String`.
    Str,
    /// Any wrapper whose last path segment ends with `"BigInt"` — treated
    /// as the arbitrary-precision integer category.
    CanonicalBigInt,
    /// `CanonicalBigRat` — arbitrary-precision rational.
    CanonicalBigRat,
    /// `CanonicalFixedPoint` — fixed-point decimal.
    CanonicalFixedPoint,
    /// Anything else (custom user wrapper, collection container, etc.).
    Other,
}

impl NativeKind {
    /// Classify the already-observed last path-segment spelling using the
    /// original exact-name match and final BigInt suffix fallback.
    /// This does not parse a type, strip qualification, or normalize aliases.
    pub fn from_last_path_segment(seg: &str) -> Self {
        match seg {
            "i8" => Self::Int8,
            "i16" => Self::Int16,
            "i32" => Self::Int32,
            "i64" => Self::Int64,
            "i128" => Self::Int128,
            "isize" => Self::Isize,
            "u8" => Self::UInt8,
            "u16" => Self::UInt16,
            "u32" => Self::UInt32,
            "u64" => Self::UInt64,
            "u128" => Self::UInt128,
            "usize" => Self::Usize,
            "f32" => Self::Float32,
            "f64" => Self::Float64,
            "bool" => Self::Bool,
            "str" | "String" => Self::Str,
            "CanonicalBigRat" => Self::CanonicalBigRat,
            "CanonicalFixedPoint" => Self::CanonicalFixedPoint,
            other if other.ends_with("BigInt") => Self::CanonicalBigInt,
            _ => Self::Other,
        }
    }

    /// Whether this kind is one of the bounded-integer widths or
    /// `CanonicalBigInt` — i.e. shares `Token::Integer(IntLit)`.
    #[inline]
    pub const fn is_integer(self) -> bool {
        matches!(
            self,
            Self::Int8
                | Self::Int16
                | Self::Int32
                | Self::Int64
                | Self::Int128
                | Self::Isize
                | Self::UInt8
                | Self::UInt16
                | Self::UInt32
                | Self::UInt64
                | Self::UInt128
                | Self::Usize
                | Self::CanonicalBigInt
        )
    }

    /// Standard `Token::<name>` variant family for this native kind.
    ///
    /// Returns `None` for `Other` — caller keeps the user-facing
    /// category name in that case. Callers in `macros` should convert
    /// the result to `TokenFamily` via `TokenFamily::from_name()` for
    /// all subsequent dispatch (single string→enum gateway).
    pub const fn standard_token_variant(self) -> Option<&'static str> {
        match self {
            Self::Float32 | Self::Float64 => Some("Float"),
            Self::Bool => Some("Boolean"),
            Self::Str => Some("StringLit"),
            // CanonicalBigInt / CanonicalBigRat / CanonicalFixedPoint do NOT
            // collapse into a shared family variant — a shared `Token::Integer(i64)`
            // would clamp arbitrary-precision literals like
            // `32478132567813256718n` to i64::MAX. Returning None keeps the
            // declared category name (e.g. `BigInt`, `BigRat`, `Fixed`) as the
            // Token variant with a `&'a str` payload; the category's parse
            // arm then calls `parse_int_lit` / `parse_rational_lit` /
            // `parse_fixed_lit` on the full text — preserving precision.
            Self::CanonicalBigInt => None,
            Self::CanonicalBigRat => None,
            Self::CanonicalFixedPoint => None,
            // Fixed-width integer types collapse onto the shared
            // `Token::Integer(i64)` variant.
            Self::Int8
            | Self::Int16
            | Self::Int32
            | Self::Int64
            | Self::Int128
            | Self::Isize
            | Self::UInt8
            | Self::UInt16
            | Self::UInt32
            | Self::UInt64
            | Self::UInt128
            | Self::Usize => Some("Integer"),
            Self::Other => None,
        }
    }

    // ─────────────────────────────────────────────────────────────────
    // Stage 3.13 — BuiltinTypeLattice (2026-04-30)
    //
    // Lossless / lossy promotion edges between built-in types. Used by:
    // - Stage 3.13 auto-injection codegen — emits cross-cat injection
    //   rules byte-identical to hand-written `IntToBigInt . i:Int |- i : BigInt`.
    // - Stage 3.27f G-INTEGER-OVERFLOW-FORK — emits promotion-Fork
    //   branches for every lossless edge declared in a grammar.
    //
    // Future-proof contract: adding a new built-in type (e.g. Decimal128)
    // only requires (a) a new variant here, (b) updates to `from_last_path_segment`
    // and `standard_token_variant`, (c) new rows in `lossless_targets` /
    // `lossy_targets`. No code change in binder.rs/prefix.rs/auto_inject.rs
    // is needed — the codegen consumes the lattice abstractly.
    // ─────────────────────────────────────────────────────────────────

    /// Return the lossless promotion targets for this kind.
    ///
    /// A lossless edge `Source → Target` means every `Source`-valued
    /// literal can be embedded in `Target` without loss (no truncation,
    /// no precision loss, no representable-range overflow).
    ///
    /// **Auto-emittable:** Stage 3.13 unconditionally emits cross-cat
    /// injection rules for every lossless edge declared in a grammar
    /// (i.e., when both source and target categories are present).
    ///
    /// **Lossless edges:**
    /// - `Bool → Int{8..128}`, `Bool → UInt{8..128}` (false→0, true→1).
    /// - `IntN → IntM` for N ≤ M (signed widening).
    /// - `UIntN → UIntM` for N ≤ M (unsigned widening).
    /// - `UIntN → IntM` for N < M (sign bit available).
    /// - `IntN/UIntN → CanonicalBigInt` (arbitrary precision).
    /// - `CanonicalBigInt → CanonicalBigRat` (Z ⊂ Q).
    /// - `Float32 → Float64` (IEEE 754 widen).
    /// - `Float64 → CanonicalBigRat` (exact via `f64_to_exact_rational`).
    /// - `CanonicalFixedPoint → CanonicalBigRat` (rational with bounded denom).
    ///
    /// Multi-step lossless chains (e.g., `Int32 → CanonicalBigInt →
    /// CanonicalBigRat`) are NOT enumerated explicitly — Stage 3.27f's
    /// promotion-target search is BFS over the direct-edge graph this
    /// function defines.
    pub const fn lossless_targets(self) -> &'static [NativeKind] {
        match self {
            // Bool → all integer widths (false=0, true=1 fits everywhere).
            Self::Bool => &[
                Self::Int8,
                Self::Int16,
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::Isize,
                Self::UInt8,
                Self::UInt16,
                Self::UInt32,
                Self::UInt64,
                Self::UInt128,
                Self::Usize,
                Self::CanonicalBigInt,
                Self::CanonicalBigRat,
            ],

            // Signed integer widening: IntN → IntM for N ≤ M, plus to CanonicalBigInt + CanonicalBigRat.
            Self::Int8 => &[
                Self::Int16,
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::CanonicalBigInt,
                Self::CanonicalBigRat,
            ],
            Self::Int16 => &[
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::CanonicalBigInt,
                Self::CanonicalBigRat,
            ],
            Self::Int32 => {
                &[Self::Int64, Self::Int128, Self::CanonicalBigInt, Self::CanonicalBigRat]
            },
            Self::Int64 => &[Self::Int128, Self::CanonicalBigInt, Self::CanonicalBigRat],
            Self::Int128 => &[Self::CanonicalBigInt, Self::CanonicalBigRat],
            // isize is 32-or-64-bit platform-dependent; treat as Int64-equivalent for lattice purposes.
            Self::Isize => &[Self::Int128, Self::CanonicalBigInt, Self::CanonicalBigRat],

            // Unsigned integer widening: UIntN → UIntM (N ≤ M); UIntN → IntM (N < M, sign bit available).
            Self::UInt8 => &[
                Self::UInt16,
                Self::UInt32,
                Self::UInt64,
                Self::UInt128,
                Self::Int16,
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::CanonicalBigInt,
                Self::CanonicalBigRat,
            ],
            Self::UInt16 => &[
                Self::UInt32,
                Self::UInt64,
                Self::UInt128,
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::CanonicalBigInt,
                Self::CanonicalBigRat,
            ],
            Self::UInt32 => &[
                Self::UInt64,
                Self::UInt128,
                Self::Int64,
                Self::Int128,
                Self::CanonicalBigInt,
                Self::CanonicalBigRat,
            ],
            Self::UInt64 => {
                &[Self::UInt128, Self::Int128, Self::CanonicalBigInt, Self::CanonicalBigRat]
            },
            Self::UInt128 => &[Self::CanonicalBigInt, Self::CanonicalBigRat],
            Self::Usize => {
                &[Self::UInt128, Self::Int128, Self::CanonicalBigInt, Self::CanonicalBigRat]
            },

            // Float widening + exact-to-BigRat.
            Self::Float32 => &[Self::Float64, Self::CanonicalBigRat],
            Self::Float64 => &[Self::CanonicalBigRat],

            // Canonical → CanonicalBigRat (Z ⊂ Q; FixedPoint ⊂ Q).
            Self::CanonicalBigInt => &[Self::CanonicalBigRat],
            Self::CanonicalFixedPoint => &[Self::CanonicalBigRat],

            // Terminal / non-numeric kinds: no lossless targets.
            Self::CanonicalBigRat | Self::Str | Self::Other => &[],
        }
    }

    /// Return the lossy promotion targets for this kind.
    ///
    /// A lossy edge `Source → Target` means SOME `Source` values cannot
    /// be embedded in `Target` without loss — overflow, truncation, or
    /// representable-range mismatch can occur.
    ///
    /// **Opt-in only:** Stage 3.13 auto-injection emits these only when
    /// the user grammar opts in via
    /// `options { auto_inject_lossy: true }` or per-edge
    /// `auto_inject_allow: [...]`.
    ///
    /// **Lossy edges:**
    /// - `IntN → UIntM` (negatives unrepresentable).
    /// - `Float* → IntN` / `Float* → UIntN` (truncation).
    /// - `IntN/UIntN → Float*` (precision loss for wide ints).
    /// - `CanonicalBigRat → CanonicalFixedPoint` (truncation at scale).
    /// - `CanonicalBigRat → IntN/UIntN/Float*` (truncation + range).
    /// - `Bool → Float*` (semantic, not numeric — false→0.0, true→1.0).
    /// - Any → Str / Str → any (format/parse asymmetry).
    pub const fn lossy_targets(self) -> &'static [NativeKind] {
        match self {
            Self::Int8 | Self::Int16 | Self::Int32 | Self::Int64 | Self::Int128 | Self::Isize => &[
                Self::UInt8,
                Self::UInt16,
                Self::UInt32,
                Self::UInt64,
                Self::UInt128,
                Self::Usize,
                Self::Float32,
                Self::Float64,
            ],
            Self::UInt8
            | Self::UInt16
            | Self::UInt32
            | Self::UInt64
            | Self::UInt128
            | Self::Usize => &[Self::Float32, Self::Float64],
            Self::Float32 | Self::Float64 => &[
                Self::Int8,
                Self::Int16,
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::Isize,
                Self::UInt8,
                Self::UInt16,
                Self::UInt32,
                Self::UInt64,
                Self::UInt128,
                Self::Usize,
                Self::CanonicalFixedPoint,
            ],
            Self::Bool => &[Self::Float32, Self::Float64],
            Self::CanonicalBigInt => &[
                Self::Int8,
                Self::Int16,
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::Isize,
                Self::UInt8,
                Self::UInt16,
                Self::UInt32,
                Self::UInt64,
                Self::UInt128,
                Self::Usize,
                Self::Float32,
                Self::Float64,
            ],
            Self::CanonicalBigRat => &[
                Self::CanonicalBigInt,
                Self::Int8,
                Self::Int16,
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::Isize,
                Self::UInt8,
                Self::UInt16,
                Self::UInt32,
                Self::UInt64,
                Self::UInt128,
                Self::Usize,
                Self::Float32,
                Self::Float64,
                Self::CanonicalFixedPoint,
            ],
            Self::CanonicalFixedPoint => &[
                Self::Int8,
                Self::Int16,
                Self::Int32,
                Self::Int64,
                Self::Int128,
                Self::Isize,
                Self::UInt8,
                Self::UInt16,
                Self::UInt32,
                Self::UInt64,
                Self::UInt128,
                Self::Usize,
                Self::Float32,
                Self::Float64,
                Self::CanonicalBigInt,
            ],
            Self::Str | Self::Other => &[],
        }
    }

    /// BFS over the lossless-edge graph from `self`, yielding
    /// `(reachable_kind, distance)` pairs in shortest-path order.
    ///
    /// **Used by:** Stage 3.27f G-INTEGER-OVERFLOW-FORK to enumerate all
    /// admissible promotion targets for a built-in literal (cost weighted
    /// by distance).
    pub fn lossless_promotion_chain(self) -> Vec<(NativeKind, u8)> {
        use std::collections::VecDeque;
        let mut seen: Vec<NativeKind> = vec![self];
        let mut out: Vec<(NativeKind, u8)> = Vec::new();
        let mut queue: VecDeque<(NativeKind, u8)> = VecDeque::new();
        queue.push_back((self, 0));
        while let Some((kind, distance)) = queue.pop_front() {
            for &target in kind.lossless_targets() {
                if seen.contains(&target) {
                    continue;
                }
                seen.push(target);
                let next_dist = distance.saturating_add(1);
                out.push((target, next_dist));
                queue.push_back((target, next_dist));
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::NativeKind;

    #[test]
    fn native_kind_core_classifier_uses_original_names_without_ast_or_type_parser() {
        use NativeKind::*;
        for (segment, expected) in [
            ("i8", Int8),
            ("i16", Int16),
            ("i32", Int32),
            ("i64", Int64),
            ("i128", Int128),
            ("isize", Isize),
            ("u8", UInt8),
            ("u16", UInt16),
            ("u32", UInt32),
            ("u64", UInt64),
            ("u128", UInt128),
            ("usize", Usize),
            ("f32", Float32),
            ("f64", Float64),
            ("bool", Bool),
            ("str", Str),
            ("String", Str),
            ("CanonicalBigRat", CanonicalBigRat),
            ("CanonicalFixedPoint", CanonicalFixedPoint),
            ("CanonicalBigInt", CanonicalBigInt),
            ("Opaque", Other),
            ("UserBigInt", CanonicalBigInt),
            ("r#BigInt", CanonicalBigInt),
            ("r#String", Other),
            ("UserBigRat", Other),
            ("BigRat", Other),
            ("Fixed", Other),
            ("", Other),
            ("module::i32", Other),
            ("i32<Opaque>", Other),
            ("&i32", Other),
        ] {
            assert_eq!(NativeKind::from_last_path_segment(segment), expected, "{segment}");
        }
    }
}
