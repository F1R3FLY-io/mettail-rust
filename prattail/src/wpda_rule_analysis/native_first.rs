//! Original native literal-family election and FIRST/home row construction.
//!
//! These are the original `wpda_codegen::prefix` helpers with borrowed source
//! observations and quotation constructors substituted at their original sites.
//! `NativeFirstDescriptorProjection.v` covers the finite lookup/constructor
//! boundary, including lazy gates, first matches, row order, and the discarded
//! first home-arm construction. It does not infer native kinds from carriers,
//! execute Rust literal bodies, admit arbitrary readers, or establish allocation
//! bounds. Adapters must preserve source order, spelling, optional presence, and
//! the original `NativeKind::from_syn_type` result.

use mettail_ast::language::NativeKind;

/// The original lexer's literal-pattern family, not a native carrier taxonomy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiteralFamily {
    /// Bounded signed/unsigned integers and CanonicalBigInt.
    Integer,
    Rational,
    FixedPoint,
    Float,
    /// One alternative-pattern row: True | False | BooleanLit.
    Boolean,
    String,
    /// Elected only by a declared literal with an evaluation body on a category
    /// whose present native type has no builtin family. Other alone is insufficient.
    Custom,
}

/// Original context controlling the bare Integer arm.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EmissionContext {
    /// Includes the bare integer reading, including CanonicalBigInt.
    HomeCategory,
    /// Includes bare Integer only for primitive widths or an absent kind.
    FirstSet,
}

/// Requests for the eight ORIGINAL quotation sites, not semantic token equality
/// or a new lexer taxonomy. BooleanAlternative is one construction, not three.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativePatternSite {
    IntegerTyped,
    CustomTyped,
    RationalTyped,
    FixedPointTyped,
    FloatBare,
    BooleanAlternative,
    StringBare,
    IntegerBare,
}

/// Original token/guard construction callbacks. Static quotation stays in the
/// macro adapter; another lawful consumer can retain neutral constructor data.
pub trait NativeFirstConstructors {
    type Pattern;

    fn pattern(&mut self, site: NativePatternSite) -> Self::Pattern;
    fn category_guard(&mut self, category: &str) -> Self::Pattern;
}

/// First authored literal declaration carrying an evaluation body.
///
/// The callbacks are invoked in the original lazy `&&` order; category spelling
/// is not observed before both flags succeed. The returned borrowed declaration
/// retains its complete payload and original identity. No token-name, decoder,
/// evaluation, or carrier inference substitutes for these authored observations.
pub fn declared_literal_token_def<'source, T>(
    cat_name: &str,
    tokens: &'source [T],
    mut from_literals: impl FnMut(&T) -> bool,
    mut has_rust_code: impl FnMut(&T) -> bool,
    mut category: impl FnMut(&T) -> Option<String>,
) -> Option<&'source T> {
    tokens.iter().find(|token| {
        from_literals(token)
            && has_rust_code(token)
            && category(token).is_some_and(|name| name == cat_name)
    })
}

/// Original category-level family election. First spelling match wins, even if
/// its native type is absent. The native-presence and kind-resolution callbacks
/// remain separate; only a present Other kind consults the declared-literal gate.
pub fn literal_family_for_category<'source, C, N>(
    cat_name: &str,
    categories: &'source [C],
    mut category_name: impl FnMut(&C) -> String,
    mut native_type: impl FnMut(&'source C) -> Option<N>,
    mut native_kind: impl FnMut(N) -> NativeKind,
    mut has_declared_literal: impl FnMut(&str) -> bool,
) -> Option<LiteralFamily> {
    let lang_type = categories.iter().find(|ty| category_name(ty) == cat_name)?;
    let native_type = native_type(lang_type)?;
    match literal_family_for(&native_kind(native_type)) {
        Some(family) => Some(family),
        None if has_declared_literal(cat_name) => Some(LiteralFamily::Custom),
        None => None,
    }
}

/// Original exhaustive NativeKind match. Custom is a declaration property and
/// is intentionally not returned by this native-only helper.
pub fn literal_family_for(kind: &NativeKind) -> Option<LiteralFamily> {
    match kind {
        NativeKind::Int8
        | NativeKind::Int16
        | NativeKind::Int32
        | NativeKind::Int64
        | NativeKind::Int128
        | NativeKind::Isize
        | NativeKind::UInt8
        | NativeKind::UInt16
        | NativeKind::UInt32
        | NativeKind::UInt64
        | NativeKind::UInt128
        | NativeKind::Usize
        | NativeKind::CanonicalBigInt => Some(LiteralFamily::Integer),
        NativeKind::CanonicalBigRat => Some(LiteralFamily::Rational),
        NativeKind::CanonicalFixedPoint => Some(LiteralFamily::FixedPoint),
        NativeKind::Float32 | NativeKind::Float64 => Some(LiteralFamily::Float),
        NativeKind::Bool => Some(LiteralFamily::Boolean),
        NativeKind::Str => Some(LiteralFamily::String),
        NativeKind::Other => None,
    }
}

/// Original family-keyed home arm. Only Integer has a bare polymorphic token.
pub fn home_polymorphic_token_arm<C: NativeFirstConstructors>(
    family: LiteralFamily,
    constructors: &mut C,
) -> Option<C::Pattern> {
    match family {
        LiteralFamily::Integer => Some(constructors.pattern(NativePatternSite::IntegerBare)),
        LiteralFamily::Rational
        | LiteralFamily::FixedPoint
        | LiteralFamily::Float
        | LiteralFamily::Boolean
        | LiteralFamily::String
        | LiteralFamily::Custom => None,
    }
}

/// Original ordered row construction, including its exact home-helper schedule.
/// Native kinds need not agree with the supplied family: the original helper
/// accepted such inputs, and its Integer FIRST gate remains exact for them.
pub fn literal_patterned_pattern_and_guard_for_kind<C: NativeFirstConstructors>(
    cat_name: &str,
    family: LiteralFamily,
    kind: Option<&NativeKind>,
    ctx: EmissionContext,
    constructors: &mut C,
) -> Vec<(C::Pattern, Option<C::Pattern>)> {
    match family {
        LiteralFamily::Integer => {
            let mut arms = vec![
                (
                    constructors.pattern(NativePatternSite::IntegerTyped),
                    Some(constructors.category_guard(cat_name)),
                ),
                (
                    constructors.pattern(NativePatternSite::CustomTyped),
                    Some(constructors.category_guard(cat_name)),
                ),
            ];
            let emit_bare_arm = match ctx {
                EmissionContext::HomeCategory => {
                    home_polymorphic_token_arm(family, constructors).is_some()
                },
                EmissionContext::FirstSet => matches!(
                    kind,
                    None | Some(NativeKind::Int8)
                        | Some(NativeKind::Int16)
                        | Some(NativeKind::Int32)
                        | Some(NativeKind::Int64)
                        | Some(NativeKind::Int128)
                        | Some(NativeKind::Isize)
                        | Some(NativeKind::UInt8)
                        | Some(NativeKind::UInt16)
                        | Some(NativeKind::UInt32)
                        | Some(NativeKind::UInt64)
                        | Some(NativeKind::UInt128)
                        | Some(NativeKind::Usize)
                ),
            };
            if emit_bare_arm {
                if let Some(pat) = home_polymorphic_token_arm(family, constructors) {
                    arms.push((pat, None));
                }
            }
            arms
        },
        LiteralFamily::Rational => vec![
            (
                constructors.pattern(NativePatternSite::RationalTyped),
                Some(constructors.category_guard(cat_name)),
            ),
            (
                constructors.pattern(NativePatternSite::CustomTyped),
                Some(constructors.category_guard(cat_name)),
            ),
        ],
        LiteralFamily::FixedPoint => vec![
            (
                constructors.pattern(NativePatternSite::FixedPointTyped),
                Some(constructors.category_guard(cat_name)),
            ),
            (
                constructors.pattern(NativePatternSite::CustomTyped),
                Some(constructors.category_guard(cat_name)),
            ),
        ],
        LiteralFamily::Float => {
            vec![(constructors.pattern(NativePatternSite::FloatBare), None)]
        },
        LiteralFamily::Boolean => {
            vec![(constructors.pattern(NativePatternSite::BooleanAlternative), None)]
        },
        LiteralFamily::String => {
            vec![(constructors.pattern(NativePatternSite::StringBare), None)]
        },
        LiteralFamily::Custom => vec![(
            constructors.pattern(NativePatternSite::CustomTyped),
            Some(constructors.category_guard(cat_name)),
        )],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    #[derive(Debug, Clone, PartialEq, Eq)]
    enum Payload {
        Pattern(NativePatternSite, usize),
        Guard(String, usize),
    }

    #[derive(Default)]
    struct TraceConstructors(Vec<Payload>);

    impl NativeFirstConstructors for TraceConstructors {
        type Pattern = Payload;

        fn pattern(&mut self, site: NativePatternSite) -> Payload {
            let payload = Payload::Pattern(site, self.0.len());
            self.0.push(payload.clone());
            payload
        }

        fn category_guard(&mut self, category: &str) -> Payload {
            let payload = Payload::Guard(category.into(), self.0.len());
            self.0.push(payload.clone());
            payload
        }
    }

    #[test]
    fn native_first_neutral_home_discards_first_bare_payload_at_original_site() {
        use NativePatternSite::*;
        let mut constructors = TraceConstructors::default();
        let rows = literal_patterned_pattern_and_guard_for_kind(
            "Value",
            LiteralFamily::Integer,
            Some(&NativeKind::CanonicalBigInt),
            EmissionContext::HomeCategory,
            &mut constructors,
        );
        assert_eq!(
            constructors.0,
            vec![
                Payload::Pattern(IntegerTyped, 0),
                Payload::Guard("Value".into(), 1),
                Payload::Pattern(CustomTyped, 2),
                Payload::Guard("Value".into(), 3),
                Payload::Pattern(IntegerBare, 4),
                Payload::Pattern(IntegerBare, 5),
            ]
        );
        assert_eq!(
            rows,
            vec![
                (Payload::Pattern(IntegerTyped, 0), Some(Payload::Guard("Value".into(), 1))),
                (Payload::Pattern(CustomTyped, 2), Some(Payload::Guard("Value".into(), 3))),
                (Payload::Pattern(IntegerBare, 5), None),
            ]
        );
    }

    #[test]
    fn native_first_neutral_first_calls_bare_constructor_once_or_never() {
        for (kind, has_bare) in [
            (None, true),
            (Some(NativeKind::UInt128), true),
            (Some(NativeKind::CanonicalBigInt), false),
            (Some(NativeKind::Other), false),
        ] {
            let mut constructors = TraceConstructors::default();
            let rows = literal_patterned_pattern_and_guard_for_kind(
                "Value",
                LiteralFamily::Integer,
                kind.as_ref(),
                EmissionContext::FirstSet,
                &mut constructors,
            );
            assert_eq!(constructors.0.len(), if has_bare { 5 } else { 4 });
            assert_eq!(rows.len(), if has_bare { 3 } else { 2 });
            if has_bare {
                assert_eq!(rows[2], (Payload::Pattern(NativePatternSite::IntegerBare, 4), None));
            }
        }
    }

    #[test]
    fn native_first_neutral_boolean_is_one_unconditional_constructor() {
        let mut constructors = TraceConstructors::default();
        let rows = literal_patterned_pattern_and_guard_for_kind(
            "Ignored",
            LiteralFamily::Boolean,
            Some(&NativeKind::Other),
            EmissionContext::HomeCategory,
            &mut constructors,
        );
        let payload = Payload::Pattern(NativePatternSite::BooleanAlternative, 0);
        assert_eq!(constructors.0, vec![payload.clone()]);
        assert_eq!(rows, vec![(payload, None)]);
    }

    #[test]
    fn native_first_neutral_token_lookup_is_lazy_and_returns_original_handle() {
        struct Token {
            id: usize,
            declared: bool,
            eval: bool,
            category: Option<&'static str>,
        }
        let tokens = [
            Token {
                id: 0,
                declared: false,
                eval: true,
                category: Some("Value"),
            },
            Token {
                id: 1,
                declared: true,
                eval: false,
                category: Some("Value"),
            },
            Token {
                id: 2,
                declared: true,
                eval: true,
                category: None,
            },
            Token {
                id: 3,
                declared: true,
                eval: true,
                category: Some("Value"),
            },
            Token {
                id: 4,
                declared: true,
                eval: true,
                category: Some("Value"),
            },
        ];
        let trace = RefCell::new(Vec::new());
        let selected = declared_literal_token_def(
            "Value",
            &tokens,
            |token| {
                trace.borrow_mut().push((token.id, "declared"));
                token.declared
            },
            |token| {
                trace.borrow_mut().push((token.id, "eval"));
                token.eval
            },
            |token| {
                trace.borrow_mut().push((token.id, "category"));
                token.category.map(str::to_owned)
            },
        )
        .expect("the fourth token is first eligible");
        assert!(std::ptr::eq(selected, &tokens[3]));
        assert_eq!(
            trace.into_inner(),
            vec![
                (0, "declared"),
                (1, "declared"),
                (1, "eval"),
                (2, "declared"),
                (2, "eval"),
                (2, "category"),
                (3, "declared"),
                (3, "eval"),
                (3, "category"),
            ]
        );
    }

    #[test]
    fn native_first_neutral_category_presence_resolution_and_literal_gates() {
        struct Category {
            id: usize,
            name: &'static str,
            native: Option<NativeKind>,
        }
        for (native, expected, expected_tail) in [
            (None, None, vec![]),
            (Some(NativeKind::Int32), Some(LiteralFamily::Integer), vec![(1, "kind")]),
            (
                Some(NativeKind::Other),
                Some(LiteralFamily::Custom),
                vec![(1, "kind"), (1, "literal")],
            ),
        ] {
            let categories = [
                Category {
                    id: 0,
                    name: "Different",
                    native: Some(NativeKind::Bool),
                },
                Category { id: 1, name: "Value", native },
                Category {
                    id: 2,
                    name: "Value",
                    native: Some(NativeKind::Str),
                },
            ];
            let trace = RefCell::new(Vec::new());
            let actual = literal_family_for_category(
                "Value",
                &categories,
                |category| {
                    trace.borrow_mut().push((category.id, "name"));
                    category.name.into()
                },
                |category| {
                    trace.borrow_mut().push((category.id, "presence"));
                    category.native.as_ref()
                },
                |kind| {
                    trace.borrow_mut().push((1, "kind"));
                    *kind
                },
                |name| {
                    assert_eq!(name, "Value");
                    trace.borrow_mut().push((1, "literal"));
                    true
                },
            );
            assert_eq!(actual, expected);
            let mut expected_trace = vec![(0, "name"), (1, "name"), (1, "presence")];
            expected_trace.extend(expected_tail);
            assert_eq!(trace.into_inner(), expected_trace);
        }
    }
}
