//! Original atomic-rule classification over shared, shallow observations.
//!
//! The judgement and legacy branch order is retained from the macro backend.
//! Resolvers are lazy: rejected judgement syntax never falls back to legacy
//! literal lookup. Native evaluation remains an opaque caller-owned payload.
//! `AtomicClassifierProjection.v` models the observation and callback boundary;
//! it does not certify literal evaluation or the complete runtime parser.

use super::{InfixParamShape, InfixRuleShape, InfixSyntaxShape, InfixTypeShape};

/// Exact legacy nonterminal discriminants; never inferred from a name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LegacyAtomicKind {
    Integer,
    Boolean,
    StringLiteral,
    FloatLiteral,
    Var,
    Ident,
    Category,
}

/// Every legacy position is retained, including unsupported ones.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LegacyAtomicItem {
    NonTerminal { kind: LegacyAtomicKind, ident: String },
    Terminal(String),
    Other,
}

/// Result of the existing same-category unary classifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicUnaryPrefix {
    pub trigger: String,
    pub operand_category: String,
}

/// Original atomic shapes with caller-owned literal payloads and plain names.
///
/// Static callers retain their original identifier objects when materializing
/// wrapper variants. The literal payload is neither inspected nor evaluated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AtomicDescriptor<L> {
    LiteralInteger,
    LiteralBoolean,
    LiteralString,
    LiteralFloat,
    LiteralPatterned(L),
    TerminalKeyword {
        terminal_text: String,
        wrapper_variant: String,
    },
    NullaryLiteralRun {
        trigger: String,
        trailing_literals: Vec<String>,
        wrapper_variant: String,
    },
    VarRule {
        wrapper_variant: String,
    },
    CrossCatProjection {
        source_cat_name: String,
        wrapper_variant: String,
    },
    CrossCatPrefixUnary {
        trigger: String,
        source_cat_name: String,
        wrapper_variant: String,
    },
    PrefixOperator {
        trigger: String,
        operand_cat_name: String,
    },
    NonAtomic,
}

/// Apply the original classifier, invoking each resolver only at its original
/// decision site. No parser, literal evaluator, or native-type taxonomy lives here.
pub fn classify_atomic<L>(
    rule: &InfixRuleShape,
    items: &[LegacyAtomicItem],
    unary_prefix: impl FnOnce() -> Option<AtomicUnaryPrefix>,
    literal: impl FnOnce(&str) -> Option<L>,
) -> AtomicDescriptor<L> {
    // Judgement-style rules: check `term_context` + `syntax_pattern` to
    // recognize TerminalKeyword (empty context, single literal pattern).
    if let (Some(tc), Some(sp)) = (&rule.term_context, &rule.syntax_pattern) {
        // Nullary rule with a single terminal literal pattern → TerminalKeyword.
        // Example: `Err . |- "error" : Int` (tc=[], sp=[Literal("error")]).
        if tc.is_empty() && sp.len() == 1 {
            if let InfixSyntaxShape::Literal(text) = &sp[0] {
                return AtomicDescriptor::TerminalKeyword {
                    terminal_text: text.clone(),
                    wrapper_variant: rule.label.clone(),
                };
            }
        }
        // GAP-3 (2026-06-28): 0-operand MULTI-literal keyword-prefix rule
        // (`Map "(" ")"`, `Pathmap "(" ")"`, `@ Nil`). Empty term-context AND
        // two-or-more syntax items that are ALL `Literal` (no `Param`/`Op`).
        // The first literal is the dispatch trigger; the rest are consumed by
        // the reused `MixfixLiteralRun { kind: 2, parts_len == 0 }` arm.
        //
        // Placement safety: `tc.is_empty()` means the CrossCat* blocks below
        // (which require `tc.len() == 1`) can never match these rules, and the
        // all-`Literal` guard excludes every `Param`/`Op`-bearing shape (PPar,
        // POutput, etc. carry a `Param` ⇒ untouched). The single-literal case
        // already returned above as `TerminalKeyword`, so here `sp.len() >= 2`.
        if tc.is_empty()
            && sp.len() >= 2
            && sp.iter().all(|e| matches!(e, InfixSyntaxShape::Literal(_)))
        {
            let mut literals = sp.iter().filter_map(|e| match e {
                InfixSyntaxShape::Literal(t) => Some(t.clone()),
                _ => None,
            });
            let trigger = literals
                .next()
                .expect("classify_atomic: sp.len() >= 2 guarantees a first literal");
            let trailing_literals: Vec<String> = literals.collect();
            return AtomicDescriptor::NullaryLiteralRun {
                trigger,
                trailing_literals,
                wrapper_variant: rule.label.clone(),
            };
        }
        // Stage 1.1: cross-category projection (e.g. `ProcInt . i:Int |- i : Proc`,
        // `CastBigRat . r:BigRat |- r : Proc`). One Simple param of base type,
        // syntax_pattern is just `Param(name)`, source_cat ≠ result_cat.
        if tc.len() == 1 && sp.len() == 1 {
            if let InfixParamShape::Simple { name: param_name, ty } = &tc[0] {
                if let InfixSyntaxShape::Param(syn_name) = &sp[0] {
                    if syn_name == param_name {
                        if let InfixTypeShape::Base(source_ident) = ty {
                            let source_cat = source_ident.to_string();
                            if source_cat != rule.category.to_string() {
                                return AtomicDescriptor::CrossCatProjection {
                                    source_cat_name: source_cat,
                                    wrapper_variant: rule.label.clone(),
                                };
                            }
                        }
                    }
                }
            }
        }
        // Stage 1.1: cross-category prefix unary (e.g. `LenStr . s:Str |- "len" s : Int`).
        // Two-element syntax_pattern: Literal + Param, single Simple param,
        // source_cat ≠ result_cat. NOT a normal Pratt prefix (which has
        // operand of same category as the result).
        if tc.len() == 1 && sp.len() == 2 {
            if let (InfixSyntaxShape::Literal(trigger), InfixSyntaxShape::Param(syn_name)) =
                (&sp[0], &sp[1])
            {
                if let InfixParamShape::Simple { name: param_name, ty } = &tc[0] {
                    // ⚠ AN `Ident` OPERAND IS NOT A CROSS-CATEGORY SOURCE. Without this
                    // guard, `Tagged . m:Ident |- "tag" m : Num` matched the
                    // `Literal + Param` shape and classified as `CrossCatPrefixUnary`,
                    // whose prefix arm routes the trigger to
                    // `WpdaState::CrossCatDelegate` and DESCENDS INTO A CATEGORY. Three
                    // consequences, all measured on #131: the walker never entered
                    // `WpdaState::BinderRule`, so the `IdentTextCapture` fork emitted into
                    // `binder_rule_c<cat>_r<rule>` was never executed (an instrumented gate
                    // logged ZERO hits); the action's arg slot instead held the delegate's
                    // `Term { type_name: "RealizedTerm" }`; and both fork-action twins
                    // failed byte-identically, because an unexecuted fork cannot depend on
                    // its action kind.
                    //
                    // Falling through leaves the rule to `classify_binder_in`, which admits
                    // it (its `sp[0]` IS a `Literal` trigger) and routes it to
                    // `UnifiedDescriptor::BinderPrefix` → `WpdaState::BinderRule` — the
                    // dispatcher that actually calls the capture fork.
                    if ty.is_ident_text() {
                        // fall through to the binder-rule classification below
                    } else if syn_name == param_name {
                        if let InfixTypeShape::Base(source_ident) = ty {
                            let source_cat = source_ident.to_string();
                            if source_cat != rule.category.to_string() {
                                return AtomicDescriptor::CrossCatPrefixUnary {
                                    trigger: trigger.clone(),
                                    source_cat_name: source_cat,
                                    wrapper_variant: rule.label.clone(),
                                };
                            }
                        }
                    }
                }
            }
        }
        // M6c.6.4.b (2026-05-14): same-cat unary prefix (e.g.,
        // `Neg . a:Int |- "-" a : Int`). Recognized via the existing
        // `builtin_metadata::classify_unary_prefix_shape` (operand
        // category == rule.category guard already enforced there).
        // Emits `AtomicDescriptor::PrefixOperator` so the lex-Fork can
        // bind `Fixed(trigger)` → this rule's `LexAltPrefixOp` branch.
        if let Some(shape) = unary_prefix() {
            return AtomicDescriptor::PrefixOperator {
                trigger: shape.trigger,
                operand_cat_name: shape.operand_category,
            };
        }
        // Other judgement-style rules need Phase A.3+ emission.
        return AtomicDescriptor::NonAtomic;
    }

    if items.len() != 1 {
        return AtomicDescriptor::NonAtomic;
    }

    match &items[0] {
        LegacyAtomicItem::NonTerminal { kind, ident } => match kind {
            LegacyAtomicKind::Integer => AtomicDescriptor::LiteralInteger,
            LegacyAtomicKind::Boolean => AtomicDescriptor::LiteralBoolean,
            LegacyAtomicKind::StringLiteral => AtomicDescriptor::LiteralString,
            LegacyAtomicKind::FloatLiteral => AtomicDescriptor::LiteralFloat,
            LegacyAtomicKind::Var => {
                // Phase 5a: synthetic Var rule for user-defined category.
                // Rule shape: single-item NonTerminal(Var, cat) where
                // `rule.category == ident`. Label is the Var-variant label
                // (TVar / PVar / etc.) — use rule.label directly.
                if rule.category == *ident {
                    AtomicDescriptor::VarRule { wrapper_variant: rule.label.clone() }
                } else {
                    AtomicDescriptor::NonAtomic
                }
            },
            // A rule whose ENTIRE body is one `Ident` is not an atomic literal rule: it
            // would accept any identifier as a whole term of the category, which is what
            // `LegacyAtomicKind::Var` exists for (and which carries the binder semantics an
            // inert `Ident` must not have). `Ident` is a MID-RULE position kind; a
            // single-item `Ident` rule has no atomic shape.
            LegacyAtomicKind::Ident => AtomicDescriptor::NonAtomic,
            LegacyAtomicKind::Category => {
                // LiteralPatterned detection: rule body is a single category
                // reference AND that category has a `from_literals` TokenDef
                // AND the rule's OWN category equals the referenced category
                // (so cross-cat projections like `ProcInt . i:Int |- i : Proc`
                // are NOT misclassified — they belong to Phase 3 cross-cat).
                if rule.category != *ident {
                    return AtomicDescriptor::NonAtomic;
                }
                literal(ident)
                    .map(AtomicDescriptor::LiteralPatterned)
                    .unwrap_or(AtomicDescriptor::NonAtomic)
            },
        },
        LegacyAtomicItem::Terminal(text) => AtomicDescriptor::TerminalKeyword {
            terminal_text: text.clone(),
            wrapper_variant: rule.label.clone(),
        },
        _ => AtomicDescriptor::NonAtomic,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    fn rule() -> InfixRuleShape {
        InfixRuleShape {
            label: "Wrapper".into(),
            category: "Int".into(),
            is_right_assoc: false,
            shares_level_with_previous: false,
            term_context: None,
            syntax_pattern: None,
        }
    }

    #[test]
    fn atomic_callbacks_preserve_judgement_priority_and_no_legacy_fallback() {
        let items = [LegacyAtomicItem::NonTerminal {
            kind: LegacyAtomicKind::Category,
            ident: "Int".into(),
        }];
        let mut rule = rule();
        rule.term_context = Some(vec![]);
        rule.syntax_pattern = Some(vec![InfixSyntaxShape::Literal("keyword".into())]);
        let result: AtomicDescriptor<()> = classify_atomic(
            &rule,
            &items,
            || panic!("earlier judgement success must not invoke unary resolver"),
            |_| panic!("judgement syntax must not invoke literal resolver"),
        );
        assert_eq!(
            result,
            AtomicDescriptor::TerminalKeyword {
                terminal_text: "keyword".into(),
                wrapper_variant: "Wrapper".into(),
            }
        );
        rule.syntax_pattern = Some(vec![]);
        let calls = RefCell::new(Vec::new());
        let result: AtomicDescriptor<()> = classify_atomic(
            &rule,
            &items,
            || {
                calls.borrow_mut().push("unary");
                None
            },
            |_| panic!("rejected judgement must not fall back to legacy lookup"),
        );
        assert_eq!(result, AtomicDescriptor::NonAtomic);
        assert_eq!(*calls.borrow(), ["unary"]);
    }

    #[test]
    fn atomic_literal_callback_is_lazy_and_returns_the_original_owned_payload() {
        let rule = rule();
        let payload = Box::new(71_u64);
        let pointer = (&*payload) as *const u64;
        let calls = RefCell::new(Vec::new());
        let result = classify_atomic(
            &rule,
            &[LegacyAtomicItem::NonTerminal {
                kind: LegacyAtomicKind::Category,
                ident: "Int".into(),
            }],
            || panic!("legacy syntax must not invoke unary resolver"),
            |name| {
                assert_eq!(name, "Int");
                calls.borrow_mut().push("literal");
                Some(payload)
            },
        );
        let AtomicDescriptor::LiteralPatterned(actual) = result else {
            panic!("matching singleton category must retain its resolved payload");
        };
        assert_eq!((&*actual) as *const u64, pointer);
        assert_eq!(*calls.borrow(), ["literal"]);

        for items in [
            vec![],
            vec![LegacyAtomicItem::Other],
            vec![LegacyAtomicItem::NonTerminal {
                kind: LegacyAtomicKind::Category,
                ident: "Other".into(),
            }],
            vec![LegacyAtomicItem::Terminal("a".into()), LegacyAtomicItem::Other],
        ] {
            let result: AtomicDescriptor<()> = classify_atomic(
                &rule,
                &items,
                || panic!("legacy refusal must not invoke unary resolver"),
                |_| panic!("ineligible legacy syntax must not invoke literal resolver"),
            );
            assert_eq!(result, AtomicDescriptor::NonAtomic);
        }
        let result: AtomicDescriptor<()> = classify_atomic(
            &rule,
            &[LegacyAtomicItem::NonTerminal {
                kind: LegacyAtomicKind::Category,
                ident: "Int".into(),
            }],
            || panic!("legacy syntax must not invoke unary resolver"),
            |_| None,
        );
        assert_eq!(result, AtomicDescriptor::NonAtomic);
    }

    #[test]
    fn atomic_unary_callback_runs_only_after_earlier_judgement_branches() {
        let mut rule = rule();
        rule.term_context = Some(vec![InfixParamShape::Simple {
            name: "x".into(),
            ty: InfixTypeShape::Base("Other".into()),
        }]);
        rule.syntax_pattern = Some(vec![
            InfixSyntaxShape::Literal("cast".into()),
            InfixSyntaxShape::Param("x".into()),
        ]);
        let result: AtomicDescriptor<()> = classify_atomic(
            &rule,
            &[],
            || panic!("cross-category success precedes unary resolver"),
            |_| panic!("judgement syntax must not invoke literal resolver"),
        );
        assert_eq!(
            result,
            AtomicDescriptor::CrossCatPrefixUnary {
                trigger: "cast".into(),
                source_cat_name: "Other".into(),
                wrapper_variant: "Wrapper".into(),
            }
        );
        rule.term_context = Some(vec![InfixParamShape::Simple {
            name: "x".into(),
            ty: InfixTypeShape::Base("Int".into()),
        }]);
        let calls = RefCell::new(Vec::new());
        let result: AtomicDescriptor<()> = classify_atomic(
            &rule,
            &[],
            || {
                calls.borrow_mut().push("unary");
                Some(AtomicUnaryPrefix {
                    trigger: "cast".into(),
                    operand_category: "Int".into(),
                })
            },
            |_| panic!("judgement syntax must not invoke literal resolver"),
        );
        assert_eq!(
            result,
            AtomicDescriptor::PrefixOperator {
                trigger: "cast".into(),
                operand_cat_name: "Int".into(),
            }
        );
        assert_eq!(*calls.borrow(), ["unary"]);
    }
}
