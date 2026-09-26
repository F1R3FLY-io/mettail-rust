//! The existing semantic production-precedence admission worker.
//!
//! Category-child positions are a caller-owned observation. They are requested
//! only after the original missing-production and missing-power early returns.
//! Callers must preserve the ordered category-child/production-top relation;
//! this is not a grammar classifier or an alternate recognition algorithm.

use crate::{Associativity, GrammarCoreV1, Production, ProductionId};

/// Apply the original `Realizer::precedence_valid` decision body.
///
/// `category_children` supplies positions in `child_tops` for the parent's
/// result category, in source order. The runtime-image caller keeps its exact
/// runtime-symbol scan. An owned caller must validate its retained argument
/// projection before supplying compact positions; omitted terminals are not
/// permission to guess the remaining positions.
pub fn production_precedence_valid(
    grammar: &GrammarCoreV1,
    parent_id: Option<ProductionId>,
    child_tops: &[Option<ProductionId>],
    category_children: impl FnOnce(&Production) -> Vec<usize>,
) -> bool {
    let Some(parent_id) = parent_id else {
        return true;
    };
    let parent = &grammar.productions[parent_id.0 as usize];
    let Some(parent_bp) = parent.precedence.binding_power else {
        return true;
    };
    let category_children = category_children(parent);
    let tighter = |child: Option<ProductionId>, allow_equal: bool| {
        child
            .and_then(|id| grammar.productions.get(id.0 as usize))
            .and_then(|production| production.precedence.binding_power)
            .is_none_or(|binding_power| {
                binding_power > parent_bp || (allow_equal && binding_power == parent_bp)
            })
    };
    if (parent.classification.infix || parent.is_binary_juxtaposition())
        && category_children.len() >= 2
    {
        let left = child_tops.get(category_children[0]).copied().flatten();
        let right = child_tops
            .get(*category_children.last().expect("two children"))
            .copied()
            .flatten();
        match parent.precedence.associativity {
            Associativity::Left => tighter(left, true) && tighter(right, false),
            Associativity::Right => tighter(left, false) && tighter(right, true),
            Associativity::NonAssociative => tighter(left, false) && tighter(right, false),
        }
    } else if parent.classification.prefix {
        category_children
            .last()
            .is_none_or(|index| tighter(child_tops.get(*index).copied().flatten(), true))
    } else if parent.classification.postfix {
        let allow_equal = parent.precedence.associativity != Associativity::NonAssociative;
        category_children
            .first()
            .is_none_or(|index| tighter(child_tops.get(*index).copied().flatten(), allow_equal))
    } else {
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CategoryId, ConstructorId, Precedence, ProductionClass, SyntaxItem};

    fn grammar() -> GrammarCoreV1 {
        let mut grammar = GrammarCoreV1::new("original precedence worker");
        for (index, binding_power) in [Some(10), Some(10), Some(11), Some(9), None]
            .into_iter()
            .enumerate()
        {
            grammar.productions.push(Production {
                id: ProductionId(index as u32),
                constructor: ConstructorId(index as u32),
                label: format!("P{index}"),
                result: CategoryId(0),
                authored: None,
                syntax: Vec::new(),
                precedence: Precedence {
                    binding_power,
                    associativity: Associativity::Left,
                    shares_previous_level: false,
                },
                classification: ProductionClass::default(),
                reduction: index as u32,
                provenance: None,
            });
        }
        grammar
    }

    #[test]
    fn original_early_returns_do_not_observe_category_children() {
        let grammar = grammar();
        for parent in [None, Some(ProductionId(4))] {
            assert!(production_precedence_valid(&grammar, parent, &[], |_| {
                panic!("missing parent or binding power must precede child projection")
            }));
        }
    }

    #[test]
    fn declared_postfix_uses_original_strictness_and_unranked_boundary() {
        let mut grammar = grammar();
        grammar.productions[0].classification.postfix = true;
        for associativity in
            [Associativity::Left, Associativity::Right, Associativity::NonAssociative]
        {
            grammar.productions[0].precedence.associativity = associativity;
            for (child, expected) in [
                (Some(ProductionId(1)), associativity != Associativity::NonAssociative),
                (Some(ProductionId(2)), true),
                (Some(ProductionId(3)), false),
                (Some(ProductionId(4)), true),
                (None, true),
            ] {
                assert_eq!(
                    production_precedence_valid(&grammar, Some(ProductionId(0)), &[child], |_| {
                        vec![0]
                    }),
                    expected,
                    "association {associativity:?}, child {child:?}",
                );
            }
        }
        grammar.productions[0].precedence.binding_power = Some(u16::MAX);
        grammar.productions[1].precedence.binding_power = Some(u16::MAX);
        assert!(!production_precedence_valid(
            &grammar,
            Some(ProductionId(0)),
            &[Some(ProductionId(1))],
            |_| vec![0],
        ));
    }

    #[test]
    fn juxtaposition_reuses_original_binary_admission_without_operator() {
        let mut grammar = grammar();
        grammar.productions[0].syntax = ["left", "right"]
            .into_iter()
            .map(|slot| SyntaxItem::Category {
                category: CategoryId(0),
                slot: slot.into(),
            })
            .collect();
        assert!(!grammar.productions[0].classification.infix);
        for (associativity, left_equal, right_equal) in [
            (Associativity::Left, true, false),
            (Associativity::Right, false, true),
            (Associativity::NonAssociative, false, false),
        ] {
            grammar.productions[0].precedence.associativity = associativity;
            for (children, expected) in [
                ([Some(ProductionId(1)), Some(ProductionId(2))], left_equal),
                ([Some(ProductionId(2)), Some(ProductionId(1))], right_equal),
                ([Some(ProductionId(2)), Some(ProductionId(2))], true),
            ] {
                assert_eq!(
                    production_precedence_valid(&grammar, Some(ProductionId(0)), &children, |_| {
                        vec![0, 1]
                    }),
                    expected,
                );
            }
        }
    }

    #[test]
    fn compact_term_slots_preserve_original_indexed_child_observations() {
        let mut grammar = grammar();
        grammar.productions[0].classification.infix = true;
        for associativity in
            [Associativity::Left, Associativity::Right, Associativity::NonAssociative]
        {
            grammar.productions[0].precedence.associativity = associativity;
            for left in 1..=4 {
                for right in 1..=4 {
                    let original = [Some(ProductionId(left)), None, Some(ProductionId(right))];
                    let compact = [original[0], original[2]];
                    assert_eq!(
                        production_precedence_valid(
                            &grammar,
                            Some(ProductionId(0)),
                            &original,
                            |_| { vec![0, 2] }
                        ),
                        production_precedence_valid(
                            &grammar,
                            Some(ProductionId(0)),
                            &compact,
                            |_| { vec![0, 1] }
                        ),
                    );
                }
            }
        }
    }
}
