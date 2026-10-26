//! Concrete builder observations for AuthoredTermConstruction's local invariants.
//!
//! These fixtures reuse the existing image and instantiate_rule_term worker.
//! They are lowered-arena tests, not a rich-source projection validator or an
//! independent whole-source evaluator. Expected results inspect actual nodes.

use super::*;
use mettail_grammar_core::{
    TheoryImageTermNodeV1, TheoryImageVariableV1, TheoryTermId, TheoryVariableRoleV1,
};
use proptest::prelude::*;

fn variables(
    declarations: &[(u32, TheoryVariableRoleV1)],
    rotation: usize,
) -> (Vec<TheoryImageVariableV1>, Vec<TheoryVariableId>) {
    let ids = (0..declarations.len())
        .map(|index| TheoryVariableId(((index + rotation) % declarations.len()) as u32))
        .collect::<Vec<_>>();
    let mut variables = declarations
        .iter()
        .zip(&ids)
        .map(|(&(sort, role), &id)| TheoryImageVariableV1 { id, sort: TheorySortId(sort), role })
        .collect::<Vec<_>>();
    variables.sort_by_key(|variable| variable.id);
    (variables, ids)
}

fn slot(sort: u32, variable: TheoryVariableId) -> TheoryImageTermNodeV1 {
    TheoryImageTermNodeV1 {
        sort: TheorySortId(sort),
        form: TheoryImageTermFormV1::Slot(variable),
    }
}

fn apply(sort: u32, operator: TheoryImageOperatorV1, arguments: &[u32]) -> TheoryImageTermNodeV1 {
    TheoryImageTermNodeV1 {
        sort: TheorySortId(sort),
        form: TheoryImageTermFormV1::Apply {
            operator,
            arguments: arguments.iter().copied().map(TheoryTermId).collect(),
            slots: Vec::new(),
            remainder: None,
            pathmap_mode: None,
        },
    }
}

fn map(
    sort: u32,
    sources: &[u32],
    parameters: &[TheoryVariableId],
    body: u32,
) -> TheoryImageTermNodeV1 {
    TheoryImageTermNodeV1 {
        sort: TheorySortId(sort),
        form: TheoryImageTermFormV1::Map {
            sources: sources.iter().copied().map(TheoryTermId).collect(),
            parameters: parameters.to_vec(),
            body: TheoryTermId(body),
        },
    }
}

fn constructor(id: u32) -> TheoryImageOperatorV1 {
    TheoryImageOperatorV1::Constructor(TheoryConstructorId(id))
}

fn list(sort: u32, element: u32) -> TheoryImageOperatorV1 {
    TheoryImageOperatorV1::Collection {
        sort: TheorySortId(sort),
        element: TheorySortId(element),
        kind: CollectionKind::List,
    }
}

fn expr(graph: &mut EGraph<FramedSemanticOperator>, leaf: u32, depth: usize) -> EClassId {
    let mut value = add(graph, constructor(leaf), Vec::new());
    for _ in 0..depth {
        value = add(graph, constructor(2), vec![value]);
    }
    value
}

fn integer(graph: &mut EGraph<FramedSemanticOperator>, value: i64) -> EClassId {
    add(
        graph,
        TheoryImageOperatorV1::Literal {
            sort: TheorySortId(1),
            value: TheoryLiteralV1::Integer(i128::from(value)),
        },
        Vec::new(),
    )
}

fn children(
    graph: &EGraph<FramedSemanticOperator>,
    root: EClassId,
    operator: TheoryImageOperatorV1,
) -> Vec<EClassId> {
    let [node] = graph.nodes(root) else {
        panic!("constructed root must have exactly one node")
    };
    assert_eq!(node.op, theory_operator_to_machine(&operator));
    node.children
        .iter()
        .map(|&child| graph.find(child))
        .collect()
}

fn construct(
    image: &TheorySemanticImageV1,
    terms: &[TheoryImageTermNodeV1],
    variables: &[TheoryImageVariableV1],
    substitution: &ActionSubstitution,
    root: u32,
    graph: &mut EGraph<FramedSemanticOperator>,
) -> Result<EClassId, SemanticMatchUndetermined> {
    instantiate_rule_term(
        TermInstantiation {
            image,
            terms,
            variables,
            substitution,
            root: TheoryTermId(root),
            limits: TermConstructionLimits {
                work: 100_000,
                nodes: 2_000,
                bytes: 1 << 20,
            },
        },
        graph,
        &mut 0,
        &mut || false,
    )
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(48))]

    #[test]
    fn generated_map_rows_keep_exact_parameters_and_every_source_row(
        rows in prop::collection::vec((0u8..8, -10_000i64..10_000), 0..7),
        rotation in 0usize..5,
        reverse_columns in any::<bool>(),
    ) {
        use TheoryVariableRoleV1::{Binder, Input};
        let image = comprehension_image();
        let (variables, ids) = variables(&[(3, Input), (6, Input), (5, Input), (2, Binder), (1, Binder)], rotation);
        let (sources, parameters) = if reverse_columns {
            (vec![1, 0], vec![ids[4], ids[3]])
        } else {
            (vec![0, 1], vec![ids[3], ids[4]])
        };
        let terms = vec![
            slot(3, ids[0]), slot(6, ids[1]), slot(5, ids[2]),
            slot(2, ids[3]), slot(1, ids[4]),
            apply(4, TheoryImageOperatorV1::Product { sort: TheorySortId(4) }, &[3, 4]),
            map(5, &sources, &parameters, 5),
            map(5, &[2], &[ids[3], ids[4]], 5),
            apply(2, constructor(2), &[3]),
            map(3, &[0], &[ids[3]], 8),
        ];
        let mut graph = EGraph::new();
        let mut expressions = Vec::new();
        let mut integers = Vec::new();
        let mut pairs = Vec::new();
        for &(shape, number) in &rows {
            let left = expr(&mut graph, u32::from(shape % 2), usize::from(shape / 2));
            let right = integer(&mut graph, number);
            expressions.push(left);
            integers.push(right);
            pairs.push(add(&mut graph, TheoryImageOperatorV1::Product { sort: TheorySortId(4) }, vec![left, right]));
        }
        let left = add(&mut graph, list(3, 2), expressions.clone());
        let right = add(&mut graph, list(6, 1), integers.clone());
        let products = add(&mut graph, list(5, 4), pairs);
        let mut substitution = vec![(ids[0], left), (ids[1], right), (ids[2], products)];
        substitution.sort_by_key(|&(variable, _)| variable);
        let original = substitution.clone();
        for root in [6, 7] {
            let output = construct(&image, &terms, &variables, &substitution, root, &mut graph).unwrap();
            let actual = children(&graph, output, list(5, 4));
            prop_assert_eq!(actual.len(), rows.len());
            for (index, &pair) in actual.iter().enumerate() {
                prop_assert_eq!(children(&graph, pair, TheoryImageOperatorV1::Product { sort: TheorySortId(4) }),
                    vec![expressions[index], integers[index]]);
            }
        }
        let scalar = construct(&image, &terms, &variables, &substitution, 9, &mut graph).unwrap();
        let actual = children(&graph, scalar, list(3, 2));
        prop_assert_eq!(actual.len(), rows.len());
        for (index, &wrapped) in actual.iter().enumerate() {
            prop_assert_eq!(children(&graph, wrapped, constructor(2)), vec![expressions[index]]);
        }
        prop_assert_eq!(&substitution, &original);

        // A mismatch must refuse even when one source is empty: no zip truncation.
        let extra = integer(&mut graph, i64::MIN);
        integers.push(extra);
        let longer = add(&mut graph, list(6, 1), integers);
        let mut unequal = substitution.clone();
        unequal.iter_mut().find(|(variable, _)| *variable == ids[1]).unwrap().1 = longer;
        prop_assert_eq!(construct(&image, &terms, &variables, &unequal, 6, &mut graph),
            Err(SemanticMatchUndetermined::InvalidImageEvidence));

        // Parameter widths are checked when forming an actual row. With no
        // rows the model's row telescope is vacuous, so do not invent a check.
        if !rows.is_empty() {
            for root in [6usize, 7, 9] {
                let mut wrong = terms.clone();
                let TheoryImageTermFormV1::Map { parameters, .. } = &mut wrong[root].form else { unreachable!() };
                if root == 9 { parameters.push(ids[4]); } else { parameters.pop(); }
                prop_assert_eq!(construct(&image, &wrong, &variables, &substitution, root as u32, &mut graph),
                    Err(SemanticMatchUndetermined::InvalidImageEvidence));
            }
        }
        let mut wrong_role = variables.clone();
        wrong_role[ids[3].0 as usize].role = Input;
        prop_assert_eq!(construct(&image, &terms, &wrong_role, &substitution, 7, &mut graph),
            Err(SemanticMatchUndetermined::InvalidImageEvidence));
    }

    #[test]
    fn generated_nested_maps_keep_saved_overlays_and_binder_before_body(
        outer_rows in 2usize..5,
        inner_rows in 2usize..5,
        depth in 0usize..4,
        rotation in 0usize..6,
    ) {
        use TheoryVariableRoleV1::{Binder, Input};
        let mut image = comprehension_image();
        image.sorts.push(sort(16, TheorySortKindImageV1::Collection {
            kind: CollectionKind::List, key: None, element: TheorySortId(7),
        }));
        image.sorts.push(sort(17, TheorySortKindImageV1::Product {
            factors: vec![TheorySortId(2), TheorySortId(16), TheorySortId(2)],
        }));
        let (variables, ids) = variables(
            &[(3, Input), (3, Input), (2, Binder), (2, Binder), (3, Input), (2, Input)], rotation,
        );
        let mut abstraction = apply(7, TheoryImageOperatorV1::Abstraction { sort: TheorySortId(7) }, &[9]);
        let TheoryImageTermFormV1::Apply { slots, .. } = &mut abstraction.form else { unreachable!() };
        slots.push(ids[2]);
        // Reusing x's numeric slot in the inner overlay is intentional. This
        // tests the builder's lexical lookup contract, not source acceptance
        // of a particular binder spelling or comprehension-context graph.
        let terms = vec![
            slot(3, ids[0]), slot(3, ids[1]), slot(2, ids[2]),
            slot(2, ids[3]), slot(3, ids[4]), slot(2, ids[5]),
            apply(2, constructor(4), &[3, 5]),
            apply(2, constructor(4), &[2, 6]),
            map(3, &[4], &[ids[2]], 7),
            apply(2, constructor(3), &[8]),
            abstraction,
            map(16, &[0, 1], &[ids[2], ids[3]], 10),
            apply(17, TheoryImageOperatorV1::Product { sort: TheorySortId(17) }, &[5, 11, 2]),
        ];
        let mut graph = EGraph::new();
        let outer_left = (0..outer_rows).map(|index| expr(&mut graph, 0, depth + index + 1)).collect::<Vec<_>>();
        let outer_right = (0..outer_rows).map(|index| expr(&mut graph, 1, depth + index + 1)).collect::<Vec<_>>();
        let inner = (0..inner_rows).map(|index| expr(&mut graph, 0, 16 + index)).collect::<Vec<_>>();
        let initial_x = expr(&mut graph, 1, 0);
        let fallback = expr(&mut graph, 1, 30);
        let left_source = add(&mut graph, list(3, 2), outer_left.clone());
        let right_source = add(&mut graph, list(3, 2), outer_right.clone());
        let inner_source = add(&mut graph, list(3, 2), inner.clone());
        let mut substitution = vec![
            (ids[0], left_source), (ids[1], right_source), (ids[2], initial_x),
            (ids[4], inner_source), (ids[5], fallback),
        ];
        substitution.sort_by_key(|&(variable, _)| variable);
        let original = substitution.clone();
        let output = construct(&image, &terms, &variables, &substitution, 12, &mut graph).unwrap();
        let surrounding = children(&graph, output, TheoryImageOperatorV1::Product { sort: TheorySortId(17) });
        prop_assert_eq!(surrounding.len(), 3);
        prop_assert_eq!(surrounding[0], fallback, "existing value-stack prefix survives the map");
        prop_assert_eq!(surrounding[2], initial_x, "later sibling keeps the original environment");
        let abstractions = children(&graph, surrounding[1], list(16, 7));
        prop_assert_eq!(abstractions.len(), outer_rows);
        for (row, &abstraction) in abstractions.iter().enumerate() {
            let bound = children(&graph, abstraction, TheoryImageOperatorV1::Abstraction { sort: TheorySortId(7) });
            prop_assert_eq!(bound.len(), 2);
            prop_assert_eq!(bound[0], outer_left[row], "binder is read from the saved outer row after inner bodies finish");
            let wrapped = children(&graph, bound[1], constructor(3));
            prop_assert_eq!(wrapped.len(), 1);
            let bodies = children(&graph, wrapped[0], list(3, 2));
            prop_assert_eq!(bodies.len(), inner_rows);
            for (index, &body) in bodies.iter().enumerate() {
                let pair = children(&graph, body, constructor(4));
                prop_assert_eq!(pair.len(), 2);
                prop_assert_eq!(pair[0], inner[index], "nearest overlay shadows x independently for each row");
                prop_assert_eq!(children(&graph, pair[1], constructor(4)), vec![outer_right[row], fallback],
                    "unbound variables fall through the parent overlay to the outer substitution");
            }
        }
        prop_assert_eq!(&substitution, &original, "construction never exports row bindings");
        validate(&image, &graph, output, TheorySortId(17), 100_000)
            .expect("the constructed operators and child sorts match the fixture signature");
    }

    #[test]
    fn generated_construction_suffix_requires_exact_width_and_preserves_prefix(
        raw in prop::collection::vec(any::<u32>(), 0..20),
        split in any::<u8>(),
    ) {
        // This helper manipulates value-stack entries only; it does not inspect
        // or admit these opaque e-class tokens into any graph.
        let original = raw.into_iter().map(EClassId).collect::<Vec<_>>();
        let base = usize::from(split) % (original.len() + 1);
        let expected = original.len() - base;
        let mut values = original.clone();
        prop_assert_eq!(take_construction_values(&mut values, base, expected).unwrap(), original[base..].to_vec());
        prop_assert_eq!(values, original[..base].to_vec());

        let mut wrong_widths = vec![expected + 1];
        if expected > 0 { wrong_widths.push(expected - 1); }
        for width in wrong_widths {
            let mut values = original.clone();
            prop_assert_eq!(take_construction_values(&mut values, base, width),
                Err(SemanticMatchUndetermined::InvalidImageEvidence));
            prop_assert_eq!(&values, &original, "refusal must not consume a partial suffix");
        }
        let mut values = original.clone();
        prop_assert_eq!(take_construction_values(&mut values, original.len() + 1, 0),
            Err(SemanticMatchUndetermined::InvalidImageEvidence));
        prop_assert_eq!(values, original);
    }
}
