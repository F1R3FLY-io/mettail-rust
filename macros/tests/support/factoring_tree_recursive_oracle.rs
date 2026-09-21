use super::*;

fn literal(text: impl Into<String>) -> SpineItem {
    SpineItem::Literal {
        text: text.into(),
        required_top_cat: None,
    }
}

fn member(kind: MemberKind, rule_idx: u16, items: Vec<SpineItem>) -> CandidateMember {
    let total_positions = items.len();
    let mixfix_coords = if kind == MemberKind::Mixfix {
        (0..=total_positions)
            .map(|depth| (if depth == 0 { 2 } else { 0 }, 0, depth as u8))
            .collect()
    } else {
        Vec::new()
    };
    CandidateMember {
        kind,
        rule_idx,
        items,
        truncated: false,
        total_positions,
        body_src_idx: (kind == MemberKind::Binder).then_some(0),
        mixfix_coords,
    }
}

fn build_tree_recursive(
    depth: usize,
    edge_item: SpineItem,
    members: Vec<CandidateMember>,
    accept_continue: bool,
    interior_accepts: &mut Vec<u16>,
    refusals: &mut Vec<String>,
) -> Vec<SpineTree> {
    if members.len() == 1 {
        let member = members
            .into_iter()
            .next()
            .expect("one recursive-oracle member");
        return vec![SpineTree::Leaf {
            item: edge_item,
            member: finalize_leaf(member, depth, refusals),
        }];
    }

    let mut order = Vec::new();
    let mut parts: Vec<Vec<CandidateMember>> = Vec::new();
    let mut accepts = Vec::new();
    for member in members {
        if member.items.len() == depth {
            if accept_continue {
                accepts.push(SpineTree::Leaf {
                    item: edge_item.clone(),
                    member: finalize_leaf(member, depth, refusals),
                });
            } else {
                interior_accepts.push(member.rule_idx);
            }
            continue;
        }
        let item = member.items[depth].clone();
        match order.iter().position(|existing| existing == &item) {
            Some(index) => parts[index].push(member),
            None => {
                order.push(item);
                parts.push(vec![member]);
            },
        }
    }
    let mut children = Vec::with_capacity(parts.len());
    for (item, part) in order.into_iter().zip(parts) {
        children.extend(build_tree_recursive(
            depth + 1,
            item,
            part,
            accept_continue,
            interior_accepts,
            refusals,
        ));
    }
    if children.is_empty() {
        return accepts;
    }
    let mut forest = Vec::with_capacity(1 + accepts.len());
    forest.push(SpineTree::Interior { item: edge_item, children });
    forest.extend(accepts);
    forest
}

fn assert_equivalent(members: Vec<CandidateMember>, accept_continue: bool) {
    let edge = members[0].items[0].clone();
    let mut expected_accepts = Vec::new();
    let mut expected_refusals = Vec::new();
    let expected = build_tree_recursive(
        1,
        edge.clone(),
        members.clone(),
        accept_continue,
        &mut expected_accepts,
        &mut expected_refusals,
    );
    let mut actual_accepts = Vec::new();
    let mut actual_refusals = Vec::new();
    let actual =
        build_tree(1, edge, members, accept_continue, &mut actual_accepts, &mut actual_refusals);
    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    assert_eq!(actual_accepts, expected_accepts);
    assert_eq!(actual_refusals, expected_refusals);
}

#[test]
fn factoring_tree_recursive_oracle_preserves_branch_and_accept_order() {
    let root = literal("root");
    let shared = literal("shared");
    let members = vec![
        member(MemberKind::Binder, 0, vec![root.clone(), shared.clone()]),
        member(
            MemberKind::Binder,
            1,
            vec![root.clone(), shared.clone(), literal("continuation")],
        ),
        member(MemberKind::Nullary, 2, vec![root.clone(), literal("other")]),
    ];
    assert_equivalent(members.clone(), false);
    assert_equivalent(members, true);
}

#[test]
fn factoring_tree_recursive_oracle_preserves_twins_and_refusal_order() {
    let root = literal("root");
    assert_equivalent(
        vec![
            member(MemberKind::Nullary, 4, vec![root.clone()]),
            member(MemberKind::Nullary, 5, vec![root.clone()]),
        ],
        true,
    );

    let mut left = member(MemberKind::Mixfix, 10, vec![root.clone(), literal("left")]);
    let mut right = member(MemberKind::Mixfix, 11, vec![root, literal("right")]);
    left.mixfix_coords.truncate(1);
    right.mixfix_coords.clear();
    assert_equivalent(vec![left, right], true);
}

#[test]
fn factoring_tree_recursive_oracle_separates_continuation_order_from_eager_accept_refusals() {
    let root = literal("root");
    let mut continuing =
        member(MemberKind::Mixfix, 30, vec![root.clone(), literal("continuation")]);
    let mut exhausted = member(MemberKind::Mixfix, 31, vec![root.clone()]);
    continuing.mixfix_coords.clear();
    exhausted.mixfix_coords.clear();
    // Source order encounters the continuation first. Partitioning still
    // finalizes the parent accept before descending into that continuation.
    let members = vec![continuing, exhausted];

    for accept_continue in [true, false] {
        assert_equivalent(members.clone(), accept_continue);
        let mut accepts = Vec::new();
        let mut refusals = Vec::new();
        let forest = build_tree(
            1,
            root.clone(),
            members.clone(),
            accept_continue,
            &mut accepts,
            &mut refusals,
        );
        let output_order: Vec<_> = forest
            .iter()
            .flat_map(SpineTree::leaves)
            .map(|leaf| leaf.rule_idx)
            .collect();
        assert!(matches!(forest.first(), Some(SpineTree::Interior { .. })));
        let expected_refusals = if accept_continue {
            assert_eq!(output_order, [30, 31], "continuation precedes parent accept in output");
            assert!(accepts.is_empty());
            assert_eq!(forest.len(), 2);
            assert!(matches!(&forest[1], SpineTree::Leaf { member, .. } if member.rule_idx == 31));
            vec![(31, 1), (30, 2)]
        } else {
            assert_eq!(output_order, [30]);
            assert_eq!(accepts, [31]);
            assert_eq!(forest.len(), 1);
            vec![(30, 2)]
        };
        assert_eq!(refusals.len(), expected_refusals.len());
        for (refusal, (rule_idx, depth)) in refusals.iter().zip(expected_refusals) {
            assert!(
                refusal.starts_with(&format!(
                    "{LIMIT_REFUSAL} the mixfix member at rule index {rule_idx} recorded 0 spine \
                     coordinates but leafs at depth {depth},"
                )),
                "unexpected refusal order or coordinate: {refusal}"
            );
        }
    }
}

#[test]
fn factoring_tree_recursive_oracle_preserves_wide_first_occurrence_order() {
    const WIDTH: usize = 1_024;
    let root = literal("root");
    let members = (0..WIDTH)
        .map(|index| {
            member(
                MemberKind::Binder,
                index as u16,
                vec![root.clone(), literal(format!("branch-{index}"))],
            )
        })
        .collect();
    assert_equivalent(members, true);
}

#[test]
fn factoring_tree_recursive_oracle_deep_shared_prefix_fits_small_stack() {
    std::thread::Builder::new()
        .name("factoring-tree-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let mut left_items = vec![literal("shared"); DEPTH];
            let mut right_items = left_items.clone();
            left_items.push(literal("left"));
            right_items.push(literal("right"));
            let members = vec![
                member(MemberKind::Binder, 20, left_items),
                member(MemberKind::Binder, 21, right_items),
            ];
            let mut accepts = Vec::new();
            let mut refusals = Vec::new();
            let forest =
                build_tree(1, literal("shared"), members, true, &mut accepts, &mut refusals);
            assert_eq!(forest.iter().map(SpineTree::leaf_count).sum::<usize>(), 2);
            assert!(accepts.is_empty());
            assert_eq!(refusals.len(), 2, "one real u8 encoding refusal per deep leaf");
        })
        .expect("spawn factoring-tree small-stack test")
        .join()
        .expect("factoring-tree small-stack test panicked");
}

fn walk_leaf(item: SpineItem, rule_idx: u16) -> SpineTree {
    let mut refusals = Vec::new();
    let leaf =
        finalize_leaf(member(MemberKind::Nullary, rule_idx, vec![item.clone()]), 1, &mut refusals);
    assert!(refusals.is_empty());
    SpineTree::Leaf { item, member: leaf }
}

#[test]
fn factoring_flatten_forest_pins_root_and_sibling_allocation_before_preorder_descent() {
    let roots = vec![
        SpineTree::Interior {
            item: literal("a"),
            children: vec![
                SpineTree::Interior {
                    item: literal("a-left"),
                    children: vec![
                        SpineTree::Interior {
                            item: literal("a-deep"),
                            children: vec![walk_leaf(literal("deep-end"), 40)],
                        },
                        walk_leaf(literal("left-end"), 41),
                    ],
                },
                walk_leaf(literal("a-middle"), 42),
                SpineTree::Interior {
                    item: literal("a-right"),
                    children: vec![walk_leaf(literal("right-end"), 43)],
                },
            ],
        },
        walk_leaf(literal("root-accept"), 44),
        SpineTree::Interior {
            item: literal("b"),
            children: vec![
                SpineTree::Interior {
                    item: literal("b-child"),
                    children: vec![walk_leaf(literal("b-child-end"), 45)],
                },
                walk_leaf(literal("b-end"), 46),
            ],
        },
    ];
    let SpineTree::Interior { children: a, .. } = &roots[0] else {
        panic!("fixture root a")
    };
    let SpineTree::Interior { children: left, .. } = &a[0] else {
        panic!("fixture a-left")
    };
    let SpineTree::Interior { children: deep, .. } = &left[0] else {
        panic!("fixture a-deep")
    };
    let SpineTree::Interior { children: right, .. } = &a[2] else {
        panic!("fixture a-right")
    };
    let SpineTree::Interior { children: b, .. } = &roots[2] else {
        panic!("fixture root b")
    };
    let SpineTree::Interior { children: b_child, .. } = &b[0] else {
        panic!("fixture b-child")
    };
    // Root b receives 3 before any descendants of a. Sibling a-right receives
    // 5 before a-deep receives 6, even though a-deep is emitted first.
    let expected = vec![
        (1, vec![(&roots[0], 2), (&roots[1], 0), (&roots[2], 3)]),
        (2, vec![(&a[0], 4), (&a[1], 0), (&a[2], 5)]),
        (4, vec![(&left[0], 6), (&left[1], 0)]),
        (6, vec![(&deep[0], 0)]),
        (5, vec![(&right[0], 0)]),
        (3, vec![(&b[0], 7), (&b[1], 0)]),
        (7, vec![(&b_child[0], 0)]),
    ];
    let mut refusals = Vec::new();
    let flat = flatten_forest(&roots, &mut refusals);
    assert!(refusals.is_empty());
    assert_eq!(flat.iter().map(|node| node.node_id).collect::<Vec<_>>(), [1, 2, 4, 6, 5, 3, 7]);
    assert_eq!(flat.len(), expected.len());
    for (actual, (node_id, children)) in flat.iter().zip(expected) {
        assert_eq!(actual.node_id, node_id);
        assert_eq!(actual.children.len(), children.len());
        for ((actual_child, actual_id), (expected_child, expected_id)) in
            actual.children.iter().zip(children)
        {
            assert_eq!(*actual_id, expected_id, "child ID of arm {node_id}");
            assert!(
                std::ptr::eq(*actual_child, expected_child),
                "borrowed child identity of arm {node_id}"
            );
        }
    }
}

#[test]
fn factoring_mixfix_walk_pins_preorder_coordinates_borrowing_and_leaf_skips() {
    let operand = SpineItem::ParamParse { cat_src_idx: 7, cur_bp: 9 };
    let root = SpineTree::Interior {
        item: literal("root"),
        children: vec![
            walk_leaf(operand.clone(), 50),
            SpineTree::Interior {
                item: operand.clone(),
                children: vec![
                    walk_leaf(operand.clone(), 51),
                    SpineTree::Interior {
                        item: literal("after-operand"),
                        children: vec![walk_leaf(literal("after-end"), 52)],
                    },
                ],
            },
            walk_leaf(literal("skipped-literal"), 53),
            SpineTree::Interior {
                item: literal("right"),
                children: vec![SpineTree::Interior {
                    item: literal("right-deep"),
                    children: vec![walk_leaf(literal("right-end"), 54)],
                }],
            },
        ],
    };
    let SpineTree::Interior { children, .. } = &root else {
        panic!("fixture root")
    };
    let SpineTree::Interior { children: operand_children, .. } = &children[1] else {
        panic!("fixture operand")
    };
    let SpineTree::Interior { children: right_children, .. } = &children[3] else {
        panic!("fixture right")
    };
    let expected = [
        ((2, 0, 1), &root),
        ((0, 0, 0), &children[1]),
        ((0, 0, 1), &operand_children[1]),
        ((2, 0, 2), &children[3]),
        ((2, 0, 3), &right_children[0]),
    ];
    // Advancing the skipped leaves would collide with later interior keys.
    let actual = mixfix_spine_arm_coords(&root).expect("leaf edges do not allocate spine arms");
    assert_eq!(actual.len(), expected.len());
    for ((key, node), (expected_key, expected_node)) in actual.iter().zip(expected) {
        assert_eq!(*key, expected_key);
        assert_ne!(*key, (2, 0, 0), "pre-root key is reserved, not an emitted interior arm");
        assert!(std::ptr::eq(*node, expected_node), "arm plan borrows the source node");
    }
    let leaf_root = walk_leaf(operand.clone(), 55);
    assert!(mixfix_spine_arm_coords(&leaf_root)
        .expect("leaf root has no arm")
        .is_empty());
    let repeated_operand = SpineTree::Interior {
        item: operand.clone(),
        children: vec![SpineTree::Interior {
            item: operand,
            children: vec![walk_leaf(literal("end"), 56)],
        }],
    };
    assert!(
        mixfix_spine_arm_coords(&repeated_operand).is_none(),
        "repeated operand interiors collide"
    );
}
