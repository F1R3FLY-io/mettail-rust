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
