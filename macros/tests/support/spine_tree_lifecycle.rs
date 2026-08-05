use super::{GroupMember, MemberCommit, MemberKind, SpineItem, SpinePosMap, SpineTree};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

fn leaf(rule_idx: u16) -> SpineTree {
    SpineTree::Leaf {
        item: SpineItem::Literal {
            text: "leaf".to_string(),
            required_top_cat: None,
        },
        member: GroupMember {
            kind: MemberKind::Nullary,
            rule_idx,
            leaf_depth: 1,
            commit: MemberCommit::Nullary { rule_idx, completed_idx: 0, sub_pos: 0 },
            pos_map: SpinePosMap::Nullary { sub_pos_at_depth: vec![0] },
            has_post_spine_remainder: false,
        },
    }
}

#[test]
fn spine_tree_lifecycle_and_walkers_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .name("spine-tree-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let mut tree = leaf(7);
            for depth in 0..DEPTH {
                tree = SpineTree::Interior {
                    item: SpineItem::Literal {
                        text: depth.to_string(),
                        required_top_cat: None,
                    },
                    children: vec![tree],
                };
            }

            assert_eq!(tree.leaf_count(), 1);
            assert_eq!(
                tree.leaves()
                    .iter()
                    .map(|member| member.rule_idx)
                    .collect::<Vec<_>>(),
                [7]
            );
            assert_eq!(tree.leaf_for(7).map(|(_, member)| member.rule_idx), Some(7));
            assert!(tree.leaf_for(8).is_none());
            let debug = format!("{tree:?}");
            assert!(debug.starts_with("Interior { item: Literal"));
            assert!(debug.contains("Leaf { item: Literal"));

            drop(tree);
        })
        .expect("spawn spine-tree small-stack gate")
        .join()
        .expect("spine-tree small-stack gate panicked");
}

#[test]
fn spine_tree_walkers_preserve_preorder_and_compact_debug_contracts() {
    let tree = SpineTree::Interior {
        item: SpineItem::ParamParse { cat_src_idx: 2, cur_bp: 3 },
        children: vec![leaf(4), leaf(5)],
    };

    assert_eq!(tree.leaf_count(), 2);
    assert_eq!(
        tree.leaves()
            .iter()
            .map(|member| member.rule_idx)
            .collect::<Vec<_>>(),
        [4, 5]
    );
    assert_eq!(tree.leaf_for(5).map(|(_, member)| member.rule_idx), Some(5));
    assert_eq!(
        format!("{tree:?}"),
        "Interior { item: ParamParse { cat_src_idx: 2, cur_bp: 3 }, children: [Leaf { item: Literal { text: \"leaf\", required_top_cat: None }, member: GroupMember { kind: Nullary, rule_idx: 4, leaf_depth: 1, commit: Nullary { rule_idx: 4, completed_idx: 0, sub_pos: 0 }, pos_map: Nullary { sub_pos_at_depth: [0] }, has_post_spine_remainder: false } }, Leaf { item: Literal { text: \"leaf\", required_top_cat: None }, member: GroupMember { kind: Nullary, rule_idx: 5, leaf_depth: 1, commit: Nullary { rule_idx: 5, completed_idx: 0, sub_pos: 0 }, pos_map: Nullary { sub_pos_at_depth: [0] }, has_post_spine_remainder: false } }] }"
    );
}
