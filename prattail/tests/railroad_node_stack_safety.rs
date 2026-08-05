use mettail_prattail::railroad::{diagram_to_text, RailroadNode};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

#[test]
fn railroad_lifecycle_and_text_rendering_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .name("railroad-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let mut node = RailroadNode::Terminal { text: "x".to_string() };
            for _ in 0..DEPTH {
                node = RailroadNode::Optional { inner: Box::new(node) };
            }

            let cloned = node.clone();
            let text = diagram_to_text(&node);
            assert!(text.starts_with("──┬──"));
            assert!(text.contains("──[ x ]──"));
            assert!(text.ends_with("──┬──\n  └──────────────┘"));
            let debug = format!("{node:?}");
            assert!(debug.starts_with("Optional { inner: Optional"));
            assert!(debug.contains("Terminal { text: \"x\" }"));

            #[cfg(feature = "railroad-diagrams")]
            {
                let svg = mettail_prattail::railroad::diagram_to_svg("deep", &node);
                assert!(svg.starts_with("<svg"));
                assert!(svg.contains("<title>deep</title>"));
                assert!(svg.contains(">x</text>"));
                assert_eq!(svg.matches("stroke=\"#888888\"").count(), DEPTH);
            }

            drop(cloned);
            drop(node);
        })
        .expect("spawn railroad small-stack gate")
        .join()
        .expect("railroad small-stack gate panicked");
}

#[test]
fn railroad_formatting_preserves_compact_contracts() {
    let node = RailroadNode::Repeat {
        element: Box::new(RailroadNode::Sequence {
            children: vec![
                RailroadNode::Terminal { text: "x".to_string() },
                RailroadNode::NonTerminal { text: "Expr".to_string() },
            ],
        }),
        separator: Some(Box::new(RailroadNode::Terminal { text: ",".to_string() })),
    };

    assert_eq!(diagram_to_text(&node), "──↻ ──[ x ]────⟨ Expr ⟩── ──[ , ]── ↻──");
    assert_eq!(
        format!("{node:?}"),
        "Repeat { element: Sequence { children: [Terminal { text: \"x\" }, NonTerminal { text: \"Expr\" }] }, separator: Some(Terminal { text: \",\" }) }"
    );
}

#[test]
fn railroad_renderers_emit_wide_deep_spines_without_intermediate_subtree_copies() {
    std::thread::Builder::new()
        .name("railroad-linear-emission-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let mut node = RailroadNode::Empty;
            for _ in 0..DEPTH {
                node = RailroadNode::Sequence {
                    children: vec![RailroadNode::Terminal { text: "x".to_string() }, node],
                };
            }

            let text = diagram_to_text(&node);
            assert_eq!(text.matches("──[ x ]──").count(), DEPTH);

            #[cfg(feature = "railroad-diagrams")]
            {
                let svg = mettail_prattail::railroad::diagram_to_svg("linear", &node);
                assert_eq!(svg.matches(">x</text>").count(), DEPTH);
            }

            drop(node);
        })
        .expect("spawn railroad linear-emission small-stack gate")
        .join()
        .expect("railroad linear-emission small-stack gate panicked");
}
