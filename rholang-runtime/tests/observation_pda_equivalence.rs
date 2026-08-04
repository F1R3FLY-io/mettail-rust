//! Differential and deep-shape gates for the observation decoder/render PDAs.
//!
//! The recursive renderer below is deliberately confined to this bounded test oracle. Production
//! decoding, rendering, Peano traversal, and temporary-value destruction are iterative.

use mettail_rholang_runtime::{
    par_as_runtime_observation_value, render_observation_text, render_observation_text_with,
    render_par_text, ObservationTermNotation, RHOLANG_BAG_ABI_TAG,
};
use mettail_runtime::RuntimeObservationValue;
use models::rhoapi::Par;
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_elist_par, new_emap_par, new_eset_par, new_etuple_par, new_gbool_par, new_gint_par,
    new_gstring_par, new_key_value_pair,
};

fn recursive_render_oracle(value: &RuntimeObservationValue) -> String {
    use RuntimeObservationValue as V;
    let V::Term { constructor, children } = value else {
        return value.to_string();
    };
    match (constructor.as_str(), children.as_slice()) {
        ("^lambda", [body]) => format!("λ.{}", recursive_render_oracle(body)),
        ("^bound", [index]) => {
            let mut index = index;
            let mut value = 0usize;
            while let V::Term { constructor, children } = index {
                if constructor != "^S" {
                    break;
                }
                let Some(child) = children.first() else {
                    break;
                };
                value += 1;
                index = child;
            }
            value.to_string()
        },
        ("^free", [name]) => recursive_render_oracle(name),
        _ if children.is_empty() => constructor.clone(),
        _ => format!(
            "{constructor}({})",
            children
                .iter()
                .map(recursive_render_oracle)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

fn reflected(label: &str, children: Vec<Par>) -> Par {
    let mut elements = Vec::with_capacity(children.len() + 1);
    elements.push(GPrivateBuilder::new_par_from_string(
        mettail_rholang_codegen::reflected_tag_string("pda-equivalence", label),
    ));
    elements.extend(children);
    new_elist_par(elements, Vec::new(), false, None, Vec::new(), false)
}

fn list(elements: Vec<Par>) -> Par {
    new_elist_par(elements, Vec::new(), false, None, Vec::new(), false)
}

#[test]
fn iterative_renderer_matches_the_bounded_recursive_oracle() {
    use RuntimeObservationValue as V;

    let zero = V::Term {
        constructor: "^Z".into(),
        children: Vec::new(),
    };
    let one = V::Term {
        constructor: "^S".into(),
        children: vec![zero],
    };
    let corpus = vec![
        V::Int(-7),
        V::Bool(true),
        V::Text("quoted\ntext".into()),
        V::TermDisplay("surface".into()),
        V::Bytes(vec![0x00, 0xab, 0xff]),
        V::Uri("rho:id:test".into()),
        V::DoubleBits(0x3ff0_0000_0000_0000),
        V::BigIntBytes(vec![1, 2, 3]),
        V::BigRationalBytes { numerator: vec![4], denominator: vec![5] },
        V::FixedPointBytes { unscaled: vec![6], scale: 7 },
        V::PrivateName(vec![8]),
        V::DeployId(vec![9]),
        V::DeployerId(vec![10]),
        V::SysAuthToken,
        V::List(vec![V::Int(1), V::List(vec![V::Bool(false)])]),
        V::Tuple(vec![V::Text("x".into()), V::Int(2)]),
        V::Set(vec![V::Int(1), V::Int(2)]),
        V::Map(vec![(V::Text("k".into()), V::List(vec![V::Int(3)]))]),
        V::Bag(vec![(V::Text("x".into()), 4)]),
        V::Term {
            constructor: "^lambda".into(),
            children: vec![V::Int(0)],
        },
        V::Term {
            constructor: "^bound".into(),
            children: vec![one],
        },
        V::Term {
            constructor: "^free".into(),
            children: vec![V::Text("x".into())],
        },
        V::Term {
            constructor: "Node".into(),
            children: vec![
                V::Int(1),
                V::Term {
                    constructor: "Leaf".into(),
                    children: vec![],
                },
            ],
        },
    ];

    for (row, value) in corpus.iter().enumerate() {
        assert_eq!(
            render_observation_text(value),
            recursive_render_oracle(value),
            "renderer mismatch at corpus row {row}"
        );
    }
}

#[test]
fn layout_only_guest_renderer_survives_a_deep_application_spine() {
    use RuntimeObservationValue as V;
    const DEPTH: usize = 16_384;

    let mut value = V::Int(0);
    for _ in 0..DEPTH {
        value = V::Term {
            constructor: "App".into(),
            children: vec![value, V::Int(1)],
        };
    }

    let rendered = render_observation_text_with(&value, &|constructor, arity| {
        (constructor == "App" && arity == 2).then_some(ObservationTermNotation {
            open: "(",
            separator: " ",
            close: ")",
        })
    });
    assert_eq!(rendered.bytes().filter(|byte| *byte == b'(').count(), DEPTH);
    assert!(rendered.starts_with('(') && rendered.ends_with(')'));

    // `RuntimeObservationValue`'s derived destructor is the next independently tracked closure
    // item. Do not let that known recursive traversal contaminate this renderer witness.
    std::mem::forget(value);
}

#[test]
fn decoder_preserves_collection_term_and_bag_images() {
    use RuntimeObservationValue as V;

    let nested = list(vec![
        new_gint_par(1, Vec::new(), false),
        new_etuple_par(vec![new_gbool_par(true, Vec::new(), false)]),
    ]);
    assert_eq!(
        par_as_runtime_observation_value(&nested),
        Some(V::List(vec![V::Int(1), V::Tuple(vec![V::Bool(true)])]))
    );

    let set = new_eset_par(
        vec![new_gint_par(2, Vec::new(), false), new_gint_par(1, Vec::new(), false)],
        Vec::new(),
        false,
        None,
        Vec::new(),
        false,
    );
    assert_eq!(par_as_runtime_observation_value(&set), Some(V::Set(vec![V::Int(1), V::Int(2)])));

    let map = new_emap_par(
        vec![new_key_value_pair(
            new_gstring_par("k".into(), Vec::new(), false),
            new_gint_par(3, Vec::new(), false),
        )],
        Vec::new(),
        false,
        None,
        Vec::new(),
        false,
    );
    assert_eq!(
        par_as_runtime_observation_value(&map),
        Some(V::Map(vec![(V::Text("k".into()), V::Int(3))]))
    );

    let term = reflected("Node", vec![reflected("Leaf", Vec::new())]);
    assert_eq!(
        par_as_runtime_observation_value(&term),
        Some(V::Term {
            constructor: "Node".into(),
            children: vec![V::Term {
                constructor: "Leaf".into(),
                children: Vec::new()
            }],
        })
    );

    let bag = list(vec![
        GPrivateBuilder::new_par_from_string(RHOLANG_BAG_ABI_TAG.to_string()),
        list(vec![
            list(vec![new_gint_par(7, Vec::new(), false), new_gint_par(2, Vec::new(), false)]),
            list(vec![new_gint_par(7, Vec::new(), false), new_gint_par(3, Vec::new(), false)]),
        ]),
    ]);
    assert_eq!(par_as_runtime_observation_value(&bag), Some(V::Bag(vec![(V::Int(7), 5)])));
}

#[test]
fn deeply_nested_list_renders_without_native_stack_growth() {
    const DEPTH: usize = 16_384;

    let mut deep = new_gint_par(1, Vec::new(), false);
    for _ in 0..DEPTH {
        deep = list(vec![deep]);
    }

    let rendered = render_par_text(&deep);
    assert!(rendered.contains("(elided,"));
}
