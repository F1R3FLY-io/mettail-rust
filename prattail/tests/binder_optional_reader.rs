//! Exercise the shared classifier through immutable integer handles and slices.

use std::cell::RefCell;
use std::collections::HashMap;

use mettail_ast::grammar::DelimitedRegionKind;
use mettail_ast::types::CollectionType;
use mettail_prattail::wpda_rule_analysis::binder::optional::{
    classify_optional_body, BinderSyntaxObservation, BinderSyntaxReader,
    OptionalOperationObservation,
};
use mettail_prattail::wpda_rule_analysis::binder::{
    ActionArgKind, BinderPosition, CollectionSepInfo, ParamKind,
};

#[derive(Clone, Copy)]
enum Node<'a> {
    Literal(&'a str),
    Param(&'a str),
    Token(&'a str),
    Guest(&'a str, &'a str, &'a str),
    Op(usize),
}

#[derive(Clone, Copy)]
enum Operation<'a> {
    Opt(usize),
    Sep(&'a str, &'a str, Option<usize>),
    Other(usize),
}

#[derive(Debug, PartialEq)]
enum Visit {
    Node(usize, usize),
    Operation(usize),
}

struct SliceReader<'a> {
    sequences: &'a [&'a [Node<'a>]],
    operations: &'a [Operation<'a>],
    visits: RefCell<Vec<Visit>>,
}

impl<'a> SliceReader<'a> {
    fn new(sequences: &'a [&'a [Node<'a>]], operations: &'a [Operation<'a>]) -> Self {
        Self {
            sequences,
            operations,
            visits: RefCell::new(Vec::new()),
        }
    }
}

impl<'a> BinderSyntaxReader<'a> for SliceReader<'a> {
    type Sequence = usize;
    type Name = &'a str;
    type Operation = usize;

    fn sequence_len(&self, sequence: usize) -> usize {
        self.sequences[sequence].len()
    }

    fn at(
        &self,
        sequence: usize,
        index: usize,
    ) -> Option<BinderSyntaxObservation<'a, &'a str, usize>> {
        self.visits.borrow_mut().push(Visit::Node(sequence, index));
        Some(match *self.sequences[sequence].get(index)? {
            Node::Literal(text) => BinderSyntaxObservation::Literal(text),
            Node::Param(name) => BinderSyntaxObservation::Param(name),
            Node::Token(name) => BinderSyntaxObservation::TokenKind { name, bind: None },
            Node::Guest(open, close, bind) => BinderSyntaxObservation::GuestBody {
                open,
                close,
                bind,
                kind: DelimitedRegionKind::Flt,
            },
            Node::Op(operation) => BinderSyntaxObservation::Op(operation),
        })
    }

    fn operation(
        &self,
        operation: usize,
    ) -> OptionalOperationObservation<'a, &'a str, usize, usize> {
        self.visits.borrow_mut().push(Visit::Operation(operation));
        match self.operations[operation] {
            Operation::Opt(inner) => OptionalOperationObservation::Opt { inner },
            Operation::Sep(collection, separator, source) => {
                OptionalOperationObservation::Sep { collection, separator, source }
            },
            Operation::Other(opaque) => OptionalOperationObservation::Other(opaque),
        }
    }
}

fn collections() -> HashMap<String, ParamKind> {
    HashMap::from([
        (
            "pairs".into(),
            ParamKind::SimpleCollection {
                elem_cat: "Pair".into(),
                coll_kind: CollectionType::HashMap,
            },
        ),
        (
            "terms".into(),
            ParamKind::SimpleCollection {
                elem_cat: "Term".into(),
                coll_kind: CollectionType::Vec,
            },
        ),
    ])
}

fn guest_position(open: &str, close: &str, param: &str) -> BinderPosition {
    BinderPosition::GuestBodyCapture {
        open_kind: open.into(),
        nested_open_kinds: vec![format!("{open}_NESTED")],
        close_kind: close.into(),
        param_name: param.into(),
    }
}

fn guest_arg(param: &str) -> ActionArgKind {
    ActionArgKind::GuestBody {
        param_name: param.into(),
        kind: DelimitedRegionKind::Flt,
    }
}

#[test]
fn nested_payloads_preserve_helper_order_and_absent_kv_separator() {
    let root = [Node::Op(0), Node::Guest("OUT", "END", "outer"), Node::Op(3), Node::Literal("]")];
    let middle = [Node::Op(1), Node::Guest("IN", "STOP", "inner"), Node::Op(2), Node::Literal(")")];
    let leaf = [Node::Literal("if"), Node::Token("Word")];
    let sequences: &[&[Node<'_>]] = &[&root, &middle, &leaf];
    let operations = [
        Operation::Opt(1),
        Operation::Opt(2),
        Operation::Sep("pairs", ",", None),
        Operation::Sep("terms", "|", None),
    ];
    let reader = SliceReader::new(sequences, &operations);
    let effects = RefCell::new(Vec::new());
    let mut group = 7;
    let mut slot = 4;
    let actual = classify_optional_body(
        &reader,
        0,
        &collections(),
        &mut group,
        &mut slot,
        |open| {
            effects.borrow_mut().push(format!("guest:{open}"));
            vec![format!("{open}_NESTED")]
        },
        |kind| {
            effects.borrow_mut().push(format!("kv:{kind:?}"));
            match kind {
                CollectionType::HashMap => Some(":".into()),
                CollectionType::Vec => None,
                _ => panic!("unexpected collection helper argument"),
            }
        },
    )
    .expect("finite nested optional body should classify");

    let expected = (
        vec![
            BinderPosition::OptionalGroup {
                positions: vec![
                    BinderPosition::OptionalGroup {
                        positions: vec![
                            BinderPosition::Literal("if".into()),
                            BinderPosition::TokenKindCapture {
                                kind_name: "Word".into(),
                                param_name: "__tok_Word".into(),
                            },
                        ],
                        group_idx: 8,
                        first_token_set: vec!["if".into()],
                    },
                    guest_position("IN", "STOP", "inner"),
                    BinderPosition::ParamParse {
                        cat: "Pair".into(),
                        collection: Some(CollectionSepInfo {
                            separator: ",".into(),
                            close: ")".into(),
                            elem_cat: "Pair".into(),
                            key_val_separator: Some(":".into()),
                            slot_idx: 4,
                        }),
                    },
                ],
                group_idx: 7,
                first_token_set: vec!["if".into()],
            },
            guest_position("OUT", "END", "outer"),
            BinderPosition::ParamParse {
                cat: "Term".into(),
                collection: Some(CollectionSepInfo {
                    separator: "|".into(),
                    close: "]".into(),
                    elem_cat: "Term".into(),
                    key_val_separator: None,
                    slot_idx: 5,
                }),
            },
        ],
        vec![
            ActionArgKind::Optional(vec![
                ActionArgKind::Optional(vec![ActionArgKind::TokenText {
                    param_name: "__tok_Word".into(),
                }]),
                guest_arg("inner"),
                ActionArgKind::CollectionDrain {
                    elem_cat: "Pair".into(),
                    coll_kind: CollectionType::HashMap,
                },
            ]),
            guest_arg("outer"),
            ActionArgKind::CollectionDrain {
                elem_cat: "Term".into(),
                coll_kind: CollectionType::Vec,
            },
        ],
    );
    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    assert_eq!((group, slot), (9, 6));
    assert_eq!(*effects.borrow(), ["guest:IN", "kv:HashMap", "guest:OUT", "kv:Vec"]);
}

#[test]
fn failed_prefix_retains_counter_and_helper_effects() {
    let root = [Node::Op(0), Node::Op(usize::MAX)];
    let middle = [Node::Op(1)];
    let leaf = [
        Node::Guest("IN", "STOP", "inner"),
        Node::Op(2),
        Node::Literal(")"),
        Node::Param("missing"),
        Node::Op(usize::MAX),
    ];
    let sequences: &[&[Node<'_>]] = &[&root, &middle, &leaf];
    let operations = [Operation::Opt(1), Operation::Opt(2), Operation::Sep("terms", ",", None)];
    let reader = SliceReader::new(sequences, &operations);
    let effects = RefCell::new(Vec::new());
    let mut group = 9;
    let mut slot = 3;
    let result = classify_optional_body(
        &reader,
        0,
        &collections(),
        &mut group,
        &mut slot,
        |open| {
            effects.borrow_mut().push(format!("guest:{open}"));
            Vec::new()
        },
        |kind| {
            effects.borrow_mut().push(format!("kv:{kind:?}"));
            None
        },
    );
    assert!(result.is_none());
    assert_eq!((group, slot), (11, 4));
    assert_eq!(*effects.borrow(), ["guest:IN", "kv:Vec"]);
    assert_eq!(reader.visits.borrow().last(), Some(&Visit::Node(2, 3)));
}

#[test]
fn sourced_separator_and_other_refuse_without_reading_opaque_handles() {
    for operation in
        [Operation::Sep("missing", ",", Some(usize::MAX)), Operation::Other(usize::MAX)]
    {
        let root = [Node::Op(0), Node::Op(usize::MAX)];
        let sequences: &[&[Node<'_>]] = &[&root];
        let operations = [operation];
        let reader = SliceReader::new(sequences, &operations);
        let mut group = 17;
        let mut slot = 23;
        let result = classify_optional_body(
            &reader,
            0,
            &HashMap::new(),
            &mut group,
            &mut slot,
            |_| panic!("refusal must precede guest helpers"),
            |_| panic!("refusal must precede collection helpers"),
        );
        assert!(result.is_none());
        assert_eq!((group, slot), (17, 23));
        assert_eq!(*reader.visits.borrow(), [Visit::Node(0, 0), Visit::Operation(0)]);
    }
}

#[test]
fn counter_overflow_gates_child_reads_and_collection_helpers() {
    for (operation, initial_group, initial_slot) in [
        (Operation::Opt(usize::MAX), u32::MAX, 5),
        (Operation::Sep("terms", ",", None), 13, u8::MAX),
    ] {
        let root = [
            Node::Guest("PREFIX", "END", "prefix"),
            Node::Op(0),
            Node::Literal(")"),
            Node::Op(usize::MAX),
        ];
        let sequences: &[&[Node<'_>]] = &[&root];
        let operations = [operation];
        let reader = SliceReader::new(sequences, &operations);
        let effects = RefCell::new(Vec::new());
        let mut group = initial_group;
        let mut slot = initial_slot;
        let result = classify_optional_body(
            &reader,
            0,
            &collections(),
            &mut group,
            &mut slot,
            |open| {
                effects.borrow_mut().push(open.to_owned());
                Vec::new()
            },
            |_| panic!("overflow must precede collection helper"),
        );
        assert!(result.is_none());
        assert_eq!((group, slot), (initial_group, initial_slot));
        assert_eq!(*effects.borrow(), ["PREFIX"]);
        let mut expected_visits = vec![Visit::Node(0, 0), Visit::Node(0, 1), Visit::Operation(0)];
        if initial_slot == u8::MAX {
            expected_visits.push(Visit::Node(0, 2));
        }
        assert_eq!(*reader.visits.borrow(), expected_visits);
    }
}
