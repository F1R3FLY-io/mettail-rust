//! Traverse borrowed parameter observations backed by flat integer-handle stores.

use mettail_prattail::wpda_rule_analysis::binder::term_param::{
    TermParamLeafKind, TermParamLeaves, TermParamObservation, TermParamReader,
};

#[derive(Clone, Copy)]
enum Param {
    Simple { name: usize, ty: usize },
    GuardBody { name: usize },
    Abstraction { binder: usize, body: usize, ty: usize },
    MultiAbstraction { binder: usize, body: usize, ty: usize },
    Optional { params: usize },
}

struct FlatReader {
    sequences: Vec<Vec<usize>>,
    params: Vec<Param>,
}

impl<'syntax> TermParamReader<'syntax> for FlatReader {
    type Parameters = usize;
    type Param = usize;
    type Name = usize;
    type Type = usize;

    fn params_len(&self, params: usize) -> usize {
        self.sequences[params].len()
    }

    fn param_at(&self, params: usize, index: usize) -> Option<usize> {
        self.sequences[params].get(index).copied()
    }

    fn param(&self, param: usize) -> TermParamObservation<usize, usize, usize> {
        match self.params[param] {
            Param::Simple { name, ty } => TermParamObservation::Simple { name, ty },
            Param::GuardBody { name } => TermParamObservation::GuardBody { name },
            Param::Abstraction { binder, body, ty } => {
                TermParamObservation::Abstraction { binder, body, ty }
            },
            Param::MultiAbstraction { binder, body, ty } => {
                TermParamObservation::MultiAbstraction { binder, body, ty }
            },
            Param::Optional { params } => TermParamObservation::Optional { params },
        }
    }
}

// Record each yielded leaf without traversing or projecting the input ourselves.
type Record = (usize, &'static str, Vec<usize>, bool);

fn records(reader: &FlatReader, params: usize, is_optional: bool) -> Vec<Record> {
    TermParamLeaves::new(reader, params, is_optional)
        .map(|leaf| {
            let original = leaf.kind.param();
            let (param, kind, payload) = match leaf.kind {
                TermParamLeafKind::Simple { param, name, ty } => (param, "simple", vec![name, ty]),
                TermParamLeafKind::GuardBody { param, name } => (param, "guard", vec![name]),
                TermParamLeafKind::Abstraction { param, binder, body, ty } => {
                    (param, "abstraction", vec![binder, body, ty])
                },
                TermParamLeafKind::MultiAbstraction { param, binder, body, ty } => {
                    (param, "multi", vec![binder, body, ty])
                },
            };
            assert_eq!(original, param, "param() must preserve the original parameter handle");
            (original, kind, payload, leaf.is_optional)
        })
        .collect()
}

#[test]
fn ordered_payloads_preserve_handles_and_optional_context() {
    let reader = FlatReader {
        sequences: vec![
            vec![0, 1, 2, 3, 5, 4, 0, 8],
            vec![1, 6, 5, 2],
            vec![],
            vec![7, 3],
            vec![0, 1],
        ],
        params: vec![
            Param::Simple { name: 11, ty: 101 },
            Param::GuardBody { name: 22 },
            Param::Abstraction { binder: 31, body: 32, ty: 103 },
            Param::MultiAbstraction { binder: 41, body: 42, ty: 104 },
            Param::Optional { params: 1 },
            Param::Optional { params: 2 },
            Param::Optional { params: 3 },
            Param::Simple { name: 71, ty: 107 },
            Param::Optional { params: 4 },
        ],
    };
    let expected = vec![
        (0, "simple", vec![11, 101], false),
        (1, "guard", vec![22], false),
        (2, "abstraction", vec![31, 32, 103], false),
        (3, "multi", vec![41, 42, 104], false),
        (1, "guard", vec![22], true),
        (7, "simple", vec![71, 107], true),
        (3, "multi", vec![41, 42, 104], true),
        (2, "abstraction", vec![31, 32, 103], true),
        (0, "simple", vec![11, 101], false),
        (0, "simple", vec![11, 101], true),
        (1, "guard", vec![22], true),
    ];
    for initial_optional in [false, true] {
        let expected_context: Vec<Record> = expected
            .iter()
            .map(|(param, kind, payload, optional)| {
                (*param, *kind, payload.clone(), *optional || initial_optional)
            })
            .collect();
        assert_eq!(records(&reader, 0, initial_optional), expected_context);
        assert!(records(&reader, 2, initial_optional).is_empty());
    }
}

#[test]
fn twenty_thousand_flat_optional_handles_fit_a_small_stack() {
    const DEPTH: usize = 20_000;
    let reader = FlatReader {
        sequences: (0..=DEPTH).map(|param| vec![param]).collect(),
        params: (0..DEPTH)
            .map(|index| Param::Optional { params: index + 1 })
            .chain(std::iter::once(Param::Simple { name: 7, ty: 8 }))
            .collect(),
    };
    std::thread::Builder::new()
        .name("flat-term-param-reader".into())
        .stack_size(256 * 1024)
        .spawn(move || {
            assert_eq!(records(&reader, 0, false), [(DEPTH, "simple", vec![7, 8], true)]);
        })
        .expect("spawn small-stack parameter traversal")
        .join()
        .expect("traverse and drop flat parameter storage without recursive projection");
}
