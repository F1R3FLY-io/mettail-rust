use super::*;
use std::cell::RefCell;

#[derive(Clone, Copy)]
enum Param {
    Simple,
    Guard,
    Abs,
    Multi,
    Optional(usize),
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Read {
    Length(usize),
    Index(usize, usize),
    Param(usize),
    Context(usize),
    Items(usize),
    Item(bool),
}
struct Reader {
    params: Vec<Param>,
    sequences: Vec<Vec<usize>>,
    rules: Vec<(Option<usize>, Vec<bool>)>,
    reads: RefCell<Vec<Read>>,
}
impl<'a> TermParamReader<'a> for Reader {
    type Parameters = usize;
    type Param = usize;
    type Name = usize;
    type Type = usize;
    fn params_len(&self, params: usize) -> usize {
        self.reads.borrow_mut().push(Read::Length(params));
        self.sequences[params].len()
    }
    fn param_at(&self, params: usize, index: usize) -> Option<usize> {
        self.reads.borrow_mut().push(Read::Index(params, index));
        self.sequences[params].get(index).copied()
    }
    fn param(&self, param: usize) -> TermParamObservation<usize, usize, usize> {
        self.reads.borrow_mut().push(Read::Param(param));
        match self.params[param] {
            Param::Simple => TermParamObservation::Simple { name: param + 10, ty: param + 20 },
            Param::Guard => TermParamObservation::GuardBody { name: param + 10 },
            Param::Abs => TermParamObservation::Abstraction { binder: 10, body: 11, ty: 20 },
            Param::Multi => TermParamObservation::MultiAbstraction { binder: 12, body: 13, ty: 21 },
            Param::Optional(params) => TermParamObservation::Optional { params },
        }
    }
}
impl<'a> BinderPresenceReader<'a> for &'a Reader {
    type Rule = usize;
    type Item = bool;
    fn context(&self, rule: usize) -> Option<usize> {
        self.reads.borrow_mut().push(Read::Context(rule));
        self.rules[rule].0
    }
    fn items(&self, rule: usize) -> &'a [bool] {
        self.reads.borrow_mut().push(Read::Items(rule));
        &self.rules[rule].1
    }
    fn item_is_binder(&self, item: &bool) -> bool {
        self.reads.borrow_mut().push(Read::Item(*item));
        *item
    }
}
impl<'a> TermParamReader<'a> for &'a Reader {
    type Parameters = usize;
    type Param = usize;
    type Name = usize;
    type Type = usize;
    fn params_len(&self, params: usize) -> usize {
        Reader::params_len(self, params)
    }
    fn param_at(&self, params: usize, index: usize) -> Option<usize> {
        Reader::param_at(self, params, index)
    }
    fn param(&self, param: usize) -> TermParamObservation<usize, usize, usize> {
        Reader::param(self, param)
    }
}
fn fixture() -> Reader {
    Reader {
        params: vec![Param::Simple, Param::Optional(1), Param::Guard, Param::Abs, Param::Multi],
        sequences: vec![vec![0, 1, 4], vec![2, 3, 2], vec![], vec![0, 2]],
        rules: vec![
            (Some(0), vec![false, true, false]),
            (None, vec![true]),
            (Some(3), vec![false]),
            (Some(2), vec![]),
        ],
        reads: RefCell::new(Vec::new()),
    }
}

#[test]
fn original_worker_retains_leaf_order_identity_flags_and_two_reads() {
    let reader = fixture();
    let leaves: Vec<_> = TermParamLeaves::new(&reader, 0, false).collect();
    assert_eq!(
        leaves
            .iter()
            .map(|leaf| (leaf.kind.param(), leaf.is_optional))
            .collect::<Vec<_>>(),
        vec![(0, false), (2, true), (3, true), (2, true), (4, false)]
    );
    assert!(matches!(
        leaves[0].kind,
        TermParamLeafKind::Simple { param: 0, name: 10, ty: 20 }
    ));
    assert!(matches!(leaves[1].kind, TermParamLeafKind::GuardBody { param: 2, name: 12 }));
    assert!(matches!(
        leaves[2].kind,
        TermParamLeafKind::Abstraction { param: 3, binder: 10, body: 11, ty: 20 }
    ));
    assert!(matches!(
        leaves[4].kind,
        TermParamLeafKind::MultiAbstraction { param: 4, binder: 12, body: 13, ty: 21 }
    ));
    assert_eq!(
        *reader.reads.borrow(),
        vec![
            Read::Length(0),
            Read::Index(0, 2),
            Read::Index(0, 1),
            Read::Index(0, 0),
            Read::Param(0),
            Read::Param(0),
            Read::Param(1),
            Read::Length(1),
            Read::Index(1, 2),
            Read::Index(1, 1),
            Read::Index(1, 0),
            Read::Param(2),
            Read::Param(2),
            Read::Param(3),
            Read::Param(3),
            Read::Param(2),
            Read::Param(2),
            Read::Param(4),
            Read::Param(4),
        ]
    );
}

type Event = BinderPresenceEvent<usize, usize, usize>;
fn event_read(reader: &Reader, event: Event) -> Option<Read> {
    match event {
        Event::ReadContext(rule) => Some(Read::Context(rule)),
        Event::ReadItems(rule) => Some(Read::Items(rule)),
        Event::ReadItem { rule, index } => Some(Read::Item(reader.rules[rule].1[index])),
        Event::Parameter(event) => match event {
            TermParamWalkEvent::ReadLength(params) => Some(Read::Length(params)),
            TermParamWalkEvent::ReadIndex { params, index } => Some(Read::Index(params, index)),
            TermParamWalkEvent::ObserveFirst(param) | TermParamWalkEvent::ObserveSecond(param) => {
                Some(Read::Param(param))
            },
            _ => None,
        },
    }
}

#[test]
fn every_admission_failure_is_exact_prefix_without_later_source_reads() {
    let reader = fixture();
    let mut baseline = Vec::new();
    assert_eq!(
        try_declares_binder(&&reader, [2, 3, 0, 1], |event| {
            baseline.push(event);
            Ok::<_, usize>(())
        }),
        Ok(true)
    );
    assert_eq!(
        *reader.reads.borrow(),
        baseline
            .iter()
            .filter_map(|e| event_read(&reader, *e))
            .collect::<Vec<_>>()
    );
    for denied in 0..baseline.len() {
        reader.reads.borrow_mut().clear();
        let mut seen = Vec::new();
        let result = try_declares_binder(&&reader, [2, 3, 0, 1], |event| {
            seen.push(event);
            if seen.len() == denied + 1 {
                Err(denied)
            } else {
                Ok(())
            }
        });
        assert_eq!(result, Err(BinderPresenceError::Admission(denied)));
        assert_eq!(seen, baseline[..=denied]);
        assert_eq!(
            *reader.reads.borrow(),
            baseline[..denied]
                .iter()
                .filter_map(|e| event_read(&reader, *e))
                .collect::<Vec<_>>()
        );
    }
}

#[test]
fn true_context_still_reads_items_and_outer_any_stops_first_true() {
    let reader = fixture();
    let mut events = Vec::new();
    assert_eq!(
        try_declares_binder(&&reader, [0, 1], |event| {
            events.push(event);
            Ok::<_, ()>(())
        }),
        Ok(true)
    );
    assert!(events.contains(&Event::ReadItems(0)));
    assert!(events.contains(&Event::ReadItem { rule: 0, index: 1 }));
    assert!(!events.contains(&Event::ReadItem { rule: 0, index: 2 }));
    assert!(!events.contains(&Event::ReadContext(1)));
    assert!(!events.contains(&Event::Parameter(TermParamWalkEvent::PopFrame(4))));
    assert_eq!(
        try_rule_declares_binder(&&reader, 0, |event| {
            if event == Event::ReadItems(0) {
                Err("items denied")
            } else {
                Ok(())
            }
        }),
        Err(BinderPresenceError::Admission("items denied"))
    );
}

#[test]
fn absence_empty_and_legacy_binder_preserve_original_answers() {
    let reader = fixture();
    assert!(!params_declares_binder(&reader, 2));
    assert!(!params_declares_binder(&reader, 3));
    assert!(!declares_binder(&&reader, []));
    assert!(!declares_binder(&&reader, [2, 3]));
    assert!(rule_declares_binder(&&reader, 1));
    assert!(declares_binder(&&reader, [2, 3, 1]));
}

#[test]
fn nested_optional_scan_and_drop_are_stack_safe() {
    std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(|| {
            let depth = 20_000;
            let mut params = Vec::with_capacity(depth + 1);
            let mut sequences = Vec::with_capacity(depth + 1);
            for index in 0..depth {
                params.push(Param::Optional(index + 1));
                sequences.push(vec![index]);
            }
            params.push(Param::Abs);
            sequences.push(vec![depth]);
            let reader = Reader {
                params,
                sequences,
                rules: vec![],
                reads: RefCell::new(Vec::new()),
            };
            assert!(params_declares_binder(&reader, 0));
            drop(reader);
        })
        .expect("spawn small-stack parameter test")
        .join()
        .expect("parameter traversal and drop");
}

#[test]
fn invalid_reader_index_returns_no_boolean() {
    struct Invalid;
    impl<'a> TermParamReader<'a> for Invalid {
        type Parameters = ();
        type Param = ();
        type Name = ();
        type Type = ();
        fn params_len(&self, _: ()) -> usize {
            1
        }
        fn param_at(&self, _: (), _: usize) -> Option<()> {
            None
        }
        fn param(&self, _: ()) -> TermParamObservation<(), (), ()> {
            panic!("must not observe missing parameter")
        }
    }
    let mut events = Vec::new();
    assert_eq!(
        try_params_declares_binder(&Invalid, (), |event| {
            events.push(event);
            Ok::<_, ()>(())
        }),
        Err(BinderPresenceError::InvalidParameterIndex { index: 0 })
    );
    assert_eq!(
        events,
        vec![
            TermParamWalkEvent::ReadLength(()),
            TermParamWalkEvent::ReserveFrames(1),
            TermParamWalkEvent::ReadIndex { params: (), index: 0 }
        ]
    );
}
