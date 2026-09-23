use mettail_grammar_core::context_items::{
    convert_term_context_to_items_with, try_convert_term_context_to_items_with, ContextItemsError,
    ContextItemsEvent, ContextItemsReader,
};
use mettail_grammar_core::{TermParamObservation, TermParamReader};
use std::cell::RefCell;

#[derive(Clone, Copy)]
enum Ty {
    Base(u8),
    Collection(u8, usize),
    Map(usize, usize),
    Arrow(usize, usize),
    Multi(usize),
    Other,
}
#[derive(Debug, PartialEq, Eq)]
enum Item {
    Nonterminal(u8),
    Binder(u8),
    Collection(u8, u8, &'static str),
}

struct Reader {
    types: Vec<Ty>,
    params: Vec<TermParamObservation<u8, usize, usize>>,
    lists: Vec<Vec<usize>>,
    log: RefCell<Vec<String>>,
}

impl<'a> TermParamReader<'a> for Reader {
    type Parameters = usize;
    type Param = usize;
    type Name = u8;
    type Type = usize;
    fn params_len(&self, list: usize) -> usize {
        self.log.borrow_mut().push(format!("length:{list}"));
        self.lists[list].len()
    }
    fn param_at(&self, list: usize, index: usize) -> Option<usize> {
        self.log.borrow_mut().push(format!("access:{list}:{index}"));
        self.lists[list].get(index).copied()
    }
    fn param(&self, param: usize) -> TermParamObservation<u8, usize, usize> {
        self.log.borrow_mut().push(format!("read:{param}"));
        match self.params[param] {
            TermParamObservation::Simple { name, ty } => TermParamObservation::Simple { name, ty },
            TermParamObservation::GuardBody { name } => TermParamObservation::GuardBody { name },
            TermParamObservation::Abstraction { binder, body, ty } => {
                TermParamObservation::Abstraction { binder, body, ty }
            },
            TermParamObservation::MultiAbstraction { binder, body, ty } => {
                TermParamObservation::MultiAbstraction { binder, body, ty }
            },
            TermParamObservation::Optional { params } => TermParamObservation::Optional { params },
        }
    }
}
impl<'a> ContextItemsReader<'a> for Reader {
    type CollectionKind = u8;
    type Item = Item;
    fn base_name(&self, ty: usize) -> Option<u8> {
        if let Ty::Base(name) = self.types[ty] {
            Some(name)
        } else {
            None
        }
    }
    fn collection(&self, ty: usize) -> Option<(u8, usize)> {
        if let Ty::Collection(kind, element) = self.types[ty] {
            Some((kind, element))
        } else {
            None
        }
    }
    fn map(&self, ty: usize) -> Option<(usize, usize)> {
        if let Ty::Map(key, value) = self.types[ty] {
            Some((key, value))
        } else {
            None
        }
    }
    fn arrow(&self, ty: usize) -> Option<(usize, usize)> {
        if let Ty::Arrow(domain, body) = self.types[ty] {
            Some((domain, body))
        } else {
            None
        }
    }
    fn multi_binder(&self, ty: usize) -> Option<usize> {
        if let Ty::Multi(inner) = self.types[ty] {
            Some(inner)
        } else {
            None
        }
    }
    fn names_equal(&self, left: u8, right: u8) -> bool {
        left == right
    }
    fn hash_map_kind(&self) -> u8 {
        9
    }
    fn make_nonterminal(&self, name: u8) -> Item {
        self.log.borrow_mut().push(format!("make:nt:{name}"));
        Item::Nonterminal(name)
    }
    fn make_binder(&self, name: u8) -> Item {
        self.log.borrow_mut().push(format!("make:binder:{name}"));
        Item::Binder(name)
    }
    fn make_collection(&self, kind: u8, element: u8, sep: &'static str) -> Item {
        self.log
            .borrow_mut()
            .push(format!("make:collection:{kind}:{element}:{sep}"));
        Item::Collection(kind, element, sep)
    }
}

fn fixture() -> Reader {
    use TermParamObservation::*;
    Reader {
        types: vec![
            Ty::Base(1),
            Ty::Base(2),
            Ty::Collection(3, 0),
            Ty::Map(0, 0),
            Ty::Map(0, 1),
            Ty::Arrow(0, 1),
            Ty::Multi(0),
            Ty::Arrow(6, 1),
            Ty::Other,
            Ty::Arrow(8, 8),
        ],
        params: vec![
            Simple { name: 0, ty: 0 },
            Simple { name: 0, ty: 2 },
            Simple { name: 0, ty: 3 },
            Simple { name: 0, ty: 4 },
            Abstraction { binder: 0, body: 0, ty: 5 },
            MultiAbstraction { binder: 0, body: 0, ty: 7 },
            Abstraction { binder: 0, body: 0, ty: 9 },
            GuardBody { name: 0 },
            Optional { params: 1 },
            Optional { params: 2 },
        ],
        lists: vec![(0..9).collect(), vec![4, 9, 5], vec![0, 7]],
        log: RefCell::new(Vec::new()),
    }
}

#[test]
fn successful_admission_preserves_all_original_output_and_constructor_order() {
    let reader = fixture();
    let original = convert_term_context_to_items_with(&reader, 0);
    let original_log = reader.log.replace(Vec::new());
    let mut events = Vec::new();
    let admitted = try_convert_term_context_to_items_with(&reader, 0, |event| {
        events.push(event);
        Ok::<_, ()>(())
    })
    .expect("all visits and constructions admitted");
    assert_eq!(admitted, original);
    assert_eq!(*reader.log.borrow(), original_log);
    assert_eq!(admitted.1, vec![(3, vec![4]), (5, vec![6]), (7, vec![7])]);
    assert_eq!(
        events
            .iter()
            .filter(|event| matches!(event, ContextItemsEvent::Binding))
            .count(),
        3
    );
    assert_eq!(
        events
            .iter()
            .filter(|event| matches!(event, ContextItemsEvent::EnterOptional))
            .count(),
        2
    );
}

#[test]
fn each_refusal_is_an_exact_prefix_before_the_unpaid_operation() {
    let reader = fixture();
    let mut events = 0;
    try_convert_term_context_to_items_with(&reader, 0, |event| {
        reader.log.borrow_mut().push(format!("admit:{event:?}"));
        events += 1;
        Ok::<_, usize>(())
    })
    .expect("reference schedule admitted");
    let complete = reader.log.replace(Vec::new());
    let sites: Vec<_> = complete
        .iter()
        .enumerate()
        .filter_map(|(index, entry)| entry.starts_with("admit:").then_some(index))
        .collect();
    assert_eq!(sites.len(), events);
    for (rejected, &site) in sites.iter().enumerate() {
        let mut seen = 0;
        let result = try_convert_term_context_to_items_with(&reader, 0, |event| {
            reader.log.borrow_mut().push(format!("admit:{event:?}"));
            let index = seen;
            seen += 1;
            if index == rejected {
                Err(index)
            } else {
                Ok(())
            }
        });
        assert_eq!(result, Err(ContextItemsError::Admission(rejected)));
        assert_eq!(reader.log.replace(Vec::new()), complete[..=site], "refusal {rejected}");
    }
}

#[test]
fn first_unpaid_visit_does_not_access_the_parameter() {
    let reader = fixture();
    let result = try_convert_term_context_to_items_with(&reader, 0, |_| Err("budget"));
    assert_eq!(result, Err(ContextItemsError::Admission("budget")));
    assert_eq!(*reader.log.borrow(), ["length:0"]);
}

#[test]
fn shared_optional_dag_is_charged_per_occurrence_and_refuses_promptly() {
    use TermParamObservation::*;
    let mut reader = Reader {
        types: vec![Ty::Base(1)],
        params: vec![Simple { name: 0, ty: 0 }],
        lists: vec![vec![0]],
        log: RefCell::new(Vec::new()),
    };
    for level in 1..=28 {
        reader.params.push(Optional { params: level - 1 });
        reader.lists.push(vec![level, level]);
    }
    let mut visits = 0;
    let result = try_convert_term_context_to_items_with(&reader, 28, |event| {
        if matches!(event, ContextItemsEvent::VisitParameter) {
            if visits == 100 {
                return Err("visit limit");
            }
            visits += 1;
        }
        Ok(())
    });
    assert_eq!(result, Err(ContextItemsError::Admission("visit limit")));
    assert_eq!(visits, 100);
    assert_eq!(
        reader
            .log
            .borrow()
            .iter()
            .filter(|entry| entry.starts_with("read:"))
            .count(),
        100
    );
}

#[test]
fn deep_optional_frames_and_cleanup_remain_stack_safe() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            use TermParamObservation::*;
            let depth = 20_000;
            let mut reader = Reader {
                types: vec![Ty::Base(1)],
                params: Vec::with_capacity(depth + 1),
                lists: Vec::with_capacity(depth + 1),
                log: RefCell::new(Vec::new()),
            };
            reader.params.push(Simple { name: 0, ty: 0 });
            reader.lists.push(vec![0]);
            for level in 1..=depth {
                reader.params.push(Optional { params: level - 1 });
                reader.lists.push(vec![level]);
            }
            let mut visits = 0;
            let output = try_convert_term_context_to_items_with(&reader, depth, |event| {
                if matches!(event, ContextItemsEvent::VisitParameter) {
                    visits += 1;
                }
                Ok::<_, ()>(())
            })
            .expect("finite deep source admitted");
            assert_eq!(visits, depth + 1);
            assert_eq!(output, (vec![Item::Nonterminal(1)], vec![]));
        })
        .expect("small stack thread starts")
        .join()
        .expect("iterative traversal and drop complete");
}
