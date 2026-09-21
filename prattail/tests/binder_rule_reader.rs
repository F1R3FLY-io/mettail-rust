//! Main classifier observations over flat, owned handle stores.

use std::cell::RefCell;
use std::fmt;

use mettail_ast::grammar::DelimitedRegionKind;
use mettail_ast::types::CollectionType;
use mettail_prattail::wpda_rule_analysis::binder::optional::{
    BinderSyntaxObservation, BinderSyntaxReader, OptionalOperationObservation,
};
use mettail_prattail::wpda_rule_analysis::binder::rule::{
    classify_binder_in, BinderRuleReader, BinderTypeObservation, MapZipObservation,
};
use mettail_prattail::wpda_rule_analysis::binder::term_param::{
    TermParamObservation, TermParamReader,
};
use mettail_prattail::wpda_rule_analysis::binder::{
    ActionArgKind, BinderPosition, BinderShape, CollectionSepInfo,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Name {
    spelling: &'static str,
    identity: usize,
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.spelling)
    }
}

fn name(spelling: &'static str) -> Name {
    Name { spelling, identity: 0 }
}

#[derive(Clone, Copy)]
enum Node {
    Literal(&'static str),
    Param(Name),
    Guest(Name),
    Op(usize),
}

#[derive(Clone, Copy)]
enum Operation {
    Sep(Name, Option<usize>),
    Opt(usize),
    Map {
        source: usize,
        params: usize,
        body: usize,
    },
    Zip {
        left: Name,
        right: Name,
    },
}

#[derive(Clone, Copy)]
enum Param {
    Simple(Name, usize),
    Multi(Name, Name, usize),
}

#[derive(Clone, Copy)]
enum Ty {
    Base(Name),
    Collection(&'static CollectionType, usize),
    Map(usize, usize),
    Arrow(usize),
}

struct Reader {
    context: Option<usize>,
    pattern: Option<usize>,
    syntax: Vec<Vec<Node>>,
    operations: Vec<Operation>,
    params: Vec<Vec<Param>>,
    types: Vec<Ty>,
    names: Vec<Vec<Name>>,
    equalities: RefCell<Vec<(Name, Name)>>,
}

impl Default for Reader {
    fn default() -> Self {
        Self {
            context: Some(0),
            pattern: Some(0),
            syntax: vec![vec![]],
            operations: vec![],
            params: vec![vec![]],
            types: vec![],
            names: vec![],
            equalities: RefCell::new(vec![]),
        }
    }
}

impl<'s> BinderSyntaxReader<'s> for Reader {
    type Sequence = usize;
    type Name = Name;
    type Operation = usize;

    fn sequence_len(&self, sequence: usize) -> usize {
        self.syntax[sequence].len()
    }

    fn at(
        &self,
        sequence: usize,
        index: usize,
    ) -> Option<BinderSyntaxObservation<'s, Name, usize>> {
        Some(match *self.syntax[sequence].get(index)? {
            Node::Literal(text) => BinderSyntaxObservation::Literal(text),
            Node::Param(name) => BinderSyntaxObservation::Param(name),
            Node::Guest(open) => BinderSyntaxObservation::GuestBody {
                open,
                close: name("Close"),
                bind: name("guest"),
                kind: DelimitedRegionKind::Flt,
            },
            Node::Op(operation) => BinderSyntaxObservation::Op(operation),
        })
    }

    fn operation(&self, operation: usize) -> OptionalOperationObservation<'s, Name, usize, usize> {
        match self.operations[operation] {
            Operation::Sep(collection, source) => {
                OptionalOperationObservation::Sep { collection, separator: ",", source }
            },
            Operation::Opt(inner) => OptionalOperationObservation::Opt { inner },
            Operation::Map { .. } | Operation::Zip { .. } => {
                OptionalOperationObservation::Other(operation)
            },
        }
    }
}

impl<'s> TermParamReader<'s> for Reader {
    type Parameters = usize;
    type Param = (usize, usize);
    type Name = Name;
    type Type = usize;

    fn params_len(&self, params: usize) -> usize {
        self.params[params].len()
    }

    fn param_at(&self, params: usize, index: usize) -> Option<(usize, usize)> {
        self.params[params].get(index).map(|_| (params, index))
    }

    fn param(&self, (params, index): (usize, usize)) -> TermParamObservation<Name, usize, usize> {
        match self.params[params][index] {
            Param::Simple(name, ty) => TermParamObservation::Simple { name, ty },
            Param::Multi(binder, body, ty) => {
                TermParamObservation::MultiAbstraction { binder, body, ty }
            },
        }
    }
}

impl<'s> BinderRuleReader<'s> for Reader {
    type Rule = ();
    type Names = usize;

    fn term_context(&self, (): ()) -> Option<usize> {
        self.context
    }

    fn syntax_pattern(&self, (): ()) -> Option<usize> {
        self.pattern
    }

    fn label(&self, (): ()) -> Name {
        name("Projection")
    }

    fn category(&self, (): ()) -> Name {
        name("Expr")
    }

    fn ty(&self, ty: usize) -> BinderTypeObservation<'s, Name, usize> {
        match self.types[ty] {
            Ty::Base(name) => BinderTypeObservation::Base(name),
            Ty::Collection(coll_type, element) => {
                BinderTypeObservation::Collection { coll_type, element }
            },
            Ty::Map(key, value) => BinderTypeObservation::Map { key, value },
            Ty::Arrow(codomain) => BinderTypeObservation::Arrow { codomain },
        }
    }

    fn names_len(&self, names: usize) -> usize {
        self.names[names].len()
    }

    fn name_at(&self, names: usize, index: usize) -> Option<Name> {
        self.names[names].get(index).copied()
    }

    fn names_equal(&self, left: Name, right: Name) -> bool {
        self.equalities.borrow_mut().push((left, right));
        left == right
    }

    fn map_zip_operation(&self, operation: usize) -> MapZipObservation<Name, usize, usize, usize> {
        match self.operations[operation] {
            Operation::Map { source, params, body } => {
                MapZipObservation::Map { source, params, body }
            },
            Operation::Zip { left, right } => MapZipObservation::Zip { left, right },
            _ => MapZipObservation::Other(operation),
        }
    }
}

fn run(reader: &Reader, effects: &RefCell<Vec<String>>) -> Option<BinderShape> {
    classify_binder_in(
        reader,
        (),
        || {
            effects.borrow_mut().push("resolve".into());
            77_u32
        },
        |open| {
            effects.borrow_mut().push(format!("guest:{open}"));
            vec![format!("{open}_nested")]
        },
        |kind, delims| {
            effects.borrow_mut().push(format!("kv:{kind:?}:{delims}"));
            matches!(kind, CollectionType::HashMap).then(|| ":".into())
        },
    )
}

fn shape(positions: Vec<BinderPosition>, action_args: Vec<ActionArgKind>) -> BinderShape {
    BinderShape {
        label: "Projection".into(),
        result_cat: "Expr".into(),
        leading_category: None,
        leading_ident_capture: None,
        positions,
        is_multi: false,
        has_binder: false,
        action_arity: action_args.len().try_into().expect("small fixture"),
        action_args,
        body_cat: None,
        param_cats: vec![],
    }
}

fn collection(cat: &str, close: &str, slot_idx: u8, kv: Option<&str>) -> BinderPosition {
    BinderPosition::ParamParse {
        cat: cat.into(),
        collection: Some(CollectionSepInfo {
            separator: ",".into(),
            close: close.into(),
            elem_cat: cat.into(),
            key_val_separator: kv.map(str::to_owned),
            slot_idx,
        }),
    }
}

fn drain(cat: &str, coll_kind: CollectionType) -> ActionArgKind {
    ActionArgKind::CollectionDrain { elem_cat: cat.into(), coll_kind }
}

#[test]
fn resolver_runs_after_context_and_empty_syntax_gates_before_structural_refusals() {
    for case in 0..5 {
        let mut reader = Reader::default();
        match case {
            0 => {
                reader.context = None;
                reader.pattern = Some(usize::MAX);
            },
            1 => reader.pattern = None,
            2 => {}, // Present but empty syntax.
            3 => reader.syntax[0] = vec![Node::Op(usize::MAX)],
            4 => {
                reader.params[0] = vec![Param::Simple(name("xs"), 1)];
                reader.types =
                    vec![Ty::Base(name("Name")), Ty::Collection(&CollectionType::Vec, 0)];
                reader.operations = vec![Operation::Sep(name("xs"), None)];
                reader.syntax[0] = vec![Node::Literal("["), Node::Op(0), Node::Literal("]")];
            },
            _ => unreachable!(),
        }
        let effects = RefCell::new(vec![]);
        assert!(run(&reader, &effects).is_none());
        let expected: Vec<String> = if case < 3 {
            vec![]
        } else {
            vec!["resolve".into()]
        };
        assert_eq!(*effects.borrow(), expected, "gate case {case}");
    }
}

#[test]
fn late_failure_preserves_ordered_resolver_guest_and_collection_callbacks() {
    let reader = Reader {
        syntax: vec![
            vec![
                Node::Guest(name("Leading")),
                Node::Guest(name("Outer")),
                Node::Op(0),
                Node::Literal(";"),
                Node::Op(1),
                Node::Param(name("missing")),
                Node::Op(usize::MAX),
            ],
            vec![
                Node::Literal("with"),
                Node::Guest(name("Inner")),
                Node::Op(2),
                Node::Literal("]"),
            ],
        ],
        operations: vec![
            Operation::Sep(name("xs"), None),
            Operation::Opt(1),
            Operation::Sep(name("pairs"), None),
        ],
        params: vec![vec![Param::Simple(name("xs"), 1), Param::Simple(name("pairs"), 2)]],
        types: vec![
            Ty::Base(name("Name")),
            Ty::Collection(&CollectionType::Vec, 0),
            Ty::Collection(&CollectionType::HashMap, 0),
        ],
        ..Reader::default()
    };
    let effects = RefCell::new(vec![]);
    assert!(run(&reader, &effects).is_none());
    assert_eq!(
        *effects.borrow(),
        ["resolve", "guest:Outer", "kv:Vec:77", "guest:Inner", "kv:HashMap:77"]
    );
}

#[test]
fn map_type_uses_raw_name_identity_even_when_spellings_match() {
    let key = name("Name");
    for identity in [0, 1] {
        let value = Name { spelling: "Name", identity };
        let reader = Reader {
            syntax: vec![vec![Node::Literal("["), Node::Op(0), Node::Literal("]")]],
            operations: vec![Operation::Sep(name("pairs"), None)],
            params: vec![vec![Param::Simple(name("pairs"), 2)]],
            types: vec![Ty::Base(key), Ty::Base(value), Ty::Map(0, 1)],
            ..Reader::default()
        };
        let effects = RefCell::new(vec![]);
        let actual = run(&reader, &effects);
        assert_eq!(*reader.equalities.borrow(), [(key, value)]);
        if identity == 0 {
            let mut expected = shape(
                vec![collection("Name", "]", 0, Some(":"))],
                vec![drain("Name", CollectionType::HashMap)],
            );
            expected.param_cats = vec!["Name".into()];
            assert_eq!(
                format!("{:?}", actual.expect("identical map types")),
                format!("{expected:?}")
            );
            assert_eq!(*effects.borrow(), ["resolve", "kv:HashMap:77"]);
        } else {
            assert!(actual.is_none());
            assert_eq!(*effects.borrow(), ["resolve"]);
        }
    }
}

#[test]
fn map_zip_and_optional_collections_share_slots_but_aliases_use_spelling() {
    let reader = Reader {
        syntax: vec![
            vec![
                Node::Literal("start"),
                Node::Op(0),
                Node::Literal(";"),
                Node::Op(1),
                Node::Literal(")"),
                Node::Op(4),
                Node::Op(6),
            ],
            vec![Node::Literal("with"), Node::Op(5), Node::Literal("]")],
            vec![
                Node::Param(Name { spelling: "x", identity: 1 }),
                Node::Literal("?"),
                Node::Param(Name { spelling: "n", identity: 1 }),
            ],
        ],
        operations: vec![
            Operation::Sep(name("prefix"), None),
            Operation::Sep(name("ignored"), Some(2)),
            Operation::Map { source: 3, params: 0, body: 2 },
            Operation::Zip { left: name("names"), right: name("xs") },
            Operation::Opt(1),
            Operation::Sep(name("suffix"), None),
            Operation::Sep(name("prefix"), None),
        ],
        params: vec![vec![
            Param::Simple(name("prefix"), 2),
            Param::Simple(name("names"), 3),
            Param::Multi(name("xs"), name("body"), 4),
            Param::Simple(name("suffix"), 5),
        ]],
        types: vec![
            Ty::Base(name("Expr")),
            Ty::Base(name("Name")),
            Ty::Collection(&CollectionType::Vec, 0),
            Ty::Collection(&CollectionType::HashSet, 1),
            Ty::Arrow(0),
            Ty::Collection(&CollectionType::HashMap, 1),
        ],
        names: vec![vec![name("n"), name("x")]],
        ..Reader::default()
    };
    let effects = RefCell::new(vec![]);
    let actual = run(&reader, &effects).expect("composed slot fixture");
    let mut expected = shape(
        vec![
            collection("Expr", ";", 0, None),
            BinderPosition::BinderListLoop {
                separator: ",".into(),
                close: ")".into(),
                inner_positions: vec![
                    BinderPosition::BinderIdent,
                    BinderPosition::Literal("?".into()),
                    collection("Name", ")", 0, None),
                ],
                collection_param_cat: Some("Name".into()),
                allow_empty: true,
                allow_multi: true,
                slot_idx: 1,
            },
            BinderPosition::OptionalGroup {
                positions: vec![
                    BinderPosition::Literal("with".into()),
                    collection("Name", "]", 2, Some(":")),
                ],
                group_idx: 0,
                first_token_set: vec!["with".into()],
            },
            collection("Expr", "", 3, None),
        ],
        vec![
            drain("Expr", CollectionType::Vec),
            drain("Name", CollectionType::Vec),
            ActionArgKind::BinderList,
            ActionArgKind::Optional(vec![drain("Name", CollectionType::HashMap)]),
            drain("Expr", CollectionType::Vec),
        ],
    );
    expected.is_multi = true;
    expected.has_binder = true;
    expected.body_cat = Some("Expr".into());
    expected.param_cats = vec!["Expr".into(), "Name".into(), "Name".into()];
    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    assert_eq!(*effects.borrow(), ["resolve", "kv:Vec:77", "kv:HashMap:77", "kv:Vec:77"]);
    assert!(
        reader.equalities.borrow().is_empty(),
        "Map/Zip aliases use spelling, not raw identity"
    );
}
