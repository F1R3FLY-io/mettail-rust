use super::*;
use std::cell::{Cell, RefCell};
use std::rc::Rc;

type Log = Rc<RefCell<Vec<String>>>;

struct User {
    label: &'static str,
    var: bool,
}

struct Declaration(&'static str);

// Neither the payload nor the adapter implements Clone. The success boundary
// returns the same Box allocation; every error drops that sole private owner.
struct Payload {
    label: String,
    var: bool,
    normalized: bool,
    live: Rc<Cell<usize>>,
}

impl Drop for Payload {
    fn drop(&mut self) {
        self.live.set(self.live.get() - 1);
    }
}

struct Adapter {
    log: Log,
    fail: Option<usize>,
    drops: Rc<Cell<usize>>,
    live: Rc<Cell<usize>>,
    owner: Box<u8>,
    recipes: Vec<SyntheticRule<()>>,
    binders: bool,
}

impl Drop for Adapter {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}

impl Adapter {
    fn record(&self, message: String) -> Result<(), usize> {
        let mut log = self.log.borrow_mut();
        let position = log.len();
        log.push(message);
        if self.fail == Some(position) {
            Err(position)
        } else {
            Ok(())
        }
    }

    fn payload(&self, label: String, var: bool) -> Payload {
        self.live.set(self.live.get() + 1);
        Payload {
            label,
            var,
            normalized: false,
            live: Rc::clone(&self.live),
        }
    }
}

fn callback_name(callback: SynthesisCallback<'_, User, Declaration, Payload, ()>) -> String {
    match callback {
        SynthesisCallback::CloneUser(user) => format!("clone:{}", user.label),
        SynthesisCallback::NormalizeUser(payload) => format!("normalize:{}", payload.label),
        SynthesisCallback::FirstItemIsVar(payload) => format!("scan:{}", payload.label),
        SynthesisCallback::Materialize(rule) => format!("emit:{}:{}", rule.category, rule.label),
        SynthesisCallback::HasLiteralBlock(declaration) => format!("probe:{}", declaration.0),
        SynthesisCallback::LiteralLabel(declaration) => format!("literal:{}", declaration.0),
        SynthesisCallback::Collection(declaration) => format!("collection:{}", declaration.0),
        SynthesisCallback::VarLabel(declaration) => format!("var:{}", declaration.0),
        SynthesisCallback::DeclaresBinder => "binders".into(),
    }
}

impl TrySynthesisAdapter for Adapter {
    type SourceUser = User;
    type SourceType = Declaration;
    type RulePayload = Payload;
    type CollectionKind = ();
    type Error = usize;

    fn admit(&mut self, event: SynthesisEventFor<'_, Self>) -> Result<(), usize> {
        let name = match event {
            SynthesisEvent::CategoryIndexSlots(count) => format!("index-slots:{count}"),
            SynthesisEvent::CategoryIndexEntry { index, name } => format!("index:{index}:{name}"),
            SynthesisEvent::BucketSlots(count) => format!("buckets:{count}"),
            SynthesisEvent::Visit(phase) => format!("visit:{phase:?}"),
            SynthesisEvent::CategoryLookup(name) => format!("lookup:{name}"),
            SynthesisEvent::RowSlot(index) => format!("row:{index}"),
            SynthesisEvent::StringCopy(text) => format!("copy:{text}"),
            SynthesisEvent::TrimOpen(text) => format!("trim:{text}"),
            SynthesisEvent::Lowercase(text) => format!("lower:{text}"),
            SynthesisEvent::Format { prefix, body, suffix } => {
                format!("format:{prefix}|{body}|{suffix}")
            },
            SynthesisEvent::RecipeSlots { items, params, syntax } => {
                format!("recipe:{items}:{params}:{syntax}")
            },
            SynthesisEvent::BinderNameSlots(count) => format!("names:{count}"),
            SynthesisEvent::VectorKindClone(()) => "vector-kind".into(),
            SynthesisEvent::Callback(callback) => format!("callback:{}", callback_name(callback)),
        };
        self.record(format!("admit:{name}"))
    }

    fn clone_user(&mut self, source: &User) -> Result<Payload, usize> {
        self.record(format!("call:clone:{}", source.label))?;
        Ok(self.payload(source.label.into(), source.var))
    }

    fn normalize_user(self, rule: &mut Payload) -> Result<Self, usize> {
        self.record(format!("call:normalize:{}", rule.label))?;
        rule.normalized = true;
        Ok(self)
    }

    fn first_item_is_var(&mut self, rule: &Payload) -> Result<bool, usize> {
        self.record(format!("call:scan:{}", rule.label))?;
        Ok(rule.var)
    }

    fn materialize_synthetic(mut self, rule: SyntheticRule<()>) -> Result<(Self, Payload), usize> {
        self.record(format!("call:emit:{}:{}", rule.category, rule.label))?;
        let var = matches!(
            rule.items.first(),
            Some(LegacyAtomicItem::NonTerminal { kind: LegacyAtomicKind::Var, .. })
        );
        let payload = self.payload(rule.label.clone(), var);
        self.recipes.push(rule);
        Ok((self, payload))
    }

    fn has_literal_block(&mut self, declaration: &Declaration) -> Result<bool, usize> {
        self.record(format!("call:probe:{}", declaration.0))?;
        Ok(false)
    }
    fn literal_label(&mut self, declaration: &Declaration) -> Result<String, usize> {
        self.record(format!("call:literal:{}", declaration.0))?;
        Ok(format!("{}Lit", declaration.0))
    }
    fn collection(&mut self, declaration: &Declaration) -> Result<CollectionRecipe<()>, usize> {
        self.record(format!("call:collection:{}", declaration.0))?;
        Ok(CollectionRecipe {
            kind: (),
            label: "BagLit".into(),
            element_category: "A".into(),
            open: "Bag(((".into(),
            close: "]".into(),
            separator: ";".into(),
        })
    }
    fn var_label(&mut self, declaration: &Declaration) -> Result<String, usize> {
        self.record(format!("call:var:{}", declaration.0))?;
        Ok(format!("{}Var", declaration.0))
    }
    fn declares_binder(&mut self) -> Result<bool, usize> {
        self.record("call:binders".into())?;
        Ok(self.binders)
    }
}

fn adapter(fail: Option<usize>) -> (Adapter, Log, Rc<Cell<usize>>, Rc<Cell<usize>>) {
    let log = Rc::new(RefCell::new(Vec::new()));
    let drops = Rc::new(Cell::new(0));
    let live = Rc::new(Cell::new(0));
    (
        Adapter {
            log: Rc::clone(&log),
            fail,
            drops: Rc::clone(&drops),
            live: Rc::clone(&live),
            owner: Box::new(17),
            recipes: Vec::new(),
            binders: true,
        },
        log,
        drops,
        live,
    )
}

fn fixture(adapter: Adapter) -> Result<(Adapter, Vec<Vec<Payload>>), SynthesisError<usize>> {
    let users = [
        User { label: "uA", var: false },
        User { label: "uB", var: true },
        User { label: "ignored", var: false },
    ];
    let user_inputs = [
        UserInput { category: "A".into(), source: &users[0] },
        UserInput { category: "B".into(), source: &users[1] },
        UserInput {
            category: "Missing".into(),
            source: &users[2],
        },
    ];
    let declarations =
        [Declaration("A"), Declaration("B"), Declaration("Missing"), Declaration("Data")];
    let types = [
        TypeInput {
            name: "A".into(),
            is_data: false,
            has_native: true,
            has_collection: false,
            source: &declarations[0],
        },
        TypeInput {
            name: "B".into(),
            is_data: false,
            has_native: false,
            has_collection: true,
            source: &declarations[1],
        },
        TypeInput {
            name: "Missing".into(),
            is_data: false,
            has_native: false,
            has_collection: false,
            source: &declarations[2],
        },
        TypeInput {
            name: "Data".into(),
            is_data: true,
            has_native: false,
            has_collection: false,
            source: &declarations[3],
        },
    ];
    try_build_per_category_rules(
        &["B".into(), "A".into(), "A".into()],
        &user_inputs,
        &types,
        (),
        adapter,
    )
}

#[test]
fn fallible_synthesis_returns_same_owner_and_original_grouped_rows() {
    let (input, log, drops, live) = adapter(None);
    let address = (&*input.owner) as *const u8;
    let (output, rows) = fixture(input).expect("finite synthesis succeeds");
    assert_eq!((&*output.owner) as *const u8, address);
    assert_eq!(drops.get(), 0);
    assert!(
        rows[1].is_empty(),
        "last duplicate category wins without removing earlier bucket"
    );
    assert_eq!(rows[0][0].label, "uB");
    assert_eq!(rows[2][0].label, "uA");
    assert!(rows[0][0].normalized && rows[2][0].normalized);
    let calls: Vec<_> = log
        .borrow()
        .iter()
        .filter(|entry| entry.starts_with("call:"))
        .cloned()
        .collect();
    assert_eq!(
        &calls[..4],
        ["call:clone:uA", "call:clone:uB", "call:normalize:uB", "call:normalize:uA"]
    );
    assert!(!calls.iter().any(|entry| entry.contains("ignored")));
    assert!(
        !calls.iter().any(|entry| entry == "call:var:B"),
        "current-row true user suppresses Var"
    );
    assert!(output
        .recipes
        .iter()
        .any(|rule| rule.label == "ApplyMissing"));
    assert!(!output.recipes.iter().any(|rule| rule.label == "ApplyData"));
    drop(rows);
    assert_eq!(live.get(), 0);
    drop(output);
    assert_eq!(drops.get(), 1);
}

#[test]
fn fallible_synthesis_every_denial_or_callback_error_stops_exact_prefix_and_drops_owner() {
    let (input, complete_log, _, _) = adapter(None);
    let complete = fixture(input).expect("reference run succeeds");
    let expected = complete_log.borrow().clone();
    drop(complete);
    for position in 0..expected.len() {
        let (input, log, drops, live) = adapter(Some(position));
        let error = match fixture(input) {
            Ok(_) => panic!("event {position} must fail"),
            Err(error) => error,
        };
        if expected[position].starts_with("admit:") {
            assert_eq!(error, SynthesisError::Admission(position));
        } else {
            assert_eq!(error, SynthesisError::Callback(position));
        }
        assert_eq!(*log.borrow(), expected[..=position], "first failure at {position}");
        assert_eq!(drops.get(), 1, "no owner escapes error {position}");
        assert_eq!(live.get(), 0, "no partial payload escapes error {position}");
    }
}

#[test]
fn fallible_synthesis_keeps_pair_prelude_before_apply_and_all_pairs_before_lambda() {
    let (input, log, _, _) = adapter(None);
    let _completed = fixture(input).expect("reference binder run succeeds");
    let log = log.borrow();
    let position = |wanted: &str| {
        log.iter()
            .position(|entry| entry == wanted)
            .expect("expected original site is reached")
    };
    assert!(position("admit:format:MApply|A|") < position("call:emit:A:ApplyA"));
    assert!(position("call:emit:A:ApplyA") < position("admit:vector-kind"));
    assert!(position("admit:vector-kind") < position("call:emit:A:MApplyA"));
    let first_lam = log
        .iter()
        .position(|entry| entry.starts_with("call:emit:") && entry.contains(":Lam"))
        .expect("lambda pass runs");
    let last_application = log
        .iter()
        .rposition(|entry| entry.starts_with("call:emit:") && entry.contains(":MApply"))
        .expect("pair pass runs");
    assert!(last_application < first_lam);
}

#[test]
fn fallible_synthesis_collection_split_is_once_and_moved_metadata_is_not_copied_again() {
    let (input, log, _, _) = adapter(None);
    let (output, _) = fixture(input).expect("collection run succeeds");
    let rule = output
        .recipes
        .iter()
        .find(|rule| rule.label == "BagLit")
        .expect("collection recipe retained");
    let syntax = rule.syntax_pattern.as_ref().expect("collection has syntax");
    assert_eq!(syntax.len(), 4);
    assert!(matches!(&syntax[0], InfixSyntaxShape::Literal(text) if text == "Bag"));
    assert!(matches!(&syntax[1], InfixSyntaxShape::Literal(text) if text == "("));
    assert!(
        matches!(&syntax[2], InfixSyntaxShape::Sep { collection, separator } if collection == "elems" && separator == ";")
    );
    assert!(matches!(&syntax[3], InfixSyntaxShape::Literal(text) if text == "]"));
    let log = log.borrow();
    assert!(log.iter().any(|entry| entry == "admit:trim:Bag((("));
    for moved in ["admit:copy:;", "admit:copy:]", "admit:copy:BagLit"] {
        assert!(!log.iter().any(|entry| entry == moved), "owned metadata moves: {moved}");
    }
}

#[test]
fn fallible_synthesis_unused_literal_probe_can_fail_before_no_native_skip() {
    let (mut input, log, drops, _) = adapter(Some(5));
    input.binders = false;
    let declaration = Declaration("A");
    let types = [TypeInput {
        name: "A".into(),
        is_data: false,
        has_native: false,
        has_collection: false,
        source: &declaration,
    }];
    // Determine the exact probe callback from a successful run, so the oracle
    // remains callback order rather than an incidental admission-event count.
    let (mut reference, reference_log, _, _) = adapter(None);
    reference.binders = false;
    let _ = try_build_per_category_rules(&["A".into()], &[], &types, (), reference)
        .expect("no-native reference succeeds");
    let probe = reference_log
        .borrow()
        .iter()
        .position(|entry| entry == "call:probe:A")
        .expect("unused original probe runs");
    input.fail = Some(probe);
    assert!(
        matches!(try_build_per_category_rules(&["A".into()], &[], &types, (), input), Err(SynthesisError::Callback(index)) if index == probe)
    );
    assert_eq!(log.borrow().last().map(String::as_str), Some("call:probe:A"));
    assert_eq!(drops.get(), 1);
}

#[test]
fn fallible_synthesis_impossible_vector_reservation_is_typed_and_preserves_buffer() {
    let mut values = vec![7u8];
    assert_eq!(reserve::<u8, ()>(&mut values, usize::MAX), Err(SynthesisError::Allocation));
    assert_eq!(values, [7]);
}
