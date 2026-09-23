//! Acceptance through the existing canonical decoder and schema lowerer.
use super::{core, RhoValue};
use crate::canonical::{value_to_core, value_to_language_core};
use crate::core_value::{language_core_to_value, LANGUAGE_CORE_VALUE_SCHEMA_CURRENT};
use std::collections::BTreeMap;

fn s(value: &str) -> RhoValue {
    RhoValue::String(value.into())
}
fn l(values: impl IntoIterator<Item = RhoValue>) -> RhoValue {
    RhoValue::List(values.into_iter().collect())
}
fn m(values: impl IntoIterator<Item = (&'static str, RhoValue)>) -> RhoValue {
    RhoValue::Map(
        values
            .into_iter()
            .map(|(key, value)| (key.into(), value))
            .collect(),
    )
}
fn language(fields: impl IntoIterator<Item = (&'static str, RhoValue)>) -> RhoValue {
    let mut values = BTreeMap::from([
        ("mettail".into(), s("language/2")),
        ("name".into(), s("RetainedDeclarations")),
    ]);
    values.extend(fields.into_iter().map(|(key, value)| (key.into(), value)));
    RhoValue::Map(values)
}
fn native_type(name: &str, carrier: &str) -> RhoValue {
    m([("name", s(name)), ("carrier", s(carrier))])
}
fn literal(category: &str) -> RhoValue {
    m([
        ("category", s(category)),
        ("pattern", s("[0-9]+")),
        ("eval", l([s("handler"), s("mtl:test:retained-literal")])),
    ])
}
fn store(grammar: &core::GrammarCoreV1) -> &core::AuthoredRuleStore {
    grammar
        .authored
        .as_ref()
        .expect("schema lowering retains an arena owner")
}
fn header(grammar: &core::GrammarCoreV1) -> &core::AuthoredDeclarations {
    store(grammar)
        .declarations()
        .expect("schema lowering retains source declarations")
}
fn bindings(grammar: &core::GrammarCoreV1) -> &core::AuthoredDeclarationBindings {
    grammar
        .authored_bindings
        .as_ref()
        .expect("source declarations have complete final-ID bindings")
}
fn name(grammar: &core::GrammarCoreV1, id: core::AuthoredNameId) -> &core::AuthoredName {
    match store(grammar).get(id.0) {
        Some(core::AuthoredNode::Name(name)) => name,
        other => panic!("retained declaration name must reference a Name node, got {other:?}"),
    }
}

#[test]
fn authored_declarations_preserve_scalar_widths_absence_and_opaque_carriers() {
    use core::NativeKind as K;
    let scalars = [
        ("i8", K::Int8),
        ("i16", K::Int16),
        ("i32", K::Int32),
        ("i64", K::Int64),
        ("i128", K::Int128),
        ("isize", K::Isize),
        ("u8", K::UInt8),
        ("u16", K::UInt16),
        ("u32", K::UInt32),
        ("u64", K::UInt64),
        ("u128", K::UInt128),
        ("usize", K::Usize),
        ("f32", K::Float32),
        ("f64", K::Float64),
        ("bool", K::Bool),
        ("str", K::Str),
        ("String", K::Str),
        ("BigInt", K::CanonicalBigInt),
        ("BigRat", K::CanonicalBigRat),
        ("Fixed", K::CanonicalFixedPoint),
    ];
    let mut types = vec![s("Expr")];
    types.extend(
        scalars
            .iter()
            .enumerate()
            .map(|(index, (symbol, _))| native_type(&format!("Scalar{index}"), symbol)),
    );
    types.push(m([("name", s("Opaque")), ("carrier", l([s("extern"), s("urn:test:opaque")]))]));
    types.push(m([
        ("name", s("Exprs")),
        ("carrier", l([s("vec"), s("Expr")])),
        ("collection", m([("kind", s("list"))])),
    ]));
    let grammar = value_to_core(&language([("types", l(types))]))
        .expect("all accepted scalar and opaque declarations lower");
    assert_eq!(header(&grammar).categories[0].native, None);
    for (index, (_, expected)) in scalars.iter().enumerate() {
        assert_eq!(header(&grammar).categories[index + 1].native, Some(*expected));
        assert_eq!(bindings(&grammar).categories[index + 1], core::CategoryId((index + 1) as u32));
    }
    assert_eq!(header(&grammar).categories[21].native, Some(K::Other));
    assert_eq!(header(&grammar).categories[22].native, Some(K::Other));
    assert!(
        matches!(&grammar.categories[21].carrier, core::Carrier::Extern { urn } if urn == "urn:test:opaque")
    );
    assert!(
        matches!(&grammar.categories[22].carrier, core::Carrier::Collection(carrier) if carrier.key == "Expr" && carrier.value.is_none())
    );
    // Canonical aliases are adapter observations, not additions to the original classifier.
    assert_eq!(K::from_last_path_segment("BigRat"), K::Other);
    assert_eq!(K::from_last_path_segment("Fixed"), K::Other);
}

#[test]
fn authored_declarations_literals_use_original_name_selector_and_keep_source_category() {
    let rows = [
        ("Tiny", "i8", "Integer"),
        ("Wide", "i64", "Integer"),
        ("Real", "f64", "Float"),
        ("Truth", "bool", "Boolean"),
        ("Text", "String", "StringLit"),
        ("Huge", "BigInt", "Huge"),
        ("Rat", "BigRat", "Rat"),
        ("Money", "Fixed", "Money"),
    ];
    let grammar = value_to_core(&language([
        (
            "types",
            l(rows
                .iter()
                .map(|(category, carrier, _)| native_type(category, carrier))),
        ),
        ("literals", l(rows.iter().map(|(category, _, _)| literal(category)))),
    ]))
    .expect("literal source observations lower through the shared selector");
    for (index, (category, _, expected_name)) in rows.iter().enumerate() {
        let row = &header(&grammar).tokens[index];
        assert_eq!(name(&grammar, row.name).spelling, *expected_name);
        assert_eq!(
            name(&grammar, row.category.expect("literal retains its source category")).spelling,
            *category
        );
        assert!(row.from_literals && row.has_evaluation);
        assert_eq!(row.push, None);
        let binding = &bindings(&grammar).tokens[index];
        assert_eq!(binding.direct, core::TokenId(index as u32 + 1));
        assert_eq!(binding.typed_literal, None, "runtime does not invent macro auxiliary routes");
        assert_eq!(
            grammar.tokens[binding.direct.0 as usize].name,
            format!("literal/{category}/{index}")
        );
    }
    let first = name(&grammar, header(&grammar).tokens[0].name);
    let second = name(&grammar, header(&grammar).tokens[1].name);
    assert_eq!(
        first.equality_class, second.equality_class,
        "equal selector names share String equality, not occurrence identity"
    );
}

fn modal_value() -> RhoValue {
    language([
        ("types", l([s("Expr"), native_type("Number", "i16")])),
        (
            "tokens",
            l([
                m([
                    ("name", s("Word")),
                    ("pattern", s("[a-z]+")),
                    ("category", s("Expr")),
                    ("push", s("Quoted")),
                ]),
                m([("name", s("Bare")), ("pattern", s("!"))]),
            ]),
        ),
        ("literals", l([literal("Number")])),
        (
            "modes",
            l([
                m([
                    ("name", s("Quoted")),
                    ("raw", RhoValue::Boolean(true)),
                    (
                        "tokens",
                        l([
                            m([
                                ("name", s("End")),
                                ("pattern", s("q")),
                                ("pop", RhoValue::Boolean(true)),
                            ]),
                            m([("name", s("Nest")), ("pattern", s("n")), ("push", s("Raw"))]),
                        ]),
                    ),
                ]),
                m([
                    ("name", s("Raw")),
                    (
                        "tokens",
                        l([m([
                            ("name", s("End")),
                            ("pattern", s("r")),
                            ("pop", RhoValue::Boolean(true)),
                        ])]),
                    ),
                ]),
            ]),
        ),
    ])
}

#[test]
fn authored_declarations_bind_source_order_to_actual_execution_ids_and_modes() {
    let grammar = value_to_core(&modal_value()).expect("modal lexer declarations lower");
    let retained = header(&grammar);
    assert_eq!(retained.global_tokens, [0, 1, 2]);
    assert_eq!(retained.modes[0].tokens, [3, 4]);
    assert_eq!(retained.modes[1].tokens, [5]);
    let names: Vec<_> = retained
        .tokens
        .iter()
        .map(|row| name(&grammar, row.name).spelling.as_str())
        .collect();
    assert_eq!(names, ["Word", "Bare", "Integer", "End", "Nest", "End"]);
    let actual: Vec<_> = bindings(&grammar)
        .tokens
        .iter()
        .map(|row| row.direct.0)
        .collect();
    assert_eq!(
        actual,
        [2, 3, 1, 4, 5, 6],
        "Identifier precedes literals, then globals, then ordered mode tokens"
    );
    assert!(bindings(&grammar)
        .tokens
        .iter()
        .all(|row| row.typed_literal.is_none()));
    assert_eq!(bindings(&grammar).modes, [core::ModeId(1), core::ModeId(2)]);
    assert_eq!(
        name(&grammar, retained.tokens[0].push.expect("Word retains authored push")).spelling,
        "Quoted"
    );
    assert!(!retained.tokens[0].from_literals && !retained.tokens[0].has_evaluation);
    assert_eq!(retained.tokens[1].category, None);
    assert_eq!(retained.tokens[1].push, None);
    assert_eq!(grammar.tokens[2].transition.push, Some(core::ModeId(1)));
    assert_eq!(grammar.tokens[5].transition.push, Some(core::ModeId(2)));
    assert!(grammar.tokens[4].transition.pop && grammar.tokens[6].transition.pop);
    assert!(grammar.modes[1].raw && !grammar.modes[2].raw);
    assert_eq!(name(&grammar, retained.modes[0].name).spelling, "Quoted");
    assert_eq!(name(&grammar, retained.modes[1].name).spelling, "Raw");
    assert_eq!(
        name(&grammar, retained.tokens[3].name).equality_class,
        name(&grammar, retained.tokens[5].name).equality_class
    );
    assert_eq!(grammar.tokens[4].name, "Quoted/End");
    assert_eq!(grammar.tokens[6].name, "Raw/End");
    grammar
        .validate()
        .expect("actual execution bindings validate");
}

#[test]
fn authored_declarations_keep_independent_collection_delimiters() {
    let grammar = value_to_core(&language([(
        "types",
        l([
            s("Expr"),
            m([
                ("name", s("Mapping")),
                ("carrier", l([s("map"), s("Expr"), s("Expr")])),
                (
                    "collection",
                    m([
                        ("kind", s("map")),
                        ("open", s("{")),
                        ("sep", s(";")),
                        ("key_val_sep", s("")),
                    ]),
                ),
            ]),
        ]),
    )]))
    .expect("independent optional delimiter fields retain their decoded values");
    let collection = header(&grammar).categories[1]
        .collection
        .as_ref()
        .expect("declared collection metadata is retained");
    assert_eq!(collection.kind, core::CollectionKind::Map);
    assert_eq!(collection.open.as_deref(), Some("{"));
    assert_eq!(collection.close, None);
    assert_eq!(collection.separator.as_deref(), Some(";"));
    assert_eq!(collection.key_value_separator.as_deref(), Some(""));
    assert!(
        matches!(&grammar.categories[1].carrier, core::Carrier::Collection(carrier) if carrier.key == "Expr" && carrier.value.as_deref() == Some("Expr"))
    );
}

#[test]
fn authored_declarations_survive_zero_rule_and_zero_declaration_languages() {
    for types in [l([]), l([s("Expr")])] {
        let grammar =
            value_to_core(&language([("types", types)])).expect("empty rule roster still lowers");
        assert!(grammar.productions.is_empty());
        assert!(header(&grammar).tokens.is_empty() && header(&grammar).modes.is_empty());
        assert_eq!(header(&grammar).categories.len(), grammar.categories.len());
        assert_eq!(bindings(&grammar).categories.len(), grammar.categories.len());
        assert!(bindings(&grammar).tokens.is_empty() && bindings(&grammar).modes.is_empty());
        grammar
            .validate()
            .expect("zero-rule owner and complete empty bindings validate");
    }
}

fn map_mut(value: &mut RhoValue) -> &mut BTreeMap<String, RhoValue> {
    match value {
        RhoValue::Map(fields) => fields,
        other => panic!("structural fixture component must be a map, got {other:?}"),
    }
}

#[test]
fn authored_declarations_exact_value_roundtrip_requires_header_and_binding_fields() {
    let language = value_to_language_core(&modal_value()).expect("schema yields complete language");
    let value = language_core_to_value(&language).expect("retained language encodes structurally");
    let RhoValue::Map(envelope) = &value else {
        panic!("structural language envelope must be a map")
    };
    assert_eq!(envelope.get("core_schema"), Some(&s(LANGUAGE_CORE_VALUE_SCHEMA_CURRENT)));
    let decoded = value_to_language_core(&value).expect("current exact format decodes");
    assert_eq!(decoded, language);
    assert_eq!(
        decoded
            .grammar
            .fingerprint()
            .expect("decoded grammar hashes"),
        language
            .grammar
            .fingerprint()
            .expect("original grammar hashes")
    );
    for missing_header in [false, true] {
        let mut malformed = value.clone();
        let core = map_mut(
            map_mut(&mut malformed)
                .get_mut("core")
                .expect("envelope contains core"),
        );
        let grammar = map_mut(core.get_mut("grammar").expect("language contains grammar"));
        if missing_header {
            let arena = map_mut(
                grammar
                    .get_mut("authored")
                    .expect("grammar contains authored store"),
            );
            assert!(arena.remove("declarations").is_some());
        } else {
            assert!(grammar.remove("authored_bindings").is_some());
        }
        assert!(
            value_to_language_core(&malformed).is_err(),
            "missing retained field must not become absent metadata"
        );
    }
}

#[test]
fn authored_declarations_width_changes_identity_but_omitted_defaults_do_not() {
    let narrow = value_to_core(&language([("types", l([native_type("Number", "i8")]))]))
        .expect("i8 declaration lowers");
    let wide = value_to_core(&language([("types", l([native_type("Number", "i64")]))]))
        .expect("i64 declaration lowers");
    assert_eq!(
        narrow.categories, wide.categories,
        "existing Core carrier projection erases integer width"
    );
    assert_ne!(header(&narrow).categories[0].native, header(&wide).categories[0].native);
    assert_ne!(
        narrow.fingerprint().expect("narrow grammar hashes"),
        wide.fingerprint().expect("wide grammar hashes")
    );
    let shorthand = value_to_core(&language([("types", l([s("Expr")]))]))
        .expect("shorthand dynamic category lowers");
    let explicit = value_to_core(&language([(
        "types",
        l([m([("name", s("Expr")), ("admits_variables", RhoValue::Boolean(true))])]),
    )]))
    .expect("explicit default dynamic category lowers");
    assert_eq!(shorthand, explicit);
    assert_eq!(
        shorthand.fingerprint().expect("shorthand hashes"),
        explicit.fingerprint().expect("explicit defaults hash")
    );
}
