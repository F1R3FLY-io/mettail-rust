use super::PROFILE_ROWS;
use crate::gen::term_ops::collection_walk::{field_carrier, FieldCarrier};
use crate::gen::term_ops::iterative_cmp::census_tests::actual_rholang;
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_ast::types::CollectionType;
use std::collections::{BTreeMap, BTreeSet};

type Profile = BTreeMap<(&'static str, &'static str), Vec<&'static str>>;

fn profile() -> Profile {
    let mut result = BTreeMap::new();
    for line in PROFILE_ROWS.lines().filter(|line| !line.trim().is_empty()) {
        let mut columns = line.split_whitespace();
        let category = columns.next().expect("profile category");
        let constructors = columns.next().expect("profile constructors");
        let fields: Vec<_> = columns.collect();
        for constructor in constructors.split('|') {
            assert!(
                result
                    .insert((category, constructor), fields.clone())
                    .is_none(),
                "duplicate explicit profile row {category}::{constructor}"
            );
        }
    }
    result
}

// Namespace normalization checks the carrier, not arbitrary Rust alias equality.
fn shape(ty: &syn::Type) -> String {
    let syn::Type::Path(path) = ty else {
        panic!("named carrier required")
    };
    assert!(path.qself.is_none());
    let segment = path.path.segments.last().expect("carrier name");
    match &segment.arguments {
        syn::PathArguments::None => segment.ident.to_string(),
        syn::PathArguments::AngleBracketed(arguments) => {
            let arguments = arguments
                .args
                .iter()
                .map(|arg| match arg {
                    syn::GenericArgument::Type(ty) => shape(ty),
                    _ => panic!("type-only carrier arguments required"),
                })
                .collect::<Vec<_>>()
                .join(",");
            format!("{}<{arguments}>", segment.ident)
        },
        syn::PathArguments::Parenthesized(_) => panic!("function carrier outside profile"),
    }
}

fn collection_shape(kind: CollectionType, category: &str) -> String {
    match kind {
        CollectionType::Vec => format!("Vec<{category}>"),
        CollectionType::HashBag => format!("HashBag<{category}>"),
        CollectionType::HashMap => format!("HashMapLit<{category},{category}>"),
        _ => panic!("unsupported collection in admitted row"),
    }
}

fn classified_field(field: &FieldInfo) -> (String, bool) {
    match field_carrier(field) {
        FieldCarrier::Leaf => {
            assert!(!field.is_optional && !field.is_predicate);
            let ty = syn::parse2(field.opaque_leaf_type()).expect("opaque field Rust type");
            (shape(&ty), false)
        },
        FieldCarrier::Child => (format!("Arc<{}>", field.category), true),
        FieldCarrier::Collection { coll_type } => {
            (collection_shape(coll_type, &field.category.to_string()), true)
        },
        FieldCarrier::OptionalChild | FieldCarrier::OptionalCollection { .. } => {
            panic!("new optional profile field requires explicit policy review")
        },
    }
}

fn classified_fields(kind: &VariantKind, enum_fields: &[String]) -> Vec<(String, bool)> {
    match kind {
        VariantKind::Var { .. } => vec![("OrdVar".into(), false)],
        VariantKind::Literal { .. } => {
            assert_eq!(enum_fields.len(), 1);
            vec![(enum_fields[0].clone(), false)]
        },
        VariantKind::Nullary { .. } => vec![],
        VariantKind::Regular { fields, .. } => fields.iter().map(classified_field).collect(),
        VariantKind::Collection { coll_type, element_cat, .. }
        | VariantKind::CollectionLiteral { coll_type, element_cat, .. } => {
            vec![(collection_shape(coll_type.clone(), &element_cat.to_string()), true)]
        },
        VariantKind::MultiBinder {
            pre_scope_fields, binder_cat, body_cat, ..
        } => {
            assert_eq!(binder_cat, "Name", "only original new scopes in this profile");
            let mut fields: Vec<_> = pre_scope_fields.iter().map(classified_field).collect();
            fields.push((format!("Scope<Vec<Binder<String>>,Arc<{body_cat}>>"), true));
            fields
        },
        VariantKind::Binder { .. }
        | VariantKind::RecursiveNativeLiteral { .. }
        | VariantKind::Refused { .. } => panic!("non-admitted classifier recipe"),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Role {
    Term,
    Name,
    Pattern,
    NamePattern,
    Guard,
    Declaration,
}

fn child_role(annotation: &str, incoming: Role) -> Role {
    match annotation {
        "T" => Role::Term,
        "N" => Role::Name,
        "P" => Role::Pattern,
        "PN" => Role::NamePattern,
        "G" => Role::Guard,
        "D" => Role::Declaration,
        "I" => incoming,
        "Q" => {
            if incoming == Role::NamePattern {
                Role::Pattern
            } else {
                Role::Term
            }
        },
        "B" => {
            if incoming == Role::Guard {
                Role::Guard
            } else {
                Role::Term
            }
        },
        _ => panic!("unknown source role {annotation}"),
    }
}

#[test]
fn actual_rholang_source_profile_covers_exact_constructors_and_original_slots() {
    let language = actual_rholang();
    let table = profile();
    assert_eq!(table.len(), 144, "approved constructor inventory changed");
    assert_eq!(
        table.values().map(Vec::len).sum::<usize>(),
        231,
        "approved original field-slot inventory changed"
    );
    let declarations =
        syn::parse2::<syn::File>(crate::gen::types::enums::generate_ast_enums(&language))
            .expect("actual enum declarations; no full-language compilation");
    let enums: BTreeMap<_, _> = declarations
        .items
        .into_iter()
        .filter_map(|item| match item {
            syn::Item::Enum(item) => Some((item.ident.to_string(), item)),
            _ => None,
        })
        .collect();
    let mut visited = BTreeSet::new();
    let mut constructors = 0;
    for category in &language.types {
        let name = category.name.to_string();
        let declaration = enums.get(&name).expect("actual category enum");
        let variants = collect_category_variants(&category.name, &language);
        assert_eq!(variants.len(), declaration.variants.len(), "{name} exhaustive classifier");
        let actual: BTreeMap<_, _> = declaration
            .variants
            .iter()
            .map(|variant| (variant.ident.to_string(), variant))
            .collect();
        assert_eq!(actual.len(), variants.len());
        let mut classified_labels = BTreeSet::new();
        for kind in variants {
            constructors += 1;
            let label = kind.label().to_string();
            assert!(
                classified_labels.insert(label.clone()),
                "{name} classifier must not substitute a duplicate for another constructor"
            );
            let variant = actual
                .get(&label)
                .expect("classifier maps actual enum variant");
            let Some(expected) = table.get(&(name.as_str(), label.as_str())) else {
                // Closed policy: every other actual enum is refused before fields.
                continue;
            };
            assert!(visited.insert((name.clone(), label.clone())));
            let fields: Vec<_> = variant
                .fields
                .iter()
                .map(|field| shape(&field.ty))
                .collect();
            let classified = classified_fields(&kind, &fields);
            assert_eq!(
                fields,
                classified
                    .iter()
                    .map(|(shape, _)| shape.clone())
                    .collect::<Vec<_>>(),
                "{name}::{label}: classifier preserves actual carrier and original slot order"
            );
            let expected_shapes: Vec<_> = expected
                .iter()
                .map(|slot| slot.split('@').next().expect("slot type"))
                .collect();
            assert_eq!(
                fields, expected_shapes,
                "{name}::{label}: explicit approved profile must match every actual field"
            );
            for ((_, child), slot) in classified.iter().zip(expected) {
                assert_eq!(
                    *child,
                    slot.contains('@'),
                    "{name}::{label}: every child has a role, opaque data has none"
                );
                if let Some((_, role)) = slot.split_once('@') {
                    for incoming in [
                        Role::Term,
                        Role::Name,
                        Role::Pattern,
                        Role::NamePattern,
                        Role::Guard,
                        Role::Declaration,
                    ] {
                        child_role(role, incoming);
                    }
                }
            }
        }
    }
    assert_eq!(constructors, 1990, "actual generated constructor snapshot changed");
    assert_eq!(visited.len(), table.len(), "no invented or stale approved constructor");
    for category in [
        "DdlModuleItem",
        "DdlParam",
        "DdlPath",
        "DdlImports",
        "DdlImport",
        "DdlTheoryExpr",
        "DdlCatDecl",
        "DdlExport",
        "DdlReplacement",
        "DdlTermRule",
        "DdlBinding",
        "DdlSort",
        "DdlSyntaxItem",
        "DdlEquation",
        "DdlFreshnesses",
        "DdlFreshness",
        "DdlRewrite",
        "DdlPremises",
        "DdlPremise",
        "DdlRuleAst",
        "DdlRuleAstItems",
        "DdlRuleAstRemainderTail",
    ] {
        for variant in &enums[category].variants {
            assert!(
                table.contains_key(&(category, variant.ident.to_string().as_str())),
                "complete declaration closure: {category}::{}",
                variant.ident
            );
        }
    }
}

#[test]
fn source_profile_context_crossings_and_refusals_are_explicit() {
    let table = profile();
    for (category, label) in [
        ("Proc", "CastBag"),
        ("Bag", "BagLit"),
        ("Proc", "CastSet"),
        ("Set", "SetLit"),
        ("Proc", "CastPathmap"),
        ("Proc", "PLookahead"),
        ("Int", "BoolToInt"),
        ("Int", "IVar"),
        ("InputBind", "InputBindQuery"),
        ("InputBind", "InputBindEmptyQuery"),
        ("InputBind", "InputBindQuotedQuery"),
        ("ForRow", "FVar"),
        ("Map", "MVar"),
        ("Proc", "LamProc"),
        ("Proc", "Add"),
        ("Proc", "PPersistOutputQuoted"),
        ("Map", "MapEmpty"),
    ] {
        assert!(!table.contains_key(&(category, label)), "refuse {category}::{label}");
    }
    assert_eq!(table[&("DdlSort", "DdlSortSet")], ["String"]);
    assert_eq!(table[&("Proc", "MapEmpty")], Vec::<&str>::new());
    for incoming in [Role::Term, Role::Pattern, Role::Guard] {
        // One collection slot denotes both original Map sides, key then value.
        for field in ["HashMapLit<Proc,Proc>@I", "Vec<Proc>@I"] {
            let (_, annotation) = field.split_once('@').expect("collection role");
            assert_eq!(child_role(annotation, incoming), incoming);
        }
        for label in ["PFlt", "PFltFence", "PFltBrace"] {
            assert_eq!(table[&("Proc", label)], ["Arc<FltNode>"]);
        }
    }
    assert_eq!(table[&("Map", "MapLit")], ["HashMapLit<Proc,Proc>@I"]);
    assert_eq!(table[&("Name", "NParen")], ["Arc<Name>@I"]);
    assert_eq!(child_role("I", Role::NamePattern), Role::NamePattern);
    assert_eq!(child_role("Q", Role::NamePattern), Role::Pattern);
    assert_eq!(child_role("Q", Role::Name), Role::Term);
    assert_eq!(child_role("B", Role::Guard), Role::Guard);
    assert_eq!(child_role("B", Role::Pattern), Role::Term);
    assert_eq!(
        table[&("DdlTheoryExpr", "DdlTheoryData")],
        ["Arc<DdlTheoryExpr>@D", "Arc<Proc>@T"]
    );
    assert_eq!(table[&("DdlTheoryExpr", "DdlTheoryDataImplicit")], ["Arc<Proc>@T"]);
    assert_eq!(table[&("DdlModuleItem", "DdlModuleProcItem")], ["Arc<Proc>@T"]);
    assert_eq!(table[&("Proc", "MethodCall")], ["Arc<Proc>@T", "String", "Vec<Proc>@T"]);
}
