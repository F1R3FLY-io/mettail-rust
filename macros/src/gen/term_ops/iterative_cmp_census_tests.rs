//! Actual Rholang comparison census; no generated-language compilation.
//! This pins source correspondence only, not comparator factorization.
use super::*;
use crate::gen::term_ops::subst::OpaqueLeafKind;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

fn compact(tokens: TokenStream) -> String {
    tokens.to_string().split_whitespace().collect()
}

fn actual_rholang() -> LanguageDef {
    let source = syn::parse_file(include_str!("../../../../languages/src/rholang.rs"))
        .expect("actual Rholang source must parse as Rust items");
    let mut inputs = source.items.into_iter().filter_map(|item| match item {
        syn::Item::Macro(item)
            if item
                .mac
                .path
                .segments
                .last()
                .is_some_and(|part| part.ident == "language") =>
        {
            Some(item.mac.tokens)
        },
        _ => None,
    });
    let input = inputs.next().expect("actual Rholang language macro");
    assert!(inputs.next().is_none(), "one Rholang language definition");
    let mut language: LanguageDef =
        syn::parse2(input).expect("actual Rholang LanguageDef must parse");
    assert!(
        language.extends_names.is_empty()
            && language.include_names.is_empty()
            && language.mixin_names.is_empty(),
        "this bounded standalone Rholang census must not silently skip composition"
    );
    // Same preparation as expand_language, before enum/comparison generation.
    let injections =
        crate::gen::runtime::wpda_codegen::auto_inject::emit_auto_injection_rules(&language);
    language.terms.extend(injections.terms);
    language.rewrites.extend(injections.rewrites);
    language
}

// Qualified source types remain in the capture. This compares carrier shape
// only, not arbitrary aliases or namespace semantics.
fn shape(ty: &syn::Type) -> String {
    let syn::Type::Path(path) = ty else {
        panic!("comparison carrier must be a named Rust type: {}", quote! { #ty });
    };
    assert!(path.qself.is_none(), "no qualified associated carrier");
    let segment = path.path.segments.last().expect("carrier path segment");
    match &segment.arguments {
        syn::PathArguments::None => segment.ident.to_string(),
        syn::PathArguments::AngleBracketed(arguments) => {
            let types = arguments
                .args
                .iter()
                .map(|argument| match argument {
                    syn::GenericArgument::Type(ty) => shape(ty),
                    _ => panic!("unexpected non-type comparison carrier parameter"),
                })
                .collect::<Vec<_>>();
            format!("{}<{}>", segment.ident, types.join(","))
        },
        _ => panic!("unexpected function-style comparison carrier"),
    }
}

fn pattern_label(pattern: &syn::Pat) -> String {
    let path = match pattern {
        syn::Pat::Path(pattern) => &pattern.path,
        syn::Pat::TupleStruct(pattern) => &pattern.path,
        _ => panic!("comparison index must match an explicit constructor"),
    };
    path.segments
        .last()
        .expect("constructor path segment")
        .ident
        .to_string()
}

fn actual_indices(category: &Ident, language: &LanguageDef) -> BTreeMap<String, usize> {
    let function = syn::parse2::<syn::ItemFn>(generate_variant_index_fn(category, language))
        .expect("actual comparison index function");
    let [syn::Stmt::Expr(syn::Expr::Match(matched), None)] = function.block.stmts.as_slice() else {
        panic!("comparison index must be one exhaustive match");
    };
    let mut indices = BTreeMap::new();
    for arm in &matched.arms {
        assert!(arm.guard.is_none(), "comparison index arm has no guard");
        let syn::Expr::Lit(syn::ExprLit { lit: syn::Lit::Int(index), .. }) = &*arm.body else {
            panic!("comparison index must be an integer constant");
        };
        assert!(
            indices
                .insert(
                    pattern_label(&arm.pat),
                    index.base10_parse().expect("comparison index fits usize")
                )
                .is_none(),
            "duplicate constructor index arm"
        );
    }
    indices
}

fn field_recipe(field: &FieldInfo) -> String {
    format!(
        "{:?}:{}:optional={}:predicate={}:opaque={:?}",
        field_carrier(field),
        field.category,
        field.is_optional,
        field.is_predicate,
        field.opaque_leaf
    )
}

fn check_supported_field(field: &FieldInfo, actual: &syn::Type) {
    let category = &field.category;
    let base = match field_carrier(field) {
        FieldCarrier::Leaf => match field.opaque_leaf {
            Some(OpaqueLeafKind::TokenText) => "String".to_owned(),
            Some(OpaqueLeafKind::GuestBody) => "Arc<FltNode>".to_owned(),
            None => panic!("supported opaque comparison field lacks a closed leaf kind"),
        },
        FieldCarrier::Child | FieldCarrier::OptionalChild => format!("Arc<{category}>"),
        FieldCarrier::Collection { coll_type } | FieldCarrier::OptionalCollection { coll_type } => {
            match coll_type {
                CollectionType::Vec => format!("Vec<{category}>"),
                CollectionType::HashMap => format!("HashMapLit<{category},{category}>"),
                _ => panic!("unsupported collection entered the checked comparison field census"),
            }
        },
    };
    let expected = if field.is_optional {
        format!("Option<{base}>")
    } else {
        base
    };
    assert_eq!(shape(actual), expected, "field carrier {:?}", field);
}

fn inspect_variant(
    language: &LanguageDef,
    category: &Ident,
    index: usize,
    kind: &VariantKind,
    declaration: &syn::Variant,
    capture: &mut String,
) -> bool {
    let supported = checked_cmp_variant_supported(category, kind, language);
    let label = kind.label();
    let fields = declaration
        .fields
        .iter()
        .map(|field| &field.ty)
        .collect::<Vec<_>>();
    let mut recipes = Vec::<String>::new();
    let mut ordinary_fields: &[FieldInfo] = &[];
    let description = match kind {
        VariantKind::Refused { .. } => {
            panic!("actual Rholang contains a compile-time refused shape")
        },
        VariantKind::Nullary { .. } => {
            assert!(fields.is_empty(), "{category}::{label} must be nullary");
            "nullary".to_owned()
        },
        VariantKind::Literal { .. } => {
            assert_eq!(fields.len(), 1, "{category}::{label} literal width");
            if supported {
                let native = language
                    .get_type(category)
                    .and_then(|ty| ty.native_type.as_ref())
                    .expect("supported literal has declared native type");
                let expected = match mettail_ast::language::NativeKind::from_syn_type(native) {
                    mettail_ast::language::NativeKind::Int64 => "i64",
                    mettail_ast::language::NativeKind::Bool => "bool",
                    mettail_ast::language::NativeKind::Str => "String",
                    _ => panic!("unsupported native literal entered checked comparison census"),
                };
                assert_eq!(shape(fields[0]), expected, "{category}::{label}");
            }
            recipes.push("native-original-cmp".to_owned());
            "literal".to_owned()
        },
        VariantKind::Var { .. } => {
            assert_eq!(fields.len(), 1, "{category}::{label} variable width");
            assert_eq!(shape(fields[0]), "OrdVar", "{category}::{label}");
            recipes.push("ordvar-original-cmp".to_owned());
            "variable".to_owned()
        },
        VariantKind::Regular { fields: described, .. } => {
            assert_eq!(fields.len(), described.len(), "{category}::{label} field census");
            ordinary_fields = described;
            "regular".to_owned()
        },
        VariantKind::Binder {
            pre_scope_fields, binder_cat, body_cat, ..
        }
        | VariantKind::MultiBinder {
            pre_scope_fields, binder_cat, body_cat, ..
        } => {
            assert_eq!(
                fields.len(),
                pre_scope_fields.len() + 1,
                "{category}::{label} scope must be last"
            );
            ordinary_fields = pre_scope_fields;
            let multi = matches!(kind, VariantKind::MultiBinder { .. });
            let pattern = if multi {
                "Vec<Binder<String>>"
            } else {
                "Binder<String>"
            };
            assert_eq!(
                shape(fields[pre_scope_fields.len()]),
                format!("Scope<{pattern},Arc<{body_cat}>>"),
                "{category}::{label}"
            );
            format!(
                "scope:{}:binder={binder_cat}:body={body_cat}",
                if multi {
                    "multi-length-then-digests"
                } else {
                    "single-digest"
                }
            )
        },
        VariantKind::Collection { element_cat, coll_type, .. }
        | VariantKind::CollectionLiteral { element_cat, coll_type, .. } => {
            assert_eq!(fields.len(), 1, "{category}::{label} collection width");
            if supported {
                let expected = match coll_type {
                    CollectionType::Vec => format!("Vec<{element_cat}>"),
                    CollectionType::HashMap => format!("HashMapLit<{element_cat},{element_cat}>"),
                    _ => panic!("unsupported whole collection entered checked comparison census"),
                };
                assert_eq!(shape(fields[0]), expected, "{category}::{label}");
            }
            recipes.push(format!("collection:{coll_type:?}:element={element_cat}"));
            if matches!(kind, VariantKind::CollectionLiteral { .. }) {
                "collection-literal".to_owned()
            } else {
                "collection-field".to_owned()
            }
        },
        VariantKind::RecursiveNativeLiteral { .. } => {
            assert_eq!(fields.len(), 1, "{category}::{label} recursive native width");
            assert!(!supported, "recursive native must stay refused in the checked Map profile");
            recipes.push("recursive-native-refused".to_owned());
            "recursive-native".to_owned()
        },
    };
    for (position, field) in ordinary_fields.iter().enumerate() {
        if supported {
            check_supported_field(field, fields[position]);
        }
        recipes.push(field_recipe(field));
    }
    if matches!(kind, VariantKind::Binder { .. } | VariantKind::MultiBinder { .. }) {
        recipes.push(description.clone());
    }
    assert_eq!(
        recipes.len(),
        fields.len(),
        "{category}::{label} every positional field recorded"
    );
    writeln!(
        capture,
        "C\t{category}\t{index}\t{label}\t{}\t{description}",
        if supported {
            "supported-shallow"
        } else {
            "refused"
        }
    )
    .expect("append census row");
    for (position, (ty, recipe)) in fields.iter().zip(&recipes).enumerate() {
        writeln!(
            capture,
            "F\t{category}\t{index}\t{position}\t{recipe}\t{}",
            compact(quote! { #ty })
        )
        .expect("append positional carrier row");
    }
    if !supported {
        let refusal = compact(generate_cmp_variant_arm(
            category,
            kind,
            language,
            &CmpEmissionNames::checked(),
        ));
        assert!(
            refusal.contains("NativeComparisonFailure::UnsupportedConstructor"),
            "{category}::{label} must have a whole-arm named refusal"
        );
        assert!(
            refusal.contains(&format!("constructor:\"{label}\"")),
            "{category}::{label} refusal must retain its actual constructor name"
        );
    }
    supported
}

#[test]
fn actual_rholang_comparison_census_matches_enum_indices_and_carriers() {
    let language = actual_rholang();
    let categories = language
        .types
        .iter()
        .map(|ty| ty.name.to_string())
        .collect::<BTreeSet<_>>();
    assert_eq!(categories.len(), language.types.len(), "unique actual Rholang categories");
    let declarations =
        syn::parse2::<syn::File>(crate::gen::types::enums::generate_ast_enums(&language))
            .expect("actual Rholang enum declarations parse without compiling a language");
    let mut enums = BTreeMap::new();
    for item in declarations.items {
        if let syn::Item::Enum(item) = item {
            if categories.contains(&item.ident.to_string()) {
                assert!(
                    enums.insert(item.ident.to_string(), item).is_none(),
                    "one declaration per actual category"
                );
            }
        }
    }
    assert_eq!(enums.len(), categories.len(), "complete actual category census");
    let mut capture = String::from(
        "# Rholang comparison census; shallow support is not full-source admission\n\
         # C category comparison-index constructor supported/refused recipe\n\
         # F category comparison-index field-position carrier-recipe exact-Rust-type\n",
    );
    let mut rows = BTreeMap::new();
    let mut single_scopes = 0;
    let mut multi_scopes = 0;
    let mut maps = 0;
    let mut refused = 0;
    for language_type in &language.types {
        let category = &language_type.name;
        let declaration = enums
            .get(&category.to_string())
            .expect("actual category enum");
        let mut constructors = BTreeMap::new();
        for variant in &declaration.variants {
            assert!(
                constructors
                    .insert(variant.ident.to_string(), variant)
                    .is_none(),
                "{category} has unique constructor labels"
            );
        }
        let variants = collect_category_variants(category, &language);
        let indices = actual_indices(category, &language);
        assert_eq!(constructors.len(), variants.len(), "{category} classifier covers actual enum");
        assert_eq!(indices.len(), variants.len(), "{category} classifier covers actual indices");
        for (index, kind) in variants.iter().enumerate() {
            let label = kind.label().to_string();
            let declaration = constructors
                .get(&label)
                .unwrap_or_else(|| panic!("{category}::{label} classifier lacks enum constructor"));
            assert_eq!(
                indices.get(&label),
                Some(&index),
                "{category}::{label} explicit comparison ordinal, not enum discriminant"
            );
            let supported =
                inspect_variant(&language, category, index, kind, declaration, &mut capture);
            assert!(
                rows.insert((category.to_string(), label), supported)
                    .is_none(),
                "one census row per actual constructor"
            );
            if supported {
                match kind {
                    VariantKind::Binder { .. } => single_scopes += 1,
                    VariantKind::MultiBinder { .. } => multi_scopes += 1,
                    VariantKind::Collection { coll_type: CollectionType::HashMap, .. }
                    | VariantKind::CollectionLiteral {
                        coll_type: CollectionType::HashMap, ..
                    } => maps += 1,
                    _ => {},
                }
            } else {
                refused += 1;
            }
        }
    }
    for (category, constructor, expected) in [
        ("Proc", "PNew", true),
        ("Proc", "PNewUris", true),
        ("Map", "MapLit", true),
        ("Proc", "PPar", false),
        ("Bag", "BagLit", false),
        ("Set", "SetLit", false),
        ("Pathmap", "PathmapLit", false),
    ] {
        assert_eq!(
            rows.get(&(category.to_owned(), constructor.to_owned())),
            Some(&expected),
            "required checked Map comparison boundary {category}::{constructor}"
        );
    }
    assert!(
        maps > 0 && refused > 0,
        "actual census must retain Map and explicitly refused alternatives"
    );
    writeln!(capture,
        "# counts: single-scopes={single_scopes} multi-scopes={multi_scopes} maps={maps} refused={refused}")
        .expect("append diagnostic census counts");
    // Ordinary tests write nothing. No arbitrary output path or full grammar
    // compilation; scope counts are diagnostics, not extra demo requirements.
    if let Ok(enabled) = std::env::var("METTAIL_CMP_CENSUS_CAPTURE") {
        assert_eq!(enabled, "1", "comparison census capture is opt-in only");
        let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../target/verification/cmp-emitter");
        std::fs::create_dir_all(&directory).expect("create comparison census directory");
        std::fs::write(directory.join("rholang-census.tsv"), capture)
            .expect("write actual Rholang comparison census");
    }
}
