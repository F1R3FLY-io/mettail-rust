//! Const receipt projection of the existing Drop emitter's selected recipes.
//!
//! No constructor is selected here. The caller supplies its exact DummyPlan;
//! only already-selected, earlier dependencies may contribute child receipts.

use super::collection_walk::{plan_for, CollectionPlan, OrderSensitivity};
use super::iterative_drop::DummyPlan;
use super::subst::{FieldInfo, OpaqueLeafKind, VariantKind};
use crate::gen::native_carrier::NativeCarrierStorage;
use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::BTreeMap;
use syn::Ident;

// The checked binding entry is not yet emitted. Keep this scoped to its
// complete projection API rather than suppressing unrelated dead code.
#[allow(dead_code)]
pub(super) struct DummyReceiptEmission {
    pub(super) tokens: TokenStream,
    pub(super) indices: BTreeMap<String, usize>,
}

#[allow(dead_code)]
pub(super) fn generate_dummy_receipts(
    language: &LanguageDef,
    plan: &DummyPlan,
) -> Result<DummyReceiptEmission, syn::Error> {
    emit_table(plan, |category, variant| project_variant(language, category, variant))
}

fn emit_table(
    plan: &DummyPlan,
    mut project: impl FnMut(&Ident, &VariantKind) -> Result<(TokenStream, Vec<Ident>), syn::Error>,
) -> Result<DummyReceiptEmission, syn::Error> {
    let indices: BTreeMap<String, usize> = plan
        .dependency_order
        .iter()
        .enumerate()
        .map(|(index, category)| (category.to_string(), index))
        .collect();
    if indices.len() != plan.dependency_order.len() || indices.len() != plan.selected.len() {
        return Err(syn::Error::new(
            proc_macro2::Span::call_site(),
            "dummy receipt order must list every selected constructor exactly once",
        ));
    }
    let count = indices.len();
    let mut rows = Vec::with_capacity(count);
    for (index, category) in plan.dependency_order.iter().enumerate() {
        let variant = plan.selected.get(&category.to_string()).ok_or_else(|| {
            syn::Error::new(category.span(), "dummy receipt order has no selected constructor")
        })?;
        let (local, dependencies) = project(category, variant)?;
        let mut children = Vec::with_capacity(dependencies.len());
        for dependency in dependencies {
            let child = indices
                .get(&dependency.to_string())
                .copied()
                .filter(|child| *child < index)
                .ok_or_else(|| {
                    syn::Error::new(
                        dependency.span(),
                        "selected dummy dependency is not an earlier recipe",
                    )
                })?;
            children.push(child);
        }
        rows.push(quote! {
            {
                let local: __br::LocalReceipt = #local;
                table[#index] = __receipt_try!(__br::compose(local, &[#(table[#children]),*]));
            }
        });
    }
    let tokens = quote! {
        #[allow(dead_code, unreachable_patterns)]
        const fn build_binding_dummy_receipts() -> Result<
            [mettail_runtime::binding_receipt::Receipt; #count],
            mettail_runtime::binding_receipt::ReceiptOverflow,
        > {
            use mettail_runtime::binding_receipt as __br;
            macro_rules! __receipt_try {
                ($expression:expr) => {
                    match $expression {
                        Ok(value) => value,
                        Err(error) => return Err(error),
                    }
                };
            }
            let mut table = [__br::Receipt::ZERO; #count];
            #(#rows)*
            Ok(table)
        }
        #[allow(dead_code)]
        const BINDING_DUMMY_RECEIPTS: Result<
            [mettail_runtime::binding_receipt::Receipt; #count],
            mettail_runtime::binding_receipt::ReceiptOverflow,
        > = build_binding_dummy_receipts();
    };
    Ok(DummyReceiptEmission { tokens, indices })
}

fn add_extraction(expression: TokenStream) -> TokenStream {
    quote! {
        local.extraction = __receipt_try!(local.extraction.checked_add(#expression));
    }
}

fn event(name: &str, count: usize) -> TokenStream {
    let name = format_ident!("{}", name);
    quote! { __br::Counts::singleton(__br::Event::#name, #count) }
}

/// Empty consuming-iterator construction, terminal next, and cleanup. The
/// owned iterator is one logical record; mem::take's replacement is separate.
fn empty_iterator() -> TokenStream {
    let calls = event("NativeWork", 3);
    let record = event("NativeRecord", 1);
    quote! { __receipt_try!(#calls.checked_add(#record)) }
}

fn infer_field(category: &Ident, pattern: TokenStream, field: TokenStream) -> TokenStream {
    quote! {
        __receipt_try!(__br::default_field_local(|value: &#category| match value {
            #category::#pattern => #field,
            _ => unreachable!("selected dummy field projection is never executed"),
        }))
    }
}

fn project_variant(
    language: &LanguageDef,
    category: &Ident,
    variant: &VariantKind,
) -> Result<(TokenStream, Vec<Ident>), syn::Error> {
    let label = variant.label();
    let inferred = quote! { __receipt_try!(__br::default_local_for(#category::#label)) };
    let handle = add_extraction(event("HandleField", 1));
    let iterator = add_extraction(empty_iterator());
    let replacement = add_extraction(quote! { local.construction });
    let no_children = Vec::new();
    let local = match variant {
        VariantKind::Nullary { .. } => quote! { __br::LocalReceipt::ZERO },
        VariantKind::Var { .. } => {
            let call = event("NativeWork", 1);
            let record = event("NativeRecord", 1);
            quote! {
                __br::LocalReceipt {
                    construction: __receipt_try!(#call.checked_add(#record)),
                    ..__br::LocalReceipt::ZERO
                }
            }
        },
        VariantKind::Literal { .. } => inferred,
        VariantKind::Collection { .. } => quote! {{
            let mut local = #inferred;
            #handle #replacement #iterator
            local
        }},
        VariantKind::CollectionLiteral { element_cat, coll_type, .. } => {
            match plan_for(element_cat, coll_type, OrderSensitivity::OrderAgnostic, language) {
                CollectionPlan::WholeValue { .. } => inferred,
                CollectionPlan::PerElement { .. } => quote! {{
                    let mut local = #inferred;
                    #handle #replacement #iterator
                    local
                }},
            }
        },
        VariantKind::Regular { fields, .. } => return project_regular(category, label, fields),
        VariantKind::RecursiveNativeLiteral { carrier, .. } => {
            let pattern = quote! { #label(native) };
            let pathmap =
                infer_field(category, pattern.clone(), carrier.pathmap_ref(&quote! { native }));
            let replace_pathmap = add_extraction(quote! { pathmap.construction });
            match carrier.storage() {
                NativeCarrierStorage::Direct => quote! {{
                    let mut local = #inferred;
                    let pathmap = #pathmap;
                    #handle #replace_pathmap #iterator
                    local
                }},
                NativeCarrierStorage::Arc => {
                    let inner = infer_field(category, pattern, quote! { native.as_ref() });
                    let check_owner = add_extraction(event("CheckArcOwner", 1));
                    let inner_glue = add_extraction(quote! { inner.field_glue });
                    quote! {{
                        let mut local = #inferred;
                        let pathmap = #pathmap;
                        let inner = #inner;
                        #handle #replacement #check_owner #replace_pathmap #iterator #inner_glue
                        local
                    }}
                },
            }
        },
        VariantKind::Refused { .. }
        | VariantKind::Binder { .. }
        | VariantKind::MultiBinder { .. } => {
            return Err(syn::Error::new(category.span(), "unsupported selected dummy recipe"));
        },
    };
    Ok((local, no_children))
}

fn project_regular(
    category: &Ident,
    label: &Ident,
    fields: &[FieldInfo],
) -> Result<(TokenStream, Vec<Ident>), syn::Error> {
    let names: Vec<_> = (0..fields.len())
        .map(|index| format_ident!("_field{}", index))
        .collect();
    let pattern = quote! { #label(#(#names),*) };
    let mut dependencies = Vec::with_capacity(fields.len());
    let mut statements = Vec::with_capacity(fields.len());
    for (index, field) in fields.iter().enumerate() {
        let name = &names[index];
        let native = field.is_optional
            || field.is_collection
            || matches!(field.opaque_leaf, Some(OpaqueLeafKind::TokenText));
        let construction = if native {
            let inferred = infer_field(category, pattern.clone(), quote! { #name });
            quote! { let field = #inferred; }
        } else {
            if field.is_predicate || field.is_opaque_leaf() {
                return Err(syn::Error::new(
                    category.span(),
                    "selected dummy has no finite field recipe",
                ));
            }
            dependencies.push(field.category.clone());
            quote! { let field = __br::LocalReceipt::ZERO; }
        };
        // Construction order follows generate_data_dummy_fn; extraction order
        // independently follows generate_regular_push_arm (opaque first).
        let extraction = if field.is_predicate || field.is_opaque_leaf() {
            TokenStream::new()
        } else if field.is_optional {
            let default = add_extraction(quote! { field.construction });
            let discarded_none = add_extraction(quote! { field.field_glue });
            quote! { #default #discarded_none }
        } else if field.is_collection {
            let default = add_extraction(quote! { field.construction });
            let iterator = add_extraction(empty_iterator());
            let into_inner = if matches!(
                field.coll_type,
                Some(CollectionType::HashMap) | Some(CollectionType::PathMap)
            ) {
                add_extraction(event("NativeWork", 1))
            } else {
                TokenStream::new()
            };
            quote! { #default #into_inner #iterator }
        } else {
            TokenStream::new()
        };
        let handle = add_extraction(event("HandleField", 1));
        statements.push(quote! {{
            #construction
            local = __receipt_try!(local.checked_add(field));
            #handle #extraction
        }});
    }
    Ok((
        quote! {{
            let mut local = __br::LocalReceipt::ZERO;
            #(#statements)*
            local
        }},
        dependencies,
    ))
}

#[cfg(test)]
mod tests {
    use super::super::iterative_drop::select_dummy_plan;
    use super::*;

    fn language() -> LanguageDef {
        syn::parse_str(
            r#"
            name: ReceiptFixture,
            types { Proc data Leaf data Pair },
            terms {
                PZero . |- "0" : Proc;
                LZero . |- "leaf" : Leaf;
                PairMake . left:Leaf, right:Leaf |- "pair" left right : Pair;
            },
            equations {}, rewrites {},
        "#,
        )
        .expect("receipt fixture language")
    }

    fn field(category: &str) -> FieldInfo {
        FieldInfo {
            category: format_ident!("{}", category),
            is_collection: false,
            coll_type: None,
            is_predicate: false,
            is_optional: false,
            opaque_leaf: None,
        }
    }

    fn text(tokens: TokenStream) -> String {
        tokens.to_string().split_whitespace().collect()
    }

    #[test]
    fn table_retains_exact_selection_order_and_repeated_dependencies() {
        let language = language();
        let plan = select_dummy_plan(&language);
        let emitted = generate_dummy_receipts(&language, &plan).expect("selected receipt table");
        assert_eq!(emitted.indices["Proc"], 0);
        assert_eq!(emitted.indices["Leaf"], 1);
        assert_eq!(emitted.indices["Pair"], 2);
        let source = text(emitted.tokens.clone());
        assert!(source.contains("table[2usize]"));
        assert!(source.contains("&[table[1usize],table[1usize]]"));
        assert_eq!(source.matches("__br::compose(").count(), 3);
        syn::parse2::<syn::File>(emitted.tokens).expect("table is Rust syntax");
    }

    #[test]
    fn invalid_order_and_projection_failure_are_not_zero_receipts() {
        let language = language();
        let mut plan = select_dummy_plan(&language);
        plan.dependency_order.swap(1, 2);
        assert!(generate_dummy_receipts(&language, &plan)
            .err()
            .expect("late dependency rejected")
            .to_string()
            .contains("not an earlier recipe"));
        plan.dependency_order.swap(1, 2);
        plan.dependency_order.push(format_ident!("Pair"));
        assert!(generate_dummy_receipts(&language, &plan).is_err());
        let plan = select_dummy_plan(&language);
        let error = emit_table(&plan, |category, _| {
            Err(syn::Error::new(category.span(), "explicit projection refusal"))
        })
        .err()
        .expect("projection error propagated");
        assert!(error.to_string().contains("explicit projection refusal"));
    }

    #[test]
    fn literal_collections_reuse_the_existing_element_boundary() {
        let language = language();
        let collection = |element: &str| VariantKind::CollectionLiteral {
            label: format_ident!("Items"),
            element_cat: format_ident!("{}", element),
            coll_type: CollectionType::Vec,
        };
        let primitive = text(
            project_variant(&language, &format_ident!("Bytes"), &collection("u8"))
                .expect("primitive collection")
                .0,
        );
        let category = text(
            project_variant(&language, &format_ident!("Leaves"), &collection("Leaf"))
                .expect("category collection")
                .0,
        );
        assert!(!primitive.contains("HandleField"));
        assert!(category.contains("HandleField"));
        assert!(category.contains("NativeWork,3usize"));
    }

    #[test]
    fn regular_optional_and_map_sites_follow_actual_drop_branch_order() {
        let category = format_ident!("Pair");
        let label = format_ident!("PairMake");
        let mut optional = field("Leaf");
        optional.is_optional = true;
        let (ordinary, children) =
            project_regular(&category, &label, &[optional.clone()]).expect("optional recipe");
        assert!(children.is_empty());
        assert!(text(ordinary).contains("checked_add(field.field_glue)"));
        optional.opaque_leaf = Some(OpaqueLeafKind::GuestBody);
        let opaque = text(
            project_regular(&category, &label, &[optional])
                .expect("opaque None")
                .0,
        );
        assert!(!opaque.contains("checked_add(field.field_glue)"));
        let mut map = field("Leaf");
        map.is_collection = true;
        map.coll_type = Some(CollectionType::HashMap);
        let regular = text(
            project_regular(&category, &label, &[map])
                .expect("regular map")
                .0,
        );
        assert!(regular.contains("NativeWork,1usize"));
        let literal = text(
            project_variant(
                &language(),
                &category,
                &VariantKind::CollectionLiteral {
                    label,
                    element_cat: format_ident!("Leaf"),
                    coll_type: CollectionType::HashMap,
                },
            )
            .expect("literal map")
            .0,
        );
        assert!(!literal.contains("NativeWork,1usize"));
    }

    #[test]
    fn emit_compilable_selected_recipe_and_overflow_fixture() {
        let language = language();
        let mut plan = select_dummy_plan(&language);
        let mut optional = field("Leaf");
        optional.is_optional = true;
        let mut vector = field("Leaf");
        vector.is_collection = true;
        vector.coll_type = Some(CollectionType::Vec);
        let mut token = field("String");
        token.opaque_leaf = Some(OpaqueLeafKind::TokenText);
        plan.selected.insert(
            "Pair".into(),
            VariantKind::Regular {
                label: format_ident!("PairMake"),
                fields: vec![field("Leaf"), field("Leaf"), optional, vector, token],
            },
        );
        // Exercise both native-storage descriptors, which ordinary categories
        // currently avoid selecting by using their Var fallback.
        for (name, storage, access) in [
            (
                "Direct",
                NativeCarrierStorage::Direct,
                crate::gen::native_carrier::ZipperAccess::Read,
            ),
            (
                "Shared",
                NativeCarrierStorage::Arc,
                crate::gen::native_carrier::ZipperAccess::Write,
            ),
        ] {
            let category = format_ident!("{}", name);
            plan.dependency_order.push(category);
            plan.selected.insert(
                name.into(),
                VariantKind::RecursiveNativeLiteral {
                    label: format_ident!("Value"),
                    carrier: crate::gen::native_carrier::NativeRecursiveCarrier::Zipper {
                        storage,
                        access,
                        key_category: format_ident!("Leaf"),
                        value_category: format_ident!("Leaf"),
                    },
                },
            );
        }
        let normal = generate_dummy_receipts(&language, &plan)
            .expect("complete fixture projection")
            .tokens;
        let overflow = emit_table(&plan, |category, variant| {
            if category == "Leaf" {
                Ok((
                    quote! { __br::LocalReceipt {
                        construction: __br::Counts::singleton(__br::Event::NativeWork, usize::MAX),
                        ..__br::LocalReceipt::ZERO
                    } },
                    Vec::new(),
                ))
            } else {
                project_variant(&language, category, variant)
            }
        })
        .expect("overflow is a target arithmetic result, not projection failure")
        .tokens;
        let fixture = quote! {
            #![allow(dead_code, unreachable_patterns)]
            enum Proc { PZero }
            enum Leaf { LZero }
            enum Pair {
                PairMake(std::sync::Arc<Leaf>, std::sync::Arc<Leaf>,
                    Option<std::sync::Arc<Leaf>>, Vec<Leaf>, String),
            }
            enum Direct { Value(mettail_runtime::ReadZipperLit<Leaf, Leaf>) }
            enum Shared { Value(std::sync::Arc<mettail_runtime::WriteZipperLit<Leaf, Leaf>>) }
            mod normal {
                use super::*;
                #normal
                pub fn verify() {
                    use mettail_runtime::binding_receipt::Event;
                    let table = BINDING_DUMMY_RECEIPTS.expect("valid table");
                    assert_eq!(table.len(), 5);
                    assert_eq!(table[2].construction.get(Event::AllocateArc), 2);
                    assert_eq!(table[2].construction.get(Event::ConstructCategory), 3);
                    assert_eq!(table[2].extraction.get(Event::HandleField), 5);
                    assert_eq!(table[2].extraction.get(Event::NativeRecord), 3);
                    assert_eq!(table[2].extraction.get(Event::NativeWork), 6);
                    assert_eq!(table[3].extraction.get(Event::NativeWork), 4);
                    assert_eq!(table[3].extraction.get(Event::NativeRecord), 2);
                    assert_eq!(table[3].extraction.get(Event::CheckArcOwner), 0);
                    assert_eq!(table[4].extraction.get(Event::NativeWork), 9);
                    assert_eq!(table[4].extraction.get(Event::NativeRecord), 5);
                    assert_eq!(table[4].extraction.get(Event::CheckArcOwner), 1);
                    assert_eq!(table[4].extraction.get(Event::AllocateArc), 1);
                    for receipt in table {
                        for event in mettail_runtime::binding_receipt::EVENTS {
                            assert!(receipt.active_drop.get(event) <= receipt.normal_drop.get(event));
                        }
                    }
                }
            }
            mod overflow {
                use super::*;
                #overflow
                pub fn verify() {
                    use mettail_runtime::binding_receipt::{Event, ReceiptOverflow};
                    assert_eq!(BINDING_DUMMY_RECEIPTS,
                        Err(ReceiptOverflow { event: Event::NativeWork }));
                }
            }
            fn main() {
                normal::verify();
                overflow::verify();
                println!("selected dummy receipts and typed overflow verified");
            }
        };
        syn::parse2::<syn::File>(fixture.clone()).expect("compiled fixture Rust syntax");
        if std::env::var_os("METTAIL_CAPTURE_DUMMY_RECEIPTS").is_some() {
            let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../target/verification/dummy-receipts");
            std::fs::create_dir_all(&directory).expect("create fixture output directory");
            std::fs::write(directory.join("selected.rs"), fixture.to_string())
                .expect("write generated receipt fixture");
        }
    }
}
