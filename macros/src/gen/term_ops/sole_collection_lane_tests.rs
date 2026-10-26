//! Sole-collection lane (`VariantKind::Collection`): every emitter follows the
//! declared carrier and element. The auto-flattening helper applies only when
//! the element is the owner category, and a `HashSet(T)` field rides
//! `mettail_runtime::HashSetLit<T>`. Each test reports every failed check.

use super::*;

/// Each carrier and element shape of the lane, with one opener per constructor.
pub(crate) fn sole_collection_lane_language() -> LanguageDef {
    syn::parse_str(
        r#"
            name: SoleCollectionLane,
            types { Proc Name data Meta },
            terms {
                PZero . |- "0" : Proc;
                NLit . |- "n" : Name;
                MLit . |- "m" : Meta;
                PPar . ps:HashBag(Proc) |- "par" "{" ps.*sep("|") "}" : Proc;
                PNames . ns:HashBag(Name) |- "names" "{" ns.*sep(",") "}" : Proc;
                PMetas . ms:HashBag(Meta) |- "metas" "{" ms.*sep(",") "}" : Proc;
                PSet . s:HashSet(Proc) |- "set" "{" s.*sep(",") "}" : Proc;
                PNameSet . s:HashSet(Name) |- "nameset" "{" s.*sep(",") "}" : Proc;
                PSeq . xs:Vec(Proc) |- "seq" "[" xs.*sep(",") "]" : Proc;
                PNameSeq . xs:Vec(Name) |- "nameseq" "[" xs.*sep(",") "]" : Proc;
            },
            equations {},
            rewrites {},
        "#,
    )
    .expect("sole-collection lane fixture must parse")
}

pub(crate) fn compact(source: impl ToString) -> String {
    source.to_string().split_whitespace().collect()
}

/// Every missing `present` needle and every found `absent` needle.
pub(crate) fn failed_checks(text: &str, present: &[&str], absent: &[&str]) -> Vec<String> {
    let mut failed = Vec::with_capacity(present.len() + absent.len());
    for needle in present {
        if !text.contains(needle) {
            failed.push(format!("missing `{needle}`"));
        }
    }
    for needle in absent {
        if text.contains(needle) {
            failed.push(format!("unexpected `{needle}`"));
        }
    }
    failed
}

#[test]
fn flatten_helper_is_emitted_only_for_the_owner_element() {
    let language = sole_collection_lane_language();
    let tokens = generate_flatten_helpers(&language);
    syn::parse2::<syn::File>(tokens.clone()).expect("flatten helpers parse");
    let failed = failed_checks(
        &compact(&tokens),
        &["pubfninsert_into_ppar("],
        &[
            "insert_into_pnames",
            "insert_into_pmetas",
            "insert_into_pset",
            "insert_into_pnameset",
            "insert_into_pseq",
            "insert_into_pnameseq",
        ],
    );
    assert!(failed.is_empty(), "{failed:#?}");
}

#[test]
fn hash_set_fields_ride_hash_set_lit_in_the_ast() {
    let language = sole_collection_lane_language();
    let tokens = crate::gen::types::enums::generate_ast_enums(&language);
    syn::parse2::<syn::File>(tokens.clone()).expect("enum declarations parse");
    let failed = failed_checks(
        &compact(&tokens),
        &[
            "PSet(mettail_runtime::HashSetLit<Proc>)",
            "PNameSet(mettail_runtime::HashSetLit<Name>)",
            "PPar(mettail_runtime::HashBag<Proc>)",
            "PNames(mettail_runtime::HashBag<Name>)",
            "PSeq(Vec<Proc>)",
            "PNameSeq(Vec<Name>)",
        ],
        &["std::collections::HashSet<"],
    );
    assert!(failed.is_empty(), "{failed:#?}");
}

#[test]
fn normalization_inserts_cross_category_elements_directly() {
    let language = sole_collection_lane_language();
    let tokens = generate_normalize_functions(&language, &[]);
    syn::parse2::<syn::File>(tokens.clone()).expect("normalization parses");
    let failed = failed_checks(
        &compact(&tokens),
        &[
            "Proc::insert_into_ppar(&mut__bag,__element);",
            "__bag.insert(__element);",
            "letmutnormalized=mettail_runtime::HashSetLit::new();",
        ],
        &[
            "insert_into_pnames",
            "insert_into_pmetas",
            "VisitMeta",
            "std::collections::HashSet::with_capacity(",
        ],
    );
    assert!(failed.is_empty(), "{failed:#?}");
}

/// TaggedNormalizationMachine.v, "Fused AC bag frames": the frame holds one slot per stored
/// entry (`fused_bag_value_count`), because the visit loop and the assembler both walk the stored
/// entries. An ordered sequence has no multiplicities, so its frame keeps `len()`.
#[test]
fn fused_bag_frames_reserve_one_slot_per_stored_entry() {
    let language = sole_collection_lane_language();
    let tokens = generate_normalize_functions(&language, &[]);
    syn::parse2::<syn::File>(tokens.clone()).expect("normalization parses");
    let failed = failed_checks(
        &compact(&tokens),
        &[
            "Proc::PPar(refcollection)=>{letvalue_base=results.len();\
             letvalue_count=collection.distinct_len();\
             results.resize_with(value_base+value_count,||None);",
            "Proc::PNames(refcollection)=>{letvalue_base=results.len();\
             letvalue_count=collection.distinct_len();\
             results.resize_with(value_base+value_count,||None);",
        ],
        &[
            "Proc::PPar(refcollection)=>{letvalue_base=results.len();\
             results.resize_with(value_base+collection.len(),||None);",
            "Proc::PNames(refcollection)=>{letvalue_base=results.len();\
             results.resize_with(value_base+collection.len(),||None);",
        ],
    );
    assert!(failed.is_empty(), "{failed:#?}");
}

#[test]
fn substitution_and_clone_rebuild_hash_sets_as_hash_set_lit() {
    let language = sole_collection_lane_language();
    let substitution = crate::gen::term_ops::subst::generate_substitution(&language);
    syn::parse2::<syn::File>(substitution.clone()).expect("substitution parses");
    let mut failed = failed_checks(
        &compact(&substitution),
        &["letmutset=mettail_runtime::HashSetLit::new();"],
        &["std::collections::HashSet::with_capacity("],
    );
    let clone = crate::gen::term_ops::iterative_clone::generate_iterative_clone(&language);
    syn::parse2::<syn::File>(clone.clone()).expect("iterative clone parses");
    failed.extend(failed_checks(
        &compact(&clone),
        &["letmutoutput=mettail_runtime::HashSetLit::new();"],
        &["with_capacity_and_hasher"],
    ));
    assert!(failed.is_empty(), "{failed:#?}");
}

#[test]
fn term_generation_follows_the_declared_carrier_and_element() {
    let language = sole_collection_lane_language();
    let exhaustive = crate::gen::term_gen::generate_term_generation(&language);
    syn::parse2::<syn::File>(exhaustive.clone()).expect("exhaustive generation parses");
    let mut failed = failed_checks(
        &compact(&exhaustive),
        &[
            "ifletSome(elems)=self.name_by_depth.get(&d){foreleminelems{\
             letmutbag=mettail_runtime::HashBag::new();bag.insert(elem.clone());\
             terms.push(Proc::PNames(bag));}}",
            "ifletSome(elems)=self.name_by_depth.get(&d){foreleminelems{\
             letmutbag=mettail_runtime::HashSetLit::new();bag.insert(elem.clone());\
             terms.push(Proc::PNameSet(bag));}}",
        ],
        &["letmutbag=mettail_runtime::HashBag::new();bag.insert(elem.clone());\
           terms.push(Proc::PNameSet(bag));"],
    );
    let random = crate::gen::term_gen::generate_random_generation(&language);
    syn::parse2::<syn::File>(random.clone()).expect("random generation parses");
    failed.extend(failed_checks(
        &compact(&random),
        &["{letsize=rng.gen_range(0..=max_collection_width);\
           letmutbag=mettail_runtime::HashSetLit::new();for_in0..size{\
           letelem_depth=ifdepth>0{rng.gen_range(0..depth)}else{0};\
           letelem=Name::generate_random_at_depth_internal(\
           vars,elem_depth,max_collection_width,rng,binding_depth);\
           bag.insert(elem);}Proc::PNameSet(bag)}"],
        &[],
    ));
    assert!(failed.is_empty(), "{failed:#?}");
}

#[test]
fn tape_strategies_build_hash_sets_as_hash_set_lit() {
    let language = sole_collection_lane_language();
    let strategies = crate::gen::test_gen::strategies::generate_strategies(&language);
    syn::parse_str::<syn::File>(&strategies).expect("strategies parse");
    let failed = failed_checks(
        &compact(&strategies),
        &["letmutset=mettail_runtime::HashSetLit::new();for_in0..num_elems{\
           set.insert(build_name_from_tape(reader,child_depth));}Proc::PNameSet(set)"],
        &["std::collections::HashSet::new()", "compile_error"],
    );
    assert!(failed.is_empty(), "{failed:#?}");
}
