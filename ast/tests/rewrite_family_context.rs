use mettail_ast::language::{parse_rewrite_fragment, RuleContextType};
use mettail_ast::types::TypeExpr;
use proptest::prelude::*;

fn base_name(ty: &TypeExpr) -> String {
    let TypeExpr::Base(name) = ty else {
        panic!("expected the authored base category");
    };
    name.to_string()
}

proptest! {
    #[test]
    fn family_context_retains_ordered_domains_and_result(
        domains in prop::collection::vec("[A-Z][a-z]{0,8}", 0..12),
        result in "[A-Z][a-z]{0,8}",
    ) {
        let mut source = format!("Rewrite({result})");
        for domain in domains.iter().rev() {
            source = format!("[{domain} -> {source}]");
        }
        let RuleContextType::RewriteFamily { domains: actual, result: output } =
            syn::parse_str(&source).expect("explicit family context parses")
        else {
            return Err(TestCaseError::fail("explicit family became an ordinary type"));
        };
        prop_assert_eq!(actual.iter().map(base_name).collect::<Vec<_>>(), domains);
        prop_assert_eq!(base_name(&output), result);
        prop_assert!(syn::parse_str::<TypeExpr>(&source).is_err());
    }

    #[test]
    fn ordinary_context_keeps_the_existing_type_parser(
        domains in prop::collection::vec("[A-Z][a-z]{0,8}", 0..12),
        result in "[A-Z][a-z]{0,8}",
    ) {
        let mut source = result;
        for domain in domains.iter().rev() {
            source = format!("[{domain} -> {source}]");
        }
        let original = syn::parse_str::<TypeExpr>(&source).expect("ordinary type parses");
        let RuleContextType::Ordinary(actual) = syn::parse_str(&source).expect("context parses") else {
            return Err(TestCaseError::fail("ordinary type became a rewrite family"));
        };
        prop_assert_eq!(actual, original);
    }
}

#[test]
fn explicit_family_context_parses_in_a_complete_rewrite() {
    let rules = parse_rewrite_fragment(
        "Body . f:[Name -> Rewrite(Proc)], q:Proc |- (New ^x.(s (f x))) ~> (New ^x.(t (f x)));",
    )
    .expect("the existing application and binder syntax carries explicit families");
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].type_context.len(), 2);
    assert!(matches!(rules[0].type_context[0].ty, RuleContextType::RewriteFamily { .. }));
    assert!(matches!(rules[0].type_context[1].ty, RuleContextType::Ordinary(_)));
}

#[test]
fn ordinary_rewrite_names_and_collection_types_remain_ordinary() {
    for source in [
        "Rewrite",
        "R",
        "s",
        "t",
        "[Name -> Rewrite]",
        "Vec(Rewrite)",
        "HashMap(Name, Proc)",
    ] {
        assert!(matches!(
            syn::parse_str::<RuleContextType>(source),
            Ok(RuleContextType::Ordinary(_))
        ));
    }
}

#[test]
fn rewrite_families_do_not_become_first_class_types() {
    for source in [
        "Vec(Rewrite(Proc))",
        "[Rewrite(Proc) -> Name]",
        "Rewrite(Rewrite(Proc))",
        "Rewrite()",
        "Rewrite(Name, Proc)",
    ] {
        assert!(syn::parse_str::<RuleContextType>(source).is_err(), "{source}");
    }
}
