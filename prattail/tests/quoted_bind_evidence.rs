use mettail_ast::types::CollectionType;
use mettail_prattail::automata::TokenKind;
use mettail_prattail::binding_power::InfixRuleInfo;
use mettail_prattail::wpda_rule_analysis::binder::BinderShape;
use mettail_prattail::wpda_rule_analysis::collection::assembly::{
    try_collect_bracket_delimiters, CollectionAssemblyContext,
};
use mettail_prattail::wpda_rule_analysis::collection::CollectionShape;
use mettail_prattail::wpda_runtime::SliceTokenSource;
use mettail_prattail::wpda_transitions::prefix_policy::prefix_at_quoted_bind_gate_evidence;
use proptest::prelude::*;
use std::collections::BTreeSet;

struct BracketContext;

impl<'a> CollectionAssemblyContext<'a, Option<(bool, u8)>> for BracketContext {
    type Error = ();
    type Label = &'static str;

    fn try_collection(
        &mut self,
        rule: &'a Option<(bool, u8)>,
    ) -> Result<Option<CollectionShape<CollectionType>>, ()> {
        Ok(rule.map(|(synth, index)| CollectionShape {
            open_token: format!("open{index}"),
            has_synth_paren: synth,
            close: if synth {
                ")".into()
            } else {
                format!("close{index}")
            },
            separator: ",".into(),
            pair_separator: None,
            element_cat: "Term".into(),
            coll_kind: CollectionType::Vec,
            label: "Collection".into(),
        }))
    }

    fn try_infix(&mut self, _: &'a Option<(bool, u8)>) -> Result<Option<InfixRuleInfo>, ()> {
        panic!("bracket collection must not inspect infix operators")
    }

    fn try_binder(&mut self, _: &'a Option<(bool, u8)>) -> Result<Option<BinderShape>, ()> {
        panic!("binder terminators must not enter the bracket alphabet")
    }

    fn try_label(&mut self, _: &'a Option<(bool, u8)>) -> Result<&'static str, ()> {
        panic!("bracket collection does not need labels")
    }
}

const OPEN: &[&str] = &["(", "[", "#{", "{", "{|", "if"];
const CLOSE: &[&str] = &[")", "]", "}#", "}", "|}", "then"];
const ROW: &[&str] = &["", ";", "|"];
const SYMBOLS: &[&str] =
    &["(", ")", "{", "}", "<-", "<=", ",", ";", "|", "Set", "where", "in", "x"];

fn scan(codes: &[usize], binds: &[&str]) -> bool {
    let kinds: Vec<_> = std::iter::once(TokenKind::Fixed("@".into()))
        .chain(
            codes
                .iter()
                .map(|&code| TokenKind::Fixed(SYMBOLS[code].into())),
        )
        .collect();
    prefix_at_quoted_bind_gate_evidence(
        &SliceTokenSource::new(&kinds),
        0,
        binds,
        &[","],
        OPEN,
        CLOSE,
        ROW,
    )
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn bracket_alphabet_contains_only_collection_pairs(
        rules in prop::collection::vec(prop::option::of((any::<bool>(), 0u8..16)), 0..64),
    ) {
        let (opens, closes) = try_collect_bracket_delimiters(&[rules.clone()], &mut BracketContext).unwrap();
        prop_assert!(opens.contains("("));
        prop_assert!(closes.contains(")"));
        for index in 0u8..16 {
            let expected = rules.iter().any(|rule| *rule == Some((false, index)));
            prop_assert_eq!(opens.contains(&format!("open{index}")), expected);
            prop_assert_eq!(closes.contains(&format!("close{index}")), expected);
        }
        prop_assert!(opens.is_disjoint(&BTreeSet::from(["<-".into(), "<=".into(), "where".into()])));
        prop_assert!(closes.is_disjoint(&BTreeSet::from(["<-".into(), "<=".into(), "where".into()])));
    }

    #[test]
    fn bind_evidence_matches_first_exposed_trigger(codes in prop::collection::vec(0usize..SYMBOLS.len(), 0..128)) {
        let levels: Vec<_> = codes.iter().scan(0i32, |level, &code| {
            let before = *level;
            *level += match code { 0 | 2 => 1, 1 | 3 => -1, _ => 0 };
            Some(before)
        }).collect();
        let decisive = codes.iter().zip(levels).find_map(|(&code, level)| {
            (level == 0 && matches!(code, 1 | 3 | 4 | 5 | 6 | 7 | 8)).then_some(code)
        });
        prop_assert_eq!(scan(&codes, &["<-", "<="]), matches!(decisive, Some(4 | 5)));
        prop_assert!(!scan(&codes, &[]));
    }

    #[test]
    fn balanced_nested_rows_cannot_supply_outer_bind_evidence(depth in 1usize..32, persistent in any::<bool>(), polyadic in any::<bool>()) {
        let bind = if persistent { 5 } else { 4 };
        let mut codes = vec![2; depth];
        codes.extend([12, bind, 12, 7, 12, bind, 12, 7, 12, bind, 12]);
        codes.extend(std::iter::repeat_n(3, depth));
        if polyadic { codes.push(6); }
        codes.push(bind);
        prop_assert_eq!(scan(&codes, &["<-", "<="]), !polyadic);
    }
}
