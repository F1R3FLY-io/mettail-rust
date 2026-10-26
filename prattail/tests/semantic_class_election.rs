use mettail_prattail::automata::lex_weight::LexicographicWeight;
use mettail_prattail::wpda_runtime::align_semantic_class_representatives;

#[derive(Clone, Debug, Eq, PartialEq)]
struct Term {
    key: u8,
    value: u16,
}

proptest::proptest! {
    #![proptest_config(proptest::prelude::ProptestConfig::with_cases(256))]

    #[test]
    fn alignment_preserves_classes_weights_and_first_elected_members(
        classes in proptest::collection::vec((0u8..16, proptest::num::u16::ANY, 0u16..32), 0..65),
        elections in proptest::collection::vec((0u8..20, proptest::num::u16::ANY), 0..65),
    ) {
        let before: Vec<_> = classes.into_iter().enumerate().map(|(index, (key, value, open_len))| {
            (Term { key, value }, LexicographicWeight::from_cost_with_lex(
                index as f64, u16::from(key), value, open_len,
            ).with_open_len(open_len))
        }).collect();
        let elected: Vec<_> = elections.into_iter().map(|(key, value)| Term { key, value }).collect();
        let mut aligned = before.clone();
        align_semantic_class_representatives(&mut aligned, &elected, |term| term.key);
        proptest::prop_assert_eq!(aligned.len(), before.len());
        for (index, (term, weight)) in aligned.iter().enumerate() {
            proptest::prop_assert_eq!(term.key, before[index].0.key);
            proptest::prop_assert_eq!(*weight, before[index].1);
            if !elected.iter().any(|candidate| candidate.key == term.key) {
                proptest::prop_assert_eq!(term, &before[index].0);
            }
        }
        for (index, candidate) in elected.iter().enumerate() {
            if elected[..index].iter().any(|earlier| earlier.key == candidate.key) { continue; }
            for (term, _) in &aligned {
                if term.key == candidate.key { proptest::prop_assert_eq!(term, candidate); }
            }
        }
        let once = aligned.clone();
        align_semantic_class_representatives(&mut aligned, &elected, |term| term.key);
        proptest::prop_assert_eq!(aligned, once);
    }
}
