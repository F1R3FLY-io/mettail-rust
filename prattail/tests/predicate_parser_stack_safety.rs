use mettail_prattail::behavioral_pred::BehavioralPred;
use mettail_prattail::parser::predicate_pratt::{parse_predicate_from_str, PredicateParserConfig};

#[test]
fn predicate_parser_handles_depth_20k_on_a_256k_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("predicate-parser-pda-small-stack".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut source = "not(".repeat(DEPTH);
            source.push_str("ready()");
            source.push_str(&")".repeat(DEPTH));

            let predicate = parse_predicate_from_str(&source, PredicateParserConfig::default())
                .expect("deep predicate parses");
            let mut depth = 0;
            let mut cursor = &predicate;
            loop {
                match cursor {
                    BehavioralPred::Not(inner) => {
                        cursor = inner;
                        depth += 1;
                    },
                    BehavioralPred::RelationQuery { relation_name, args, negated } => {
                        assert_eq!(relation_name, "ready");
                        assert!(args.is_empty());
                        assert!(!negated);
                        break;
                    },
                    _ => panic!("expected a Not spine ending in ready()"),
                }
            }
            assert_eq!(depth, DEPTH);
        })
        .expect("small-stack worker spawns")
        .join()
        .expect("predicate parser must not overflow the native stack");
}
