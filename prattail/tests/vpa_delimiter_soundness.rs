use mettail_prattail::runtime_types::Range;
use mettail_prattail::vpa::{build_skip_table, DelimiterClass};
use proptest::prelude::*;

fn classify(token: &u8) -> DelimiterClass<u8> {
    match *token {
        0..=2 => DelimiterClass::Open(*token),
        3..=5 => DelimiterClass::Close(*token - 3),
        _ => DelimiterClass::Internal,
    }
}

fn table_for(symbols: &[u8]) -> Vec<Option<usize>> {
    let tokens: Vec<_> = symbols
        .iter()
        .copied()
        .map(|symbol| (symbol, Range::zero()))
        .collect();
    build_skip_table(&tokens, classify)
}

fn typed_stack_oracle(symbols: &[u8]) -> Vec<Option<usize>> {
    let mut table = vec![None; symbols.len()];
    let mut stack: Vec<(usize, u8)> = Vec::new();
    for (index, symbol) in symbols.iter().copied().enumerate() {
        match classify(&symbol) {
            DelimiterClass::Open(kind) => stack.push((index, kind)),
            DelimiterClass::Close(kind) => {
                if stack
                    .last()
                    .is_some_and(|(_, open_kind)| *open_kind == kind)
                {
                    let (open_index, _) = stack.pop().unwrap();
                    table[open_index] = Some(index);
                }
            },
            DelimiterClass::Internal => {},
        }
    }
    table
}

proptest! {
    #[test]
    fn skip_table_agrees_with_typed_stack_oracle(symbols in prop::collection::vec(0u8..8, 0..256)) {
        prop_assert_eq!(table_for(&symbols), typed_stack_oracle(&symbols));
    }

    #[test]
    fn every_pair_is_ordered_same_kind_unique_and_laminar(symbols in prop::collection::vec(0u8..8, 0..256)) {
        let table = table_for(&symbols);
        let pairs: Vec<_> = table.iter().enumerate().filter_map(|(open, close)| close.map(|close| (open, close))).collect();

        let mut closers = std::collections::HashSet::new();
        for &(open, close) in &pairs {
            prop_assert!(open < close);
            prop_assert_eq!(symbols[open], symbols[close] - 3);
            prop_assert!(closers.insert(close));
        }
        for &(a, b) in &pairs {
            for &(c, d) in &pairs {
                prop_assert!(!(a < c && c < b && b < d), "crossing pairs ({a}, {b}) and ({c}, {d})");
            }
        }
    }
}
