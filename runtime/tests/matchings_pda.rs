#[path = "support/matchings_recursive_oracle.rs"]
mod recursive_oracle;

use mettail_runtime::enumerate_matchings;

#[test]
fn iterative_enumerator_matches_recursive_depth_first_order() {
    let corpora = [
        Vec::<Vec<(usize, char)>>::new(),
        vec![Vec::new()],
        vec![vec![(0, 'a'), (1, 'b')]],
        vec![vec![(0, 'a'), (1, 'b')], vec![(0, 'c'), (2, 'd')], vec![(1, 'e'), (2, 'f')]],
        // Duplicate candidates remain duplicate DFS branches, exactly as before.
        vec![vec![(0, 'a'), (0, 'a')], vec![(1, 'b')]],
        // Every branch is blocked before the last group.
        vec![vec![(7, 'a')], vec![(7, 'b')], vec![(8, 'c')]],
    ];

    for candidates in corpora {
        assert_eq!(
            enumerate_matchings(&candidates),
            recursive_oracle::enumerate(&candidates),
            "matching enumeration diverged for {candidates:?}"
        );
    }
}

#[test]
fn iterative_enumerator_is_stack_safe_at_twenty_thousand_groups() {
    std::thread::Builder::new()
        .name("matching-pda-stack-gate".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let candidates: Vec<Vec<(usize, usize)>> =
                (0..20_000).map(|index| vec![(index, index)]).collect();
            let matches = enumerate_matchings(&candidates);
            assert_eq!(matches.len(), 1);
            assert_eq!(matches[0].0.len(), candidates.len());
            assert_eq!(matches[0].1.len(), candidates.len());
        })
        .expect("spawn matching PDA stack-gate thread")
        .join()
        .expect("matching PDA overflowed or panicked");
}
