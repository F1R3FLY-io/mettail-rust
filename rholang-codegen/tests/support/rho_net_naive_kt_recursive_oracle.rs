use super::*;

use dovetail::rules::Pattern;
use dovetail::set_automaton::SetAutomaton;

fn recursive_non_root_ops(
    view: &SetAutomatonView<'_, String>,
    state: dovetail::set_automaton::StateId,
    ops: &mut Vec<String>,
) {
    match view.node(state) {
        AutomatonNode::Var => {},
        AutomatonNode::App { op, args } => {
            ops.push(op.to_string());
            for arg in args {
                recursive_non_root_ops(view, arg.state(), ops);
            }
        },
    }
}

fn recursive_entry_sites(
    locations: &SubjectLocationIndex<'_>,
    position: SubjectPosition,
    root_op: &str,
    sites: &mut Vec<SubjectPosition>,
) {
    let node = locations.term(position);
    if node.constructor == root_op {
        sites.push(position);
    }
    for child in locations.children(position) {
        recursive_entry_sites(locations, child, root_op, sites);
    }
}

fn recursive_ruleset_sites(
    locations: &SubjectLocationIndex<'_>,
    position: SubjectPosition,
    roots: &BTreeSet<String>,
    sites: &mut Vec<SubjectPosition>,
) {
    let node = locations.term(position);
    if roots.contains(&node.constructor) {
        sites.push(position);
    }
    for child in locations.children(position) {
        recursive_ruleset_sites(locations, child, roots, sites);
    }
}

fn recursive_selfdriving_labels(
    term: &GroundTerm,
    labels: &mut BTreeSet<String>,
) -> Result<(), NaiveKtUnsupported> {
    if term.coll_type.is_some() {
        return Err(NaiveKtUnsupported::SelfDrivingCollectionSubject {
            op: term.constructor.clone(),
        });
    }
    if respread_reserved_labels().contains(&term.constructor.as_str()) {
        return Err(NaiveKtUnsupported::SelfDrivingReservedLabel { op: term.constructor.clone() });
    }
    labels.insert(term.constructor.clone());
    for child in &term.children {
        recursive_selfdriving_labels(child, labels)?;
    }
    Ok(())
}

fn shallow_subject() -> GroundTerm {
    GroundTerm::new(
        "A",
        vec![
            GroundTerm::new("B", vec![GroundTerm::nullary("A")]),
            GroundTerm::new("C", vec![GroundTerm::nullary("D")]),
        ],
    )
}

#[test]
fn iterative_naive_walkers_match_the_recursive_equations() {
    let automaton = SetAutomaton::compile_structural([(
        PatternId(0),
        Pattern::app(
            "A".to_owned(),
            vec![
                Pattern::app("B".to_owned(), vec![Pattern::var("x")]),
                Pattern::app("C".to_owned(), vec![Pattern::var("y")]),
            ],
        ),
    )])
    .expect("shallow structural pattern compiles");
    let view = automaton.view();
    let root = view.entry_root_state(0);
    let AutomatonNode::App { args, .. } = view.node(root) else {
        unreachable!();
    };
    let mut actual_ops = Vec::new();
    let mut expected_ops = Vec::new();
    for arg in args {
        collect_non_root_ops(&view, arg.state(), &mut actual_ops);
        recursive_non_root_ops(&view, arg.state(), &mut expected_ops);
    }
    assert_eq!(actual_ops, expected_ops);

    let subject = shallow_subject();
    let locations = SubjectLocationIndex::new(&subject);
    let mut actual_sites = Vec::new();
    let mut expected_sites = Vec::new();
    collect_entry_sites(&locations, "A", &mut actual_sites);
    recursive_entry_sites(&locations, SubjectPosition::ROOT, "A", &mut expected_sites);
    assert_eq!(actual_sites, expected_sites);

    let roots = ["A".to_owned(), "D".to_owned()].into_iter().collect();
    actual_sites.clear();
    expected_sites.clear();
    collect_ruleset_sites(&locations, &roots, &mut actual_sites);
    recursive_ruleset_sites(&locations, SubjectPosition::ROOT, &roots, &mut expected_sites);
    assert_eq!(actual_sites, expected_sites);

    let mut actual_labels = BTreeSet::new();
    let mut expected_labels = BTreeSet::new();
    assert_eq!(
        collect_selfdriving_labels(&subject, &mut actual_labels),
        recursive_selfdriving_labels(&subject, &mut expected_labels)
    );
    assert_eq!(actual_labels, expected_labels);

    let conflict = GroundTerm::new(
        "Root",
        vec![GroundTerm::nullary("A"), GroundTerm::new("A", vec![GroundTerm::nullary("x")])],
    );
    actual_labels.clear();
    expected_labels.clear();
    assert_eq!(
        collect_selfdriving_labels(&conflict, &mut actual_labels),
        recursive_selfdriving_labels(&conflict, &mut expected_labels)
    );
    assert_eq!(actual_labels, expected_labels);
}

#[test]
fn naive_walkers_handle_twenty_thousand_levels_on_a_small_stack() {
    const DEPTH: usize = 20_000;
    std::thread::Builder::new()
        .name("naive-kt-walkers-small-stack".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut pattern = Pattern::var("leaf");
            for _ in 0..DEPTH {
                pattern = Pattern::app("Wrap".to_owned(), vec![pattern]);
            }
            let automaton = SetAutomaton::compile_structural([(PatternId(0), pattern)])
                .expect("deep structural pattern compiles");
            let view = automaton.view();
            let mut ops = Vec::new();
            collect_non_root_ops(&view, view.entry_root_state(0), &mut ops);
            assert_eq!(ops.len(), DEPTH);

            let mut subject = GroundTerm::nullary("Leaf");
            for _ in 0..DEPTH {
                subject = GroundTerm::new("Wrap", vec![subject]);
            }
            let locations = SubjectLocationIndex::new(&subject);
            let mut sites = Vec::new();
            collect_entry_sites(&locations, "Leaf", &mut sites);
            assert_eq!(sites.len(), 1);
            let roots = ["Leaf".to_owned()].into_iter().collect();
            let mut ruleset_sites = Vec::new();
            collect_ruleset_sites(&locations, &roots, &mut ruleset_sites);
            assert_eq!(ruleset_sites, sites);

            let mut labels = BTreeSet::new();
            collect_selfdriving_labels(&subject, &mut labels)
                .expect("the deep unary subject has admissible labels");
            assert_eq!(labels, ["Leaf".to_owned(), "Wrap".to_owned()].into_iter().collect());
        })
        .expect("small-stack naive-walker thread must spawn")
        .join()
        .expect("naive walkers must not overflow the native stack");
}
