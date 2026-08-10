use super::*;
use dovetail::rules::Pattern;
use dovetail::set_automaton::{PatternId, SetAutomaton};

fn collect_recursive(
    view: &SetAutomatonView<'_, String>,
    state: StateId,
    root_slots: Vec<SlotId>,
    locations: &SubjectLocationIndex<'_>,
    position: MatcherPosition,
    descents: &mut Vec<(String, String)>,
    captures: &mut Vec<String>,
    capture_slots: &mut Vec<SlotId>,
) {
    match view.node(state) {
        AutomatonNode::Var => {
            captures.push(locations.channel("cap", "fixture-fp", "site0", position));
            capture_slots.push(root_slots[0]);
        },
        AutomatonNode::App { op, args } => {
            descents
                .push((locations.channel("loc", "fixture-fp", "site0", position), op.to_owned()));
            for (index, arg) in args.iter().enumerate() {
                let child_root_slots = arg
                    .parent_slots()
                    .map(|parent| root_slots[parent.index()])
                    .collect();
                collect_recursive(
                    view,
                    arg.state(),
                    child_root_slots,
                    locations,
                    locations.matcher_child(position, index),
                    descents,
                    captures,
                    capture_slots,
                );
            }
        },
    }
}

fn run_iterative(
    view: &SetAutomatonView<'_, String>,
    subject: &GroundTerm,
) -> (Vec<(String, String)>, Vec<String>, Vec<SlotId>) {
    let mut descents = Vec::new();
    let mut captures = Vec::new();
    let mut capture_slots = Vec::new();
    let root = view.entry_root_state(0);
    let locations = SubjectLocationIndex::new(subject);
    collect_nested_schedule(
        view,
        root,
        (0..view.state_slot_count(root))
            .map(SlotId::from_index)
            .collect(),
        &locations,
        "site0",
        "fixture-fp",
        MatcherPosition::Live(SubjectPosition::ROOT),
        &mut descents,
        &mut captures,
        &mut capture_slots,
    );
    (
        descents
            .into_iter()
            .map(|descent| (descent.loc_channel, descent.op))
            .collect(),
        captures,
        capture_slots,
    )
}

#[test]
fn nested_schedule_matches_recursive_preorder() {
    let pattern = Pattern::app(
        "f".to_owned(),
        vec![
            Pattern::app("g".to_owned(), vec![Pattern::var("x"), Pattern::var("y")]),
            Pattern::app("h".to_owned(), vec![Pattern::var("z")]),
        ],
    );
    let subject = GroundTerm::new(
        "f",
        vec![
            GroundTerm::new("g", vec![GroundTerm::nullary("a"), GroundTerm::nullary("b")]),
            GroundTerm::new("h", vec![GroundTerm::nullary("c")]),
        ],
    );
    let automaton = SetAutomaton::compile_structural([(PatternId(0), pattern)])
        .expect("schedule oracle pattern compiles");
    let view = automaton.view();
    let mut descents = Vec::new();
    let mut captures = Vec::new();
    let mut capture_slots = Vec::new();
    let root = view.entry_root_state(0);
    let locations = SubjectLocationIndex::new(&subject);
    collect_recursive(
        &view,
        root,
        (0..view.state_slot_count(root))
            .map(SlotId::from_index)
            .collect(),
        &locations,
        MatcherPosition::Live(SubjectPosition::ROOT),
        &mut descents,
        &mut captures,
        &mut capture_slots,
    );
    assert_eq!(run_iterative(&view, &subject), (descents, captures, capture_slots));
}

#[test]
fn nested_schedule_is_stack_safe_at_twenty_thousand_levels() {
    std::thread::Builder::new()
        .name("nested-schedule-stack-gate".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let mut pattern = Pattern::var("x");
            let mut subject = GroundTerm::nullary("leaf");
            for _ in 0..DEPTH {
                pattern = Pattern::app("f".to_owned(), vec![pattern]);
                subject = GroundTerm::new("f", vec![subject]);
            }
            let automaton = SetAutomaton::compile_structural([(PatternId(0), pattern)])
                .expect("deep schedule pattern compiles");
            let (descents, captures, capture_slots) = run_iterative(&automaton.view(), &subject);
            assert_eq!(descents.len(), DEPTH);
            assert_eq!(captures.len(), 1);
            assert_eq!(capture_slots, [SlotId::from_index(0)]);
        })
        .expect("spawn nested-schedule stack-gate thread")
        .join()
        .expect("nested-schedule collector overflowed or panicked");
}
