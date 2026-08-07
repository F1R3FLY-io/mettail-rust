use super::*;
use dovetail::rules::Pattern;
use dovetail::set_automaton::{PatternId, SetAutomaton};

fn collect_recursive(
    view: &SetAutomatonView<'_, String>,
    state: StateId,
    loc_channel: &str,
    cap_channel: &str,
    descents: &mut Vec<(String, String)>,
    captures: &mut Vec<String>,
    names: &mut Vec<String>,
) {
    match view.node(state) {
        AutomatonNode::Var(name) => {
            captures.push(cap_channel.to_owned());
            names.push(name.to_owned());
        },
        AutomatonNode::App { op, args } => {
            descents.push((loc_channel.to_owned(), op.to_owned()));
            for (index, &arg) in args.iter().enumerate() {
                collect_recursive(
                    view,
                    arg,
                    &spread_child_location(loc_channel, op, index),
                    &spread_child_location(cap_channel, op, index),
                    descents,
                    captures,
                    names,
                );
            }
        },
    }
}

fn run_iterative(
    view: &SetAutomatonView<'_, String>,
) -> (Vec<(String, String)>, Vec<String>, Vec<String>) {
    let mut descents = Vec::new();
    let mut captures = Vec::new();
    let mut names = Vec::new();
    collect_nested_schedule(
        view,
        view.entry_root_state(0),
        "loc",
        "cap",
        &mut descents,
        &mut captures,
        &mut names,
    );
    (
        descents
            .into_iter()
            .map(|descent| (descent.loc_channel, descent.op))
            .collect(),
        captures,
        names,
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
    let automaton = SetAutomaton::compile_structural([(PatternId(0), pattern)])
        .expect("schedule oracle pattern compiles");
    let view = automaton.view();
    let mut descents = Vec::new();
    let mut captures = Vec::new();
    let mut names = Vec::new();
    collect_recursive(
        &view,
        view.entry_root_state(0),
        "loc",
        "cap",
        &mut descents,
        &mut captures,
        &mut names,
    );
    assert_eq!(run_iterative(&view), (descents, captures, names));
}

#[test]
fn nested_schedule_is_stack_safe_at_four_thousand_levels() {
    std::thread::Builder::new()
        .name("nested-schedule-stack-gate".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut pattern = Pattern::var("x");
            for _ in 0..4_096 {
                pattern = Pattern::app("f".to_owned(), vec![pattern]);
            }
            let automaton = SetAutomaton::compile_structural([(PatternId(0), pattern)])
                .expect("deep schedule pattern compiles");
            let (descents, captures, names) = run_iterative(&automaton.view());
            assert_eq!(descents.len(), 4_096);
            assert_eq!(captures.len(), 1);
            assert_eq!(names, ["x"]);
        })
        .expect("spawn nested-schedule stack-gate thread")
        .join()
        .expect("nested-schedule collector overflowed or panicked");
}
