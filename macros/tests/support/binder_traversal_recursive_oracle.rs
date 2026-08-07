use super::{traversal_sites, BinderPosition, TraversalResume};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ResumeTrace {
    Rule(usize),
    Optional(usize, usize),
    BinderList(usize, usize),
}

#[derive(Debug, Default, Eq, PartialEq)]
struct SiteTrace {
    optionals: Vec<(usize, ResumeTrace)>,
    binder_lists: Vec<(usize, ResumeTrace)>,
}

#[derive(Clone, Copy)]
enum Owner {
    Rule,
    Optional(usize),
    BinderList(usize),
}

fn trace_resume(resume: TraversalResume) -> ResumeTrace {
    match resume {
        TraversalResume::Rule { next_pos } => ResumeTrace::Rule(next_pos as usize),
        TraversalResume::Optional { group_idx, next_sub_pos } => {
            ResumeTrace::Optional(group_idx as usize, next_sub_pos as usize)
        },
        TraversalResume::BinderList { frame_idx, next_sub_pos } => {
            ResumeTrace::BinderList(frame_idx as usize, next_sub_pos as usize)
        },
    }
}

fn resume_for(owner: Owner, index: usize, len: usize) -> ResumeTrace {
    match owner {
        Owner::Rule => ResumeTrace::Rule(index + 2),
        Owner::Optional(group_idx) => ResumeTrace::Optional(group_idx, index + 2),
        Owner::BinderList(frame_idx) => {
            ResumeTrace::BinderList(frame_idx, if index + 1 == len { 0 } else { index + 2 })
        },
    }
}

/// Bounded specification oracle. Recursion is intentional and test-only: it
/// states the source equations directly while production uses an explicit
/// heap worklist.
fn recursive_trace(
    positions: &[BinderPosition],
    owner: Owner,
    next_frame_idx: &mut usize,
    out: &mut SiteTrace,
) {
    for (index, position) in positions.iter().enumerate() {
        let resume = resume_for(owner, index, positions.len());
        match position {
            BinderPosition::OptionalGroup { positions, group_idx, .. } => {
                out.optionals.push((*group_idx as usize, resume));
                recursive_trace(
                    positions,
                    Owner::Optional(*group_idx as usize),
                    next_frame_idx,
                    out,
                );
            },
            BinderPosition::BinderListLoop { inner_positions, .. } => {
                let frame_idx = *next_frame_idx;
                *next_frame_idx += 1;
                out.binder_lists.push((frame_idx, resume));
                recursive_trace(inner_positions, Owner::BinderList(frame_idx), next_frame_idx, out);
            },
            _ => {},
        }
    }
}

fn iterative_trace(positions: &[BinderPosition]) -> SiteTrace {
    let sites = traversal_sites(positions);
    SiteTrace {
        optionals: sites
            .optionals
            .into_iter()
            .map(|site| (site.group_idx as usize, trace_resume(site.resume)))
            .collect(),
        binder_lists: sites
            .binder_lists
            .into_iter()
            .map(|site| (site.frame_idx as usize, trace_resume(site.resume)))
            .collect(),
    }
}

fn leaf() -> BinderPosition {
    BinderPosition::ParamParse {
        cat: "Expr".to_string(),
        collection: None,
    }
}

fn wrap_optional(position: BinderPosition, group_idx: u32) -> BinderPosition {
    BinderPosition::OptionalGroup {
        positions: vec![position],
        group_idx,
        first_token_set: vec!["x".to_string()],
    }
}

fn wrap_binder(position: BinderPosition) -> BinderPosition {
    BinderPosition::BinderListLoop {
        separator: ",".to_string(),
        close: ")".to_string(),
        inner_positions: vec![position],
        collection_param_cat: Some("Expr".to_string()),
        allow_empty: true,
        allow_multi: true,
        slot_idx: 0,
    }
}

#[test]
fn traversal_sites_match_recursive_equations_on_bounded_nested_forests() {
    for depth in 0..=8usize {
        for mask in 0..(1usize << depth) {
            let mut position = leaf();
            let mut group_idx = 0u32;
            for level in 0..depth {
                if mask & (1usize << level) == 0 {
                    position = wrap_optional(position, group_idx);
                    group_idx += 1;
                } else {
                    position = wrap_binder(position);
                }
            }
            let positions = vec![position];
            let mut expected = SiteTrace::default();
            let mut next_frame_idx = 0;
            recursive_trace(&positions, Owner::Rule, &mut next_frame_idx, &mut expected);
            assert_eq!(iterative_trace(&positions), expected, "depth={depth} mask={mask:#x}");
        }
    }
}

#[test]
fn traversal_sites_match_recursive_equations_on_branching_forest() {
    let positions = vec![
        wrap_optional(wrap_binder(leaf()), 0),
        wrap_binder(BinderPosition::OptionalGroup {
            positions: vec![wrap_binder(leaf()), wrap_optional(leaf(), 2)],
            group_idx: 1,
            first_token_set: vec!["y".to_string()],
        }),
    ];
    let mut expected = SiteTrace::default();
    let mut next_frame_idx = 0;
    recursive_trace(&positions, Owner::Rule, &mut next_frame_idx, &mut expected);
    assert_eq!(iterative_trace(&positions), expected);
}
