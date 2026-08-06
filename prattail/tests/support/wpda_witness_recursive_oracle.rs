use super::*;
use crate::automata::lex_weight::LexicographicWeight;
use crate::automata::semiring::SemiringRef;
use crate::wpda_runtime::{ActionArg, ActionEntry, SemanticBuilder};

#[derive(Debug)]
struct ChainValue(usize);

#[derive(Debug)]
struct CoercedValue(usize);

fn base_action(builder: &mut SemanticBuilder, _args: Vec<ActionArg>) {
    builder.push_term(ChainValue(1));
}

fn wrap_action(builder: &mut SemanticBuilder, args: Vec<ActionArg>) {
    if let [ActionArg::Term { value, .. }] = &args[..] {
        if let Some(value) = value.downcast_ref::<ChainValue>() {
            builder.push_term(ChainValue(value.0 + 1));
        }
    }
}

fn coercion_action(builder: &mut SemanticBuilder, args: Vec<ActionArg>) {
    if let [ActionArg::Term { value, .. }] = &args[..] {
        if let Some(value) = value.downcast_ref::<ChainValue>() {
            builder.push_term(CoercedValue(value.0));
        }
    }
}

static BASE_ACTION: ActionEntry = ActionEntry {
    action_fn: base_action,
    arity: 0,
    expected_input_cats: &[],
    output_cat: 0,
};

static WRAP_ACTION: ActionEntry = ActionEntry {
    action_fn: wrap_action,
    arity: 1,
    expected_input_cats: &[0],
    output_cat: 0,
};

static COERCION_ACTION: ActionEntry = ActionEntry {
    action_fn: coercion_action,
    arity: 1,
    expected_input_cats: &[0],
    output_cat: 1,
};

static ZERO_TO_ONE: [(u16, u16); 1] = [(1, 0)];

struct WitnessEngine;

impl WpdaEngine<LexicographicWeight> for WitnessEngine {
    fn step(
        &self,
        _state: &WpdaState,
        _gss: &WpdaGss<LexicographicWeight>,
        _frontier_top: Option<&WpdaGssNode>,
        _pos: usize,
        _tokens: &dyn WpdaTokenSource,
        _frame_ctx: crate::wpda_runtime::FrameCtx,
    ) -> WpdaStepAction<LexicographicWeight> {
        WpdaStepAction::Idle
    }

    fn action_for(&self, category: u16, rule: u16) -> Option<&ActionEntry> {
        match (category, rule) {
            (0, 0) => Some(&BASE_ACTION),
            (0, 1) => Some(&WRAP_ACTION),
            (1, 0) => Some(&COERCION_ACTION),
            _ => None,
        }
    }

    fn cat_of_type_name(&self, name: &str) -> Option<u16> {
        if name.ends_with("ChainValue") {
            Some(0)
        } else if name.ends_with("CoercedValue") {
            Some(1)
        } else {
            None
        }
    }

    fn single_hop_coercion(&self, from: u16, to: u16) -> &[(u16, u16)] {
        if (from, to) == (0, 1) {
            &ZERO_TO_ONE
        } else {
            &[]
        }
    }
}

type Walker = WpdaWalker<LexicographicWeight, WitnessEngine>;

fn rule(category: u16, local_rule: u16) -> u32 {
    ((category as u32) << 16) | local_rule as u32
}

fn install_chain(walker: &mut Walker, depth: usize) -> crate::sppf::SppfId {
    let mut symbol = walker.sppf.intern_symbol(0, 0, 0);
    let base = walker
        .sppf
        .intern_packing(rule(0, 0), Vec::new(), LexicographicWeight::one_ref());
    walker.sppf.link_packing_to_symbol(symbol, base);
    for level in 1..=depth {
        let parent = walker.sppf.intern_symbol(0, 0, level as u32);
        let packing =
            walker
                .sppf
                .intern_packing(rule(0, 1), vec![symbol], LexicographicWeight::one_ref());
        walker.sppf.link_packing_to_symbol(parent, packing);
        symbol = parent;
    }
    symbol
}

fn recursive_arg(
    walker: &Walker,
    sid: crate::sppf::SppfId,
    visiting: &mut rustc_hash::FxHashSet<crate::sppf::SppfId>,
) -> Option<ActionArg> {
    match walker.sppf.node(sid)? {
        crate::sppf::SppfNode::Symbol { non_terminal_tag, .. } => {
            if let Some(term) = walker.sppf_symbol_terms.get(&sid) {
                if !term
                    .output_cat
                    .is_some_and(|category| category as u32 != *non_terminal_tag)
                {
                    return Some(ActionArg::Term {
                        value: Arc::clone(&term.value),
                        type_name: "RecursiveMemo",
                    });
                }
            }
            let term = recursive_symbol(walker, sid, visiting)?;
            if term
                .output_cat
                .is_some_and(|category| category as u32 != *non_terminal_tag)
            {
                None
            } else {
                Some(ActionArg::Term {
                    value: term.value,
                    type_name: "RecursiveWitness",
                })
            }
        },
        crate::sppf::SppfNode::Packing { rule_idx, children, .. }
            if *rule_idx == Walker::OPTIONAL_PRESENT_RULE_IDX =>
        {
            let args = children
                .iter()
                .map(|&child| recursive_arg(walker, child, visiting))
                .collect::<Option<Vec<_>>>()?;
            Some(ActionArg::Optional(Some(args)))
        },
        crate::sppf::SppfNode::OptAbsent { .. } => Some(ActionArg::Optional(None)),
        crate::sppf::SppfNode::CollectionId { id, .. } => Some(ActionArg::CollectionId(*id as u8)),
        _ => None,
    }
}

fn recursive_symbol(
    walker: &Walker,
    symbol: crate::sppf::SppfId,
    visiting: &mut rustc_hash::FxHashSet<crate::sppf::SppfId>,
) -> Option<SppfSymbolTerm> {
    let (tag, lo, hi) = match walker.sppf.node(symbol)? {
        crate::sppf::SppfNode::Symbol { non_terminal_tag, lo_pos, hi_pos, .. } => {
            (*non_terminal_tag, *lo_pos, *hi_pos)
        },
        _ => return None,
    };
    if !visiting.insert(symbol) {
        return None;
    }
    let mut found = None;
    for &packing in walker.sppf.packings_of(symbol) {
        if let Some(crate::sppf::SppfNode::Packing { rule_idx, children, .. }) =
            walker.sppf.node(packing)
        {
            if !walker.packing_satisfies_min_terminal_span(*rule_idx, children, lo, hi) {
                continue;
            }
        }
        let Some(term) = recursive_packing(walker, packing, visiting) else {
            continue;
        };
        if term
            .output_cat
            .is_some_and(|category| category as u32 != tag)
        {
            continue;
        }
        found = Some(term);
        break;
    }
    visiting.remove(&symbol);
    found
}

fn recursive_packing(
    walker: &Walker,
    packing: crate::sppf::SppfId,
    visiting: &mut rustc_hash::FxHashSet<crate::sppf::SppfId>,
) -> Option<SppfSymbolTerm> {
    let (rule_idx, children) = match walker.sppf.node(packing)? {
        crate::sppf::SppfNode::Packing { rule_idx, children, .. } => (*rule_idx, children.clone()),
        _ => return None,
    };
    if rule_idx == Walker::OPTIONAL_PRESENT_RULE_IDX {
        return None;
    }
    let category = (rule_idx >> 16) as u16;
    let local_rule = rule_idx as u16;
    let entry = walker.engine.action_for(category, local_rule)?;
    let action_children: Vec<_> = children
        .into_iter()
        .filter(|&child| {
            !matches!(walker.sppf.node(child), Some(crate::sppf::SppfNode::TriggerTerminal { .. }))
        })
        .collect();
    if action_children.len() != entry.arity as usize
        || entry.expected_input_cats.len() != entry.arity as usize
    {
        return None;
    }
    for (&child, &expected) in action_children.iter().zip(entry.expected_input_cats) {
        if expected != crate::wpda_runtime::ANY_CAT
            && !matches!(
                walker.sppf.node(child),
                Some(crate::sppf::SppfNode::Symbol { non_terminal_tag, .. })
                    if *non_terminal_tag == expected as u32
            )
        {
            return None;
        }
    }
    let args = action_children
        .iter()
        .map(|&child| recursive_arg(walker, child, visiting))
        .collect::<Option<Vec<_>>>()?;
    let mut builder = SemanticBuilder::new();
    for arg in &args {
        match arg {
            ActionArg::Term { value, .. } => builder.push_term_arc(Arc::clone(value)),
            ActionArg::Optional(_) => builder.push_raw_arg(arg.clone()),
            _ => return None,
        }
    }
    let pre_len = builder.len();
    let popped = builder.pop_args(entry.arity as usize);
    (entry.action_fn)(&mut builder, popped);
    if builder.len()
        != pre_len
            .saturating_sub(entry.arity as usize)
            .saturating_add(1)
    {
        return None;
    }
    let output_cat = builder
        .top_term_type_name()
        .and_then(|name| walker.engine.cat_of_type_name(name));
    let value = builder.take_dyn_result()?;
    Some(SppfSymbolTerm { value, output_cat })
}

fn arg_chain_value(arg: ActionArg) -> Option<usize> {
    match &arg {
        ActionArg::Term { value, .. } => value.downcast_ref::<ChainValue>().map(|value| value.0),
        _ => None,
    }
}

#[test]
fn witness_pda_matches_recursive_oracle_for_nested_and_fallback_packings() {
    let mut actual = Walker::new(WitnessEngine, 0);
    let mut expected = Walker::new(WitnessEngine, 0);
    let actual_root = install_chain(&mut actual, 32);
    let expected_root = install_chain(&mut expected, 32);

    // A cycle is linked first; both machines must reject it by the visiting
    // witness and continue to the already-installed acyclic packing.
    let actual_packings = actual.sppf.packings_of(actual_root).to_vec();
    let expected_packings = expected.sppf.packings_of(expected_root).to_vec();
    let actual_fallback = actual_packings[0];
    let expected_fallback = expected_packings[0];
    let actual_symbol = actual.sppf.intern_symbol(0, 1, 34);
    let expected_symbol = expected.sppf.intern_symbol(0, 1, 34);
    let actual_cycle =
        actual
            .sppf
            .intern_packing(rule(0, 1), vec![actual_symbol], LexicographicWeight::one_ref());
    let expected_cycle = expected.sppf.intern_packing(
        rule(0, 1),
        vec![expected_symbol],
        LexicographicWeight::one_ref(),
    );
    actual
        .sppf
        .link_packing_to_symbol(actual_symbol, actual_cycle);
    actual
        .sppf
        .link_packing_to_symbol(actual_symbol, actual_fallback);
    expected
        .sppf
        .link_packing_to_symbol(expected_symbol, expected_cycle);
    expected
        .sppf
        .link_packing_to_symbol(expected_symbol, expected_fallback);

    let actual_cursor = actual.make_probe_cursor();
    let actual_value = arg_chain_value(
        actual
            .reconstruct_action_arg(&actual_cursor, actual_symbol)
            .expect("iterative witness exists"),
    );
    let expected_value = arg_chain_value(
        recursive_arg(&expected, expected_symbol, &mut rustc_hash::FxHashSet::default())
            .expect("recursive witness exists"),
    );
    assert_eq!(actual_value, expected_value);

    let optional = actual.sppf.intern_packing(
        Walker::OPTIONAL_PRESENT_RULE_IDX,
        vec![actual_root],
        LexicographicWeight::one_ref(),
    );
    let actual_optional = actual.reconstruct_action_arg(&actual_cursor, optional);
    assert!(matches!(
        actual_optional.as_ref(),
        Some(ActionArg::Optional(Some(args))) if args.len() == 1
    ));
}

#[test]
fn witness_and_coercion_pdas_handle_depth_20k_on_a_256k_stack() {
    std::thread::Builder::new()
        .name("prattail-wpda-witness-small-stack".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            const DEPTH: usize = 20_000;
            let mut walker = Walker::new(WitnessEngine, 0);
            let root = install_chain(&mut walker, DEPTH);
            let cursor = walker.make_probe_cursor();
            assert_eq!(
                arg_chain_value(
                    walker
                        .reconstruct_action_arg(&cursor, root)
                        .expect("deep witness exists")
                ),
                Some(DEPTH + 1)
            );

            let body = walker.sppf.intern_symbol(0, 7, 8);
            walker.sppf_symbol_terms.insert(
                body,
                SppfSymbolTerm {
                    value: Arc::new(ChainValue(9)),
                    output_cat: Some(0),
                },
            );
            let wrapped = walker
                .intern_coercion_over_body(body, 1, 0)
                .expect("declared coercion is interned without mutual recursion");
            assert!(matches!(
                walker.sppf.node(wrapped),
                Some(crate::sppf::SppfNode::Symbol { non_terminal_tag: 1, .. })
            ));
            assert_eq!(
                walker.sppf_symbol_terms[&wrapped]
                    .value
                    .downcast_ref::<CoercedValue>()
                    .map(|value| value.0),
                Some(9)
            );
        })
        .expect("small-stack thread starts")
        .join()
        .expect("WPDA witness/coercion PDAs do not overflow a 256 KiB stack");
}
