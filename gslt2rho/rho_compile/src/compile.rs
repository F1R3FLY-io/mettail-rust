//! GSLT-to-rho compiler.
//!
//! Implements the translation scheme of the accompanying paper, with
//! channel names computed by `crate::channel::tc`. Direct rules compile to
//! a single persistent for/send pair; contextual rules compile to the
//! polymorphic `let tc = ⌜T_M(K)⌝` form discussed in §3 of the paper.

use std::collections::BTreeSet;

use crate::automaton::{DependencyKind, SetAutomaton};
use crate::channel::{reflect, suspended_trace};
use crate::gslt::{Gslt, Pattern, Premise, Rewrite};
use crate::rho::{Name, Proc};

/// The output of compilation: a parallel composition of one rho process
/// per rule. Each process is a persistent listener that fires the rule
/// whenever its preconditions are met.
pub struct CompiledGslt {
    pub processes: Vec<CompiledRule>,
    pub automaton: SetAutomaton,
}

/// One compiled rule, with a label suitable for debugging or tracing.
pub struct CompiledRule {
    pub label: String,
    pub channel: Name,
    pub process: Proc,
}

/// Compile a full GSLT specification into a parallel rho process,
/// using the outermost-preserving dependency relation by default.
pub fn compile(gslt: &Gslt) -> CompiledGslt {
    compile_with(gslt, DependencyKind::OutermostPreserving)
}

/// Compile a full GSLT specification, choosing the dependency relation
/// for the underlying set-automaton construction.
pub fn compile_with(gslt: &Gslt, kind: DependencyKind) -> CompiledGslt {
    // 1. Collect all LHS patterns from all rules.
    let lhss: Vec<Pattern> = gslt
        .rewrites
        .iter()
        .flat_map(|r| r.principal_lhs())
        .cloned()
        .collect();

    // 2. Build the signature in the form the automaton expects.
    let signature: Vec<(&str, usize)> = gslt
        .signature
        .iter()
        .map(|c| (c.name.as_str(), c.arity))
        .collect();

    // 3. Construct the set automaton.
    let automaton = SetAutomaton::build(&signature, lhss, kind);

    // 4. Compile each rule individually.
    let processes: Vec<CompiledRule> = gslt
        .rewrites
        .iter()
        .enumerate()
        .map(|(i, r)| compile_rule(i, r, &automaton))
        .collect();

    CompiledGslt {
        processes,
        automaton,
    }
}

/// Compile one rule against the given automaton.
fn compile_rule(rule_index: usize, rule: &Rewrite, aut: &SetAutomaton) -> CompiledRule {
    match rule {
        Rewrite::Direct { lhs, rhs } => compile_direct(rule_index, lhs, rhs),
        Rewrite::Contextual {
            premises,
            outer_lhs,
            outer_rhs,
        } => compile_contextual(rule_index, premises, outer_lhs, outer_rhs, aut),
    }
}

/// Direct rule:
///
/// ```text
/// [| L ~> R |](tl) = for ([|L|] <= tl) { tl!([|R|]) }
/// ```
fn compile_direct(rule_index: usize, lhs: &Pattern, rhs: &Pattern) -> CompiledRule {
    // Translation channel for the rule: a unique name derived from the
    // rule's index. In a fully-elaborated system this would be the
    // automaton's output channel for the principal LHS, but for direct
    // rules we use a single dedicated channel.
    let chan = Name::var(format!("__rule_{}_chan", rule_index));

    // Bind each unique LHS variable in the for-receive, in first-occurrence
    // order. Repeated occurrences (non-linear LHS) are not rebound; per
    // §5 of the paper they are checked by a separate consistency receive,
    // which is not yet emitted by this prototype --- TODO for non-linear
    // support.
    let binders = unique_free_vars(lhs);
    let rhs_proc = pattern_to_proc(rhs);

    let body = Proc::out(chan.clone(), rhs_proc);
    let process = Proc::tuple_input(chan.clone(), binders, body);

    CompiledRule {
        label: format!("rule_{}", rule_index),
        channel: chan,
        process,
    }
}

/// Free variables of a pattern, deduplicated and in first-occurrence order.
fn unique_free_vars(p: &Pattern) -> Vec<String> {
    let mut seen = std::collections::BTreeSet::new();
    let mut out = Vec::new();
    for v in p.free_vars() {
        if seen.insert(v.to_string()) {
            out.push(v.to_string());
        }
    }
    out
}

/// Contextual rule:
///
/// ```text
/// [| S_1 ~> T_1, ..., S_n ~> T_n  =>  K(S_1,...,S_n) ~> K'(T_1,...,T_n) |]
///   = let tc = [| K |] in
///       for ((y_1,...,y_n) <= tc) {
///         tc!( [| K' |]( [| T_1[y_1] |], ..., [| T_n[y_n] |] ) )
///       }
/// ```
fn compile_contextual(
    _rule_index: usize,
    premises: &[Premise],
    outer_lhs: &Pattern,
    outer_rhs: &Pattern,
    aut: &SetAutomaton,
) -> CompiledRule {
    // The hole positions of the outer context are precisely the positions
    // at which a `var_in` of some premise appears in `outer_lhs`.
    let hole_vars: BTreeSet<String> = premises
        .iter()
        .map(|p| p.var_in.clone())
        .collect();

    // Compute tc(K).
    let trace = suspended_trace(aut, outer_lhs, &hole_vars);
    let tc = reflect(&trace);

    // Binders for the for-receive: one per premise's var_out (the result
    // of the inner reduction).
    let binders: Vec<String> = premises.iter().map(|p| p.var_out.clone()).collect();

    // Body: send K'(T_1[y_1], ..., T_n[y_n]) on tc.
    let body = Proc::out(tc.clone(), pattern_to_proc(outer_rhs));

    let process = Proc::tuple_input(tc.clone(), binders, body);

    CompiledRule {
        label: format!("contextual_{}", premises.len()),
        channel: tc,
        process,
    }
}

/// Encode a pattern (used as a term on the right-hand side) as a rho
/// process. Constructors become tagged Sends, variables become Drops of
/// names of the same identifier.
///
/// This is a structural encoding chosen for unambiguity and round-trippability
/// rather than for efficiency: every constructor `f(t1,...,tn)` becomes
/// `f_chan!( <encoded children> )` where `<encoded children>` is a parallel
/// composition. The downstream rho engine can re-parse this into the
/// MeTTaIL term language by inspecting the constructor channels.
fn pattern_to_proc(p: &Pattern) -> Proc {
    match p {
        Pattern::Cons { name, args } => {
            let chan = Name::var(format!("__cons_{}", name));
            let payload = if args.is_empty() {
                Proc::Zero
            } else {
                Proc::par(args.iter().map(pattern_to_proc).collect())
            };
            Proc::out(chan, payload)
        }
        Pattern::Var(v) => Proc::Drop(Name::var(v.clone())),
        Pattern::Wild => Proc::Zero,
        Pattern::Rest(v) => Proc::Drop(Name::var(format!("rest_{}", v))),
    }
}

/// Combine all compiled rules into a single parallel rho process.
pub fn collect_into_par(c: &CompiledGslt) -> Proc {
    Proc::par(c.processes.iter().map(|r| r.process.clone()).collect())
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gslt::{Constructor, Premise};

    fn lambda_signature() -> Vec<Constructor> {
        vec![
            Constructor { name: "app".into(), arity: 2 },
            Constructor { name: "lam".into(), arity: 1 },
        ]
    }

    fn beta_lhs() -> Pattern {
        Pattern::cons(
            "app",
            vec![
                Pattern::cons("lam", vec![Pattern::var("M")]),
                Pattern::var("N"),
            ],
        )
    }

    #[test]
    fn compile_direct_beta_rule() {
        let g = Gslt {
            signature: lambda_signature(),
            rewrites: vec![Rewrite::Direct {
                lhs: beta_lhs(),
                rhs: Pattern::cons("subst", vec![
                    Pattern::var("M"),
                    Pattern::var("N"),
                ]),
            }],
        };
        let c = compile(&g);
        assert_eq!(c.processes.len(), 1);
        let s = format!("{}", c.processes[0].process);
        // It should be a for-receive.
        assert!(s.contains("?"));
    }

    #[test]
    fn compile_contextual_head_rule() {
        let g = Gslt {
            signature: lambda_signature(),
            rewrites: vec![
                Rewrite::Direct {
                    lhs: beta_lhs(),
                    rhs: Pattern::cons("subst", vec![
                        Pattern::var("M"),
                        Pattern::var("N"),
                    ]),
                },
                Rewrite::Contextual {
                    premises: vec![Premise {
                        var_in: "S".into(),
                        var_out: "T".into(),
                    }],
                    outer_lhs: Pattern::cons("app", vec![
                        Pattern::var("S"),
                        Pattern::var("N"),
                    ]),
                    outer_rhs: Pattern::cons("app", vec![
                        Pattern::var("T"),
                        Pattern::var("N"),
                    ]),
                },
            ],
        };
        let c = compile(&g);
        assert_eq!(c.processes.len(), 2);
        // Both rules compile to processes; the contextual one should
        // have a Quote channel (computed by tc), not a Var channel.
        let head = &c.processes[1];
        match &head.channel {
            Name::Quote(_) => {}
            _ => panic!("contextual rule channel must be a quoted process"),
        }
    }

    #[test]
    fn equivalent_contexts_share_channel() {
        // Two contextual rules whose outer contexts the matcher cannot
        // distinguish must compile to the same channel.
        let g = Gslt {
            signature: lambda_signature(),
            rewrites: vec![
                Rewrite::Direct {
                    lhs: beta_lhs(),
                    rhs: Pattern::var("M"),
                },
                Rewrite::Contextual {
                    premises: vec![Premise {
                        var_in: "S".into(),
                        var_out: "T".into(),
                    }],
                    outer_lhs: Pattern::cons("app", vec![
                        Pattern::var("S"),
                        Pattern::var("N"),
                    ]),
                    outer_rhs: Pattern::cons("app", vec![
                        Pattern::var("T"),
                        Pattern::var("N"),
                    ]),
                },
                Rewrite::Contextual {
                    premises: vec![Premise {
                        var_in: "U".into(),
                        var_out: "V".into(),
                    }],
                    outer_lhs: Pattern::cons("app", vec![
                        Pattern::var("U"),
                        Pattern::var("Q"),
                    ]),
                    outer_rhs: Pattern::cons("app", vec![
                        Pattern::var("V"),
                        Pattern::var("Q"),
                    ]),
                },
            ],
        };
        let c = compile(&g);
        let chan_a = &c.processes[1].channel;
        let chan_b = &c.processes[2].channel;
        assert_eq!(chan_a, chan_b,
            "contexts app(S,N) and app(U,Q) should share a channel");
    }
}
