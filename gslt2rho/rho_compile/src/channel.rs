//! Channel naming via partial evaluation of the set automaton.
//!
//! Given a context `K` (a pattern with hole positions), we compute the
//! suspended configuration tree `T_M(K)` by running the set automaton
//! on the surface of `K` until a hole position is reached. The canonical
//! reflection of this tree is the channel `tc(K)`.
//!
//! See `optimal-channels.tex` (the accompanying paper) for the formal
//! development; this module implements Construction 4.4 / Algorithm 1
//! of that paper.

use std::collections::BTreeSet;

use crate::automaton::{Position, SetAutomaton, StateId, position_concat};
use crate::gslt::Pattern;
use crate::rho::{Name, Proc};

/// A configuration tree --- either a bud (unexplored) or a node (explored).
///
/// Buds remain when their inspection position lies in a hole; we serialise
/// them into the channel name.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ConfigTree {
    /// `B(s, p)`: the matcher would inspect at `p · L(s)` next, but that
    /// position is a hole. Suspended.
    Bud {
        state: StateId,
        position: Position,
        kind: BudKind,
    },
    /// `N(s, p, cts)`: explored at this configuration; `cts` are the
    /// successors.
    Node {
        state: StateId,
        position: Position,
        children: Vec<ConfigTree>,
    },
}

/// Why a bud is suspended.
///
/// At the matcher level both `Hole` and `Schema` are equally non-inspected,
/// but they are *operationally* distinct: a `Hole` bud is where an inner
/// reduction's output will arrive; a `Schema` bud is where a free
/// metavariable of the rule sits. Distinguishing them in the reflection
/// keeps the contexts `par(S, Q)` (hole at 1) and `par(P, S)` (hole at 2)
/// at separate channels --- as required for sound dispatch of `Par_L` vs
/// `Par_R`-style rules.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BudKind {
    /// A true hole: a variable in `hole_vars` (the `var_in` of some premise).
    Hole,
    /// A schema variable: any other variable, wildcard, or rest pattern.
    Schema,
}

/// Compute the suspended configuration tree for a context.
///
/// `holes` is the set of positions in `context` at which a hole sits ---
/// i.e. positions whose subterms are determined by the inner premises of a
/// contextual rule, not by the surface of the outer context.
///
/// A `Pattern::Var` whose name appears in `hole_vars` is treated as a hole;
/// `Pattern::Wild` and `Pattern::Rest` are always treated as holes;
/// `Pattern::Var` whose name does not appear in `hole_vars` is also treated
/// as a hole at the matcher level (no LHS ever depends on its content), in
/// keeping with the footnote in §6.1 of the paper.
pub fn suspended_trace(
    automaton: &SetAutomaton,
    context: &Pattern,
    hole_vars: &BTreeSet<String>,
) -> ConfigTree {
    let s0 = automaton.initial_state();
    let mut tree = ConfigTree::Bud {
        state: s0,
        position: Position::new(),
        kind: BudKind::Schema, // placeholder; overwritten if it stays a bud
    };
    grow_until_hole(&mut tree, automaton, context, hole_vars);
    tree
}

/// Repeatedly grow the configuration tree until no growable buds remain.
/// A bud is "growable" iff its inspection position is in the surface of
/// `context` (i.e. has a function symbol there, not a hole).
fn grow_until_hole(
    tree: &mut ConfigTree,
    aut: &SetAutomaton,
    context: &Pattern,
    hole_vars: &BTreeSet<String>,
) {
    loop {
        let mut changed = false;
        grow_step(tree, aut, context, hole_vars, &mut changed);
        if !changed {
            break;
        }
    }
}

fn grow_step(
    tree: &mut ConfigTree,
    aut: &SetAutomaton,
    context: &Pattern,
    hole_vars: &BTreeSet<String>,
    changed: &mut bool,
) {
    match tree {
        ConfigTree::Bud { state, position, kind } => {
            let label = aut.label(*state);
            let inspect_pos = position_concat(position, label);
            // Is `inspect_pos` in the surface of `context`?
            match surface_at(context, &inspect_pos, hole_vars) {
                Some(SurfaceSymbol::Cons(symbol_name, _arity)) => {
                    // Grow this bud.
                    let succs = aut.step(*state, &symbol_name);
                    let children: Vec<ConfigTree> = succs
                        .iter()
                        .map(|(s, p_rel)| ConfigTree::Bud {
                            state: *s,
                            position: position_concat(position, p_rel),
                            kind: BudKind::Schema, // placeholder
                        })
                        .collect();
                    *tree = ConfigTree::Node {
                        state: *state,
                        position: position.clone(),
                        children,
                    };
                    *changed = true;
                }
                Some(SurfaceSymbol::Hole) => {
                    *kind = BudKind::Hole;
                }
                Some(SurfaceSymbol::Schema) | None => {
                    *kind = BudKind::Schema;
                }
            }
        }
        ConfigTree::Node { children, .. } => {
            for c in children.iter_mut() {
                grow_step(c, aut, context, hole_vars, changed);
            }
        }
    }
}

/// What the context has at a given position.
enum SurfaceSymbol {
    /// A constructor with this name and arity.
    Cons(String, usize),
    /// A hole: a variable bound by some premise's `var_in`.
    Hole,
    /// A schema variable: variable not bound by a premise, wildcard, or
    /// rest pattern.
    Schema,
}

fn surface_at(
    context: &Pattern,
    pos: &Position,
    hole_vars: &BTreeSet<String>,
) -> Option<SurfaceSymbol> {
    let mut p: &Pattern = context;
    for &i in pos {
        match p {
            Pattern::Cons { args, .. } => {
                if i == 0 || i > args.len() {
                    return None;
                }
                p = &args[i - 1];
            }
            _ => return None,
        }
    }
    match p {
        Pattern::Cons { name, args } => {
            Some(SurfaceSymbol::Cons(name.clone(), args.len()))
        }
        Pattern::Var(v) => {
            if hole_vars.contains(v) {
                Some(SurfaceSymbol::Hole)
            } else {
                Some(SurfaceSymbol::Schema)
            }
        }
        Pattern::Wild | Pattern::Rest(_) => Some(SurfaceSymbol::Schema),
    }
}

// ---------------------------------------------------------------------------
// Reflection: ConfigTree -> rho calculus name
// ---------------------------------------------------------------------------

/// Reflect a configuration tree into a canonical rho-calculus name.
///
/// The reflection is a `Name::Quote` of a structurally-encoded process
/// uniquely determined by the tree. Two contexts with identical
/// `ConfigTree`s receive the same `Name`; two contexts with different
/// `ConfigTree`s receive different `Name`s. This is the channel-naming
/// function `tc(K)`.
pub fn reflect(tree: &ConfigTree) -> Name {
    Name::Quote(Box::new(encode_tree(tree)))
}

fn encode_tree(tree: &ConfigTree) -> Proc {
    match tree {
        ConfigTree::Bud { state, position, kind } => {
            // Encode as a tagged process with the bud kind in the tag.
            let tag = match kind {
                BudKind::Hole => format!("__hole_s{}", state),
                BudKind::Schema => format!("__schema_s{}", state),
            };
            Proc::Output {
                chan: Name::var(tag),
                msg: Box::new(encode_position(position)),
            }
        }
        ConfigTree::Node {
            state,
            position,
            children,
        } => {
            let mut parts = vec![
                Proc::Output {
                    chan: Name::var(format!("__node_s{}", state)),
                    msg: Box::new(encode_position(position)),
                },
            ];
            for c in children {
                parts.push(encode_tree(c));
            }
            Proc::par(parts)
        }
    }
}

fn encode_position(p: &Position) -> Proc {
    if p.is_empty() {
        Proc::Zero
    } else {
        let mut parts = Vec::new();
        for &i in p {
            parts.push(Proc::Output {
                chan: Name::var(format!("__pos_{}", i)),
                msg: Box::new(Proc::Zero),
            });
        }
        Proc::par(parts)
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
#[allow(non_snake_case)] // K, N as in the paper
mod tests {
    use super::*;
    use crate::automaton::{DependencyKind, SetAutomaton};

    #[test]
    fn lambda_head_context_suspends_at_hole() {
        // GSLT: app(lam(M), N) ~> ...
        let beta_lhs = Pattern::cons(
            "app",
            vec![
                Pattern::cons("lam", vec![Pattern::var("M")]),
                Pattern::var("N"),
            ],
        );
        let aut = SetAutomaton::build(
            &[("app", 2), ("lam", 1)],
            vec![beta_lhs],
            DependencyKind::OutermostPreserving,
        );

        // Context K = app(_, N) for the head reduction rule:
        // S ~> T => app(S, N) ~> app(T, N)
        let k = Pattern::cons(
            "app",
            vec![Pattern::var("S"), Pattern::var("N")],
        );
        let mut holes = BTreeSet::new();
        holes.insert("S".to_string());

        let tree = suspended_trace(&aut, &k, &holes);
        // The trace should be a Node (we read 'app'), with at least one
        // bud child (suspended at the hole).
        match &tree {
            ConfigTree::Node { children, .. } => {
                assert!(!children.is_empty(), "expected child buds");
                let any_bud = children.iter().any(|c| {
                    matches!(c, ConfigTree::Bud { .. })
                });
                assert!(any_bud, "expected at least one suspended bud");
            }
            _ => panic!("expected Node at root after reading 'app'"),
        }
    }

    #[test]
    fn same_K_yields_same_channel_regardless_of_N() {
        let beta_lhs = Pattern::cons(
            "app",
            vec![
                Pattern::cons("lam", vec![Pattern::var("M")]),
                Pattern::var("N"),
            ],
        );
        let aut = SetAutomaton::build(
            &[("app", 2), ("lam", 1)],
            vec![beta_lhs],
            DependencyKind::OutermostPreserving,
        );

        // The two contexts differ only at the hole-2 position (which the
        // automaton never inspects under R_op).
        let k1 = Pattern::cons(
            "app",
            vec![Pattern::var("S"), Pattern::var("N")],
        );
        let k2 = Pattern::cons(
            "app",
            vec![Pattern::var("S"), Pattern::var("Q")],
        );
        let mut holes = BTreeSet::new();
        holes.insert("S".to_string());

        let t1 = suspended_trace(&aut, &k1, &holes);
        let t2 = suspended_trace(&aut, &k2, &holes);
        let n1 = reflect(&t1);
        let n2 = reflect(&t2);
        assert_eq!(n1, n2, "channels must coincide for equivalent contexts");
    }

    #[test]
    fn different_K_yields_different_channel() {
        // app(lam(M), N) -- the LHS itself
        let beta_lhs = Pattern::cons(
            "app",
            vec![
                Pattern::cons("lam", vec![Pattern::var("M")]),
                Pattern::var("N"),
            ],
        );
        let aut = SetAutomaton::build(
            &[("app", 2), ("lam", 1)],
            vec![beta_lhs],
            DependencyKind::OutermostPreserving,
        );

        // K1 = app(_, _); K2 = lam(_)
        let k1 = Pattern::cons("app", vec![Pattern::var("S"), Pattern::var("N")]);
        let k2 = Pattern::cons("lam", vec![Pattern::var("S")]);
        let mut holes = BTreeSet::new();
        holes.insert("S".to_string());
        holes.insert("N".to_string());

        let t1 = suspended_trace(&aut, &k1, &holes);
        let t2 = suspended_trace(&aut, &k2, &holes);
        let n1 = reflect(&t1);
        let n2 = reflect(&t2);
        assert_ne!(n1, n2, "structurally distinct contexts must differ");
    }
}
