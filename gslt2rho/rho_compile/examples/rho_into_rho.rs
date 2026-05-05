//! Example: the rho calculus compiled into itself.
//!
//! This is the GSLT of §6.2 of the accompanying paper:
//!
//! ```text
//!   (Comm):  par(in(x, y, P), out(x, Q)) ~> subst(P, y, quote(Q))
//!   (Par_L): S ~> T => par(S, Q) ~> par(T, Q)
//!   (Par_R): S ~> T => par(P, S) ~> par(P, T)
//! ```
//!
//! Run with:
//!
//! ```text
//! cargo run --example rho_into_rho
//! ```

use rho_compile::{compile, gslt::*, rho::Name};

fn main() {
    let signature = vec![
        Constructor { name: "par".into(), arity: 2 },
        Constructor { name: "in".into(), arity: 3 },
        Constructor { name: "out".into(), arity: 2 },
        Constructor { name: "drop".into(), arity: 1 },
        Constructor { name: "nil".into(), arity: 0 },
        Constructor { name: "quote".into(), arity: 1 },
        Constructor { name: "subst".into(), arity: 3 },
    ];

    // (Comm) LHS: par(in(x, y, P), out(x, Q))
    // The non-linearity (x = x') is recorded via shared variable name `x`;
    // a downstream consistency receive (per §5 of the paper) will check
    // it. For this example we focus on the channel structure.
    let comm_lhs = Pattern::cons(
        "par",
        vec![
            Pattern::cons("in", vec![
                Pattern::var("x"),
                Pattern::var("y"),
                Pattern::var("P"),
            ]),
            Pattern::cons("out", vec![
                Pattern::var("x"),
                Pattern::var("Q"),
            ]),
        ],
    );
    let comm_rhs = Pattern::cons(
        "subst",
        vec![
            Pattern::var("P"),
            Pattern::var("y"),
            Pattern::cons("quote", vec![Pattern::var("Q")]),
        ],
    );

    let par_l_lhs = Pattern::cons(
        "par",
        vec![Pattern::var("S"), Pattern::var("Q")],
    );
    let par_l_rhs = Pattern::cons(
        "par",
        vec![Pattern::var("T"), Pattern::var("Q")],
    );

    let par_r_lhs = Pattern::cons(
        "par",
        vec![Pattern::var("P"), Pattern::var("S")],
    );
    let par_r_rhs = Pattern::cons(
        "par",
        vec![Pattern::var("P"), Pattern::var("T")],
    );

    let gslt = Gslt {
        signature,
        rewrites: vec![
            Rewrite::Direct {
                lhs: comm_lhs,
                rhs: comm_rhs,
            },
            Rewrite::Contextual {
                premises: vec![Premise {
                    var_in: "S".into(),
                    var_out: "T".into(),
                }],
                outer_lhs: par_l_lhs,
                outer_rhs: par_l_rhs,
            },
            Rewrite::Contextual {
                premises: vec![Premise {
                    var_in: "S".into(),
                    var_out: "T".into(),
                }],
                outer_lhs: par_r_lhs,
                outer_rhs: par_r_rhs,
            },
        ],
    };

    let c = compile(&gslt);

    println!("=== rho calculus compiled into rho ===");
    println!();
    println!("Set automaton: {} states", c.automaton.states.len());
    println!();

    for (i, r) in c.processes.iter().enumerate() {
        let kind = match &gslt.rewrites[i] {
            Rewrite::Direct { .. } => "direct",
            Rewrite::Contextual { .. } => "contextual",
        };
        println!("Rule {} ({} - '{}')", i, kind, r.label);
        match &r.channel {
            Name::Var(v) => println!("  channel: var '{}'", v),
            Name::Quote(_) => println!("  channel: tc(K) computed by set automaton"),
        }
        println!("  process:");
        println!("    {}", r.process);
        println!();
    }

    // Demonstrate optimality (O1)+(O3): the par symbol is consumed once
    // per Comm step; par(_,Q) and par(_,Q') with the second-arg-as-hole
    // share a channel.
    println!("=== Optimality benefits ===");
    println!();
    println!("  (O1) Each `par` consumed by exactly one for-receive.");
    println!("  (O3) Channels for Par_L and Par_R differ:");
    println!("       Par_L channel: {}", c.processes[1].channel);
    println!("       Par_R channel: {}", c.processes[2].channel);
    println!(
        "       distinct: {}",
        c.processes[1].channel != c.processes[2].channel
    );
    println!();
    println!("  This is correct: positions 1 and 2 of `par` are R_dep-independent,");
    println!("  so the automaton dispatches them to separate sub-channels");
    println!("  --- enabling concurrent firing of Par_L and Par_R.");
}
