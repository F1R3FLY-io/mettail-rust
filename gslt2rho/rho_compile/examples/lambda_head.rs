//! Example: lambda calculus with weak-head-context reduction.
//!
//! This is the GSLT of §6.1 of the accompanying paper:
//!
//! ```text
//!   (β):    app(lam(M), N) ~> subst(M, N)
//!   (Head): S ~> T => app(S, N) ~> app(T, N)
//! ```
//!
//! Run with:
//!
//! ```text
//! cargo run --example lambda_head
//! ```

use rho_compile::{compile, gslt::*, rho::Name};

fn main() {
    let signature = vec![
        Constructor { name: "app".into(), arity: 2 },
        Constructor { name: "lam".into(), arity: 1 },
        Constructor { name: "subst".into(), arity: 2 },
    ];

    let beta_lhs = Pattern::cons(
        "app",
        vec![
            Pattern::cons("lam", vec![Pattern::var("M")]),
            Pattern::var("N"),
        ],
    );
    let beta_rhs = Pattern::cons(
        "subst",
        vec![Pattern::var("M"), Pattern::var("N")],
    );

    let head_lhs = Pattern::cons(
        "app",
        vec![Pattern::var("S"), Pattern::var("N")],
    );
    let head_rhs = Pattern::cons(
        "app",
        vec![Pattern::var("T"), Pattern::var("N")],
    );

    let gslt = Gslt {
        signature,
        rewrites: vec![
            Rewrite::Direct {
                lhs: beta_lhs,
                rhs: beta_rhs,
            },
            Rewrite::Contextual {
                premises: vec![Premise {
                    var_in: "S".into(),
                    var_out: "T".into(),
                }],
                outer_lhs: head_lhs,
                outer_rhs: head_rhs,
            },
        ],
    };

    let c = compile(&gslt);

    println!("=== Lambda calculus with head-context reduction ===");
    println!();
    println!("Set automaton: {} states", c.automaton.states.len());
    println!();

    for r in &c.processes {
        println!("Rule '{}'", r.label);
        match &r.channel {
            Name::Var(v) => println!("  channel: var '{}' (direct rule)", v),
            Name::Quote(_) => println!("  channel: tc(K) [computed via set automaton]"),
        }
        println!("  process: {}", r.process);
        println!();
    }

    // Demonstrate optimality (O3): equivalent contexts share a channel.
    let alt_head_lhs = Pattern::cons(
        "app",
        vec![Pattern::var("U"), Pattern::var("Q")],
    );
    let alt_head_rhs = Pattern::cons(
        "app",
        vec![Pattern::var("V"), Pattern::var("Q")],
    );
    let g2 = Gslt {
        signature: gslt.signature.clone(),
        rewrites: vec![
            gslt.rewrites[0].clone(),
            Rewrite::Contextual {
                premises: vec![Premise {
                    var_in: "U".into(),
                    var_out: "V".into(),
                }],
                outer_lhs: alt_head_lhs,
                outer_rhs: alt_head_rhs,
            },
        ],
    };
    let c2 = compile(&g2);
    let chan_orig = &c.processes[1].channel;
    let chan_alt = &c2.processes[1].channel;

    println!("=== Optimality (O3): coarsest sound partition ===");
    println!("  app(S, N) channel: {}", chan_orig);
    println!("  app(U, Q) channel: {}", chan_alt);
    println!(
        "  identical: {}",
        chan_orig == chan_alt
    );
}
