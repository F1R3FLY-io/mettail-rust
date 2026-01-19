// RhoCalc demonstration - uses theory from mettail-theories library
//
// This example shows how to use a theory defined in the theories crate
// to parse terms and run Ascent rewrite rules.

use ascent::*;
use ascent_byods_rels::*;
use mettail_theories::rhocalc::*;
use std::time::Instant;

fn main() {
    println!("=== RhoCalc Rewrite Demo ===\n");

    let start_time = Instant::now();

    // Example 1: Basic communication
    println!("Example 1: Communication");
    let input1 = "for(a->x){*x}|a!(0)";
    // demonstrate_rewrite(input1);

    // Example 2: Drop with quote
    println!("\nExample 2: Drop/Quote");
    let input2 = "*@(0)";
    // demonstrate_rewrite(input2);

    // Example 3: Nested parallel
    println!("\nExample 3: Nested Parallel");
    let input3 = "{for(a->x){*x}|{a!(0)|0}}";
    // demonstrate_rewrite(input3);

    let elapsed = Instant::now().duration_since(start_time);
    println!("\n✅ Total time: {:?}", elapsed);
}

// fn demonstrate_rewrite(input: &str) {
//     println!("  Input:  {}", input);

//     // Parse the term
//     mettail_runtime::clear_var_cache();
//     let parser = rhocalc::ProcParser::new();
//     let term = parser.parse(input).unwrap_or_else(|e| {
//         eprintln!("  Parse error: {:?}", e);
//         std::process::exit(1);
//     });

//     // Run Ascent
//     let prog = ascent_run! {
//         include_source!(mettail_theories::rhocalc::rhocalc_source);
//         proc(term.clone());
//     };

//     // Show results
//     let procs: Vec<_> = prog.proc.iter().map(|(p,)| p).collect();
//     let rewrites: Vec<_> = prog.rw_proc.iter().collect();

//     println!("  Terms reachable: {}", procs.len());

//     // Find normal forms (terms with no outgoing rewrites)
//     let normal_forms: Vec<_> = procs
//         .iter()
//         .filter(|p| !rewrites.iter().any(|(from, _)| from == **p))
//         .collect();

//     if normal_forms.is_empty() {
//         println!("  No normal form found");
//     } else {
//         println!("  Normal forms: {}", normal_forms.len());
//         for nf in normal_forms {
//             println!("    → {}", nf);
//         }
//     }
// }
