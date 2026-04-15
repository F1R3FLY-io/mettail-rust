// AUTO-GENERATED simulation binary for Lambda — do not edit
// Regenerated on each compilation of the language definition.
// Run with: cargo run --bin simulate_lambda -- [OPTIONS]

use clap::Parser;
use mettail_simulation::runner::{
    SimulationConfig, SimulationRunner, TraceOutputFormat,
};
use mettail_simulation::invariant::{
    AlwaysParseable, BoundedDepth, BoundedSize, NormalFormReachable,
};
use mettail_languages::lambda::LambdaLanguage;
use mettail_languages::lambda::strategies::arb_term;
use mettail_runtime::Language;
use proptest::strategy::Strategy;
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "simulate_lambda")]
#[command(about = "Simulation runner for the Lambda language")]
struct Args {
    /// Maximum number of rewrite steps per term before declaring non-termination.
    #[arg(short, long, default_value = "1000")]
    steps: usize,

    /// Number of random test cases to generate.
    #[arg(short, long, default_value = "10000")]
    cases: u32,

    /// Fixed seed for reproducible runs (64-character hex string).
    #[arg(long)]
    seed: Option<String>,

    /// LTL formula to check (can be specified multiple times).
    #[arg(long)]
    ltl: Vec<String>,

    /// Named invariant to enable: BoundedSize, BoundedDepth, AlwaysParseable, NormalFormReachable.
    #[arg(long)]
    invariant: Vec<String>,

    /// Output path for JSONL trace file.
    #[arg(short, long)]
    output: Option<String>,

    /// Print rule coverage statistics.
    #[arg(long)]
    coverage: bool,

    /// Print morphology statistics.
    #[arg(long)]
    morphology: bool,

    /// Verbose output (print each test case).
    #[arg(short, long)]
    verbose: bool,
}

fn main() {
    let args = Args::parse();

    let regression_path = PathBuf::from("simulate_lambda.regressions");

    // Parse seed if provided.
    let seed: Option<[u8; 32]> = args.seed.as_ref().map(|s| {
        if s.len() != 64 {
            eprintln!("Error: seed must be a 64-character hex string");
            std::process::exit(1);
        }
        let mut seed = [0u8; 32];
        for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
            let high = match chunk[0] {
                b'0'..=b'9' => chunk[0] - b'0',
                b'a'..=b'f' => chunk[0] - b'a' + 10,
                b'A'..=b'F' => chunk[0] - b'A' + 10,
                _ => { eprintln!("Error: invalid hex character in seed"); std::process::exit(1); }
            };
            let low = match chunk[1] {
                b'0'..=b'9' => chunk[1] - b'0',
                b'a'..=b'f' => chunk[1] - b'a' + 10,
                b'A'..=b'F' => chunk[1] - b'A' + 10,
                _ => { eprintln!("Error: invalid hex character in seed"); std::process::exit(1); }
            };
            seed[i] = (high << 4) | low;
        }
        seed
    });

    // Build invariants from CLI flags.
    let mut invariants: Vec<Box<dyn mettail_simulation::invariant::Invariant>> = Vec::new();
    for name in &args.invariant {
        match name.as_str() {
            "BoundedSize" => invariants.push(Box::new(BoundedSize { max_nodes: 10000 })),
            "BoundedDepth" => invariants.push(Box::new(BoundedDepth { max_depth: 100 })),
            "AlwaysParseable" => invariants.push(Box::new(AlwaysParseable)),
            "NormalFormReachable" => invariants.push(Box::new(NormalFormReachable { max_steps: args.steps })),
            other => {
                eprintln!("Warning: unknown invariant '{}', skipping", other);
            }
        }
    }

    // Build trace output config.
    let trace_output = match args.output {
        Some(ref path) => TraceOutputFormat::Jsonl { path: PathBuf::from(path) },
        None => TraceOutputFormat::None,
    };

    let config = SimulationConfig {
        max_steps: args.steps,
        max_term_depth: 50,
        proptest_cases: args.cases,
        seed,
        invariants,
        ltl_properties: args.ltl.clone(),
        track_morphology: args.morphology,
        trace_output,
        regression_path: Some(regression_path.clone()),
        verbose: args.verbose,
    };

    let lang = LambdaLanguage;
    let lang_ref: &dyn Language = &lang;
    let mut runner = SimulationRunner::new(lang_ref, config);

    // Build the input strategy: generate random terms and display them as strings.
    let strategy = arb_term(3).prop_map(|term| format!("{}", term));

    if args.verbose {
        eprintln!("Running simulation for Lambda:");
        eprintln!("  steps={}, cases={}", args.steps, args.cases);
        if let Some(ref s) = args.seed {
            eprintln!("  seed={}", s);
        }
        eprintln!("  regression_file={}", regression_path.display());
    }

    let results = runner.run_campaign(strategy);

    // Print summary to stdout.
    println!("=== Lambda Simulation Results ===");
    println!("{}", results);

    if args.coverage {
        println!();
        println!("Rule Coverage: {}", results.coverage);
    }

    if args.morphology {
        if let Some(ref morph) = results.aggregate_morphology {
            println!();
            println!("Morphology Summary:");
            println!("  Steps: {}", morph.total_steps);
            println!("  Nodes: min={}, max={}, mean={:.1}", morph.min_nodes, morph.max_nodes, morph.mean_nodes);
            println!("  Depth: min={}, max={}, mean={:.1}", morph.min_depth, morph.max_depth, morph.mean_depth);
            println!("  Distinct shapes: {}", morph.distinct_shapes);
            if !morph.alerts.is_empty() {
                println!("  Alerts:");
                for alert in &morph.alerts {
                    println!("    [step {}] {}", alert.step, alert.message);
                }
            }
        }
    }

    if !results.failures.is_empty() {
        eprintln!();
        eprintln!("FAILURES: {} / {}", results.failed, results.total_cases);
        for (i, failure) in results.failures.iter().enumerate() {
            eprintln!("  [{}] input={:?}", i, failure.input);
            eprintln!("       error={}", failure.error);
        }
        std::process::exit(1);
    } else {
        println!();
        println!("All {} cases passed.", results.total_cases);
    }
}
