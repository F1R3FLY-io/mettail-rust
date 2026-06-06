//! Per-language simulation CLI binary generation.
//!
//! Generates `languages/src/bin/simulate_{lang_lower}.rs` for each language
//! defined via the `language!` macro. Each binary provides a CLI interface
//! for running simulation campaigns with configurable parameters.
//!
//! ## Generated Binary Features
//!
//! - Clap-based CLI argument parsing
//! - Configurable: `--steps`, `--cases`, `--seed`, `--ltl`, `--invariant`, `-o`, `--coverage`, `--morphology`, `--verbose`
//! - Loads regression seeds from `simulate_{lang_lower}.regressions` on startup
//! - Saves new failing seeds to the regression file
//! - Prints summary to stdout

use mettail_ast::language::LanguageDef;
use std::path::{Path, PathBuf};

/// Write content to a file only if it differs from what is already on disk.
///
/// Skipping the write when content is unchanged prevents cargo from seeing a
/// newer mtime on generated files and triggering spurious recompilation of the
/// entire `mettail-languages` crate on every build.
///
/// Returns `true` if the file was written, `false` if it was unchanged.
fn write_if_changed(path: &Path, content: &str) -> std::io::Result<bool> {
    if let Ok(existing) = std::fs::read_to_string(path) {
        if existing == content {
            return Ok(false);
        }
    }
    std::fs::write(path, content)?;
    Ok(true)
}

/// Write a simulation CLI binary source file for the given language.
///
/// The binary is written to `languages/src/bin/simulate_{lang_lower}.rs`.
/// It uses `clap` for argument parsing and `mettail-simulation` for execution.
pub fn write_simulation_binary(language: &LanguageDef) {
    let lang_name = language.name.to_string();
    let lang_lower = lang_name.to_lowercase();
    let content = generate_simulation_binary(language);

    match write_binary_to_disk(&lang_lower, &content) {
        Ok((path, true)) => {
            eprintln!("  ({}) Generated simulation binary: {}", lang_name, path.display());
        },
        Ok((_, false)) => {
            // Content unchanged — skip write, no message (avoids mtime update)
        },
        Err(e) => {
            eprintln!("Warning: Failed to write simulation binary for {}: {}", lang_name, e);
        },
    }
}

/// Generate the full source code for a per-language simulation binary.
fn generate_simulation_binary(language: &LanguageDef) -> String {
    let lang_name = language.name.to_string();
    let lang_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    // Determine the primary category (first type in the language definition).
    let primary_cat = language
        .types
        .first()
        .map(|t| t.name.to_string())
        .unwrap_or_else(|| "Term".to_string());
    let primary_cat_lower = primary_cat.to_lowercase();

    let mut out = String::with_capacity(8192);

    // Header
    out.push_str(&format!(
        "// AUTO-GENERATED simulation binary for {} — do not edit\n",
        lang_name
    ));
    out.push_str("// Regenerated on each compilation of the language definition.\n");
    out.push_str(&format!(
        "// Run with: cargo run --bin simulate_{} -- [OPTIONS]\n\n",
        lang_lower
    ));

    // Imports
    out.push_str("use clap::Parser;\n");
    out.push_str("use mettail_simulation::runner::{\n");
    out.push_str("    SimulationConfig, SimulationRunner, TraceOutputFormat,\n");
    out.push_str("};\n");
    out.push_str("use mettail_simulation::invariant::{\n");
    out.push_str("    AlwaysParseable, BoundedDepth, BoundedSize, NormalFormReachable,\n");
    out.push_str("};\n");
    out.push_str(&format!("use mettail_languages::{}::{};\n", lang_lower, lang_struct));
    out.push_str(&format!(
        "use mettail_languages::{}::strategies::arb_{};\n",
        lang_lower, primary_cat_lower
    ));
    out.push_str("use mettail_runtime::Language;\n");
    out.push_str("use proptest::strategy::Strategy;\n");
    out.push_str("use std::path::PathBuf;\n\n");

    // CLI struct
    out.push_str(&format!(
        r#"#[derive(Parser)]
#[command(name = "simulate_{lang_lower}")]
#[command(about = "Simulation runner for the {lang_name} language")]
struct Args {{
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
}}

"#,
        lang_lower = lang_lower,
        lang_name = lang_name,
    ));

    // Main function
    out.push_str(&format!(
        r#"fn main() {{
    let args = Args::parse();

    let regression_path = PathBuf::from("simulate_{lang_lower}.regressions");

    // Parse seed if provided.
    let seed: Option<[u8; 32]> = args.seed.as_ref().map(|s| {{
        if s.len() != 64 {{
            eprintln!("Error: seed must be a 64-character hex string");
            std::process::exit(1);
        }}
        let mut seed = [0u8; 32];
        for (i, chunk) in s.as_bytes().chunks(2).enumerate() {{
            let high = match chunk[0] {{
                b'0'..=b'9' => chunk[0] - b'0',
                b'a'..=b'f' => chunk[0] - b'a' + 10,
                b'A'..=b'F' => chunk[0] - b'A' + 10,
                _ => {{ eprintln!("Error: invalid hex character in seed"); std::process::exit(1); }}
            }};
            let low = match chunk[1] {{
                b'0'..=b'9' => chunk[1] - b'0',
                b'a'..=b'f' => chunk[1] - b'a' + 10,
                b'A'..=b'F' => chunk[1] - b'A' + 10,
                _ => {{ eprintln!("Error: invalid hex character in seed"); std::process::exit(1); }}
            }};
            seed[i] = (high << 4) | low;
        }}
        seed
    }});

    // Build invariants from CLI flags.
    let mut invariants: Vec<Box<dyn mettail_simulation::invariant::Invariant>> = Vec::new();
    for name in &args.invariant {{
        match name.as_str() {{
            "BoundedSize" => invariants.push(Box::new(BoundedSize {{ max_nodes: 10000 }})),
            "BoundedDepth" => invariants.push(Box::new(BoundedDepth {{ max_depth: 100 }})),
            "AlwaysParseable" => invariants.push(Box::new(AlwaysParseable)),
            "NormalFormReachable" => invariants.push(Box::new(NormalFormReachable {{ max_steps: args.steps }})),
            other => {{
                eprintln!("Warning: unknown invariant '{{}}', skipping", other);
            }}
        }}
    }}

    // Build trace output config.
    let trace_output = match args.output {{
        Some(ref path) => TraceOutputFormat::Jsonl {{ path: PathBuf::from(path) }},
        None => TraceOutputFormat::None,
    }};

    let config = SimulationConfig {{
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
    }};

    let lang = {lang_struct};
    let lang_ref: &dyn Language = &lang;
    let mut runner = SimulationRunner::new(lang_ref, config);

    // Build the input strategy: generate random terms and display them as strings.
    let strategy = arb_{primary_cat_lower}(3).prop_map(|term| format!("{{}}", term));

    if args.verbose {{
        eprintln!("Running simulation for {lang_name}:");
        eprintln!("  steps={{}}, cases={{}}", args.steps, args.cases);
        if let Some(ref s) = args.seed {{
            eprintln!("  seed={{}}", s);
        }}
        eprintln!("  regression_file={{}}", regression_path.display());
    }}

    let results = runner.run_campaign(strategy);

    // Print summary to stdout.
    println!("=== {lang_name} Simulation Results ===");
    println!("{{}}", results);

    if args.coverage {{
        println!();
        println!("Rule Coverage: {{}}", results.coverage);
    }}

    if args.morphology {{
        if let Some(ref morph) = results.aggregate_morphology {{
            println!();
            println!("Morphology Summary:");
            println!("  Steps: {{}}", morph.total_steps);
            println!("  Nodes: min={{}}, max={{}}, mean={{:.1}}", morph.min_nodes, morph.max_nodes, morph.mean_nodes);
            println!("  Depth: min={{}}, max={{}}, mean={{:.1}}", morph.min_depth, morph.max_depth, morph.mean_depth);
            println!("  Distinct shapes: {{}}", morph.distinct_shapes);
            if !morph.alerts.is_empty() {{
                println!("  Alerts:");
                for alert in &morph.alerts {{
                    println!("    [step {{}}] {{}}", alert.step, alert.message);
                }}
            }}
        }}
    }}

    if !results.failures.is_empty() {{
        eprintln!();
        eprintln!("FAILURES: {{}} / {{}}", results.failed, results.total_cases);
        for (i, failure) in results.failures.iter().enumerate() {{
            eprintln!("  [{{}}] input={{:?}}", i, failure.input);
            eprintln!("       error={{}}", failure.error);
        }}
        std::process::exit(1);
    }} else {{
        println!();
        println!("All {{}} cases passed.", results.total_cases);
    }}
}}
"#,
        lang_lower = lang_lower,
        lang_name = lang_name,
        lang_struct = lang_struct,
        primary_cat_lower = primary_cat_lower,
    ));

    out
}

/// Write the simulation binary source file to disk.
///
/// Returns `(path, written)` where `written` is `true` if the file was actually
/// changed on disk, `false` if the content was already up-to-date.
fn write_binary_to_disk(lang_lower: &str, content: &str) -> std::io::Result<(PathBuf, bool)> {
    let filename = format!("simulate_{}.rs", lang_lower);

    // CARGO_MANIFEST_DIR points to macros/ — go up to workspace root.
    let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());

    let mut path = PathBuf::from(manifest_dir);
    path.pop(); // Go up from macros/ to workspace root
    path.push("languages");
    path.push("src");
    path.push("bin");

    // Create directory if it doesn't exist.
    std::fs::create_dir_all(&path)?;

    path.push(filename);
    let written = write_if_changed(&path, content)?;
    Ok((path, written))
}
