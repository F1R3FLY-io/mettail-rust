//! Per-language simulation CLI binary generation.
//!
//! Generates `target/generated/{lang_lower}/simulate.rs` for each language defined via
//! the `language!` macro. A HAND-WRITTEN host at `languages/src/bin/simulate_{lang}.rs`
//! `include!`s it, which is what makes the target a cargo `[[bin]]`.
//!
//! Before S4 this wrote the binary straight into `languages/src/bin/` as tracked source,
//! at a destination computed from `CARGO_MANIFEST_DIR` regardless of which crate was
//! compiling. Eighteen committed files were rewritten on every build of the workspace.
//! See `macros/tests/generated_output_locality.rs`.
//!
//! ## Generated Binary Features
//!
//! - Clap-based CLI argument parsing
//! - Configurable: `--steps`, `--cases`, `--seed`, `--ltl`, `--invariant`, `-o`, `--coverage`, `--morphology`, `--verbose`
//! - Loads regression seeds from `simulate_{lang_lower}.regressions` on startup
//! - Saves new failing seeds to the regression file
//! - Prints summary to stdout

use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// Spill the simulation CLI body and return the `<lang>_simulation_main!` wrapper.
///
/// The body goes to `target/generated/{lang_lower}/simulate.rs`; the cargo `[[bin]]`
/// target is a hand-written host that invokes the returned wrapper. It uses `clap` for
/// argument parsing and `mettail-simulation` for execution.
///
/// # Why a wrapper and not a bare `include!` in the host
///
/// The host cannot simply `include!` the body, and the reason is a BOOTSTRAP hazard rather
/// than a matter of taste. A test-hosted language's definition lives in
/// `languages/tests/definitions/<lang>.rs`; the only targets that compile it are its host
/// test binary and this CLI. On a clean tree — right after `cargo clean`, or on a fresh
/// checkout — `target/generated/<lang>/simulate.rs` does not exist yet, so whether a bare
/// `include!` resolves would depend on rustc happening to expand the `#[path] mod`
/// (which runs `language!`, which writes the file) before reaching the `include!` later in
/// the same file. That is an ordering coincidence, not a guarantee, and a build that
/// depends on one is precisely the fragility this work exists to remove.
///
/// Emitting the `include!` from INSIDE the macro that wrote the file removes the question:
/// the write and the include belong to the same expansion, in that order, always. It is
/// also the mechanism already proven by `<lang>_generated_tests!`, so the CLI and the test
/// suite now reach their generated bodies the same way.
pub fn write_simulation_binary(language: &LanguageDef) -> TokenStream {
    let lang_name = language.name.to_string();
    let lang_lower = lang_name.to_lowercase();
    let content = super::format_generated_rust_source(&generate_simulation_binary(language));

    let path = match crate::logic::writer::write_lang_module(&lang_name, "simulate", &content) {
        Ok(path) => {
            eprintln!("  ({}) Generated simulation binary: {}", lang_name, path.display());
            path
        },
        Err(e) => {
            eprintln!("Warning: Failed to write simulation binary for {}: {}", lang_name, e);
            return TokenStream::new();
        },
    };

    let primary_cat_lower = primary_category(language).to_lowercase();
    let macro_ident = format_ident!("{}_simulation_main", lang_lower);
    let arb_ident = format_ident!("arb_{}", primary_cat_lower);
    let include = crate::logic::writer::include_stmt(&path);
    // ⚠ Every `\n` here ends in a `\` continuation, and the two invocation forms are a
    // markdown LIST. Both are load-bearing, and for the same reason: a `\n\n` without a
    // continuation leaves this file's own source indentation inside the rendered doc, and
    // markdown reads a blank line followed by a ≥4-space indent as a CODE BLOCK, which
    // rustdoc compiles as Rust. This `format!` did exactly that, and because the macro
    // expands once per language it turned into SIXTEEN doctests of rustc parsing English
    // — invisible to `cargo nextest`, which does not run doctests. Keep prose at the left
    // margin and enumerate with a real list; `dovetail/tests/doc_fence_justification.rs`
    // now fails on any doc comment, hand-written or emitted, that does otherwise.
    let doc = format!(
        "Simulation CLI entry point for `{lang_name}`.\n\n\
         Invoke ONCE, from the crate root of `languages/src/bin/simulate_{lang_lower}.rs`, \
         passing the path of the module the definition lives in:\n\
         - library-hosted language: \
         `{lang_lower}_simulation_main!(mettail_languages::{lang_lower});`\n\
         - test-hosted language, after `#[path] mod {lang_lower};`: \
         `{lang_lower}_simulation_main!(crate::{lang_lower});`\n\n\
         Expands to the `fn main` and clap argument struct; the body itself is included \
         from `target/generated/{lang_lower}/simulate.rs`.",
    );

    quote! {
        #[doc = #doc]
        #[macro_export]
        macro_rules! #macro_ident {
            ($($definition:tt)*) => {
                // The definition's own path is a PARAMETER for the same reason the test
                // wrapper takes one: only the invoking host knows whether the language is
                // a library module or a `#[path]`-included test definition.
                use $($definition)*::*;
                use $($definition)*::strategies::#arb_ident;
                #include
            };
        }
        pub use #macro_ident;
    }
}

/// The language's primary category — the first declared type, which is what the CLI
/// generates terms for.
fn primary_category(language: &LanguageDef) -> String {
    language
        .types
        .first()
        .map(|t| t.name.to_string())
        .unwrap_or_else(|| "Term".to_string())
}

/// Generate the full source code for a per-language simulation binary.
fn generate_simulation_binary(language: &LanguageDef) -> String {
    let lang_name = language.name.to_string();
    let lang_lower = lang_name.to_lowercase();
    let lang_struct = format!("{}Language", lang_name);

    let primary_cat_lower = primary_category(language).to_lowercase();

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
    // The definition's imports are NOT emitted here. `<lang>_simulation_main!` supplies
    // them from the module path its host passes in, which is the only thing that knows
    // whether the language is a library module (`mettail_languages::<lang>`) or a
    // `#[path]`-included test definition (`crate::<lang>`). Emitting a literal path here
    // is what used to make this file host-specific, and it is why the `hosted_in` branch
    // that stood here is gone.
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
