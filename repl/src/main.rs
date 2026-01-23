use anyhow::Result;
use clap::Parser;
use mettail_repl::{build_registry, Repl};

/// MeTTaIL Term Explorer - Interactive REPL for exploring rewrite systems
#[derive(Parser, Debug)]
#[command(name = "mettail")]
#[command(about = "Interactive term exploration for programming languages", long_about = None)]
struct Args {
    /// Language to load on startup
    #[arg(value_name = "LANGUAGE")]
    language: Option<String>,
}

fn main() -> Result<()> {
    let args = Args::parse();

    // Build the language registry
    let registry = build_registry().unwrap_or_else(|e| {
        eprintln!("Warning: {}", e);
        eprintln!("Continuing with empty registry...");
        mettail_repl::LanguageRegistry::new()
    });

    // Create and run the REPL
    let mut repl = Repl::new(registry)?;

    // If a language was specified, load it on startup
    if let Some(language_name) = args.language {
        repl.load_language(&language_name)?;
    }

    repl.run()?;

    Ok(())
}
