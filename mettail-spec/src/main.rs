use std::path::PathBuf;

use clap::Parser;
use mettail_spec::{compile_entry, validate_ntir, SpecError};

#[derive(Parser)]
#[command(
    name = "mettail-spec",
    about = "Compile MeTTaIL .rho module specifications"
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(clap::Subcommand)]
enum Command {
    /// Compile an entry `.rho` file to NTIR
    Compile {
        entry: PathBuf,
        #[arg(long)]
        language: Option<String>,
        #[arg(long, default_value = "debug")]
        emit: EmitFormat,
    },
}

#[derive(Clone, clap::ValueEnum)]
enum EmitFormat {
    Debug,
    Json,
}

fn main() {
    if let Err(e) = run() {
        eprintln!("error: {e}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), SpecError> {
    let cli = Cli::parse();
    match cli.command {
        Command::Compile { entry, language, emit } => {
            let ntir = compile_entry(entry, language.as_deref())?;
            validate_ntir(&ntir)?;
            match emit {
                EmitFormat::Json => {
                    println!(
                        "{}",
                        serde_json::to_string_pretty(&ntir.summary())
                            .map_err(|e| { SpecError::Other(e.to_string()) })?
                    );
                },
                EmitFormat::Debug => {
                    println!("language: {}", ntir.name);
                    println!("hash: {}", ntir.hash);
                    println!("semantics: {:?}", ntir.semantics);
                    println!("types: {}", ntir.types.len());
                    println!("terms: {}", ntir.terms.len());
                    println!("equations: {}", ntir.equations.len());
                    println!("rewrites: {}", ntir.rewrites.len());
                    if let Some(ctx) = &ntir.lowered_context {
                        println!("context:\n{ctx}");
                    }
                },
            }
        },
    }
    Ok(())
}
