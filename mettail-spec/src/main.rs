use std::path::PathBuf;

use clap::Parser;
use mettail_spec::{
    compile_entry, compile_entry_with_spaces, project_rust_file, project_rust_source,
    validate_ntir, SpecError,
};

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
    /// Project a compiled language to Rust `language!` source
    Project {
        entry: PathBuf,
        #[arg(long)]
        language: Option<String>,
        /// Output `.rs` path (default: stdout)
        #[arg(short, long)]
        out: Option<PathBuf>,
    },
}

#[derive(Clone, clap::ValueEnum)]
enum EmitFormat {
    Debug,
    Json,
    Rust,
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
        Command::Compile { entry, language, emit } => match emit {
            EmitFormat::Json => {
                let (ntir, spaces) = compile_entry_with_spaces(entry, language.as_deref())?;
                validate_ntir(&ntir)?;
                #[derive(serde::Serialize)]
                struct Emit<'a> {
                    ntir: mettail_spec::ntir::NtirSummary,
                    spaces: &'a [mettail_spec::ntir::SpaceSummary],
                }
                let payload = Emit { ntir: ntir.summary(), spaces: &spaces };
                println!(
                    "{}",
                    serde_json::to_string_pretty(&payload)
                        .map_err(|e| { SpecError::Other(e.to_string()) })?
                );
            },
            EmitFormat::Rust => {
                let ntir = compile_entry(entry, language.as_deref())?;
                validate_ntir(&ntir)?;
                let src = project_rust_source(&ntir)?;
                print!("{src}");
            },
            EmitFormat::Debug => {
                let ntir = compile_entry(entry, language.as_deref())?;
                validate_ntir(&ntir)?;
                println!("language: {}", ntir.name);
                println!("hash: {}", ntir.hash);
                println!("semantics: {:?}", ntir.semantics);
                println!("types: {}", ntir.types.len());
                println!("terms: {}", ntir.terms.len());
                println!("equations: {}", ntir.equations.len());
                println!("rewrites: {}", ntir.rewrites.len());
                if let Some(ctx) = &ntir.context_template {
                    println!("context_template: insert_here={}", ctx.insert_offset.is_some());
                    println!("context:\n{}", ctx.raw);
                }
            },
        },
        Command::Project { entry, language, out } => match out {
            Some(path) => {
                project_rust_file(entry, language.as_deref(), path)?;
            },
            None => {
                let ntir = compile_entry(entry, language.as_deref())?;
                validate_ntir(&ntir)?;
                print!("{}", project_rust_source(&ntir)?);
            },
        },
    }
    Ok(())
}
