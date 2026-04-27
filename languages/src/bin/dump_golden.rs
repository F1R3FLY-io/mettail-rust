//! `dump_golden` — decode and pretty-print a `.golden.bin` postcard file.
//!
//! Stage 8 of W7 plan v5.1. Companion CLI to the parity testing
//! infrastructure at `prattail/src/parity.rs`.
//!
//! ## Usage
//!
//! ```text
//! dump_golden <path-to-golden.bin>
//! ```
//!
//! Reads the file, treats its contents as raw postcard bytes, and prints
//! a hexdump-style summary plus a length report. Full Debug-render of the
//! decoded type requires runtime type information that is not available
//! generically — language-specific dump binaries (e.g.,
//! `dump_calculator_golden`) can be added per language and use the
//! language's AST type for `Deserialize` + Debug-print.
//!
//! For now this binary serves as a smoke-test that goldens can be loaded
//! and that their byte-size is sane.

use std::env;
use std::fs;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <path-to-golden.bin>", args[0]);
        return ExitCode::from(2);
    }
    let path = &args[1];
    let bytes = match fs::read(path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("error: failed to read {}: {}", path, e);
            return ExitCode::from(1);
        }
    };
    println!("file:        {}", path);
    println!("byte length: {}", bytes.len());
    println!("first 64 bytes (hex):");
    let take = bytes.len().min(64);
    for (i, chunk) in bytes[..take].chunks(16).enumerate() {
        let hex: Vec<String> = chunk.iter().map(|b| format!("{:02x}", b)).collect();
        println!("  {:04x}: {}", i * 16, hex.join(" "));
    }
    if bytes.len() > 64 {
        println!("  ... ({} more bytes)", bytes.len() - 64);
    }
    ExitCode::SUCCESS
}
