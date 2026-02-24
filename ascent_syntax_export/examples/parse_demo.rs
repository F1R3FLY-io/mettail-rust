//! Demo: parse an Ascent program and print a summary.
//!
//! Run with: `cargo run -p ascent_syntax_export --example parse_demo`

use ascent_syntax_export::{extract_relations, extract_rule_heads, parse_ascent_program_text};

const SAMPLE_PROGRAM: &str = r#"
relation edge(i32, i32);
relation path(i32, i32);

path(x, y) <-- edge(x, y);
path(x, z) <-- path(x, y), edge(y, z);
"#;

fn main() {
    println!("Parsing Ascent program:\n---\n{}\n---\n", SAMPLE_PROGRAM.trim());

    match parse_ascent_program_text(SAMPLE_PROGRAM) {
        Ok(program) => {
            let relations = extract_relations(&program);
            let heads = extract_rule_heads(&program);

            println!("Relations ({}):", relations.len());
            for (name, types, is_lattice) in &relations {
                let kind = if *is_lattice { "lattice" } else { "relation" };
                println!("  {} {} ({})", kind, name, types.join(", "));
            }

            println!("\nRules ({}):", program.rules.len());
            for (i, head) in heads.iter().enumerate() {
                println!("  {}  head: {}", i + 1, head);
            }
        },
        Err(e) => {
            eprintln!("Parse error: {}", e);
            std::process::exit(1);
        },
    }
}
