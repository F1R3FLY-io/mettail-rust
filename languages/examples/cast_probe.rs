//! Stable cast-dispatch probe used by the parser formal-verification ledgers.
//!
//! Usage:
//! - `cast_probe` parses every case once.
//! - `cast_probe <idx>` parses one case and prints a single CSV row.
//!
//! The corpus intentionally stays small: it is a correctness/regression probe,
//! not the timing panel. Use `cast_tower_bench` for repeated measurements.

use mettail_languages::calculator::{Bool, Float, Int};

enum Shape {
    Int,
    Float,
    Bool,
}

struct Case {
    input: &'static str,
    shape: Shape,
}

fn cases() -> Vec<Case> {
    vec![
        Case { input: "int(3) == 3", shape: Shape::Bool },
        Case { input: "int(3) + 3", shape: Shape::Int },
        Case { input: "int(3)", shape: Shape::Int },
        Case {
            input: "int(float(int(3.14)))",
            shape: Shape::Int,
        },
        Case {
            input: "int(float(int(3.14))) == 3",
            shape: Shape::Bool,
        },
        Case {
            input: "int(float(int(float(int(3.14)))))",
            shape: Shape::Int,
        },
        Case {
            input: "int(float(int(float(int(3.14))))) == 3",
            shape: Shape::Bool,
        },
        Case {
            input: "int(1) == 1 and int(2) == 2",
            shape: Shape::Bool,
        },
        Case {
            input: "float(3) >= 3.0",
            shape: Shape::Bool,
        },
        Case { input: "-3!", shape: Shape::Int },
        Case {
            input: "float(float(3))",
            shape: Shape::Float,
        },
        Case { input: "int(int(3))", shape: Shape::Int },
        Case {
            input: "float(int(3.14))",
            shape: Shape::Float,
        },
    ]
}

fn shape_name(shape: &Shape) -> &'static str {
    match shape {
        Shape::Int => "Int",
        Shape::Float => "Float",
        Shape::Bool => "Bool",
    }
}

fn parse_case(case: &Case) -> Result<usize, String> {
    mettail_runtime::clear_var_cache();
    match case.shape {
        Shape::Int => Int::parse_via_wpda_all(case.input)
            .map(|alts| alts.len())
            .map_err(|err| err.to_string()),
        Shape::Float => Float::parse_via_wpda_all(case.input)
            .map(|alts| alts.len())
            .map_err(|err| err.to_string()),
        Shape::Bool => Bool::parse_via_wpda_all(case.input)
            .map(|alts| alts.len())
            .map_err(|err| err.to_string()),
    }
}

fn run_one(idx: usize, case: &Case) -> Result<(), String> {
    let alternatives = parse_case(case)?;
    println!("{},{},{},{}", idx, shape_name(&case.shape), alternatives, case.input);
    Ok(())
}

fn main() {
    let cases = cases();
    let args: Vec<String> = std::env::args().collect();

    let result = if let Some(raw_idx) = args.get(1) {
        match raw_idx.parse::<usize>() {
            Ok(idx) => match cases.get(idx) {
                Some(case) => run_one(idx, case),
                None => Err(format!("case index {} out of range 0..{}", idx, cases.len())),
            },
            Err(err) => Err(format!("invalid case index {:?}: {}", raw_idx, err)),
        }
    } else {
        cases
            .iter()
            .enumerate()
            .try_for_each(|(idx, case)| run_one(idx, case))
    };

    if let Err(err) = result {
        eprintln!("cast_probe failed: {}", err);
        std::process::exit(1);
    }
}
