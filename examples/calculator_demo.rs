use mettail_theories::calculator::*;

fn main() {
    println!("=== Simple arithmetic expressions ===");
    let expr_tests = vec!["3", "3 + 3", "5-2", "1+2-3", "(1+2)-3"];
    let mut env = CalculatorIntEnv::new();

    for t in expr_tests {
        match parse_and_eval_with_env(t, &mut env) {
            Ok(v) => println!("Input: {:<10} Output: {}", t, v),
            Err(e) => println!("Input: {:<10} Error: {}", t, e),
        }
    }

    println!("\n=== Variable assignment and lookup ===");
    let mut env = CalculatorIntEnv::new();

    println!("\nStoring variables:");
    let assignments = vec!["x = 3 + 2", "y = 10 - 1", "myVar = 100"];

    for assignment in assignments {
        match parse_and_eval_with_env(assignment, &mut env) {
            Ok(v) => println!("  {} => {}", assignment, v),
            Err(e) => println!("  {} => Error: {}", assignment, e),
        }
    }

    println!("\nRetrieving variables:");
    let lookups = vec!["x", "y", "myVar"];

    for var in &lookups {
        match parse_and_eval_with_env(var, &mut env) {
            Ok(v) => println!("  {} => {}", var, v),
            Err(e) => println!("  {} => Error: {}", var, e),
        }
    }

    println!("\nExpressions with variables:");
    let expressions = vec!["x + 2", "y - 1", "x + y", "myVar - x - y"];

    for expr in expressions {
        match parse_and_eval_with_env(expr, &mut env) {
            Ok(v) => println!("  {} => {}", expr, v),
            Err(e) => println!("  {} => Error: {}", expr, e),
        }
    }

    println!("\nAssignments with variables in RHS:");
    let var_assignments = vec!["z = x + y", "w = myVar - z"];

    for assignment in var_assignments {
        match parse_and_eval_with_env(assignment, &mut env) {
            Ok(v) => println!("  {} => {}", assignment, v),
            Err(e) => println!("  {} => Error: {}", assignment, e),
        }
    }

    println!("\nFinal variable values:");
    let all_vars = vec!["x", "y", "z", "w", "myVar"];
    for var in &all_vars {
        match parse_and_eval_with_env(var, &mut env) {
            Ok(v) => println!("  {} = {}", var, v),
            Err(e) => println!("  {} => Error: {}", var, e),
        }
    }

    println!("\n=== Multi-base integer literals ===");
    let mut env = CalculatorIntEnv::new();

    let multi_base_tests = vec![
        ("0xFF", 255),        // Hexadecimal
        ("0x4A", 74),         // Hexadecimal lowercase
        ("0o77", 63),         // Octal
        ("0b1111", 15),       // Binary
        ("0x10 + 0o10", 24),  // Hex 16 + Octal 8
        ("0xFF - 0b11", 252), // Hex 255 - Binary 3
    ];

    for (input, expected) in multi_base_tests {
        match parse_and_eval_with_env(input, &mut env) {
            Ok(v) => {
                let status = if v == expected { "OK" } else { "FAIL" };
                println!("  [{}] {} = {} (expected {})", status, input, v, expected);
            },
            Err(e) => println!("  [FAIL] {} => Error: {}", input, e),
        }
    }
}
