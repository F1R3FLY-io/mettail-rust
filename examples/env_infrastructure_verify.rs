use mettail_theories::calculator::*;
/// Comprehensive test verifying environment infrastructure properties:
/// 1. Environment is automatic for all theories
/// 2. Environment does NOT depend on rewrites
/// 3. Uses HashMap<String, #category_name> for storage
use mettail_theories::rhocalc::*;

fn main() {
    println!("===== ENVIRONMENT INFRASTRUCTURE VERIFICATION =====\n");

    // Test 1: RhoCalc (no env_var conditions)
    println!("✓ TEST 1: RhoCalc (No env_var conditions)");
    println!("  - Verifies environment is generated even without rewrites using env_var");
    test_rhocalc_env();
    println!("  PASSED\n");

    // Test 2: Calculator (has env_var conditions but they don't affect env generation)
    println!("✓ TEST 2: Calculator (Has env_var conditions)");
    println!("  - Verifies environment generation is independent of rewrite rules");
    test_calculator_env();
    println!("  PASSED\n");

    // Test 3: Type safety with HashMap<String, Category>
    println!("✓ TEST 3: Type Safety Verification");
    println!("  - Verifies HashMap uses category names directly");
    test_type_safety();
    println!("  PASSED\n");

    println!("===== ALL VERIFICATION TESTS PASSED =====");
}

fn test_rhocalc_env() {
    // RhoCalc has two categories: Proc and Name
    // Environment should be generated for BOTH regardless of rewrites

    let mut proc_env = RhoCalcProcEnv::new();
    let mut name_env = RhoCalcNameEnv::new();

    mettail_runtime::clear_var_cache();
    let proc_parser = rhocalc::ProcParser::new();
    let name_parser = rhocalc::NameParser::new();

    // Parse terms
    let proc = proc_parser.parse("0").expect("Parse failed");
    let name = name_parser.parse("@(0)").expect("Parse failed");

    // Store and retrieve
    proc_env.set("p".to_string(), proc.clone());
    name_env.set("n".to_string(), name.clone());

    assert!(proc_env.get("p").is_some(), "Proc environment failed");
    assert!(name_env.get("n").is_some(), "Name environment failed");

    // Verify HashMap structure
    let proc_facts = proc_env.env_to_facts();
    assert!(!proc_facts.is_empty(), "Proc facts should not be empty");

    let name_facts = name_env.env_to_facts();
    assert!(!name_facts.is_empty(), "Name facts should not be empty");
}

fn test_calculator_env() {
    // Calculator uses env_var conditions, but environment generation
    // should NOT depend on detecting/analyzing those rewrites
    // It should just generate an env for the Int category

    let mut int_env = CalculatorIntEnv::new();

    mettail_runtime::clear_var_cache();
    let int_parser = calculator::IntParser::new();

    // Create a simple value
    let val = int_parser.parse("42").expect("Parse failed");

    // Store and retrieve
    int_env.set("x".to_string(), val.clone());
    assert!(int_env.get("x").is_some(), "Int environment failed");

    let facts = int_env.env_to_facts();
    assert!(!facts.is_empty(), "Int facts should not be empty");
}

fn test_type_safety() {
    println!("  Checking HashMap type signatures:");

    // These should compile without issues, proving HashMap<String, CategoryName> works
    let mut proc_env = RhoCalcProcEnv::new();
    let mut name_env = RhoCalcNameEnv::new();
    let mut int_env = CalculatorIntEnv::new();

    // The HashMap<String, Proc> type works
    mettail_runtime::clear_var_cache();
    let proc_parser = rhocalc::ProcParser::new();
    let p = proc_parser.parse("0").unwrap();
    proc_env.set("key1".to_string(), p);
    println!("    - HashMap<String, Proc> ✓");

    // The HashMap<String, Name> type works
    let name_parser = rhocalc::NameParser::new();
    let n = name_parser.parse("@(0)").unwrap();
    name_env.set("key2".to_string(), n);
    println!("    - HashMap<String, Name> ✓");

    // The HashMap<String, Int> type works
    let int_parser = calculator::IntParser::new();
    let i = int_parser.parse("42").unwrap();
    int_env.set("key3".to_string(), i);
    println!("    - HashMap<String, Int> ✓");
}
