/// Test environment infrastructure on RhoCalc
///
/// This test verifies that environment structs are automatically generated
/// for all exported categories in a theory, regardless of whether they have
/// env_var conditions or not.
use mettail_theories::rhocalc::*;

fn main() {
    println!("Testing environment infrastructure on RhoCalc");

    // Create environment for Proc category
    let mut proc_env = RhoCalcProcEnv::new();

    // Create environment for Name category
    let mut name_env = RhoCalcNameEnv::new();

    // Test basic operations
    println!("RhoCalcProcEnv created: {:?}", proc_env);
    println!("RhoCalcNameEnv created: {:?}", name_env);

    // Test set/get operations on Proc environment
    mettail_runtime::clear_var_cache();
    let parser = rhocalc::ProcParser::new();
    let proc_term = parser.parse("0").expect("Failed to parse simple process");

    proc_env.set("p0".to_string(), proc_term.clone());
    if let Some(retrieved) = proc_env.get("p0") {
        println!("Successfully retrieved Proc from environment: {:?}", retrieved);
    }

    // Test set/get operations on Name environment
    let parser = rhocalc::NameParser::new();
    let name_term = parser.parse("@(0)").expect("Failed to parse simple name");

    name_env.set("n0".to_string(), name_term.clone());
    if let Some(retrieved) = name_env.get("n0") {
        println!("Successfully retrieved Name from environment: {:?}", retrieved);
    }

    // Test env_to_facts
    let proc_facts = proc_env.env_to_facts();
    println!("Proc environment facts: {:?}", proc_facts);

    let name_facts = name_env.env_to_facts();
    println!("Name environment facts: {:?}", name_facts);

    // Test clear
    proc_env.clear();
    assert!(proc_env.get("p0").is_none(), "Environment was not cleared");
    println!("Successfully cleared Proc environment");

    name_env.clear();
    assert!(name_env.get("n0").is_none(), "Environment was not cleared");
    println!("Successfully cleared Name environment");

    println!("\nAll environment infrastructure tests passed!");
}
