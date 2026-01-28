use ascent::*;
use ascent_byods_rels::*;
use mettail_languages::ambient::*;

struct TestCase {
    name: &'static str,
    input: &'static str,
    expected_output: Option<&'static str>,
    should_normalize: bool,
    min_rewrites: usize,
    description: &'static str,
}

fn run_test(test: &TestCase) -> Result<(), String> {
    println!("TEST: {}", test.name);
    println!("Description: {}", test.description);
    println!("Input: {}", test.input);

    mettail_runtime::clear_var_cache();
    let parser = ambient::ProcParser::new();
    let input_term = parser
        .parse(test.input)
        .map_err(|e| format!("Parse error: {:?}", e))?;

    // Normalize to flatten any nested collections
    let input_term = input_term.normalize();

    println!("Parsed: {}", input_term);

    let prog = ascent_run! {
        include_source!(ambient_source);
        proc(p) <-- for p in [input_term.clone()];

        relation path(Proc, Proc);
        path(p1, p2) <-- rw_proc(p1,p2);
        path(p1, p3) <-- path(p1,p2), path(p2,p3);

        relation is_normal_form(Proc);
        is_normal_form(t.clone()) <-- proc(t), !rw_proc(t.clone(),_);
    };

    let mut rewrites: Vec<_> = prog.rw_proc.iter().collect();
    rewrites.sort_by(|a, b| a.0.cmp(&b.0));

    println!("Equations:");
    for (lhs, rhs) in prog.__eq_proc_ind_common.iter_all_added() {
        if lhs.to_string() != rhs.to_string() {
            println!("  {} = {}", lhs, rhs);
        }
    }

    println!("\nRewrites found: {}", rewrites.len());
    for (i, (s, t)) in rewrites.iter().enumerate() {
        println!("  [{}] {} ~> {}", i + 1, s, t);
    }

    // Check minimum rewrites
    if rewrites.len() < test.min_rewrites {
        return Err(format!(
            "Expected at least {} rewrites, found {}",
            test.min_rewrites,
            rewrites.len()
        ));
    }

    // Check normalization
    let normal_forms: Vec<_> = prog.is_normal_form.iter().collect();
    println!("\nNormal forms: {}", normal_forms.len());
    for nf in &normal_forms {
        println!("  {}", nf.0);
    }

    if test.should_normalize && normal_forms.is_empty() {
        return Err("Expected to find a normal form, but none found".to_string());
    }

    // Check expected output if provided
    if let Some(expected_str) = test.expected_output {
        let expected = parser
            .parse(expected_str)
            .map_err(|e| format!("Parse error in expected: {:?}", e))?;

        // Check if expected output is in the rewrite relation
        let found = rewrites
            .iter()
            .any(|(from, to)| from == &input_term && to == &expected)
            || prog
                .path
                .iter()
                .any(|(from, to)| from == &input_term && to == &expected);

        if !found {
            // Also check if it's in normal forms
            let in_normal_forms = normal_forms.iter().any(|nf| nf.0 == expected);
            if !in_normal_forms {
                return Err(format!(
                    "Expected output '{}' not found in rewrites or normal forms",
                    expected_str
                ));
            }
        }
        println!("\n✓ Expected output found: {}", expected_str);
    }

    println!("\n✓ Test passed!");
    Ok(())
}

fn main() {
    let tests = vec![
        // Basic rest patterns - empty context
        TestCase {
            name: "enter_empty_rest",
            input: "{n[{in(m,p)}] | m[r]}",
            expected_output: Some("m[{n[{p}] | r}]"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Basic entry with empty rest pattern: n enters m",
        },

        TestCase {
            name: "exit_empty_rest",
            input: "m[{n[{out(m,p)}] | r}]",
            expected_output: Some("{n[{p}] | m[r]}"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Basic exit with empty rest pattern: n exits m",
        },

        TestCase {
            name: "open_basic",
            input: "{open(n,p) | n[q]}",
            expected_output: Some("{p | q}"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Basic open capability",
        },

        // Rest patterns - non-empty context
        TestCase {
            name: "enter_nonempty_rest",
            input: "{n[{in(m,p) | q}] | m[r]}",
            expected_output: Some("m[{n[{p | q}] | r}]"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Entry with non-empty rest: preserves q during move",
        },

        TestCase {
            name: "enter_multiple_rest",
            input: "{n[{in(m,p) | q | s}] | m[r]}",
            expected_output: Some("m[{n[{p | q | s}] | r}]"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Entry with multiple items in rest",
        },

        TestCase {
            name: "exit_nonempty_rest",
            input: "m[{n[{out(m,p) | q}] | r}]",
            expected_output: Some("{n[{p | q}] | m[r]}"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Exit with non-empty rest: preserves q during exit",
        },

        TestCase {
            name: "exit_multiple_rest",
            input: "m[{n[{out(m,p) | q | s | t}] | r}]",
            expected_output: Some("{n[{p | q | s | t}] | m[r]}"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Exit with multiple items in rest",
        },

        // Context preservation
        TestCase {
            name: "context_preservation",
            input: "{n[{in(m,p) | state1 | state2}] | m[{r | local}]}",
            expected_output: Some("m[{n[{p | state1 | state2}] | r | local}]"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Both ambients preserve their local state",
        },

        // Parallel operations
        TestCase {
            name: "parallel_entry",
            input: "{a[{in(parent,x)}] | b[{in(parent,y)}] | parent[z]}",
            expected_output: None, // Multiple possible outcomes
            should_normalize: false, // May have multiple normal forms
            min_rewrites: 2, // At least two rewrites (one for each entry)
            description: "Two ambients entering the same parent in parallel",
        },

        // Sequential operations
        TestCase {
            name: "sequential_mobility",
            input: "{agent[{in(loc1, in(loc2, {}))}] | loc1[{}] | loc2[{}]}",
            expected_output: None, // Complex chain
            should_normalize: false,
            min_rewrites: 1, // At least the first move
            description: "Agent moves through multiple locations",
        },

        // Nested mobility
        TestCase {
            name: "nested_mobility",
            input: "{parent[{in(grandparent,{}) | child[{}]}] | grandparent[{}]}",
            expected_output: Some("grandparent[{parent[{child[{}]}]}]"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Parent with child moves together",
        },

        // Complex interactions
        TestCase {
            name: "entry_then_exit",
            input: "{n[{in(m, out(m, p))}] | m[r]}",
            expected_output: None, // Chain of rewrites
            should_normalize: true,
            min_rewrites: 2, // Enter, then exit
            description: "Agent enters then immediately exits",
        },

        TestCase {
            name: "open_after_entry",
            input: "{agent[{in(container, {})}] | container[{open(agent, result)}]}",
            expected_output: Some("container[{result}]"), // Multi-step
            should_normalize: true,
            min_rewrites: 2, // Entry then open
            description: "Agent enters container, then is opened",
        },

        TestCase {
            name: "nested_ambients_in_rest",
            input: "{n[{in(m,p) | inner[data]}] | m[r]}",
            expected_output: Some("m[{n[{p | inner[data]}] | r}]"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Nested ambient preserved in rest during move",
        },

        // Congruence closure tests
        TestCase {
            name: "congruence_in_ambient",
            input: "outer[{n[{in(m,p)}] | m[r]}]",
            expected_output: None, // Rewrites under ambient
            should_normalize: false,
            min_rewrites: 1,
            description: "Rewrite applies under ambient constructor",
        },

        TestCase {
            name: "congruence_in_parallel",
            input: "{n[{in(m,p)}] | m[r] | observer}",
            expected_output: None, // Rewrites in parallel context
            should_normalize: false,
            min_rewrites: 1,
            description: "Rewrite applies within parallel composition",
        },

        // =====================================================================
        // PHASE 4: Complex Equation + Rewrite Interaction Tests
        // =====================================================================

        TestCase {
            name: "equation_then_rewrite_extrusion_in",
            input: "{n[{in(m,{})}] | new(x,m[{}])}",
            expected_output: Some("new(x, {m[{n[{}]}]})"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Extrusion equation allows in-capability rewrite: {n[{in(m,{})}], new(x,m[{}])} =eq= new(x,{n[{in(m,{})}], m[{}]}) =>rw new(x,{m[{n[{}],{}}]})",
        },

        TestCase {
            name: "equation_zero_then_rewrite",
            input: "{n[{in(m,p)}] | m[{}] | {}}",
            expected_output: Some("{m[{n[{p}]}]}"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Zero elimination via equation, then in-capability rewrite",
        },

        TestCase {
            name: "nested_extrusion_in",
            input: "new(x, new(y, {p | in(n, q)}))",
            expected_output: Some("new(x, new(y, {p | in(n, q)}))"), // Doesn't reduce, but equations apply
            should_normalize: false,
            min_rewrites: 0,
            description: "Nested binders with capability - tests equation application",
        },

        TestCase {
            name: "extrusion_enables_out",
            input: "{open(n, p) | new(x, n[{out(m, q)}])}",
            expected_output: None, // Complex multi-step
            should_normalize: false,
            min_rewrites: 1,
            description: "Scope extrusion positions term for later open/out interaction",
        },

        TestCase {
            name: "parallel_with_extrusion",
            input: "{new(x, {p | n[{in(m, q)}]}) | m[r]}",
            expected_output: Some("new(x,{m[{n[{q}] | r}] | p})"), // Equation then rewrite
            should_normalize: true,
            min_rewrites: 1,
            description: "Extrusion equation enables parallel in-capability: {new(x,{p,n[{in(m,q)}]}), m[r]} =eq= {p, n[{in(m, new(x,q))}], m[r]} =>rw {p, m[{n[{r, new(x,q)}]}]}",
        },

        TestCase {
            name: "zero_in_multiple_contexts",
            input: "{{} | p | {{} | q}}",
            expected_output: Some("{p | q}"),
            should_normalize: true,
            min_rewrites: 0, // Only equations
            description: "Multiple zero eliminations through equations",
        },

        TestCase {
            name: "extrusion_amb_then_open",
            input: "{open(n, p) | new(x, {q | n[r]})}",
            expected_output: None, // Multi-step
            should_normalize: false,
            min_rewrites: 1,
            description: "Ambient extrusion equation positions for open rewrite",
        },

        TestCase {
            name: "complex_mobility_with_binding",
            input: "new(x, {n[{in(m, x)}] | m[{}]})",
            expected_output: Some("new(x, {m[{n[{x}]}]})"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Bound variable in capability - tests freshness and rewrite",
        },

        TestCase {
            name: "sequential_extrusions",
            input: "new(x, new(y, {p | in(n, q)}))",
            expected_output: Some("new(x, new(y, {p | in(n, q)}))"), // Equations apply but no rewrites
            should_normalize: false,
            min_rewrites: 0,
            description: "Multiple nested binders with capability",
        },

        TestCase {
            name: "zero_elimination_cascade",
            input: "{{} | {} | {} | {}}",
            expected_output: Some("{}"),
            should_normalize: true,
            min_rewrites: 0,
            description: "Cascading zero elimination through equations",
        },

        TestCase {
            name: "extrusion_with_out_and_in",
            input: "new(x, {n[{in(m, p) | out(k, q)}] | m[r]})",
            expected_output: Some("new(x, {m[{n[{p | out(k, q)}] | r}]})"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Extrusion doesn't interfere with mixed capabilities",
        },

        TestCase {
            name: "open_after_amb_extrusion",
            input: "{open(n, p) | new(x, {x[q] | n[r]})}",
            // = new(x, {open(n,p) | x[q] | n[r]})
            expected_output: None, // Requires equation then multiple rewrites
            should_normalize: false,
            min_rewrites: 1,
            description: "Ambient extrusion followed by open: {open(n,p), new(x,{q,n[r]})} =eq= {open(n,p), q, n[new(x,r)]} =>rw {p, q, new(x,r)}",
        },

        TestCase {
            name: "in_with_zero_elimination",
            input: "{n[{in(m, {p | {}})}] | m[q]}",
            expected_output: Some("{m[{n[{p}] | q}]}"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Zero elimination in capability before mobility",
        },
    ];

    println!("\nRunning {} ambient calculus tests...", tests.len());

    let mut passed = 0;
    let mut failed = 0;
    let mut errors = Vec::new();

    for test in &tests {
        match run_test(test) {
            Ok(()) => passed += 1,
            Err(e) => {
                failed += 1;
                errors.push((test.name, e));
            },
        }
    }

    println!("TEST SUMMARY");
    println!("Total: {}", tests.len());
    println!("Passed: {}", passed);
    println!("Failed: {}", failed);

    if !errors.is_empty() {
        println!("FAILURES:");
        for (name, error) in &errors {
            println!("\n✗ {}", name);
            println!("  Error: {}", error);
        }
    }

    if failed > 0 {
        std::process::exit(1);
    }
}
