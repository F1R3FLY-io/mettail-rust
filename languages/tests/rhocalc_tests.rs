use ascent::*;
use ascent_byods_rels::*;
use mettail_languages::rhocalc::*;

fn parse_proc(input: &str) -> Result<Proc, String> {
    Proc::parse(input)
}

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
    let input_term = parse_proc(test.input)?;

    // Normalize to flatten any nested collections
    let input_term = input_term.normalize();

    println!("Parsed: {}", input_term);

    let prog = ascent_run! {
        include_source!(rhocalc_source);
        proc(p) <-- for p in [input_term.clone()];

        relation redex_eq(Proc);
        redex_eq(q.clone()) <-- eq_proc(input_term.clone(), q);
        proc(q) <-- redex_eq(q);

        relation path(Proc, Proc);
        path(p1, p2) <-- rw_proc(p1,p2);
        path(p1, p3) <-- path(p1,p2), path(p2,p3);

        relation is_normal_form(Proc);
        is_normal_form(t.clone()) <-- proc(t), !rw_proc(t.clone(),_);

        relation path_full(Proc, Proc);
        path_full(input_term.clone(), z.clone()) <-- is_normal_form(z), path(input_term.clone(), z.clone());
    };

    let mut rewrites: Vec<_> = prog.rw_proc.iter().collect();
    rewrites.sort_by(|a, b| a.0.cmp(&b.0));

    println!("\nEquations:");
    let eq_count = 0;
    // for (lhs, rhs) in prog.__eq_proc_ind_common.iter_all_added() {
    //     if lhs.to_string() != rhs.to_string() {
    //         println!("  {} = {}", lhs, rhs);
    //         eq_count += 1;
    //     }
    // }
    if eq_count == 0 {
        println!("  (none)");
    }

    println!("\nRewrites found: {}", rewrites.len());
    for (i, (s, t)) in rewrites.iter().enumerate().take(20) {
        println!("  [{}] {} ~> {}", i + 1, s, t);
    }
    if rewrites.len() > 20 {
        println!("  ... ({} more)", rewrites.len() - 20);
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
        let expected = parse_proc(expected_str)?
            .normalize();

        // Check if expected output is in the rewrite relation or path
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
                    "Expected output '{}' not found in rewrites or normal forms.\nNormalized expected: {}\nAvailable normal forms: {:?}",
                    expected_str,
                    expected,
                    normal_forms.iter().map(|nf| nf.0.to_string()).collect::<Vec<_>>()
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
        // =====================================================================
        // PHASE 1: Basic Communication Tests
        // =====================================================================

        // TestCase {
        //     name: "basic_communication",
        //     input: "{for(x -> y) {y!(0)}, x!({})}",
        //     expected_output: Some("{{@({})!(0)}}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "Basic send/receive: channel x sends {}, received as y in continuation",
        // },

        // TestCase {
        //     name: "communication_with_data",
        //     input: "{for(chan -> x) {x!(result)}, chan!(data)}",
        //     expected_output: Some("{{@(data)!(result)}}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "Communication with non-trivial data",
        // },

        // TestCase {
        //     name: "zero_communication",
        //     input: "{for(c -> x) {0}, c!(p)}",
        //     expected_output: Some("{0}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "Communication where continuation is zero",
        // },

        // // =====================================================================
        // // PHASE 2: Drop-Quote Equation Tests
        // // =====================================================================

        // TestCase {
        //     name: "drop_quote_equation",
        //     input: "*(n)",
        //     expected_output: None, // Just checks equation works
        //     should_normalize: false,
        //     min_rewrites: 0,
        //     description: "Drop-quote equation: @(*(n)) = n (tested via equations)",
        // },

        // TestCase {
        //     name: "drop_quote_in_output",
        //     input: "@(*(n))!({})",
        //     expected_output: None,
        //     should_normalize: false,
        //     min_rewrites: 0,
        //     description: "Drop-quote in output position uses equation",
        // },

        // TestCase {
        //     name: "drop_quote_in_input",
        //     input: "for(@(*(n)) -> x) {x!(result)}",
        //     expected_output: None,
        //     should_normalize: false,
        //     min_rewrites: 0,
        //     description: "Drop-quote in input channel uses equation",
        // },

        // // =====================================================================
        // // PHASE 3: PDrop Rewrite Tests
        // // =====================================================================

        // TestCase {
        //     name: "pdrop_basic",
        //     input: "{*(@(p))}",
        //     expected_output: Some("{p}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "Basic PDrop rewrite: *(name) => proc when name is @(proc)",
        // },

        // TestCase {
        //     name: "pdrop_in_parallel",
        //     input: "{*(@(p)), q}",
        //     expected_output: Some("{p, q}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "PDrop in parallel context",
        // },

        // TestCase {
        //     name: "pdrop_nested_quote",
        //     input: "{*(@({a, b}))}",
        //     expected_output: Some("{{a, b}}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "PDrop with nested process in quote",
        // },

        // TestCase {
        //     name: "multiple_pdrops",
        //     input: "{*(@(p)), *(@(q))}",
        //     expected_output: Some("{p, q}"),
        //     should_normalize: true,
        //     min_rewrites: 2,
        //     description: "Multiple PDrop rewrites in parallel",
        // },

        // // =====================================================================
        // // PHASE 4: Communication + PDrop Interaction
        // // =====================================================================

        // TestCase {
        //     name: "send_quoted_process",
        //     input: "{for(c -> x) {*(x)}, c!(result)}",
        //     expected_output: Some("{result}"),
        //     should_normalize: true,
        //     min_rewrites: 2, // Communication, then PDrop
        //     description: "Send a quoted process, receive and drop it",
        // },

        // TestCase {
        //     name: "send_and_drop_complex",
        //     input: "{for(c -> x) {{*(x), observer}}, c!(p)}",
        //     expected_output: Some("{p, observer}"),
        //     should_normalize: true,
        //     min_rewrites: 2,
        //     description: "Communication followed by drop with other processes",
        // },

        // TestCase {
        //     name: "nested_communication_drop",
        //     input: "{for(c1 -> x) {{for(c2 -> y) {{*(x), *(y)}}, c2!(q)}}, c1!(p)}",
        //     expected_output: Some("{p, q}"),
        //     should_normalize: true,
        //     min_rewrites: 3, // Two communications, two drops
        //     description: "Nested communication with multiple drops",
        // },

        // TestCase {
        //     name: "quote_drop_roundtrip",
        //     input: "{for(c -> name) {*(@(*(name)))}, c!(x)}",
        //     expected_output: Some("{x}"),
        //     should_normalize: true,
        //     min_rewrites: 2, // Communication, then drop
        //     description: "Quote-drop roundtrip: @(*(name)) drops to *(name)",
        // },

        // // =====================================================================
        // // PHASE 5: Parallel Communication Tests
        // // =====================================================================

        // TestCase {
        //     name: "parallel_sends",
        //     input: "{for(c -> x) {x!(result)}, c!(a), c!(b)}",
        //     expected_output: None, // Multiple possible outcomes
        //     should_normalize: false,
        //     min_rewrites: 2, // Two different communications possible
        //     description: "Multiple senders on same channel - non-deterministic",
        // },

        // TestCase {
        //     name: "parallel_receives",
        //     input: "{for(c -> x) {x!(p)}, for(c -> y) {y!(q)}, c!(data)}",
        //     expected_output: None, // Multiple receivers
        //     should_normalize: false,
        //     min_rewrites: 2,
        //     description: "Multiple receivers on same channel",
        // },

        // TestCase {
        //     name: "different_channels",
        //     input: "{for(c1 -> x) {x!(p)}, for(c2 -> y) {y!(q)}, c1!(a), c2!(b)}",
        //     expected_output: Some("{{@(a)!(p), @(b)!(q)}}"),
        //     should_normalize: true,
        //     min_rewrites: 2,
        //     description: "Independent communications on different channels",
        // },

        // // =====================================================================
        // // PHASE 6: Forwarding and Pipelines
        // // =====================================================================

        // TestCase {
        //     name: "simple_forward",
        //     input: "{for(in -> x) {out!(*(x))}, in!(data)}",
        //     expected_output: Some("{out!(*(@(data)))}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "Simple forwarding: receive on 'in', send on 'out'",
        // },

        // TestCase {
        //     name: "pipeline_two_stage",
        //     input: "{for(c1 -> x) {c2!(*(x))}, for(c2 -> y) {result!(*(y))}, c1!(data)}",
        //     expected_output: Some("{result!(*(@(*(@(data)))))}"),
        //     should_normalize: true,
        //     min_rewrites: 2,
        //     description: "Two-stage pipeline: c1 -> c2 -> result",
        // },

        // TestCase {
        //     name: "broadcast",
        //     input: "{for(in -> x) {{out1!(*(x)), out2!(*(x))}}, in!(data)}",
        //     expected_output: Some("{{out1!(*(@(data))), out2!(*(@(data)))}}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "Broadcast: one input, multiple outputs",
        // },

        // // =====================================================================
        // // PHASE 7: Recursive Patterns (Limited)
        // // =====================================================================

        // TestCase {
        //     name: "nested_parallel_comm",
        //     input: "{{for(c -> x) {x!(p)}, c!(a)}, observer}",
        //     expected_output: Some("{@(a)!(p), observer}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "Communication inside nested parallel composition",
        // },

        // TestCase {
        //     name: "drop_inside_output",
        //     input: "{for(c -> x) {result!(*(x))}, c!(data)}",
        //     expected_output: Some("{result!(*(@(data)))}"),
        //     should_normalize: true,
        //     min_rewrites: 2, // Comm, then drop inside output
        //     description: "Drop rewrite applies inside output continuation",
        // },

        // // =====================================================================
        // // PHASE 8: Complex Substitution Tests
        // // =====================================================================

        // TestCase {
        //     name: "substitution_in_output",
        //     input: "{for(c -> x) {x!(*(x))}, c!(self)}",
        //     expected_output: Some("{@(self)!(*(@(self)))}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "Substitution where variable appears multiple times",
        // },

        // TestCase {
        //     name: "substitution_with_drop",
        //     input: "{for(c -> x) {*(x)}, c!({p, q})}",
        //     expected_output: Some("{p, q}"),
        //     should_normalize: true,
        //     min_rewrites: 2,
        //     description: "Substitution followed by drop of complex process",
        // },

        // TestCase {
        //     name: "nested_substitution",
        //     input: "{for(c1 -> x) {for(c2 -> y) {{out!(*(x)), out!(*(y))}}}, c1!(a)}",
        //     expected_output: Some("{for(c2 -> y) {{out!(*(@(a))), out!(*(y))}}}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "Nested input with partial substitution",
        // },

        // // =====================================================================
        // // PHASE 9: Congruence Under Parallel
        // // =====================================================================

        // TestCase {
        //     name: "congruence_basic",
        //     input: "{{*(@(p)), q}, observer}",
        //     expected_output: Some("{{p, q}, observer}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "Rewrite applies under parallel constructor",
        // },

        // TestCase {
        //     name: "congruence_deep",
        //     input: "{{{*(@(p))}}}",
        //     expected_output: Some("{{{p}}}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "Rewrite applies through multiple parallel layers",
        // },

        // TestCase {
        //     name: "congruence_with_comm",
        //     input: "{for(c -> x) {*(x)}, c!(result), observer}",
        //     expected_output: Some("{result, observer}"),
        //     should_normalize: true,
        //     min_rewrites: 2,
        //     description: "Communication and drop under parallel context",
        // },

        // // =====================================================================
        // // PHASE 10: Edge Cases and Complex Patterns
        // // =====================================================================

        // TestCase {
        //     name: "self_communication",
        //     input: "{for(@(p) -> x) {x!(result)}, @(p)!(data)}",
        //     expected_output: Some("{{@(data)!(result)}}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "Communication on a quoted process channel",
        // },

        // TestCase {
        //     name: "zero_in_parallel",
        //     input: "{for(c -> x) {{x!(p), 0}}, c!(q)}",
        //     expected_output: Some("{@(q)!(p), 0}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "Zero process explicitly in parallel",
        // },

        // TestCase {
        //     name: "complex_quote_nesting",
        //     input: "{*(@(*(@(*(@(p))))))}",
        //     expected_output: Some("{*(@(*(@(p))))}"),
        //     should_normalize: true,
        //     min_rewrites: 1, // Only outermost drop reduces
        //     description: "Deeply nested quote-drop (only outermost reduces)",
        // },

        // TestCase {
        //     name: "multiple_independent_comms",
        //     input: "{for(a -> x) {x!(p1)}, for(b -> y) {y!(p2)}, for(c -> z) {z!(p3)}, a!(d1), b!(d2), c!(d3)}",
        //     expected_output: Some("{{@(d1)!(p1), @(d2)!(p2), @(d3)!(p3)}}"),
        //     should_normalize: true,
        //     min_rewrites: 3,
        //     description: "Three independent communications in parallel",
        // },

        // TestCase {
        //     name: "comm_with_complex_continuation",
        //     input: "{for(c -> x) {{*(x), y!(*(x)), z!(*(x))}}, c!(data)}",
        //     expected_output: Some("{data, y!(*(@(data))), z!(*(@(data)))}"),
        //     should_normalize: true,
        //     min_rewrites: 2, // Comm + drop
        //     description: "Communication with complex nested continuation",
        // },

        // TestCase {
        //     name: "drop_chain",
        //     input: "{*(@(p)), *(@(q)), *(@(r))}",
        //     expected_output: Some("{p, q, r}"),
        //     should_normalize: true,
        //     min_rewrites: 3,
        //     description: "Multiple independent drops in parallel",
        // },

        // TestCase {
        //     name: "variable_shadowing",
        //     input: "{for(c -> x) {for(d -> x) {x!(result)}}, c!(outer)}",
        //     expected_output: Some("{{for(d -> x) {x!(result)}}}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "Variable shadowing in nested inputs (outer x substituted)",
        // },

        // TestCase {
        //     name: "equation_in_communication",
        //     input: "{for(@(*(n)) -> x){x!(result)}, n!(data)}",
        //     expected_output: Some("{@(data)!(result)}"),
        //     should_normalize: true,
        //     min_rewrites: 1,
        //     description: "Drop-quote equation applied in input channel",
        // },

        // =====================================================================
        // PHASE 11: Multi-Communication Tests (Join Patterns)
        // =====================================================================
        TestCase {
            name: "multi_comm_basic",
            input: "{(c1?x, c2?y).{*(x)} | c1!(p) | c2!(q)}",
            expected_output: Some("p"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Basic multi-communication: receive on two channels, use first",
        },
        TestCase {
            name: "multi_comm_both_vars",
            input: "{(c1?x, c2?y).{{*(x) | *(y)}} | c1!(p) | c2!(q)}",
            expected_output: Some("{p | q}"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Multi-communication using both received values",
        },
        TestCase {
            name: "multi_comm_three_channels",
            input: "{(a?x, b?y, c?z).{{*(x) | *(y) | *(z)}} | a!(p) | b!(q) | c!(r)}",
            expected_output: Some("{p | q | r}"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Multi-communication on three channels",
        },
        TestCase {
            name: "multi_comm_forward",
            input: "{(c1?x, c2?y).{out!(*(x))} | c1!(data) | c2!(ignored)}",
            expected_output: Some("out!(*(@(data)))"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Multi-comm with forwarding on one channel",
        },
        TestCase {
            name: "multi_comm_join",
            input: "{(c?x, c?y).{{*(x) | *(y)}} | c!(a) | c!(b)}",
            expected_output: Some("{a | b}"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Join pattern: two receives on same channel",
        },
        TestCase {
            name: "multi_comm_with_parallel",
            input: "{(c1?x, c2?y).{*(x)} | c1!(p) | c2!(q)}",
            expected_output: Some("p"),
            should_normalize: true,
            min_rewrites: 1,
            description: "Multi-comm in nested parallel context",
        },
    ];

    println!("Running {} RhoCalc tests...", tests.len());

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
    } else {
        println!("\n✓ All tests passed!");
    }
}
