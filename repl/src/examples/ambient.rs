// Ambient Calculus example processes for the REPL
//
// Demonstrates mobility, security, and context preservation patterns

use super::{Example, ExampleCategory, LanguageName};

pub fn all() -> Vec<&'static Example> {
    vec![
        &AMB_ENTER,
        &AMB_EXIT,
        &AMB_OPEN,
        &AMB_FIREWALL,
        &AMB_MOBILE_AGENT,
        &AMB_COLOCATED,
        &AMB_NESTED_MOBILITY,
        &AMB_CAPABILITY_PASSING,
        &AMB_SAFE_AMBIENT,
        &AMB_PARENT_CHILD,
        // Rest pattern demonstrations
        &AMB_REST_EMPTY,
        &AMB_REST_NONEMPTY,
        &AMB_REST_CONTEXT,
        &AMB_REST_NESTED,
        &AMB_REST_MULTIPLE,
        &AMB_REST_PRESERVATION,
        &AMB_REST_COMPLEX,
    ]
}

//=============================================================================
// SIMPLE MOBILITY EXAMPLES
//=============================================================================

pub static AMB_ENTER: Example = Example {
    name: "amb_enter",
    description: "Basic ambient entry: n[{in(m,p)}] | m[r] => m[{n[{p}] | r}]",
    source: "{n[{in(m,p)}] | m[r]}",
    category: ExampleCategory::Simple,
    language: LanguageName::AmbientCalculus,
};

pub static AMB_EXIT: Example = Example {
    name: "amb_exit",
    description: "Ambient exit: m[{n[{out(m,p)}] | r}] => {n[{p}] | m[r]}",
    source: "m[{n[{out(m,p)}] | r}]",
    category: ExampleCategory::Simple,
    language: LanguageName::AmbientCalculus,
};

pub static AMB_OPEN: Example = Example {
    name: "amb_open",
    description: "Open ambient: {open(n,p) | n[q]} => {p | q}",
    source: "{open(n,p) | n[q]}",
    category: ExampleCategory::Simple,
    language: LanguageName::AmbientCalculus,
};

//=============================================================================
// MOBILITY PATTERNS
//=============================================================================

pub static AMB_FIREWALL: Example = Example {
    name: "amb_firewall",
    description: "Firewall pattern: agent enters trusted zone but not untrusted",
    source: "{firewall[{agent[{in(firewall,0)} | trusted[0]}] | untrusted[{agent[{in(untrusted,0)} | 0]}]}",
    category: ExampleCategory::Mobility,
    language: LanguageName::AmbientCalculus,
};

pub static AMB_MOBILE_AGENT: Example = Example {
    name: "amb_mobile_agent",
    description: "Mobile agent: travels through multiple locations sequentially",
    source: "{agent[{in(loc1, in(loc2, 0))}] | loc1[0] | loc2[0]}",
    category: ExampleCategory::Mobility,
    language: LanguageName::AmbientCalculus,
};

pub static AMB_COLOCATED: Example = Example {
    name: "amb_colocated",
    description: "Co-location: two ambients enter the same parent",
    source: "{parent[0] | child1[{in(parent,0)}] | child2[{in(parent,0)}]}",
    category: ExampleCategory::Mobility,
    language: LanguageName::AmbientCalculus,
};

pub static AMB_NESTED_MOBILITY: Example = Example {
    name: "amb_nested_mobility",
    description: "Nested mobility: child moves with parent",
    source: "{grandparent[0] | parent[{in(grandparent,0) | child[0]}]}",
    category: ExampleCategory::Mobility,
    language: LanguageName::AmbientCalculus,
};

//=============================================================================
// ADVANCED PATTERNS
//=============================================================================

pub static AMB_CAPABILITY_PASSING: Example = Example {
    name: "amb_capability_passing",
    description: "Capability passing: new creates fresh ambient names",
    source: "new(x, {agent[{in(x,0)}] | x[0]})",
    category: ExampleCategory::Advanced,
    language: LanguageName::AmbientCalculus,
};

pub static AMB_SAFE_AMBIENT: Example = Example {
    name: "amb_safe_ambient",
    description: "Safe ambient: only authorized agents can access resources",
    source: "{safe[{open(key,0)}] | key[{secret[0]}] | agent[{in(safe,0) | open(key,0)}]}",
    category: ExampleCategory::Advanced,
    language: LanguageName::AmbientCalculus,
};

pub static AMB_PARENT_CHILD: Example = Example {
    name: "amb_parent_child",
    description: "Parent-child coordination: child exits and parent opens",
    source: "parent[{child[{out(parent,0)}] | open(child,result)}]",
    category: ExampleCategory::Advanced,
    language: LanguageName::AmbientCalculus,
};

//=============================================================================
// REST PATTERN DEMONSTRATIONS
//=============================================================================

pub static AMB_REST_EMPTY: Example = Example {
    name: "amb_rest_empty",
    description: "Rest pattern with empty context: demonstrates ...rest matching empty bag",
    source: "{n[{in(m,p)}] | m[r]}",
    category: ExampleCategory::EdgeCase,
    language: LanguageName::AmbientCalculus,
};

pub static AMB_REST_NONEMPTY: Example = Example {
    name: "amb_rest_nonempty",
    description: "Rest pattern with non-empty context: ...rest captures additional processes",
    source: "{n[{in(m,p), q, s}] | m[r]}",
    category: ExampleCategory::EdgeCase,
    language: LanguageName::AmbientCalculus,
};

pub static AMB_REST_CONTEXT: Example = Example {
    name: "amb_rest_context",
    description: "Context preservation: rest maintains ambient state during mobility",
    source: "{n[{in(m,p), state1, state2, counter}] | m[{r, local}]}",
    category: ExampleCategory::Mobility,
    language: LanguageName::AmbientCalculus,
};

pub static AMB_REST_NESTED: Example = Example {
    name: "amb_rest_nested",
    description: "Nested rest patterns: multiple levels of context preservation",
    source: "{outer[{inner[{in(target, data), ctx1}] | ctx2}] | target[base]}",
    category: ExampleCategory::Advanced,
    language: LanguageName::AmbientCalculus,
};

pub static AMB_REST_MULTIPLE: Example = Example {
    name: "amb_rest_multiple",
    description: "Multiple mobility operations with independent contexts",
    source: "{a[{in(parent, x), ctxA}] | b[{in(parent, y), ctxB}] | parent[z]}",
    category: ExampleCategory::Parallel,
    language: LanguageName::AmbientCalculus,
};

pub static AMB_REST_PRESERVATION: Example = Example {
    name: "amb_rest_preservation",
    description: "Sequential mobility preserving context through multiple steps",
    source: "{agent[{in(loc1, in(loc2, done)), state}] | loc1[0] | loc2[0]}",
    category: ExampleCategory::Mobility,
    language: LanguageName::AmbientCalculus,
};

pub static AMB_REST_COMPLEX: Example = Example {
    name: "amb_rest_complex",
    description: "Complex interaction: entry, exit, and open with context preservation",
    source: "{container[{child[{out(container, result), data}] | open(child, final)}] | observer}",
    category: ExampleCategory::Advanced,
    language: LanguageName::AmbientCalculus,
};
