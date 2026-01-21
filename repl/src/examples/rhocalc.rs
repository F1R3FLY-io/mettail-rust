// RhoCalc example processes for the REPL
//
// Demonstrates various communication patterns in the Rho Calculus

use super::{Example, ExampleCategory, TheoryName};

pub fn all() -> Vec<&'static Example> {
    vec![
        &SIMPLE_COMM,
        &SEQUENTIAL,
        &REFLECTION,
        &CHOICE,
        &RACE,
        &FORWARD,
        &CIRCULAR,
        &HANDSHAKE,
        &MULTI_PATH,
        &PARALLEL,
        &BARRIER,
        &SPAWN,
        &FRESH_NAMES,
        &CONTRACT,
        &DEADLOCK,
        &PHILOSOPHERS,
        &REPLICATED_INPUT,
        &FANOUT,
        &PIPELINE,
        &EMPTY,
        &SELF_COMM,
        &DROP_QUOTE_TEST,
        // Multi-communication patterns
        &JOIN_BASIC,
        &JOIN_BARRIER,
        &JOIN_SAME_CHANNEL,
        &ATOMIC_PAIR,
        &SCATTER_GATHER,
        &RESOURCE_LOCK,
        &RENDEZVOUS,
        &CORRELATION,
        &MULTI_PARTY_SYNC,
    ]
}

//=============================================================================
// SIMPLE EXAMPLES
//=============================================================================

pub static SIMPLE_COMM: Example = Example {
    name: "simple_comm",
    description: "Basic communication: single channel, immediate communication",
    source: "{a!(0) | for(a->x){*(x)}}",
    category: ExampleCategory::Simple,
    theory: TheoryName::RhoCalculus,
};

pub static SEQUENTIAL: Example = Example {
    name: "sequential",
    description: "Two independent channels communicating in parallel",
    source: "{a!(0) | for(a->x){*(x)} | b!(0) | for(b->y){*(y)}}",
    category: ExampleCategory::Simple,
    theory: TheoryName::RhoCalculus,
};

pub static REFLECTION: Example = Example {
    name: "reflection",
    description: "Quote/drop cycle demonstrating reflection",
    source: "{for(@(0)->x){*x} | @(0)!(0)}",
    category: ExampleCategory::Simple,
    theory: TheoryName::RhoCalculus,
};

//=============================================================================
// BRANCHING EXAMPLES
//=============================================================================

pub static CHOICE: Example = Example {
    name: "choice",
    description: "Non-deterministic choice: multiple listeners on same channel",
    source: "{a!(0) | for(a->x){x!(0)} | for(a->y){y!(0)}}",
    category: ExampleCategory::Branching,
    theory: TheoryName::RhoCalculus,
};

pub static RACE: Example = Example {
    name: "race",
    description: "Race condition: multiple senders, one listener",
    source: "{a!(0) | a!(1) | for(a->x){*(x)}}",
    category: ExampleCategory::Branching,
    theory: TheoryName::RhoCalculus,
};

//=============================================================================
// COMPLEX PATTERNS
//=============================================================================

pub static FORWARD: Example = Example {
    name: "forward",
    description: "Relay messages between channels (forwarder pattern)",
    source: "{a!(0) | for(a->x){b!(*(x))} | for(b->y){*(y)}}",
    category: ExampleCategory::Complex,
    theory: TheoryName::RhoCalculus,
};

pub static CIRCULAR: Example = Example {
    name: "circular",
    description: "Circular communication (infinite loop, no normal form)",
    source: "{a!(0) | for(a->x){b!(*(x))} | for(b->y){a!(*(y))}}",
    category: ExampleCategory::Complex,
    theory: TheoryName::RhoCalculus,
};

pub static HANDSHAKE: Example = Example {
    name: "handshake",
    description: "Three-way handshake protocol",
    source: "{a!(0) | for(a->x){{b!(*(x)) | for(c->z){*(z)}}} | for(b->y){c!(*(y))}}",
    category: ExampleCategory::Complex,
    theory: TheoryName::RhoCalculus,
};

//=============================================================================
// PARALLEL COMPUTATION
//=============================================================================

pub static MULTI_PATH: Example = Example {
    name: "multi_path",
    description: "Multiple concurrent communications with dependencies (50 terms, 66 rewrites)",
    source: "{
        a!(0) |
        for(a->x0){ {x0!(0) | for(b->y1){y1!(*(a))}} } |
        b!(0) |
        for(b->x1){a!(*(b))} |
        c!(0) |
        for(c->x2){x2!(0)} |
        for(@(0)->y0){*(y0)}
    }",
    category: ExampleCategory::Parallel,
    theory: TheoryName::RhoCalculus,
};

pub static PARALLEL: Example = Example {
    name: "parallel",
    description: "Four independent parallel processes (many execution orders)",
    source: "{
        a!(0) | for(a->x){*(x)  } |
        b!(0) | for(b->y){*(y)  } |
        c!(0) | for(c->z){*(z)  } |
        d!(0) | for(d->w){*(w)  }
    }",
    category: ExampleCategory::Parallel,
    theory: TheoryName::RhoCalculus,
};

pub static BARRIER: Example = Example {
    name: "barrier",
    description: "Barrier synchronization: wait for all inputs",
    source: "{a!(0) | b!(0) | for(a->x){for(b->y){{*(x) | *(y)}}}}",
    category: ExampleCategory::Parallel,
    theory: TheoryName::RhoCalculus,
};

//=============================================================================
// ADVANCED PATTERNS
//=============================================================================

pub static SPAWN: Example = Example {
    name: "spawn",
    description: "Recursive spawning: process creates new processes",
    source: "{a!(0) | for(a->x){{a!(*(x)) | for(a->y){*(y)}}}",
    category: ExampleCategory::Advanced,
    theory: TheoryName::RhoCalculus,
};

pub static FRESH_NAMES: Example = Example {
    name: "fresh_names",
    description: "Name generation via bound variables (capability passing)",
    source: "{for(new->chan){{chan!(0) | for(chan->x){*(x)}}} | new!(@(0))}",
    category: ExampleCategory::Advanced,
    theory: TheoryName::RhoCalculus,
};

pub static CONTRACT: Example = Example {
    name: "contract",
    description: "Contract net: broadcast request, collect responses",
    source: "{req!(0) | for(req->x){{resp1!(*(x)) | resp2!(*(x))}} | for(resp1->a){*(a)  } | for(resp2->b){*(b)  }}",
    category: ExampleCategory::Advanced,
    theory: TheoryName::RhoCalculus,
};

pub static DEADLOCK: Example = Example {
    name: "deadlock",
    description: "Deadlock: circular dependency, no progress possible",
    source: "{for(a->x){for(b->y){{*(x) | *(y)}}} | for(b->z){a!(z)}}",
    category: ExampleCategory::Advanced,
    theory: TheoryName::RhoCalculus,
};

pub static PHILOSOPHERS: Example = Example {
    name: "philosophers",
    description: "Dining philosophers (2): resource contention",
    source: "{
        fork1!(0) | fork2!(0) |
        for(fork1->f1){for(fork2->f2){done1!({*(f1) | *(f2)})}} |
        for(fork2->f2){for(fork1->f1){done2!({*(f2) | *(f1)})}}
    }",
    category: ExampleCategory::Advanced,
    theory: TheoryName::RhoCalculus,
};

pub static REPLICATED_INPUT: Example = Example {
    name: "replicated_input",
    description: "Replication encoding: persistent input listener",
    source: "{
        for(dup->y){ {*(y) | dup!(*(y))} },
        dup!(for(req->x){
            { resp!(*(x)) | for(dup->y){ {*(y) | dup!(*(y))} } }
        }),
        req!(0)
    }",
    category: ExampleCategory::Advanced,
    theory: TheoryName::RhoCalculus,
};

pub static DROP_QUOTE_TEST: Example = Example {
    name: "drop_quote_test",
    description: "Test the *@(P) => P rewrite rule",
    source: "{*(@(0)) | a!(0)}",
    category: ExampleCategory::EdgeCase,
    theory: TheoryName::RhoCalculus,
};

//=============================================================================
// PERFORMANCE BENCHMARKS
//=============================================================================

pub static FANOUT: Example = Example {
    name: "fanout",
    description: "Wide fanout: one-to-many broadcast (performance benchmark)",
    source: "{
        bcast!(0) |
        for(bcast->x){{a!(*x) | b!(*x) | c!(*x) | d!(*x) | e!(*x) | f!(*x) | g!(*x) | h!(*x)}},
        for(a->y){*(y)  } | for(b->y){*(y)  } | for(c->y){*(y)  } | for(d->y){*(y)  } |
        for(e->y){*(y)  } | for(f->y){*(y)  } | for(g->y){*(y)  } | for(h->y){*(y)  }
    }",
    category: ExampleCategory::Performance,
    theory: TheoryName::RhoCalculus,
};

pub static PIPELINE: Example = Example {
    name: "pipeline",
    description: "Deep pipeline: sequential message passing (depth benchmark)",
    source: "{
        a!(0) |
        for(a->x){b!(*(x))} |
        for(b->x){c!(*(x))} |
        for(c->x){d!(*(x))} |
        for(d->x){e!(*(x))} |
        for(e->x){f!(*(x))} |
        for(f->x){*(x)  }
    }",
    category: ExampleCategory::Performance,
    theory: TheoryName::RhoCalculus,
};

//=============================================================================
// EDGE CASES
//=============================================================================

pub static EMPTY: Example = Example {
    name: "empty",
    description: "Empty parallel process (tests identity normalization)",
    source: "{}",
    category: ExampleCategory::EdgeCase,
    theory: TheoryName::RhoCalculus,
};

pub static SELF_COMM: Example = Example {
    name: "self_comm",
    description: "Self-communication (infinite loop)",
    source: "{for(x->y){x!(*(y))} | x!(@(0))}",
    category: ExampleCategory::EdgeCase,
    theory: TheoryName::RhoCalculus,
};

//=============================================================================
// MULTI-COMMUNICATION PATTERNS
//=============================================================================
// These examples use the join pattern: (n1?x, n2?y).{body}
// which receives from multiple channels atomically before proceeding.

pub static JOIN_BASIC: Example = Example {
    name: "join_basic",
    description: "Basic join: wait for two channels before proceeding",
    source: "{(a?x, b?y).{result!({*(x) | *(y)})} | a!(p) | b!(q)}",
    category: ExampleCategory::MultiComm,
    theory: TheoryName::RhoCalculus,
};

pub static JOIN_BARRIER: Example = Example {
    name: "join_barrier",
    description: "Join barrier: cleaner than nested for-loops",
    source: "{
        (ready1?x, ready2?y, ready3?z).{go!({*(x) | *(y) | *(z)})} |
        ready1!(a) | ready2!(b) | ready3!(c)
    }",
    category: ExampleCategory::MultiComm,
    theory: TheoryName::RhoCalculus,
};

pub static JOIN_SAME_CHANNEL: Example = Example {
    name: "join_same_channel",
    description: "Join on same channel: consume two distinct messages atomically",
    source: "{(c?x, c?y).{{*(x) | *(y)}} | c!(a) | c!(b)}",
    category: ExampleCategory::MultiComm,
    theory: TheoryName::RhoCalculus,
};

pub static ATOMIC_PAIR: Example = Example {
    name: "atomic_pair",
    description: "Atomic pair receive: prevents partial consumption",
    source: "{
        (key?k, value?v).{store!({*(k) | *(v)})} |
        key!(name) | value!(data)
    }",
    category: ExampleCategory::MultiComm,
    theory: TheoryName::RhoCalculus,
};

pub static SCATTER_GATHER: Example = Example {
    name: "scatter_gather",
    description: "Scatter-gather: broadcast request, collect all responses",
    source: "{
        req!(query) |
        (req?q).{{resp1!(*(q)) | resp2!(*(q))}} |
        (resp1?r1, resp2?r2).{result!({*(r1) | *(r2)})}
    }",
    category: ExampleCategory::MultiComm,
    theory: TheoryName::RhoCalculus,
};

pub static RESOURCE_LOCK: Example = Example {
    name: "resource_lock",
    description: "Atomic resource acquisition: acquire both forks or neither",
    source: "{
        fork1!(f1) | fork2!(f2) |
        (fork1?a, fork2?b).{eating!({*(a) | *(b)})}
    }",
    category: ExampleCategory::MultiComm,
    theory: TheoryName::RhoCalculus,
};

pub static RENDEZVOUS: Example = Example {
    name: "rendezvous",
    description: "Rendezvous: two parties meet and exchange simultaneously",
    source: "{
        (alice_out?a, bob_out?b).{{alice_in!(*(b)) | bob_in!(*(a))}} |
        alice_out!(gift_a) | bob_out!(gift_b) |
        (alice_in?x).{got_a!(*(x))} | (bob_in?y).{got_b!(*(y))}
    }",
    category: ExampleCategory::MultiComm,
    theory: TheoryName::RhoCalculus,
};

pub static CORRELATION: Example = Example {
    name: "correlation",
    description: "Correlated receive: match request with its response by correlation ID",
    source: "{
        (request?id, response?data).{matched!({*(id) | *(data)})} |
        request!(txn42) | response!(result42)
    }",
    category: ExampleCategory::MultiComm,
    theory: TheoryName::RhoCalculus,
};

pub static MULTI_PARTY_SYNC: Example = Example {
    name: "multi_party_sync",
    description: "Multi-party synchronization: all four parties must contribute",
    source: "{
        (p1?a, p2?b, p3?c, p4?d).{consensus!({*(a) | *(b) | *(c) | *(d)})} |
        p1!(vote1) | p2!(vote2) | p3!(vote3) | p4!(vote4)
    }",
    category: ExampleCategory::MultiComm,
    theory: TheoryName::RhoCalculus,
};
