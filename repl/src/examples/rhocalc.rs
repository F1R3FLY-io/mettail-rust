// RhoCalc example processes for the REPL
//
// Demonstrates various communication patterns in the Rho Calculus

use super::{Example, ExampleCategory, LanguageName};

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
    source: "{a!(0) | for(x <- a){*(x)}}",
    category: ExampleCategory::Simple,
    language: LanguageName::RhoCalculus,
};

pub static SEQUENTIAL: Example = Example {
    name: "sequential",
    description: "Two independent channels communicating in parallel",
    source: "{a!(0) | for(x <- a){*(x)} | b!(0) | for(y <- b){*(y)}}",
    category: ExampleCategory::Simple,
    language: LanguageName::RhoCalculus,
};

pub static REFLECTION: Example = Example {
    name: "reflection",
    description: "Quote/drop cycle demonstrating reflection",
    source: "{for(x <- @(0)){*x} | @(0)!(0)}",
    category: ExampleCategory::Simple,
    language: LanguageName::RhoCalculus,
};

//=============================================================================
// BRANCHING EXAMPLES
//=============================================================================

pub static CHOICE: Example = Example {
    name: "choice",
    description: "Non-deterministic choice: multiple listeners on same channel",
    source: "{a!(0) | for(x <- a){x!(0)} | for(y <- a){y!(0)}}",
    category: ExampleCategory::Branching,
    language: LanguageName::RhoCalculus,
};

pub static RACE: Example = Example {
    name: "race",
    description: "Race condition: multiple senders, one listener",
    source: "{a!(0) | a!(1) | for(x <- a){*(x)}}",
    category: ExampleCategory::Branching,
    language: LanguageName::RhoCalculus,
};

//=============================================================================
// COMPLEX PATTERNS
//=============================================================================

pub static FORWARD: Example = Example {
    name: "forward",
    description: "Relay messages between channels (forwarder pattern)",
    source: "{a!(0) | for(x <- a){b!(*(x))} | for(y <- b){*(y)}}",
    category: ExampleCategory::Complex,
    language: LanguageName::RhoCalculus,
};

pub static CIRCULAR: Example = Example {
    name: "circular",
    description: "Circular communication (infinite loop, no normal form)",
    source: "{a!(0) | for(x <- a){b!(*(x))} | for(y <- b){a!(*(y))}}",
    category: ExampleCategory::Complex,
    language: LanguageName::RhoCalculus,
};

pub static HANDSHAKE: Example = Example {
    name: "handshake",
    description: "Three-way handshake protocol",
    source: "{a!(0) | for(x <- a){{b!(*(x)) | for(z <- c){*(z)}}} | for(y <- b){c!(*(y))}}",
    category: ExampleCategory::Complex,
    language: LanguageName::RhoCalculus,
};

//=============================================================================
// PARALLEL COMPUTATION
//=============================================================================

pub static MULTI_PATH: Example = Example {
    name: "multi_path",
    description: "Multiple concurrent communications with dependencies (50 terms, 66 rewrites)",
    source: "{
        a!(0) |
        for(x0 <- a){ {x0!(0) | for(y1 <- b){y1!(*(a))}} } |
        b!(0) |
        for(x1 <- b){a!(*(b))} |
        c!(0) |
        for(x2 <- c){x2!(0)} |
        for(y0 <- @(0)){*(y0)}
    }",
    category: ExampleCategory::Parallel,
    language: LanguageName::RhoCalculus,
};

pub static PARALLEL: Example = Example {
    name: "parallel",
    description: "Four independent parallel processes (many execution orders)",
    source: "{
        a!(0) | for(x <- a){*(x)  } |
        b!(0) | for(y <- b){*(y)  } |
        c!(0) | for(z <- c){*(z)  } |
        d!(0) | for(w <- d){*(w)  }
    }",
    category: ExampleCategory::Parallel,
    language: LanguageName::RhoCalculus,
};

pub static BARRIER: Example = Example {
    name: "barrier",
    description: "Barrier synchronization: wait for all inputs",
    source: "{a!(0) | b!(0) | for(x <- a){for(y <- b){{*(x) | *(y)}}}}",
    category: ExampleCategory::Parallel,
    language: LanguageName::RhoCalculus,
};

//=============================================================================
// ADVANCED PATTERNS
//=============================================================================

pub static SPAWN: Example = Example {
    name: "spawn",
    description: "Recursive spawning: process creates new processes",
    source: "{a!(0) | for(x <- a){{a!(*(x)) | for(y <- a){*(y)}}}",
    category: ExampleCategory::Advanced,
    language: LanguageName::RhoCalculus,
};

pub static FRESH_NAMES: Example = Example {
    name: "fresh_names",
    description: "Name generation via bound variables (capability passing)",
    source: "{for(chan <- new){{chan!(0) | for(x <- chan){*(x)}}} | new!(@(0))}",
    category: ExampleCategory::Advanced,
    language: LanguageName::RhoCalculus,
};

pub static CONTRACT: Example = Example {
    name: "contract",
    description: "Contract net: broadcast request, collect responses",
    source: "{req!(0) | for(x <- req){{resp1!(*(x)) | resp2!(*(x))}} | for(a <- resp1){*(a)  } | for(b <- resp2){*(b)  }}",
    category: ExampleCategory::Advanced,
    language: LanguageName::RhoCalculus,
};

pub static DEADLOCK: Example = Example {
    name: "deadlock",
    description: "Deadlock: circular dependency, no progress possible",
    source: "{for(x <- a){for(y <- b){{*(x) | *(y)}}} | for(z <- b){a!(z)}}",
    category: ExampleCategory::Advanced,
    language: LanguageName::RhoCalculus,
};

pub static PHILOSOPHERS: Example = Example {
    name: "philosophers",
    description: "Dining philosophers (2): resource contention",
    source: "{
        fork1!(0) | fork2!(0) |
        for(f1 <- fork1){for(f2 <- fork2){done1!({*(f1) | *(f2)})}} |
        for(f2 <- fork2){for(f1 <- fork1){done2!({*(f2) | *(f1)})}}
    }",
    category: ExampleCategory::Advanced,
    language: LanguageName::RhoCalculus,
};

pub static REPLICATED_INPUT: Example = Example {
    name: "replicated_input",
    description: "Replication encoding: persistent input listener",
    source: "{
        for(y <- dup){ {*(y) | dup!(*(y))} },
        dup!(for(x <- req){
            { resp!(*(x)) | for(y <- dup){ {*(y) | dup!(*(y))} } }
        }),
        req!(0)
    }",
    category: ExampleCategory::Advanced,
    language: LanguageName::RhoCalculus,
};

pub static DROP_QUOTE_TEST: Example = Example {
    name: "drop_quote_test",
    description: "Test the *@(P) => P rewrite rule",
    source: "{*(@(0)) | a!(0)}",
    category: ExampleCategory::EdgeCase,
    language: LanguageName::RhoCalculus,
};

//=============================================================================
// PERFORMANCE BENCHMARKS
//=============================================================================

pub static FANOUT: Example = Example {
    name: "fanout",
    description: "Wide fanout: one-to-many broadcast (performance benchmark)",
    source: "{
        bcast!(0) |
        for(x <- bcast){{a!(*x) | b!(*x) | c!(*x) | d!(*x) | e!(*x) | f!(*x) | g!(*x) | h!(*x)}},
        for(y <- a){*(y)  } | for(y <- b){*(y)  } | for(y <- c){*(y)  } | for(y <- d){*(y)  } |
        for(y <- e){*(y)  } | for(y <- f){*(y)  } | for(y <- g){*(y)  } | for(y <- h){*(y)  }
    }",
    category: ExampleCategory::Performance,
    language: LanguageName::RhoCalculus,
};

pub static PIPELINE: Example = Example {
    name: "pipeline",
    description: "Deep pipeline: sequential message passing (depth benchmark)",
    source: "{
        a!(0) |
        for(x <- a){b!(*(x))} |
        for(x <- b){c!(*(x))} |
        for(x <- c){d!(*(x))} |
        for(x <- d){e!(*(x))} |
        for(x <- e){f!(*(x))} |
        for(x <- f){*(x)  }
    }",
    category: ExampleCategory::Performance,
    language: LanguageName::RhoCalculus,
};

//=============================================================================
// EDGE CASES
//=============================================================================

pub static EMPTY: Example = Example {
    name: "empty",
    description: "Empty parallel process (tests identity normalization)",
    source: "{}",
    category: ExampleCategory::EdgeCase,
    language: LanguageName::RhoCalculus,
};

pub static SELF_COMM: Example = Example {
    name: "self_comm",
    description: "Self-communication (infinite loop)",
    source: "{for(y <- x){x!(*(y))} | x!(@(0))}",
    category: ExampleCategory::EdgeCase,
    language: LanguageName::RhoCalculus,
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
    language: LanguageName::RhoCalculus,
};

pub static JOIN_BARRIER: Example = Example {
    name: "join_barrier",
    description: "Join barrier: cleaner than nested for-loops",
    source: "{
        (ready1?x, ready2?y, ready3?z).{go!({*(x) | *(y) | *(z)})} |
        ready1!(a) | ready2!(b) | ready3!(c)
    }",
    category: ExampleCategory::MultiComm,
    language: LanguageName::RhoCalculus,
};

pub static JOIN_SAME_CHANNEL: Example = Example {
    name: "join_same_channel",
    description: "Join on same channel: consume two distinct messages atomically",
    source: "{(c?x, c?y).{{*(x) | *(y)}} | c!(a) | c!(b)}",
    category: ExampleCategory::MultiComm,
    language: LanguageName::RhoCalculus,
};

pub static ATOMIC_PAIR: Example = Example {
    name: "atomic_pair",
    description: "Atomic pair receive: prevents partial consumption",
    source: "{
        (key?k, value?v).{store!({*(k) | *(v)})} |
        key!(name) | value!(data)
    }",
    category: ExampleCategory::MultiComm,
    language: LanguageName::RhoCalculus,
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
    language: LanguageName::RhoCalculus,
};

pub static RESOURCE_LOCK: Example = Example {
    name: "resource_lock",
    description: "Atomic resource acquisition: acquire both forks or neither",
    source: "{
        fork1!(f1) | fork2!(f2) |
        (fork1?a, fork2?b).{eating!({*(a) | *(b)})}
    }",
    category: ExampleCategory::MultiComm,
    language: LanguageName::RhoCalculus,
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
    language: LanguageName::RhoCalculus,
};

pub static CORRELATION: Example = Example {
    name: "correlation",
    description: "Correlated receive: match request with its response by correlation ID",
    source: "{
        (request?id, response?data).{matched!({*(id) | *(data)})} |
        request!(txn42) | response!(result42)
    }",
    category: ExampleCategory::MultiComm,
    language: LanguageName::RhoCalculus,
};

pub static MULTI_PARTY_SYNC: Example = Example {
    name: "multi_party_sync",
    description: "Multi-party synchronization: all four parties must contribute",
    source: "{
        (p1?a, p2?b, p3?c, p4?d).{consensus!({*(a) | *(b) | *(c) | *(d)})} |
        p1!(vote1) | p2!(vote2) | p3!(vote3) | p4!(vote4)
    }",
    category: ExampleCategory::MultiComm,
    language: LanguageName::RhoCalculus,
};
