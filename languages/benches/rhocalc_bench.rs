//! Performance benchmarks for RhoCalc language execution
//!
//! These benchmarks measure the Ascent-based term rewriting engine across
//! multiple scaling dimensions to identify bottlenecks and track regressions.
//!
//! Run with: `cargo bench -p mettail-languages`
//! View reports: `open target/criterion/report/index.html`

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use mettail_languages::rhocalc::*;
use std::time::Duration;

// =============================================================================
// Test Case Generators
// =============================================================================

/// Generate n parallel zero processes: {0 | 0 | ... | 0}
fn gen_parallel_zeros(n: usize) -> String {
    if n == 0 {
        return "0".to_string();
    }
    let procs: Vec<_> = (0..n).map(|_| "0").collect();
    format!("{{{}}}", procs.join(" | "))
}

/// Generate n independent communication pairs
/// {a0!(0) | a0?x.{*(x)} | a1!(0) | a1?x.{*(x)} | ...}
fn gen_comm_pairs(n: usize) -> String {
    if n == 0 {
        return "0".to_string();
    }
    let pairs: Vec<_> = (0..n)
        .map(|i| format!("c{}!(0) | c{}?x.{{*(x)}}", i, i))
        .collect();
    format!("{{{}}}", pairs.join(" | "))
}

/// Generate a pipeline of depth n: a→b→c→...
/// {a!(0) | a?x.{b!(*(x))} | b?x.{c!(*(x))} | ... | z?x.{*(x)}}
fn gen_pipeline(depth: usize) -> String {
    if depth == 0 {
        return "0".to_string();
    }
    if depth == 1 {
        return "{a!(0) | a?x.{*(x)}}".to_string();
    }
    
    let channels: Vec<char> = ('a'..='z').take(depth).collect();
    let mut parts = vec![format!("{}!(0)", channels[0])];
    
    for i in 0..depth - 1 {
        let curr = channels[i];
        let next = channels[i + 1];
        parts.push(format!("{}?x.{{{}!(*(x))}}", curr, next));
    }
    
    let last = channels[depth - 1];
    parts.push(format!("{}?x.{{*(x)}}", last));
    
    format!("{{{}}}", parts.join(" | "))
}

/// Generate n senders racing to one receiver (non-determinism)
/// {c!(0) | c!(1) | ... | c?x.{*(x)}}
fn gen_race(n_senders: usize) -> String {
    if n_senders == 0 {
        return "c?x.{*(x)}".to_string();
    }
    let senders: Vec<_> = (0..n_senders).map(|i| format!("c!({})", i)).collect();
    format!("{{c?x.{{*(x)}} | {}}}", senders.join(" | "))
}

/// Generate 1 sender to n receivers (choice)
/// {c!(0) | c?x.{out1!(*(x))} | c?x.{out2!(*(x))} | ...}
fn gen_choice(n_receivers: usize) -> String {
    if n_receivers == 0 {
        return "c!(0)".to_string();
    }
    let receivers: Vec<_> = (0..n_receivers)
        .map(|i| format!("c?x.{{out{}!(*(x))}}", i))
        .collect();
    format!("{{c!(0) | {}}}", receivers.join(" | "))
}

/// Generate broadcast pattern: 1 sender, fanout to n channels
/// {bcast!(0) | bcast?x.{{a!(*(x)) | b!(*(x)) | ...}} | a?y.{*(y)} | b?y.{*(y)} | ...}
fn gen_fanout(n: usize) -> String {
    if n == 0 {
        return "0".to_string();
    }
    let channels: Vec<char> = ('a'..='z').take(n).collect();
    let outputs: Vec<_> = channels.iter().map(|c| format!("{}!(*(x))", c)).collect();
    let receivers: Vec<_> = channels.iter().map(|c| format!("{}?y.{{*(y)}}", c)).collect();
    
    format!(
        "{{bcast!(0) | bcast?x.{{{{{}}}}} | {}}}",
        outputs.join(" | "),
        receivers.join(" | ")
    )
}

/// Generate nested quote-drop pattern: *(@(*(@(...*(@(0))...))))
fn gen_nested_reflect(depth: usize) -> String {
    let mut result = "0".to_string();
    for _ in 0..depth {
        result = format!("*(@({}))", result);
    }
    format!("{{{}}}", result)
}

/// Generate join pattern with n channels
/// {(c0?x0, c1?x1, ...).{result} | c0!(a) | c1!(b) | ...}
fn gen_join(n: usize) -> String {
    if n == 0 {
        return "0".to_string();
    }
    let bindings: Vec<_> = (0..n).map(|i| format!("c{}?x{}", i, i)).collect();
    let drops: Vec<_> = (0..n).map(|i| format!("*(x{})", i)).collect();
    let senders: Vec<_> = (0..n).map(|i| format!("c{}!(v{})", i, i)).collect();
    
    format!(
        "{{({}).{{{{{}}}}} | {}}}",
        bindings.join(", "),
        drops.join(" | "),
        senders.join(" | ")
    )
}

/// Replication environment definitions (must be pre-substituted)
const REP_ENV: &str = r#"
dup = ^l.{l?x.{{*(x)|l!(*(x))}}}
rep = ^n.{^a.{^cont.{{$name(dup,n)|n!(a?y.{{$name(cont,y)|$name(dup,n)}})}}}}
id = ^z.{*(z)}
"#;

/// Generate replication pattern: rep(loc)(server)(id)
/// This requires environment substitution
fn gen_replication_base() -> &'static str {
    "$proc($name($name(rep, loc), server), id)"
}

// =============================================================================
// Benchmark Helper
// =============================================================================

/// Run Ascent and return metrics
struct BenchMetrics {
    term_count: usize,
    rewrite_count: usize,
    normal_form_count: usize,
}

fn run_rhocalc(input: &str) -> BenchMetrics {
    mettail_runtime::clear_var_cache();
    let parser = rhocalc::ProcParser::new();
    let term = parser.parse(input).expect("Parse failed");
    let term = term.normalize();
    
    // Create environment and substitute if needed
    let term = if input.contains('$') {
        // Parse and substitute environment
        let mut env = RhoCalcEnv::new();
        
        // Parse environment definitions
        for line in REP_ENV.lines() {
            let line = line.trim();
            if line.is_empty() || !line.contains('=') {
                continue;
            }
            let parts: Vec<_> = line.splitn(2, '=').collect();
            if parts.len() == 2 {
                let name = parts[0].trim();
                let value = parts[1].trim();
                if let Ok(val_term) = parser.parse(value) {
                    env.proc.set(name.to_string(), val_term.normalize());
                }
            }
        }
        
        term.substitute_env(&env)
    } else {
        term
    };
    
    let term = RhoCalcTerm(term);
    let results = RhoCalcLanguage::run_ascent_typed(&term);
    
    BenchMetrics {
        term_count: results.all_terms.len(),
        rewrite_count: results.rewrites.len(),
        normal_form_count: results.normal_forms().len(),
    }
}

// =============================================================================
// Benchmarks: Term Size Scaling
// =============================================================================

fn bench_size_parallel_zeros(c: &mut Criterion) {
    let mut group = c.benchmark_group("size/parallel_zeros");
    group.measurement_time(Duration::from_secs(5));
    
    for n in [1, 2, 5, 10, 20, 50].iter() {
        let input = gen_parallel_zeros(*n);
        group.throughput(Throughput::Elements(*n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &input, |b, input| {
            b.iter(|| run_rhocalc(black_box(input)))
        });
    }
    group.finish();
}

fn bench_size_comm_pairs(c: &mut Criterion) {
    let mut group = c.benchmark_group("size/comm_pairs");
    group.measurement_time(Duration::from_secs(10));
    
    for n in [1, 2, 3, 4, 5, 6].iter() {
        let input = gen_comm_pairs(*n);
        group.throughput(Throughput::Elements(*n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &input, |b, input| {
            b.iter(|| run_rhocalc(black_box(input)))
        });
    }
    group.finish();
}

// =============================================================================
// Benchmarks: Rewrite Depth
// =============================================================================

fn bench_depth_pipeline(c: &mut Criterion) {
    let mut group = c.benchmark_group("depth/pipeline");
    group.measurement_time(Duration::from_secs(5));
    
    for depth in [2, 3, 4, 5, 6, 8, 10].iter() {
        let input = gen_pipeline(*depth);
        group.throughput(Throughput::Elements(*depth as u64));
        group.bench_with_input(BenchmarkId::from_parameter(depth), &input, |b, input| {
            b.iter(|| run_rhocalc(black_box(input)))
        });
    }
    group.finish();
}

// =============================================================================
// Benchmarks: Non-determinism
// =============================================================================

fn bench_ndet_race(c: &mut Criterion) {
    let mut group = c.benchmark_group("ndet/race");
    group.measurement_time(Duration::from_secs(5));
    
    for n in [1, 2, 3, 4, 5].iter() {
        let input = gen_race(*n);
        group.throughput(Throughput::Elements(*n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &input, |b, input| {
            b.iter(|| run_rhocalc(black_box(input)))
        });
    }
    group.finish();
}

fn bench_ndet_choice(c: &mut Criterion) {
    let mut group = c.benchmark_group("ndet/choice");
    group.measurement_time(Duration::from_secs(5));
    
    for n in [1, 2, 3, 4, 5].iter() {
        let input = gen_choice(*n);
        group.throughput(Throughput::Elements(*n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &input, |b, input| {
            b.iter(|| run_rhocalc(black_box(input)))
        });
    }
    group.finish();
}

// =============================================================================
// Benchmarks: Parallelism
// =============================================================================

fn bench_parallel_fanout(c: &mut Criterion) {
    let mut group = c.benchmark_group("parallel/fanout");
    group.measurement_time(Duration::from_secs(5));
    
    for n in [2, 3, 4, 5, 6, 8].iter() {
        let input = gen_fanout(*n);
        group.throughput(Throughput::Elements(*n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &input, |b, input| {
            b.iter(|| run_rhocalc(black_box(input)))
        });
    }
    group.finish();
}

// =============================================================================
// Benchmarks: Reflection
// =============================================================================

fn bench_reflect_nested(c: &mut Criterion) {
    let mut group = c.benchmark_group("reflect/nested");
    group.measurement_time(Duration::from_secs(5));
    
    for depth in [1, 2, 3, 4, 5, 6, 8, 10].iter() {
        let input = gen_nested_reflect(*depth);
        group.throughput(Throughput::Elements(*depth as u64));
        group.bench_with_input(BenchmarkId::from_parameter(depth), &input, |b, input| {
            b.iter(|| run_rhocalc(black_box(input)))
        });
    }
    group.finish();
}

// =============================================================================
// Benchmarks: Join Patterns
// =============================================================================

fn bench_join_channels(c: &mut Criterion) {
    let mut group = c.benchmark_group("join/channels");
    group.measurement_time(Duration::from_secs(5));
    
    for n in [2, 3, 4, 5, 6].iter() {
        let input = gen_join(*n);
        group.throughput(Throughput::Elements(*n as u64));
        group.bench_with_input(BenchmarkId::from_parameter(n), &input, |b, input| {
            b.iter(|| run_rhocalc(black_box(input)))
        });
    }
    group.finish();
}

// =============================================================================
// Benchmarks: Replication (Primary Target)
// =============================================================================

fn bench_replication_basic(c: &mut Criterion) {
    let mut group = c.benchmark_group("replication");
    group.measurement_time(Duration::from_secs(10));
    group.sample_size(30);
    
    let input = gen_replication_base();
    group.bench_function("basic", |b| {
        b.iter(|| run_rhocalc(black_box(input)))
    });
    
    group.finish();
}

// =============================================================================
// Benchmark Groups
// =============================================================================

criterion_group! {
    name = size_scaling;
    config = Criterion::default().sample_size(50);
    targets = bench_size_parallel_zeros, bench_size_comm_pairs
}

criterion_group! {
    name = depth_scaling;
    config = Criterion::default().sample_size(50);
    targets = bench_depth_pipeline
}

criterion_group! {
    name = nondeterminism;
    config = Criterion::default().sample_size(50);
    targets = bench_ndet_race, bench_ndet_choice
}

criterion_group! {
    name = parallelism;
    config = Criterion::default().sample_size(50);
    targets = bench_parallel_fanout
}

criterion_group! {
    name = reflection;
    config = Criterion::default().sample_size(50);
    targets = bench_reflect_nested
}

criterion_group! {
    name = join_patterns;
    config = Criterion::default().sample_size(50);
    targets = bench_join_channels
}

criterion_group! {
    name = replication;
    config = Criterion::default().sample_size(30);
    targets = bench_replication_basic
}

criterion_main!(
    size_scaling,
    depth_scaling,
    nondeterminism,
    parallelism,
    reflection,
    join_patterns,
    replication
);
