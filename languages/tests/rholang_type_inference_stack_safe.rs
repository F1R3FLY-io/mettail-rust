use std::sync::Arc;

use mettail_languages::rholang::{Proc, RholangLanguage, RholangTerm, RholangTermInner};

#[path = "support/rholang_type_inference_recursive_oracle.rs"]
mod recursive_oracle;

const DEPTH: usize = 20_000;
const STACK_BYTES: usize = 256 * 1024;

fn parse_proc(source: &str) -> Proc {
    Proc::parse(source).unwrap_or_else(|error| panic!("failed to parse `{source}`: {error}"))
}

fn snapshot(
    infos: impl IntoIterator<Item = mettail_runtime::VarTypeInfo>,
) -> Vec<(String, String)> {
    infos
        .into_iter()
        .map(|info| (info.name, info.ty.to_string()))
        .collect()
}

#[test]
fn iterative_type_inference_matches_recursive_oracle_on_receive_corpus() {
    let corpus = [
        "for(y <- x){*(y)}",
        "for(y <- x){y}",
        "for(x <- c where x > 0){*x}",
        "for(x <- c1 & y <- c2){*x | y}",
        "for(x <- c1; y <- c2){*x | y}",
        "for(x <- c){for(y <- d){*x | y}}",
        "for(@x <- @\"c\"){x}",
        "for(x <- c where true){for(y <- d where y > 0){*x | y}}",
    ];

    for source in corpus {
        mettail_runtime::clear_var_cache();
        let proc = parse_proc(source);
        let expected = snapshot(recursive_oracle::infer_var_types(&proc));
        let term = RholangTerm(RholangTermInner::Proc(proc));
        let actual = snapshot(RholangLanguage.infer_var_types(&term));
        assert_eq!(actual, expected, "recursive/PDA mismatch for `{source}`");
    }
}

#[test]
fn receive_type_inference_is_stack_safe_at_depth_20k() {
    mettail_runtime::clear_var_cache();
    let fixture = parse_proc("for(y <- x){y}");
    let rows = match &fixture {
        Proc::PForUser(rows, _) => rows.clone(),
        _ => panic!("receive fixture did not parse as PForUser"),
    };
    let leaf = parse_proc("y");

    std::thread::Builder::new()
        .name("rholang-type-inference-depth-gate".into())
        .stack_size(STACK_BYTES)
        .spawn(move || {
            let mut body = leaf;
            for _ in 0..DEPTH {
                body = Proc::GuardThen(Arc::new(Proc::PZero), Arc::new(body));
            }
            let term = RholangTerm(RholangTermInner::Proc(Proc::PForUser(rows, Arc::new(body))));
            let infos = RholangLanguage.infer_var_types(&term);
            let y = infos
                .iter()
                .find(|info| info.name == "y")
                .expect("receive-bound y");
            assert_eq!(y.ty.to_string(), "Proc");
        })
        .expect("spawn depth-gate thread")
        .join()
        .expect("20k-deep type-inference gate");
}
