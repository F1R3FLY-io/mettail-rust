//! Run a lowered-MeTTaIL Rholang program on a real in-memory f1r3node-rust
//! `RhoRuntime` and read ground results back — the M-RHO.0.5 execution path and
//! the substrate of the M-RHO.0.4 differential oracle.
//!
//! No disk / RocksDB / network: the runtime is backed by `InMemoryStoreManager`
//! (pure `DashMap`). Threading/scheduling are f1r3node's (RSpace + the reducer);
//! MeTTaIL only emits the `Par` program and reads the resting data.

use std::collections::HashMap;
use std::sync::Arc;

use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{BindPattern, Expr, ListParWithRandom, Par, TaggedContinuation};

use rholang::rust::interpreter::external_services::ExternalServices;
use rholang::rust::interpreter::matcher::r#match::Matcher;
use rholang::rust::interpreter::rho_runtime::{create_rho_runtime, RhoRuntime};

use rspace_plus_plus::rspace::rspace::RSpace;
use rspace_plus_plus::rspace::shared::in_mem_store_manager::InMemoryStoreManager;
use rspace_plus_plus::rspace::shared::key_value_store_manager::KeyValueStoreManager;

/// A quoted-name channel `@"<name>"` (a `Par` holding a single `GString`).
fn quoted_channel(name: &str) -> Par {
    Par {
        exprs: vec![Expr {
            expr_instance: Some(ExprInstance::GString(name.to_string())),
        }],
        ..Default::default()
    }
}

/// Pull the single ground `i64` out of a `Par` of the form `Par{exprs:[GInt(n)]}`.
fn par_as_i64(par: &Par) -> Option<i64> {
    match par.exprs.as_slice() {
        [e] => match &e.expr_instance {
            Some(ExprInstance::GInt(i)) => Some(*i),
            _ => None,
        },
        _ => None,
    }
}

/// Build an in-memory `RhoRuntime`, evaluate `program` to quiescence, and return
/// every ground integer left resting on the quoted channel `@"<out_channel>"`.
///
/// `Err` on a store/rspace failure or when evaluation reports interpreter errors
/// (so a malformed lowering surfaces, never silently "succeeds").
pub async fn run_and_read_ints(program: &str, out_channel: &str) -> Result<Vec<i64>, String> {
    let mut kvm = InMemoryStoreManager::new();
    let store = kvm
        .r_space_stores()
        .await
        .map_err(|e| format!("in-mem store: {e:?}"))?;
    let space: RSpace<Par, BindPattern, ListParWithRandom, TaggedContinuation> =
        RSpace::create(store, Arc::new(Box::new(Matcher))).map_err(|e| format!("rspace: {e:?}"))?;

    let mut runtime = create_rho_runtime(
        space,
        Arc::new(HashMap::new()), // mergeable tags: none (single-node eval)
        false,                    // init_registry: not needed for pure arithmetic
        &mut Vec::new(),          // no extra system processes
        ExternalServices::noop(), // inert — no ChromaDB/SBERT/OpenAI
    )
    .await;

    let result = runtime
        .evaluate_with_term(program)
        .await
        .map_err(|e| format!("evaluate: {e:?}"))?;
    if !result.errors.is_empty() {
        return Err(format!("evaluation errors: {:?}", result.errors));
    }

    let channel = quoted_channel(out_channel);
    let data = runtime.get_data(&channel).await;
    let mut out = Vec::new();
    for datum in data {
        for par in &datum.a.pars {
            if let Some(i) = par_as_i64(par) {
                out.push(i);
            }
        }
    }
    Ok(out)
}
