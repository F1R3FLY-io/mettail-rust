//! AST-first lowering from MeTTaIL's `rhocalc` terms to normalized Rholang `Par`.
//!
//! This module is an oracle/integration bridge for the Rho machine backend. It
//! consumes MeTTaIL/WPDA-produced `rhocalc` AST values and constructs
//! `rhoapi::Par` directly. Rholang-looking strings in docs/tests are reader
//! annotations only; they are never parsed on this execution path.

use std::collections::{BTreeMap, HashMap};

use mettail_languages::rhocalc::{Bag, List, Map, Name, Proc};
use mettail_runtime::{Binder, FreeVar, OrdVar, Var};
use models::rhoapi::{Expr, Par, ReceiveBind};
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_emap_par, new_freevar_par, new_gbigint_expr,
    new_gbigrat_expr, new_gbool_par, new_gdouble_expr, new_gfixedpoint_expr, new_gint_par,
    new_gstring_par, new_key_value_pair, new_new_par, new_receive_par, new_send_par, union,
};

const FREE_NAME_PREFIX: &str = "mtl:";
const FREE_PROC_OUTPUT: &str = "mtl#out";
pub const RHOCALC_BAG_ABI_TAG: &str = "mettail.rhocalc.bag.v1";

type BoundEnv = HashMap<FreeVar<String>, usize>;

/// Fallible rhocalc-to-Rholang-AST lowering error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RhocalcAstLowerError {
    UnsupportedProc(&'static str),
    UnsupportedName(&'static str),
    FreeVarWithoutName,
    EmptyInputJoin,
    InputArityMismatch { names: usize, binders: usize },
}

/// Lower a rhocalc process into normalized Rholang `Par`.
pub fn lower_rhocalc_proc(proc: &Proc) -> Result<Par, RhocalcAstLowerError> {
    lower_proc(proc, &BoundEnv::new())
}

/// Lower a rhocalc name into the normalized Rholang `Par` representation used
/// for channels.
pub fn lower_rhocalc_name(name: &Name) -> Result<Par, RhocalcAstLowerError> {
    lower_name(name, &BoundEnv::new())
}

fn lower_proc(proc: &Proc, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match proc {
        Proc::PZero => Ok(Par::default()),
        Proc::PDrop(name) => lower_drop(name.as_ref(), env),
        Proc::PPar(parts) => parts
            .iter_elements()
            .try_fold(Par::default(), |acc, part| Ok(acc.append(lower_proc(part, env)?))),
        Proc::POutput(channel, payload) => {
            let channel = lower_name(channel.as_ref(), env)?;
            let payload = lower_proc(payload.as_ref(), env)?;
            Ok(send_par(channel, vec![payload]))
        },
        Proc::PInputs(channels, scope) => {
            if channels.is_empty() {
                return Err(RhocalcAstLowerError::EmptyInputJoin);
            }

            let (binders, body) = scope.clone().unbind::<String>();
            if channels.len() != binders.len() {
                return Err(RhocalcAstLowerError::InputArityMismatch {
                    names: channels.len(),
                    binders: binders.len(),
                });
            }

            let sources = channels
                .iter()
                .map(|channel| lower_name(channel, env))
                .collect::<Result<Vec<_>, _>>()?;
            let extended_env = extend_env(env, &binders);
            let body = lower_proc(body.as_ref(), &extended_env)?;

            let binds = sources
                .into_iter()
                .map(|source| ReceiveBind {
                    patterns: vec![new_freevar_par(0, Vec::new())],
                    source: Some(source),
                    remainder: None,
                    free_count: 1,
                })
                .collect::<Vec<_>>();
            let locally_free = receive_locally_free(&binds, &body, binders.len());

            Ok(new_receive_par(
                binds,
                body,
                false,
                false,
                binders.len() as i32,
                locally_free.clone(),
                false,
                locally_free,
                false,
            ))
        },
        Proc::PNew(scope) => {
            let (binders, body) = scope.clone().unbind::<String>();
            let extended_env = extend_env(env, &binders);
            let body = lower_proc(body.as_ref(), &extended_env)?;
            let locally_free = filter_and_adjust_bitset(&body.locally_free, binders.len());

            Ok(new_new_par(
                binders.len() as i32,
                body,
                Vec::new(),
                BTreeMap::new(),
                locally_free.clone(),
                locally_free,
                false,
            ))
        },
        Proc::CastInt(value) => value
            .as_ref()
            .try_eval()
            .map(|value| new_gint_par(value, Vec::new(), false))
            .ok_or(RhocalcAstLowerError::UnsupportedProc("non-ground integer process")),
        Proc::CastBool(value) => value
            .as_ref()
            .try_eval()
            .map(|value| new_gbool_par(value, Vec::new(), false))
            .ok_or(RhocalcAstLowerError::UnsupportedProc("non-ground boolean process")),
        Proc::CastStr(value) => value
            .as_ref()
            .try_eval()
            .map(|value| new_gstring_par(value, Vec::new(), false))
            .ok_or(RhocalcAstLowerError::UnsupportedProc("non-ground string process")),
        Proc::PVar(var) => lower_proc_var(var, env),
        Proc::Err => Err(RhocalcAstLowerError::UnsupportedProc("error process")),
        Proc::CastBigRat(value) => value
            .as_ref()
            .try_eval()
            .map(|value| {
                let rational = value.get();
                expr_par(new_gbigrat_expr(
                    rational.numer().to_signed_bytes_be(),
                    rational.denom().to_signed_bytes_be(),
                ))
            })
            .ok_or(RhocalcAstLowerError::UnsupportedProc("non-ground big rational process")),
        Proc::CastFixed(value) => value
            .as_ref()
            .try_eval()
            .map(|value| {
                expr_par(new_gfixedpoint_expr(
                    value.unscaled().to_signed_bytes_be(),
                    value.places(),
                ))
            })
            .ok_or(RhocalcAstLowerError::UnsupportedProc("non-ground fixed-point process")),
        Proc::CastFloat(value) => value
            .as_ref()
            .try_eval()
            .map(|value| expr_par(new_gdouble_expr(value.get())))
            .ok_or(RhocalcAstLowerError::UnsupportedProc("non-ground float process")),
        Proc::CastBigInt(value) => value
            .as_ref()
            .try_eval()
            .map(|value| expr_par(new_gbigint_expr(value.get().to_signed_bytes_be())))
            .ok_or(RhocalcAstLowerError::UnsupportedProc("non-ground big integer process")),
        Proc::CastUInt32(value) => value
            .as_ref()
            .try_eval()
            .map(|value| new_gint_par(i64::from(value), Vec::new(), false))
            .ok_or(RhocalcAstLowerError::UnsupportedProc("non-ground u32 process")),
        Proc::CastList(value) => lower_list(value.as_ref(), env),
        Proc::CastBag(value) => lower_bag(value.as_ref(), env),
        Proc::CastMap(value) => lower_map(value.as_ref(), env),
        _ => Err(RhocalcAstLowerError::UnsupportedProc("computed rhocalc expression")),
    }
}

fn lower_bag(bag: &Bag, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match bag {
        Bag::BagLit(entries) => {
            let mut entries = entries.iter().collect::<Vec<_>>();
            entries.sort_by(|(lhs, _), (rhs, _)| lhs.cmp(rhs));

            let mut pairs = Vec::with_capacity(entries.len());
            for (item, count) in entries {
                let count = i64::try_from(count).map_err(|_| {
                    RhocalcAstLowerError::UnsupportedProc("bag multiplicity exceeds i64")
                })?;
                let item = lower_proc(item, env)?;
                let count = new_gint_par(count, Vec::new(), false);
                let pair_locally_free =
                    union(item.locally_free.clone(), count.locally_free.clone());
                pairs.push(new_elist_par(
                    vec![item, count],
                    pair_locally_free.clone(),
                    false,
                    None,
                    pair_locally_free,
                    false,
                ));
            }

            let pairs_locally_free = locally_free_union(&pairs);
            let pairs = new_elist_par(
                pairs,
                pairs_locally_free.clone(),
                false,
                None,
                pairs_locally_free,
                false,
            );
            let tag = GPrivateBuilder::new_par_from_string(RHOCALC_BAG_ABI_TAG.to_string());
            let locally_free = union(tag.locally_free.clone(), pairs.locally_free.clone());

            Ok(new_elist_par(
                vec![tag, pairs],
                locally_free.clone(),
                false,
                None,
                locally_free,
                false,
            ))
        },
        _ => Err(RhocalcAstLowerError::UnsupportedProc("computed bag process")),
    }
}

fn lower_list(list: &List, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match list {
        List::ListLit(items) => {
            let items = items
                .iter()
                .map(|item| lower_proc(item, env))
                .collect::<Result<Vec<_>, _>>()?;
            let locally_free = locally_free_union(&items);
            Ok(new_elist_par(items, locally_free.clone(), false, None, locally_free, false))
        },
        _ => Err(RhocalcAstLowerError::UnsupportedProc("computed list process")),
    }
}

fn lower_map(map: &Map, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match map {
        Map::MapLit(entries) => {
            let mut pairs = Vec::with_capacity(entries.len());
            let mut locally_free = Vec::new();

            for (key, value) in entries.iter() {
                let key = lower_proc(key, env)?;
                let value = lower_proc(value, env)?;
                locally_free = union(
                    locally_free,
                    union(key.locally_free.clone(), value.locally_free.clone()),
                );
                pairs.push(new_key_value_pair(key, value));
            }

            Ok(new_emap_par(pairs, locally_free.clone(), false, None, locally_free, false))
        },
        _ => Err(RhocalcAstLowerError::UnsupportedProc("computed map process")),
    }
}

fn lower_drop(name: &Name, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match name {
        Name::NQuote(proc) => lower_proc(proc.as_ref(), env),
        Name::NVar(var) => lower_name_var(var, env),
        _ => Err(RhocalcAstLowerError::UnsupportedName("computed rhocalc name")),
    }
}

fn lower_name(name: &Name, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match name {
        Name::NQuote(proc) => lower_proc(proc.as_ref(), env),
        Name::NVar(var) => lower_name_var(var, env),
        _ => Err(RhocalcAstLowerError::UnsupportedName("computed rhocalc name")),
    }
}

fn lower_name_var(var: &OrdVar, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match &var.0 {
        Var::Free(free_var) => {
            if let Some(index) = env.get(free_var) {
                Ok(new_boundvar_par(*index as i32, Vec::new(), false))
            } else {
                let name = pretty_var_name(free_var)?;
                Ok(new_gstring_par(format!("{FREE_NAME_PREFIX}{name}"), Vec::new(), false))
            }
        },
        Var::Bound(_) => Err(RhocalcAstLowerError::UnsupportedName("unopened bound name variable")),
    }
}

fn lower_proc_var(var: &OrdVar, env: &BoundEnv) -> Result<Par, RhocalcAstLowerError> {
    match &var.0 {
        Var::Free(free_var) => {
            if let Some(index) = env.get(free_var) {
                Ok(new_boundvar_par(*index as i32, Vec::new(), false))
            } else {
                let name = pretty_var_name(free_var)?;
                Ok(send_par(
                    new_gstring_par(FREE_PROC_OUTPUT.to_string(), Vec::new(), false),
                    vec![new_gstring_par(format!("{FREE_NAME_PREFIX}{name}"), Vec::new(), false)],
                ))
            }
        },
        Var::Bound(_) => {
            Err(RhocalcAstLowerError::UnsupportedProc("unopened bound process variable"))
        },
    }
}

fn pretty_var_name(var: &FreeVar<String>) -> Result<&str, RhocalcAstLowerError> {
    var.pretty_name
        .as_deref()
        .ok_or(RhocalcAstLowerError::FreeVarWithoutName)
}

fn extend_env(env: &BoundEnv, binders: &[Binder<String>]) -> BoundEnv {
    let width = binders.len();
    let mut extended = env
        .iter()
        .map(|(var, index)| (var.clone(), index + width))
        .collect::<BoundEnv>();

    for (formal_index, binder) in binders.iter().enumerate() {
        extended.insert(binder.0.clone(), width - 1 - formal_index);
    }

    extended
}

fn send_par(channel: Par, data: Vec<Par>) -> Par {
    let locally_free = data
        .iter()
        .fold(channel.locally_free.clone(), |acc, item| union(acc, item.locally_free.clone()));
    new_send_par(channel, data, false, locally_free.clone(), false, locally_free, false)
}

fn locally_free_union(parts: &[Par]) -> Vec<u8> {
    parts
        .iter()
        .fold(Vec::new(), |acc, part| union(acc, part.locally_free.clone()))
}

fn expr_par(expr: Expr) -> Par {
    Par::default().with_exprs(vec![expr])
}

fn receive_locally_free(binds: &[ReceiveBind], body: &Par, bind_count: usize) -> Vec<u8> {
    let sources = binds
        .iter()
        .filter_map(|bind| bind.source.as_ref())
        .fold(Vec::new(), |acc, source| union(acc, source.locally_free.clone()));
    union(sources, filter_and_adjust_bitset(&body.locally_free, bind_count))
}

fn filter_and_adjust_bitset(bitset: &[u8], bind_count: usize) -> Vec<u8> {
    let adjusted = bitset
        .iter()
        .enumerate()
        .filter_map(|(index, bit)| {
            if *bit != 0 && index >= bind_count {
                Some(index - bind_count)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    bitvec_from_indices(&adjusted)
}

fn bitvec_from_indices(indices: &[usize]) -> Vec<u8> {
    let Some(max_index) = indices.iter().copied().max() else {
        return Vec::new();
    };

    let mut bitset = vec![0; max_index + 1];
    for index in indices {
        bitset[*index] = 1;
    }
    bitset
}
