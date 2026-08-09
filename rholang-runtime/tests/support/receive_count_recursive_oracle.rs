//! Bounded specification oracle for `bench_support::count_receive_nodes`.
//!
//! This intentionally preserves the former direct/mutual recursion and is
//! called only on shallow fixtures. Production and deep tests use the
//! stack-safe driver.

use models::rhoapi::connective::ConnectiveInstance;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{EPathMap, Expr, Par};
use models::rust::epathmap_trie_codec::EPathMapMode;

pub fn count_receive_nodes(par: &Par) -> usize {
    let mut count = 0usize;
    visit_par(par, &mut count);
    count
}

fn visit_opt_par(par: &Option<Par>, count: &mut usize) {
    if let Some(par) = par {
        visit_par(par, count);
    }
}

fn visit_par(par: &Par, count: &mut usize) {
    for send in &par.sends {
        visit_opt_par(&send.chan, count);
        for datum in &send.data {
            visit_par(datum, count);
        }
    }
    for receive in &par.receives {
        *count += 1;
        for bind in &receive.binds {
            for pattern in &bind.patterns {
                visit_par(pattern, count);
            }
            visit_opt_par(&bind.source, count);
        }
        visit_opt_par(&receive.body, count);
        visit_opt_par(&receive.condition, count);
    }
    for new in &par.news {
        visit_opt_par(&new.p, count);
        for injected in new.injections.values() {
            visit_par(injected, count);
        }
    }
    for expr in &par.exprs {
        visit_expr(expr, count);
    }
    for match_node in &par.matches {
        visit_opt_par(&match_node.target, count);
        for case in &match_node.cases {
            visit_opt_par(&case.pattern, count);
            visit_opt_par(&case.source, count);
            visit_opt_par(&case.guard, count);
        }
    }
    for bundle in &par.bundles {
        visit_opt_par(&bundle.body, count);
    }
    for connective in &par.connectives {
        match connective.connective_instance.as_ref() {
            Some(ConnectiveInstance::ConnAndBody(body))
            | Some(ConnectiveInstance::ConnOrBody(body)) => {
                for par in &body.ps {
                    visit_par(par, count);
                }
            },
            Some(ConnectiveInstance::ConnNotBody(par)) => visit_par(par, count),
            _ => {},
        }
    }
    for conditional in &par.conditionals {
        visit_opt_par(&conditional.condition, count);
        visit_opt_par(&conditional.if_true, count);
        visit_opt_par(&conditional.if_false, count);
    }
}

fn visit_expr(expr: &Expr, count: &mut usize) {
    let Some(instance) = expr.expr_instance.as_ref() else {
        return;
    };
    match instance {
        ExprInstance::EListBody(list) => {
            for par in &list.ps {
                visit_par(par, count);
            }
        },
        ExprInstance::ETupleBody(tuple) => {
            for par in &tuple.ps {
                visit_par(par, count);
            }
        },
        ExprInstance::ESetBody(set) => {
            for par in &set.ps {
                visit_par(par, count);
            }
        },
        ExprInstance::EPathmapBody(pathmap) => visit_epathmap(pathmap, count),
        ExprInstance::EZipperBody(zipper) => {
            if let Some(pathmap) = &zipper.pathmap {
                visit_epathmap(pathmap, count);
            }
        },
        ExprInstance::EMapBody(map) => {
            for pair in &map.kvs {
                visit_opt_par(&pair.key, count);
                visit_opt_par(&pair.value, count);
            }
        },
        ExprInstance::EMethodBody(method) => {
            visit_opt_par(&method.target, count);
            for argument in &method.arguments {
                visit_par(argument, count);
            }
        },
        ExprInstance::ENotBody(inner) => visit_opt_par(&inner.p, count),
        ExprInstance::ENegBody(inner) => visit_opt_par(&inner.p, count),
        ExprInstance::EMultBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EDivBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EModBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EPlusBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EMinusBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::ELtBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::ELteBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EGtBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EGteBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EEqBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::ENeqBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EAndBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EOrBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EPercentPercentBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EPlusPlusBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EMinusMinusBody(inner) => {
            visit_opt_par(&inner.p1, count);
            visit_opt_par(&inner.p2, count);
        },
        ExprInstance::EMatchesBody(inner) => {
            visit_opt_par(&inner.target, count);
            visit_opt_par(&inner.pattern, count);
        },
        ExprInstance::GBool(_)
        | ExprInstance::GInt(_)
        | ExprInstance::GString(_)
        | ExprInstance::GUri(_)
        | ExprInstance::GByteArray(_)
        | ExprInstance::GDouble(_)
        | ExprInstance::GBigInt(_)
        | ExprInstance::GBigRat(_)
        | ExprInstance::GFixedPoint(_)
        | ExprInstance::EVarBody(_) => {},
    }
}

fn visit_epathmap(pathmap: &EPathMap, count: &mut usize) {
    match pathmap.mode() {
        EPathMapMode::Empty => {},
        EPathMapMode::Set => pathmap.entry_trie().for_each_entry(|entry| {
            visit_par(entry, count);
        }),
        EPathMapMode::Map => pathmap
            .for_each_map_entry(|key, value| {
                visit_par(key, count);
                visit_par(value, count);
            })
            .expect("map-mode EPathMap rejected its own map visitor"),
    }
}
