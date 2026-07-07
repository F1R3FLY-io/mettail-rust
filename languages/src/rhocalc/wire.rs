use super::{Bag, Bool, Int, List, Map, Proc, Set, Str};
use crate::rhocalc::runtime::normalize_bag_elements;
use mettail_runtime::{HashBag, HashMapLit, HashSetLit};
use prost::Message;

pub(crate) mod rho_proto {
    include!(concat!(env!("OUT_DIR"), "/rhoapi.rs"));
}

use rho_proto::expr::ExprInstance;
use rho_proto::{EList, EMap, ESet, Expr, KeyValuePair, Par};

#[derive(Debug)]
pub(crate) enum WireError {
    UnsupportedProc,
    NonLiteralCollection,
}

fn sort_pars(pars: &mut [Par]) {
    pars.sort_by_key(|left| left.encode_to_vec());
}

fn sort_map_entries(entries: &mut [(Par, Par)]) {
    entries.sort_by_key(|(key, _)| key.encode_to_vec());
}

fn proc_to_par(proc: &Proc) -> Result<Par, WireError> {
    match proc {
        Proc::CastInt(inner) => match inner.as_ref() {
            Int::NumLit(value) => Ok(Par {
                exprs: vec![Expr {
                    expr_instance: Some(ExprInstance::GInt(*value)),
                }],
            }),
            _ => Err(WireError::UnsupportedProc),
        },
        Proc::CastBool(inner) => match inner.as_ref() {
            Bool::BoolLit(value) => Ok(Par {
                exprs: vec![Expr {
                    expr_instance: Some(ExprInstance::GBool(*value)),
                }],
            }),
            _ => Err(WireError::UnsupportedProc),
        },
        Proc::CastStr(inner) => match inner.as_ref() {
            Str::StringLit(value) => Ok(Par {
                exprs: vec![Expr {
                    expr_instance: Some(ExprInstance::GString(value.clone())),
                }],
            }),
            _ => Err(WireError::UnsupportedProc),
        },
        Proc::CastList(list) => match list.as_ref() {
            List::ListLit(elements) => {
                let ps = elements
                    .iter()
                    .map(proc_to_par)
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Par {
                    exprs: vec![Expr {
                        expr_instance: Some(ExprInstance::EListBody(EList { ps })),
                    }],
                })
            },
            _ => Err(WireError::NonLiteralCollection),
        },
        Proc::CastSet(set) => match set.as_ref() {
            Set::SetLit(elements) => {
                let mut ps = elements
                    .iter()
                    .map(proc_to_par)
                    .collect::<Result<Vec<_>, _>>()?;
                sort_pars(&mut ps);
                Ok(Par {
                    exprs: vec![Expr {
                        expr_instance: Some(ExprInstance::ESetBody(ESet { ps })),
                    }],
                })
            },
            _ => Err(WireError::NonLiteralCollection),
        },
        Proc::CastMap(map) => match map.as_ref() {
            Map::MapLit(entries) => {
                let mut pairs = entries
                    .iter()
                    .map(|(key, value)| Ok((proc_to_par(key)?, proc_to_par(value)?)))
                    .collect::<Result<Vec<_>, WireError>>()?;
                sort_map_entries(&mut pairs);
                Ok(Par {
                    exprs: vec![Expr {
                        expr_instance: Some(ExprInstance::EMapBody(EMap {
                            kvs: pairs
                                .into_iter()
                                .map(|(key, value)| KeyValuePair {
                                    key: Some(key),
                                    value: Some(value),
                                })
                                .collect(),
                        })),
                    }],
                })
            },
            _ => Err(WireError::NonLiteralCollection),
        },
        Proc::CastBag(bag) => match bag.as_ref() {
            Bag::BagLit(elements) => {
                let normalized = normalize_bag_elements(elements);
                let mut entries: Vec<(Par, usize)> = normalized
                    .iter()
                    .map(|(elem, count)| Ok((proc_to_par(elem)?, count)))
                    .collect::<Result<Vec<_>, WireError>>()?;
                entries.sort_by_key(|(par, _)| par.encode_to_vec());
                let mut ps = Vec::new();
                for (par, count) in entries {
                    for _ in 0..count {
                        ps.push(par.clone());
                    }
                }
                Ok(Par {
                    exprs: vec![Expr {
                        expr_instance: Some(ExprInstance::EListBody(EList { ps })),
                    }],
                })
            },
            _ => Err(WireError::NonLiteralCollection),
        },
        _ => Err(WireError::UnsupportedProc),
    }
}

pub(crate) fn collection_to_bytes(proc: &Proc) -> Result<Vec<u8>, WireError> {
    let par = proc_to_par(proc)?;
    Ok(par.encode_to_vec())
}

pub(crate) fn collection_to_byte_array_proc(proc: &Proc) -> Result<Proc, WireError> {
    let bytes = collection_to_bytes(proc)?;
    Ok(Proc::CastBytes(std::sync::Arc::new(super::Bytes::StringLit(hex::encode(bytes)))))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn list_123_matches_f1r3fly_reference() {
        let proc = Proc::CastList(std::sync::Arc::new(List::ListLit(vec![
            Proc::CastInt(std::sync::Arc::new(Int::NumLit(1))),
            Proc::CastInt(std::sync::Arc::new(Int::NumLit(2))),
            Proc::CastInt(std::sync::Arc::new(Int::NumLit(3))),
        ])));
        let bytes = collection_to_bytes(&proc).expect("encode list");
        assert_eq!(hex::encode(bytes), "2a15a201120a042a0210020a042a0210040a042a021006");
    }

    #[test]
    fn set_123_matches_f1r3fly_reference() {
        let proc = Proc::CastSet(std::sync::Arc::new(Set::SetLit({
            let mut set = HashSetLit::new();
            set.insert(Proc::CastInt(std::sync::Arc::new(Int::NumLit(1))));
            set.insert(Proc::CastInt(std::sync::Arc::new(Int::NumLit(2))));
            set.insert(Proc::CastInt(std::sync::Arc::new(Int::NumLit(3))));
            set
        })));
        let bytes = collection_to_bytes(&proc).expect("encode set");
        assert_eq!(hex::encode(bytes), "2a15b201120a042a0210020a042a0210040a042a021006");
    }

    #[test]
    fn map_12_matches_f1r3fly_reference() {
        let mut map = HashMapLit::new();
        map.insert(
            Proc::CastInt(std::sync::Arc::new(Int::NumLit(1))),
            Proc::CastInt(std::sync::Arc::new(Int::NumLit(10))),
        );
        map.insert(
            Proc::CastInt(std::sync::Arc::new(Int::NumLit(2))),
            Proc::CastInt(std::sync::Arc::new(Int::NumLit(20))),
        );
        let proc = Proc::CastMap(std::sync::Arc::new(Map::MapLit(map)));
        let bytes = collection_to_bytes(&proc).expect("encode map");
        assert_eq!(
            hex::encode(bytes),
            "2a1fba011c0a0c0a042a02100212042a0210140a0c0a042a02100412042a021028"
        );
    }

    #[test]
    fn nested_list_matches_reference() {
        let proc = Proc::CastList(std::sync::Arc::new(List::ListLit(vec![
            Proc::CastList(std::sync::Arc::new(List::ListLit(vec![
                Proc::CastInt(std::sync::Arc::new(Int::NumLit(1))),
                Proc::CastInt(std::sync::Arc::new(Int::NumLit(2))),
            ]))),
            Proc::CastList(std::sync::Arc::new(List::ListLit(vec![Proc::CastInt(std::sync::Arc::new(Int::NumLit(3)))]))),
        ])));
        let bytes = collection_to_bytes(&proc).expect("encode nested list");
        assert_eq!(
            hex::encode(bytes),
            "2a23a201200a112a0fa2010c0a042a0210020a042a0210040a0b2a09a201060a042a021006"
        );
    }

    #[test]
    fn bag_multiset_matches_reference() {
        let mut bag = HashBag::new();
        bag.insert(Proc::CastInt(std::sync::Arc::new(Int::NumLit(1))));
        bag.insert(Proc::CastInt(std::sync::Arc::new(Int::NumLit(2))));
        bag.insert(Proc::CastInt(std::sync::Arc::new(Int::NumLit(2))));
        let proc = Proc::CastBag(std::sync::Arc::new(Bag::BagLit(bag)));
        let bytes = collection_to_bytes(&proc).expect("encode bag");
        assert_eq!(hex::encode(bytes), "2a15a201120a042a0210020a042a0210040a042a021004");
    }
}
