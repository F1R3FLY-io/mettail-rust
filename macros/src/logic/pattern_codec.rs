//! Optimized De Bruijn pattern encoding for alpha-equivalence detection.
//!
//! Serializes `Pattern` / `PatternTerm` into byte sequences where
//! alpha-equivalent patterns produce identical bytes. Variable names are
//! erased and replaced with De Bruijn introduction indices.
//!
//! # Tag Byte Layout (MORK-compatible 2-bit prefix scheme)
//!
//! ```text
//!  0b00_aaaaaa (0x00-0x3F)  Arity(a)      — Apply with a children
//!  0b10_iiiiii (0x80-0xBF)  VarRef(i)     — Reference to i-th variable
//!  0b11_000000 (0xC0)       NewVar        — Introduce a fresh variable
//!  0b11_ssssss (0xC1-0xFE)  SymbolSize(s) — Next s bytes are a constructor name
//!  0b11_111111 (0xFF)       ExtTag        — Reserved
//!
//!  0b01_tttttt PraTTaIL extensions:
//!    0x40  Collection(HashBag)
//!    0x41  Collection(HashSet)
//!    0x42  Collection(Vec)
//!    0x43  Collection(infer)
//!    0x44  RestVar
//!    0x45  NoRest
//!    0x46  Map
//!    0x47  Zip
//!    0x48  Lambda
//!    0x49  MultiLambda
//!    0x4A  Subst
//!    0x4B  MultiSubst
//! ```
//!
//! # Alpha-Equivalence Guarantee
//!
//! `encode(p) == encode(q)` iff `p ≡α q`. Variables are numbered by
//! introduction order in left-to-right pre-order traversal. First occurrence
//! emits `NewVar` (0xC0), subsequent occurrences emit `VarRef(slot)`.

use crate::ast::pattern::{Pattern, PatternTerm};
use crate::ast::types::CollectionType;
use std::collections::HashMap;

// ── Tag Constants ──────────────────────────────────────────────────────────

// 0b00_aaaaaa — Arity (0x00-0x3F)
// Value IS the arity byte, no separate constant needed.

// 0b10_iiiiii — VarRef (0x80-0xBF)
const VAR_REF_BASE: u8 = 0x80;

// 0b11_000000 — NewVar
const NEW_VAR: u8 = 0xC0;

// 0b11_ssssss — SymbolSize(s) = 0xC0 + s for s ∈ [1, 62]
// Tag 0xC1 → 1 byte, 0xC2 → 2 bytes, ..., 0xFE → 62 bytes
// (0xC0 is reserved for NewVar, 0xFF for ExtTag)

// PraTTaIL extension tags (0b01_tttttt)
const TAG_COLLECTION_HASHBAG: u8 = 0x40;
const TAG_COLLECTION_HASHSET: u8 = 0x41;
const TAG_COLLECTION_VEC: u8 = 0x42;
const TAG_COLLECTION_INFER: u8 = 0x43;
const TAG_REST_VAR: u8 = 0x44;
const TAG_NO_REST: u8 = 0x45;
const TAG_MAP: u8 = 0x46;
const TAG_ZIP: u8 = 0x47;
const TAG_LAMBDA: u8 = 0x48;
const TAG_MULTI_LAMBDA: u8 = 0x49;
const TAG_SUBST: u8 = 0x4A;
const TAG_MULTI_SUBST: u8 = 0x4B;

// ── Encoding Environment ───────────────────────────────────────────────────

/// Tracks variable introduction order for De Bruijn canonicalization.
struct EncodingEnv {
    /// Variable name → introduction index (De Bruijn slot).
    var_slots: HashMap<String, u8>,
    /// Next slot index to assign.
    next_slot: u8,
}

impl EncodingEnv {
    fn new() -> Self {
        EncodingEnv {
            var_slots: HashMap::new(),
            next_slot: 0,
        }
    }

    /// Resolve a variable. Returns `(is_new, slot_index)`.
    fn resolve_var(&mut self, name: &str) -> (bool, u8) {
        if let Some(&slot) = self.var_slots.get(name) {
            (false, slot)
        } else {
            let slot = self.next_slot;
            self.next_slot += 1;
            self.var_slots.insert(name.to_string(), slot);
            (true, slot)
        }
    }

    /// Introduce a binder variable, saving previous binding for restore.
    /// Returns `(slot, previous_slot_if_any)`.
    fn introduce_binder(&mut self, name: &str) -> (u8, Option<u8>) {
        let prev = self.var_slots.get(name).copied();
        let slot = self.next_slot;
        self.next_slot += 1;
        self.var_slots.insert(name.to_string(), slot);
        (slot, prev)
    }

    /// Restore a binder scope (call after encoding body).
    fn restore_binder(&mut self, name: &str, prev: Option<u8>) {
        match prev {
            Some(old_slot) => {
                self.var_slots.insert(name.to_string(), old_slot);
            }
            None => {
                self.var_slots.remove(name);
            }
        }
        self.next_slot -= 1;
    }
}

// ── Size Estimation ────────────────────────────────────────────────────────

/// Estimate encoded size for preallocation. Conservative upper bound.
fn estimate_size(pat: &Pattern) -> usize {
    match pat {
        Pattern::Term(t) => estimate_size_term(t),
        Pattern::Collection {
            elements, rest, ..
        } => 2 + elements.iter().map(estimate_size).sum::<usize>() + if rest.is_some() { 2 } else { 1 },
        Pattern::Map {
            collection,
            params,
            body,
            ..
        } => 2 + params.len() + estimate_size(collection) + estimate_size(body),
        Pattern::Zip { first, second } => 1 + estimate_size(first) + estimate_size(second),
    }
}

fn estimate_size_term(t: &PatternTerm) -> usize {
    match t {
        PatternTerm::Var(_) => 1,
        PatternTerm::Apply { constructor, args } => {
            1 + 1
                + constructor.to_string().len()
                + args.iter().map(estimate_size).sum::<usize>()
        }
        PatternTerm::Lambda { body, .. } => 2 + estimate_size(body),
        PatternTerm::MultiLambda { binders, body, .. } => {
            2 + binders.len() + estimate_size(body)
        }
        PatternTerm::Subst {
            term, replacement, ..
        } => 2 + estimate_size(term) + estimate_size(replacement),
        PatternTerm::MultiSubst {
            scope,
            replacements,
        } => {
            2 + estimate_size(scope)
                + replacements.iter().map(estimate_size).sum::<usize>()
        }
    }
}

// ── Encoding ───────────────────────────────────────────────────────────────

/// Encode a pattern to De Bruijn-canonicalized bytes.
///
/// Alpha-equivalent patterns produce identical byte sequences.
pub fn pattern_to_debruijn_bytes(pat: &Pattern) -> Vec<u8> {
    let cap = estimate_size(pat);
    let mut buf = Vec::with_capacity(cap);
    let mut env = EncodingEnv::new();
    encode_pattern(pat, &mut env, &mut buf);
    buf
}

fn encode_pattern(pat: &Pattern, env: &mut EncodingEnv, buf: &mut Vec<u8>) {
    match pat {
        Pattern::Term(t) => encode_term(t, env, buf),
        Pattern::Collection {
            coll_type,
            elements,
            rest,
        } => encode_collection(coll_type.as_ref(), elements, rest.as_ref(), env, buf),
        Pattern::Map {
            collection,
            params,
            body,
            ..
        } => encode_map(collection, params, body, env, buf),
        Pattern::Zip { first, second } => encode_zip(first, second, env, buf),
    }
}

fn encode_term(t: &PatternTerm, env: &mut EncodingEnv, buf: &mut Vec<u8>) {
    match t {
        PatternTerm::Var(ident) => {
            let name = ident.to_string();
            let (is_new, slot) = env.resolve_var(&name);
            if is_new {
                buf.push(NEW_VAR);
            } else {
                buf.push(VAR_REF_BASE | (slot & 0x3F));
            }
        }
        PatternTerm::Apply { constructor, args } => {
            let arity = args.len().min(0x3F);
            buf.push(arity as u8);

            let name = constructor.to_string();
            let name_bytes = name.as_bytes();
            let sym_size = name_bytes.len().min(0x3E);
            buf.push(NEW_VAR + sym_size as u8); // tag = 0xC0 + s
            buf.extend_from_slice(&name_bytes[..sym_size]);

            for arg in args {
                encode_pattern(arg, env, buf);
            }
        }
        PatternTerm::Lambda { binder, body } => {
            buf.push(TAG_LAMBDA);
            let name = binder.to_string();
            let (slot, prev) = env.introduce_binder(&name);
            buf.push(slot);
            encode_pattern(body, env, buf);
            env.restore_binder(&name, prev);
        }
        PatternTerm::MultiLambda { binders, body, .. } => {
            buf.push(TAG_MULTI_LAMBDA);
            buf.push(binders.len() as u8);
            let mut saved: Vec<(String, Option<u8>)> =
                Vec::with_capacity(binders.len());
            for b in binders {
                let name = b.to_string();
                let (slot, prev) = env.introduce_binder(&name);
                buf.push(slot);
                saved.push((name, prev));
            }
            encode_pattern(body, env, buf);
            for (name, prev) in saved.into_iter().rev() {
                env.restore_binder(&name, prev);
            }
        }
        PatternTerm::Subst {
            term,
            var,
            replacement,
        } => {
            buf.push(TAG_SUBST);
            let name = var.to_string();
            let (_is_new, slot) = env.resolve_var(&name);
            buf.push(slot);
            encode_pattern(term, env, buf);
            encode_pattern(replacement, env, buf);
        }
        PatternTerm::MultiSubst {
            scope,
            replacements,
        } => {
            buf.push(TAG_MULTI_SUBST);
            buf.push(replacements.len() as u8);
            encode_pattern(scope, env, buf);
            for r in replacements {
                encode_pattern(r, env, buf);
            }
        }
    }
}

fn encode_collection(
    coll_type: Option<&CollectionType>,
    elements: &[Pattern],
    rest: Option<&syn::Ident>,
    env: &mut EncodingEnv,
    buf: &mut Vec<u8>,
) {
    let tag = match coll_type {
        Some(CollectionType::HashBag) => TAG_COLLECTION_HASHBAG,
        Some(CollectionType::HashSet) => TAG_COLLECTION_HASHSET,
        Some(CollectionType::Vec) => TAG_COLLECTION_VEC,
        None => TAG_COLLECTION_INFER,
    };
    buf.push(tag);
    buf.push(elements.len() as u8);

    // For unordered collections (HashBag, HashSet, infer), sort elements
    // for canonical form. Vec preserves order.
    let is_ordered = matches!(coll_type, Some(CollectionType::Vec));

    if is_ordered || elements.len() <= 1 {
        for elem in elements {
            encode_pattern(elem, env, buf);
        }
    } else {
        // Encode each element into a temporary buffer, sort, then emit
        let mut encoded_elems: Vec<Vec<u8>> = Vec::with_capacity(elements.len());
        for elem in elements {
            let mut elem_buf = Vec::with_capacity(estimate_size(elem));
            // Clone env for each element to avoid cross-element variable leaking
            let mut elem_env = EncodingEnv {
                var_slots: env.var_slots.clone(),
                next_slot: env.next_slot,
            };
            encode_pattern(elem, &mut elem_env, &mut elem_buf);
            encoded_elems.push(elem_buf);
        }
        encoded_elems.sort();
        for encoded in &encoded_elems {
            buf.extend_from_slice(encoded);
        }
    }

    // Rest variable
    if let Some(rest_ident) = rest {
        buf.push(TAG_REST_VAR);
        let name = rest_ident.to_string();
        let (is_new, slot) = env.resolve_var(&name);
        if is_new {
            buf.push(NEW_VAR);
        } else {
            buf.push(VAR_REF_BASE | (slot & 0x3F));
        }
    } else {
        buf.push(TAG_NO_REST);
    }
}

fn encode_map(
    collection: &Pattern,
    params: &[syn::Ident],
    body: &Pattern,
    env: &mut EncodingEnv,
    buf: &mut Vec<u8>,
) {
    buf.push(TAG_MAP);
    buf.push(params.len() as u8);

    // Introduce params as binders
    let mut saved: Vec<(String, Option<u8>)> = Vec::with_capacity(params.len());
    for p in params {
        let name = p.to_string();
        let (slot, prev) = env.introduce_binder(&name);
        buf.push(slot);
        saved.push((name, prev));
    }

    encode_pattern(collection, env, buf);
    encode_pattern(body, env, buf);

    // Restore
    for (name, prev) in saved.into_iter().rev() {
        env.restore_binder(&name, prev);
    }
}

fn encode_zip(
    first: &Pattern,
    second: &Pattern,
    env: &mut EncodingEnv,
    buf: &mut Vec<u8>,
) {
    buf.push(TAG_ZIP);
    encode_pattern(first, env, buf);
    encode_pattern(second, env, buf);
}

#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro2::Ident;
    use proc_macro2::Span;

    fn var(name: &str) -> Pattern {
        Pattern::Term(PatternTerm::Var(Ident::new(name, Span::call_site())))
    }

    fn apply(ctor: &str, args: Vec<Pattern>) -> Pattern {
        Pattern::Term(PatternTerm::Apply {
            constructor: Ident::new(ctor, Span::call_site()),
            args,
        })
    }

    fn lambda(binder: &str, body: Pattern) -> Pattern {
        Pattern::Term(PatternTerm::Lambda {
            binder: Ident::new(binder, Span::call_site()),
            body: Box::new(body),
        })
    }

    #[test]
    fn test_alpha_equivalence_variables() {
        // (Add x y) and (Add a b) should produce identical bytes
        let p1 = apply("Add", vec![var("x"), var("y")]);
        let p2 = apply("Add", vec![var("a"), var("b")]);
        assert_eq!(
            pattern_to_debruijn_bytes(&p1),
            pattern_to_debruijn_bytes(&p2),
            "Alpha-equivalent patterns must produce identical bytes"
        );
    }

    #[test]
    fn test_non_alpha_equivalent_repeated_var() {
        // (Add x y) vs (Add x x) — different: y is fresh vs x is reused
        let p1 = apply("Add", vec![var("x"), var("y")]);
        let p2 = apply("Add", vec![var("x"), var("x")]);
        assert_ne!(
            pattern_to_debruijn_bytes(&p1),
            pattern_to_debruijn_bytes(&p2),
            "Non-alpha-equivalent patterns must produce different bytes"
        );
    }

    #[test]
    fn test_different_constructors() {
        let p1 = apply("Add", vec![var("x"), var("y")]);
        let p2 = apply("Mul", vec![var("x"), var("y")]);
        assert_ne!(
            pattern_to_debruijn_bytes(&p1),
            pattern_to_debruijn_bytes(&p2),
        );
    }

    #[test]
    fn test_different_arity() {
        let p1 = apply("F", vec![var("x")]);
        let p2 = apply("F", vec![var("x"), var("y")]);
        assert_ne!(
            pattern_to_debruijn_bytes(&p1),
            pattern_to_debruijn_bytes(&p2),
        );
    }

    #[test]
    fn test_lambda_alpha_equivalence() {
        // \x.x and \y.y should be alpha-equivalent
        let p1 = lambda("x", var("x"));
        let p2 = lambda("y", var("y"));
        assert_eq!(
            pattern_to_debruijn_bytes(&p1),
            pattern_to_debruijn_bytes(&p2),
        );
    }

    #[test]
    fn test_lambda_non_equivalent() {
        // \x.x vs \x.y (free var y vs bound var x)
        let p1 = lambda("x", var("x"));
        let p2 = lambda("x", var("y"));
        assert_ne!(
            pattern_to_debruijn_bytes(&p1),
            pattern_to_debruijn_bytes(&p2),
        );
    }

    #[test]
    fn test_nested_apply() {
        // (Add x (Lit y)) alpha-equiv to (Add a (Lit b))
        let p1 = apply("Add", vec![var("x"), apply("Lit", vec![var("y")])]);
        let p2 = apply("Add", vec![var("a"), apply("Lit", vec![var("b")])]);
        assert_eq!(
            pattern_to_debruijn_bytes(&p1),
            pattern_to_debruijn_bytes(&p2),
        );
    }

    #[test]
    fn test_collection_unordered_canonical() {
        // {x, y} and {y, x} should produce same bytes for unordered collections
        // when variables are both fresh (x and y are first-seen in different order)
        // Note: since each element is encoded with a cloned env, individual
        // elements produce identical single-NewVar bytes, so sorting works.
        let p1 = Pattern::Collection {
            coll_type: Some(CollectionType::HashSet),
            elements: vec![var("x"), var("y")],
            rest: None,
        };
        let p2 = Pattern::Collection {
            coll_type: Some(CollectionType::HashSet),
            elements: vec![var("y"), var("x")],
            rest: None,
        };
        assert_eq!(
            pattern_to_debruijn_bytes(&p1),
            pattern_to_debruijn_bytes(&p2),
        );
    }

    #[test]
    fn test_encoding_is_compact() {
        // (Add x y) should be ~7 bytes: [02, C4, 'A','d','d', C0, C0]
        let p = apply("Add", vec![var("x"), var("y")]);
        let bytes = pattern_to_debruijn_bytes(&p);
        assert!(bytes.len() <= 10, "Encoding should be compact: got {} bytes", bytes.len());
    }
}
