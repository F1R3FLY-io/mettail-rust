//! Prototype: the cost endofunctor `cost` as an `ascent!` program over a
//! relational encoding of a decorated `LanguageDef` (a continued-interactive MILS).
//!
//! The rule set is GENERIC: it is keyed entirely off the decoration relations
//! (`contact`, `program_intro`, `env_intro`, `env_cont_on_contact`, `cut`) and the
//! spec's own facts. No constructor names, sorts, or arities are hardcoded.
//! `main` feeds in two decorated specs as fact-sets — untyped lambda (rigid K,
//! degenerate Ke => only R1) and a minimal communication calculus (AC K =>
//! the full five-rule lattice) — to exercise the transform; neither is special-cased.
//!
//! Output is the cost-accounted MILS, read back from the `out_*` relations and
//! pretty-printed. Check the emitted Comm_R1..Comm_R5 against §4.7 of the
//! cost-accounted-rho paper, and Beta_R1 against §8.3 of the cost-endofunctor paper.

use ascent::ascent;
use std::collections::HashMap;

type Sym = String;
type Id = u32;

// ----- pure helpers usable inside ascent rule heads/bodies -----

/// The lifted contact constructor K (made polymorphic by C); realized as a
/// distinctly-labelled constructor since the framework is monomorphic per sort.
fn meter(k: &str) -> String {
    format!("{k}__meter")
}
fn wrap_ctor() -> String {
    "Wrap".to_string()
}
fn scons_ctor() -> String {
    "SCons".to_string()
}
fn compose_ctor() -> String {
    "SCompose".to_string()
}

/// Re-sort a continuation slot's type to the wrapped sort T ("wrapping by
/// construction"). Codomain of an abstraction is lifted to T; the domain
/// (binder type) is left to the source — correct for quoting calculi (rho:
/// `[Name -> Proc]` => `[Name -> T]`). Non-quoting calculi (lambda) want the
/// binder to range over T as well; that finer point is noted, not yet modelled,
/// and does not affect the rule schemes (lambda is rigid => R1 only).
fn lift_ty(kind: &str, ty: &str) -> String {
    if kind == "abstr" {
        if let Some(inner) = ty.trim().strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
            if let Some((d, _c)) = inner.split_once("->") {
                return format!("[{}-> T]", d);
            }
        }
        "[T -> T]".to_string()
    } else {
        "T".to_string()
    }
}

/// Content-hashed id for a synthesized output pattern node, namespaced by
/// (scheme, role) and the cut's name. Deterministic, collision-resistant enough
/// for the prototype, and disjoint from reify ids (which stay below 0x8000_0000).
fn nid(scheme: &str, role: &str, name: &str) -> Id {
    let key = format!("{scheme}|{role}|{name}");
    let mut h: u32 = 2166136261;
    for b in key.bytes() {
        h ^= b as u32;
        h = h.wrapping_mul(16777619);
    }
    0x8000_0000 | (h & 0x7fff_ffff)
}

fn rname(name: &str, scheme: &str) -> String {
    format!("{name}_{scheme}")
}

ascent! {
    // ===================== INPUT: relational encoding of the decorated MILS =====================
    relation sort(Sym);                              // a syntactic category
    relation term(Sym, Sym);                         // (constructor label, result category)
    relation param(Sym, u32, Sym, Sym, Sym);         // (label, idx, pname, kind, ty)  kind: simple|abstr|coll
    relation param_binder(Sym, u32, Sym);            // (label, idx, binder-var) for abstr params
    relation eqn_mentions(Sym);                      // constructor named anywhere in equations
    relation comm_collection(Sym);                   // constructor whose AC-ness lives in a bag/set sort
    relation rewrite_rule(Sym, Id, Id);              // (rule name, lhs root id, rhs root id)
    relation pat_node(Id, Sym);                      // (node id, constructor)
    relation pat_child(Id, u32, Id);                 // (parent, idx, child)
    relation pat_var(Id, Sym);                       // (node id, metavariable)

    // decorations marking continued-interactive structure
    relation contact(Sym);                           // K
    relation program_intro(Sym, i64, u32);           // (label, surface idx (-1 = none), continuation idx)
    relation env_intro(Sym, i64, u32);               // (label, surface idx, continuation idx)
    relation env_cont_on_contact(Sym, u32);          // degenerate Ke: contact slot is the env continuation
    relation cut(Sym);                               // rewrite-rule name that is a cut

    // ===================== DERIVED: preconditions & cut anatomy =====================
    relation constrained(Sym);                       // K's positional surface is NOT free
    constrained(k) <-- contact(k), eqn_mentions(k);
    constrained(k) <-- contact(k), comm_collection(k);

    // Prototype stand-in for the OSLF check: a nominal surface is required exactly
    // when K is constrained. Reject an intro that lacks one.
    relation reject(Sym);
    reject(format!("intro `{l}` needs a nominal surface: its contact is constrained"))
        <-- program_intro(l, -1, _c), contact(k), constrained(k), cut(n),
            rewrite_rule(n, lhs, _), pat_node(lhs, k);

    relation cut_k(Sym, Sym);                        // (cut, the contact K heading its LHS)
    cut_k(n, k) <-- cut(n), rewrite_rule(n, l, _), pat_node(l, k), contact(k);

    relation cut_lr(Sym, Id, Id);                    // (cut, LHS root, RHS root)
    cut_lr(n, l, r) <-- cut(n), rewrite_rule(n, l, r);

    relation cut_constrained(Sym);
    cut_constrained(n) <-- cut_k(n, k), constrained(k);

    relation cut_prog(Sym, Id);                      // (cut, program-introduction subterm A)
    cut_prog(n, a) <-- cut_lr(n, l, _), pat_child(l, _, a), pat_node(a, ca), program_intro(ca, _, _);
    relation cut_env(Sym, Id);                       // (cut, environment-introduction subterm B)
    cut_env(n, b) <-- cut_lr(n, l, _), pat_child(l, _, b), pat_node(b, cb), env_intro(cb, _, _);

    // ===================== OUTPUT: the cost-accounted MILS =====================
    relation out_sort(Sym);
    relation out_term(Sym, Sym);
    relation out_param(Sym, u32, Sym, Sym, Sym);
    relation out_param_binder(Sym, u32, Sym);
    relation out_rewrite_rule(Sym, Id, Id);
    relation out_pat_node(Id, Sym);
    relation out_pat_child(Id, u32, Id);
    relation out_pat_var(Id, Sym);

    // --- (1) carry sorts, adjoin the metering sorts ---
    out_sort(s.clone()) <-- sort(s);
    out_sort("Sig".to_string());
    out_sort("T".to_string());
    out_sort("Stk".to_string());
    out_sort("Cfg".to_string());

    // --- (2) carry term declarations; re-sort marked continuation slots to T ---
    out_term(l.clone(), c.clone()) <-- term(l, c);

    relation resort(Sym, u32);                       // (label, idx) of slots that become T
    resort(l.clone(), *ci) <-- program_intro(l, _s, ci);
    resort(l.clone(), *ci) <-- env_intro(l, _s, ci);
    resort(l.clone(), *ci) <-- env_cont_on_contact(l, ci);

    out_param(l.clone(), *i, pn.clone(), k.clone(), ty.clone())
        <-- param(l, i, pn, k, ty), !resort(l, i);
    out_param(l.clone(), *i, pn.clone(), k.clone(), lift_ty(k, ty))
        <-- param(l, i, pn, k, ty), resort(l, i);
    out_param_binder(l.clone(), *i, b.clone()) <-- param_binder(l, i, b);

    // --- (3) adjoin the cost apparatus as constructors ---
    // wrapper {p}_s : P x Sig -> T, with P = the contact's category
    out_term(wrap_ctor(), "T".to_string());
    out_param(wrap_ctor(), 0, "p".to_string(), "simple".to_string(), cat.clone())
        <-- contact(k), term(k, cat);
    out_param(wrap_ctor(), 1, "s".to_string(), "simple".to_string(), "Sig".to_string());
    // token stack Stk ::= () | s : S
    out_term("SNil".to_string(), "Stk".to_string());
    out_term(scons_ctor(), "Stk".to_string());
    out_param(scons_ctor(), 0, "head".to_string(), "simple".to_string(), "Sig".to_string());
    out_param(scons_ctor(), 1, "tail".to_string(), "simple".to_string(), "Stk".to_string());
    // signatures Sig ::= g | #P | s * s  (low-budget: ground backend G fixed)
    out_term("SGround".to_string(), "Sig".to_string());
    out_term("SQuote".to_string(), "Sig".to_string());
    out_param("SQuote".to_string(), 0, "p".to_string(), "simple".to_string(), cat.clone())
        <-- contact(k), term(k, cat);
    out_term(compose_ctor(), "Sig".to_string());
    out_param(compose_ctor(), 0, "l".to_string(), "simple".to_string(), "Sig".to_string());
    out_param(compose_ctor(), 1, "r".to_string(), "simple".to_string(), "Sig".to_string());
    // lifted contact K : (bag of T/Stk) -> Cfg, one per contact
    out_term(meter(k), "Cfg".to_string()) <-- contact(k);
    out_param(meter(k), 0, "operands".to_string(), "note".to_string(),
              "T/Stk under K".to_string()) <-- contact(k);

    // --- (4) reuse each cut's LHS/RHS pattern forests verbatim (compute is not lifted) ---
    relation cut_forest(Sym, Id);
    cut_forest(n.clone(), l) <-- cut_lr(n, l, _);
    cut_forest(n.clone(), r) <-- cut_lr(n, _, r);
    cut_forest(n.clone(), c) <-- cut_forest(n, p), pat_child(p, _, c);

    out_pat_node(id, c.clone())  <-- cut_forest(_n, id), pat_node(id, c);
    out_pat_child(p, *i, c)      <-- cut_forest(_n, p), pat_child(p, i, c);
    out_pat_var(id, v.clone())   <-- cut_forest(_n, id), pat_var(id, v);

    // --- (5) the gated family, synthesized at the seams ---
    // Each scheme: distinct content-hashed node ids; metavariables shared within a scheme.

    // R1 (whole redex, single sig, single token) — emitted for EVERY cut.
    //   K{ {L}_s, s:S }  ~>  K{ R, S }
    out_rewrite_rule(rname(n, "R1"), nid("R1", "gl", n), nid("R1", "gr", n)) <-- cut(n);
    out_pat_node(nid("R1", "gl", n), meter(k)) <-- cut_k(n, k);
    out_pat_child(nid("R1", "gl", n), 0, nid("R1", "wrapL", n)) <-- cut(n);
    out_pat_child(nid("R1", "gl", n), 1, nid("R1", "sc", n))    <-- cut(n);
    out_pat_node(nid("R1", "wrapL", n), wrap_ctor()) <-- cut(n);
    out_pat_child(nid("R1", "wrapL", n), 0, l) <-- cut_lr(n, l, _);
    out_pat_child(nid("R1", "wrapL", n), 1, nid("R1", "sv", n)) <-- cut(n);
    out_pat_var(nid("R1", "sv", n), "s".to_string()) <-- cut(n);
    out_pat_node(nid("R1", "sc", n), scons_ctor()) <-- cut(n);
    out_pat_child(nid("R1", "sc", n), 0, nid("R1", "sv", n)) <-- cut(n);
    out_pat_child(nid("R1", "sc", n), 1, nid("R1", "Sv", n)) <-- cut(n);
    out_pat_var(nid("R1", "Sv", n), "S".to_string()) <-- cut(n);
    out_pat_node(nid("R1", "gr", n), meter(k)) <-- cut_k(n, k);
    out_pat_child(nid("R1", "gr", n), 0, r) <-- cut_lr(n, _, r);
    out_pat_child(nid("R1", "gr", n), 1, nid("R1", "Sv", n)) <-- cut(n);

    // R2 (whole redex, compound sig, split tokens) — constrained K only.
    //   K{ {L}_{s1*s2}, s1:S1, s2:S2 }  ~>  K{ R, S1, S2 }
    out_rewrite_rule(rname(n, "R2"), nid("R2", "gl", n), nid("R2", "gr", n)) <-- cut_constrained(n);
    out_pat_node(nid("R2", "gl", n), meter(k)) <-- cut_constrained(n), cut_k(n, k);
    out_pat_child(nid("R2", "gl", n), 0, nid("R2", "wrapL", n)) <-- cut_constrained(n);
    out_pat_child(nid("R2", "gl", n), 1, nid("R2", "sca", n))   <-- cut_constrained(n);
    out_pat_child(nid("R2", "gl", n), 2, nid("R2", "scb", n))   <-- cut_constrained(n);
    out_pat_node(nid("R2", "wrapL", n), wrap_ctor()) <-- cut_constrained(n);
    out_pat_child(nid("R2", "wrapL", n), 0, l) <-- cut_constrained(n), cut_lr(n, l, _);
    out_pat_child(nid("R2", "wrapL", n), 1, nid("R2", "comp", n)) <-- cut_constrained(n);
    out_pat_node(nid("R2", "comp", n), compose_ctor()) <-- cut_constrained(n);
    out_pat_child(nid("R2", "comp", n), 0, nid("R2", "s1v", n)) <-- cut_constrained(n);
    out_pat_child(nid("R2", "comp", n), 1, nid("R2", "s2v", n)) <-- cut_constrained(n);
    out_pat_var(nid("R2", "s1v", n), "s1".to_string()) <-- cut_constrained(n);
    out_pat_var(nid("R2", "s2v", n), "s2".to_string()) <-- cut_constrained(n);
    out_pat_node(nid("R2", "sca", n), scons_ctor()) <-- cut_constrained(n);
    out_pat_child(nid("R2", "sca", n), 0, nid("R2", "s1v", n)) <-- cut_constrained(n);
    out_pat_child(nid("R2", "sca", n), 1, nid("R2", "S1v", n)) <-- cut_constrained(n);
    out_pat_node(nid("R2", "scb", n), scons_ctor()) <-- cut_constrained(n);
    out_pat_child(nid("R2", "scb", n), 0, nid("R2", "s2v", n)) <-- cut_constrained(n);
    out_pat_child(nid("R2", "scb", n), 1, nid("R2", "S2v", n)) <-- cut_constrained(n);
    out_pat_var(nid("R2", "S1v", n), "S1".to_string()) <-- cut_constrained(n);
    out_pat_var(nid("R2", "S2v", n), "S2".to_string()) <-- cut_constrained(n);
    out_pat_node(nid("R2", "gr", n), meter(k)) <-- cut_constrained(n), cut_k(n, k);
    out_pat_child(nid("R2", "gr", n), 0, r) <-- cut_constrained(n), cut_lr(n, _, r);
    out_pat_child(nid("R2", "gr", n), 1, nid("R2", "S1v", n)) <-- cut_constrained(n);
    out_pat_child(nid("R2", "gr", n), 2, nid("R2", "S2v", n)) <-- cut_constrained(n);

    // R3 (whole redex, compound sig, combined token) — constrained K only.
    //   K{ {L}_{s1*s2}, (s1*s2):S }  ~>  K{ R, S }
    out_rewrite_rule(rname(n, "R3"), nid("R3", "gl", n), nid("R3", "gr", n)) <-- cut_constrained(n);
    out_pat_node(nid("R3", "gl", n), meter(k)) <-- cut_constrained(n), cut_k(n, k);
    out_pat_child(nid("R3", "gl", n), 0, nid("R3", "wrapL", n)) <-- cut_constrained(n);
    out_pat_child(nid("R3", "gl", n), 1, nid("R3", "sc", n))    <-- cut_constrained(n);
    out_pat_node(nid("R3", "wrapL", n), wrap_ctor()) <-- cut_constrained(n);
    out_pat_child(nid("R3", "wrapL", n), 0, l) <-- cut_constrained(n), cut_lr(n, l, _);
    out_pat_child(nid("R3", "wrapL", n), 1, nid("R3", "comp", n)) <-- cut_constrained(n);
    out_pat_node(nid("R3", "comp", n), compose_ctor()) <-- cut_constrained(n);
    out_pat_child(nid("R3", "comp", n), 0, nid("R3", "s1v", n)) <-- cut_constrained(n);
    out_pat_child(nid("R3", "comp", n), 1, nid("R3", "s2v", n)) <-- cut_constrained(n);
    out_pat_var(nid("R3", "s1v", n), "s1".to_string()) <-- cut_constrained(n);
    out_pat_var(nid("R3", "s2v", n), "s2".to_string()) <-- cut_constrained(n);
    out_pat_node(nid("R3", "sc", n), scons_ctor()) <-- cut_constrained(n);
    out_pat_child(nid("R3", "sc", n), 0, nid("R3", "comp", n)) <-- cut_constrained(n);
    out_pat_child(nid("R3", "sc", n), 1, nid("R3", "Sv", n))   <-- cut_constrained(n);
    out_pat_var(nid("R3", "Sv", n), "S".to_string()) <-- cut_constrained(n);
    out_pat_node(nid("R3", "gr", n), meter(k)) <-- cut_constrained(n), cut_k(n, k);
    out_pat_child(nid("R3", "gr", n), 0, r) <-- cut_constrained(n), cut_lr(n, _, r);
    out_pat_child(nid("R3", "gr", n), 1, nid("R3", "Sv", n)) <-- cut_constrained(n);

    // R4 (split processes, split tokens) — constrained K with both introductions.
    //   K{ {A}_s1, {B}_s2, s1:S1, s2:S2 }  ~>  K{ R, S1, S2 }
    out_rewrite_rule(rname(n, "R4"), nid("R4", "gl", n), nid("R4", "gr", n))
        <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_node(nid("R4", "gl", n), meter(k)) <-- cut_constrained(n), cut_k(n, k), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R4", "gl", n), 0, nid("R4", "wrapA", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R4", "gl", n), 1, nid("R4", "wrapB", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R4", "gl", n), 2, nid("R4", "sca", n))   <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R4", "gl", n), 3, nid("R4", "scb", n))   <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_node(nid("R4", "wrapA", n), wrap_ctor()) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R4", "wrapA", n), 0, a) <-- cut_constrained(n), cut_prog(n, a), cut_env(n, _b);
    out_pat_child(nid("R4", "wrapA", n), 1, nid("R4", "s1v", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_node(nid("R4", "wrapB", n), wrap_ctor()) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R4", "wrapB", n), 0, b) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, b);
    out_pat_child(nid("R4", "wrapB", n), 1, nid("R4", "s2v", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_var(nid("R4", "s1v", n), "s1".to_string()) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_var(nid("R4", "s2v", n), "s2".to_string()) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_node(nid("R4", "sca", n), scons_ctor()) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R4", "sca", n), 0, nid("R4", "s1v", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R4", "sca", n), 1, nid("R4", "S1v", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_node(nid("R4", "scb", n), scons_ctor()) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R4", "scb", n), 0, nid("R4", "s2v", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R4", "scb", n), 1, nid("R4", "S2v", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_var(nid("R4", "S1v", n), "S1".to_string()) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_var(nid("R4", "S2v", n), "S2".to_string()) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_node(nid("R4", "gr", n), meter(k)) <-- cut_constrained(n), cut_k(n, k), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R4", "gr", n), 0, r) <-- cut_constrained(n), cut_lr(n, _, r), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R4", "gr", n), 1, nid("R4", "S1v", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R4", "gr", n), 2, nid("R4", "S2v", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);

    // R5 (split processes, combined token) — constrained K with both introductions.
    //   K{ {A}_s1, {B}_s2, (s1*s2):S }  ~>  K{ R, S }
    out_rewrite_rule(rname(n, "R5"), nid("R5", "gl", n), nid("R5", "gr", n))
        <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_node(nid("R5", "gl", n), meter(k)) <-- cut_constrained(n), cut_k(n, k), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R5", "gl", n), 0, nid("R5", "wrapA", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R5", "gl", n), 1, nid("R5", "wrapB", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R5", "gl", n), 2, nid("R5", "sc", n))    <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_node(nid("R5", "wrapA", n), wrap_ctor()) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R5", "wrapA", n), 0, a) <-- cut_constrained(n), cut_prog(n, a), cut_env(n, _b);
    out_pat_child(nid("R5", "wrapA", n), 1, nid("R5", "s1v", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_node(nid("R5", "wrapB", n), wrap_ctor()) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R5", "wrapB", n), 0, b) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, b);
    out_pat_child(nid("R5", "wrapB", n), 1, nid("R5", "s2v", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_var(nid("R5", "s1v", n), "s1".to_string()) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_var(nid("R5", "s2v", n), "s2".to_string()) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_node(nid("R5", "comp", n), compose_ctor()) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R5", "comp", n), 0, nid("R5", "s1v", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R5", "comp", n), 1, nid("R5", "s2v", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_node(nid("R5", "sc", n), scons_ctor()) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R5", "sc", n), 0, nid("R5", "comp", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R5", "sc", n), 1, nid("R5", "Sv", n))   <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_var(nid("R5", "Sv", n), "S".to_string()) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
    out_pat_node(nid("R5", "gr", n), meter(k)) <-- cut_constrained(n), cut_k(n, k), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R5", "gr", n), 0, r) <-- cut_constrained(n), cut_lr(n, _, r), cut_prog(n, _a), cut_env(n, _b);
    out_pat_child(nid("R5", "gr", n), 1, nid("R5", "Sv", n)) <-- cut_constrained(n), cut_prog(n, _a), cut_env(n, _b);
}

// ============================== reify: decorated MILS -> facts ==============================

/// Untyped lambda: rigid K (App in no equation), degenerate Ke (App.arg is Ce).
fn reify_lambda(p: &mut AscentProgram) {
    p.sort = vec![("Term".into(),)];
    p.term = vec![("Lam".into(), "Term".into()), ("App".into(), "Term".into())];
    p.param = vec![
        ("Lam".into(), 0, "body".into(), "abstr".into(), "[Term -> Term]".into()),
        ("App".into(), 0, "fun".into(), "simple".into(), "Term".into()),
        ("App".into(), 1, "arg".into(), "simple".into(), "Term".into()),
    ];
    p.param_binder = vec![("Lam".into(), 0, "x".into())];
    // equations {} -> no eqn_mentions, no comm_collection -> App is rigid
    // Beta . |- (App (Lam fun) arg) ~> (eval fun arg)
    p.rewrite_rule = vec![("Beta".into(), 1, 10)];
    p.pat_node = vec![(1, "App".into()), (2, "Lam".into()), (10, "eval".into())];
    p.pat_child = vec![(1, 0, 2), (1, 1, 4), (2, 0, 3), (10, 0, 11), (10, 1, 12)];
    p.pat_var = vec![(3, "fun".into()), (4, "arg".into()), (11, "fun".into()), (12, "arg".into())];
    p.contact = vec![("App".into(),)];
    p.program_intro = vec![("Lam".into(), -1, 0)]; // surface structural (degenerate), cont = body
    p.env_cont_on_contact = vec![("App".into(), 1)]; // arg is the degenerate env continuation
    p.cut = vec![("Beta".into(),)];
}

/// Minimal communication calculus: AC K (Par is a comm-collection), two real
/// introductions For/Send -> the full five-rule lattice.
fn reify_comm(p: &mut AscentProgram) {
    p.sort = vec![("Proc".into(),), ("Name".into(),)];
    p.term = vec![
        ("Par".into(), "Proc".into()),
        ("For".into(), "Proc".into()),
        ("Send".into(), "Proc".into()),
    ];
    p.param = vec![
        ("Par".into(), 0, "ps".into(), "coll".into(), "Bag(Proc)".into()),
        ("For".into(), 0, "body".into(), "abstr".into(), "[Name -> Proc]".into()),
        ("For".into(), 1, "chan".into(), "simple".into(), "Name".into()),
        ("Send".into(), 0, "chan".into(), "simple".into(), "Name".into()),
        ("Send".into(), 1, "payload".into(), "simple".into(), "Proc".into()),
    ];
    p.param_binder = vec![("For".into(), 0, "y".into())];
    p.comm_collection = vec![("Par".into(),)]; // | is AC => constrained
    // Comm . |- (Par { (For ^y.P chan), (Send chan U) }) ~> (subst P U)
    p.rewrite_rule = vec![("Comm".into(), 100, 110)];
    p.pat_node = vec![
        (100, "Par".into()), (101, "For".into()), (104, "Send".into()), (110, "subst".into()),
    ];
    p.pat_child = vec![
        (100, 0, 101), (100, 1, 104),
        (101, 0, 102), (101, 1, 103),
        (104, 0, 105), (104, 1, 106),
        (110, 0, 111), (110, 1, 112),
    ];
    p.pat_var = vec![
        (102, "P".into()), (103, "chan".into()),
        (105, "chan".into()), (106, "U".into()),
        (111, "P".into()), (112, "U".into()),
    ];
    p.contact = vec![("Par".into(),)];
    p.program_intro = vec![("For".into(), 1, 0)]; // surface = chan (idx1), cont = body (idx0)
    p.env_intro = vec![("Send".into(), 0, 1)]; // surface = chan (idx0), cont = payload (idx1)
    p.cut = vec![("Comm".into(),)];
}

// ============================== reflect: facts -> MILS text ==============================

fn render_pat(
    id: Id,
    nodes: &HashMap<Id, String>,
    children: &HashMap<Id, Vec<(u32, Id)>>,
    vars: &HashMap<Id, String>,
) -> String {
    if let Some(v) = vars.get(&id) {
        return v.clone();
    }
    let ctor = nodes.get(&id).cloned().unwrap_or_else(|| format!("?{id}"));
    let mut ch = children.get(&id).cloned().unwrap_or_default();
    ch.sort_by_key(|(i, _)| *i);
    if ch.is_empty() {
        return ctor;
    }
    let parts: Vec<String> = ch.iter().map(|(_, c)| render_pat(*c, nodes, children, vars)).collect();
    format!("({} {})", ctor, parts.join(" "))
}

fn print_mils(title: &str, p: &AscentProgram) {
    println!("\n================ {title} ================");

    if !p.reject.is_empty() {
        println!("REJECTED (precondition failures):");
        for (m,) in &p.reject {
            println!("  - {m}");
        }
        return;
    }

    let mut sorts: Vec<&str> = p.out_sort.iter().map(|(s,)| s.as_str()).collect();
    sorts.sort();
    println!("types {{ {} }}", sorts.join(" "));

    // params grouped by constructor
    let mut params: HashMap<&str, Vec<(u32, &str, &str, &str)>> = HashMap::new();
    for (l, i, pn, k, ty) in &p.out_param {
        params.entry(l).or_default().push((*i, pn, k, ty));
    }
    let mut binders: HashMap<(&str, u32), &str> = HashMap::new();
    for (l, i, b) in &p.out_param_binder {
        binders.insert((l, *i), b);
    }
    println!("terms {{");
    let mut terms: Vec<(&str, &str)> = p.out_term.iter().map(|(l, c)| (l.as_str(), c.as_str())).collect();
    terms.sort();
    for (l, c) in terms {
        let mut ps = params.get(l).cloned().unwrap_or_default();
        ps.sort_by_key(|(i, _, _, _)| *i);
        let ctx: Vec<String> = ps
            .iter()
            .map(|(i, pn, k, ty)| {
                if *k == "abstr" {
                    let b = binders.get(&(l, *i)).copied().unwrap_or("_");
                    format!("^{b}.{pn}:{ty}")
                } else {
                    format!("{pn}:{ty}")
                }
            })
            .collect();
        println!("    {l} . {} : {c};", ctx.join(", "));
    }
    println!("}}");

    // rewrites
    let nodes: HashMap<Id, String> = p.out_pat_node.iter().map(|(i, c)| (*i, c.clone())).collect();
    let mut children: HashMap<Id, Vec<(u32, Id)>> = HashMap::new();
    for (par, i, c) in &p.out_pat_child {
        children.entry(*par).or_default().push((*i, *c));
    }
    let vars: HashMap<Id, String> = p.out_pat_var.iter().map(|(i, v)| (*i, v.clone())).collect();
    let mut rules: Vec<(&str, Id, Id)> = p.out_rewrite_rule.iter().map(|(n, l, r)| (n.as_str(), *l, *r)).collect();
    rules.sort();
    println!("rewrites {{");
    for (name, l, r) in rules {
        let lhs = render_pat(l, &nodes, &children, &vars);
        let rhs = render_pat(r, &nodes, &children, &vars);
        println!("    {name} . |- {lhs} ~> {rhs};");
    }
    println!("}}");
}

fn main() {
    let mut lam = AscentProgram::default();
    reify_lambda(&mut lam);
    lam.run();
    print_mils("cost(lambda)  [rigid K, degenerate Ke => R1 only]", &lam);

    let mut comm = AscentProgram::default();
    reify_comm(&mut comm);
    comm.run();
    print_mils("cost(comm)  [AC K => full five-rule lattice]", &comm);
}
