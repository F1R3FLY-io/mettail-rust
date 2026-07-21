//! The generated de-Bruijn substitution/shift term-rewriting system (TRS) — the PAYLOAD of
//! Stage 4 S-binder SLICE 2a (the in-Rho β cascade).
//!
//! # What this module builds
//!
//! Five PERSISTENT reserved receivers whose mutually-recursive `Match`-dispatch bodies compute the
//! capture-avoiding de-Bruijn β-substitution `b[a/0]` ON the live f1r3node reducer, with NO host
//! loop and NO `Value → GroundTerm` de-reflection. Once installed (parallel-composed into
//! [`crate::rho_net_lower::RhoNetLowered::installed_program_par`]) a single seed send
//! `^subst(⟦Z⟧, ⟦a⟧, ⟦b⟧, out)` self-drives the cascade to the β-normal form on `out`. This is the
//! codegen realization of the de-risking spike `rholang-runtime/tests/spike_subst_driver.rs`
//! (proven on the reducer, 6/6), transcribed from the spike's hand-written Rholang `contract`s into
//! the REAL reflected-`Par` encoding the set-automaton emits.
//!
//! # Encoding — the reflected-term ABI (NOT the spike's string/tuple encoding)
//!
//! Terms are the SAME tagged `EList` values [`crate::rho_net_lower::reflect_ground_term_par`]
//! produces, so a captured lambda body flows straight from the automaton into a `^subst` seed with
//! NO re-encoding:
//!
//! | object / de-Bruijn shape | reflected `Par`                                              |
//! |--------------------------|-------------------------------------------------------------|
//! | nullary ctor `A`         | `EList[ GPrivate(⌜A⌝) ]`                                     |
//! | ctor `C(t₀,…,t_{m-1})`   | `EList[ GPrivate(⌜C⌝), ⟦t₀⟧, …, ⟦t_{m-1}⟧ ]`                 |
//! | Peano `Z`                | `EList[ GPrivate(⌜Z⌝) ]`                                     |
//! | Peano `S(n)`             | `EList[ GPrivate(⌜S⌝), ⟦n⟧ ]`                                |
//! | `^bound(n)`              | `EList[ GPrivate(⌜^bound⌝), ⟦n⟧ ]`  (`n` a Peano numeral)    |
//! | `^lambda(b)`             | `EList[ GPrivate(⌜^lambda⌝), ⟦b⟧ ]`                          |
//! | `^free(x)`               | `EList[ GPrivate(⌜^free⌝), ⟦x⟧ ]`                            |
//! | `^cmp` result `Eq/Lt/Gt` | `EList[ GPrivate(⌜^Eq⌝ / ⌜^Lt⌝ / ⌜^Gt⌝) ]`  (internal only)  |
//!
//! where `⌜L⌝ = GPrivate(reflect_tag(fp, L))` is the unforgeable per-language tag. The `^cmp`
//! results never appear in a subject or an NF — they flow only between the receivers.
//!
//! # The TRS (blueprint §3.1, corrected depth-indexed C1 + C2 object congruence)
//!
//! ```text
//! ^subst(j,a,^bound n) → ^cmp(n,j){ Eq → ^shiftk(j,a) ; Gt → ^bound(^pred n) ; Lt → ^bound n }
//! ^subst(j,a,^lambda b)→ ^lambda(^subst(S j, a, b))            -- depth INCREMENTS under a binder
//! ^subst(j,a,^free x)  → ^free x
//! ^subst(j,a,C(t…))    → C(^subst(j,a,t)…)                     -- C2: one MatchCase per object ctor
//! ^shift(c,^bound n)   → ^cmp(n,c){ Lt → ^bound n ; _ → ^bound(S n) }
//! ^shift(c,^lambda b)  → ^lambda(^shift(S c, b))
//! ^shift(c,^free x)    → ^free x
//! ^shift(c,C(t…))      → C(^shift(c,t)…)
//! ^shiftk(Z,a)=a ; ^shiftk(S k,a)=^shift(Z, ^shiftk(k,a))
//! ^cmp(Z,Z)=Eq; ^cmp(Z,S_)=Lt; ^cmp(S_,Z)=Gt; ^cmp(S m,S n)=^cmp(m,n)
//! ^pred(Z)=Z; ^pred(S n)=n                                     -- TOTAL
//! ```
//!
//! # Driver-B (self-re-spreading)
//!
//! The receivers ARE the driver. Each reduced sub-term is produced by re-sending on a reserved
//! channel with a FRESH `new`-bound return channel; a partial object term `C(^subst(…))` is never
//! observable because the object-congruence arm publishes `C(s₀,…)` only from a continuation JOIN
//! `for(@s₀ <- r₀ & … ){ ret!(C(s₀,…)) }` that fires after every child substitution delivered its
//! NF (blueprint §4). The cross-receiver channels are ground `GPrivate(reflect_tag(fp,"^subst"))`
//! etc. (public, unforgeable, no enclosing `new` scope), so the five receivers are built
//! independently and parallel-composed — no new dispatch family, disturbing no landed receiver.
//!
//! # De Bruijn discipline
//!
//! Every `Par` is built through the [`Node`] combinators, which track a variable's free-set as a
//! sorted `Vec<usize>` and set `locally_free` accurately (the reducer's substitution reads it), and
//! through [`Env`], which resolves a named variable to its current `BoundVar` index. A binder
//! (receive formals / `new` names / `Match`-case free vars) pushes its innermost-last names onto the
//! `Env` and shifts the free-set down. This mirrors `rho_net_automaton`'s `wrap_capture_chain`
//! discipline and the `sigma_receiver_par` reverse-De-Bruijn frame.
//!
//! FV (SLICE 2b, NOT built here): `DeBruijnSubstTRS.v` (SN + confluence + `NF = b[a/0]`) and
//! `InRhoBetaCascadeWeakBisim.v` (object-β with the in-Rho subst cascade ≈ abstract β).

use mettail_ast::grammar::{GrammarItem, TermParam};
use mettail_ast::language::LanguageDef;
use models::rhoapi::{MatchCase, Par, Receive, ReceiveBind};
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_freevar_par, new_match_par, new_new_par, new_send_par,
    new_wildcard_par,
};

use crate::rho_net_lower::{
    reflect_ground_term_par, reflect_tag, BOUND_VAR_REFLECT_LABEL,
    CMP_RESERVED_LABEL, DRIVE_AC_RESERVED_LABEL, DRIVE_ERR_RESERVED_LABEL,
    DRIVE_FUEL_RESERVED_LABEL, DRIVE_RESERVED_LABEL,
    FIRED_RESERVED_LABEL, FLOAT_HOIST_RESERVED_LABEL, FLOAT_MERGE_RESERVED_LABEL,
    FLOAT_RESERVED_LABEL, FREE_VAR_REFLECT_LABEL, GroundTerm, LAMBDA_REFLECT_LABEL,
    MULTILAMBDA_REFLECT_LABEL, PEANO_SUCC_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL, PRED_RESERVED_LABEL,
    SB_RESERVED_LABEL, SHB_RESERVED_LABEL, SHIFTK_RESERVED_LABEL, SHIFT_RESERVED_LABEL,
    SUBST_RESERVED_LABEL,
};

/// The internal `^cmp`-result tags — `^`-prefixed so they cannot collide with any user constructor
/// (a Rust `Ident`, never containing `^`). They flow only between the receivers (a `^subst`/`^shift`
/// `^bound` arm reads the `^cmp` return), never appearing in a reflected subject or an NF.
const CMP_EQ_LABEL: &str = "^Eq";
const CMP_LT_LABEL: &str = "^Lt";
const CMP_GT_LABEL: &str = "^Gt";

/// The C2 object-congruence EXCLUSION set: an object constructor whose reflected tag is any of these
/// must NOT receive a generic congruence arm (blueprint §3.2). `^lambda`/`^multilambda` need the
/// `S j` depth INCREMENT (not a generic descent), and `^bound`/`^free`/`^subst`/`^shift`/`^shiftk`/
/// `^cmp`/`^pred`/`^sb`/`^shb` are reserved reduction machinery — a generic congruence over any of
/// them would break confluence and capture-avoidance. Every entry is `^`-prefixed, so an object
/// constructor (a user `Ident`) is disjoint from this set BY CONSTRUCTION; the codegen assertion in
/// [`object_congruence_constructors`] is the defensive guard that keeps it that way (e.g. if a future
/// binder-tag mapping regressed).
pub fn reserved_subst_trs_labels() -> [&'static str; 19] {
    [
        LAMBDA_REFLECT_LABEL,
        MULTILAMBDA_REFLECT_LABEL,
        BOUND_VAR_REFLECT_LABEL,
        FREE_VAR_REFLECT_LABEL,
        SUBST_RESERVED_LABEL,
        SHIFT_RESERVED_LABEL,
        SHIFTK_RESERVED_LABEL,
        CMP_RESERVED_LABEL,
        PRED_RESERVED_LABEL,
        SB_RESERVED_LABEL,
        SHB_RESERVED_LABEL,
        // A-S5.2 (leg v): the in-Rho quiescence-driver tags — `^drive` (the driver's
        // GPrivate rendezvous) plus the three GString observation-channel labels
        // (`crate::rho_net_drive`). Reserved so no user constructor can shadow the driver's
        // dispatch or forge its observation channels; the C2 assertion below now guards
        // these too.
        DRIVE_RESERVED_LABEL,
        DRIVE_ERR_RESERVED_LABEL,
        DRIVE_FUEL_RESERVED_LABEL,
        FIRED_RESERVED_LABEL,
        // A-S5.5: the per-rule AC-carrier tag PREFIX — every driver AC-carrier channel is
        // `⌜^drive-ac:{RuleLabel}⌝`; reserving the base label keeps the whole `:`-suffixed
        // family unforgeable vs user constructors (a Rust `Ident` contains neither `^` nor
        // `:`), and the C2 assertion guards the base like every other reserved tag.
        DRIVE_AC_RESERVED_LABEL,
        // A-S5.8: the in-Rho `^float` receiver-family tags — the dispatcher's rendezvous
        // (`^float`) plus the two per-constructor / per-collection-op satellite tag PREFIXES
        // (`⌜^float-hoist:{C}⌝` / `⌜^float-merge:{op}⌝`, the `^drive-ac` prefix precedent) —
        // registry 16 → 19 (`crate::rho_net_float`). The C2 assertion guards the bases like
        // every other reserved tag.
        FLOAT_RESERVED_LABEL,
        FLOAT_HOIST_RESERVED_LABEL,
        FLOAT_MERGE_RESERVED_LABEL,
    ]
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// De Bruijn `Node` combinators — every `Par` carries an accurate free-set (`locally_free`).
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// A built process `Par` paired with its free-variable set (the De Bruijn indices it references in
/// the CURRENT frame), sorted + de-duplicated. `locally_free` on the `Par` is kept in sync with
/// `free` so the reducer's substitution / COMM read the correct set.
///
/// `pub(crate)` (fields included): the Track-B R3 self-driving emitter
/// (`rho_net_naive_kt`, feature `bench-naive-baseline`) builds its `^respread`
/// reserved-receiver family with THESE combinators, so its De Bruijn/free-set
/// discipline is the TRS's by construction (and its one extra combinator — a
/// GString `++` concat — is assembled from the exposed fields).
#[derive(Clone)]
pub(crate) struct Node {
    pub(crate) par: Par,
    pub(crate) free: Vec<usize>,
}

/// Sorted-unique union of De Bruijn free-sets.
pub(crate) fn union_free(sets: &[&[usize]]) -> Vec<usize> {
    let mut all: Vec<usize> = sets.iter().flat_map(|s| s.iter().copied()).collect();
    all.sort_unstable();
    all.dedup();
    all
}

/// Shift a free-set DOWN through `n` innermost binders: drop the bound indices `0..n` and decrement
/// the rest. The free-set of a binder node in terms of the OUTER frame.
fn shift_down(free: &[usize], n: usize) -> Vec<usize> {
    free.iter().filter(|&&i| i >= n).map(|&i| i - n).collect()
}

/// Encode a free-set as the reducer's `locally_free` bit vector (one byte per index; empty ⟹ `[]`).
pub(crate) fn free_bits(free: &[usize]) -> Vec<u8> {
    if free.is_empty() {
        Vec::new()
    } else {
        models::create_bit_vector(free)
    }
}

/// A `BoundVar(i)` reference — free in `{i}`.
pub(crate) fn bv(i: usize) -> Node {
    Node { par: new_boundvar_par(i as i32, Vec::new(), false), free: vec![i] }
}

/// A GROUND `Par` (a reflected term, a tag, a reserved channel) — no free variables.
pub(crate) fn ground(par: Par) -> Node {
    Node { par, free: Vec::new() }
}

/// Recover a [`Node`] from a `Par` whose `locally_free` bit-vector already encodes its
/// De Bruijn free-set (one byte per index, `1` ⟹ referenced — the [`free_bits`] /
/// `models::create_bit_vector` encoding). Unlike [`ground`] (which asserts the Par has NO
/// free variables), this PRESERVES a frame-relative Par's free-set: the E-1 scion bundle
/// (`crate::rho_net_drive::FiringEmission::ScionBundle`) references its arm frame's σ /
/// `fuel` / `ret` slots, so the enclosing `Match`-case + receiver binders MUST see those
/// indices or the reducer's COMM/substitution reads a corrupt `locally_free`.
pub(crate) fn node_from_par(par: Par) -> Node {
    let free: Vec<usize> = par
        .locally_free
        .iter()
        .enumerate()
        .filter_map(|(index, &byte)| (byte != 0).then_some(index))
        .collect();
    Node { par, free }
}

/// The reserved unforgeable channel / tag `GPrivate(reflect_tag(fp, label))`.
pub(crate) fn tag_par(fp: &str, label: &str) -> Par {
    GPrivateBuilder::new_par_from_string(reflect_tag(fp, label))
}

/// A reflected NULLARY term `EList[ GPrivate(⌜label⌝) ]` — used for Peano `Z`, the `^cmp` results,
/// and (as a ground pattern) their `Match` cases. Byte-identical to
/// `reflect_ground_term_par(&GroundTerm::nullary(label), fp)`.
pub(crate) fn nullary_term(fp: &str, label: &str) -> Par {
    reflect_ground_term_par(&GroundTerm::nullary(label), fp)
}

/// An `EList[children…]` process value, free in the union of the children's free-sets.
fn elist(children: Vec<Node>) -> Node {
    let free = union_free(&children.iter().map(|c| c.free.as_slice()).collect::<Vec<_>>());
    let ps: Vec<Par> = children.into_iter().map(|c| c.par).collect();
    let bits = free_bits(&free);
    Node { par: new_elist_par(ps, bits.clone(), false, None, bits, false), free }
}

/// A tagged reflected value `EList[ GPrivate(⌜label⌝), children… ]` (`^bound(n)`, `^lambda(b)`,
/// `^free(x)`, `S(n)`, or an object ctor `C(t…)`), free in the union of the children.
///
/// `pub(crate)`: the A-S5.2 quiescence driver (`crate::rho_net_drive`) rebuilds driven
/// nodes with the SAME combinator so its reflected-ABI discipline is the TRS's by
/// construction (the `:129-133` sharing precedent).
pub(crate) fn tagged(fp: &str, label: &str, children: Vec<Node>) -> Node {
    let mut items = Vec::with_capacity(children.len() + 1);
    items.push(ground(tag_par(fp, label)));
    items.extend(children);
    elist(items)
}

/// A NON-persistent send `chan!(data…)`, free in `chan.free ∪ ⋃ data.free`.
pub(crate) fn send(chan: Node, data: Vec<Node>) -> Node {
    let mut free_refs: Vec<&[usize]> = vec![chan.free.as_slice()];
    free_refs.extend(data.iter().map(|d| d.free.as_slice()));
    let free = union_free(&free_refs);
    let ps: Vec<Par> = data.into_iter().map(|d| d.par).collect();
    let bits = free_bits(&free);
    Node { par: new_send_par(chan.par, ps, false, bits.clone(), false, bits, false), free }
}

/// One `Match` case: a `(pattern, free_count, body)` where `pattern` is a GROUND-relative pattern
/// `Par` (its `free_count` `FreeVar`s bind innermost in `body`), and `body` is a [`Node`] built in
/// the frame with those `free_count` vars pushed.
pub(crate) struct Case {
    pub(crate) pattern: Par,
    pub(crate) free_count: usize,
    pub(crate) body: Node,
}

/// `match target { case₀ ; case₁ ; … }` — free in `target.free ∪ ⋃ᵢ shift_down(caseᵢ.body.free,
/// caseᵢ.free_count)` (each case pattern binds `free_count` innermost vars in its body).
pub(crate) fn match_(target: Node, cases: Vec<Case>) -> Node {
    match_guarded(target, cases.into_iter().map(|case| (case, None)).collect())
}

/// [`match_`] with an OPTIONAL per-case `MatchCase.guard` (A-S5.5, plan v2 §4.1 / F12): the
/// guard `Par` is evaluated by the reducer IN THE CASE ENV (the pattern's `free_count`
/// binders pushed, reverse-De-Bruijn — `f1r3node reduce.rs:1290-1298` via rho_pure_eval);
/// the case fires iff it extracts `GBool(true)`, and `false`/non-bool/error falls through
/// to the NEXT case — exactly the non-linear cross-level checks the driver's AC redex arms
/// ride (`rho_net_lower::nonlinear_consistency_condition` over the case frame).
///
/// A guard may reference ONLY the case's own binders (`BoundVar < free_count`), so it
/// contributes nothing to the surrounding free-set — asserted here (fail-closed at
/// codegen time), which is what keeps the [`Node`] free-set bookkeeping exact without
/// threading guard frees.
pub(crate) fn match_guarded(target: Node, cases: Vec<(Case, Option<Par>)>) -> Node {
    let mut free_sets: Vec<Vec<usize>> = vec![target.free.clone()];
    let mut match_cases = Vec::with_capacity(cases.len());
    for (case, guard) in cases {
        if let Some(guard) = &guard {
            // `locally_free` is the reducer's index-per-byte bit vector
            // (`models::create_bit_vector`: `bit_vector[index] = 1`), so the highest
            // referenced De Bruijn index is the last set position.
            let highest_set = guard
                .locally_free
                .iter()
                .rposition(|&bit| bit != 0);
            assert!(
                highest_set.is_none_or(|index| index < case.free_count),
                "match_guarded: a case guard references BoundVar(s) beyond the case's own \
                 {} binder(s) (locally_free = {:?}) — guards must be case-closed",
                case.free_count,
                guard.locally_free,
            );
        }
        free_sets.push(shift_down(&case.body.free, case.free_count));
        match_cases.push(MatchCase {
            pattern: Some(case.pattern),
            source: Some(case.body.par),
            free_count: case.free_count as i32,
            guard,
        });
    }
    let free = union_free(&free_sets.iter().map(|s| s.as_slice()).collect::<Vec<_>>());
    let bits = free_bits(&free);
    Node { par: new_match_par(target.par, match_cases, bits.clone(), false, bits, false), free }
}

/// `new r₀, …, r_{n-1} in { body }` — the `n` fresh names bind innermost (`r_{n-1} = BoundVar(0)`,
/// matching f1r3node's reverse-syntactic-order normalization). Free in `shift_down(body.free, n)`.
///
/// `pub(crate)`: shared with the A-S5.2 quiescence driver (`crate::rho_net_drive`) — the
/// `:129-133` combinator-sharing precedent.
pub(crate) fn new_scope(n: usize, body: Node) -> Node {
    let free = shift_down(&body.free, n);
    let bits = free_bits(&free);
    let par = new_new_par(
        n as i32,
        body.par,
        Vec::new(),
        std::collections::BTreeMap::new(),
        bits.clone(),
        bits,
        false,
    );
    Node { par, free }
}

/// A persistent contract `for(f₀,…,f_{n-1} <= chan){ body }` — one POLYADIC `ReceiveBind` of `n`
/// `FreeVar` patterns over the GROUND reserved channel `chan`, body in the frame with the `n`
/// formals pushed (formal `i` ⟹ `BoundVar(n-1-i)`, the `sigma_receiver_par` frame). Top-level (its
/// free-set is `shift_down(body.free, n)`, which is `[]` for a closed receiver).
pub(crate) fn persistent_contract(chan: Par, n_formals: usize, body: Node) -> Node {
    polyadic_receive(chan, n_formals, body, true)
}

/// A POLYADIC single-bind receive `for(f₀,…,f_{n-1} <(=) source){ body }` (one `ReceiveBind` with
/// `n` `FreeVar` patterns, matching a polyadic send). `persistent` ⟹ a `contract`.
fn polyadic_receive(source: Par, n_formals: usize, body: Node, persistent: bool) -> Node {
    // The source is a GROUND reserved / resolved channel (no free vars); the body's `n` formals
    // bind innermost.
    let free = shift_down(&body.free, n_formals);
    let bits = free_bits(&free);
    let patterns: Vec<Par> = (0..n_formals).map(|i| new_freevar_par(i as i32, Vec::new())).collect();
    let receive = Receive {
        binds: vec![ReceiveBind {
            patterns,
            source: Some(source),
            remainder: None,
            free_count: n_formals as i32,
        }],
        body: Some(body.par),
        persistent,
        peek: false,
        bind_count: n_formals as i32,
        locally_free: bits.clone(),
        connective_used: false,
        condition: None,
    };
    Node { par: Par::default().with_receives(vec![receive]), free }
}

/// A single non-persistent `for(@x <- source){ body }` (used for a fresh return-channel read).
///
/// `pub(crate)`: shared with the A-S5.2 quiescence driver (`crate::rho_net_drive`).
pub(crate) fn for1(source: Node, body: Node) -> Node {
    // The source is evaluated in the OUTER frame; the one formal binds innermost in `body`.
    let free = union_free(&[source.free.as_slice(), shift_down(&body.free, 1).as_slice()]);
    let bits = free_bits(&free);
    let receive = Receive {
        binds: vec![ReceiveBind {
            patterns: vec![new_freevar_par(0, Vec::new())],
            source: Some(source.par),
            remainder: None,
            free_count: 1,
        }],
        body: Some(body.par),
        persistent: false,
        peek: false,
        bind_count: 1,
        locally_free: bits.clone(),
        connective_used: false,
        condition: None,
    };
    Node { par: Par::default().with_receives(vec![receive]), free }
}

/// An atomic n-ary continuation JOIN `for(@s₀ <- r₀ & … & @s_{n-1} <- r_{n-1}){ body }` — `n`
/// single-formal binds; the formals flatten bind-0-first so `sᵢ ⟹ BoundVar(n-1-i)` in `body`
/// (the reverse-De-Bruijn frame `contextual_join_receiver_par` uses). The join publishes `body`
/// only after EVERY child channel `rᵢ` delivered, so a partial object term is never observable.
///
/// `pub(crate)`: shared with the A-S5.2 quiescence driver (`crate::rho_net_drive`) — the
/// driver's congruence-descent reassembly IS this join generalized from "substitute" to
/// "reduce" (plan v2 §4, F2/F14).
pub(crate) fn join(sources: Vec<Node>, body: Node) -> Node {
    let n = sources.len();
    // The `n` sources are read in the OUTER frame; the `n` formals flatten bind-0-first and bind
    // innermost in `body`.
    let source_free: Vec<usize> =
        union_free(&sources.iter().map(|s| s.free.as_slice()).collect::<Vec<_>>());
    let free = union_free(&[source_free.as_slice(), shift_down(&body.free, n).as_slice()]);
    let bits = free_bits(&free);
    let binds: Vec<ReceiveBind> = sources
        .into_iter()
        .map(|source| ReceiveBind {
            patterns: vec![new_freevar_par(0, Vec::new())],
            source: Some(source.par),
            remainder: None,
            free_count: 1,
        })
        .collect();
    let receive = Receive {
        binds,
        body: Some(body.par),
        persistent: false,
        peek: false,
        bind_count: n as i32,
        locally_free: bits.clone(),
        connective_used: false,
        condition: None,
    };
    Node { par: Par::default().with_receives(vec![receive]), free }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// Pattern builders — GROUND-relative `Par`s whose `FreeVar`s bind in the case body.
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// A tagged pattern `EList[ GPrivate(⌜label⌝), children… ]` with `connective_used` set (it carries
/// `FreeVar`/`Wildcard` leaves), `locally_free = []` (pattern free vars are binders, not
/// locally-free bound vars) — the [`crate::rho_net_lower`] `comm_element_pattern` convention.
pub(crate) fn pat_tagged(fp: &str, label: &str, children: Vec<Par>) -> Par {
    let mut items = Vec::with_capacity(children.len() + 1);
    items.push(tag_par(fp, label));
    items.extend(children);
    new_elist_par(items, Vec::new(), true, None, Vec::new(), true)
}

/// `FreeVar(level)` — a pattern binder at the given local free-var level.
pub(crate) fn pat_free(level: usize) -> Par {
    new_freevar_par(level as i32, Vec::new())
}

/// A GROUND nullary pattern `EList[ GPrivate(⌜label⌝) ]` (Peano `Z`, a `^cmp` result) — no free
/// vars, `connective_used = false`; equal as a value to what the emitter sends.
fn pat_nullary(fp: &str, label: &str) -> Par {
    nullary_term(fp, label)
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// De Bruijn environment — resolve a named variable to its current `BoundVar` index.
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// A De Bruijn environment: `names[0]` is OUTERMOST, `names.last()` is innermost (`BoundVar(0)`).
/// Entering a binder [`Env::push`]es its formals (innermost last).
#[derive(Clone)]
pub(crate) struct Env {
    names: Vec<String>,
}

impl Env {
    /// A receiver's root frame: `formals[0]` outermost … `formals.last()` = `BoundVar(0)`.
    pub(crate) fn root(formals: &[&str]) -> Env {
        Env { names: formals.iter().map(|s| s.to_string()).collect() }
    }

    /// Extend the frame with a binder's formals (innermost last).
    pub(crate) fn push(&self, new: &[&str]) -> Env {
        let mut names = self.names.clone();
        names.extend(new.iter().map(|s| s.to_string()));
        Env { names }
    }

    /// The `BoundVar` index of `name` in the current frame (innermost binding wins).
    fn get(&self, name: &str) -> usize {
        let pos = self
            .names
            .iter()
            .rposition(|n| n == name)
            .unwrap_or_else(|| panic!("TRS builder: unbound variable {name} in {:?}", self.names));
        self.names.len() - 1 - pos
    }

    /// A [`Node`] referencing `name`.
    pub(crate) fn var(&self, name: &str) -> Node {
        bv(self.get(name))
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// The five reserved TRS receivers (blueprint §3.3).
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// `^cmp(m, n, ret)` — Peano comparison, returning `^Eq`/`^Lt`/`^Gt` on `ret`.
///
/// ```text
/// match m { Z    => match n { Z => ret!(Eq) ; S _ => ret!(Lt) }
///           S mm => match n { Z => ret!(Gt) ; S nn => ^cmp(mm, nn, ret) } }
/// ```
pub(crate) fn cmp_receiver_par(fp: &str) -> Par {
    let chan = tag_par(fp, CMP_RESERVED_LABEL);
    let env = Env::root(&["m", "n", "ret"]);
    let body = cmp_body(fp, &env);
    persistent_contract(chan, 3, body).par
}

fn cmp_body(fp: &str, env: &Env) -> Node {
    let eq = ground(nullary_term(fp, CMP_EQ_LABEL));
    let lt = ground(nullary_term(fp, CMP_LT_LABEL));
    let gt = ground(nullary_term(fp, CMP_GT_LABEL));
    // match m
    match_(
        env.var("m"),
        vec![
            // Z => match n { Z => ret!(Eq) ; S _ => ret!(Lt) }
            Case {
                pattern: pat_nullary(fp, PEANO_ZERO_REFLECT_LABEL),
                free_count: 0,
                body: match_(
                    env.var("n"),
                    vec![
                        Case {
                            pattern: pat_nullary(fp, PEANO_ZERO_REFLECT_LABEL),
                            free_count: 0,
                            body: send(env.var("ret"), vec![eq]),
                        },
                        Case {
                            pattern: pat_tagged(fp, PEANO_SUCC_REFLECT_LABEL, vec![pat_wildcard()]),
                            free_count: 0,
                            body: send(env.var("ret"), vec![lt]),
                        },
                    ],
                ),
            },
            // S mm => match n { Z => ret!(Gt) ; S nn => ^cmp(mm, nn, ret) }
            Case {
                pattern: pat_tagged(fp, PEANO_SUCC_REFLECT_LABEL, vec![pat_free(0)]),
                free_count: 1,
                body: {
                    let env = env.push(&["mm"]);
                    match_(
                        env.var("n"),
                        vec![
                            Case {
                                pattern: pat_nullary(fp, PEANO_ZERO_REFLECT_LABEL),
                                free_count: 0,
                                body: send(env.var("ret"), vec![gt]),
                            },
                            Case {
                                pattern: pat_tagged(
                                    fp,
                                    PEANO_SUCC_REFLECT_LABEL,
                                    vec![pat_free(0)],
                                ),
                                free_count: 1,
                                body: {
                                    let env = env.push(&["nn"]);
                                    send(
                                        ground(tag_par(fp, CMP_RESERVED_LABEL)),
                                        vec![env.var("mm"), env.var("nn"), env.var("ret")],
                                    )
                                },
                            },
                        ],
                    )
                },
            },
        ],
    )
}

pub(crate) fn pat_wildcard() -> Par {
    new_wildcard_par(Vec::new(), true)
}

/// `^pred(n, ret)` — TOTAL Peano predecessor. `match n { Z => ret!(Z) ; S m => ret!(m) }`.
pub(crate) fn pred_receiver_par(fp: &str) -> Par {
    let chan = tag_par(fp, PRED_RESERVED_LABEL);
    let env = Env::root(&["n", "ret"]);
    let body = match_(
        env.var("n"),
        vec![
            Case {
                pattern: pat_nullary(fp, PEANO_ZERO_REFLECT_LABEL),
                free_count: 0,
                body: send(env.var("ret"), vec![ground(nullary_term(fp, PEANO_ZERO_REFLECT_LABEL))]),
            },
            Case {
                pattern: pat_tagged(fp, PEANO_SUCC_REFLECT_LABEL, vec![pat_free(0)]),
                free_count: 1,
                body: {
                    let env = env.push(&["m"]);
                    send(env.var("ret"), vec![env.var("m")])
                },
            },
        ],
    );
    persistent_contract(chan, 2, body).par
}

/// `^shiftk(k, a, ret)` — apply `k` successive `^shift(Z, …)` passes to `a`.
///
/// ```text
/// match k { Z    => ret!(a)
///           S kk => new r in { ^shiftk(kk, a, r) | for(@sk <- r){ ^shift(Z, sk, ret) } } }
/// ```
pub(crate) fn shiftk_receiver_par(fp: &str) -> Par {
    let chan = tag_par(fp, SHIFTK_RESERVED_LABEL);
    let env = Env::root(&["k", "a", "ret"]);
    let body = match_(
        env.var("k"),
        vec![
            Case {
                pattern: pat_nullary(fp, PEANO_ZERO_REFLECT_LABEL),
                free_count: 0,
                body: send(env.var("ret"), vec![env.var("a")]),
            },
            Case {
                pattern: pat_tagged(fp, PEANO_SUCC_REFLECT_LABEL, vec![pat_free(0)]),
                free_count: 1,
                body: {
                    let env = env.push(&["kk"]);
                    new_scope(1, {
                        let env = env.push(&["r"]);
                        let recur = send(
                            ground(tag_par(fp, SHIFTK_RESERVED_LABEL)),
                            vec![env.var("kk"), env.var("a"), env.var("r")],
                        );
                        let observe = for1(env.var("r"), {
                            let env = env.push(&["sk"]);
                            send(
                                ground(tag_par(fp, SHIFT_RESERVED_LABEL)),
                                vec![
                                    ground(nullary_term(fp, PEANO_ZERO_REFLECT_LABEL)),
                                    env.var("sk"),
                                    env.var("ret"),
                                ],
                            )
                        });
                        par2(recur, observe)
                    })
                },
            },
        ],
    );
    persistent_contract(chan, 3, body).par
}

/// `^shift(c, t, ret)` — increment every `^bound n` with `n ≥ c` (free-variable shift under a
/// binder), descending `^lambda` with `c+1` and every object constructor structurally.
pub(crate) fn shift_receiver_par(def: &LanguageDef, fp: &str) -> Par {
    let chan = tag_par(fp, SHIFT_RESERVED_LABEL);
    let env = Env::root(&["c", "t", "ret"]);
    let body = match_(env.var("t"), shift_cases(def, fp, &env));
    persistent_contract(chan, 3, body).par
}

/// `^shift` `match t` cases: `^bound`, `^lambda`, `^free`, and one object-congruence arm per
/// non-reserved constructor.
fn shift_cases(def: &LanguageDef, fp: &str, env: &Env) -> Vec<Case> {
    let mut cases = vec![
        // ^bound n => new r in { ^cmp(n, c, r) | for(@cr <- r){ match cr { Lt => ^bound n ; _ => ^bound(S n) } } }
        Case {
            pattern: pat_tagged(fp, BOUND_VAR_REFLECT_LABEL, vec![pat_free(0)]),
            free_count: 1,
            body: {
                let env = env.push(&["n"]);
                new_scope(1, {
                    let env = env.push(&["r"]);
                    let cmp_call = send(
                        ground(tag_par(fp, CMP_RESERVED_LABEL)),
                        vec![env.var("n"), env.var("c"), env.var("r")],
                    );
                    let observe = for1(env.var("r"), {
                        let env = env.push(&["cr"]);
                        match_(
                            env.var("cr"),
                            vec![
                                Case {
                                    pattern: pat_nullary(fp, CMP_LT_LABEL),
                                    free_count: 0,
                                    body: send(
                                        env.var("ret"),
                                        vec![tagged(
                                            fp,
                                            BOUND_VAR_REFLECT_LABEL,
                                            vec![env.var("n")],
                                        )],
                                    ),
                                },
                                Case {
                                    pattern: pat_wildcard(),
                                    free_count: 0,
                                    body: send(
                                        env.var("ret"),
                                        vec![tagged(
                                            fp,
                                            BOUND_VAR_REFLECT_LABEL,
                                            vec![tagged(
                                                fp,
                                                PEANO_SUCC_REFLECT_LABEL,
                                                vec![env.var("n")],
                                            )],
                                        )],
                                    ),
                                },
                            ],
                        )
                    });
                    par2(cmp_call, observe)
                })
            },
        },
        // ^lambda b => new r in { ^shift(S c, b, r) | for(@rb <- r){ ret!(^lambda rb) } }
        Case {
            pattern: pat_tagged(fp, LAMBDA_REFLECT_LABEL, vec![pat_free(0)]),
            free_count: 1,
            body: {
                let env = env.push(&["b"]);
                new_scope(1, {
                    let env = env.push(&["r"]);
                    let recur = send(
                        ground(tag_par(fp, SHIFT_RESERVED_LABEL)),
                        vec![
                            tagged(fp, PEANO_SUCC_REFLECT_LABEL, vec![env.var("c")]),
                            env.var("b"),
                            env.var("r"),
                        ],
                    );
                    let observe = for1(env.var("r"), {
                        let env = env.push(&["rb"]);
                        send(env.var("ret"), vec![tagged(fp, LAMBDA_REFLECT_LABEL, vec![env.var("rb")])])
                    });
                    par2(recur, observe)
                })
            },
        },
        // ^free x => ret!(^free x)
        free_passthrough_case(fp, env),
    ];
    cases.extend(object_congruence_cases(def, fp, env, SHIFT_RESERVED_LABEL, "c"));
    // A-S5.8 (F8-AM-5e): the SOUP + Nil arms — one peel arm per HashBag collection op, plus
    // the shared Nil (empty-bag) leaf — GATED on the language declaring HashBag ops at all,
    // so a bag-free language's `^shift` (Lambda) is BYTE-IDENTICAL to pre-A-S5.8. Without
    // them, `^shift` on a bag-carrying value SILENTLY STALLS (the C2 congruence enumeration
    // excludes collections and the receiver has no wildcard) — and the A-S5.8 `^float`
    // hoist/merge satellites shift values that carry bags. Both arms keep the cutoff `c`
    // UNCHANGED (a bag crosses no binder) and REWRAP without splice logic (shift is a
    // congruence — it never changes a value's shape, so the shifted element re-wraps as the
    // one element send it was and the shifted remainder composes directly):
    //
    // ```text
    // {@"ac:op"!(e) | rem} => new re, rr in {
    //     ^shift(c, e, re) | ^shift(c, rem, rr)
    //   | for(@se <- re & @sr <- rr){ ret!( @"ac:op"!(se) | sr ) } }
    // Nil => ret!(Nil)
    // ```
    //
    // The Nil arm is FIRST-CLASS, not merely the peel recursion's base: `@"ac:op"!(Nil)` is
    // the legitimate reflection image of a nested EMPTY bag, and a `^float-merge` v-strip
    // shifts a Nil u (F8-AM-5f) — without this arm that shift stalls.
    let bag_ops = crate::rho_net_drive::hashbag_collection_ops(def);
    for op in &bag_ops {
        cases.push(Case {
            pattern: crate::rho_net_drive::soup_peel_pattern(op),
            free_count: 2,
            body: {
                let env = env.push(&["e", "rem"]);
                new_scope(2, {
                    let env = env.push(&["re", "rr"]);
                    let shift_element = send(
                        ground(tag_par(fp, SHIFT_RESERVED_LABEL)),
                        vec![env.var("c"), env.var("e"), env.var("re")],
                    );
                    let shift_remainder = send(
                        ground(tag_par(fp, SHIFT_RESERVED_LABEL)),
                        vec![env.var("c"), env.var("rem"), env.var("rr")],
                    );
                    let join_node = join(vec![env.var("re"), env.var("rr")], {
                        let env = env.push(&["se", "sr"]);
                        send(
                            env.var("ret"),
                            vec![par2(
                                crate::rho_net_drive::wrap_element_send(op, env.var("se")),
                                env.var("sr"),
                            )],
                        )
                    });
                    par2(par2(shift_element, shift_remainder), join_node)
                })
            },
        });
    }
    if !bag_ops.is_empty() {
        cases.push(Case {
            pattern: Par::default(),
            free_count: 0,
            body: send(env.var("ret"), vec![ground(Par::default())]),
        });
    }
    cases
}

/// `^subst(j, a, t, ret)` — capture-avoiding de-Bruijn substitution `t[a/j]`.
pub(crate) fn subst_receiver_par(def: &LanguageDef, fp: &str) -> Par {
    let chan = tag_par(fp, SUBST_RESERVED_LABEL);
    let env = Env::root(&["j", "a", "t", "ret"]);
    let body = match_(env.var("t"), subst_cases(def, fp, &env));
    persistent_contract(chan, 4, body).par
}

/// `^subst` `match t` cases: `^bound`, `^lambda` (depth increment), `^free`, and one
/// object-congruence arm per non-reserved constructor.
fn subst_cases(def: &LanguageDef, fp: &str, env: &Env) -> Vec<Case> {
    let mut cases = vec![
        // ^bound n => new r in { ^cmp(n, j, r) |
        //   for(@cr <- r){ match cr { Eq => ^shiftk(j, a, ret)
        //                             Gt => new rp in { ^pred(n, rp) | for(@pn <- rp){ ret!(^bound pn) } }
        //                             Lt => ret!(^bound n) } } }
        Case {
            pattern: pat_tagged(fp, BOUND_VAR_REFLECT_LABEL, vec![pat_free(0)]),
            free_count: 1,
            body: {
                let env = env.push(&["n"]);
                new_scope(1, {
                    let env = env.push(&["r"]);
                    let cmp_call = send(
                        ground(tag_par(fp, CMP_RESERVED_LABEL)),
                        vec![env.var("n"), env.var("j"), env.var("r")],
                    );
                    let observe = for1(env.var("r"), {
                        let env = env.push(&["cr"]);
                        match_(
                            env.var("cr"),
                            vec![
                                // Eq => ^shiftk(j, a, ret)
                                Case {
                                    pattern: pat_nullary(fp, CMP_EQ_LABEL),
                                    free_count: 0,
                                    body: send(
                                        ground(tag_par(fp, SHIFTK_RESERVED_LABEL)),
                                        vec![env.var("j"), env.var("a"), env.var("ret")],
                                    ),
                                },
                                // Gt => new rp in { ^pred(n, rp) | for(@pn <- rp){ ret!(^bound pn) } }
                                Case {
                                    pattern: pat_nullary(fp, CMP_GT_LABEL),
                                    free_count: 0,
                                    body: new_scope(1, {
                                        let env = env.push(&["rp"]);
                                        let pred_call = send(
                                            ground(tag_par(fp, PRED_RESERVED_LABEL)),
                                            vec![env.var("n"), env.var("rp")],
                                        );
                                        let observe = for1(env.var("rp"), {
                                            let env = env.push(&["pn"]);
                                            send(
                                                env.var("ret"),
                                                vec![tagged(
                                                    fp,
                                                    BOUND_VAR_REFLECT_LABEL,
                                                    vec![env.var("pn")],
                                                )],
                                            )
                                        });
                                        par2(pred_call, observe)
                                    }),
                                },
                                // Lt => ret!(^bound n)
                                Case {
                                    pattern: pat_nullary(fp, CMP_LT_LABEL),
                                    free_count: 0,
                                    body: send(
                                        env.var("ret"),
                                        vec![tagged(
                                            fp,
                                            BOUND_VAR_REFLECT_LABEL,
                                            vec![env.var("n")],
                                        )],
                                    ),
                                },
                            ],
                        )
                    });
                    par2(cmp_call, observe)
                })
            },
        },
        // ^lambda b => new r in { ^subst(S j, a, b, r) | for(@rb <- r){ ret!(^lambda rb) } }  [DEPTH INCREMENT]
        Case {
            pattern: pat_tagged(fp, LAMBDA_REFLECT_LABEL, vec![pat_free(0)]),
            free_count: 1,
            body: {
                let env = env.push(&["b"]);
                new_scope(1, {
                    let env = env.push(&["r"]);
                    let recur = send(
                        ground(tag_par(fp, SUBST_RESERVED_LABEL)),
                        vec![
                            tagged(fp, PEANO_SUCC_REFLECT_LABEL, vec![env.var("j")]),
                            env.var("a"),
                            env.var("b"),
                            env.var("r"),
                        ],
                    );
                    let observe = for1(env.var("r"), {
                        let env = env.push(&["rb"]);
                        send(env.var("ret"), vec![tagged(fp, LAMBDA_REFLECT_LABEL, vec![env.var("rb")])])
                    });
                    par2(recur, observe)
                })
            },
        },
        // ^free x => ret!(^free x)
        free_passthrough_case(fp, env),
    ];
    cases.extend(object_congruence_cases(def, fp, env, SUBST_RESERVED_LABEL, "j"));
    cases
}

/// The `^free x => ret!(^free x)` passthrough arm (shared by `^subst` / `^shift`): a free variable
/// is inert under both.
fn free_passthrough_case(fp: &str, env: &Env) -> Case {
    Case {
        pattern: pat_tagged(fp, FREE_VAR_REFLECT_LABEL, vec![pat_free(0)]),
        free_count: 1,
        body: {
            let env = env.push(&["x"]);
            send(env.var("ret"), vec![tagged(fp, FREE_VAR_REFLECT_LABEL, vec![env.var("x")])])
        },
    }
}

/// The C2 object-congruence arms: one `MatchCase` per non-reserved object constructor `C` of arity
/// `m` (blueprint §3.2). `op` is the reserved receiver channel (`^subst` / `^shift`), `depth_var`
/// the depth argument name (`j` for `^subst`, `c` for `^shift`) that is threaded UNCHANGED into each
/// child call (object descent does NOT cross a binder — only the `^lambda` arm increments).
///
/// ```text
/// C(t₀,…,t_{m-1}) => new r₀,…,r_{m-1} in {
///     op(depth, a, t₀, r₀) | … | op(depth, a, t_{m-1}, r_{m-1}) |
///     for(@s₀ <- r₀ & … & @s_{m-1} <- r_{m-1}){ ret!(C(s₀,…,s_{m-1})) } }      [m ≥ 1]
/// C                => ret!(C)                                                    [m = 0]
/// ```
///
/// `^subst` threads `(j, a)`; `^shift` threads only `c` (no replacement `a`), so the child call
/// arity differs — handled by [`descend_child_call`].
fn object_congruence_cases(
    def: &LanguageDef,
    fp: &str,
    env: &Env,
    op: &str,
    depth_var: &str,
) -> Vec<Case> {
    let mut cases = Vec::new();
    for (label, arity) in object_congruence_constructors(def) {
        let child_pats: Vec<Par> = (0..arity).map(pat_free).collect();
        cases.push(Case {
            pattern: pat_tagged(fp, &label, child_pats),
            free_count: arity,
            body: {
                // The `arity` captured children are innermost; child `i` = `FreeVar(i)` ⟹
                // `BoundVar(arity-1-i)`. Name them `c0..c_{arity-1}` (innermost-last order).
                let child_names: Vec<String> = (0..arity).map(|i| format!("c{i}")).collect();
                let child_refs: Vec<&str> = child_names.iter().map(String::as_str).collect();
                let env = env.push(&child_refs);
                if arity == 0 {
                    // A nullary object term is inert: ret!(C).
                    send(env.var("ret"), vec![tagged(fp, &label, Vec::new())])
                } else {
                    new_scope(arity, {
                        // Fresh return channels r0..r_{arity-1} (innermost-last).
                        let ret_names: Vec<String> = (0..arity).map(|i| format!("r{i}")).collect();
                        let ret_refs: Vec<&str> = ret_names.iter().map(String::as_str).collect();
                        let env = env.push(&ret_refs);
                        // One child-substitution send per child.
                        let mut composed: Option<Node> = None;
                        for i in 0..arity {
                            let call = descend_child_call(
                                fp,
                                op,
                                &env,
                                depth_var,
                                &child_names[i],
                                &ret_names[i],
                            );
                            composed = Some(match composed {
                                None => call,
                                Some(acc) => par2(acc, call),
                            });
                        }
                        // The atomic join reassembling C(s0,…,s_{m-1}).
                        let join_sources: Vec<Node> =
                            ret_names.iter().map(|r| env.var(r)).collect();
                        let join_node = join(join_sources, {
                            let s_names: Vec<String> = (0..arity).map(|i| format!("s{i}")).collect();
                            let s_refs: Vec<&str> = s_names.iter().map(String::as_str).collect();
                            let env = env.push(&s_refs);
                            let assembled: Vec<Node> = s_names.iter().map(|s| env.var(s)).collect();
                            send(env.var("ret"), vec![tagged(fp, &label, assembled)])
                        });
                        par2(composed.expect("arity ≥ 1"), join_node)
                    })
                }
            },
        });
    }
    cases
}

/// One child descent call: `^subst(depth, a, child, r)` (4-ary) or `^shift(depth, child, r)`
/// (3-ary), depending on `op`.
fn descend_child_call(
    fp: &str,
    op: &str,
    env: &Env,
    depth_var: &str,
    child: &str,
    ret_chan: &str,
) -> Node {
    let chan = ground(tag_par(fp, op));
    if op == SUBST_RESERVED_LABEL {
        send(chan, vec![env.var(depth_var), env.var("a"), env.var(child), env.var(ret_chan)])
    } else {
        send(chan, vec![env.var(depth_var), env.var(child), env.var(ret_chan)])
    }
}

/// Parallel composition `p | q` — the free-set is the union (parallel composition binds nothing).
pub(crate) fn par2(p: Node, q: Node) -> Node {
    let free = union_free(&[p.free.as_slice(), q.free.as_slice()]);
    let par = p.par.append(q.par);
    Node { par, free }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// C2 object-constructor enumeration + the reserved-disjointness assertion.
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// Enumerate the NON-reserved object constructors that get a C2 congruence arm, each with its
/// reflected arity (number of structural children in `EList[tag, c₀, …]`). Iterates `def.terms`,
/// EXCLUDING every binder (a `Lam`/`MultiLambda` reflects to `^lambda`/`^multilambda`, handled by
/// the fixed depth-increment arm) and every term whose reflected tag is reserved
/// ([`reserved_subst_trs_labels`]).
///
/// # C2 assertion (blueprint §3.2, LOAD-BEARING)
///
/// Panics (codegen-time, fail-closed) if any EMITTED object constructor's reflected tag is in the
/// reserved set — a generic congruence over `^lambda` would lose the `S j` depth increment
/// (non-confluence + variable CAPTURE). Because reserved tags are `^`-prefixed and a user
/// constructor is a Rust `Ident`, this holds by construction; the assertion is the guard that keeps
/// it true if a binder-tag mapping ever regressed.
///
/// Scalar / HOL (native `![…]`) constructors are excluded (they have no de-Bruijn subterm to
/// descend); a language mixing scalar leaves UNDER a binder is out of this slice's scope and would
/// need an inert-scalar arm (documented follow-on).
pub(crate) fn object_congruence_constructors(def: &LanguageDef) -> Vec<(String, usize)> {
    let reserved = reserved_subst_trs_labels();
    let mut ctors = Vec::new();
    for term in &def.terms {
        // Skip HOL / native constructors (no structural subterm to substitute).
        if term.rust_code.is_some() {
            continue;
        }
        // A binder reflects to `^lambda`/`^multilambda` — excluded (handled by the fixed arm).
        if is_binder_term(term) {
            continue;
        }
        // Determine the reflected arity (structural children). `None` ⟹ not a plain structural
        // constructor (scalar-only / unsupported shape) — skip.
        let Some(arity) = structural_arity(term) else {
            continue;
        };
        let label = term.label.to_string();
        // C2 ASSERTION: an emitted object ctor must be disjoint from the reserved set.
        assert!(
            !reserved.contains(&label.as_str()),
            "S-binder C2 violation: object constructor {label:?} collides with a reserved TRS tag \
             {reserved:?} — a generic congruence over it would break confluence / capture-avoidance",
        );
        ctors.push((label, arity));
    }
    ctors
}

/// Whether a term is a single- or multi-binder (has an `Abstraction`/`MultiAbstraction` term-context
/// param, or an old-syntax `Binder` grammar item) — the reflection tags it `^lambda`/`^multilambda`.
///
/// `pub(crate)`: the A-S5.2 quiescence driver's LHS-pattern transcription and binder-arm
/// emission (`crate::rho_net_drive`) consult the SAME predicate so the driver's binder
/// remap can never drift from the TRS's.
pub(crate) fn is_binder_term(term: &mettail_ast::grammar::GrammarRule) -> bool {
    if let Some(params) = &term.term_context {
        if params
            .iter()
            .any(|p| matches!(p, TermParam::Abstraction { .. } | TermParam::MultiAbstraction { .. }))
        {
            return true;
        }
    }
    term.items.iter().any(|item| matches!(item, GrammarItem::Binder { .. }))
}

/// The reflected arity of a plain STRUCTURAL constructor: the count of `Simple` term-context params
/// (each reflects to one `EList` child). `None` if the term is not a plain structural constructor
/// (has a guard/optional param, or an old-syntax shape this slice does not model). A nullary
/// constructor (no params) has arity `0`.
fn structural_arity(term: &mettail_ast::grammar::GrammarRule) -> Option<usize> {
    match &term.term_context {
        Some(params) => {
            let mut arity = 0;
            for param in params {
                match param {
                    TermParam::Simple { .. } => arity += 1,
                    // Binder params are handled by `is_binder_term` (already excluded upstream);
                    // guard / optional params are out of scope for object congruence.
                    TermParam::Abstraction { .. } | TermParam::MultiAbstraction { .. } => {
                        return None
                    },
                    TermParam::GuardBody { .. } | TermParam::Optional { .. } => return None,
                }
            }
            Some(arity)
        },
        // Old BNFC-style: count structural (user-category) nonterminals. A terminal contributes no
        // child; a builtin (Var/literal) is not a structural subterm this slice descends.
        None => {
            let mut arity = 0;
            for item in &term.items {
                match item {
                    GrammarItem::NonTerminal { .. } if !item.is_builtin() => arity += 1,
                    GrammarItem::NonTerminal { .. } | GrammarItem::Terminal(_) => {},
                    GrammarItem::Binder { .. } | GrammarItem::Collection { .. } => return None,
                }
            }
            Some(arity)
        },
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// Program composer + the β seed (receiver body + ground send).
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// The five reserved TRS receivers parallel-composed into one installable `Par` (blueprint §3.4).
/// Installed ONCE per language carrying a `SubstRewrite` — persistent, on disjoint reserved roots,
/// disturbing no landed receiver. `^cmp`/`^pred`/`^shiftk` are language-independent; `^subst`/
/// `^shift` carry the object-congruence arms derived from `def`.
pub fn subst_trs_program_par(def: &LanguageDef, fingerprint: &str) -> Par {
    Par::default()
        .append(cmp_receiver_par(fingerprint))
        .append(pred_receiver_par(fingerprint))
        .append(shiftk_receiver_par(fingerprint))
        .append(shift_receiver_par(def, fingerprint))
        .append(subst_receiver_par(def, fingerprint))
}

/// The β SEED as the `Beta` σ-receiver body (blueprint §2/§4): instead of forwarding a host-computed
/// reduct, the installed `SubstRewrite` σ-receiver (`for(σ₀,…,σ_{k-1}, out <= c_beta)`) SENDS
/// `^subst(⟦Z⟧, σ_repl, σ_scope, out)` on the reserved `^subst` channel, threading `out` as the
/// cascade's continuation. THIS ONE COMM is the observable β-FIRE; the reduct is the τ-cascade NF the
/// TRS delivers on `out`.
///
/// `scope_bv` / `repl_bv` are the `BoundVar` indices (reverse-De-Bruijn over the `k+1` formals, via
/// [`crate::rho_net_lower::rhs_var_index`]) of the subst SCOPE (the lambda body `b`) and the
/// REPLACEMENT (the argument `a`); `out = BoundVar(0)`.
pub fn subst_seed_receiver_par(
    k: usize,
    scope_bv: usize,
    repl_bv: usize,
    fingerprint: &str,
    source: Par,
) -> Par {
    let n_formals = k + 1;
    // ^subst(⟦Z⟧, a=BoundVar(repl_bv), b=BoundVar(scope_bv), out=BoundVar(0))
    let body = send(
        ground(tag_par(fingerprint, SUBST_RESERVED_LABEL)),
        vec![
            ground(nullary_term(fingerprint, PEANO_ZERO_REFLECT_LABEL)),
            bv(repl_bv),
            bv(scope_bv),
            bv(0),
        ],
    );
    persistent_contract_over(source, n_formals, body).par
}

/// A ground β seed SEND `^subst(⟦Z⟧, a, b, @out)` (blueprint §4) — for a DIRECT injection / a
/// reducer test that drives the cascade without the automaton match. `arg` (`⟦a⟧`) and `body`
/// (`⟦b⟧`) are already-reflected ground terms; the NF rests on the GString channel `@out`.
pub fn subst_seed_send_par(fingerprint: &str, arg: Par, body: Par, out_channel: &str) -> Par {
    send(
        ground(tag_par(fingerprint, SUBST_RESERVED_LABEL)),
        vec![
            ground(nullary_term(fingerprint, PEANO_ZERO_REFLECT_LABEL)),
            ground(arg),
            ground(body),
            ground(models::rust::utils::new_gstring_par(out_channel.to_string(), Vec::new(), false)),
        ],
    )
    .par
}

/// A persistent contract over an ARBITRARY source channel `Par` (the σ-receiver's resolved source),
/// n formals, body — like [`persistent_contract`] but the channel may carry free vars (it does not,
/// for a resolved ground source, but this keeps the free-set honest).
fn persistent_contract_over(source: Par, n_formals: usize, body: Node) -> Node {
    polyadic_receive(source, n_formals, body, true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::language::LanguageDef;

    /// A LambdaDemo-shaped def (App/F/A structural + Lam binder + Beta), parsed as the inner
    /// `language!` fragment (the `syn::parse_str::<LanguageDef>` shape the codegen tests use).
    fn lambda_like_def() -> LanguageDef {
        let fragment = r#"
            name: LambdaDemo,
            types { Term },
            terms {
                Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term ;
                App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term ;
                F . a:Term |- "f" "(" a ")" : Term ;
                A . |- "A" : Term ;
            },
            equations {},
            rewrites { Beta . |- (App (Lam fun) arg) ~> (eval fun arg) ; }
        "#;
        syn::parse_str::<LanguageDef>(fragment).expect("probe def parses")
    }

    #[test]
    fn object_congruence_excludes_the_binder_and_keeps_the_object_ctors() {
        let def = lambda_like_def();
        let ctors = object_congruence_constructors(&def);
        // Lam is a binder (⟹ ^lambda) — excluded. App (arity 2), F (arity 1), A (arity 0) remain.
        let by_label: std::collections::HashMap<&str, usize> =
            ctors.iter().map(|(l, a)| (l.as_str(), *a)).collect();
        assert!(!by_label.contains_key("Lam"), "the binder Lam must be excluded from C2");
        assert_eq!(by_label.get("App"), Some(&2), "App is a binary object ctor");
        assert_eq!(by_label.get("F"), Some(&1), "F is a unary object ctor");
        assert_eq!(by_label.get("A"), Some(&0), "A is a nullary object ctor");
    }

    #[test]
    fn the_program_has_five_reserved_receivers() {
        let def = lambda_like_def();
        let program = subst_trs_program_par(&def, "fp");
        // Each receiver is one persistent `Receive` at the top level.
        assert_eq!(
            program.receives.len(),
            5,
            "the TRS installs exactly five persistent receivers (cmp/pred/shiftk/shift/subst)",
        );
        assert!(
            program.receives.iter().all(|r| r.persistent),
            "every TRS receiver is persistent",
        );
    }

    #[test]
    fn the_seed_receiver_sends_on_the_reserved_subst_channel() {
        // k=2 (fun, arg): scope=fun=BoundVar(2), repl=arg=BoundVar(1), out=BoundVar(0).
        let source = models::rust::utils::new_gstring_par("c_beta".to_string(), Vec::new(), false);
        let receiver = subst_seed_receiver_par(2, 2, 1, "fp", source);
        assert_eq!(receiver.receives.len(), 1, "the seed is one persistent receiver");
        let bind = &receiver.receives[0].binds[0];
        assert_eq!(bind.patterns.len(), 3, "k+1 = 3 formals (fun, arg, out)");
        // Its body sends on the reserved `^subst` GPrivate channel.
        let body = receiver.receives[0].body.as_ref().expect("seed body");
        assert_eq!(body.sends.len(), 1, "the seed body is one send");
        let expected_chan = tag_par("fp", SUBST_RESERVED_LABEL);
        assert_eq!(
            body.sends[0].chan.as_ref(),
            Some(&expected_chan),
            "the seed sends on the reserved ^subst channel",
        );
        assert_eq!(body.sends[0].data.len(), 4, "^subst(Z, a, b, out) — four args");
    }
}
