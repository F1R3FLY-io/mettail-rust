//! FLT (Foreign Language Term) Phase 2 — the PUBLIC reflector API.
//!
//! This module is the public, syntax-independent hinge between an FLT surface template
//! (`` lambda:Term`(${f}, lam a. lam b. a)` ``) and the reflected-`Par` shapes the installed
//! set-automaton / driver
//! family MATCHES and SEEDS on. It GENERATES the exact hand-built shapes pinned in
//! `rholang-runtime/tests/flt_abi_over_rspace.rs` (the ground truth), reusing the landed
//! reflected-term ABI ([`crate::rho_net_lower::reflect_ground_term_par`] and the E-2-D v2
//! hereditary-ground marker) — no new reduction machinery, no host evaluation of guest semantics.
//!
//! # The two reflectors
//!
//! An FLT template is a guest [`GroundTerm`] whose HOLE leaves are `^free(name)` nodes
//! (`FREE_VAR_REFLECT_LABEL`), produced once by the guest's `Term → GroundTerm` reflector. The
//! template is used two ways:
//!
//! * **PATTERN** (a receive `BindPattern`) — [`reflect_flt_pattern`]. Each declared hole becomes a
//!   match `FreeVar` and each E-2-D marker over a hole-bearing node becomes a `Wildcard`; a
//!   hole-free subtree reflects byte-for-byte as the ground reflection ([`reflect_ground_term_par`])
//!   with its real `^gnd`/`^nog` marker.
//! * **CONSTRUCTION** (a value) — [`reflect_flt_construction`] (Phase 2 Stage 2). Each hole is
//!   spliced with a typed `Par` fill; EVERY ancestor's marker is RECOMPUTED from the FILLED
//!   subtree's own ground bit (C2), never keeping a stale template `^gnd`.
//!
//! # No-Injection is structural
//!
//! The guest template is reflected ONCE from a parsed guest term; only typed reflected-`Par` FILLS
//! graft in. A rendered delimiter inside a fill can never re-open the grammar (fills never
//! concatenate into source text) — the FIP No-Injection property, enforced by construction.

use std::collections::{BTreeMap, HashMap};

use mettail_ast::types::CollectionType;
use models::create_bit_vector;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{EAnd, EEq, Expr, Par, ReceiveBind};
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_freevar_par, new_receive_par, new_wildcard_par, union,
};

use crate::rho_net_lower::{
    assemble_positional_ground_node, ground_marker_tag_par, is_marked_object_label,
    par_carries_ground_marker, reflect_ground_term_par, reflect_tag, GroundTerm,
    BOUND_VAR_REFLECT_LABEL, FREE_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
    PEANO_SUCC_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL,
};

// ── Public types ────────────────────────────────────────────────────────────────────────────

/// One declared FLT hole: a `${name}` (or `${name:Cat}`) metavariable in the surface template.
///
/// `category` is the optionally-declared guest category `Cat` the surface parser records (design
/// §Registry "Parser just records the declared `:Cat`"); `None` is the v1 default (untyped hole).
/// The admission gate ([`reflect_flt_pattern`] / [`reflect_flt_construction`]) is the sole
/// enforcement point (C5).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FltHole {
    /// The hole's metavariable name (the identifier after `$`), matched against a `^free(name)`
    /// leaf's name.
    pub name: String,
    /// The declared guest category, if the surface wrote `${name:Cat}`; `None` otherwise.
    pub category: Option<String>,
}

impl FltHole {
    /// An untyped hole `${name}`.
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into(), category: None }
    }

    /// A category-declared hole `${name:category}`.
    pub fn typed(name: impl Into<String>, category: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            category: Some(category.into()),
        }
    }
}

/// A fail-closed FLT reflection error — the C5 category/arity admission gate's typed rejections.
///
/// The gate is deliberately CLOSED: there is NO cross-context-binder corner (decision D-A makes
/// the host-side de-Bruijn shift a total, pure function — [`shift_fill_for_depth`]), so a
/// well-formed FLT template over the v1 subset never fails to reflect.
///
/// [`shift_fill_for_depth`]: crate::rho_net_flt::shift_fill_for_depth
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FltReflectError {
    /// A `^free(name)` occurrence names a hole with no provided fill (construction side) — the
    /// caller asked to fill holes but omitted this one.
    UnknownHole {
        /// The unfilled hole's name.
        hole: String,
    },
    /// A hole is declared with category `expected` but re-declared (or occurs) with an
    /// incompatible category `found` — a conflicting `${h:A}` / `${h:B}` admission failure.
    CategoryMismatch {
        /// The offending hole's name.
        hole: String,
        /// The category first declared for the hole.
        expected: String,
        /// The conflicting category.
        found: String,
    },
    /// A hole cannot be placed at its occurrence: a malformed `^free` envelope (not exactly one
    /// nullary name leaf), or a hole inside an AC-collection carrier — a position with no flat
    /// positional image in the v1 subset.
    ArityMismatch {
        /// The offending hole's name (or `"^free"` when the envelope is too malformed to name).
        hole: String,
    },
}

impl std::fmt::Display for FltReflectError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FltReflectError::UnknownHole { hole } => {
                write!(f, "FLT hole ${{{hole}}} has no provided fill")
            },
            FltReflectError::CategoryMismatch { hole, expected, found } => {
                write!(f, "FLT hole ${{{hole}}} declared as :{expected} but used as :{found}")
            },
            FltReflectError::ArityMismatch { hole } => {
                write!(
                    f,
                    "FLT hole ${{{hole}}} cannot be placed at its occurrence (no flat positional image)"
                )
            },
        }
    }
}

impl std::error::Error for FltReflectError {}

/// The reflected FLT PATTERN plus the metadata a receive builder needs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FltPatternReflection {
    /// The reflected marked-`Par` receive pattern — a tagged `EList` carrying a match `FreeVar` at
    /// each hole, a `Wildcard` at each hole-bearing node's E-2-D marker slot, and a GROUND
    /// reflected subterm elsewhere. Byte-for-byte the hand-built `hole_rendezvous_program` pattern.
    pub pattern: Par,
    /// The number of distinct match `FreeVar`s the pattern binds — one per hole OCCURRENCE (a
    /// repeated hole binds a distinct `FreeVar` each time, C3), so it equals the receive's
    /// `bind_count` / `ReceiveBind.free_count`.
    pub free_count: i32,
    /// Per-occurrence `(hole name, FreeVar level)`, in first-appearance (left-to-right pre-order)
    /// traversal order. A repeated hole appears once per occurrence with its distinct level.
    pub hole_bindings: Vec<(String, i32)>,
    /// C3 non-linearity: `(first_level, repeat_level)` pairs — each a `FreeVar` level that must
    /// equal an earlier occurrence's level, woven into the receive's `condition` by
    /// [`flt_receive_par`] as an `EEq` conjunct so the reducer commits the COMM only when the
    /// repeated captures are structurally equal.
    pub linearity_guards: Vec<(i32, i32)>,
}

// ── P1 — reflect_flt_pattern ────────────────────────────────────────────────────────────────

/// Reflect an FLT template [`GroundTerm`] into a receive PATTERN (P1).
///
/// A bottom-up walk mirroring [`reflect_ground_term_par`]'s marked reflection, diverging at exactly
/// three points:
///
/// * **(C1) marker → wildcard.** A node that (transitively) contains a hole cannot commit to a
///   `^gnd`/`^nog` marker — the hole's groundness is unknown until it is filled — so its E-2-D
///   index-1 marker slot becomes a `Wildcard`. A HOLE-FREE subtree is fully ground-determined and
///   reflects byte-for-byte as [`reflect_ground_term_par`] (real marker).
/// * **hole `^free(name ∈ holes)` → `FreeVar`.** Emits `new_freevar_par(level, ())` in
///   left-to-right first-appearance order.
/// * **`^free(name ∉ holes)` → ground `^free` literal.** A genuine free variable is matched
///   literally (reflected as the ground `^free` node).
/// * **(C3) repeated hole → distinct `FreeVar` each + an `EEq` linearity guard.**
///
/// Proven byte-for-byte equal to the hand-built `hole_rendezvous_program` pattern (the only
/// deliberate divergence is `connective_used = true`, correct for a match pattern). Fails closed
/// (C5) on a conflicting hole category declaration or a malformed hole envelope.
pub fn reflect_flt_pattern(
    term: &GroundTerm,
    holes: &[FltHole],
    fingerprint: &str,
) -> Result<FltPatternReflection, FltReflectError> {
    validate_hole_declarations(holes)?;
    let mut ctx = PatternWalk::new(holes, fingerprint);
    let (pattern, _has_hole) = ctx.reflect_node(term)?;
    Ok(FltPatternReflection {
        pattern,
        free_count: ctx.next_level,
        hole_bindings: ctx.hole_bindings,
        linearity_guards: ctx.linearity_guards,
    })
}

/// The mutable state threaded through the P1 pattern walk: hole → `FreeVar` level assignment
/// (occurrence order), the per-occurrence bindings, and the C3 linearity guard pairs.
struct PatternWalk<'a> {
    holes: &'a [FltHole],
    fingerprint: &'a str,
    next_level: i32,
    first_seen: BTreeMap<String, i32>,
    hole_bindings: Vec<(String, i32)>,
    linearity_guards: Vec<(i32, i32)>,
}

impl<'a> PatternWalk<'a> {
    fn new(holes: &'a [FltHole], fingerprint: &'a str) -> Self {
        Self {
            holes,
            fingerprint,
            next_level: 0,
            first_seen: BTreeMap::new(),
            hole_bindings: Vec::new(),
            linearity_guards: Vec::new(),
        }
    }

    fn is_hole(&self, name: &str) -> bool {
        self.holes.iter().any(|h| h.name == name)
    }

    /// Assign the next `FreeVar` level to a hole occurrence (occurrence order), recording the
    /// binding and — for a repeat — a `(first_level, this_level)` linearity guard.
    fn assign_level(&mut self, name: &str) -> i32 {
        let level = self.next_level;
        self.next_level += 1;
        match self.first_seen.get(name) {
            Some(&first) => self.linearity_guards.push((first, level)),
            None => {
                self.first_seen.insert(name.to_string(), level);
            },
        }
        self.hole_bindings.push((name.to_string(), level));
        level
    }

    /// Reflect one node, returning `(par, contains_hole)`.
    fn reflect_node(&mut self, term: &GroundTerm) -> Result<(Par, bool), FltReflectError> {
        enum PatternTask<'term> {
            Visit(&'term GroundTerm),
            Assemble {
                term: &'term GroundTerm,
                child_count: usize,
            },
        }

        // One post-order analysis gives every node its first declared hole in
        // left-to-right pre-order. The construction PDA can then collapse each
        // maximal hole-free subtree through the optimized ground reflector once,
        // avoiding both repeated scans and O(n²) reflection on deep spines.
        let first_hole = analyze_first_hole(term, |name| self.is_hole(name));
        let mut tasks = vec![PatternTask::Visit(term)];
        let mut values: Vec<(Par, bool)> = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                PatternTask::Visit(term) => {
                    let hole = first_hole
                        .get(&(term as *const GroundTerm))
                        .copied()
                        .flatten();
                    let Some(hole) = hole else {
                        values.push((reflect_ground_term_par(term, self.fingerprint), false));
                        continue;
                    };

                    if term.constructor == FREE_VAR_REFLECT_LABEL {
                        let name = free_var_name(term)?;
                        debug_assert_eq!(name, hole);
                        let level = self.assign_level(&name);
                        values.push((new_freevar_par(level, Vec::new()), true));
                    } else if term.coll_type.is_some() {
                        return Err(FltReflectError::ArityMismatch { hole: hole.to_string() });
                    } else {
                        tasks
                            .push(PatternTask::Assemble { term, child_count: term.children.len() });
                        for child in term.children.iter().rev() {
                            tasks.push(PatternTask::Visit(child));
                        }
                    }
                },
                PatternTask::Assemble { term, child_count } => {
                    let first = values
                        .len()
                        .checked_sub(child_count)
                        .expect("FLT pattern PDA lost a child result");
                    let child_values = values.split_off(first);
                    let tag = GPrivateBuilder::new_par_from_string(reflect_tag(
                        self.fingerprint,
                        &term.constructor,
                    ));
                    let mut elements = Vec::with_capacity(child_values.len() + 2);
                    elements.push(tag);
                    if is_marked_object_label(&term.constructor) {
                        elements.push(new_wildcard_par(Vec::new(), true));
                    }
                    elements.extend(child_values.into_iter().map(|(child, _)| child));
                    values.push((
                        new_elist_par(elements, Vec::new(), true, None, Vec::new(), true),
                        true,
                    ));
                },
            }
        }

        debug_assert_eq!(values.len(), 1);
        Ok(values.pop().expect("FLT pattern PDA produced no result"))
    }
}

// ── flt_receive_par ─────────────────────────────────────────────────────────────────────────

/// Assemble the FLT receive `for( @pattern <- source ) { continuation }` from a
/// [`FltPatternReflection`], weaving any C3 linearity guards and an optional caller `guard` into
/// the receive's `condition` (evaluated by the reducer in the receive's binder frame; the COMM
/// commits only when it extracts `GBool(true)`).
///
/// The continuation is supplied by the caller already referencing each captured hole as its
/// continuation-scope `BoundVar` (a `FreeVar` at level `l` binds `BoundVar(free_count - 1 - l)` —
/// the reducer's reverse De-Bruijn frame; [`FltPatternReflection::hole_bindings`] carries the
/// levels).
pub fn flt_receive_par(
    reflection: &FltPatternReflection,
    source: Par,
    guard: Option<Par>,
    continuation: Par,
) -> Par {
    let free_count = reflection.free_count;
    let condition = flt_receive_condition(&reflection.linearity_guards, guard, free_count);

    // ★ COMPILE-TIME GUARD DISCHARGE — ASSERT ONLY, NEVER BRANCH.
    //
    // A linearity guard is an `EEq(BoundVar_i, BoundVar_j)` conjunction over the receive's OWN
    // hole slots: payload-dependent by construction, so it is 0% dischargeable and this site
    // must stay wired to the machine's `check_commit`. The assertion pins that fact where the
    // guard is BUILT, so a future change that made a linearity guard variable-free would fail
    // here rather than silently become eligible for elision. See
    // `mettail_rholang_runtime::guard_discharge` for the decision this refuses to make, and
    // `rholang-runtime/tests/guard_discharge_corpus.rs::the_three_codegen_guard_sites_are_all_residual`
    // for the full `classify(..) == Residual` verdict (which additionally needs the evaluator).
    debug_assert!(
        reflection.linearity_guards.is_empty()
            || condition
                .as_ref()
                .is_some_and(|cond| !crate::guard_closure::is_binder_closed(cond)),
        "an FLT linearity guard is EEq over the receive's own hole slots and can never be \
         binder-closed; {} guard(s) produced a variable-free condition",
        reflection.linearity_guards.len(),
    );

    // The source is evaluated in the OUTER scope (its frees are the receive's frees); the
    // continuation is under `free_count` binders (its frees < free_count are bound, ≥ free_count
    // shift down to the outer frame); the case-closed condition references only bound holes, so it
    // contributes nothing to the receive's free-set.
    let recv_free = union(
        source.locally_free.clone(),
        shift_down_bits(&continuation.locally_free, free_count),
    );

    let mut receive = new_receive_par(
        vec![ReceiveBind {
            patterns: vec![reflection.pattern.clone()],
            source: Some(source),
            remainder: None,
            free_count,
        }],
        continuation,
        false,
        false,
        free_count,
        recv_free.clone(),
        false,
        recv_free,
        false,
    );
    if let Some(condition) = condition {
        if let Some(receive_msg) = receive.receives.first_mut() {
            receive_msg.condition = Some(condition);
        }
    }
    receive
}

/// Build the receive `condition` = the `EAnd` conjunction of every C3 linearity `EEq` and the
/// optional caller `guard`. `None` when there is neither (the receive stays unconditional).
fn flt_receive_condition(
    linearity_guards: &[(i32, i32)],
    guard: Option<Par>,
    free_count: i32,
) -> Option<Par> {
    let mut conjuncts: Vec<Par> = Vec::with_capacity(linearity_guards.len() + 1);
    for &(first, repeat) in linearity_guards {
        // A FreeVar level `l` binds `BoundVar(free_count - 1 - l)` in the shared reverse-De-Bruijn
        // frame the receive condition is evaluated in (F12).
        let idx0 = free_count - 1 - first;
        let idxj = free_count - 1 - repeat;
        let eq = Expr {
            expr_instance: Some(ExprInstance::EEqBody(EEq {
                p1: Some(new_boundvar_par(idx0, create_bit_vector(&[idx0 as usize]), false)),
                p2: Some(new_boundvar_par(idxj, create_bit_vector(&[idxj as usize]), false)),
            })),
        };
        let lo = idx0.min(idxj) as usize;
        let hi = idx0.max(idxj) as usize;
        conjuncts.push(par_from_expr(eq, &[lo, hi]));
    }
    if let Some(guard) = guard {
        conjuncts.push(guard);
    }
    let mut iter = conjuncts.into_iter();
    let mut combined = iter.next()?;
    for conjunct in iter {
        let free = union(combined.locally_free.clone(), conjunct.locally_free.clone());
        let and = Expr {
            expr_instance: Some(ExprInstance::EAndBody(EAnd {
                p1: Some(combined),
                p2: Some(conjunct),
            })),
        };
        let mut next = Par::default();
        next.exprs = vec![and];
        next.locally_free = free;
        next.connective_used = false;
        combined = next;
    }
    Some(combined)
}

// ── P2 — reflect_flt_construction ───────────────────────────────────────────────────────────

/// Reflect an FLT template [`GroundTerm`] into a CONSTRUCTION value (P2), splicing each hole with
/// its typed `Par` fill.
///
/// A bottom-up walk mirroring [`reflect_ground_term_par`]'s marked reflection, diverging at exactly
/// one point: a `^free(name)` leaf is replaced by the typed reflected-`Par` fill `fills[name]`
/// (NEVER text — the No-Injection substrate). The critical correctness constraint is **C2**: EVERY
/// ancestor's E-2-D marker is RECOMPUTED from its FILLED children's own ground bits
/// ([`par_carries_ground_marker`] on a fill, threaded recursively otherwise) — never keeping a
/// template `^gnd`. A fill only makes a node LESS ground (`InRhoCreeperTrace.oground`), so recompute
/// is conservatively sound; a stale `^gnd` over a `^bound`-carrying fill would let the reducer's
/// hereditary-ground guard short-circuit `^subst` to the identity, silently skipping the required β.
///
/// Round-trips: for a hole-free-after-fill closed term,
/// `reflect_flt_construction(App(^free(f), K), {f: ⟦id⟧}, fp)` is byte-for-byte
/// `reflect_ground_term_par(App(id, K), fp)`.
pub fn reflect_flt_construction(
    term: &GroundTerm,
    fills: &BTreeMap<String, Par>,
    fingerprint: &str,
) -> Result<Par, FltReflectError> {
    Ok(reflect_construction_node(term, fills, fingerprint)?.0)
}

/// Reflect one construction node, returning `(par, is_ground)` — the E-2-D hereditary-ground bit
/// threaded bottom-up (C2), so a parent recomputes its marker without re-traversing.
fn reflect_construction_node(
    term: &GroundTerm,
    fills: &BTreeMap<String, Par>,
    fingerprint: &str,
) -> Result<(Par, bool), FltReflectError> {
    enum ConstructionTask<'term> {
        Visit(&'term GroundTerm),
        Assemble {
            term: &'term GroundTerm,
            child_count: usize,
        },
    }

    let mut tasks = vec![ConstructionTask::Visit(term)];
    let mut values: Vec<(Par, bool)> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            ConstructionTask::Visit(term) => {
                if term.constructor == FREE_VAR_REFLECT_LABEL {
                    let name = free_var_name(term)?;
                    let fill = fills
                        .get(&name)
                        .ok_or(FltReflectError::UnknownHole { hole: name })?;
                    values.push((fill.clone(), par_carries_ground_marker(fill, fingerprint)));
                } else if term.coll_type.is_some() {
                    if let Some(hole) = first_fill_hole_in(term, fills) {
                        return Err(FltReflectError::ArityMismatch { hole });
                    }
                    values.push((reflect_ground_term_par(term, fingerprint), false));
                } else {
                    tasks.push(ConstructionTask::Assemble {
                        term,
                        child_count: term.children.len(),
                    });
                    for child in term.children.iter().rev() {
                        tasks.push(ConstructionTask::Visit(child));
                    }
                }
            },
            ConstructionTask::Assemble { term, child_count } => {
                let first = values
                    .len()
                    .checked_sub(child_count)
                    .expect("FLT construction PDA lost a child result");
                let children = values.split_off(first);
                values.push(assemble_positional_ground_node(term, children, fingerprint));
            },
        }
    }

    debug_assert_eq!(values.len(), 1);
    Ok(values
        .pop()
        .expect("FLT construction PDA produced no result"))
}

// ── P4 — runtime-Peano binder reflectors + the D-A host-side oshift ──────────────────────────

/// The reflected Peano numeral `⟦S(S(…Z))⟧` with `n` successors — byte-for-byte the runtime twin's
/// `opeano`/`g_bound` peano construction (`Z`/`S` are UNMARKED nullary/unary tags; the reserved-ness
/// rides the enclosing `^bound`).
pub fn peano_par(n: usize, fingerprint: &str) -> Par {
    reflect_ground_term_par(&peano_ground_term(n), fingerprint)
}

/// The reflected bound-variable leaf `⟦^bound(peano(depth))⟧` — a tagged `EList`
/// `[⌜^bound⌝, ⌜^nog⌝, ⟦peano(depth)⟧]`, OPAQUE to the host Rholang binder machinery (a plain
/// `EList`, not a host `BoundVar` Par), so a guest binder depth SURVIVES the Rholang boundary
/// (invisible to `locally_free`/`filter_and_adjust_bitset`).
pub fn bound_var_par(depth: usize, fingerprint: &str) -> Par {
    reflect_ground_term_par(
        &GroundTerm::new(BOUND_VAR_REFLECT_LABEL, vec![peano_ground_term(depth)]),
        fingerprint,
    )
}

/// D-A — the COMPLETE host-side de-Bruijn shift for splicing a fill under `depth` guest binders at
/// CONSTRUCTION time. A total, pure `Par → Par` function, PROVABLY equal to the in-Rho `^shift` TRS
/// rule (proven byte-for-byte on the reducer in the runtime twin's shift-equivalence test).
///
/// * `depth == 0` (no enclosing template binders) → identity.
/// * a `^gnd` (hereditarily-ground) fill → identity at ANY depth (`oground_shift_id`:
///   `oground t ⟹ oshift c t = t`) — this, with `depth == 0`, covers the ENTIRE primary demo.
/// * otherwise → [`host_oshift`] at cutoff `depth`, the exact image of the in-Rho
///   `^shift(peano(depth), ·)`: every `^bound n` with `n ≥ cutoff` increments (`n → S n`), a
///   `^lambda` body recurses at `cutoff + 1`, a `^free` / ground subtree is fixed, and every object
///   constructor recurses structurally at the same cutoff.
pub fn shift_fill_for_depth(fill: Par, depth: usize, fingerprint: &str) -> Par {
    if depth == 0 || par_carries_ground_marker(&fill, fingerprint) {
        return fill;
    }
    host_oshift(&fill, depth, fingerprint)
}

/// The reflected Peano numeral GroundTerm `S(S(…Z))` with `n` successors.
fn peano_ground_term(n: usize) -> GroundTerm {
    let mut peano = GroundTerm::nullary(PEANO_ZERO_REFLECT_LABEL);
    for _ in 0..n {
        peano = GroundTerm::new(PEANO_SUCC_REFLECT_LABEL, vec![peano]);
    }
    peano
}

/// The complete host-side `oshift` at cutoff `cutoff` over a reflected `Par` — the pure mirror of
/// the in-Rho `^shift` TRS receiver's arms, in the SAME dispatch order:
///
/// 1. a `^gnd` (hereditarily-ground) node is shift-invariant → returned VERBATIM (the
///    `ground_guard_case`, which fires first; also subsumes the `^free` passthrough — `^free` is
///    `^gnd`).
/// 2. `^bound n` → `n < cutoff` keeps the leaf; `n ≥ cutoff` increments to `^bound(S n)`.
/// 3. `^lambda b` → `^lambda(oshift (cutoff + 1) b)` (the cutoff descends under the binder).
/// 4. any other object node → recurse every child at the SAME cutoff, preserving the head tag and
///    (groundness-invariant under `oshift`) the E-2-D marker.
///
/// `oshift` never adds or removes a `^bound` leaf — it only renames indices — so `oground` (and
/// hence every ancestor marker) is preserved; preserving the existing marker on a rebuild is
/// therefore identical to the reducer's `tagged` recompute, keeping the shared ABI byte-identical.
fn host_oshift(par: &Par, cutoff: usize, fingerprint: &str) -> Par {
    enum Task<'par> {
        Visit {
            par: &'par Par,
            cutoff: usize,
        },
        Assemble {
            head: &'par Par,
            marker: Option<&'par Par>,
            child_count: usize,
        },
    }

    // These dispatch tokens are constant for the complete traversal. Constructing them once avoids
    // hashing the fingerprint/label pair at every node while retaining exact `Par` comparisons.
    let ground_marker = ground_marker_tag_par(fingerprint, true);
    let nonground_marker = ground_marker_tag_par(fingerprint, false);
    let bound_tag = flt_tag_par(fingerprint, BOUND_VAR_REFLECT_LABEL);
    let lambda_tag = flt_tag_par(fingerprint, LAMBDA_REFLECT_LABEL);
    let peano_zero = flt_tag_par(fingerprint, PEANO_ZERO_REFLECT_LABEL);
    let peano_succ = flt_tag_par(fingerprint, PEANO_SUCC_REFLECT_LABEL);

    let mut tasks = vec![Task::Visit { par, cutoff }];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit { par, cutoff } => {
                // (1) ground short-circuit — verbatim identity (matches `ground_guard_case`;
                // covers `^free`).
                if matches!(
                    elist_ps(par),
                    Some(ps) if ps.get(1) == Some(&ground_marker)
                ) {
                    values.push(par.clone());
                    continue;
                }
                let ps = match elist_ps(par) {
                    Some(ps) if !ps.is_empty() => ps,
                    // A non-EList leaf (a bare scalar / GString) carries no `^bound` — passthrough.
                    _ => {
                        values.push(par.clone());
                        continue;
                    },
                };
                let head = &ps[0];
                if head == &bound_tag {
                    // (2) `[⌜^bound⌝, ⌜^nog⌝, ⟦n⟧]`.
                    values.push(match peano_value_with_tags(ps.get(2), &peano_zero, &peano_succ) {
                        Some(n) if n >= cutoff => bound_var_par(n + 1, fingerprint),
                        // n < cutoff (keep) or a malformed index (e.g. a `^multilambda` GString
                        // binder leaf) → verbatim, matching the reducer's `Lt` rebuild.
                        _ => par.clone(),
                    });
                } else if head == &lambda_tag {
                    // (3) `[⌜^lambda⌝, marker, ⟦b⟧]`: descend at `cutoff + 1`.
                    tasks.push(Task::Assemble { head, marker: ps.get(1), child_count: 1 });
                    tasks.push(Task::Visit { par: &ps[2], cutoff: cutoff + 1 });
                } else {
                    // (4) generic object: descend every child at the same cutoff, preserving marker.
                    let marked =
                        ps.len() >= 2 && (ps[1] == ground_marker || ps[1] == nonground_marker);
                    let children_start = if marked { 2 } else { 1 };
                    tasks.push(Task::Assemble {
                        head,
                        marker: marked.then(|| &ps[1]),
                        child_count: ps.len() - children_start,
                    });
                    tasks.extend(
                        ps[children_start..]
                            .iter()
                            .rev()
                            .map(|par| Task::Visit { par, cutoff }),
                    );
                }
            },
            Task::Assemble { head, marker, child_count } => {
                let first = values
                    .len()
                    .checked_sub(child_count)
                    .expect("host oshift PDA lost a child result");
                let children = values.split_off(first);
                values.push(rebuild_object_node(head, marker.cloned(), children));
            },
        }
    }

    debug_assert_eq!(values.len(), 1);
    values.pop().expect("host oshift PDA produced no result")
}

/// Rebuild a reflected object `EList[head, marker?, children…]` (the shared reflected-ABI shape:
/// `locally_free` = union of the parts, both `EList`- and `Par`-level, `connective_used = false`).
/// The `marker` is threaded through unchanged (groundness is invariant under `oshift`).
fn rebuild_object_node(head: &Par, marker: Option<Par>, children: Vec<Par>) -> Par {
    let mut elements = Vec::with_capacity(children.len() + 2);
    let mut locally_free = head.locally_free.clone();
    elements.push(head.clone());
    if let Some(marker) = marker {
        // A `^gnd`/`^nog` GPrivate marker has empty `locally_free` — it never widens the free-set.
        elements.push(marker);
    }
    for child in children {
        locally_free = union(locally_free, child.locally_free.clone());
        elements.push(child);
    }
    new_elist_par(elements, locally_free.clone(), false, None, locally_free, false)
}

/// The unforgeable `GPrivate` tag `⌜label⌝` for `fingerprint` — the head-tag comparison key
/// [`host_oshift`] dispatches on (built the same way [`reflect_ground_term_par`] does).
fn flt_tag_par(fingerprint: &str, label: &str) -> Par {
    GPrivateBuilder::new_par_from_string(reflect_tag(fingerprint, label))
}

/// Decode a reflected Peano numeral `⟦S(S(…Z))⟧` back to its integer value; `None` if `par` is not
/// a well-formed Peano numeral (`Z`/`S` are UNMARKED, so the successor child is at index 1).
#[cfg(test)]
fn peano_value(par: Option<&Par>, fingerprint: &str) -> Option<usize> {
    let zero = flt_tag_par(fingerprint, PEANO_ZERO_REFLECT_LABEL);
    let succ = flt_tag_par(fingerprint, PEANO_SUCC_REFLECT_LABEL);
    peano_value_with_tags(par, &zero, &succ)
}

/// [`peano_value`] with traversal-invariant tags supplied by its caller.
fn peano_value_with_tags(par: Option<&Par>, zero: &Par, succ: &Par) -> Option<usize> {
    let mut node = par?;
    let mut count = 0usize;
    loop {
        let ps = elist_ps(node)?;
        let head = ps.first()?;
        if head == zero {
            return Some(count);
        }
        if head == succ {
            count += 1;
            node = ps.get(1)?;
        } else {
            return None;
        }
    }
}

/// Borrow a reflected object `Par`'s `EList.ps`, or `None` if `par` is not a single-`EList` Par.
fn elist_ps(par: &Par) -> Option<&Vec<Par>> {
    match par
        .exprs
        .first()
        .and_then(|expr| expr.expr_instance.as_ref())
    {
        Some(ExprInstance::EListBody(list)) => Some(&list.ps),
        _ => None,
    }
}

// ── FltReflect — the guest surface → reflected GroundTerm hinge (Stage 4) ─────────────────────

/// The syntax-independent, per-guest FLT reflection surface: parse a guest FLT template body and
/// reflect it into the [`GroundTerm`] the public reflectors ([`reflect_flt_pattern`] /
/// [`reflect_flt_construction`]) consume, with each declared hole appearing as a STABLE
/// `^free(pretty_name)` leaf.
///
/// It is a SUBTRAIT of [`mettail_runtime::Language`], so a `&dyn FltReflect` upcasts to a
/// `&dyn Language` (design §Stage-4) — a resolver can read the guest's `name()` /
/// `metadata().definition_fingerprint()` off the SAME reflector value it reflects with, keeping the
/// reflected-tag fingerprint coherent with the reflection.
///
/// This trait is homed in `rholang-codegen` (not `mettail_runtime`) precisely because its return
/// type is the codegen-owned [`GroundTerm`], which `mettail_runtime` may not name (the reverse
/// dependency edge would cycle — `formal/rocq/rho_bridge/theories/BridgeInertness.v`). The
/// per-guest implementation is generated by the `language!` macro (feature `rho-codegen`), reusing
/// the SAME `Term → GroundTerm` reflection the in-Rho match/drive invocations emit and post-passing
/// the free-variable leaf names through [`flt_normalize_hole_names`] so a hole `${f}` reflects to
/// `^free(f)` (the stable moniker `pretty_name`) rather than the reflector's unstable
/// `format!("{:?}", fv)` debug string.
pub trait FltReflect: mettail_runtime::Language {
    /// Reflect an already-parsed guest term through the generated structural bridge used by
    /// match/drive. This parser-independent seam lets integration code reuse a typed term and
    /// lets depth gates isolate reflection from parsing.
    fn reflect_flt_term(&self, term: &dyn mettail_runtime::Term) -> Result<GroundTerm, String>;

    /// Parse `body` in the guest's own surface syntax (holes rendered as ordinary guest free
    /// variables) and reflect it into a [`GroundTerm`] whose hole leaves are STABLE
    /// `^free(pretty_name)` nodes. Fails closed with a typed message on a parse error or a
    /// structurally un-reflectable subterm (a native/optional/predicate field with no positional
    /// ground image — the same fail-closed reflection contract the in-Rho match path uses).
    fn parse_and_reflect_flt(&self, body: &str) -> Result<GroundTerm, String>;

    /// Parse a structural host FLT without reconstructing guest source. Text
    /// pieces and hole terminals remain separate through guest lexing and WPDA
    /// parsing.
    fn parse_and_reflect_flt_template(
        &self,
        template: &mettail_runtime::FltNode,
    ) -> Result<GroundTerm, String>;
}

// ── FltResolve — the FLT tag → guest-reflector registry (L9-6) ─────────────────────────────────

/// The registry a Rho lowering's `PFlt` arm consults to elaborate a foreign-language template. A
/// `PFlt` node's selector (the opener payload before `:Category`, e.g. `"lambda"`) selects the
/// [`FltReflect`] guest that parses and reflects its body; the resolver maps that selector to the
/// guest. The node retains the category independently so the selected guest can reject an unknown
/// or incompatible entry category.
///
/// Behind a trait so a lowering threads a `&dyn FltResolve` (or an `Arc<dyn FltResolve>`) without
/// naming a concrete registry, and so the EMPTY default ([`EmptyFltResolver`]) can resolve nothing:
/// with it installed, every FLT-free program lowers byte-identically to the pre-L9-6 lowering (there
/// is no guest for any tag, so a `PFlt` never elaborates), and a `PFlt` bearing an unregistered tag
/// fails closed rather than fabricating a term.
pub trait FltResolve {
    /// Resolve the guest reflector registered under `tag`, or `None` for the empty-default and
    /// unregistered-tag cases.
    fn resolve(&self, tag: &str) -> Option<&dyn FltReflect>;
}

/// The EMPTY [`FltResolve`] — resolves no tag. THE zero-behavior-change default: a lowering carrying
/// it never elaborates a `PFlt`, so a program that constructs none lowers byte-identically to the
/// pre-L9-6 pipeline.
pub struct EmptyFltResolver;

impl FltResolve for EmptyFltResolver {
    fn resolve(&self, _tag: &str) -> Option<&dyn FltReflect> {
        None
    }
}

/// A concrete growable [`FltResolve`] registry: a `selector → Box<dyn FltReflect>` map. The guest
/// reflectors are the per-language `impl FltReflect for <Guest>Language` values (macro-generated
/// under feature `rho-codegen`); a caller registers each guest under the surface tag its FLT openers
/// carry (e.g. `"lambda"` in `` lambda:Term`…` `` → `LambdaLanguage`).
#[derive(Default)]
pub struct FltRegistry {
    guests: std::collections::HashMap<String, Box<dyn FltReflect>>,
}

impl FltRegistry {
    /// A registry with no guests (equivalent to [`EmptyFltResolver`], but growable).
    pub fn new() -> Self {
        Self::default()
    }

    /// Register `guest` under the surface `tag` its FLT openers carry; returns `self` for builder
    /// chaining.
    pub fn with_guest(mut self, tag: impl Into<String>, guest: Box<dyn FltReflect>) -> Self {
        self.guests.insert(tag.into(), guest);
        self
    }
}

impl FltResolve for FltRegistry {
    fn resolve(&self, tag: &str) -> Option<&dyn FltReflect> {
        self.guests.get(tag).map(|guest| guest.as_ref())
    }
}

/// Rewrite every `^free(<debug>)` leaf of a freshly-reflected FLT template so its name is the
/// moniker `pretty_name` (`^free(f)`) rather than the generated reflector's unstable
/// `format!("{:?}", fv)` string (`^free("FreeVar { unique_id: UniqueId(7), pretty_name: Some(\"f\") }")`).
///
/// This is the ONLY divergence the FLT reflection needs from the production `Term → GroundTerm`
/// reflector, so the macro-generated [`FltReflect`] impl reuses that reflector verbatim and applies
/// this pure post-pass. It preserves every other node — constructor label, child order,
/// `coll_type` (so a hole-free AC collection subterm keeps its native carrier), the `^bound(peano)`
/// binder leaves — touching only `^free` name leaves. A leaf whose debug string carries no
/// `pretty_name` hint (an anonymous free variable) is left verbatim, so it still reflects as a
/// ground `^free` literal (matched literally by [`reflect_flt_pattern`]).
pub fn flt_normalize_hole_names(term: GroundTerm) -> GroundTerm {
    enum NormalizeTask {
        Visit(GroundTerm),
        Assemble {
            constructor: String,
            coll_type: Option<CollectionType>,
            child_count: usize,
        },
    }

    let mut tasks = vec![NormalizeTask::Visit(term)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            NormalizeTask::Visit(mut term) => {
                let constructor = std::mem::take(&mut term.constructor);
                let children = std::mem::take(&mut term.children);
                let coll_type = term.coll_type.take();
                if constructor == FREE_VAR_REFLECT_LABEL {
                    if let [name_leaf] = children.as_slice() {
                        if name_leaf.children.is_empty() && name_leaf.coll_type.is_none() {
                            let pretty = parse_pretty_name(&name_leaf.constructor)
                                .unwrap_or_else(|| name_leaf.constructor.clone());
                            values.push(GroundTerm {
                                constructor,
                                children: vec![GroundTerm::nullary(pretty)],
                                coll_type,
                            });
                            continue;
                        }
                    }
                }

                let child_count = children.len();
                tasks.push(NormalizeTask::Assemble { constructor, coll_type, child_count });
                for child in children.into_iter().rev() {
                    tasks.push(NormalizeTask::Visit(child));
                }
            },
            NormalizeTask::Assemble { constructor, coll_type, child_count } => {
                let first_child = values
                    .len()
                    .checked_sub(child_count)
                    .expect("FLT hole-normalization PDA lost a child result");
                let children = values.split_off(first_child);
                values.push(GroundTerm { constructor, children, coll_type });
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values
        .pop()
        .expect("FLT hole-normalization PDA produced no result")
}

/// Extract the `pretty_name` hint from a moniker `FreeVar` debug string
/// (`FreeVar { unique_id: UniqueId(7), pretty_name: Some("x") }` — the exact shape the generated
/// reflector emits via `format!("{:?}", fv)`); `None` when the string carries no `Some("…")` hint
/// (an anonymous free variable). Mirrors `repl::observation_surface::parse_pretty_name` (the
/// display-side twin of this reflection-side normalization).
fn parse_pretty_name(debug: &str) -> Option<String> {
    let marker = "pretty_name: Some(\"";
    let start = debug.find(marker)? + marker.len();
    let rest = &debug[start..];
    let end = rest.find('"')?;
    Some(rest[..end].to_string())
}

// ── Shared helpers ──────────────────────────────────────────────────────────────────────────

/// Wrap one `Expr` in a `Par` carrying `free` as its `locally_free` bitset (empty → empty vec, so a
/// free-free expr stays byte-clean rather than a `[0]` sentinel).
fn par_from_expr(instance: Expr, free: &[usize]) -> Par {
    let mut par = Par::default();
    par.exprs = vec![instance];
    par.locally_free = if free.is_empty() {
        Vec::new()
    } else {
        create_bit_vector(free)
    };
    par.connective_used = false;
    par
}

/// Shift a `locally_free` bitset down by `n` binders: keep set bits ≥ `n`, remap to `bit - n`. An
/// empty result is the empty vec (never a `[0]` sentinel).
fn shift_down_bits(bits: &[u8], n: i32) -> Vec<u8> {
    let n = n.max(0) as usize;
    let shifted: Vec<usize> = bits
        .iter()
        .enumerate()
        .filter_map(|(index, &bit)| (bit != 0 && index >= n).then_some(index - n))
        .collect();
    if shifted.is_empty() {
        Vec::new()
    } else {
        create_bit_vector(&shifted)
    }
}

/// Extract the name of a `^free(name)` leaf, validating its envelope (exactly one nullary name
/// child). A malformed envelope fails closed as [`FltReflectError::ArityMismatch`].
fn free_var_name(term: &GroundTerm) -> Result<String, FltReflectError> {
    match term.children.as_slice() {
        [name_node] if name_node.children.is_empty() && name_node.coll_type.is_none() => {
            Ok(name_node.constructor.clone())
        },
        _ => Err(FltReflectError::ArityMismatch {
            hole: term
                .children
                .first()
                .map(|n| n.constructor.clone())
                .unwrap_or_else(|| FREE_VAR_REFLECT_LABEL.to_string()),
        }),
    }
}

/// Analyze declared-hole reachability once, bottom-up.
///
/// Each entry stores the first hole in the same left-to-right pre-order the
/// recursive reflector used. A `^free` envelope is terminal for this analysis:
/// an undeclared free literal cannot expose a nested hole through its payload.
fn analyze_first_hole<'term>(
    root: &'term GroundTerm,
    is_hole: impl Fn(&str) -> bool,
) -> HashMap<*const GroundTerm, Option<&'term str>> {
    enum Task<'term> {
        Visit(&'term GroundTerm),
        Assemble(&'term GroundTerm),
    }

    let mut tasks = vec![Task::Visit(root)];
    let mut analysis = HashMap::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(term) if term.constructor == FREE_VAR_REFLECT_LABEL => {
                let first = term
                    .children
                    .first()
                    .map(|name| name.constructor.as_str())
                    .filter(|name| is_hole(name));
                analysis.insert(term as *const GroundTerm, first);
            },
            Task::Visit(term) => {
                tasks.push(Task::Assemble(term));
                for child in term.children.iter().rev() {
                    tasks.push(Task::Visit(child));
                }
            },
            Task::Assemble(term) => {
                let first = term.children.iter().find_map(|child| {
                    analysis
                        .get(&(child as *const GroundTerm))
                        .copied()
                        .flatten()
                });
                analysis.insert(term as *const GroundTerm, first);
            },
        }
    }
    analysis
}

/// The first (pre-order) `^free(name)` leaf whose `name` is a key of `fills`, for error reporting
/// on the construction side.
fn first_fill_hole_in(term: &GroundTerm, fills: &BTreeMap<String, Par>) -> Option<String> {
    let mut work = vec![term];
    while let Some(term) = work.pop() {
        if term.constructor == FREE_VAR_REFLECT_LABEL {
            if let Some(name_node) = term.children.first() {
                if fills.contains_key(&name_node.constructor) {
                    return Some(name_node.constructor.clone());
                }
            }
            continue;
        }
        for child in term.children.iter().rev() {
            work.push(child);
        }
    }
    None
}

/// Validate the declared hole set (C5): a hole re-declared with a conflicting category fails
/// closed as [`FltReflectError::CategoryMismatch`].
fn validate_hole_declarations(holes: &[FltHole]) -> Result<(), FltReflectError> {
    let mut seen: BTreeMap<&str, &Option<String>> = BTreeMap::new();
    for hole in holes {
        match seen.get(hole.name.as_str()) {
            Some(prev) if **prev != hole.category => {
                return Err(FltReflectError::CategoryMismatch {
                    hole: hole.name.clone(),
                    expected: (**prev).clone().unwrap_or_default(),
                    found: hole.category.clone().unwrap_or_default(),
                });
            },
            Some(_) => {},
            None => {
                seen.insert(hole.name.as_str(), &hole.category);
            },
        }
    }
    Ok(())
}

#[cfg(test)]
#[path = "../tests/support/rho_net_flt_oshift_recursive_oracle.rs"]
mod oshift_recursive_oracle;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rho_net_lower::{
        ground_marker_tag_par, reflected_tag_string, BOUND_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
        PEANO_SUCC_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL,
    };
    use models::rust::utils::{new_freevar_par, new_wildcard_par};

    /// The current production Lambda fingerprint (Phase-1). The byte-for-byte gate is
    /// self-consistent under ANY fingerprint (both sides share `FP`); this value ties the anchor
    /// to the real `LambdaLanguage` the runtime twin drives.
    const FP: &str = "mettail-langdef-v1:6ef0c40636bb0bca";

    // ── guest GroundTerm builders (mirror flt_abi_over_rspace.rs's g_* helpers) ──────────────
    fn g_bound(depth: usize) -> GroundTerm {
        let mut peano = GroundTerm::nullary(PEANO_ZERO_REFLECT_LABEL);
        for _ in 0..depth {
            peano = GroundTerm::new(PEANO_SUCC_REFLECT_LABEL, vec![peano]);
        }
        GroundTerm::new(BOUND_VAR_REFLECT_LABEL, vec![peano])
    }
    fn g_lambda(body: GroundTerm) -> GroundTerm {
        GroundTerm::new(LAMBDA_REFLECT_LABEL, vec![body])
    }
    /// `K = lam a. lam b. a` — the committed golden (`λ.λ.1`).
    fn g_k() -> GroundTerm {
        g_lambda(g_lambda(g_bound(1)))
    }
    /// A `^free(name)` hole/free leaf, exactly as the guest `Term → GroundTerm` reflector emits it.
    fn g_free(name: &str) -> GroundTerm {
        GroundTerm::new(FREE_VAR_REFLECT_LABEL, vec![GroundTerm::nullary(name)])
    }
    fn g_app(fun: GroundTerm, arg: GroundTerm) -> GroundTerm {
        GroundTerm::new("App", vec![fun, arg])
    }

    /// THE Stage-1 anchor: `reflect_flt_pattern(App(^free(f), K), [{f}], fp).pattern` is
    /// BYTE-FOR-BYTE the hand-built `hole_rendezvous_program` receive pattern
    /// `[⌜App⌝, _, ${f}, ⟦K⟧]` (the sole deliberate divergence — `connective_used = true` — is
    /// correct for a match pattern).
    #[test]
    fn reflect_flt_pattern_is_byte_identical_to_the_hole_rendezvous_pattern() {
        let term = GroundTerm::new("App", vec![g_free("f"), g_k()]);
        let holes = [FltHole::new("f")];
        let reflection =
            reflect_flt_pattern(&term, &holes, FP).expect("App(^free(f), K) reflects to a pattern");

        // The hand-built pattern, reconstructed with the `models` builders exactly as the runtime
        // twin's `hole_rendezvous_program` does: `[⌜App⌝, wildcard, FreeVar(0), ⟦K⟧]`,
        // locally_free = ∅, connective_used = true.
        let app_tag = GPrivateBuilder::new_par_from_string(reflected_tag_string(FP, "App"));
        let k_reflected = reflect_ground_term_par(&g_k(), FP);
        let expected = new_elist_par(
            vec![
                app_tag,
                new_wildcard_par(Vec::new(), true),
                new_freevar_par(0, Vec::new()),
                k_reflected,
            ],
            Vec::new(),
            true,
            None,
            Vec::new(),
            true,
        );

        assert_eq!(
            reflection.pattern, expected,
            "the reflected FLT pattern must be byte-for-byte the hand-built hole_rendezvous pattern"
        );
        assert_eq!(reflection.free_count, 1, "one hole occurrence ⟹ one FreeVar");
        assert_eq!(reflection.hole_bindings, vec![("f".to_string(), 0)], "f binds FreeVar(0)");
        assert!(reflection.linearity_guards.is_empty(), "no repeated hole ⟹ no linearity guard");
    }

    /// A hole-free ground argument keeps its REAL `^nog` marker (byte-for-byte the ground
    /// reflection), while the enclosing hole-bearing App node's marker is a wildcard — the two
    /// diverge exactly as C1 prescribes.
    #[test]
    fn hole_free_subtree_keeps_its_real_marker() {
        let term = GroundTerm::new("App", vec![g_free("f"), g_k()]);
        let holes = [FltHole::new("f")];
        let reflection = reflect_flt_pattern(&term, &holes, FP).expect("reflects");

        // Index 3 (the ⟦K⟧ argument) must equal the standalone ground reflection of K.
        let ExprInstance::EListBody(list) = reflection
            .pattern
            .exprs
            .first()
            .and_then(|e| e.expr_instance.as_ref())
            .expect("pattern is an EList")
        else {
            panic!("pattern must be an EList");
        };
        assert_eq!(list.ps.len(), 4, "[⌜App⌝, marker, hole, ⟦K⟧]");
        assert_eq!(list.ps[3], reflect_ground_term_par(&g_k(), FP), "⟦K⟧ keeps its real marker");
        // The marker slot (index 1) is a wildcard, NOT the ground marker token.
        assert_eq!(list.ps[1], new_wildcard_par(Vec::new(), true), "the App marker is wildcarded");
    }

    /// A bare whole-term hole `${t}` reflects to just `FreeVar(0)` — the Beat-5 consumer-1 shape.
    #[test]
    fn bare_hole_reflects_to_a_freevar() {
        let reflection =
            reflect_flt_pattern(&g_free("t"), &[FltHole::new("t")], FP).expect("reflects");
        assert_eq!(reflection.pattern, new_freevar_par(0, Vec::new()));
        assert_eq!(reflection.free_count, 1);
    }

    // ── Stage 4 — the guest-surface hole-name normalization (FltReflect post-pass) ──────────────

    /// `parse_pretty_name` recovers the moniker `pretty_name` hint from the reflector's
    /// `format!("{:?}", fv)` debug string, and returns `None` for an anonymous free variable.
    #[test]
    fn parse_pretty_name_recovers_the_moniker_hint() {
        assert_eq!(
            parse_pretty_name("FreeVar { unique_id: UniqueId(7), pretty_name: Some(\"f\") }"),
            Some("f".to_string())
        );
        assert_eq!(
            parse_pretty_name("FreeVar { unique_id: UniqueId(12), pretty_name: None }"),
            None
        );
    }

    /// THE Stage-4 unit anchor: normalizing the reflector's debug-named `^free` leaf of
    /// `App(^free("FreeVar { … pretty_name: Some(\"f\") }"), K)` yields `App(^free(f), K)` — the
    /// STABLE hole leaf `reflect_flt_pattern` matches against a declared `${f}` — while the
    /// hole-free `K` subtree (its `^bound(peano)` binder leaves) is untouched.
    #[test]
    fn flt_normalize_hole_names_stabilizes_the_free_leaf() {
        let debug = "FreeVar { unique_id: UniqueId(7), pretty_name: Some(\"f\") }";
        let reflected = GroundTerm::new("App", vec![g_free(debug), g_k()]);
        let normalized = flt_normalize_hole_names(reflected);
        assert_eq!(
            normalized,
            GroundTerm::new("App", vec![g_free("f"), g_k()]),
            "the debug-named ^free leaf normalizes to the stable ^free(f); K is untouched"
        );
        // The normalized template is byte-identical to the hand-built `App(^free(f), K)` reflection.
        assert_eq!(
            reflect_flt_pattern(&normalized, &[FltHole::new("f")], FP)
                .expect("normalized template reflects")
                .pattern,
            reflect_flt_pattern(
                &GroundTerm::new("App", vec![g_free("f"), g_k()]),
                &[FltHole::new("f")],
                FP
            )
            .expect("hand-built template reflects")
            .pattern,
        );
    }

    /// An anonymous free leaf (no `pretty_name` hint) is left verbatim (still a ground `^free`
    /// literal), and `coll_type` on any node is preserved by the walk.
    #[test]
    fn flt_normalize_hole_names_preserves_anonymous_and_collections() {
        let anon = "FreeVar { unique_id: UniqueId(3), pretty_name: None }";
        assert_eq!(
            flt_normalize_hole_names(g_free(anon)),
            g_free(anon),
            "anonymous free leaf verbatim"
        );

        // A collection node keeps its coll_type through the normalization walk.
        let bag = GroundTerm::collection(
            mettail_ast::types::CollectionType::HashBag,
            "PPar",
            vec![g_free("FreeVar { unique_id: UniqueId(1), pretty_name: Some(\"x\") }")],
        );
        let normalized = flt_normalize_hole_names(bag);
        assert_eq!(normalized.coll_type, Some(mettail_ast::types::CollectionType::HashBag));
        assert_eq!(
            normalized.children[0],
            g_free("x"),
            "the bag element's ^free leaf still normalizes"
        );
    }

    /// A free leaf whose name is NOT a declared hole reflects to the GROUND `^free` literal
    /// (matched literally), never a `FreeVar`.
    #[test]
    fn non_hole_free_var_reflects_as_ground_literal() {
        let reflection = reflect_flt_pattern(&g_free("y"), &[], FP).expect("reflects");
        assert_eq!(reflection.pattern, reflect_ground_term_par(&g_free("y"), FP));
        assert_eq!(reflection.free_count, 0, "no holes ⟹ no FreeVars");
    }

    /// C3: a repeated hole binds a DISTINCT FreeVar each occurrence (levels 0, 1 in left-to-right
    /// order) and records one `(0, 1)` linearity guard.
    #[test]
    fn repeated_hole_binds_distinct_freevars_with_a_linearity_guard() {
        let term = GroundTerm::new("App", vec![g_free("f"), g_free("f")]);
        let reflection = reflect_flt_pattern(&term, &[FltHole::new("f")], FP).expect("reflects");
        assert_eq!(reflection.free_count, 2, "two occurrences ⟹ two FreeVars");
        assert_eq!(
            reflection.hole_bindings,
            vec![("f".to_string(), 0), ("f".to_string(), 1)],
            "left-to-right: first f = FreeVar(0), second f = FreeVar(1)"
        );
        assert_eq!(reflection.linearity_guards, vec![(0, 1)], "FreeVar(0) must EEq FreeVar(1)");

        let ExprInstance::EListBody(list) = reflection
            .pattern
            .exprs
            .first()
            .and_then(|e| e.expr_instance.as_ref())
            .expect("EList")
        else {
            panic!("EList");
        };
        assert_eq!(list.ps[2], new_freevar_par(0, Vec::new()), "index 2 = FreeVar(0)");
        assert_eq!(list.ps[3], new_freevar_par(1, Vec::new()), "index 3 = FreeVar(1)");
    }

    /// A conflicting category re-declaration fails closed (C5).
    #[test]
    fn conflicting_hole_category_is_rejected() {
        let holes = [FltHole::typed("f", "Proc"), FltHole::typed("f", "Name")];
        let err = reflect_flt_pattern(&g_free("f"), &holes, FP).expect_err("must reject");
        assert_eq!(
            err,
            FltReflectError::CategoryMismatch {
                hole: "f".to_string(),
                expected: "Proc".to_string(),
                found: "Name".to_string(),
            }
        );
    }

    /// The C3 linearity guard is woven into the receive's `condition` as an `EEq` over the two
    /// captured slots (repeated-hole occurrences bind `BoundVar(free_count-1-level)`).
    #[test]
    fn flt_receive_weaves_linearity_into_the_condition() {
        let term = GroundTerm::new("App", vec![g_free("f"), g_free("f")]);
        let reflection = reflect_flt_pattern(&term, &[FltHole::new("f")], FP).expect("reflects");
        let source = models::rust::utils::new_gstring_par("fltX".to_string(), Vec::new(), false);
        let continuation =
            models::rust::utils::new_gstring_par("done".to_string(), Vec::new(), false);
        let receive = flt_receive_par(&reflection, source, None, continuation);
        let condition = receive.receives[0]
            .condition
            .as_ref()
            .expect("a repeated hole installs a receive condition");
        // free_count = 2, so FreeVar(0) → BoundVar(1) and FreeVar(1) → BoundVar(0): EEq(BoundVar(1), BoundVar(0)).
        assert!(
            matches!(
                condition
                    .exprs
                    .first()
                    .and_then(|e| e.expr_instance.as_ref()),
                Some(ExprInstance::EEqBody(_))
            ),
            "the condition is an EEq over the two captured occurrences"
        );
    }

    // ── P2 — construction ────────────────────────────────────────────────────────────────────

    /// `id = lam x. x` — non-ground (contains `^bound`).
    fn g_id() -> GroundTerm {
        g_lambda(g_bound(0))
    }
    /// A nullary user constructor `A` — hereditarily ground.
    fn g_nullary(label: &str) -> GroundTerm {
        GroundTerm::nullary(label)
    }

    /// THE Stage-2 round-trip gate: `reflect_flt_construction(App(^free(f), K), {f: ⟦id⟧}, fp)` is
    /// BYTE-FOR-BYTE `reflect_ground_term_par(App(id, K), fp)`.
    #[test]
    fn reflect_flt_construction_round_trips_to_the_ground_reflection() {
        let template = GroundTerm::new("App", vec![g_free("f"), g_k()]);
        let fills: BTreeMap<String, Par> =
            [("f".to_string(), reflect_ground_term_par(&g_id(), FP))]
                .into_iter()
                .collect();

        let constructed = reflect_flt_construction(&template, &fills, FP).expect("constructs");
        let ground = reflect_ground_term_par(&GroundTerm::new("App", vec![g_id(), g_k()]), FP);
        assert_eq!(
            constructed, ground,
            "filling ${{f}} with ⟦id⟧ must round-trip byte-for-byte to ⟦App(id, K)⟧"
        );

        // The recomputed App marker is ^nog (id + K both carry ^bound ⟹ non-ground).
        let ExprInstance::EListBody(list) = constructed
            .exprs
            .first()
            .and_then(|e| e.expr_instance.as_ref())
            .expect("EList")
        else {
            panic!("EList");
        };
        assert_eq!(
            list.ps[1],
            ground_marker_tag_par(FP, false),
            "the App marker is recomputed ^nog over the non-ground fill"
        );
    }

    /// C2 NECESSITY (structural): the SAME template node's marker is recomputed from the FILL's
    /// ground bit — `^gnd` when the fill is a ground nullary, `^nog` when the fill carries `^bound`.
    /// A stale template marker would be wrong in one of the two cases.
    #[test]
    fn reflect_flt_construction_recomputes_marker_from_the_fill() {
        // `Foo(^free(x))` — Foo is a user constructor (marked object).
        let template = GroundTerm::new("Foo", vec![g_free("x")]);

        // (a) fill x with a GROUND nullary ⟦A⟧ ⟹ Foo is hereditarily ground ⟹ ^gnd.
        let ground_fill: BTreeMap<String, Par> =
            [("x".to_string(), reflect_ground_term_par(&g_nullary("A"), FP))]
                .into_iter()
                .collect();
        let with_ground =
            reflect_flt_construction(&template, &ground_fill, FP).expect("constructs");
        assert_eq!(
            marker_of(&with_ground),
            ground_marker_tag_par(FP, true),
            "a ground fill ⟹ Foo marker recomputed to ^gnd"
        );

        // (b) fill x with a `^bound`-carrying reflected term ⟹ Foo is NOT ground ⟹ ^nog.
        //     (A stale template ^gnd here would let the reducer short-circuit subst — the C2 hazard.)
        let bound_fill: BTreeMap<String, Par> =
            [("x".to_string(), reflect_ground_term_par(&g_bound(0), FP))]
                .into_iter()
                .collect();
        let with_bound = reflect_flt_construction(&template, &bound_fill, FP).expect("constructs");
        assert_eq!(
            marker_of(&with_bound),
            ground_marker_tag_par(FP, false),
            "a ^bound-carrying fill ⟹ Foo marker recomputed to ^nog (C2 — not a stale ^gnd)"
        );
    }

    /// An unfilled hole fails closed as `UnknownHole`.
    #[test]
    fn reflect_flt_construction_unfilled_hole_is_rejected() {
        let template = GroundTerm::new("App", vec![g_free("f"), g_k()]);
        let err =
            reflect_flt_construction(&template, &BTreeMap::new(), FP).expect_err("must reject");
        assert_eq!(err, FltReflectError::UnknownHole { hole: "f".to_string() });
    }

    /// The index-1 E-2-D marker of a reflected object `Par`.
    fn marker_of(par: &Par) -> Par {
        let ExprInstance::EListBody(list) = par
            .exprs
            .first()
            .and_then(|e| e.expr_instance.as_ref())
            .expect("EList")
        else {
            panic!("EList");
        };
        list.ps[1].clone()
    }

    // ── P4 — runtime-Peano binder reflectors + host-side oshift ───────────────────────────────

    /// `peano_par`/`bound_var_par` reflect the same shapes the runtime twin's `opeano`/`g_bound`
    /// build (self-consistent with the ground reflector).
    #[test]
    fn peano_and_bound_var_reflect_the_twin_shapes() {
        assert_eq!(peano_par(0, FP), reflect_ground_term_par(&peano_ground_term(0), FP));
        assert_eq!(peano_par(3, FP), reflect_ground_term_par(&peano_ground_term(3), FP));
        assert_eq!(bound_var_par(0, FP), reflect_ground_term_par(&g_bound(0), FP));
        assert_eq!(bound_var_par(2, FP), reflect_ground_term_par(&g_bound(2), FP));
        // Peano round-trips through the private decoder.
        assert_eq!(peano_value(Some(&peano_par(4, FP)), FP), Some(4));
    }

    /// GATE (binder-depth preservation): a `^bound(peano(n))` leaf under a `^lambda` in an FLT
    /// pattern is preserved as `⟦^bound(peano(n))⟧` — the guest binder depth survives reflection.
    #[test]
    fn reflect_flt_pattern_preserves_binder_depth() {
        // Pattern `^lambda(App(${f}, ^bound(1)))`.
        let term = g_lambda(g_app(g_free("f"), g_bound(1)));
        let reflection = reflect_flt_pattern(&term, &[FltHole::new("f")], FP).expect("reflects");

        // pattern = [⌜^lambda⌝, wildcard, body]; body = [⌜App⌝, wildcard, FreeVar(0), ⟦^bound(1)⟧].
        let lambda_ps = elist_ps(&reflection.pattern).expect("^lambda EList");
        let body_ps = elist_ps(&lambda_ps[2]).expect("App EList");
        assert_eq!(body_ps.len(), 4, "[⌜App⌝, marker, hole, ⟦^bound(1)⟧]");
        assert_eq!(
            body_ps[3],
            bound_var_par(1, FP),
            "the ^bound(1) leaf under the ^lambda is preserved at depth 1"
        );
    }

    /// GATE (identity cases): `depth == 0` and a `^gnd` fill are the identity; a CLOSED non-ground
    /// term (every `^bound` below its binder) is also unchanged by the structural oshift.
    #[test]
    fn shift_fill_for_depth_identity_cases() {
        let open = reflect_ground_term_par(&g_app(g_bound(0), g_bound(1)), FP);
        assert_eq!(
            shift_fill_for_depth(open.clone(), 0, FP),
            open,
            "depth 0 is the identity (no enclosing template binder)"
        );

        let ground = reflect_ground_term_par(&g_nullary("A"), FP); // ⟦A⟧ is ^gnd
        assert_eq!(
            shift_fill_for_depth(ground.clone(), 5, FP),
            ground,
            "a ^gnd fill is shift-invariant at any depth (oground_shift_id)"
        );

        let closed = reflect_ground_term_par(&g_k(), FP); // K = λλ.^bound(1), closed (^nog)
        assert_eq!(
            shift_fill_for_depth(closed.clone(), 1, FP),
            closed,
            "a closed term (every ^bound below its binder) is unchanged by oshift"
        );
    }

    /// The host-side oshift EQUALS the reflected image of the hand-computed shift: `oshift 1` keeps
    /// `^bound 0`, sends `^bound 1 → ^bound 2`, and descends a `^lambda` at `cutoff + 1`. (The
    /// runtime twin proves this equals the in-Rho `^shift(S Z, ·)` NF byte-for-byte on the reducer.)
    #[test]
    fn host_oshift_matches_the_hand_computed_shift() {
        // oshift 1 (App(^bound 0, ^bound 1)) = App(^bound 0, ^bound 2).
        let open = reflect_ground_term_par(&g_app(g_bound(0), g_bound(1)), FP);
        assert_eq!(
            shift_fill_for_depth(open, 1, FP),
            reflect_ground_term_par(&g_app(g_bound(0), g_bound(2)), FP),
            "oshift 1 keeps ^bound 0 and shifts ^bound 1 → ^bound 2"
        );

        // oshift 1 (^lambda(App(^bound 1, ^bound 2))) = ^lambda(App(^bound 1, ^bound 3)): under the
        // ^lambda the cutoff is 2, so ^bound 1 stays and ^bound 2 → ^bound 3.
        let under_binder = reflect_ground_term_par(&g_lambda(g_app(g_bound(1), g_bound(2))), FP);
        assert_eq!(
            shift_fill_for_depth(under_binder, 1, FP),
            reflect_ground_term_par(&g_lambda(g_app(g_bound(1), g_bound(3))), FP),
            "the cutoff descends under the ^lambda: ^bound 1 kept, ^bound 2 → ^bound 3"
        );
    }
}
