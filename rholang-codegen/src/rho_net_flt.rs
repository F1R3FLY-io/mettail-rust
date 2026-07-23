//! FLT (Foreign Language Term) Phase 2 — the PUBLIC reflector API.
//!
//! This module is the public, syntax-independent hinge between an FLT surface template
//! (`` lam`App(${f}, K)` ``) and the reflected-`Par` shapes the installed set-automaton / driver
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

use std::collections::BTreeMap;

use models::create_bit_vector;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{EAnd, EEq, Expr, Par, ReceiveBind};
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_freevar_par, new_receive_par, new_wildcard_par, union,
};

use crate::rho_net_lower::{
    is_marked_object_label, reflect_ground_term_par, reflect_tag, GroundTerm, FREE_VAR_REFLECT_LABEL,
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
        Self { name: name.into(), category: Some(category.into()) }
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
            FltReflectError::CategoryMismatch { hole, expected, found } => write!(
                f,
                "FLT hole ${{{hole}}} declared as :{expected} but used as :{found}"
            ),
            FltReflectError::ArityMismatch { hole } => {
                write!(f, "FLT hole ${{{hole}}} cannot be placed at its occurrence (no flat positional image)")
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
        // A `^free` leaf: a hole (→ FreeVar) or a genuine free literal (→ ground reflection).
        if term.constructor == FREE_VAR_REFLECT_LABEL {
            let name = free_var_name(term)?;
            if self.is_hole(&name) {
                let level = self.assign_level(&name);
                return Ok((new_freevar_par(level, Vec::new()), true));
            }
            return Ok((reflect_ground_term_par(term, self.fingerprint), false));
        }

        // A hole-free subtree is fully ground-determined: byte-for-byte the ground reflection
        // (real E-2-D marker). This is the ONLY path a hole-free child of a hole-bearing node
        // takes, so a captured ground subpattern keeps its real `^gnd`/`^nog` marker.
        if !ground_term_contains_hole(term, self.holes) {
            return Ok((reflect_ground_term_par(term, self.fingerprint), false));
        }

        // A hole inside an AC-collection carrier has no flat positional image in the v1 subset:
        // fail closed rather than mis-reflect (the carrier is order-independent, not a tagged
        // EList). Hole-free collections took the ground path above.
        if term.coll_type.is_some() {
            return Err(FltReflectError::ArityMismatch {
                hole: first_hole_name_in(term, self.holes).unwrap_or_else(|| "^free".to_string()),
            });
        }

        // A hole-bearing object/constructor node → a connective pattern EList. (C1) its marker
        // slot is a Wildcard; children are reflected in order.
        let mut child_pars = Vec::with_capacity(term.children.len());
        for child in &term.children {
            let (child_par, _child_hole) = self.reflect_node(child)?;
            child_pars.push(child_par);
        }
        let tag =
            GPrivateBuilder::new_par_from_string(reflect_tag(self.fingerprint, &term.constructor));
        let mut elements = Vec::with_capacity(child_pars.len() + 2);
        elements.push(tag);
        if is_marked_object_label(&term.constructor) {
            // (C1): the E-2-D index-1 hereditary-ground marker becomes a wildcard over a
            // hole-bearing node.
            elements.push(new_wildcard_par(Vec::new(), true));
        }
        elements.extend(child_pars);
        // An FLT pattern carries only FreeVar/Wildcard connectives + ground reflections, none of
        // which contribute a locally-free (de-Bruijn) index — so the pattern's free-set is empty.
        Ok((
            new_elist_par(elements, Vec::new(), true, None, Vec::new(), true),
            true,
        ))
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
        combined = Par { exprs: vec![and], locally_free: free, connective_used: false, ..Par::default() };
    }
    Some(combined)
}

// ── Shared helpers ──────────────────────────────────────────────────────────────────────────

/// Wrap one `Expr` in a `Par` carrying `free` as its `locally_free` bitset (empty → empty vec, so a
/// free-free expr stays byte-clean rather than a `[0]` sentinel).
fn par_from_expr(instance: Expr, free: &[usize]) -> Par {
    Par {
        exprs: vec![instance],
        locally_free: if free.is_empty() { Vec::new() } else { create_bit_vector(free) },
        connective_used: false,
        ..Par::default()
    }
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

/// Is any `^free(name)` leaf with `name ∈ holes` present anywhere in `term`?
fn ground_term_contains_hole(term: &GroundTerm, holes: &[FltHole]) -> bool {
    if term.constructor == FREE_VAR_REFLECT_LABEL {
        return term
            .children
            .first()
            .is_some_and(|name_node| holes.iter().any(|h| h.name == name_node.constructor));
    }
    term.children
        .iter()
        .any(|child| ground_term_contains_hole(child, holes))
}

/// The first (pre-order) hole name occurring in `term`, for error reporting.
fn first_hole_name_in(term: &GroundTerm, holes: &[FltHole]) -> Option<String> {
    if term.constructor == FREE_VAR_REFLECT_LABEL {
        if let Some(name_node) = term.children.first() {
            if holes.iter().any(|h| h.name == name_node.constructor) {
                return Some(name_node.constructor.clone());
            }
        }
        return None;
    }
    term.children
        .iter()
        .find_map(|child| first_hole_name_in(child, holes))
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
mod tests {
    use super::*;
    use crate::rho_net_lower::{
        reflected_tag_string, BOUND_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
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
        let reflection = reflect_flt_pattern(&g_free("t"), &[FltHole::new("t")], FP).expect("reflects");
        assert_eq!(reflection.pattern, new_freevar_par(0, Vec::new()));
        assert_eq!(reflection.free_count, 1);
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
        let reflection =
            reflect_flt_pattern(&term, &[FltHole::new("f")], FP).expect("reflects");
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
        let continuation = models::rust::utils::new_gstring_par("done".to_string(), Vec::new(), false);
        let receive = flt_receive_par(&reflection, source, None, continuation);
        let condition = receive.receives[0]
            .condition
            .as_ref()
            .expect("a repeated hole installs a receive condition");
        // free_count = 2, so FreeVar(0) → BoundVar(1) and FreeVar(1) → BoundVar(0): EEq(BoundVar(1), BoundVar(0)).
        assert!(
            matches!(
                condition.exprs.first().and_then(|e| e.expr_instance.as_ref()),
                Some(ExprInstance::EEqBody(_))
            ),
            "the condition is an EEq over the two captured occurrences"
        );
    }
}
