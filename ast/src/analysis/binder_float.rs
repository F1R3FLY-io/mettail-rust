//! Shared, node-independent analysis of declared binder-float equations.

use std::collections::HashSet;

use crate::grammar::{GrammarItem, GrammarRule, NonTerminalKind, TermParam};
use crate::language::{Equation, FreshnessCondition, FreshnessTarget, LanguageDef, Premise};
use crate::pattern::{Pattern, PatternTerm};
#[cfg(test)]
use crate::types::CollectionType;
use crate::types::TypeExpr;
use syn::Ident;

/// A-S5.4b: whether `def`'s declared equational theory is fully discharged by the generated
/// unconditional binder float at the invocation boundary — the replacement for the nested
/// receiver's `def.equations.is_empty()` gate. `true` iff the equations are empty, OR every
/// equation is a recognized binder-float congruence ([`is_binder_float_equation`]) AND the float
/// handler is generated for the language ([`language_has_float_handler`]).
pub fn equations_boundary_canonicalizable(def: &LanguageDef) -> bool {
    if def.equations.is_empty() {
        return true;
    }
    if !language_has_float_handler(def) {
        return false;
    }
    let Some(binder_label) = float_surface_binder_label(def) else {
        return false;
    };
    def.equations
        .iter()
        .all(|equation| is_binder_float_equation(def, equation, &binder_label))
}

/// A-S5.8: the equation-DERIVED satellite table of the in-Rho `^float` receiver family — one
/// `^float-hoist:{C}` satellite per recognized PREFIX float-across-constructor equation
/// (deduplicated by constructor, declaration order) and one `^float-merge:{op}` satellite per
/// recognized COLLECTION float equation (deduplicated by op, declaration order). Read off the
/// SAME per-equation recognizer walk [`equations_boundary_canonicalizable`] admits with
/// ([`classify_float_across_constructor_equation`]), so the emitted family can never drift
/// from the admission (never hardcoded to Ambient). A binder-commutation equation (`NewComm`)
/// derives NO satellite — the Q-NC user decision: in-Rho NewComm reordering is DELIBERATELY
/// omitted (the host's α-canonical-key minimization is not Match-expressible; redex exposure
/// is NewComm-invariant), so the float NF is unique UP TO the NewComm run permutation.
///
/// ★ A-S5.4c — TWO CONSUMERS, ONE DERIVATION. This is no longer only the in-Rho family's
/// table; it is the table of the float congruences a language actually DECLARES, and the
/// generated HOST binder-congruence normal form
/// (`macros/src/gen/runtime/binder_congruence.rs`) now emits one float arm per entry. Hence
/// `pub`. Consumer 2 is why: the host NF used to derive its arms from the primary category's
/// TERM FORMERS instead, floating the binder outward through every constructor of the category
/// whether or not an equation licensed it. For Ambient the two sets coincide; for Pi they did
/// not, and the surplus included `PRep` — a float out of replication (`!(νx.P) ⟶ νx.!P`),
/// UNSOUND in the π-calculus (fresh name per replica on the left, one name shared across all
/// replicas on the right) and not repairable by freshening, because it is not a
/// capture-avoidance failure. Deriving both consumers here is the structural fix.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FloatSatelliteTable {
    /// The recognized PREFIX floats: `(constructor, float_index, arity)` per equation — the
    /// `^float-hoist:{C}` satellite in-Rho, the prefix float arm on the host.
    pub hoist: Vec<(String, usize, usize)>,
    /// The recognized COLLECTION floats: the bag op per equation — the `^float-merge:{op}`
    /// satellite in-Rho, the bag-extrusion float arm on the host.
    pub merge_ops: Vec<String>,
}

/// Derive the [`FloatSatelliteTable`] of `def`'s declared float equations (A-S5.8). Total:
/// unrecognized/commutation equations contribute nothing. The in-Rho consumer gates on
/// [`equations_boundary_canonicalizable`] ∧ [`language_has_float_handler`] before emitting; the
/// host consumer (A-S5.4c) does NOT — a language whose equations are not WHOLLY float-discharged
/// (Pi, whose `RepUnfold` is no float) still gets a host NF, just one restricted to the floats it
/// does declare — which is exactly why this table is TOTAL rather than an `Option`.
pub fn float_satellite_table(def: &LanguageDef) -> FloatSatelliteTable {
    let mut table = FloatSatelliteTable::default();
    let Some(binder_label) = float_surface_binder_label(def) else {
        return table;
    };
    for equation in &def.equations {
        match classify_float_across_constructor_equation(def, equation, &binder_label) {
            Some(FloatAcrossClassification::Prefix { constructor, float_index, arity }) => {
                if !table
                    .hoist
                    .iter()
                    .any(|(label, _, _)| *label == constructor)
                {
                    table.hoist.push((constructor, float_index, arity));
                }
            },
            // `collapsible_match` is wrong HERE, and provably so: its suggestion moves the
            // dedup test into a match GUARD, and guarded arms do not count toward
            // exhaustivity — the rewrite stops compiling with E0004 (`Collection` no longer
            // covered). `cargo clippy --fix` applied it, failed to build, and reverted the
            // whole crate's fixes. The `if` stays in the arm BODY.
            #[allow(clippy::collapsible_match)]
            Some(FloatAcrossClassification::Collection { op }) => {
                if !table.merge_ops.contains(&op) {
                    table.merge_ops.push(op);
                }
            },
            None => {},
        }
    }
    table
}

/// A-S5.4b: whether the macros side generates the binder-congruence float handler for `def` — the
/// `rholang-codegen` restatement of `should_emit_binder_congruence`'s three conditions
/// (`macros/src/gen/runtime/binder_congruence.rs`):
///
///   1. the language declares structural-congruence equations,
///   2. it is host-less — no `RhoNativeJoin` guard obligation
///      ([`super::guard_obligations::collect_guard_obligations`]), and
///   3. it has a surface SINGLE-binder constructor over the primary category
///      ([`float_surface_binder_label`]).
///
/// A macros-side cross-crate agreement test pins this predicate ≡ `should_emit_binder_congruence`
/// over every bundled language definition, so the two crates cannot drift.
pub fn language_has_float_handler(def: &LanguageDef) -> bool {
    !def.equations.is_empty()
        && !super::guard_obligations::collect_guard_obligations(def)
            .iter()
            .any(|obligation| {
                matches!(
                    obligation.kind,
                    super::guard_obligations::RhoGuardObligationKind::RhoNativeJoin
                )
            })
        && float_surface_binder_label(def).is_some()
}

/// The label of the FIRST surface (user-declared) single-binder constructor over the primary
/// category, if any — the binder the generated float handler floats (`Ambient`'s `PNew`). Mirrors
/// the macros-side `surface_single_binder_label` over the AST: a `term_context`-declared rule is a
/// single binder iff it carries a `TermParam::Abstraction` (and no `MultiAbstraction` — the
/// message-passing multi-binders route to the host); an items-declared rule iff its first
/// `bindings` entry points a `GrammarItem::Binder` at a body `NonTerminal`. The body category must
/// be the primary category.
fn float_surface_binder_label(def: &LanguageDef) -> Option<String> {
    let primary = def.types.first()?.name.to_string();
    def.terms
        .iter()
        .filter(|rule| rule.category == primary)
        .find_map(|rule| {
            single_binder_body_category(rule)
                .filter(|body_category| *body_category == primary)
                .map(|_| rule.label.to_string())
        })
}

/// The body category of a surface SINGLE-binder rule, or `None` when the rule is not a single
/// binder (nullary/regular/collection/multi-binder). Mirrors the macros-side
/// `variant_kind_from_term_context` / `variant_kind_from_items` binder classification.
fn single_binder_body_category(rule: &GrammarRule) -> Option<String> {
    if let Some(term_context) = &rule.term_context {
        // A `MultiAbstraction` anywhere makes the rule a MULTI-binder (checked FIRST, exactly as
        // `variant_kind_from_term_context` does) — not a single binder.
        if term_context
            .iter()
            .any(|param| matches!(param, TermParam::MultiAbstraction { .. }))
        {
            return None;
        }
        return term_context.iter().find_map(|param| match param {
            TermParam::Abstraction { ty: TypeExpr::Arrow { codomain, .. }, .. } => {
                base_category_name(codomain)
            },
            _ => None,
        });
    }
    // Items route: the single-collection classification takes precedence over bindings (exactly as
    // `variant_kind_from_items` orders its checks), then the first bindings entry names the binder.
    let collection_items = rule
        .items
        .iter()
        .filter(|item| matches!(item, GrammarItem::Collection { .. }))
        .count();
    let non_terminal_items = rule
        .items
        .iter()
        .filter(|item| !matches!(item, GrammarItem::Terminal(_)))
        .count();
    if collection_items == 1 && non_terminal_items == 1 {
        return None;
    }
    let (binder_index, body_indices) = rule.bindings.first()?;
    if !matches!(rule.items.get(*binder_index), Some(GrammarItem::Binder { .. })) {
        return None;
    }
    match rule.items.get(*body_indices.first()?) {
        Some(GrammarItem::NonTerminal { ident, .. }) => Some(ident.to_string()),
        _ => None,
    }
}

/// The base category name of a type expression (`Base` directly; a `Collection`'s element,
/// recursively — the macros-side `extract_base_category` behavior). `None` for shapes a binder
/// codomain never takes (fail-closed).
fn base_category_name(ty: &TypeExpr) -> Option<String> {
    let mut ty = ty;
    loop {
        ty = match ty {
            TypeExpr::Base(ident) => return Some(ident.to_string()),
            TypeExpr::Collection { element, .. } => element,
            _ => return None,
        };
    }
}

/// A-S5.4b: whether `equation` is a recognized BINDER-FLOAT congruence over the surface binder
/// `binder_label` — binder-binder commutation or float-across-constructor (module doc above).
fn is_binder_float_equation(def: &LanguageDef, equation: &Equation, binder_label: &str) -> bool {
    is_binder_commutation_equation(equation, binder_label)
        || is_float_across_constructor_equation(def, equation, binder_label)
}

/// Task #94: how the BINDER-FLOAT lane disposes of one declared equation.
///
/// The Dovetail structural lowering cannot lower a binder-shaped equation — its LHS carries a
/// `Lambda` metapattern, which `pattern_to_dovetail` fails closed on. Until this classifier
/// existed, every such equation looked identical from outside: an entry in a dropped
/// `Vec<String>`. But the three cases are not the same thing at all, and conflating them is
/// exactly the defect Task #94 names:
///
///   * [`Self::FloatAcrossConstructor`] — the generated binder-congruence normal form
///     (`macros/src/gen/runtime/binder_congruence.rs`) DISCHARGES this equation by floating the
///     binder outward before reduction. It is delivered, just on another lane.
///   * [`Self::BinderCommutation`] — `NewComm`. In-Rho reordering is DELIBERATELY omitted (the
///     user's Q-NC decision; see [`float_satellite_table`]): the host's α-canonical-key
///     minimization is not Match-expressible, and redex exposure is NewComm-invariant, so the
///     float normal form is unique UP TO the NewComm run permutation. It is suppressed by
///     decision, not declined by omission.
///   * [`Self::NotFloatFamily`] — genuinely nothing here covers it.
///
/// Total and side-effect-free; reads the SAME recognizer walk `equations_boundary_canonicalizable`
/// admits with, so it can never claim coverage the float handler does not provide.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EquationFloatDisposition {
    /// Not a recognized member of the binder-float family (or the language has no generated
    /// float handler at all).
    NotFloatFamily,
    /// Family (ii): FLOAT-ACROSS-CONSTRUCTOR — discharged by the generated float handler.
    FloatAcrossConstructor,
    /// Family (i): BINDER-BINDER COMMUTATION (`NewComm`) — deliberately derives no satellite.
    BinderCommutation,
}

/// Classify one declared equation against the binder-float lane
/// ([`EquationFloatDisposition`]).
///
/// ★ FAILS CLOSED IN THREE PLACES, because a wrong answer here is a *false claim of coverage*
/// — the one failure mode a disposition record must never have:
///
///   1. a language with no generated float handler ([`language_has_float_handler`]) yields
///      `NotFloatFamily` for every equation;
///   2. so does a language with no surface single-binder constructor
///      ([`float_surface_binder_label`]);
///   3. ★ and a recognized float equation whose classification is NOT PRESENT in the emitted
///      [`float_satellite_table`] also yields `NotFloatFamily`.
///
/// Point 3 is not paranoia. `float_satellite_table` DEDUPLICATES hoists by constructor, so two
/// equations that float across the same constructor at DIFFERENT argument positions derive one
/// satellite between them, and the generated handler therefore floats only one of them. Merely
/// *recognizing* the second as float-shaped would attribute it to a lane that does not carry
/// it. Requiring the exact `(constructor, float_index, arity)` triple — or, for the collection
/// form, the exact bag operator — to appear in the emitted table ties the claim to the arm that
/// actually exists.
pub fn classify_equation_float_disposition(
    def: &LanguageDef,
    equation: &Equation,
) -> EquationFloatDisposition {
    if !language_has_float_handler(def) {
        return EquationFloatDisposition::NotFloatFamily;
    }
    let Some(binder_label) = float_surface_binder_label(def) else {
        return EquationFloatDisposition::NotFloatFamily;
    };
    if is_binder_commutation_equation(equation, &binder_label) {
        return EquationFloatDisposition::BinderCommutation;
    }
    let Some(classification) =
        classify_float_across_constructor_equation(def, equation, &binder_label)
    else {
        return EquationFloatDisposition::NotFloatFamily;
    };
    let table = float_satellite_table(def);
    let emitted = match &classification {
        FloatAcrossClassification::Prefix { constructor, float_index, arity } => {
            table.hoist.iter().any(|(label, index, count)| {
                label == constructor && index == float_index && count == arity
            })
        },
        FloatAcrossClassification::Collection { op } => table.merge_ops.contains(op),
    };
    if emitted {
        EquationFloatDisposition::FloatAcrossConstructor
    } else {
        EquationFloatDisposition::NotFloatFamily
    }
}

/// Family (i): BINDER-BINDER COMMUTATION — both sides the single surface binder nested over
/// itself, same body variable, swapped binders, premise-free (`NewComm` = C-G (Struct Res Res)).
fn is_binder_commutation_equation(equation: &Equation, binder_label: &str) -> bool {
    if !equation.premises.is_empty() {
        return false;
    }
    let (Some((left_outer, left_inner, left_body)), Some((right_outer, right_inner, right_body))) = (
        double_binder_shape(&equation.left, binder_label),
        double_binder_shape(&equation.right, binder_label),
    ) else {
        return false;
    };
    left_outer == right_inner && left_inner == right_outer && left_body == right_body
}

/// `B(^a. B(^b. Var(v)))` → `(a, b, v)` (names), else `None`.
fn double_binder_shape(pattern: &Pattern, binder_label: &str) -> Option<(String, String, String)> {
    let (outer, inner_scope) = binder_scope(pattern, binder_label)?;
    let (inner, body) = binder_scope(inner_scope, binder_label)?;
    match body {
        Pattern::Term(PatternTerm::Var(var)) => Some((outer, inner, var.to_string())),
        _ => None,
    }
}

/// `B(^x. body)` → `(x, body)` when `pattern` is the surface binder applied to a single-binder
/// lambda, else `None`.
fn binder_scope<'a>(pattern: &'a Pattern, binder_label: &str) -> Option<(String, &'a Pattern)> {
    let Pattern::Term(PatternTerm::Apply { constructor, args }) = pattern else {
        return None;
    };
    if constructor != binder_label {
        return None;
    }
    let [Pattern::Term(PatternTerm::Lambda { binder, body })] = args.as_slice() else {
        return None;
    };
    Some((binder.to_string(), body.as_ref()))
}

/// A-S5.8: the CLASSIFICATION a recognized float-across-constructor equation carries — the
/// satellite-derivation record ([`float_satellite_table`]) the `^float` family's emitters
/// consume, read off the SAME recognizer walk `equations_boundary_canonicalizable` admits
/// with (never a parallel hand-maintained table).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum FloatAcrossClassification {
    /// The PREFIX form (`InNew`-family + `AmbNew`): `C(a₁, …, B(^x. P), …) = B(^x. C(…))` —
    /// the `^float-hoist:{C}` satellite's derivation.
    Prefix {
        /// The floated-across constructor label `C`.
        constructor: String,
        /// The binder-scoped argument's position (the single plain primary-category field).
        float_index: usize,
        /// `C`'s total field count.
        arity: usize,
    },
    /// The COLLECTION form (`ScopeExtrusion`): `op{ …, B(^x. P), …, ...rest } = B(^x. op{…})`
    /// — the `^float-merge:{op}` satellite's derivation.
    Collection {
        /// The AC bag operator constructor `op`.
        op: String,
    },
}

/// Family (ii): FLOAT-ACROSS-CONSTRUCTOR, either orientation.
fn is_float_across_constructor_equation(
    def: &LanguageDef,
    equation: &Equation,
    binder_label: &str,
) -> bool {
    classify_float_across_constructor_equation(def, equation, binder_label).is_some()
}

/// A-S5.8: the classification core of [`is_float_across_constructor_equation`] — the SAME
/// recognizer walk, returning WHICH satellite the equation derives (either orientation).
fn classify_float_across_constructor_equation(
    def: &LanguageDef,
    equation: &Equation,
    binder_label: &str,
) -> Option<FloatAcrossClassification> {
    float_across_sides(def, &equation.left, &equation.right, binder_label, &equation.premises)
        .or_else(|| {
            float_across_sides(
                def,
                &equation.right,
                &equation.left,
                binder_label,
                &equation.premises,
            )
        })
}

/// One orientation of family (ii): `c_side = C(a₁, …, B(^x. P), …)` (prefix form) or
/// `C{ …, (B ^x. P), …, ...rest }` (collection form), `b_side = B(^x. C(a₁, …, P, …))` — same
/// constructor, same argument variables, the freshness premises exactly covering every
/// floated-past field, and `C` in the exact shape the generated float handler floats (AM-6e).
/// Returns the A-S5.8 satellite classification on recognition (`None` = not this family).
fn float_across_sides(
    def: &LanguageDef,
    c_side: &Pattern,
    b_side: &Pattern,
    binder_label: &str,
    premises: &[Premise],
) -> Option<FloatAcrossClassification> {
    let (binder_name, b_inner) = binder_scope(b_side, binder_label)?;
    let Pattern::Term(PatternTerm::Apply { constructor: c_ctor, args: c_args }) = c_side else {
        return None;
    };
    // The floated-across constructor must not be the binder itself (a binder-over-binder equation
    // is family (i)'s commutation, never a float-across).
    if c_ctor == binder_label {
        return None;
    }
    let Pattern::Term(PatternTerm::Apply {
        constructor: b_inner_ctor,
        args: b_inner_args,
    }) = b_inner
    else {
        return None;
    };
    if b_inner_ctor != c_ctor {
        return None;
    }
    match (c_args.as_slice(), b_inner_args.as_slice()) {
        // COLLECTION form (`ScopeExtrusion`): both sides one collection literal.
        (
            [Pattern::Collection { elements: c_elements, rest: c_rest, .. }],
            [Pattern::Collection { elements: b_elements, rest: b_rest, .. }],
        ) => float_across_collection(
            def,
            c_ctor,
            c_elements,
            c_rest.as_ref(),
            b_elements,
            b_rest.as_ref(),
            &binder_name,
            binder_label,
            premises,
        ),
        // PREFIX form (`InNew` family + `AmbNew`): plain argument lists.
        _ => float_across_prefix(
            def,
            c_ctor,
            c_args,
            b_inner_args,
            &binder_name,
            binder_label,
            premises,
        ),
    }
}

/// The PREFIX float form: exactly one `C` argument is `B(^x. Var(P))` (the same binder and body
/// variable reappearing on the `b_side` at the same position), every other argument a bare
/// variable equal on both sides; freshness declared on every other argument; `C` in the handler's
/// prefix shape with the binder at the single plain primary-category field (AM-6e). Returns the
/// `^float-hoist:{C}` satellite classification on recognition.
#[allow(clippy::too_many_arguments)]
fn float_across_prefix(
    def: &LanguageDef,
    c_ctor: &Ident,
    c_args: &[Pattern],
    b_args: &[Pattern],
    binder_name: &str,
    binder_label: &str,
    premises: &[Premise],
) -> Option<FloatAcrossClassification> {
    if c_args.len() != b_args.len() {
        return None;
    }
    let mut float_position: Option<(usize, String)> = None;
    let mut floated_past: Vec<String> = Vec::with_capacity(c_args.len().saturating_sub(1));
    for (index, (c_arg, b_arg)) in c_args.iter().zip(b_args).enumerate() {
        if let Some((scope_binder, scope_body)) = binder_scope(c_arg, binder_label) {
            // The floated position: same binder as the b_side scope, bare-variable body, and the
            // b_side carries exactly that body variable here.
            if scope_binder != binder_name {
                return None;
            }
            let Pattern::Term(PatternTerm::Var(body_var)) = scope_body else {
                return None;
            };
            let Pattern::Term(PatternTerm::Var(b_var)) = b_arg else {
                return None;
            };
            if b_var != body_var {
                return None;
            }
            if float_position
                .replace((index, body_var.to_string()))
                .is_some()
            {
                // Two binder-scoped arguments — not the single-float shape.
                return None;
            }
        } else {
            let (Pattern::Term(PatternTerm::Var(c_var)), Pattern::Term(PatternTerm::Var(b_var))) =
                (c_arg, b_arg)
            else {
                return None;
            };
            if c_var != b_var {
                return None;
            }
            floated_past.push(c_var.to_string());
        }
    }
    let (float_index, body_var) = float_position?;
    if !float_metavariables_distinct(binder_name, &body_var, &floated_past) {
        return None;
    }
    // AM-6e: `C` must be the handler's prefix shape — exactly one plain primary-category field —
    // and the equation's binder argument must sit AT that field.
    let shape_matches = match float_constructor_shape(def, c_ctor) {
        FloatConstructorShape::Prefix { primary_field_index, field_count } => {
            field_count == c_args.len() && primary_field_index == float_index
        },
        _ => return None,
    };
    (shape_matches
        && premises_are_exactly_float_freshness(premises, binder_name, &floated_past, None))
    .then(|| FloatAcrossClassification::Prefix {
        constructor: c_ctor.to_string(),
        float_index,
        arity: c_args.len(),
    })
}

/// The COLLECTION float form (`ScopeExtrusion`): exactly one collection element is `B(^x. Var(P))`
/// (reappearing as `Var(P)` at the same position on the `b_side`), every other element a bare
/// variable equal on both sides, the same `...rest` on both sides; freshness declared on every
/// other element and on the rest; `C` the primary-category collection constructor (AM-6e).
/// Returns the `^float-merge:{op}` satellite classification on recognition.
#[allow(clippy::too_many_arguments)]
fn float_across_collection(
    def: &LanguageDef,
    c_ctor: &Ident,
    c_elements: &[Pattern],
    c_rest: Option<&Ident>,
    b_elements: &[Pattern],
    b_rest: Option<&Ident>,
    binder_name: &str,
    binder_label: &str,
    premises: &[Premise],
) -> Option<FloatAcrossClassification> {
    if c_elements.len() != b_elements.len() {
        return None;
    }
    if c_rest != b_rest {
        return None;
    }
    let mut float_position: Option<(usize, String)> = None;
    let mut floated_past: Vec<String> = Vec::with_capacity(c_elements.len().saturating_sub(1));
    for (index, (c_element, b_element)) in c_elements.iter().zip(b_elements).enumerate() {
        if let Some((scope_binder, scope_body)) = binder_scope(c_element, binder_label) {
            if scope_binder != binder_name {
                return None;
            }
            let Pattern::Term(PatternTerm::Var(body_var)) = scope_body else {
                return None;
            };
            let Pattern::Term(PatternTerm::Var(b_var)) = b_element else {
                return None;
            };
            if b_var != body_var {
                return None;
            }
            if float_position
                .replace((index, body_var.to_string()))
                .is_some()
            {
                return None;
            }
        } else {
            let (Pattern::Term(PatternTerm::Var(c_var)), Pattern::Term(PatternTerm::Var(b_var))) =
                (c_element, b_element)
            else {
                return None;
            };
            if c_var != b_var {
                return None;
            }
            floated_past.push(c_var.to_string());
        }
    }
    let (_, body_var) = float_position?;
    if !float_metavariables_distinct(binder_name, &body_var, &floated_past) {
        return None;
    }
    // AM-6e: `C` must be the handler's bag-extrusion shape — the primary-category collection
    // constructor (the bag arm extrudes a binder MEMBER against the whole residual).
    (matches!(
        float_constructor_shape(def, c_ctor),
        FloatConstructorShape::CollectionOverPrimary
    ) && premises_are_exactly_float_freshness(
        premises,
        binder_name,
        &floated_past,
        c_rest.map(|rest| rest.to_string()).as_deref(),
    ))
    .then(|| FloatAcrossClassification::Collection { op: c_ctor.to_string() })
}

/// The float's metavariables must be pairwise distinct — the binder, the body variable, and every
/// floated-past field variable. A shared name (e.g. the body variable doubling as a sibling field)
/// would make the equation assert more than the handler's float performs — fail closed.
fn float_metavariables_distinct(
    binder_name: &str,
    body_var: &str,
    floated_past: &[String],
) -> bool {
    let mut seen: HashSet<&str> = HashSet::with_capacity(floated_past.len() + 2);
    seen.insert(binder_name);
    if !seen.insert(body_var) {
        return false;
    }
    floated_past.iter().all(|name| seen.insert(name.as_str()))
}

/// The freshness premises are EXACTLY the float's capture-avoidance conditions: every premise is
/// `binder # target` with `target` a floated-past field (`Var`) or the floated-past collection
/// rest (`...rest`), AND every floated-past field/rest is covered by such a premise. Any other
/// premise kind, a premise over a different variable, or a MISSING freshness condition rejects.
fn premises_are_exactly_float_freshness(
    premises: &[Premise],
    binder_name: &str,
    floated_past: &[String],
    floated_past_rest: Option<&str>,
) -> bool {
    for premise in premises {
        let Premise::Freshness(FreshnessCondition { var, term }) = premise else {
            return false;
        };
        if var != binder_name {
            return false;
        }
        let recognized = match term {
            FreshnessTarget::Var(target) => floated_past.iter().any(|name| target == name),
            FreshnessTarget::CollectionRest(target) => {
                floated_past_rest.is_some_and(|rest| target == rest)
            },
        };
        if !recognized {
            return false;
        }
    }
    let var_covered = |name: &String| {
        premises.iter().any(|premise| {
            matches!(
                premise,
                Premise::Freshness(FreshnessCondition { var, term: FreshnessTarget::Var(target) })
                    if var == binder_name && target == name
            )
        })
    };
    let rest_covered = |name: &str| {
        premises.iter().any(|premise| {
            matches!(
                premise,
                Premise::Freshness(FreshnessCondition {
                    var,
                    term: FreshnessTarget::CollectionRest(target),
                }) if var == binder_name && target == name
            )
        })
    };
    floated_past.iter().all(var_covered) && floated_past_rest.is_none_or(rest_covered)
}

/// How the generated float handler treats a constructor `C` (AM-6e) — derived from the SAME shape
/// logic `binder_congruence.rs`'s arms use, restated over the AST on this side of the crate
/// boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
enum FloatConstructorShape {
    /// The prefix arm's shape: a regular constructor with EXACTLY ONE plain (non-collection,
    /// non-optional) primary-category field, at `primary_field_index` of `field_count` fields.
    Prefix {
        primary_field_index: usize,
        field_count: usize,
    },
    /// The bag-extrusion arm's shape: the collection constructor over the primary category.
    CollectionOverPrimary,
    /// Every other shape falls to the handler's no-recursion catch-all — never floated.
    Other,
}

/// One restated constructor field — the (category, is_collection, is_optional) triple the
/// handler's prefix-arm filter reads (`f.category == proc_cat && !f.is_collection &&
/// !f.is_optional`), mirrored from the macros-side `FieldInfo` derivation.
#[derive(Debug, PartialEq, Eq)]
struct RestatedField {
    category: String,
    is_collection: bool,
    is_optional: bool,
}

/// Classify constructor `label` by the float handler's arm shapes ([`FloatConstructorShape`]).
fn float_constructor_shape(def: &LanguageDef, label: &Ident) -> FloatConstructorShape {
    let Some(primary) = def
        .types
        .first()
        .map(|lang_type| lang_type.name.to_string())
    else {
        return FloatConstructorShape::Other;
    };
    let Some(rule) = def.get_constructor(label) else {
        return FloatConstructorShape::Other;
    };
    // The handler emits arms for primary-category variants only.
    if rule.category != primary {
        return FloatConstructorShape::Other;
    }
    // A binder rule (either declaration route) is the binder arm, never a float-across target.
    if single_binder_body_category(rule).is_some() {
        return FloatConstructorShape::Other;
    }
    let fields: Vec<RestatedField> = if let Some(term_context) = &rule.term_context {
        // A MULTI-binder rule is not a float-across target either.
        if term_context
            .iter()
            .any(|param| matches!(param, TermParam::MultiAbstraction { .. }))
        {
            return FloatConstructorShape::Other;
        }
        let mut fields = Vec::with_capacity(term_context.len());
        restated_fields_from_params(term_context, false, &mut fields);
        fields
    } else {
        if !rule.bindings.is_empty() {
            return FloatConstructorShape::Other;
        }
        restated_fields_from_items(&rule.items)
    };
    // The collection classification (`variant_kind_from_term_context` / `variant_kind_from_items`):
    // exactly one field and it is a collection.
    if let [field] = fields.as_slice() {
        if field.is_collection {
            return if field.category == primary {
                FloatConstructorShape::CollectionOverPrimary
            } else {
                FloatConstructorShape::Other
            };
        }
    }
    // The prefix arm's filter: exactly one plain primary-category field.
    let primary_positions: Vec<usize> = fields
        .iter()
        .enumerate()
        .filter(|(_, field)| {
            field.category == primary && !field.is_collection && !field.is_optional
        })
        .map(|(index, _)| index)
        .collect();
    match primary_positions.as_slice() {
        [position] => FloatConstructorShape::Prefix {
            primary_field_index: *position,
            field_count: fields.len(),
        },
        _ => FloatConstructorShape::Other,
    }
}

/// Restate a `term_context` parameter list as constructor fields — the mirror of the macros-side
/// `field_infos_from_term_param` (abstractions contribute no field outside an `Optional` group;
/// `Optional` groups flatten with `is_optional` set; a guard slot is a non-primary marker field).
fn restated_fields_from_params(
    params: &[TermParam],
    in_optional: bool,
    out: &mut Vec<RestatedField>,
) {
    let mut work: Vec<_> = params
        .iter()
        .rev()
        .map(|param| (param, in_optional))
        .collect();
    while let Some((param, in_optional)) = work.pop() {
        match param {
            TermParam::Simple { ty, .. } => out.push(restated_field_from_type(ty, in_optional)),
            // The macros-side `field_info_for_guard_slot` marker category, byte-exact.
            TermParam::GuardBody { .. } => out.push(RestatedField {
                category: "Guard".to_string(),
                is_collection: false,
                is_optional: in_optional,
            }),
            TermParam::Optional { params: inner } => {
                work.extend(inner.iter().rev().map(|param| (param, true)));
            },
            TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. }
                if in_optional =>
            {
                let category = match ty {
                    TypeExpr::Arrow { codomain, .. } => {
                        base_category_name(codomain).unwrap_or_else(|| "__unknown".to_string())
                    },
                    _ => "__unknown".to_string(),
                };
                out.push(RestatedField {
                    category,
                    is_collection: false,
                    is_optional: true,
                });
            },
            TermParam::Abstraction { .. } | TermParam::MultiAbstraction { .. } => {},
        }
    }
}

#[cfg(test)]
#[path = "../../tests/support/binder_float_recursive_oracle.rs"]
mod metadata_recursive_oracle;

/// Restate a grammar-item list as constructor fields — the mirror of the macros-side
/// `variant_kind_from_items` field derivation (non-`Var` non-terminals and collections contribute
/// fields; terminals, `Var` non-terminals, and binder items do not).
fn restated_fields_from_items(items: &[GrammarItem]) -> Vec<RestatedField> {
    items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::NonTerminal { ident, kind } if *kind != NonTerminalKind::Var => {
                Some(RestatedField {
                    category: ident.to_string(),
                    is_collection: false,
                    is_optional: false,
                })
            },
            GrammarItem::Collection { element_type, .. } => Some(RestatedField {
                category: element_type.to_string(),
                is_collection: true,
                is_optional: false,
            }),
            _ => None,
        })
        .collect()
}

/// Restate one `TypeExpr` as a constructor field — the mirror of the macros-side
/// `field_info_from_type_expr` (base category; collections and maps as collection fields).
fn restated_field_from_type(ty: &TypeExpr, is_optional: bool) -> RestatedField {
    match ty {
        TypeExpr::Base(ident) => RestatedField {
            category: ident.to_string(),
            is_collection: false,
            is_optional,
        },
        TypeExpr::Collection { element, .. } => RestatedField {
            category: base_category_name(element).unwrap_or_else(|| "__unknown".to_string()),
            is_collection: true,
            is_optional,
        },
        TypeExpr::Map { value, .. } => RestatedField {
            category: base_category_name(value).unwrap_or_else(|| "__unknown".to_string()),
            is_collection: true,
            is_optional,
        },
        _ => RestatedField {
            category: "__unknown".to_string(),
            is_collection: false,
            is_optional,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn ident(name: &str) -> Ident {
        syn::parse_str(name).expect("test identifier must parse")
    }

    /// The CORRECTED Ambient equation set (A-S5.4b premise fix: capture-avoidance `x # N` on the
    /// capability trio + `AmbNew`; `ScopeExtrusion` freshness on the floated-past `...rest`;
    /// `NewComm` premise-free) over the production constructor inventory — the exact declarations
    /// `equations_boundary_canonicalizable` must admit.
    const MINI_CORRECTED_AMBIENT_FRAGMENT: &str = r#"
        name: RhoNetLowerMiniCorrectedAmbient,
        options {
            emit_simulator: false,
            emit_blockly: false,
        },
        types {
            Proc
            Name
        },
        terms {
            PZero . |- "0" : Proc ;
            PIn . n:Name, p:Proc |- "in" "(" n "," p ")" : Proc ;
            POut . n:Name, p:Proc |- "out" "(" n "," p ")" : Proc ;
            POpen . n:Name, p:Proc |- "open" "(" n "," p ")" : Proc ;
            PAmb . n:Name, p:Proc |- n "[" p "]" : Proc ;
            PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc ;
            PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc ;
        },
        equations {
            NewComm . |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P));
            ScopeExtrusion . | x # ...rest |- (PPar {(PNew ^x.P), ...rest}) = (PNew ^x.(PPar {P, ...rest}));
            InNew . | x # N |- (PIn N (PNew ^x.P)) = (PNew ^x.(PIn N P));
            OutNew . | x # N |- (POut N (PNew ^x.P)) = (PNew ^x.(POut N P));
            OpenNew . | x # N |- (POpen N (PNew ^x.P)) = (PNew ^x.(POpen N P));
            AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));
        },
        rewrites {}
    "#;

    fn corrected_ambient_def() -> LanguageDef {
        syn::parse_str::<LanguageDef>(MINI_CORRECTED_AMBIENT_FRAGMENT)
            .expect("the corrected mini-Ambient fragment must parse")
    }

    proptest! {
        #[test]
        fn satellite_order_is_first_declared_occurrence(
            order in proptest::collection::vec(0usize..6, 0..32),
        ) {
            let mut def = corrected_ambient_def();
            let equations = def.equations.clone();
            def.equations = order.iter().map(|index| equations[*index].clone()).collect();
            let table = float_satellite_table(&def);
            let names = ["PIn", "POut", "POpen", "PAmb"];
            let expected: Vec<_> = order.iter().enumerate()
                .filter(|(position, index)| **index >= 2 && !order[..*position].contains(index))
                .map(|(_, index)| (names[*index - 2].to_owned(), 1, 2))
                .collect();
            prop_assert_eq!(table.hoist, expected);
            prop_assert_eq!(table.merge_ops, if order.contains(&1) {
                vec!["PPar".to_owned()]
            } else {
                Vec::new()
            });
            prop_assert!(equations_boundary_canonicalizable(&def));
        }
    }

    #[test]
    fn no_surface_binder_has_no_satellites_or_claimed_dispositions() {
        let mut def = corrected_ambient_def();
        def.terms.retain(|rule| rule.label != "PNew");
        assert_eq!(float_satellite_table(&def), FloatSatelliteTable::default());
        assert!(!language_has_float_handler(&def));
        assert!(!equations_boundary_canonicalizable(&def));
        for equation in &def.equations {
            assert_eq!(
                classify_equation_float_disposition(&def, equation),
                EquationFloatDisposition::NotFloatFamily
            );
        }
    }

    /// Every one of the six CORRECTED Ambient equations is individually recognized as a
    /// binder-float congruence, the handler leg holds, and the whole language is boundary-
    /// canonicalizable — the exact A-S5.4b admission.
    #[test]
    fn equations_gate_accepts_all_six_corrected_ambient_equations() {
        let def = corrected_ambient_def();
        assert!(
            language_has_float_handler(&def),
            "the mini corrected Ambient has equations + no RhoNativeJoin + the single PNew binder"
        );
        assert_eq!(
            float_surface_binder_label(&def).as_deref(),
            Some("PNew"),
            "PNew is the surface single binder"
        );
        for equation in &def.equations {
            assert!(
                is_binder_float_equation(&def, equation, "PNew"),
                "corrected equation {} must be recognized as a binder-float congruence",
                equation.name
            );
        }
        assert!(
            equations_boundary_canonicalizable(&def),
            "the corrected Ambient equation set is fully float-discharged at the boundary"
        );
    }

    /// A NON-binder equation (no float, no commutation — here a bare constructor identity) rejects
    /// the whole language: the gate stays fail-closed.
    #[test]
    fn equations_gate_rejects_a_non_binder_equation() {
        let with_non_binder = MINI_CORRECTED_AMBIENT_FRAGMENT.replace(
            "NewComm . |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P));",
            "NewComm . |- (PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P));\n            \
             Swap . |- (PIn N P) = (POut N P);",
        );
        let def = syn::parse_str::<LanguageDef>(&with_non_binder).expect("fragment must parse");
        let swap = def
            .equations
            .iter()
            .find(|equation| equation.name == "Swap")
            .expect("the Swap equation is present");
        assert!(
            !is_binder_float_equation(&def, swap, "PNew"),
            "a non-binder equation is never a float congruence"
        );
        assert!(
            !equations_boundary_canonicalizable(&def),
            "one unrecognized equation keeps the language gated"
        );
    }

    /// A float with a MISSING freshness premise (the pre-A-S5.4b vacuous-binder `x # P` — or no
    /// premise at all — instead of the capture-avoidance `x # N`) is rejected: the recognizer
    /// checks freshness on EVERY floated-past field, against the CORRECTED declarations only.
    #[test]
    fn equations_gate_rejects_a_float_with_a_missing_freshness_premise() {
        for wrong in [
            // No premise at all.
            "InNew . |- (PIn N (PNew ^x.P)) = (PNew ^x.(PIn N P));",
            // The pre-A-S5.4b vacuous-binder premise (freshness on the BODY, not the passed field).
            "InNew . | x # P |- (PIn N (PNew ^x.P)) = (PNew ^x.(PIn N P));",
        ] {
            let variant = MINI_CORRECTED_AMBIENT_FRAGMENT
                .replace("InNew . | x # N |- (PIn N (PNew ^x.P)) = (PNew ^x.(PIn N P));", wrong);
            let def = syn::parse_str::<LanguageDef>(&variant).expect("fragment must parse");
            let in_new = def
                .equations
                .iter()
                .find(|equation| equation.name == "InNew")
                .expect("InNew present");
            assert!(
                !is_binder_float_equation(&def, in_new, "PNew"),
                "a float missing the capture-avoidance freshness on the passed field must be \
                 rejected (declared: {wrong})"
            );
            assert!(!equations_boundary_canonicalizable(&def));
        }
    }

    /// A TWO-binder language whose extra equation floats the SECOND binder is rejected: the float
    /// handler floats only THE surface binder (the first single binder over the primary category),
    /// so an equation over any other binder is not discharged at the boundary.
    #[test]
    fn equations_gate_rejects_a_float_over_a_different_binder_in_a_two_binder_language() {
        let two_binder = MINI_CORRECTED_AMBIENT_FRAGMENT
            .replace(
                "PPar . ps:HashBag(Proc) |- \"{\" ps.*sep(\"|\") \"}\" : Proc ;",
                "PPar . ps:HashBag(Proc) |- \"{\" ps.*sep(\"|\") \"}\" : Proc ;\n            \
                 PBind . ^x.p:[Name -> Proc] |- \"bind\" \"(\" x \",\" p \")\" : Proc ;",
            )
            .replace(
                "AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));",
                "AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));\n            \
                 BindNew . | x # N |- (PIn N (PBind ^x.P)) = (PBind ^x.(PIn N P));",
            );
        let def = syn::parse_str::<LanguageDef>(&two_binder).expect("fragment must parse");
        // The surface binder is STILL the first single binder (PNew) — the handler's target.
        assert_eq!(float_surface_binder_label(&def).as_deref(), Some("PNew"));
        let bind_new = def
            .equations
            .iter()
            .find(|equation| equation.name == "BindNew")
            .expect("BindNew present");
        assert!(
            !is_binder_float_equation(&def, bind_new, "PNew"),
            "a float over the NON-surface binder is not discharged by the handler"
        );
        assert!(
            !equations_boundary_canonicalizable(&def),
            "the two-binder language stays gated on its second-binder float"
        );
    }

    /// AM-6e: a float-across-constructor whose `C` LACKS the handler's prefix shape (here TWO
    /// plain primary-category fields — the handler's prefix arm floats only the exactly-one-field
    /// shape and everything else falls to its no-recursion catch-all) is rejected, even with a
    /// complete freshness premise set.
    #[test]
    fn equations_gate_rejects_a_float_across_a_non_prefix_shape_constructor() {
        let with_both = MINI_CORRECTED_AMBIENT_FRAGMENT
            .replace(
                "PZero . |- \"0\" : Proc ;",
                "PZero . |- \"0\" : Proc ;\n            \
                 PBoth . a:Proc, b:Proc |- \"both\" \"(\" a \",\" b \")\" : Proc ;",
            )
            .replace(
                "AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));",
                "AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));\n            \
                 BothNew . | x # Q |- (PBoth (PNew ^x.P) Q) = (PNew ^x.(PBoth P Q));",
            );
        let def = syn::parse_str::<LanguageDef>(&with_both).expect("fragment must parse");
        // PBoth has TWO plain primary-category fields — the handler's catch-all, never floated.
        assert_eq!(
            float_constructor_shape(&def, &ident("PBoth")),
            FloatConstructorShape::Other,
            "PBoth is not the handler's exactly-one-primary-field prefix shape"
        );
        let both_new = def
            .equations
            .iter()
            .find(|equation| equation.name == "BothNew")
            .expect("BothNew present");
        assert!(
            !is_binder_float_equation(&def, both_new, "PNew"),
            "AM-6e: a float across a catch-all-shaped constructor must NOT pass the recognizer"
        );
        assert!(!equations_boundary_canonicalizable(&def));
    }

    /// The handler-shape classifier agrees with the handler's arms on the production inventory:
    /// the capability prefixes + the ambient are prefix-shaped with the binder at the single
    /// primary field, the bag is the collection shape, and the binder itself is neither.
    #[test]
    fn float_constructor_shape_classifies_the_ambient_inventory() {
        let def = corrected_ambient_def();
        for label in ["PIn", "POut", "POpen", "PAmb"] {
            assert_eq!(
                float_constructor_shape(&def, &ident(label)),
                FloatConstructorShape::Prefix { primary_field_index: 1, field_count: 2 },
                "{label} is the handler's prefix shape (Name field 0, Proc field 1)"
            );
        }
        assert_eq!(
            float_constructor_shape(&def, &ident("PPar")),
            FloatConstructorShape::CollectionOverPrimary,
            "PPar is the handler's bag-extrusion shape"
        );
        assert_eq!(
            float_constructor_shape(&def, &ident("PNew")),
            FloatConstructorShape::Other,
            "the binder itself is the binder arm, never a float-across target"
        );
        assert_eq!(
            float_constructor_shape(&def, &ident("PZero")),
            FloatConstructorShape::Other,
            "a nullary constructor has no float arm"
        );
    }
}
