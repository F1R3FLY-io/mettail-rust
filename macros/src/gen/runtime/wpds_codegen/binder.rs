//! Phase 5: Binder + multi-step rule codegen.
//!
//! Detects judgement-style rules with one or more of: literal terminals,
//! parameter sub-parses, single-binder ident slot, multi-binder list,
//! body parse, guard slot. Emits a multi-step state machine that walks
//! the rule's `syntax_pattern`, capturing args along the way, firing the
//! rule's action when the marker pops.
//!
//! Supported rule shapes:
//! - **Single-binder** (Phase 5a, e.g. Lambda's `Lam`): `^x.body:[T -> T]`
//!   with syntax `"trigger" x "." body`.
//! - **Multi-Param non-binder** (Phase 5b, e.g. Calculator's `Fraction`):
//!   `a:T, b:T |- "trigger" "(" a "," b ")"`. The rule has multiple
//!   `Simple` params and no binder.
//! - **Multi-binder list** (Phase 5b, e.g. RhoCalc's `PNew`):
//!   `^[xs].p:[T* -> T]` with syntax containing a `Sep` operator over
//!   the binder list.
//! - **Mixed** (Phase 5b, e.g. PInputs): combines `Simple` params,
//!   collection-as-`Op(Sep)`, and binder via `MultiAbstraction`.
//! - **Guard slot** (Phase 6, e.g. PGuardedInput): includes a
//!   `?guard:Guard` parameter parsed via `parse_predicate_from_tokens`.

use mettail_ast::grammar::{GrammarRule, PatternOp, SyntaxExpr, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::{CollectionType, TypeExpr};
use mettail_prattail::binding_power::compute_prefix_bp;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashMap;
use syn::Ident;

use super::builtin_metadata::classify_unary_prefix_shape;

/// Stage 3.27d (G-PREFIX-BP, 2026-04-30): map from `(category_src_idx,
/// rule_idx)` to the unary-prefix binding power, for rules whose shape
/// matches `Label . a:T |- "literal" a : T;` (single-Simple-param,
/// `[Literal, Param]` pattern, T == result_cat). Used by ParamParse
/// arms in `emit_binder_rule_body` and `emit_optional_group_body` to
/// install `cur_bp = prefix_bp` for the operand sub-parse, preventing
/// lower-precedence trailing infix from "stealing" the prefix's child.
///
/// Computed via `compute_prefix_bp()` (single source of truth at
/// `prattail::binding_power::compute_prefix_bp`), so Display + lint +
/// WPDS parser all agree on `prefix_bp = max_infix_bp + 2`.
///
/// Empty entry => non-unary-prefix rule, ParamParse uses `cur_bp: 0`.
pub(crate) fn build_prefix_bp_map(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> HashMap<(u16, u16), u8> {
    let bp_table = super::infix::build_bp_table(language);
    let mut map: HashMap<(u16, u16), u8> = HashMap::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            if classify_unary_prefix_shape(rule).is_some() {
                let bp = compute_prefix_bp(
                    &rule.category.to_string(),
                    rule.prefix_bp,
                    &bp_table,
                );
                map.insert((cat_i as u16, rule_i as u16), bp);
            }
        }
    }
    map
}

/// Classification of a multi-step rule.
#[derive(Debug, Clone)]
pub struct BinderShape {
    /// Constructor label (e.g., `"Lam"`, `"Fraction"`, `"PNew"`).
    #[allow(dead_code)]
    pub label: String,
    /// Result category name (e.g., `"Term"`, `"BigRat"`, `"Proc"`).
    #[allow(dead_code)]
    pub result_cat: String,
    /// Per-position dispatch entries (excluding position 0 which is the
    /// trigger consumed at PrefixDispatch open arm).
    pub positions: Vec<BinderPosition>,
    /// Whether the rule uses a multi-binder list (^[xs]).
    pub is_multi: bool,
    /// Whether the rule has any binder slot at all (for action body shape).
    pub has_binder: bool,
    /// Action arity (number of args the action consumes).
    pub action_arity: u8,
    /// Action body: per-arg, what kind of arg it is (Ident binder name,
    /// Term sub-parse, Predicate, BinderListNames). Used to construct the
    /// Cat::Label(...) expression.
    pub action_args: Vec<ActionArgKind>,
    /// Body category (for single-binder rules — None for non-binder).
    #[allow(dead_code)]
    pub body_cat: Option<String>,
    /// Param categories in declaration order (for non-binder Simple params).
    #[allow(dead_code)]
    pub param_cats: Vec<String>,
}

/// A single position in a multi-step rule's syntax pattern.
#[derive(Debug, Clone)]
pub enum BinderPosition {
    /// `Literal("text")` — consume + advance position.
    Literal(String),
    /// `Param(binder_name)` — capture single Ident, start_binder_scope,
    /// advance position.
    BinderIdent,
    /// `Op(Sep { collection: xs, separator })` — for ^[xs] multi-binder
    /// list. Engine enters BinderListLoop sub-state, captures Idents
    /// separated by `separator`, until close delim of position N+1 (the
    /// next Literal in the syntax pattern).
    ///
    /// B8 / Class 3 ZIP-MAP-SEP (2026-05-08): extended fields support the
    /// chained `Sep{source: Some(Map{source: Zip})}` pattern (e.g.
    /// rhocalc PInputs `*zip(ns,xs).*map(|n,x| n "?" x).*sep(",")`).
    /// `inner_positions` is the per-iteration inner walk; for PNew-style
    /// rules it's `[BinderIdent]`. `binder_param_idx` is the index into
    /// `inner_positions` of the binder slot (the BinderIdent for PNew,
    /// or the binder slot inside the map body for Class 3).
    /// `collection_param_cat` is `Some(elem_cat)` for Class 3 (the
    /// synthesized Names accumulator's element category) and None for
    /// PNew-style rules (no synthesized accumulator).
    BinderListLoop {
        separator: String,
        close: String,
        /// Per-iteration inner walk. PNew → `[BinderIdent]`. Class 3 →
        /// the body of the Map closure (e.g. `[ParamParse{Name,
        /// collection:Some(...)}, Literal("?"), BinderIdent]`).
        inner_positions: Vec<BinderPosition>,
        /// Action-arg layout for the inner walk; mirrors inner_positions.
        inner_action_args: Vec<ActionArgKind>,
        /// Index into inner_positions of the binder ident slot. PNew → 0.
        binder_param_idx: u8,
        /// For Class 3 rules: the element category of the synthesized
        /// names accumulator. None for PNew-style rules.
        collection_param_cat: Option<String>,
    },
    /// `Param(name)` — sub-parse the param's category. After the parse
    /// returns, the marker advances to the next position. When the marker
    /// reaches `positions.len() + 1`, the rule's RuleAt symbol pops in
    /// Unwinding and the action fires (no separate `is_final` flag needed
    /// — it's encoded by position arithmetic).
    ///
    /// B9 / Class 2 (2026-05-08): when the param is `Sep`-driven over a
    /// SimpleCollection (e.g. `Vec(Proc).*sep("|") ")"`), `collection`
    /// is `Some(...)`. The dispatch arm pushes a CollectionMarker onto
    /// the GSS, transitioning to PrefixDispatch where the existing
    /// CollectionLoop apparatus parses elements separated by `separator`
    /// until `close`. On close, the marker pops — but the FireAction is
    /// suppressed (binder-internal collection); the binder rule's
    /// terminal action drains the CollectionId via `CollectionDrain`.
    ParamParse {
        cat: String,
        collection: Option<CollectionSepInfo>,
    },
    /// `Param(guard)` for `?guard:Guard` — parse predicate inline via
    /// `parse_predicate_from_tokens`. Advance position.
    GuardSlot,
    /// Opt-Group (2026-04-29): `Op(Opt { inner })` — recursive
    /// optional-group lowering. The engine transitions into
    /// `WpdsState::OptionalGroup { sub_pos: 0 }`; on entry it peeks
    /// the FIRST-set of `inner_positions[0]` to decide whether to take
    /// the group (push inner args + advance into group) or skip (push
    /// `ActionArg::Optional(None)` + advance past group). The
    /// `first_token_set` is a list of literal-text predicates that
    /// trigger entry into the group (computed at codegen from the
    /// inner positions' types).
    OptionalGroup {
        positions: Vec<BinderPosition>,
        action_args: Vec<ActionArgKind>,
        /// Sequence index of THIS group within its parent rule's
        /// positions list (used to disambiguate FIRST-set tables when
        /// a rule has multiple groups).
        group_idx: u8,
        /// Tokens that, when peeked at group entry, indicate the group
        /// should be taken. Strings are the literal text from the first
        /// inner Literal; if the first inner is a ParamParse the
        /// FIRST-set is computed from the param's category.
        first_token_set: Vec<String>,
    },
}

/// B9 / Class 2 (2026-05-08): separator + close + container-kind info
/// for a `ParamParse` slot whose source is a `Sep`-driven collection.
/// Mirrors `CollectionShape` (collection.rs) but lives on the binder
/// position because the slot is INSIDE a multi-position binder rule
/// rather than the rule itself BEING a collection rule.
#[derive(Debug, Clone)]
pub struct CollectionSepInfo {
    pub separator: String,
    pub close: String,
    pub coll_kind: CollectionType,
    pub elem_cat: String,
}

/// What kind of arg the action body extracts at each position (in push order).
#[derive(Debug, Clone)]
pub enum ActionArgKind {
    /// `ActionArg::Ident { name }` — single binder name.
    BinderName,
    /// `ActionArg::Term { value, .. }` of a specific category.
    Term(String),
    /// `ActionArg::Predicate` — parsed predicate.
    Predicate,
    /// Multi-binder list: a `BinderHandle` pushed by the binder-list-loop
    /// finalize step. Action body wraps as `Scope<Vec<Binder>, ...>`.
    BinderList,
    /// Opt-Group: a captured optional group's inner action args.
    /// `inner` mirrors the inner positions' action_args layout. At
    /// runtime the action body extracts `ActionArg::Optional(Option<
    /// Vec<ActionArg>>)` and produces `Some(...)` / `None` for each
    /// `Option<T>` field of the AST variant in inner-args order.
    Optional(Vec<ActionArgKind>),
    /// B9 / Class 2 (2026-05-08): a CollectionId arg pushed by the
    /// CollectionMarker push helper. The action body calls
    /// `b.drain_collection(id)` to materialize the elements into the
    /// container type per `coll_kind`. Mirrors the body of
    /// `emit_collection_action_entry::action_fn` but for a SLOT inside
    /// a multi-position binder rule.
    CollectionDrain {
        elem_cat: String,
        coll_kind: CollectionType,
    },
}

/// Try to classify a `GrammarRule` as a multi-step rule (binder, multi-Param,
/// or guard-bearing).
pub(crate) fn classify_binder(rule: &GrammarRule) -> Option<BinderShape> {
    let tc = rule.term_context.as_ref()?;
    let sp = rule.syntax_pattern.as_ref()?;
    if sp.is_empty() {
        return None;
    }
    // Position 0 must be a Literal trigger (otherwise it's an infix/prefix
    // Pratt rule handled by Phase 3).
    if !matches!(&sp[0], SyntaxExpr::Literal(_)) {
        return None;
    }

    // B9 / Class 2 (2026-05-08): Class-5 collection-rule structural exclusion.
    // A rule with exactly one Simple param of Collection type AND a syntax
    // pattern matching the Class-5 shape — `[Literal(open), Op(Sep), Literal(close)]`
    // (3 elements) or `[Literal(open_kw), Literal("("), Op(Sep), Literal(close)]`
    // (4 elements, synthesized by `synthetic.rs` for default-form open delims
    // like `"list("`) — is a Class-5 collection rule classified by
    // `classify_collection`. Reject here so classify_binder does NOT
    // double-classify these rules. Without this exclusion, my B9 changes
    // (which now accept Collection-typed Simple params via
    // ParamKind::SimpleCollection) would emit binder prefix arms +
    // action entries that conflict with the existing Class-5 emission.
    if tc.len() == 1 {
        if let TermParam::Simple {
            ty: TypeExpr::Collection { .. },
            ..
        } = &tc[0]
        {
            let class5_shape_3 = sp.len() == 3
                && matches!(&sp[0], SyntaxExpr::Literal(_))
                && matches!(
                    &sp[1],
                    SyntaxExpr::Op(PatternOp::Sep { source: None, .. })
                )
                && matches!(&sp[2], SyntaxExpr::Literal(_));
            let class5_shape_4 = sp.len() == 4
                && matches!(&sp[0], SyntaxExpr::Literal(_))
                && matches!(&sp[1], SyntaxExpr::Literal(s) if s == "(")
                && matches!(
                    &sp[2],
                    SyntaxExpr::Op(PatternOp::Sep { source: None, .. })
                )
                && matches!(&sp[3], SyntaxExpr::Literal(_));
            if class5_shape_3 || class5_shape_4 {
                return None;
            }
        }
    }

    // Build a map: param name → (kind, type_info).
    enum ParamKind {
        Simple { cat: String },
        Binder,
        BinderList,
        Body { cat: String },
        Guard,
        /// B9 / Class 2 (2026-05-08): a `Simple` param whose type is
        /// `Collection { coll_type: Vec/HashBag/HashSet, element: Base(elem) }`.
        /// Distinct from the collection-rule case (handled by
        /// `classify_collection`) because Class-2 rules have OTHER
        /// non-collection params (e.g. a tag param + a collection param);
        /// `classify_collection` requires `tc.len() == 1`.
        SimpleCollection {
            elem_cat: String,
            coll_kind: CollectionType,
        },
    }
    let mut param_map: std::collections::HashMap<String, ParamKind> =
        std::collections::HashMap::new();
    let mut is_multi = false;
    let mut has_binder = false;
    let mut body_cat: Option<String> = None;
    let mut param_cats: Vec<String> = Vec::new();

    // Opt-Group: track which param names are inside an `#opt(...)` group
    // so action emission knows to wrap them as `Option<T>`. Inner params
    // are registered in param_map identically to top-level params; the
    // `optional_params` set lets later code distinguish the two.
    let mut optional_params: std::collections::HashSet<String> =
        std::collections::HashSet::new();

    fn walk_params(
        params: &[TermParam],
        in_optional: bool,
        param_map: &mut std::collections::HashMap<String, ParamKind>,
        optional_params: &mut std::collections::HashSet<String>,
        is_multi: &mut bool,
        has_binder: &mut bool,
        body_cat: &mut Option<String>,
        param_cats: &mut Vec<String>,
    ) -> Option<()> {
        for p in params {
            if in_optional {
                match p {
                    TermParam::Simple { name, .. }
                    | TermParam::Abstraction { binder: name, .. }
                    | TermParam::MultiAbstraction { binder: name, .. }
                    | TermParam::GuardBody { name } => {
                        optional_params.insert(name.to_string());
                    },
                    TermParam::Optional { .. } => {}
                }
            }
            match p {
                TermParam::Simple { name, ty } => match ty {
                    TypeExpr::Base(ident) => {
                        let cat = ident.to_string();
                        param_cats.push(cat.clone());
                        param_map.insert(name.to_string(), ParamKind::Simple { cat });
                    }
                    // B9 / Class 2 (2026-05-08): SimpleCollection. The
                    // pilot supports Vec / HashBag / HashSet over a Base
                    // element type; HashMap and nested collections are
                    // out of pilot scope.
                    TypeExpr::Collection { coll_type, element } => match (coll_type, element.as_ref()) {
                        (CollectionType::Vec, TypeExpr::Base(elem))
                        | (CollectionType::HashBag, TypeExpr::Base(elem))
                        | (CollectionType::HashSet, TypeExpr::Base(elem)) => {
                            let elem_cat = elem.to_string();
                            param_cats.push(elem_cat.clone());
                            param_map.insert(
                                name.to_string(),
                                ParamKind::SimpleCollection {
                                    elem_cat,
                                    coll_kind: coll_type.clone(),
                                },
                            );
                        }
                        _ => return None,
                    },
                    _ => return None,
                },
                TermParam::Abstraction { binder, body, ty } => {
                    let bcat = arrow_codomain_name(ty)?;
                    *body_cat = Some(bcat.clone());
                    *has_binder = true;
                    param_map.insert(binder.to_string(), ParamKind::Binder);
                    param_map
                        .insert(body.to_string(), ParamKind::Body { cat: bcat });
                    if in_optional {
                        optional_params.insert(body.to_string());
                    }
                }
                TermParam::MultiAbstraction { binder, body, ty } => {
                    let bcat = arrow_codomain_name(ty)?;
                    *body_cat = Some(bcat.clone());
                    *has_binder = true;
                    *is_multi = true;
                    param_map.insert(binder.to_string(), ParamKind::BinderList);
                    param_map
                        .insert(body.to_string(), ParamKind::Body { cat: bcat });
                    if in_optional {
                        optional_params.insert(body.to_string());
                    }
                }
                TermParam::GuardBody { name } => {
                    param_map.insert(name.to_string(), ParamKind::Guard);
                }
                TermParam::Optional { params: inner } => {
                    walk_params(
                        inner,
                        true,
                        param_map,
                        optional_params,
                        is_multi,
                        has_binder,
                        body_cat,
                        param_cats,
                    )?;
                }
            }
        }
        Some(())
    }

    walk_params(
        tc,
        false,
        &mut param_map,
        &mut optional_params,
        &mut is_multi,
        &mut has_binder,
        &mut body_cat,
        &mut param_cats,
    )?;

    // Walk syntax_pattern (skipping index 0 = trigger) building positions
    // + action_args in encountered-order (push order).
    //
    // L12 follow-up B2.f (2026-05-07): when a `BinderList` (Sep over a
    // BinderList kind) is pushed as `BinderPosition::BinderListLoop`,
    // the syntax_pattern's NEXT element is the loop's close delimiter
    // (consumed by the BinderListLoop's close-branch dispatch). It must
    // NOT be re-pushed as a separate `BinderPosition::Literal` — doing so
    // produces a position-numbering bug where the close token is consumed
    // twice (once by BinderListLoop's close branch, once by the spurious
    // pos+1 Literal arm), causing rhocalc::PNew parses to fail with
    // "expected '<close>' but found '<next>'" at every dispatch.
    // `skip_next` tracks this and skips the close Literal at the next
    // iteration.
    let mut positions = Vec::new();
    let mut action_args = Vec::new();
    let mut skip_next: bool = false;
    for (i, item) in sp.iter().enumerate().skip(1) {
        if skip_next {
            skip_next = false;
            continue;
        }
        match item {
            SyntaxExpr::Literal(text) => {
                positions.push(BinderPosition::Literal(text.clone()));
            }
            SyntaxExpr::Param(name) => {
                let n = name.to_string();
                let kind = param_map.get(&n)?;
                match kind {
                    ParamKind::Binder => {
                        positions.push(BinderPosition::BinderIdent);
                        action_args.push(ActionArgKind::BinderName);
                    }
                    ParamKind::Body { cat } | ParamKind::Simple { cat } => {
                        positions.push(BinderPosition::ParamParse {
                            cat: cat.clone(),
                            collection: None,
                        });
                        action_args.push(ActionArgKind::Term(cat.clone()));
                    }
                    ParamKind::Guard => {
                        positions.push(BinderPosition::GuardSlot);
                        action_args.push(ActionArgKind::Predicate);
                    }
                    ParamKind::BinderList => {
                        // BinderList shouldn't appear as a bare Param —
                        // it's expressed as Op(Sep) below. Defensive.
                        return None;
                    }
                    ParamKind::SimpleCollection { .. } => {
                        // SimpleCollection appears only as Op(Sep) below.
                        // Bare Param reference is invalid — the collection
                        // requires a separator + close delim.
                        return None;
                    }
                }
            }
            SyntaxExpr::Op(PatternOp::Sep {
                collection,
                separator,
                source: None,
            }) => {
                let n = collection.to_string();
                let kind = param_map.get(&n)?;
                match kind {
                    ParamKind::BinderList => {
                        // Find the next Literal in syntax_pattern — that's
                        // the close delim of the binder-list loop.
                        let close = match sp.get(i + 1) {
                            Some(SyntaxExpr::Literal(text)) => text.clone(),
                            _ => return None,
                        };
                        positions.push(BinderPosition::BinderListLoop {
                            separator: separator.clone(),
                            close,
                            // B8 (2026-05-08): PNew-style — inner_positions
                            // is `[BinderIdent]`; binder_param_idx=0;
                            // collection_param_cat=None (no synthesized
                            // accumulator).
                            inner_positions: vec![BinderPosition::BinderIdent],
                            inner_action_args: vec![ActionArgKind::BinderName],
                            binder_param_idx: 0,
                            collection_param_cat: None,
                        });
                        action_args.push(ActionArgKind::BinderList);
                        // Skip the close Literal at i+1 — it's already
                        // absorbed into the BinderListLoop's close-branch
                        // dispatch. Without this skip, the close token
                        // would be double-consumed (once by BinderListLoop,
                        // once by the spurious pos+1 Literal arm).
                        skip_next = true;
                    }
                    ParamKind::SimpleCollection { elem_cat, coll_kind } => {
                        // B9 / Class 2 (2026-05-08): Sep-driven collection
                        // slot in a multi-position binder rule. Lower to
                        // ParamParse{collection: Some(...)} which dispatches
                        // by pushing a CollectionMarker into the GSS — the
                        // existing CollectionLoop apparatus then parses
                        // elements separated by `separator` until `close`.
                        // The action body extracts CollectionDrain.
                        let close = match sp.get(i + 1) {
                            Some(SyntaxExpr::Literal(text)) => text.clone(),
                            _ => return None,
                        };
                        positions.push(BinderPosition::ParamParse {
                            cat: elem_cat.clone(),
                            collection: Some(CollectionSepInfo {
                                separator: separator.clone(),
                                close,
                                coll_kind: coll_kind.clone(),
                                elem_cat: elem_cat.clone(),
                            }),
                        });
                        action_args.push(ActionArgKind::CollectionDrain {
                            elem_cat: elem_cat.clone(),
                            coll_kind: coll_kind.clone(),
                        });
                        // Skip the close Literal at i+1 — absorbed into
                        // CollectionLoop's close-branch dispatch.
                        skip_next = true;
                    }
                    _ => return None, // bare Simple, Body, Guard, Binder are not Sep-eligible.
                }
            }
            // B8 / Class 3 ZIP-MAP-SEP (2026-05-08): chained-Sep pattern
            // `*zip(left,right).*map(|p1,p2| body).*sep(",")`. Used by
            // rhocalc PInputs:
            //   ns:Vec(Name), ^[xs].p:[Name* -> Proc] |- "(" *zip(ns,xs)
            //     .*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc;
            // Per-iteration the inner walk parses a Name (n, spliced into
            // the synthesized ns accumulator) and captures a binder ident
            // (x, added to the xs binder scope).
            SyntaxExpr::Op(PatternOp::Sep {
                collection: _,
                separator,
                source: Some(source_op),
            }) => {
                // Source must be Map { source: Zip{left,right}, params, body }.
                let (zip_left, zip_right, map_params, map_body) = match source_op.as_ref() {
                    PatternOp::Map { source, params, body } => match source.as_ref() {
                        PatternOp::Zip { left, right } => (left, right, params, body),
                        _ => return None,
                    },
                    _ => return None,
                };
                if map_params.len() != 2 {
                    return None;
                }
                // Validate left/right param kinds:
                //   - left must be SimpleCollection (the names accumulator)
                //   - right must be BinderList (the multi-binder)
                let (collection_elem_cat,) = match param_map.get(&zip_left.to_string()) {
                    Some(ParamKind::SimpleCollection { elem_cat, .. }) => (elem_cat.clone(),),
                    _ => return None,
                };
                if !matches!(param_map.get(&zip_right.to_string()), Some(ParamKind::BinderList)) {
                    return None;
                }
                // map_params[0] alias for the names-element; map_params[1]
                // alias for the binder slot. Inside the body, Param(p1)
                // refers to a Name parse, Param(p2) refers to the binder
                // ident capture.
                let map_param_n = map_params[0].to_string();
                let map_param_x = map_params[1].to_string();
                let close = match sp.get(i + 1) {
                    Some(SyntaxExpr::Literal(text)) => text.clone(),
                    _ => return None,
                };
                // Walk the map body; build inner_positions and
                // inner_action_args per the Class 3 dispatch.
                let mut inner_positions: Vec<BinderPosition> = Vec::new();
                let mut inner_action_args: Vec<ActionArgKind> = Vec::new();
                let mut binder_param_idx_opt: Option<u8> = None;
                for inner_item in map_body {
                    match inner_item {
                        SyntaxExpr::Literal(text) => {
                            inner_positions.push(BinderPosition::Literal(text.clone()));
                        }
                        SyntaxExpr::Param(p_name) => {
                            let pn = p_name.to_string();
                            if pn == map_param_n {
                                // Names-element: parse as Name, splice into accumulator.
                                inner_positions.push(BinderPosition::ParamParse {
                                    cat: collection_elem_cat.clone(),
                                    collection: Some(CollectionSepInfo {
                                        separator: separator.clone(),
                                        close: close.clone(),
                                        coll_kind: CollectionType::Vec,
                                        elem_cat: collection_elem_cat.clone(),
                                    }),
                                });
                                inner_action_args.push(ActionArgKind::Term(
                                    collection_elem_cat.clone(),
                                ));
                            } else if pn == map_param_x {
                                // Binder-ident slot.
                                if binder_param_idx_opt.is_none() {
                                    binder_param_idx_opt = Some(inner_positions.len() as u8);
                                }
                                inner_positions.push(BinderPosition::BinderIdent);
                                inner_action_args.push(ActionArgKind::BinderName);
                            } else {
                                return None; // unrecognized inner Param.
                            }
                        }
                        SyntaxExpr::Op(_) => return None, // nested Op out of pilot.
                    }
                }
                let binder_param_idx = binder_param_idx_opt?;
                positions.push(BinderPosition::BinderListLoop {
                    separator: separator.clone(),
                    close,
                    inner_positions,
                    inner_action_args,
                    binder_param_idx,
                    collection_param_cat: Some(collection_elem_cat.clone()),
                });
                // Class 3 emits TWO action args: the synthesized Names
                // accumulator drain + the binder list. Order: names first,
                // then binder list — matches the order of the term_context
                // entries (ns:Vec(Name), ^[xs].p) so the action body's
                // field order is correct without extra reordering.
                action_args.push(ActionArgKind::CollectionDrain {
                    elem_cat: collection_elem_cat.clone(),
                    coll_kind: CollectionType::Vec,
                });
                action_args.push(ActionArgKind::BinderList);
                is_multi = true;
                has_binder = true;
                skip_next = true;
            }
            SyntaxExpr::Op(PatternOp::Opt { inner }) => {
                // Opt-Group: recursively classify inner SyntaxExprs.
                // Reuses param_map (inner Param references resolve against
                // the same TermContext entries — including any TermParam::Optional
                // already registered by walk_params). For the pilot, the
                // inner positions support Literal, ParamParse (Simple/Body),
                // BinderIdent, GuardSlot. Nested Optional and Sep are out
                // of pilot scope.
                let group_idx = positions.iter().filter(|p| {
                    matches!(p, BinderPosition::OptionalGroup { .. })
                }).count() as u8;

                let mut inner_positions: Vec<BinderPosition> = Vec::new();
                let mut inner_action_args: Vec<ActionArgKind> = Vec::new();

                for inner_item in inner {
                    match inner_item {
                        SyntaxExpr::Literal(text) => {
                            inner_positions.push(BinderPosition::Literal(text.clone()));
                        }
                        SyntaxExpr::Param(name) => {
                            let n = name.to_string();
                            let kind = param_map.get(&n)?;
                            match kind {
                                ParamKind::Binder => {
                                    inner_positions.push(BinderPosition::BinderIdent);
                                    inner_action_args.push(ActionArgKind::BinderName);
                                }
                                ParamKind::Body { cat } | ParamKind::Simple { cat } => {
                                    inner_positions.push(BinderPosition::ParamParse {
                                        cat: cat.clone(),
                                        collection: None,
                                    });
                                    inner_action_args.push(ActionArgKind::Term(cat.clone()));
                                }
                                ParamKind::Guard => {
                                    inner_positions.push(BinderPosition::GuardSlot);
                                    inner_action_args.push(ActionArgKind::Predicate);
                                }
                                ParamKind::BinderList => {
                                    return None;
                                }
                                // B9 pilot: SimpleCollection inside Optional
                                // is out of pilot scope. The optional-group
                                // inner walker doesn't yet support nested
                                // collection sub-parses.
                                ParamKind::SimpleCollection { .. } => {
                                    return None;
                                }
                            }
                        }
                        SyntaxExpr::Op(_) => {
                            return None;
                        }
                    }
                }

                if inner_positions.is_empty() {
                    return None;
                }

                // Compute first_token_set: the literal-text predicates that
                // trigger entry into the group. For BinderPosition::Literal,
                // first_token_set = vec![text]. ParamParse-leading inner
                // positions are out of pilot scope (would require threading
                // language access through classify_binder to compute
                // first_set_of_category).
                let first_token_set: Vec<String> = match &inner_positions[0] {
                    BinderPosition::Literal(text) => vec![text.clone()],
                    _ => return None,
                };

                positions.push(BinderPosition::OptionalGroup {
                    positions: inner_positions,
                    action_args: inner_action_args.clone(),
                    group_idx,
                    first_token_set,
                });
                action_args.push(ActionArgKind::Optional(inner_action_args));
            }
            // Op(Map/Zip) or chained ops — Phase 5c territory; skip for now.
            SyntaxExpr::Op(_) => return None,
        }
    }

    // Skip rules with no parsed positions (they're trivial and likely not
    // multi-step — let the atomic / TerminalKeyword classifier handle them).
    if positions.is_empty() {
        return None;
    }
    // Skip pure-literal rules (no params, no binder, no guard) — those are
    // already handled by the TerminalKeyword classifier.
    if action_args.is_empty() {
        return None;
    }

    // B9 / Class 2 (2026-05-08) pilot constraint: at most ONE SimpleCollection
    // slot per rule. The static `(result_src, rule_idx)` keying for the
    // emit_collection_close_lookup / emit_collection_loop_arm tables doesn't
    // accommodate two slots in the same rule. Multi-collection-slot Class 2
    // is a future extension; reject silently here so multi-slot rules fall
    // through to other classifiers (currently no other classifier handles
    // them, so they'll surface as rule-not-classified errors).
    let collection_slot_count = positions
        .iter()
        .filter(|p| matches!(p, BinderPosition::ParamParse { collection: Some(_), .. }))
        .count();
    if collection_slot_count > 1 {
        return None;
    }

    let action_arity: u8 = action_args.len() as u8;

    Some(BinderShape {
        label: rule.label.to_string(),
        result_cat: rule.category.to_string(),
        positions,
        is_multi,
        has_binder,
        action_arity,
        action_args,
        body_cat,
        param_cats,
    })
}

/// Extract the codomain name from `TypeExpr::Arrow { domain, codomain }`.
fn arrow_codomain_name(ty: &TypeExpr) -> Option<String> {
    match ty {
        TypeExpr::Arrow { codomain, .. } => match codomain.as_ref() {
            TypeExpr::Base(ident) => Some(ident.to_string()),
            _ => None,
        },
        _ => None,
    }
}

/// Look up a category name's src_idx in the categories slice.
pub(crate) fn lookup_src_idx(name: &str, categories: &[String]) -> Option<u16> {
    categories.iter().position(|c| c == name).map(|i| i as u16)
}

/// Phase 5 + F7 (2026-04-28): emit prefix-dispatch arms that recognize the
/// FIRST literal of each multi-step rule. On match, the arm pushes a
/// `RuleAt(1)` marker symbol and transitions to `BinderRule { ... }`.
///
/// **Multi-rule trigger disambiguation via Fork (F7):** when multiple rules
/// in the same result category share the same trigger keyword (e.g.,
/// Calculator's five `bool(arg)` cast rules with `arg` of different
/// categories), the arm emits `WpdsStepAction::Fork` with one branch per
/// rule. The walker fans out N `BranchCursor`s and `step_fanout` drives
/// each independently until lex-min selects the surviving branch.
///
/// Per-branch `LexicographicWeight::from_cost(0.0, result_src, rule_idx)`
/// gives a unique tiebreak by source-order rule_idx — preserving the
/// trampoline's first-declared-wins convention under tie. Wrong-arity
/// branches auto-discriminate via parse failure: if the wrong branch's
/// `BinderRule` state expects e.g. `,` but encounters `)`, the next
/// `engine.step` returns `Error` → `Drop` → only the right-arity branch
/// survives.
///
/// (Pre-F7 history: this used a FIRST-set lookup table + paren-depth scan
/// + fallback-rule heuristic. The principled Fork-based replacement
/// fulfills `feedback_use_wpds_disambiguation_not_heuristics.md`.)
pub(crate) fn emit_binder_prefix_arms(
    _language: &mettail_ast::language::LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    use std::collections::BTreeMap;

    /// Per-rule arm metadata.
    struct RuleEntry {
        rule_i: usize,
        shape: BinderShape,
    }

    // Group entries by (trigger, result_src_idx). BTreeMap gives
    // deterministic iteration order; within a group, source order is
    // preserved by insertion.
    let mut groups: BTreeMap<(String, u16), Vec<RuleEntry>> = BTreeMap::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder(rule) else {
                continue;
            };
            let trigger = match rule
                .syntax_pattern
                .as_ref()
                .and_then(|sp| sp.first())
            {
                Some(SyntaxExpr::Literal(text)) => text.clone(),
                _ => continue,
            };
            // Stage 3.20 / Commit 4 part 2 (Plan agent Fix, 2026-05-06):
            // skip `(`-triggered binders here — they're handled by
            // `prefix.rs::emit_paren_dispatch_arms` which emits a Fork
            // combining grouping + binder rule(s) so lex-min disambiguates
            // the `(`-conflict (e.g. Lambda's App rule shares `(` with the
            // B7 paren-grouping arm). Per `feedback_use_wpds_disambiguation_not_heuristics.md`.
            if trigger == "(" {
                continue;
            }
            let key = (trigger, cat_i as u16);
            groups.entry(key).or_default().push(RuleEntry {
                rule_i,
                shape,
            });
        }
    }

    let mut arms = Vec::new();
    for ((trigger, result_src_idx), entries) in groups {
        if entries.len() == 1 {
            // Single-rule group: ConsumeAndPush directly. No ambiguity, no
            // need for Fork.
            let entry = &entries[0];
            let rule_idx = entry.rule_i as u16;
            let body_src_idx = match &entry.shape.body_cat {
                Some(name) => lookup_src_idx(name, categories).unwrap_or(result_src_idx),
                None => result_src_idx,
            };
            arms.push(quote! {
                Some(mettail_prattail::automata::TokenKind::Fixed(__trigger))
                    if __trigger == #trigger && state_cat_src_idx == #result_src_idx => {
                    return WpdsStepAction::ConsumeAndPush {
                        symbol: StackSymbolV2::rule_at(
                            #result_src_idx, #rule_idx, 1u8, Some(_outer_bp),
                        ),
                        weight: LexicographicWeight::from_cost(
                            0.0, #result_src_idx, #rule_idx,
                        ),
                        new_state: WpdsState::BinderRule {
                            result_src_idx: #result_src_idx,
                            rule_idx: #rule_idx,
                            body_src_idx: #body_src_idx,
                            outer_bp: _outer_bp,
                        },
                        capture_token: false,
                    };
                }
            });
            continue;
        }

        // Multi-rule group → Fork. Emit one ForkBranch per rule; the
        // walker fans out cursors and lex-min picks the winner.
        let branches: Vec<TokenStream> = entries
            .iter()
            .map(|entry| {
                let rule_idx = entry.rule_i as u16;
                let body_src_idx = match &entry.shape.body_cat {
                    Some(name) => lookup_src_idx(name, categories).unwrap_or(result_src_idx),
                    None => result_src_idx,
                };
                quote! {
                    mettail_prattail::wpds_walker::ForkBranch {
                        symbol: StackSymbolV2::rule_at(
                            #result_src_idx, #rule_idx, 1u8, Some(_outer_bp),
                        ),
                        weight: LexicographicWeight::from_cost(
                            0.0, #result_src_idx, #rule_idx,
                        ),
                        new_state: WpdsState::BinderRule {
                            result_src_idx: #result_src_idx,
                            rule_idx: #rule_idx,
                            body_src_idx: #body_src_idx,
                            outer_bp: _outer_bp,
                        },
                        // Stage 3.12 / Class A.i (2026-05-01): default Push action.
                        action_kind: mettail_prattail::wpds_walker::ForkActionKind::Push,
                    }
                }
            })
            .collect();

        arms.push(quote! {
            Some(mettail_prattail::automata::TokenKind::Fixed(__trigger))
                if __trigger == #trigger && state_cat_src_idx == #result_src_idx => {
                return WpdsStepAction::Fork {
                    branches: vec![ #( #branches ),* ],
                    consume_trigger: true,
                };
            }
        });
    }
    quote! { #(#arms)* }
}

/// Phase 5: emit the body of `WpdsState::BinderRule`. Reads the marker's
/// `RuleAt(position)` from frontier_top, dispatches per-rule-per-position.
///
/// Stage 3.27d (G-PREFIX-BP, 2026-04-30): `prefix_bp_map` carries the
/// unary-prefix BP for rules whose shape matches the unary-prefix pattern.
/// ParamParse arms install `cur_bp = prefix_bp` for the operand sub-parse,
/// preventing lower-precedence trailing infix from stealing the prefix's
/// child. Non-prefix rules continue to use `cur_bp: 0`.
pub(crate) fn emit_binder_rule_body(
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
    prefix_bp_map: &HashMap<(u16, u16), u8>,
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder(rule) else {
                continue;
            };
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            // Stage 4 fix: emit a "rule complete" arm at position
            // `positions.len() + 1`. This arm fires when the marker has
            // advanced past the final syntax-pattern position (either via
            // a ConsumeAndReplace from a closing literal or a ReplaceAndPush
            // from a final ParamParse). It pops the RuleAt and fires the
            // semantic action; transitions to InfixLoop so the parent rule
            // can apply postfix/infix operators on the freshly-built result.
            let final_pos = (shape.positions.len() + 1) as u8;
            arms.push(quote! {
                (#result_src_idx, #rule_idx, #final_pos) => {
                    return WpdsStepAction::Pop {
                        weight: LexicographicWeight::one(),
                        new_state: WpdsState::InfixLoop {
                            cur_bp: *outer_bp,
                        },
                    };
                }
            });
            for (idx, position) in shape.positions.iter().enumerate() {
                let pos = (idx + 1) as u8;
                let next_pos = pos + 1;
                let arm = match position {
                    BinderPosition::Literal(text) => quote! {
                        (#result_src_idx, #rule_idx, #pos) => {
                            // Stage 3.20 / L12 Commit F (2026-05-06):
                            // Cluster 1 hack #5 closure. Single-branch
                            // GuardedConsumeAndReplace Fork — peek_text
                            // == #text guard runs inside the walker,
                            // failure produces no child (cursor dies via
                            // step_fanout's empty-children pathway).
                            return WpdsStepAction::Fork {
                                branches: vec![mettail_prattail::wpds_walker::ForkBranch {
                                    symbol: StackSymbolV2::rule_at(
                                        #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                    ),
                                    weight: LexicographicWeight::one(),
                                    new_state: WpdsState::BinderRule {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        body_src_idx: *_body_src_idx,
                                        outer_bp: *outer_bp,
                                    },
                                    action_kind:
                                        mettail_prattail::wpds_walker::ForkActionKind::GuardedConsumeAndReplace {
                                            expected_text: #text.to_string(),
                                        },
                                }],
                                consume_trigger: false,
                            };
                        }
                    },
                    BinderPosition::BinderIdent => quote! {
                        (#result_src_idx, #rule_idx, #pos) => {
                            // Stage 3.20 / L12 Commit F (2026-05-06):
                            // Cluster 1 hack #6 closure. Single-branch
                            // GuardedConsumeIdentAndReplace Fork —
                            // peek_kind == Ident guard runs inside the
                            // walker.
                            return WpdsStepAction::Fork {
                                branches: vec![mettail_prattail::wpds_walker::ForkBranch {
                                    symbol: StackSymbolV2::rule_at(
                                        #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                    ),
                                    weight: LexicographicWeight::one(),
                                    new_state: WpdsState::BinderRule {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        body_src_idx: *_body_src_idx,
                                        outer_bp: *outer_bp,
                                    },
                                    action_kind:
                                        mettail_prattail::wpds_walker::ForkActionKind::GuardedConsumeIdentAndReplace {
                                            start_scope: true,
                                        },
                                }],
                                consume_trigger: false,
                            };
                        }
                    },
                    BinderPosition::BinderListLoop {
                        separator: _,
                        close,
                        collection_param_cat,
                        ..
                    } => {
                        // Phase 5b: enter BinderListLoop sub-state. The
                        // first iteration here checks `close` (empty list)
                        // or starts collecting Idents; subsequent iterations
                        // (handled in BinderListLoop's own state) use the
                        // separator to chain Ident captures.
                        //
                        // B8 / Class 3 (2026-05-08): when collection_param_cat
                        // is Some, this is a Class 3 ZIP-MAP-SEP rule and
                        // the bootstrap differs: we Push a CollectionMarker
                        // to allocate the Names accumulator (and push
                        // ActionArg::CollectionId for the terminal action),
                        // then transition directly into BinderListLoop
                        // {sub_pos:0}. The StartBinderScope is opened at
                        // the first BinderIdent capture inside the inner
                        // walk via start_scope=true (or, in the empty-list
                        // path, via the BRANCH 1 effect).
                        if collection_param_cat.is_some() {
                            quote! {
                                (#result_src_idx, #rule_idx, #pos) => {
                                    let _ = tokens.peek_text(_pos);
                                    return WpdsStepAction::Fork {
                                        branches: vec![
                                            // BRANCH 1: empty close — Class 3
                                            // multi-effect: log
                                            // [StartCollection,
                                            // PushCollectionId{id:0},
                                            // StartBinderScope] so the
                                            // empty-list path matches the
                                            // terminal action's arity-3
                                            // expectation [CollectionId,
                                            // BinderScope, Term<Proc>].
                                            mettail_prattail::wpds_walker::ForkBranch {
                                                symbol: StackSymbolV2::rule_at(
                                                    #result_src_idx, #rule_idx,
                                                    #next_pos, Some(*outer_bp),
                                                ),
                                                weight: LexicographicWeight::from_cost(
                                                    0.0, #result_src_idx, #rule_idx,
                                                ),
                                                new_state: WpdsState::BinderRule {
                                                    result_src_idx: #result_src_idx,
                                                    rule_idx: #rule_idx,
                                                    body_src_idx: *_body_src_idx,
                                                    outer_bp: *outer_bp,
                                                },
                                                action_kind:
                                                    mettail_prattail::wpds_walker::ForkActionKind::GuardedConsumeAndReplaceWithMultipleEffects {
                                                        expected_text: #close.to_string(),
                                                        effects: vec![
                                                            mettail_prattail::wpds_walker::BuilderDelta::StartCollection,
                                                            mettail_prattail::wpds_walker::BuilderDelta::PushCollectionId { id: 0u8 },
                                                            mettail_prattail::wpds_walker::BuilderDelta::StartBinderScope {
                                                                names: Vec::new(),
                                                            },
                                                        ],
                                                    },
                                            },
                                            // BRANCH 2: non-empty — Push
                                            // CollectionMarker, transition
                                            // to BinderListLoop{sub_pos:0}.
                                            mettail_prattail::wpds_walker::ForkBranch {
                                                symbol: StackSymbolV2::collection_marker(
                                                    #result_src_idx, #rule_idx, 0,
                                                ),
                                                weight: LexicographicWeight::from_cost(
                                                    mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP,
                                                    #result_src_idx, #rule_idx,
                                                ),
                                                new_state: WpdsState::BinderListLoop {
                                                    result_src_idx: #result_src_idx,
                                                    rule_idx: #rule_idx,
                                                    body_src_idx: *_body_src_idx,
                                                    outer_bp: *outer_bp,
                                                    marker_pos: #pos,
                                                    next_pos: #next_pos,
                                                    sub_pos: 0u8,
                                                },
                                                action_kind:
                                                    mettail_prattail::wpds_walker::ForkActionKind::Push,
                                            },
                                        ],
                                        consume_trigger: false,
                                    };
                                }
                            }
                        } else {
                        quote! {
                            (#result_src_idx, #rule_idx, #pos) => {
                                // L12 follow-up B2 (2026-05-07): two-branch
                                // GuardedFork over empty (close-delim) and
                                // non-empty (first-ident) bootstrap paths.
                                // Each branch carries a runtime guard so at
                                // most one fires per dispatch.
                                //
                                //   - BRANCH 1 (empty): GuardedConsumeAndReplaceWithEffect
                                //     fires only when peek_text == close.
                                //     Logs StartBinderScope { names: vec![] }.
                                //   - BRANCH 2 (first ident): GuardedConsumeIdentAndReplace
                                //     fires only when peek_kind == Ident.
                                //
                                // Pre-fix: BRANCH 1 (ConsumeAndReplaceWithEffect)
                                // and BRANCH 2 (ConsumeIdentAndReplace) BOTH
                                // fired unconditionally on every dispatch,
                                // contributing to BinderListLoop's exponential
                                // cursor explosion on multi-binder grammars.
                                let _ = tokens.peek_text(_pos);
                                return WpdsStepAction::Fork {
                                    branches: vec![
                                        // BRANCH 1: empty close — GuardedConsumeAndReplaceWithEffect
                                        mettail_prattail::wpds_walker::ForkBranch {
                                            symbol: StackSymbolV2::rule_at(
                                                #result_src_idx, #rule_idx,
                                                #next_pos, Some(*outer_bp),
                                            ),
                                            weight: LexicographicWeight::from_cost(
                                                0.0, #result_src_idx, #rule_idx,
                                            ),
                                            new_state: WpdsState::BinderRule {
                                                result_src_idx: #result_src_idx,
                                                rule_idx: #rule_idx,
                                                body_src_idx: *_body_src_idx,
                                                outer_bp: *outer_bp,
                                            },
                                            action_kind:
                                                mettail_prattail::wpds_walker::ForkActionKind::GuardedConsumeAndReplaceWithEffect {
                                                    expected_text: #close.to_string(),
                                                    effect:
                                                        mettail_prattail::wpds_walker::BuilderDelta::StartBinderScope {
                                                            names: Vec::new(),
                                                        },
                                                },
                                        },
                                        // BRANCH 2: first ident — GuardedConsumeIdentAndReplace
                                        mettail_prattail::wpds_walker::ForkBranch {
                                            symbol: StackSymbolV2::rule_at(
                                                #result_src_idx, #rule_idx,
                                                #pos, Some(*outer_bp),
                                            ),
                                            weight: LexicographicWeight::from_cost(
                                                mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP,
                                                #result_src_idx, #rule_idx,
                                            ),
                                            new_state: WpdsState::BinderListLoop {
                                                result_src_idx: #result_src_idx,
                                                rule_idx: #rule_idx,
                                                body_src_idx: *_body_src_idx,
                                                outer_bp: *outer_bp,
                                                marker_pos: #pos,
                                                next_pos: #next_pos,
                                                sub_pos: 0u8,
                                            },
                                            action_kind:
                                                mettail_prattail::wpds_walker::ForkActionKind::GuardedConsumeIdentAndReplace {
                                                    start_scope: true,
                                                },
                                        },
                                    ],
                                    consume_trigger: false,
                                };
                            }
                        }
                        }
                    }
                    BinderPosition::ParamParse { cat, collection } => {
                        let cat_src_idx = lookup_src_idx(cat, categories).unwrap_or(0);
                        // Stage 3.27d (G-PREFIX-BP, 2026-04-30): for unary-prefix
                        // rules, install `cur_bp = prefix_bp` so the operand sub-parse
                        // cannot be stolen by lower-precedence trailing infix.
                        let cur_bp_lit: u8 = prefix_bp_map
                            .get(&(result_src_idx, rule_idx))
                            .copied()
                            .unwrap_or(0u8);
                        match collection {
                            None => quote! {
                                (#result_src_idx, #rule_idx, #pos) => {
                                    // Replace marker to next_pos so when the
                                    // sub-parse returns, Unwinding-RuleAt sees
                                    // the post-param position. THEN push
                                    // CategoryEntry on top of the new marker.
                                    return WpdsStepAction::ReplaceAndPush {
                                        replace_symbol: StackSymbolV2::rule_at(
                                            #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                        ),
                                        push_symbol: StackSymbolV2::category_entry(#cat_src_idx),
                                        weight: LexicographicWeight::one(),
                                        new_state: WpdsState::PrefixDispatch {
                                            pos: _pos,
                                            cur_bp: #cur_bp_lit,
                                        },
                                    };
                                }
                            },
                            Some(_) => {
                                // B9 / Class 2 (2026-05-08): the slot is a
                                // Sep-driven collection. Replace the rule's
                                // RuleAt marker with `next_pos` (so when the
                                // CollectionMarker pops, Unwinding-RuleAt
                                // sees the post-collection position) AND
                                // push a CollectionMarker keyed on this
                                // rule's `(result_src_idx, rule_idx)`.
                                //
                                // The walker's emit_push_side_effects logic
                                // sees the CollectionMarker push, allocates
                                // an accumulator id, patches symbol.bp =
                                // Some(id), and pushes ActionArg::CollectionId
                                // onto the args stack. The transition state
                                // is PrefixDispatch{cur_bp: 0} — the next
                                // step's frontier_top is the marker, and
                                // the existing CollectionLoop apparatus
                                // (emit_collection_close_lookup +
                                // emit_collection_loop_arm, extended in
                                // collection.rs to recognize Class-2 binder
                                // rules) parses elements separated by
                                // `separator` until `close`.
                                //
                                // On close, the CollectionMarker pops and
                                // the walker checks is_binder_internal_collection
                                // — for Class-2 rules this returns true, so
                                // FireAction is suppressed (the binder
                                // rule's terminal action will drain the
                                // CollectionId at its own RuleAt pop).
                                quote! {
                                    (#result_src_idx, #rule_idx, #pos) => {
                                        return WpdsStepAction::ReplaceAndPush {
                                            replace_symbol: StackSymbolV2::rule_at(
                                                #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                            ),
                                            push_symbol: StackSymbolV2::collection_marker(
                                                #result_src_idx, #rule_idx, 0,
                                            ),
                                            weight: LexicographicWeight::one(),
                                            new_state: WpdsState::PrefixDispatch {
                                                pos: _pos,
                                                cur_bp: 0u8,
                                            },
                                        };
                                    }
                                }
                            }
                        }
                    }
                    BinderPosition::GuardSlot => quote! {
                        (#result_src_idx, #rule_idx, #pos) => {
                            // Phase 6: parse predicate inline. Walker
                            // invokes parse_predicate_from_tokens, pushes
                            // ActionArg::Predicate, advances pos.
                            return WpdsStepAction::ParsePredicate {
                                replace_symbol: StackSymbolV2::rule_at(
                                    #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                ),
                                weight: LexicographicWeight::one(),
                                new_state: WpdsState::BinderRule {
                                    result_src_idx: #result_src_idx,
                                    rule_idx: #rule_idx,
                                    body_src_idx: *_body_src_idx,
                                    outer_bp: *outer_bp,
                                },
                            };
                        }
                    },
                    BinderPosition::OptionalGroup { group_idx, .. } => {
                        // Opt-Group: outer rule reached an `#opt(...)` group
                        // at this position. Transition to OptionalGroup state
                        // with sub_pos=0; the engine's OptionalGroup arm
                        // peeks the FIRST set, decides take-or-skip, and
                        // (on the take path) walks inner positions until
                        // OptGroupFinalize advances the outer marker to
                        // next_pos. On the skip path, OptGroupAbsent
                        // advances directly to next_pos.
                        let group_idx_byte = *group_idx;
                        quote! {
                            (#result_src_idx, #rule_idx, #pos) => {
                                return WpdsStepAction::Advance(
                                    WpdsState::OptionalGroup {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        group_idx: #group_idx_byte,
                                        sub_pos: 0,
                                        outer_bp: *outer_bp,
                                    },
                                );
                            }
                        }
                    }
                };
                arms.push(arm);
            }
        }
    }
    if arms.is_empty() {
        return quote! { WpdsStepAction::Idle };
    }
    quote! {
        {
            let position: u8 = match frontier_top.map(|n| n.symbol.kind) {
                Some(mettail_prattail::wpds_runtime::SymbolKind::RuleAt(p)) => p,
                _ => return WpdsStepAction::Idle,
            };
            // The empty-list branch needs to push an empty BinderList arg
            // representing zero binders. Use a closure-based local helper.
            #[allow(unused_variables)]
            let b_pre_finalize_empty_list = || ();
            match (*result_src_idx, *rule_idx, position) {
                #(#arms)*
                _ => WpdsStepAction::Idle,
            }
        }
    }
}

/// B8 / Class 3 (2026-05-08): emit a per-rule predicate `is_binderlist_inner(rule_idx)`
/// that returns `true` when the rule is a Class 3 ZIP-MAP-SEP rule (its
/// BinderListLoop has more than one inner position). Used by the Unwinding-
/// OptionalGroupAt arm to route back to BinderListLoop instead of
/// OptionalGroup state when the symbol belongs to a Class 3 rule.
pub(crate) fn emit_binderlist_inner_lookup(per_cat: &[Vec<GrammarRule>]) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder(rule) else {
                continue;
            };
            let is_class3 = shape.positions.iter().any(|p| {
                matches!(
                    p,
                    BinderPosition::BinderListLoop {
                        collection_param_cat: Some(_),
                        ..
                    }
                )
            });
            if is_class3 {
                let cat = cat_i as u16;
                let rule_idx = rule_i as u16;
                arms.push(quote! { (#cat, #rule_idx) => true, });
            }
        }
    }
    if arms.is_empty() {
        quote! { false }
    } else {
        quote! {
            match (result_src_idx, rule_idx) {
                #(#arms)*
                _ => false,
            }
        }
    }
}

/// B8 / Issue D (2026-05-09): emit a per-rule predicate
/// `is_class3_collection(rule_idx) -> bool` that returns `true` when
/// the rule has a Class 3 BinderListLoop. Used by the walker's
/// `emit_push_side_effects` to atomically open a BinderScope alongside
/// the Names accumulator allocation when a Class 3 CollectionMarker
/// is pushed.
pub(crate) fn emit_is_class3_collection(per_cat: &[Vec<GrammarRule>]) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder(rule) else {
                continue;
            };
            let is_class3 = shape.positions.iter().any(|p| {
                matches!(
                    p,
                    BinderPosition::BinderListLoop {
                        collection_param_cat: Some(_),
                        ..
                    }
                )
            });
            if is_class3 {
                let cat = cat_i as u16;
                let rule_idx = rule_i as u16;
                arms.push(quote! { (#cat, #rule_idx) => true, });
            }
        }
    }
    if arms.is_empty() {
        quote! { false }
    } else {
        quote! {
            match (src_idx, rule_idx) {
                #(#arms)*
                _ => false,
            }
        }
    }
}

/// B8 / Issue A' (2026-05-09): emit a per-rule lookup that returns
/// `(marker_pos, next_pos, body_src_idx)` for Class 3 BinderListLoop
/// slots. Used by the Unwinding-OptionalGroupAt arm to reconstruct the
/// outer BinderRule's slot coordinates when routing back into
/// BinderListLoop after an inner-walk sub-parse returns. Pre-fix, the
/// engine arm hardcoded `marker_pos: 0u8, next_pos: 0u8` which broke
/// sub_pos=N arms that need the real outer-position values.
///
/// Returns `(0u8, 0u8, 0u16)` for non-Class-3 rules; the engine arm
/// only consults this lookup when `is_binderlist_inner` returns true,
/// so the default branch is unreachable in practice.
pub(crate) fn emit_binderlist_inner_metadata(per_cat: &[Vec<GrammarRule>]) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder(rule) else {
                continue;
            };
            for (idx, position) in shape.positions.iter().enumerate() {
                if let BinderPosition::BinderListLoop {
                    collection_param_cat: Some(_),
                    ..
                } = position {
                    let cat = cat_i as u16;
                    let rule_idx = rule_i as u16;
                    let marker_pos = (idx + 1) as u8;
                    let next_pos = marker_pos + 1;
                    // body_src_idx is the result category's idx — same
                    // as cat_i for binder rules emitting their own cat.
                    let body_src = cat_i as u16;
                    arms.push(quote! {
                        (#cat, #rule_idx) => (#marker_pos, #next_pos, #body_src),
                    });
                }
            }
        }
    }
    if arms.is_empty() {
        quote! { (0u8, 0u8, 0u16) }
    } else {
        quote! {
            match (result_src_idx, rule_idx) {
                #(#arms)*
                _ => (0u8, 0u8, 0u16),
            }
        }
    }
}

/// Phase 5b + B8 (2026-05-08): emit the body of `WpdsState::BinderListLoop`.
/// The state body dispatches on `(result_src_idx, rule_idx, sub_pos)`.
///
/// PNew-style rules (inner_positions=[BinderIdent], collection_param_cat=
/// None) emit ONE arm at sub_pos=0: the legacy 3-branch fork over close /
/// sep / ident — the third branch's GuardedConsumeIdentAndReplace
/// captures the Ident inline and stays at sub_pos=0.
///
/// Class 3 ZIP-MAP-SEP rules (inner_positions has multiple slots,
/// collection_param_cat=Some(elem_cat)) emit ARMS for sub_pos=0 (3-branch
/// fork over close / sep / first inner) PLUS one arm per
/// inner_positions[i] at sub_pos=i+1 (dispatching the i-th inner slot)
/// PLUS a wrap arm at sub_pos=inner_positions.len()+1 that loops back
/// to sub_pos=0.
pub(crate) fn emit_binder_list_loop_body(
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder(rule) else {
                continue;
            };
            for (idx, position) in shape.positions.iter().enumerate() {
                if let BinderPosition::BinderListLoop {
                    separator,
                    close,
                    inner_positions,
                    inner_action_args: _,
                    binder_param_idx: _,
                    collection_param_cat,
                } = position {
                    let pos = (idx + 1) as u8;
                    let next_pos = pos + 1;
                    let result_src_idx = cat_i as u16;
                    let rule_idx = rule_i as u16;
                    let is_class3 = collection_param_cat.is_some();
                    if !is_class3 {
                    arms.push(quote! {
                        (#result_src_idx, #rule_idx, 0u8) => {
                            // L12 follow-up B2 (2026-05-07): three-branch
                            // GuardedFork over close / sep / ident. Each
                            // branch carries a runtime peek_text/peek_kind
                            // guard so at most one branch's child cursor
                            // is allocated per dispatch. Pre-fix the
                            // unguarded `Consume` and `ConsumeIdentAndReplace`
                            // branches fired on every dispatch regardless
                            // of token, multiplying cursor count
                            // exponentially per BinderListLoop iteration
                            // — caused >4000s hangs on rhocalc::PNew
                            // multi-binder grammars.
                            //
                            // Branch semantics:
                            //   - BRANCH 1 (close): GuardedConsumeAndReplace
                            //     fires only when peek_text == close.
                            //     Weight 0.0; transitions to BinderRule.
                            //   - BRANCH 2 (sep): GuardedConsume fires
                            //     only when peek_text == separator.
                            //     Weight 0.0; stays in BinderListLoop.
                            //   - BRANCH 3 (ident): GuardedConsumeIdentAndReplace
                            //     fires only when peek_kind == Ident.
                            //     Weight EPSILON_OPT_SKIP; stays in
                            //     BinderListLoop.
                            //
                            // When all three guards fail (e.g. unexpected
                            // punctuation), `step_fanout`'s empty-children
                            // pathway raises `Error("all fork branches
                            // dropped")` cleanly.
                            let _ = tokens.peek_text(_pos);
                            return WpdsStepAction::Fork {
                                branches: vec![
                                    // BRANCH 1: close — GuardedConsumeAndReplace
                                    mettail_prattail::wpds_walker::ForkBranch {
                                        symbol: StackSymbolV2::rule_at(
                                            #result_src_idx, #rule_idx,
                                            #next_pos, Some(*outer_bp),
                                        ),
                                        weight: LexicographicWeight::from_cost(
                                            0.0, #result_src_idx, #rule_idx,
                                        ),
                                        new_state: WpdsState::BinderRule {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            body_src_idx: *body_src_idx,
                                            outer_bp: *outer_bp,
                                        },
                                        action_kind:
                                            mettail_prattail::wpds_walker::ForkActionKind::GuardedConsumeAndReplace {
                                                expected_text: #close.to_string(),
                                            },
                                    },
                                    // BRANCH 2: sep — GuardedConsume
                                    mettail_prattail::wpds_walker::ForkBranch {
                                        symbol: StackSymbolV2::category_entry(0),
                                        weight: LexicographicWeight::from_cost(
                                            0.0, #result_src_idx, #rule_idx,
                                        ),
                                        new_state: WpdsState::BinderListLoop {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            body_src_idx: *body_src_idx,
                                            outer_bp: *outer_bp,
                                            marker_pos: *marker_pos,
                                            next_pos: *next_pos,
                                            sub_pos: 0u8,
                                        },
                                        action_kind:
                                            mettail_prattail::wpds_walker::ForkActionKind::GuardedConsume {
                                                expected_text: #separator.to_string(),
                                            },
                                    },
                                    // BRANCH 3: ident — GuardedConsumeIdentAndReplace
                                    mettail_prattail::wpds_walker::ForkBranch {
                                        symbol: StackSymbolV2::rule_at(
                                            #result_src_idx, #rule_idx,
                                            *marker_pos, Some(*outer_bp),
                                        ),
                                        weight: LexicographicWeight::from_cost(
                                            mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP,
                                            #result_src_idx, #rule_idx,
                                        ),
                                        new_state: WpdsState::BinderListLoop {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            body_src_idx: *body_src_idx,
                                            outer_bp: *outer_bp,
                                            marker_pos: *marker_pos,
                                            next_pos: *next_pos,
                                            sub_pos: 0u8,
                                        },
                                        action_kind:
                                            mettail_prattail::wpds_walker::ForkActionKind::GuardedConsumeIdentAndReplace {
                                                start_scope: false,
                                            },
                                    },
                                ],
                                consume_trigger: false,
                            };
                        }
                    });
                    } else {
                        // B8 Class 3 (2026-05-08): emit per-sub_pos arms.
                        let inner_count = inner_positions.len() as u8;
                        // sub_pos=0: 3-branch fork over close / sep / first-
                        // inner-dispatch. The first-inner branch pushes
                        // OptionalGroupAt(rule, 1, outer_bp) without
                        // consuming a token; transitions to BinderListLoop
                        // {sub_pos:1}, where the inner walk dispatches the
                        // first inner_position.
                        arms.push(quote! {
                            (#result_src_idx, #rule_idx, 0u8) => {
                                let _ = tokens.peek_text(_pos);
                                return WpdsStepAction::Fork {
                                    branches: vec![
                                        // BRANCH 1: close → finish loop.
                                        mettail_prattail::wpds_walker::ForkBranch {
                                            symbol: StackSymbolV2::rule_at(
                                                #result_src_idx, #rule_idx,
                                                #next_pos, Some(*outer_bp),
                                            ),
                                            weight: LexicographicWeight::from_cost(
                                                0.0, #result_src_idx, #rule_idx,
                                            ),
                                            new_state: WpdsState::BinderRule {
                                                result_src_idx: #result_src_idx,
                                                rule_idx: #rule_idx,
                                                body_src_idx: *body_src_idx,
                                                outer_bp: *outer_bp,
                                            },
                                            action_kind:
                                                mettail_prattail::wpds_walker::ForkActionKind::GuardedConsumeAndReplace {
                                                    expected_text: #close.to_string(),
                                                },
                                        },
                                        // BRANCH 2: sep → next iteration.
                                        mettail_prattail::wpds_walker::ForkBranch {
                                            symbol: StackSymbolV2::category_entry(0),
                                            weight: LexicographicWeight::from_cost(
                                                0.0, #result_src_idx, #rule_idx,
                                            ),
                                            new_state: WpdsState::BinderListLoop {
                                                result_src_idx: #result_src_idx,
                                                rule_idx: #rule_idx,
                                                body_src_idx: *body_src_idx,
                                                outer_bp: *outer_bp,
                                                marker_pos: *marker_pos,
                                                next_pos: *next_pos,
                                                sub_pos: 0u8,
                                            },
                                            action_kind:
                                                mettail_prattail::wpds_walker::ForkActionKind::GuardedConsume {
                                                    expected_text: #separator.to_string(),
                                                },
                                        },
                                        // BRANCH 3: first-inner — Push
                                        // OptionalGroupAt(rule, 1, outer_bp)
                                        // and transition to sub_pos:1 where
                                        // the inner walk takes over. No
                                        // token consumed at this branch.
                                        mettail_prattail::wpds_walker::ForkBranch {
                                            symbol: StackSymbolV2::optional_group_at(
                                                #result_src_idx, #rule_idx,
                                                1u8, *outer_bp,
                                            ),
                                            weight: LexicographicWeight::from_cost(
                                                mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP,
                                                #result_src_idx, #rule_idx,
                                            ),
                                            new_state: WpdsState::BinderListLoop {
                                                result_src_idx: #result_src_idx,
                                                rule_idx: #rule_idx,
                                                body_src_idx: *body_src_idx,
                                                outer_bp: *outer_bp,
                                                marker_pos: *marker_pos,
                                                next_pos: *next_pos,
                                                sub_pos: 1u8,
                                            },
                                            action_kind:
                                                mettail_prattail::wpds_walker::ForkActionKind::Push,
                                        },
                                    ],
                                    consume_trigger: false,
                                };
                            }
                        });
                        // sub_pos=N for N=1..=inner_count: dispatch
                        // inner_positions[N-1].
                        for (i, inner_pos) in inner_positions.iter().enumerate() {
                            let cur_sp = (i + 1) as u8;
                            let next_sp = if i + 1 == inner_positions.len() { 0u8 } else { (i + 2) as u8 };
                            let arm = match inner_pos {
                                BinderPosition::Literal(text) => {
                                    let txt = text.clone();
                                    quote! {
                                        (#result_src_idx, #rule_idx, #cur_sp) => {
                                            return WpdsStepAction::Fork {
                                                branches: vec![
                                                    mettail_prattail::wpds_walker::ForkBranch {
                                                        symbol: StackSymbolV2::optional_group_at(
                                                            #result_src_idx, #rule_idx,
                                                            #next_sp, *outer_bp,
                                                        ),
                                                        weight: LexicographicWeight::from_cost(
                                                            0.0, #result_src_idx, #rule_idx,
                                                        ),
                                                        new_state: WpdsState::BinderListLoop {
                                                            result_src_idx: #result_src_idx,
                                                            rule_idx: #rule_idx,
                                                            body_src_idx: *body_src_idx,
                                                            outer_bp: *outer_bp,
                                                            marker_pos: *marker_pos,
                                                            next_pos: *next_pos,
                                                            sub_pos: #next_sp,
                                                        },
                                                        action_kind:
                                                            mettail_prattail::wpds_walker::ForkActionKind::GuardedConsumeAndReplace {
                                                                expected_text: #txt.to_string(),
                                                            },
                                                    },
                                                ],
                                                consume_trigger: false,
                                            };
                                        }
                                    }
                                }
                                BinderPosition::BinderIdent => {
                                    // Capture ident as binder name. On the
                                    // last inner step, transition back to
                                    // sub_pos=0 AND replace top with the
                                    // RuleAt marker so the next iteration
                                    // sees BinderListLoop's marker.
                                    let is_last = i + 1 == inner_positions.len();
                                    if is_last {
                                        quote! {
                                            (#result_src_idx, #rule_idx, #cur_sp) => {
                                                return WpdsStepAction::Fork {
                                                    branches: vec![
                                                        mettail_prattail::wpds_walker::ForkBranch {
                                                            symbol: StackSymbolV2::rule_at(
                                                                #result_src_idx, #rule_idx,
                                                                *marker_pos, Some(*outer_bp),
                                                            ),
                                                            weight: LexicographicWeight::from_cost(
                                                                0.0, #result_src_idx, #rule_idx,
                                                            ),
                                                            new_state: WpdsState::BinderListLoop {
                                                                result_src_idx: #result_src_idx,
                                                                rule_idx: #rule_idx,
                                                                body_src_idx: *body_src_idx,
                                                                outer_bp: *outer_bp,
                                                                marker_pos: *marker_pos,
                                                                next_pos: *next_pos,
                                                                sub_pos: 0u8,
                                                            },
                                                            action_kind:
                                                                mettail_prattail::wpds_walker::ForkActionKind::GuardedConsumeIdentAndReplace {
                                                                    start_scope: false,
                                                                },
                                                        },
                                                    ],
                                                    consume_trigger: false,
                                                };
                                            }
                                        }
                                    } else {
                                        quote! {
                                            (#result_src_idx, #rule_idx, #cur_sp) => {
                                                return WpdsStepAction::Fork {
                                                    branches: vec![
                                                        mettail_prattail::wpds_walker::ForkBranch {
                                                            symbol: StackSymbolV2::optional_group_at(
                                                                #result_src_idx, #rule_idx,
                                                                #next_sp, *outer_bp,
                                                            ),
                                                            weight: LexicographicWeight::from_cost(
                                                                0.0, #result_src_idx, #rule_idx,
                                                            ),
                                                            new_state: WpdsState::BinderListLoop {
                                                                result_src_idx: #result_src_idx,
                                                                rule_idx: #rule_idx,
                                                                body_src_idx: *body_src_idx,
                                                                outer_bp: *outer_bp,
                                                                marker_pos: *marker_pos,
                                                                next_pos: *next_pos,
                                                                sub_pos: #next_sp,
                                                            },
                                                            action_kind:
                                                                mettail_prattail::wpds_walker::ForkActionKind::GuardedConsumeIdentAndReplace {
                                                                    start_scope: false,
                                                                },
                                                        },
                                                    ],
                                                    consume_trigger: false,
                                                };
                                            }
                                        }
                                    }
                                }
                                BinderPosition::ParamParse { cat, collection: _ } => {
                                    // Push CategoryEntry, transition to
                                    // PrefixDispatch. The current top is
                                    // OptionalGroupAt(rule, cur_sp); we
                                    // replace it with OptionalGroupAt(rule,
                                    // next_sp) so on Unwinding we land at
                                    // sub_pos=next_sp.
                                    let cat_src_idx = lookup_src_idx(cat, categories).unwrap_or(0);
                                    quote! {
                                        (#result_src_idx, #rule_idx, #cur_sp) => {
                                            return WpdsStepAction::ReplaceAndPush {
                                                replace_symbol: StackSymbolV2::optional_group_at(
                                                    #result_src_idx, #rule_idx,
                                                    #next_sp, *outer_bp,
                                                ),
                                                push_symbol: StackSymbolV2::category_entry(#cat_src_idx),
                                                weight: LexicographicWeight::one(),
                                                new_state: WpdsState::PrefixDispatch {
                                                    pos: _pos,
                                                    cur_bp: 0u8,
                                                },
                                            };
                                        }
                                    }
                                }
                                _ => {
                                    // Other inner positions (GuardSlot,
                                    // OptionalGroup, BinderListLoop) out of
                                    // pilot scope.
                                    quote! {}
                                }
                            };
                            arms.push(arm);
                        }
                        let _ = inner_count;
                    }
                }
            }
        }
    }
    if arms.is_empty() {
        return quote! { WpdsStepAction::Idle };
    }
    quote! {
        {
            // Bind categories ref so the per-arm code can use
            // lookup_src_idx — though Class 3 emits cat_src_idx as
            // hard-coded literals, this is safe.
            match (*result_src_idx, *rule_idx, *sub_pos) {
                #(#arms)*
                _ => WpdsStepAction::Idle,
            }
        }
    }
}

/// Opt-Group (2026-04-29): emit the body of `WpdsState::OptionalGroup`.
/// Dispatches on `(*result_src_idx, *rule_idx, *group_idx, *sub_pos)` to:
///   - sub_pos == 0: peek FIRST set, emit `Push(OptionalGroupAt(1))` (take)
///     or `OptGroupAbsent` (skip).
///   - sub_pos in 1..=inner.len(): walk inner positions (Literal,
///     ParamParse, BinderIdent, GuardSlot) — each step replaces
///     OptionalGroupAt(sub_pos) with OptionalGroupAt(sub_pos+1).
///   - sub_pos == inner.len() + 1: emit `OptGroupFinalize` to pop the
///     OptionalGroupAt marker, finalize the inner-arg scope, and advance
///     the outer RuleAt to next_outer_pos.
pub(crate) fn emit_optional_group_body(
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
    prefix_bp_map: &HashMap<(u16, u16), u8>,
) -> TokenStream {
    let mut arms: Vec<TokenStream> = Vec::new();

    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder(rule) else {
                continue;
            };
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;

            for (outer_idx, outer_pos) in shape.positions.iter().enumerate() {
                let outer_pos_byte = (outer_idx + 1) as u8;
                let outer_next_pos_byte = outer_pos_byte + 1;
                let BinderPosition::OptionalGroup {
                    positions: inner,
                    first_token_set,
                    group_idx,
                    ..
                } = outer_pos
                else {
                    continue;
                };

                let group_idx_byte = *group_idx;
                let inner_len_byte = inner.len() as u8;
                let final_sub_pos = inner_len_byte + 1;

                // Stage 3.12 / Class A.i (2026-05-01): replace the
                // deterministic FIRST-set if/else with a Fork over
                // [TAKE, SKIP] branches. Right-associative dangling-else:
                //   - TAKE branch: weight from_cost(0.0, ..) — preferred when
                //     it succeeds.
                //   - SKIP branch: weight from_cost(EPSILON_OPT_SKIP, ..) —
                //     small floor penalty so SKIP wins only when TAKE fails.
                //   - Tie at primary cost (TAKE-succeeds with following SKIP
                //     vs SKIP-then-TAKE in nested case) breaks via cursor-
                //     allocation order: TAKE first per `vec![take, skip]`.
                //
                // FIRST-set classification is preserved on
                // BinderPosition::OptionalGroup.first_token_set for Display
                // and diagnostic uses; the runtime peek is gone.
                //
                // The unused `first_token_set` variable below silences the
                // dead-code warning while documenting the source of intent.
                let _first_set_for_diagnostics_only: Vec<&str> = first_token_set
                    .iter()
                    .map(|s| s.as_str())
                    .collect();
                arms.push(quote! {
                    (#result_src_idx, #rule_idx, #group_idx_byte, 0u8) => {
                        // Stage 3.12 / Class A.i (2026-05-01): Opt-Group Fork.
                        return WpdsStepAction::Fork {
                            branches: vec![
                                // TAKE branch (push OptionalGroupAt(1) →
                                // walker auto-opens optional scope via
                                // emit_push_side_effects).
                                mettail_prattail::wpds_walker::ForkBranch {
                                    symbol: StackSymbolV2::optional_group_at(
                                        #result_src_idx, #rule_idx, 1u8, *outer_bp,
                                    ),
                                    weight: LexicographicWeight::from_cost(
                                        0.0, #result_src_idx, #rule_idx,
                                    ),
                                    new_state: WpdsState::OptionalGroup {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        group_idx: #group_idx_byte,
                                        sub_pos: 1,
                                        outer_bp: *outer_bp,
                                    },
                                    action_kind: mettail_prattail::wpds_walker::ForkActionKind::Push,
                                },
                                // SKIP branch (mirror OptGroupAbsent: log
                                // PushOptionalAbsent + pop outer RuleAt +
                                // push advanced outer RuleAt).
                                mettail_prattail::wpds_walker::ForkBranch {
                                    // `symbol` is unused for OptGroupAbsent
                                    // action_kind — the cursor-side Fork
                                    // arm uses `replace_symbol` from
                                    // `action_kind`. We supply a stable
                                    // sentinel to satisfy the field.
                                    symbol: StackSymbolV2::category_entry(0),
                                    weight: LexicographicWeight::from_cost(
                                        mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP,
                                        #result_src_idx, #rule_idx,
                                    ),
                                    new_state: WpdsState::BinderRule {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        body_src_idx: #result_src_idx,
                                        outer_bp: *outer_bp,
                                    },
                                    action_kind: mettail_prattail::wpds_walker::ForkActionKind::OptGroupAbsent {
                                        replace_symbol: StackSymbolV2::rule_at(
                                            #result_src_idx, #rule_idx,
                                            #outer_next_pos_byte, Some(*outer_bp),
                                        ),
                                    },
                                },
                            ],
                            consume_trigger: false,
                        };
                    }
                });

                // sub_pos in 1..=inner_len: walk inner positions.
                for (i, ipos) in inner.iter().enumerate() {
                    let sp = (i + 1) as u8;
                    let next_sp = sp + 1;
                    let inner_arm = match ipos {
                        BinderPosition::Literal(text) => quote! {
                            (#result_src_idx, #rule_idx, #group_idx_byte, #sp) => {
                                // Stage 3.20 / L12 Commit F (2026-05-06):
                                // Cluster 1 hack #4 closure (opt-group
                                // inner mirror of site #5).
                                return WpdsStepAction::Fork {
                                    branches: vec![mettail_prattail::wpds_walker::ForkBranch {
                                        symbol: StackSymbolV2::optional_group_at(
                                            #result_src_idx, #rule_idx, #next_sp, *outer_bp,
                                        ),
                                        weight: LexicographicWeight::one(),
                                        new_state: WpdsState::OptionalGroup {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            group_idx: #group_idx_byte,
                                            sub_pos: #next_sp,
                                            outer_bp: *outer_bp,
                                        },
                                        action_kind:
                                            mettail_prattail::wpds_walker::ForkActionKind::GuardedConsumeAndReplace {
                                                expected_text: #text.to_string(),
                                            },
                                    }],
                                    consume_trigger: false,
                                };
                            }
                        },
                        BinderPosition::ParamParse { cat, collection: _ } => {
                            // B9: SimpleCollection inside Optional is rejected
                            // by classify_binder's optional-group walker, so
                            // `collection` is always None at this site.
                            let cat_src_idx = lookup_src_idx(cat, categories).unwrap_or(0);
                            quote! {
                                (#result_src_idx, #rule_idx, #group_idx_byte, #sp) => {
                                    return WpdsStepAction::ReplaceAndPush {
                                        replace_symbol: StackSymbolV2::optional_group_at(
                                            #result_src_idx, #rule_idx, #next_sp, *outer_bp,
                                        ),
                                        push_symbol: StackSymbolV2::category_entry(#cat_src_idx),
                                        weight: LexicographicWeight::one(),
                                        new_state: WpdsState::PrefixDispatch {
                                            pos: _pos,
                                            // Stage 3.27d (G-PREFIX-BP, 2026-04-30):
                                            // opt-group inner ParamParse always uses
                                            // cur_bp:0 because the outer rule's shape
                                            // (`[Literal, Optional, ...]`) cannot match
                                            // the unary-prefix predicate (which requires
                                            // `[Literal, Param]` positions.len()==2).
                                            // `prefix_bp_map` is plumbed through for
                                            // symmetry; lookup will always miss here.
                                            cur_bp: 0u8,
                                        },
                                    };
                                }
                            }
                        }
                        BinderPosition::BinderIdent => quote! {
                            (#result_src_idx, #rule_idx, #group_idx_byte, #sp) => {
                                // Stage 3.20 / L12 Commit F (2026-05-06):
                                // Cluster 1 4th hack closure (opt-group
                                // inner mirror of site #6).
                                return WpdsStepAction::Fork {
                                    branches: vec![mettail_prattail::wpds_walker::ForkBranch {
                                        symbol: StackSymbolV2::optional_group_at(
                                            #result_src_idx, #rule_idx, #next_sp, *outer_bp,
                                        ),
                                        weight: LexicographicWeight::one(),
                                        new_state: WpdsState::OptionalGroup {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            group_idx: #group_idx_byte,
                                            sub_pos: #next_sp,
                                            outer_bp: *outer_bp,
                                        },
                                        action_kind:
                                            mettail_prattail::wpds_walker::ForkActionKind::GuardedConsumeIdentAndReplace {
                                                start_scope: true,
                                            },
                                    }],
                                    consume_trigger: false,
                                };
                            }
                        },
                        BinderPosition::GuardSlot => quote! {
                            (#result_src_idx, #rule_idx, #group_idx_byte, #sp) => {
                                return WpdsStepAction::ParsePredicate {
                                    replace_symbol: StackSymbolV2::optional_group_at(
                                        #result_src_idx, #rule_idx, #next_sp, *outer_bp,
                                    ),
                                    weight: LexicographicWeight::one(),
                                    new_state: WpdsState::OptionalGroup {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        group_idx: #group_idx_byte,
                                        sub_pos: #next_sp,
                                        outer_bp: *outer_bp,
                                    },
                                };
                            }
                        },
                        BinderPosition::OptionalGroup { .. }
                        | BinderPosition::BinderListLoop { .. } => {
                            // Nested Optional / BinderListLoop inside Optional
                            // are out of pilot scope. Emit no arm so the
                            // catch-all `_` returns Idle, which causes the
                            // walker's saturation loop to surface the bug.
                            quote! {}
                        }
                    };
                    arms.push(inner_arm);
                }

                // sub_pos == final_sub_pos: finalize.
                arms.push(quote! {
                    (#result_src_idx, #rule_idx, #group_idx_byte, #final_sub_pos) => {
                        return WpdsStepAction::OptGroupFinalize {
                            replace_symbol: StackSymbolV2::rule_at(
                                #result_src_idx, #rule_idx,
                                #outer_next_pos_byte, Some(*outer_bp),
                            ),
                            weight: LexicographicWeight::one(),
                            new_state: WpdsState::BinderRule {
                                result_src_idx: #result_src_idx,
                                rule_idx: #rule_idx,
                                body_src_idx: #result_src_idx,
                                outer_bp: *outer_bp,
                            },
                        };
                    }
                });
            }
        }
    }

    if arms.is_empty() {
        return quote! { WpdsStepAction::Idle };
    }
    quote! {
        {
            match (*result_src_idx, *rule_idx, *group_idx, *sub_pos) {
                #(#arms)*
                _ => WpdsStepAction::Idle,
            }
        }
    }
}

/// Phase 5: emit the action_for arm for a multi-step rule.
pub(crate) fn emit_binder_action_entry(
    src_idx: u16,
    rule_idx: u16,
    shape: &BinderShape,
    cat_ident: &Ident,
    categories: &[String],
) -> Option<TokenStream> {
    let label_ident = format_ident!("{}", shape.label);
    let arity = shape.action_arity;
    // B13c / Candidate H (2026-05-08): per-arg expected categories for
    // binder rules. Most binder slots are non-Term (BinderName, BinderList,
    // Predicate, Optional) → ANY_CAT sentinel. Only `Term(cat)` slots have
    // a real category index. Output is shape.result_cat (the home cat,
    // since binder rules belong to one category at construction).
    let lookup_cat_idx = |name: &str| -> u16 {
        categories
            .iter()
            .position(|c| c == name)
            .map(|i| i as u16)
            .unwrap_or(0)
    };
    let result_cat_idx = lookup_cat_idx(&shape.result_cat);
    // ANY_CAT = u16::MAX; matches mettail_prattail::wpds_runtime::ANY_CAT
    // (this is in macros code so we can't reference the runtime constant
    // by path; we emit `&[ANY_CAT]` literally in the generated code).
    let any_cat_value: u16 = u16::MAX;
    let expected_input_cats: Vec<u16> = shape
        .action_args
        .iter()
        .map(|kind| match kind {
            ActionArgKind::Term(cat) => lookup_cat_idx(cat),
            _ => any_cat_value,
        })
        .collect();
    let cats_lits: Vec<TokenStream> = expected_input_cats
        .iter()
        .map(|c| {
            let c = *c;
            quote! { #c }
        })
        .collect();
    let expected_input_cats_ts = quote! { &[#(#cats_lits),*] };

    // Generate the per-arg extraction code in push order.
    let mut extracts: Vec<TokenStream> = Vec::new();
    let mut field_names: Vec<TokenStream> = Vec::new();
    let mut binder_name_holders: Vec<Ident> = Vec::new();
    let mut body_holder: Option<Ident> = None;
    let mut binder_list_holder: Option<Ident> = None;

    for (i, kind) in shape.action_args.iter().enumerate() {
        let var = format_ident!("arg_{}", i);
        match kind {
            ActionArgKind::BinderName => {
                extracts.push(quote! {
                    let #var = match iter.next() {
                        Some(mettail_prattail::wpds_runtime::ActionArg::Ident { name, .. }) => name,
                        _ => return,
                    };
                });
                binder_name_holders.push(var.clone());
            }
            ActionArgKind::Term(cat) => {
                let cat_id = format_ident!("{}", cat);
                extracts.push(quote! {
                    let #var = match iter.next().and_then(|a| a.into_term::<#cat_id>()) {
                        Some(t) => t,
                        None => return,
                    };
                });
                if shape.has_binder
                    && shape.body_cat.as_deref() == Some(cat.as_str())
                    && body_holder.is_none()
                {
                    body_holder = Some(var.clone());
                } else {
                    field_names.push(quote! { Box::new(#var) });
                }
            }
            ActionArgKind::Predicate => {
                extracts.push(quote! {
                    let #var = match iter.next().and_then(|a| a.into_predicate::<mettail_runtime::BehavioralPred>()) {
                        Some(p) => p,
                        None => return,
                    };
                });
                field_names.push(quote! { #var });
            }
            ActionArgKind::BinderList => {
                extracts.push(quote! {
                    let #var = match iter.next() {
                        Some(mettail_prattail::wpds_runtime::ActionArg::BinderScope(h)) => h.names,
                        _ => return,
                    };
                });
                binder_list_holder = Some(var.clone());
            }
            ActionArgKind::CollectionDrain { elem_cat, coll_kind } => {
                // B9 / Class 2 (2026-05-08): drain the cursor's collection
                // accumulator. The CollectionMarker push at the binder rule's
                // ParamParse{collection: Some(...)} dispatch pushed an
                // ActionArg::CollectionId(id); now we consume it, drain the
                // accumulator, materialize a container of `coll_kind`, and
                // emit the bare value (no Box::new wrapping — the AST
                // variant takes a bare container per language!-macro
                // codegen convention).
                let elem_id = format_ident!("{}", elem_cat);
                let materialize_body = match coll_kind {
                    CollectionType::Vec => quote! {
                        let elems: std::vec::Vec<#elem_id> = drained
                            .into_iter()
                            .filter_map(|a| a.into_term::<#elem_id>())
                            .collect();
                        let #var = elems;
                    },
                    CollectionType::HashBag => quote! {
                        let #var = mettail_runtime::HashBag::<#elem_id>::from_iter(
                            drained
                                .into_iter()
                                .filter_map(|a| a.into_term::<#elem_id>())
                        );
                    },
                    CollectionType::HashSet => quote! {
                        let #var = std::collections::HashSet::<#elem_id>::from_iter(
                            drained
                                .into_iter()
                                .filter_map(|a| a.into_term::<#elem_id>())
                        );
                    },
                    CollectionType::HashMap => quote! {
                        // HashMap collection in Class-2 binder rules is out
                        // of pilot scope (rejected at classify_binder).
                        // Defensive: emit a panic if reached.
                        let #var = panic!("B9 pilot: HashMap collection in Class-2 binder rule unsupported");
                    },
                };
                extracts.push(quote! {
                    let id = match iter.next().and_then(|a| a.as_collection_id()) {
                        Some(i) => i,
                        None => return,
                    };
                    let drained = b.drain_collection(id);
                    #materialize_body
                });
                // Bare value — no Box::new wrapping (the AST variant takes
                // bare Vec<T> / HashBag<T> / HashSet<T> per language! macro
                // convention).
                field_names.push(quote! { #var });
            }
            ActionArgKind::Optional(inner_kinds) => {
                // Opt-Group: extract the Optional arg, exposing each inner
                // field as `Option<Box<T>>` (or Option<...> per inner kind).
                // The runtime pushes ActionArg::Optional(Some(inner_args))
                // when taken, Optional(None) when skipped. Inner args are
                // ordered identically to inner_kinds (matches enums.rs's
                // flat field emission).
                let opt_var = format_ident!("opt_{}", i);
                let mut inner_ext: Vec<TokenStream> = Vec::new();
                let mut inner_idents: Vec<Ident> = Vec::new();
                for (j, k) in inner_kinds.iter().enumerate() {
                    let inner_var = format_ident!("inner_{}_{}", i, j);
                    inner_idents.push(inner_var.clone());
                    let extract_inner = match k {
                        ActionArgKind::Term(cat) => {
                            let cat_id = format_ident!("{}", cat);
                            quote! {
                                let #inner_var: Option<Box<#cat_id>> =
                                    match #opt_var.as_mut() {
                                        Some(inner_iter) => inner_iter.next()
                                            .and_then(|a| a.into_term::<#cat_id>())
                                            .map(Box::new),
                                        None => None,
                                    };
                            }
                        }
                        ActionArgKind::BinderName => quote! {
                            let #inner_var: Option<String> =
                                match #opt_var.as_mut() {
                                    Some(inner_iter) => match inner_iter.next() {
                                        Some(mettail_prattail::wpds_runtime::ActionArg::Ident { name, .. }) => Some(name),
                                        _ => None,
                                    },
                                    None => None,
                                };
                        },
                        ActionArgKind::Predicate => quote! {
                            let #inner_var: Option<mettail_runtime::BehavioralPred> =
                                match #opt_var.as_mut() {
                                    Some(inner_iter) => inner_iter.next()
                                        .and_then(|a| a.into_predicate::<mettail_runtime::BehavioralPred>()),
                                    None => None,
                                };
                        },
                        ActionArgKind::BinderList => quote! {
                            let #inner_var: Option<Vec<String>> =
                                match #opt_var.as_mut() {
                                    Some(inner_iter) => match inner_iter.next() {
                                        Some(mettail_prattail::wpds_runtime::ActionArg::BinderScope(h)) => Some(h.names),
                                        _ => None,
                                    },
                                    None => None,
                                };
                        },
                        ActionArgKind::Optional(_) => quote! {
                            // Nested Optional: pilot scope omits this — the
                            // inner is consumed-and-dropped but doesn't
                            // contribute a field. classify_binder rejects
                            // nested Optional today, so this arm is
                            // unreachable. If the rejection lifts, extract
                            // the nested ActionArg::Optional and recursively
                            // unwrap.
                            let #inner_var: () = ();
                        },
                        ActionArgKind::CollectionDrain { .. } => quote! {
                            // B9 / Class 2 (2026-05-08): SimpleCollection
                            // inside Optional is rejected by classify_binder
                            // (out of pilot scope), so this arm is
                            // unreachable. Defensive `()` placeholder.
                            let #inner_var: () = ();
                        },
                    };
                    inner_ext.push(extract_inner);
                }
                extracts.push(quote! {
                    let mut #opt_var: Option<std::vec::IntoIter<mettail_prattail::wpds_runtime::ActionArg>> =
                        match iter.next() {
                            Some(arg) => arg.into_optional()
                                .flatten()
                                .map(|v| v.into_iter()),
                            _ => return,
                        };
                    #(#inner_ext)*
                });
                for ident in inner_idents {
                    field_names.push(quote! { #ident });
                }
            }
        }
    }

    // Build the action body's construction expression based on rule shape.
    // For binder rules with auxiliary fields (e.g. PGuardedInput's
    // `(Name, BehavioralPred, Scope<...>)`), the AST variant takes the
    // auxiliary fields first, then the Scope. We emit the call as
    // `Cat::Label(field_names..., scope)` — field_names comes from
    // non-binder, non-body Term args + Predicate args in encounter order.
    let construct = if shape.has_binder && shape.is_multi {
        // Multi-binder: Scope<Vec<Binder>, Box<Body>>.
        let binder_list = binder_list_holder.expect("multi-binder shape must have binder list");
        let body = body_holder.expect("multi-binder shape must have body");
        quote! {
            let binders: Vec<mettail_runtime::Binder<String>> = #binder_list
                .iter()
                .map(|n| mettail_runtime::Binder(mettail_runtime::get_or_create_var(n.clone())))
                .collect();
            let scope = mettail_runtime::Scope::new(binders, Box::new(#body));
            b.push_term::<#cat_ident>(
                #cat_ident::#label_ident(#(#field_names,)* scope)
            );
        }
    } else if shape.has_binder {
        // Single-binder: Scope<Binder, Box<Body>>.
        let binder_name = binder_name_holders
            .first()
            .expect("single-binder shape must have one binder name");
        let body = body_holder.expect("single-binder shape must have body");
        quote! {
            b.pop_binder_scope_silent();
            let scope = mettail_runtime::Scope::new(
                mettail_runtime::Binder(mettail_runtime::get_or_create_var(#binder_name)),
                Box::new(#body),
            );
            b.push_term::<#cat_ident>(
                #cat_ident::#label_ident(#(#field_names,)* scope)
            );
        }
    } else {
        // Multi-Param non-binder: Cat::Label(Box::new(arg_0), Box::new(arg_1), ...).
        quote! {
            b.push_term::<#cat_ident>(
                #cat_ident::#label_ident(#(#field_names),*)
            );
        }
    };

    let action_fn = quote! {
        |b: &mut mettail_prattail::wpds_runtime::SemanticBuilder,
         args: Vec<mettail_prattail::wpds_runtime::ActionArg>| {
            let mut iter = args.into_iter();
            #(#extracts)*
            #construct
        }
    };
    Some(quote! {
        (#src_idx, #rule_idx) => {
            static ENTRY: mettail_prattail::wpds_runtime::ActionEntry =
                mettail_prattail::wpds_runtime::ActionEntry {
                    action_fn: #action_fn,
                    arity: #arity,
                    expected_input_cats: #expected_input_cats_ts,
                    output_cat: #result_cat_idx,
                };
            Some(&ENTRY)
        }
        ,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::GrammarRule;
    use proc_macro2::Span;
    use syn::Ident;

    fn lambda_lam_rule() -> GrammarRule {
        GrammarRule {
            label: Ident::new("Lam", Span::call_site()),
            category: Ident::new("Term", Span::call_site()),
            items: Vec::new(),
            bindings: Vec::new(),
            term_context: Some(vec![TermParam::Abstraction {
                binder: Ident::new("x", Span::call_site()),
                body: Ident::new("body", Span::call_site()),
                ty: TypeExpr::Arrow {
                    domain: Box::new(TypeExpr::Base(Ident::new("Term", Span::call_site()))),
                    codomain: Box::new(TypeExpr::Base(Ident::new("Term", Span::call_site()))),
                },
            }]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("lam ".into()),
                SyntaxExpr::Param(Ident::new("x", Span::call_site())),
                SyntaxExpr::Literal(".".into()),
                SyntaxExpr::Param(Ident::new("body", Span::call_site())),
            ]),
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
        }
    }

    fn fraction_rule() -> GrammarRule {
        GrammarRule {
            label: Ident::new("Fraction", Span::call_site()),
            category: Ident::new("BigRat", Span::call_site()),
            items: Vec::new(),
            bindings: Vec::new(),
            term_context: Some(vec![
                TermParam::Simple {
                    name: Ident::new("a", Span::call_site()),
                    ty: TypeExpr::Base(Ident::new("BigInt", Span::call_site())),
                },
                TermParam::Simple {
                    name: Ident::new("b", Span::call_site()),
                    ty: TypeExpr::Base(Ident::new("BigInt", Span::call_site())),
                },
            ]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("fraction".into()),
                SyntaxExpr::Literal("(".into()),
                SyntaxExpr::Param(Ident::new("a", Span::call_site())),
                SyntaxExpr::Literal(",".into()),
                SyntaxExpr::Param(Ident::new("b", Span::call_site())),
                SyntaxExpr::Literal(")".into()),
            ]),
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
            is_auto_injected: false,
            doc_comment: None,
        }
    }

    #[test]
    fn classifies_lambda_lam_rule() {
        let shape = classify_binder(&lambda_lam_rule()).expect("Lam should classify");
        assert_eq!(shape.label, "Lam");
        assert!(!shape.is_multi);
        assert!(shape.has_binder);
        assert_eq!(shape.action_arity, 2);
    }

    #[test]
    fn classifies_fraction_multi_param_rule() {
        let shape = classify_binder(&fraction_rule()).expect("Fraction should classify");
        assert_eq!(shape.label, "Fraction");
        assert!(!shape.is_multi);
        assert!(!shape.has_binder);
        assert_eq!(shape.action_arity, 2);
        assert_eq!(shape.param_cats, vec!["BigInt", "BigInt"]);
    }

    #[test]
    fn emits_binder_prefix_arm_for_lambda() {
        let categories = vec!["Term".to_string()];
        let per_cat = vec![vec![lambda_lam_rule()]];
        let language = synthetic_lang_for_lambda_test();
        let ts = emit_binder_prefix_arms(&language, &categories, &per_cat);
        let s = ts.to_string();
        assert!(s.contains("ConsumeAndPush"));
        assert!(s.contains("BinderRule"));
        assert!(s.contains("\"lam \""));
    }

    fn synthetic_lang_for_lambda_test() -> mettail_ast::language::LanguageDef {
        use mettail_ast::language::LangType;
        let mut lang = mettail_ast::language::LanguageDef {
            name: Ident::new("Toy", proc_macro2::Span::call_site()),
            options: Default::default(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: Vec::new(),
            refinement_types: Vec::new(),
            token_defs: Vec::new(),
            mode_defs: Vec::new(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms: vec![lambda_lam_rule()],
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        };
        lang.types.push(LangType {
            name: Ident::new("Term", proc_macro2::Span::call_site()),
            native_type: None,
            collection_kind: None,
        });
        lang
    }

    #[test]
    fn emits_binder_rule_body_for_lambda() {
        let categories = vec!["Term".to_string()];
        let per_cat = vec![vec![lambda_lam_rule()]];
        let prefix_bp_map = std::collections::HashMap::new();
        let ts = emit_binder_rule_body(&categories, &per_cat, &prefix_bp_map);
        let s = ts.to_string();
        assert!(s.contains("ConsumeIdentAndReplace"));
        assert!(s.contains("ConsumeAndReplace"));
        assert!(s.contains("\".\""));
    }

    #[test]
    fn emits_binder_rule_body_for_fraction() {
        let categories = vec!["BigInt".to_string(), "BigRat".to_string()];
        let per_cat = vec![Vec::new(), vec![fraction_rule()]];
        let prefix_bp_map = std::collections::HashMap::new();
        let ts = emit_binder_rule_body(&categories, &per_cat, &prefix_bp_map);
        let s = ts.to_string();
        // "fraction" is the trigger consumed at open; positions 1+ are
        // "(", a (ParamParse), ",", b (ParamParse), ")". Verify the
        // emitted code contains ReplaceAndPush (for ParamParse slots) and
        // the literals.
        assert!(s.contains("ReplaceAndPush"));
        assert!(s.contains("\"(\""));
        assert!(s.contains("\")\""));
        assert!(s.contains("\",\""));
    }
}
