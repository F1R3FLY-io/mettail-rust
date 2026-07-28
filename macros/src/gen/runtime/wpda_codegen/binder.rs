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
//! - **Multi-binder list** (Phase 5b, e.g. Rholang's `PNew`):
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
use super::collection::kv_sep_for;

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
            // NOTE (measured 2026-07-24, official-Rholang `new` alignment):
            // an explicit `prefix(N)` is NOT honoured for binder rules, and
            // wiring it in here does not give a binder rule's trailing
            // same-category `ParamParse` a Pratt `min_bp` floor. A trailing
            // OPEN-ENDED body (`… "in" p` with no closing delimiter) stops at
            // the FIRST infix operator regardless of the emitted `cur_bp` —
            // `new x in 1 + 2` realizes `(new x in 1) + 2` at `cur_bp` 0 AND
            // at `cur_bp` 3 alike. Reproducing official Rholang's `Proc1`-level
            // body therefore needs real work in the walker's trailing-operand
            // path, not a binding-power annotation; see the campaign's §17.10-B1
            // for the scoped follow-up. Rholang's `PNew` consequently keeps a
            // DELIMITED body (`… "in" "{" p "}"`), which needs no floor.
            if classify_unary_prefix_shape(rule).is_some() {
                let bp = compute_prefix_bp(&rule.category.to_string(), rule.prefix_bp, &bp_table);
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
    pub label: String,
    /// Result category name (e.g., `"Term"`, `"BigRat"`, `"Proc"`).
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
    pub body_cat: Option<String>,
    /// Param categories in declaration order (for non-binder Simple params).
    // dead_code: populated by production codegen but only read by the `#[cfg(test)]` shape assertions.
    #[cfg_attr(not(test), allow(dead_code))]
    pub param_cats: Vec<String>,
}

/// A single position in a multi-step rule's syntax pattern.
#[derive(Debug, Clone)]
pub enum BinderPosition {
    /// `Literal("text")` — consume + advance position.
    Literal(String),
    /// L9-3: `w@Word` — consume ONE token of the custom KIND `kind_name`
    /// (a single-branch Fork carrying `GuardedConsumeTokenKindAndReplace`,
    /// structural clone of the `Literal` position), binding its text as the
    /// `param_name` action arg (`ActionArgKind::TokenText`). No binder scope.
    TokenKindCapture { kind_name: String, param_name: String },
    /// An `m:Ident` param — consume ONE builtin `Token::Ident` and bind its TEXT as the
    /// `param_name` action arg ([`ActionArgKind::IdentText`]). No binder scope, no new
    /// token kind, no lexical co-accept.
    ///
    /// Emits the EXISTING walker op `ForkActionKind::ConsumeIdentAndReplace {
    /// start_scope: false }` (`prattail/src/wpda_walker.rs:2612`), which interns the token
    /// as an `ActionArg::Ident`; the action body reads it back through the existing
    /// `ActionArg::as_ident()` (`prattail/src/wpda_runtime.rs:2821`). Because both halves
    /// already existed, giving `Ident` a mid-rule surface required ZERO prattail change.
    ///
    /// Structural twin of [`Self::TokenKindCapture`], and deliberately NOT
    /// [`Self::BinderIdent`]: a binder ident opens a scope, which is precisely the
    /// semantics an inert identifier field must not have.
    IdentTextCapture { param_name: String },
    /// L9-4: `*flt(node, open, close)` — consume a whole guest region (opener →
    /// GuestChunk/Hole run → closer) in one action (`ConsumeGuestBodyAndReplace`
    /// mid-rule / `ConsumeGuestBodyAndPush` leading), binding the assembled
    /// `Arc<FltNode>` as the `param_name` action arg (`ActionArgKind::GuestBody`).
    GuestBodyCapture {
        open_kind: String,
        close_kind: String,
        param_name: String,
    },
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
    /// rholang PInputs `*zip(ns,xs).*map(|n,x| n "?" x).*sep(",")`).
    /// `inner_positions` is the per-iteration inner walk; for PNew-style
    /// rules it's `[BinderIdent]`.
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
        /// For Class 3 rules: the element category of the synthesized
        /// names accumulator. None for PNew-style rules.
        collection_param_cat: Option<String>,
        /// Phase 3 Redesign B (2026-05-11): whether empty-binder-list is
        /// permitted at parse time. `true` for multi-binder PNew-style
        /// rules (`^[xs].body` — zero or more idents are valid) and
        /// Class 3 (the collection itself may be empty). `false` for
        /// single-binder collapsed shapes (`^x.body` — exactly one
        /// ident required).
        ///
        /// Default for existing construction sites: `true` (preserves
        /// pre-Phase-3 behavior). Single-binder collapse (sub-commit
        /// 3.B.3) will construct with `false`.
        allow_empty: bool,
        /// Phase 3 Redesign B (2026-05-11): whether more-than-one ident
        /// is permitted. `true` for multi-binder and Class 3. `false`
        /// for single-binder collapsed shapes (exactly one ident).
        ///
        /// Default: `true`. Single-binder collapse will construct with
        /// `false`.
        allow_multi: bool,
        /// Phase 4 #2 (2026-05-12): rule-global collection-slot index
        /// for the synthesized names accumulator (Class-3 ZIP-MAP-SEP
        /// only — `collection_param_cat: Some(_)`). Encoded at the
        /// CollectionMarker symbol's `bp` field at push time so the
        /// walker's per-(src, rule, slot_idx) lookup
        /// `is_class3_collection_per_slot` correctly distinguishes the
        /// Class-3 slot from sibling Class-2 slots in the same rule
        /// (e.g. PInputsTagged: ns:Vec(Name) — slot 0 (Class-3) +
        /// tags:Vec(Proc) — slot 1 (Class-2)).
        ///
        /// For non-Class-3 BinderListLoop variants (PNew-style and
        /// single-binder collapse): `slot_idx == 0` and the field is
        /// informational only — no names accumulator is allocated, no
        /// CollectionMarker carries this slot_idx.
        slot_idx: u8,
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
    /// `WpdaState::OptionalGroup { sub_pos: 0 }`; on entry it peeks
    /// the FIRST-set of `inner_positions[0]` to decide whether to take
    /// the group (push inner args + advance into group) or skip (push
    /// `ActionArg::Optional(None)` + advance past group). The
    /// `first_token_set` is a list of literal-text predicates that
    /// trigger entry into the group (computed at codegen from the
    /// inner positions' types).
    OptionalGroup {
        positions: Vec<BinderPosition>,
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
    pub elem_cat: String,
    /// Phase 4 #5b (2026-05-12): inter-pair separator for HashMap
    /// collections (e.g., `":"` for `k: v`). `None` for Vec/HashBag/
    /// HashSet. The walker's `CollectionLoop` uses this to dispatch
    /// key/value parsing phases while preserving the drained
    /// `[k0, v0, k1, v1, ...]` invariant.
    pub key_val_separator: Option<String>,
    /// Phase 4 #1 (2026-05-11): rule-global slot index. 0-based dense
    /// index over collection slots in `shape.positions` order. Encoded
    /// at the `CollectionMarker` symbol's `bp` field at push time so
    /// the walker's per-CollectionMarker close/sep/element-src
    /// lookups can disambiguate sibling slots within the same rule.
    /// `accumulator_id` (runtime stack-relative slot id) is recovered
    /// from `cursor.collection_stack.len() - 1` at push time. For
    /// single-slot rules, `slot_idx == 0` and behavior is unchanged
    /// (the slot_idx vs accumulator_id coincide).
    pub slot_idx: u8,
}

/// What kind of arg the action body extracts at each position (in push order).
#[derive(Debug, Clone)]
pub enum ActionArgKind {
    /// `ActionArg::Ident { name }` — single binder name.
    BinderName,
    /// L9-3: `ActionArg::Token { text, .. }` — a captured custom-kind token's
    /// text, extracted via `as_token_text()` (the proven native-literal path)
    /// and bound as a `String` action arg / AST field.
    TokenText { param_name: String },
    /// `ActionArg::Ident { name }` — the TEXT of one consumed builtin `Token::Ident`,
    /// extracted via `as_ident()` and bound as a `String` action arg / AST field.
    ///
    /// The builtin-kind twin of [`Self::TokenText`]: same `String` destination, different
    /// source token class. `TokenText` reads a DECLARED `tokens { }` kind
    /// (`ActionArg::Token`, pushed by `GuardedConsumeTokenKindAndReplace`); this reads the
    /// generic `Ident` (`ActionArg::Ident`, pushed by `ConsumeIdentAndReplace`). Keeping
    /// them distinct is what lets an `Ident`-typed param avoid declaring a new token kind
    /// — measured to move Rholang's multi-accept DFA states 0.8 % → 79.8 % and parse time
    /// geomean ×2.49 — while still landing an inert `String` in the AST.
    IdentText { param_name: String },
    /// L9-4: `ActionArg::GuestBody(GuestBodyData)` — an assembled FLT guest
    /// body, extracted via `as_guest_body()` and lowered to an
    /// `Arc<mettail_runtime::FltNode>` action arg / AST field.
    GuestBody { param_name: String },
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
pub(crate) fn classify_binder_in(
    rule: &GrammarRule,
    language: &LanguageDef,
) -> Option<BinderShape> {
    let tc = rule.term_context.as_ref()?;
    let sp = rule.syntax_pattern.as_ref()?;
    if sp.is_empty() {
        return None;
    }
    // Stage 3 (2026-06-27): the declared collection delimiters for THIS rule's
    // result category, if it is declared as a collection category (`as List`/
    // `Bag`/`Map`/`Set`/`Pathmap`). For binder rules — whose category is a host
    // category like `Proc`/`Name`, never a declared collection — this resolves to
    // `None`, so the kv-separator resolver falls to the per-type default
    // (`HashMap` ⇒ `":"`), byte-identical to the former hardcode. It is threaded
    // through `language` so the inline-binder kv-source reads through the SAME
    // `kv_sep_for` resolver as the declared-category and lexer-terminal sources.
    let declared_delims = language
        .types
        .iter()
        .find(|t| t.name == rule.category)
        .and_then(|t| t.collection_kind.as_ref())
        .map(|c| c.delimiters());
    // Position 0 must be a Literal trigger — OR (L9-3) a LEADING custom-kind
    // capture (`b@GuestChunk …`) / (L9-4) a LEADING guest body (`*flt(node,…)`),
    // whose consume is emitted by the prefix dispatch
    // (UnifiedDescriptor::LeadingTokenKindCapture / LeadingGuestBody). The
    // `.skip(1)` position loop below treats sp[0] as the trigger either way, so
    // positions start at slot 1 (= sp[1]). Otherwise it's an infix/prefix Pratt
    // rule handled by Phase 3.
    if !matches!(
        &sp[0],
        SyntaxExpr::Literal(_) | SyntaxExpr::TokenKind { .. } | SyntaxExpr::GuestBody { .. }
    ) {
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
        if let TermParam::Simple { ty: TypeExpr::Collection { .. }, .. } = &tc[0] {
            let class5_shape_3 = sp.len() == 3
                && matches!(&sp[0], SyntaxExpr::Literal(_))
                && matches!(&sp[1], SyntaxExpr::Op(PatternOp::Sep { source: None, .. }))
                && matches!(&sp[2], SyntaxExpr::Literal(_));
            let class5_shape_4 = sp.len() == 4
                && matches!(&sp[0], SyntaxExpr::Literal(_))
                && matches!(&sp[1], SyntaxExpr::Literal(s) if s == "(")
                && matches!(&sp[2], SyntaxExpr::Op(PatternOp::Sep { source: None, .. }))
                && matches!(&sp[3], SyntaxExpr::Literal(_));
            if class5_shape_3 || class5_shape_4 {
                return None;
            }
        }
    }

    // Build a map: param name → (kind, type_info).
    enum ParamKind {
        Simple {
            cat: String,
        },
        Binder,
        BinderList,
        Body {
            cat: String,
        },
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
    let mut optional_params: std::collections::HashSet<String> = std::collections::HashSet::new();

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
                    TermParam::Optional { .. } => {},
                }
            }
            match p {
                TermParam::Simple { name, ty } => match ty {
                    TypeExpr::Base(ident) => {
                        let cat = ident.to_string();
                        param_cats.push(cat.clone());
                        param_map.insert(name.to_string(), ParamKind::Simple { cat });
                    },
                    // B9 / Class 2 (2026-05-08): SimpleCollection. Supports
                    // Vec / HashBag / HashSet / HashMap over a Base element
                    // type. HashMap uses the grammar's key/value separator
                    // while preserving the drained `[k0, v0, k1, v1, ...]`
                    // invariant.
                    TypeExpr::Collection { coll_type, element } => {
                        match (coll_type, element.as_ref()) {
                            (CollectionType::Vec, TypeExpr::Base(elem))
                            | (CollectionType::HashBag, TypeExpr::Base(elem))
                            | (CollectionType::HashSet, TypeExpr::Base(elem))
                            | (CollectionType::HashMap, TypeExpr::Base(elem)) => {
                                let elem_cat = elem.to_string();
                                param_cats.push(elem_cat.clone());
                                param_map.insert(
                                    name.to_string(),
                                    ParamKind::SimpleCollection {
                                        elem_cat,
                                        coll_kind: coll_type.clone(),
                                    },
                                );
                            },
                            _ => return None,
                        }
                    },
                    // Phase 4 #5b (2026-05-12): HashMap(K, V) — the
                    // parser produces `TypeExpr::Map { key, value }`
                    // rather than `Collection { coll_type: HashMap, ... }`.
                    // Lower to SimpleCollection with `coll_kind: HashMap`
                    // when both K and V are `Base(_)` and equal (mirror
                    // Class-5's same-element-cat assumption for the
                    // empty-drain materialization invariant `[k0, v0,
                    // k1, v1, ...]`).
                    TypeExpr::Map { key, value } => match (key.as_ref(), value.as_ref()) {
                        (TypeExpr::Base(k_ident), TypeExpr::Base(v_ident))
                            if k_ident == v_ident =>
                        {
                            let elem_cat = k_ident.to_string();
                            param_cats.push(elem_cat.clone());
                            param_map.insert(
                                name.to_string(),
                                ParamKind::SimpleCollection {
                                    elem_cat,
                                    coll_kind: CollectionType::HashMap,
                                },
                            );
                        },
                        _ => return None,
                    },
                    _ => return None,
                },
                TermParam::Abstraction { binder, body, ty } => {
                    let bcat = arrow_codomain_name(ty)?;
                    *body_cat = Some(bcat.clone());
                    *has_binder = true;
                    param_map.insert(binder.to_string(), ParamKind::Binder);
                    param_map.insert(body.to_string(), ParamKind::Body { cat: bcat });
                    if in_optional {
                        optional_params.insert(body.to_string());
                    }
                },
                TermParam::MultiAbstraction { binder, body, ty } => {
                    let bcat = arrow_codomain_name(ty)?;
                    *body_cat = Some(bcat.clone());
                    *has_binder = true;
                    *is_multi = true;
                    param_map.insert(binder.to_string(), ParamKind::BinderList);
                    param_map.insert(body.to_string(), ParamKind::Body { cat: bcat });
                    if in_optional {
                        optional_params.insert(body.to_string());
                    }
                },
                TermParam::GuardBody { name } => {
                    param_map.insert(name.to_string(), ParamKind::Guard);
                },
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
                },
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
    // pos+1 Literal arm), causing rholang::PNew parses to fail with
    // "expected '<close>' but found '<next>'" at every dispatch.
    // `skip_next` tracks this and skips the close Literal at the next
    // iteration.
    let mut positions = Vec::new();
    let mut action_args = Vec::new();
    // L9-3: a LEADING custom-kind capture (sp[0] is a TokenKind) is consumed by
    // the prefix dispatch, which interns its ActionArg::Token FIRST. The
    // `.skip(1)` loop treats sp[0] as the trigger and does not re-push it, so
    // PREPEND its TokenText arg here — action_args = [leading, …positions]
    // matches the runtime intern order (else the action arity is off by one).
    if let SyntaxExpr::TokenKind { name, bind } = &sp[0] {
        let param_name = bind
            .as_ref()
            .map(|b| b.to_string())
            .unwrap_or_else(|| format!("__tok_{}", name));
        action_args.push(ActionArgKind::TokenText { param_name });
    }
    // L9-4: a LEADING guest body (sp[0] is `*flt(node,…)`) is consumed by the
    // prefix dispatch, which interns its ActionArg::GuestBody FIRST — prepend
    // its arg here (same off-by-one reasoning as the leading token capture).
    if let SyntaxExpr::GuestBody { bind, .. } = &sp[0] {
        action_args.push(ActionArgKind::GuestBody { param_name: bind.to_string() });
    }
    let mut skip_next: bool = false;
    // Phase 4 #1.B (2026-05-11): track collection-slot index. Each
    // SimpleCollection / Class-3 BinderListLoop push increments.
    // Stamped into `CollectionSepInfo.slot_idx` / (eventually) the
    // CollectionMarker symbol's `bp` field via emit_binder_rule_body
    // so the walker's per-CollectionMarker lookups can disambiguate
    // sibling slots within the same rule.
    let mut collection_slots_so_far: u8 = 0;
    for (i, item) in sp.iter().enumerate().skip(1) {
        if skip_next {
            skip_next = false;
            continue;
        }
        match item {
            SyntaxExpr::Literal(text) => {
                positions.push(BinderPosition::Literal(text.clone()));
            },
            // L9-3: a `w@Word` custom-kind capture — push a TokenKindCapture
            // position + a paired TokenText action arg (mirrors the Param→
            // position+arg pairing). An @-less capture synthesizes __tok_<name>
            // (D-5). S2.2 makes any rule containing a TokenKind a multi-step
            // ("binder") rule so it routes through this position machinery.
            SyntaxExpr::TokenKind { name, bind } => {
                let kind_name = name.to_string();
                let param_name = bind
                    .as_ref()
                    .map(|b| b.to_string())
                    .unwrap_or_else(|| format!("__tok_{}", kind_name));
                positions.push(BinderPosition::TokenKindCapture {
                    kind_name: kind_name.clone(),
                    param_name: param_name.clone(),
                });
                action_args.push(ActionArgKind::TokenText { param_name });
            },
            // L9-4: a mid-rule `*flt(node, open, close)` guest body — push a
            // GuestBodyCapture position + a paired GuestBody action arg.
            SyntaxExpr::GuestBody { open, close, bind } => {
                positions.push(BinderPosition::GuestBodyCapture {
                    open_kind: open.to_string(),
                    close_kind: close.to_string(),
                    param_name: bind.to_string(),
                });
                action_args.push(ActionArgKind::GuestBody { param_name: bind.to_string() });
            },
            SyntaxExpr::Param(name) => {
                let n = name.to_string();
                let kind = param_map.get(&n)?;
                match kind {
                    ParamKind::Binder => {
                        // Phase 3.B.3 (2026-05-11): unify single-binder
                        // into the BinderListLoop dispatch with
                        // allow_empty=false, allow_multi=false. The
                        // collapsed shape captures exactly ONE ident
                        // and closes the scope atomically via the
                        // GuardedConsumeBinderIdentAndReplaceWithEffect
                        // dispatch (`emit_binder_rule_body` checks the
                        // flags and emits a 1-branch Fork). `close`
                        // and `separator` are unused by the
                        // collapsed dispatch (no close-branch, no
                        // sep-branch); set to empty strings as
                        // sentinels. NO skip_next — the next outer
                        // position (which may be a Literal close
                        // delim or any other position) is processed
                        // normally.
                        positions.push(BinderPosition::BinderListLoop {
                            separator: String::new(),
                            close: String::new(),
                            inner_positions: vec![BinderPosition::BinderIdent],
                            collection_param_cat: None,
                            allow_empty: false,
                            allow_multi: false,
                            // Phase 4 #2: collapsed single-binder has no
                            // names accumulator; slot_idx is informational.
                            slot_idx: 0,
                        });
                        action_args.push(ActionArgKind::BinderName);
                    },
                    // `m:Ident` is NOT a nonterminal to descend into — there is no `Ident`
                    // category to parse. It is one builtin `Token::Ident` consumed in
                    // place, its text bound inertly. Routed BEFORE the generic
                    // `Simple`/`Body` arm, which would otherwise emit a `ParamParse` for a
                    // category that does not exist.
                    ParamKind::Body { cat } | ParamKind::Simple { cat }
                        if mettail_ast::grammar::NonTerminalKind::classify(cat)
                            == mettail_ast::grammar::NonTerminalKind::Ident =>
                    {
                        positions.push(BinderPosition::IdentTextCapture { param_name: n.clone() });
                        action_args.push(ActionArgKind::IdentText { param_name: n.clone() });
                    },
                    ParamKind::Body { cat } | ParamKind::Simple { cat } => {
                        positions.push(BinderPosition::ParamParse {
                            cat: cat.clone(),
                            collection: None,
                        });
                        action_args.push(ActionArgKind::Term(cat.clone()));
                    },
                    ParamKind::Guard => {
                        positions.push(BinderPosition::GuardSlot);
                        action_args.push(ActionArgKind::Predicate);
                    },
                    ParamKind::BinderList => {
                        // BinderList shouldn't appear as a bare Param —
                        // it's expressed as Op(Sep) below. Defensive.
                        return None;
                    },
                    ParamKind::SimpleCollection { .. } => {
                        // SimpleCollection appears only as Op(Sep) below.
                        // Bare Param reference is invalid — the collection
                        // requires a separator + close delim.
                        return None;
                    },
                }
            },
            SyntaxExpr::Op(PatternOp::Sep { collection, separator, source: None }) => {
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
                            // is `[BinderIdent]` and collection_param_cat=None
                            // (no synthesized accumulator).
                            inner_positions: vec![BinderPosition::BinderIdent],
                            collection_param_cat: None,
                            // Phase 3 Redesign B sub-commit 3.B.1
                            // (2026-05-11): multi-binder PNew-style — both
                            // empty (zero binders) and multi (more than
                            // one) are permitted.
                            allow_empty: true,
                            allow_multi: true,
                            // Phase 4 #2: PNew-style has no names accumulator;
                            // slot_idx is informational.
                            slot_idx: 0,
                        });
                        action_args.push(ActionArgKind::BinderList);
                        // Skip the close Literal at i+1 — it's already
                        // absorbed into the BinderListLoop's close-branch
                        // dispatch. Without this skip, the close token
                        // would be double-consumed (once by BinderListLoop,
                        // once by the spurious pos+1 Literal arm).
                        skip_next = true;
                    },
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
                        // Phase 4 #5 (2026-05-11): populate
                        // key_val_separator only for HashMap; None for
                        // Vec/HashBag/HashSet. HashMap syntax uses `":"`,
                        // matching ast/src/language.rs::map_defaults.
                        // Stage 3 (2026-06-27): routed through `kv_sep_for`
                        // (inline binder param ⇒ `declared_delims` is `None`
                        // for binder host categories ⇒ per-type default).
                        let key_val_separator = kv_sep_for(coll_kind, declared_delims);
                        // Phase 4 #1.B (2026-05-11): stamp the rule-
                        // global slot_idx and increment for the next
                        // SimpleCollection push. The CollectionMarker
                        // emitted at this position in
                        // `emit_binder_rule_body` will carry this
                        // slot_idx in its `bp` field so the walker's
                        // 3-tuple lookups disambiguate sibling slots.
                        let slot_idx_here = collection_slots_so_far;
                        collection_slots_so_far += 1;
                        positions.push(BinderPosition::ParamParse {
                            cat: elem_cat.clone(),
                            collection: Some(CollectionSepInfo {
                                separator: separator.clone(),
                                close,
                                elem_cat: elem_cat.clone(),
                                key_val_separator,
                                slot_idx: slot_idx_here,
                            }),
                        });
                        action_args.push(ActionArgKind::CollectionDrain {
                            elem_cat: elem_cat.clone(),
                            coll_kind: coll_kind.clone(),
                        });
                        // Skip the close Literal at i+1 — absorbed into
                        // CollectionLoop's close-branch dispatch.
                        skip_next = true;
                    },
                    _ => return None, // bare Simple, Body, Guard, Binder are not Sep-eligible.
                }
            },
            // B8 / Class 3 ZIP-MAP-SEP (2026-05-08): chained-Sep pattern
            // `*zip(left,right).*map(|p1,p2| body).*sep(",")`. Used by
            // rholang PInputs:
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
                // Walk the map body and build the per-iteration positions
                // used by the Class 3 dispatch.
                let mut inner_positions: Vec<BinderPosition> = Vec::new();
                let mut inner_action_args: Vec<ActionArgKind> = Vec::new();
                for inner_item in map_body {
                    match inner_item {
                        SyntaxExpr::Literal(text) => {
                            inner_positions.push(BinderPosition::Literal(text.clone()));
                        },
                        SyntaxExpr::TokenKind { .. } | SyntaxExpr::GuestBody { .. } => return None,
                        SyntaxExpr::Param(p_name) => {
                            let pn = p_name.to_string();
                            if pn == map_param_n {
                                // Names-element: parse as Name, splice into accumulator.
                                inner_positions.push(BinderPosition::ParamParse {
                                    cat: collection_elem_cat.clone(),
                                    collection: Some(CollectionSepInfo {
                                        separator: separator.clone(),
                                        close: close.clone(),
                                        elem_cat: collection_elem_cat.clone(),
                                        // Phase 4 #5 (2026-05-11):
                                        // Class-3 ZIP-MAP-SEP names
                                        // accumulator is always Vec
                                        // — no key/value separator.
                                        key_val_separator: None,
                                        // Phase 4 #1 (2026-05-11):
                                        // Class-3 names accumulator
                                        // has its own slot management
                                        // (the outer BinderListLoop
                                        // owns the accumulator slot).
                                        // slot_idx is informational
                                        // here.
                                        slot_idx: 0,
                                    }),
                                });
                                inner_action_args
                                    .push(ActionArgKind::Term(collection_elem_cat.clone()));
                            } else if pn == map_param_x {
                                // Binder-ident slot.
                                inner_positions.push(BinderPosition::BinderIdent);
                                inner_action_args.push(ActionArgKind::BinderName);
                            } else {
                                return None; // unrecognized inner Param.
                            }
                        },
                        SyntaxExpr::Op(_) => return None, // nested Op out of pilot.
                    }
                }
                if !inner_positions
                    .iter()
                    .any(|position| matches!(position, BinderPosition::BinderIdent))
                {
                    return None;
                }
                // Phase 4 #2 (2026-05-12): Class-3 ZIP-MAP-SEP allocates a
                // synthesized names accumulator — it occupies a collection
                // slot in the rule. Stamp `collection_slots_so_far` as the
                // BinderListLoop's `slot_idx`, then increment so the next
                // SimpleCollection (or another BinderListLoop) gets the
                // correct successor slot_idx.
                let slot_idx_here = collection_slots_so_far;
                collection_slots_so_far += 1;
                positions.push(BinderPosition::BinderListLoop {
                    separator: separator.clone(),
                    close,
                    inner_positions,
                    collection_param_cat: Some(collection_elem_cat.clone()),
                    // Phase 3 Redesign B sub-commit 3.B.1 (2026-05-11):
                    // Class 3 — both empty (zero iterations) and multi
                    // (more than one) are permitted.
                    allow_empty: true,
                    allow_multi: true,
                    slot_idx: slot_idx_here,
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
            },
            SyntaxExpr::Op(PatternOp::Opt { inner }) => {
                // Opt-Group: recursively classify inner SyntaxExprs.
                // Reuses param_map (inner Param references resolve against
                // the same TermContext entries — including any TermParam::Optional
                // already registered by walk_params). For the pilot, the
                // inner positions support Literal, ParamParse (Simple/Body),
                // BinderIdent, GuardSlot. Nested Optional and Sep are out
                // of pilot scope.
                let group_idx = positions
                    .iter()
                    .filter(|p| matches!(p, BinderPosition::OptionalGroup { .. }))
                    .count() as u8;

                let mut inner_positions: Vec<BinderPosition> = Vec::new();
                let mut inner_action_args: Vec<ActionArgKind> = Vec::new();
                let mut inner_skip_next: bool = false;

                for (inner_idx, inner_item) in inner.iter().enumerate() {
                    if inner_skip_next {
                        inner_skip_next = false;
                        continue;
                    }
                    match inner_item {
                        SyntaxExpr::Literal(text) => {
                            inner_positions.push(BinderPosition::Literal(text.clone()));
                        },
                        SyntaxExpr::TokenKind { .. } | SyntaxExpr::GuestBody { .. } => return None,
                        SyntaxExpr::Param(name) => {
                            let n = name.to_string();
                            let kind = param_map.get(&n)?;
                            match kind {
                                ParamKind::Binder => {
                                    inner_positions.push(BinderPosition::BinderIdent);
                                    inner_action_args.push(ActionArgKind::BinderName);
                                },
                                ParamKind::Body { cat } | ParamKind::Simple { cat } => {
                                    inner_positions.push(BinderPosition::ParamParse {
                                        cat: cat.clone(),
                                        collection: None,
                                    });
                                    inner_action_args.push(ActionArgKind::Term(cat.clone()));
                                },
                                ParamKind::Guard => {
                                    inner_positions.push(BinderPosition::GuardSlot);
                                    inner_action_args.push(ActionArgKind::Predicate);
                                },
                                ParamKind::BinderList => {
                                    return None;
                                },
                                // Bare Param ref to SimpleCollection is
                                // syntactically invalid (a collection
                                // requires Sep syntax with separator +
                                // close). The Sep-driven form is handled
                                // below via SyntaxExpr::Op(PatternOp::Sep).
                                ParamKind::SimpleCollection { .. } => {
                                    return None;
                                },
                            }
                        },
                        // Phase 4 #3 (2026-05-12): Class-2 SimpleCollection
                        // inside `*opt(...)`. Mirrors the top-level Sep arm
                        // at binder.rs:584-633 but operates over the
                        // optional inner walk's positions list. The close
                        // literal is at `inner[inner_idx + 1]`.
                        SyntaxExpr::Op(PatternOp::Sep { collection, separator, source: None }) => {
                            let n = collection.to_string();
                            let kind = param_map.get(&n)?;
                            match kind {
                                ParamKind::SimpleCollection { elem_cat, coll_kind } => {
                                    let close = match inner.get(inner_idx + 1) {
                                        Some(SyntaxExpr::Literal(text)) => text.clone(),
                                        _ => return None,
                                    };
                                    // Stage 3 (2026-06-27): same `kv_sep_for`
                                    // resolver as the top-level Sep arm —
                                    // `*opt(...)`-nested inline binder collection.
                                    let key_val_separator = kv_sep_for(coll_kind, declared_delims);
                                    let slot_idx_here = collection_slots_so_far;
                                    collection_slots_so_far += 1;
                                    inner_positions.push(BinderPosition::ParamParse {
                                        cat: elem_cat.clone(),
                                        collection: Some(CollectionSepInfo {
                                            separator: separator.clone(),
                                            close,
                                            elem_cat: elem_cat.clone(),
                                            key_val_separator,
                                            slot_idx: slot_idx_here,
                                        }),
                                    });
                                    inner_action_args.push(ActionArgKind::CollectionDrain {
                                        elem_cat: elem_cat.clone(),
                                        coll_kind: coll_kind.clone(),
                                    });
                                    // Skip the close Literal — absorbed
                                    // into CollectionLoop close-branch.
                                    inner_skip_next = true;
                                },
                                _ => return None,
                            }
                        },
                        SyntaxExpr::Op(_) => {
                            return None;
                        },
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
                    group_idx,
                    first_token_set,
                });
                action_args.push(ActionArgKind::Optional(inner_action_args));
            },
            // Op(Map/Zip) or chained ops — Phase 5c territory; skip for now.
            SyntaxExpr::Op(_) => return None,
        }
    }

    // Skip rules with no parsed positions (they're trivial and likely not
    // multi-step — let the atomic / TerminalKeyword classifier handle them).
    //
    // EXCEPTION (L9-3/L9-4): a rule whose ONLY syntax element is a leading
    // opaque-leaf capture — `b@Tok` (TokenKind) or `*flt(node, open, close)`
    // (GuestBody) — parses as a complete multi-step rule via the prefix
    // dispatch (LeadingTokenKindCapture / LeadingGuestBody), which consumes the
    // capture, pushes RuleAt(slot=1), and reduces immediately (no trailing
    // positions). Such a rule has empty `positions` yet MUST classify as a
    // binder-shape so the leading-capture fork is emitted. It always carries a
    // leading capture action arg (pushed above), so the `action_args.is_empty()`
    // guard below still filters pure-literal rules.
    let has_leading_capture =
        matches!(&sp[0], SyntaxExpr::TokenKind { .. } | SyntaxExpr::GuestBody { .. });
    if positions.is_empty() && !has_leading_capture {
        return None;
    }
    // Skip pure-literal rules (no params, no binder, no guard) — those are
    // already handled by the TerminalKeyword classifier.
    if action_args.is_empty() {
        return None;
    }

    // Phase 4 #1 (2026-05-11): multi-collection-slot Class 2 unlocked.
    // The 4 lookup-emit functions in collection.rs are now 3-tuple keyed
    // (result_src_idx, rule_idx, slot_idx) and emit one arm per slot for
    // each rule. classify_binder tracks `collection_slots_so_far` and
    // stamps `CollectionSepInfo.slot_idx` per slot. The
    // CollectionMarker pushed at each slot's dispatch carries slot_idx
    // in its `bp` field. Runtime accumulator ids are allocated by the
    // walker and flow through the pushed CollectionId action argument,
    // keeping static slot lookup separate from dynamic accumulator
    // addressing even when collections are nested.

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

fn first_param_cat_from_positions(positions: &[BinderPosition]) -> Option<&str> {
    for position in positions {
        match position {
            BinderPosition::ParamParse { cat, .. } => return Some(cat.as_str()),
            BinderPosition::BinderListLoop { collection_param_cat: Some(cat), .. } => {
                return Some(cat.as_str());
            },
            BinderPosition::BinderListLoop { inner_positions, .. }
            | BinderPosition::OptionalGroup { positions: inner_positions, .. } => {
                if let Some(cat) = first_param_cat_from_positions(inner_positions) {
                    return Some(cat);
                }
            },
            // `IdentTextCapture` joins the no-category group: it consumes a TOKEN, not a
            // nonterminal, so it contributes no parseable category to this lookup —
            // exactly as `TokenKindCapture` and `BinderIdent` do not.
            BinderPosition::Literal(_)
            | BinderPosition::TokenKindCapture { .. }
            | BinderPosition::IdentTextCapture { .. }
            | BinderPosition::GuestBodyCapture { .. }
            | BinderPosition::BinderIdent
            | BinderPosition::GuardSlot => {},
        }
    }
    None
}

/// S1-FACTORING F0 (2026-07-11): `pub(crate)` so the factoring trie's
/// `SpineItem::Literal` merge key carries the SAME derived
/// `required_top_cat` payload the `emit_binder_rule_body` Literal arm emits
/// (emitted-action-shape equality — plan §2). Visibility-only change;
/// emission is untouched.
pub(crate) fn required_top_cat_after_position(
    position: Option<&BinderPosition>,
    categories: &[String],
) -> Option<u16> {
    match position {
        Some(BinderPosition::ParamParse { cat, collection: None }) => {
            lookup_src_idx(cat, categories)
        },
        Some(BinderPosition::ParamParse { collection: Some(_), .. }) => {
            // Collection ParamParse slots leave a CollectionId action argument
            // on the stack until the enclosing binder action drains it. They
            // do not leave a term Symbol for literal guards to inspect.
            None
        },
        _ => None,
    }
}

/// Category carried in the initial `BinderRule` state.
///
/// For true abstraction binders this is the abstraction body category. For
/// multi-parameter non-binder rules there is no abstraction body, but cohort
/// equivalence still needs the first parsed parameter category instead of the
/// result category.
pub(crate) fn binder_initial_body_cat(shape: &BinderShape) -> Option<&str> {
    shape
        .body_cat
        .as_deref()
        .or_else(|| first_param_cat_from_positions(&shape.positions))
}

/// Phase 5 + F7 (2026-04-28): emit prefix-dispatch arms that recognize the
/// FIRST literal of each multi-step rule. On match, the arm pushes a
/// `RuleAt(1)` marker symbol and transitions to `BinderRule { ... }`.
///
/// **Multi-rule trigger disambiguation via Fork (F7):** when multiple rules
/// in the same result category share the same trigger keyword (e.g.,
/// Calculator's five `bool(arg)` cast rules with `arg` of different
/// categories), the arm emits `WpdaStepAction::Fork` with one branch per
/// rule. The walker fans out N `BranchCursor`s and `step_fanout` drives
/// each independently until lex-min selects the surviving branch.
///
/// Per-branch `lex_w(0.0, result_src, rule_idx)`
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
// dead_code: exercised only by the same-file `#[cfg(test)] mod tests`; dead in the non-test lib build.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn emit_binder_prefix_arms(
    language: &mettail_ast::language::LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    use std::collections::BTreeMap;

    /// Per-rule arm metadata.
    struct RuleEntry {
        rule_i: usize,
        shape: BinderShape,
        /// True when the leading literal is structural syntax rather than an
        /// action argument. The consumed trigger must still be mirrored as a
        /// span-only SPPF child; otherwise a wrapper rule with a discarded
        /// trigger and the same semantic span as its operand dedups to the
        /// operand's Symbol.
        structural_trigger: bool,
    }

    // Group entries by (trigger, result_src_idx). BTreeMap gives
    // deterministic iteration order; within a group, source order is
    // preserved by insertion.
    let mut groups: BTreeMap<(String, u16), Vec<RuleEntry>> = BTreeMap::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder_in(rule, language) else {
                continue;
            };
            let trigger = match rule.syntax_pattern.as_ref().and_then(|sp| sp.first()) {
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
                structural_trigger: true,
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
            let body_src_idx = binder_initial_body_cat(&entry.shape)
                .and_then(|name| lookup_src_idx(name, categories))
                .unwrap_or(result_src_idx);
            // Phase F.8 generalized (2026-06-04): binder-rule leading
            // literals are structural syntax. They do not become semantic
            // action args, but they must be present as span-only SPPF
            // TriggerTerminals. Otherwise a rule like
            // `"choose" a #opt(...)` with the optional group absent has the
            // same `(cat, lo, hi)` as its operand `a` and Symbol-dedups onto
            // that operand, realizing `PZero` instead of `ChooseMaybe`.
            let trigger_mode = if entry.structural_trigger {
                quote!(mettail_prattail::wpda_walker::TriggerMode::ConsumeAsTriggerOnly)
            } else {
                quote!(mettail_prattail::wpda_walker::TriggerMode::Discard)
            };
            arms.push(quote! {
                Some(mettail_prattail::automata::TokenKind::Fixed(__trigger))
                    if __trigger == #trigger && state_cat_src_idx == #result_src_idx => {
                    return WpdaStepAction::ConsumeAndPush {
                        symbol: StackSymbolV2::rule_at(
                            #result_src_idx, #rule_idx, 1u8, Some(_outer_bp),
                        ),
                        weight: lex_w(
                            0.0, #result_src_idx, #rule_idx,
                        ),
                        new_state: WpdaState::BinderRule {
                            result_src_idx: #result_src_idx,
                            rule_idx: #rule_idx,
                            body_src_idx: #body_src_idx,
                            outer_bp: _outer_bp,
                        },
                        trigger_mode: #trigger_mode,
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
                let body_src_idx = binder_initial_body_cat(&entry.shape)
                    .and_then(|name| lookup_src_idx(name, categories))
                    .unwrap_or(result_src_idx);
                quote! {
                    mettail_prattail::wpda_walker::ForkBranch {
                        symbol: StackSymbolV2::rule_at(
                            #result_src_idx, #rule_idx, 1u8, Some(_outer_bp),
                        ),
                        weight: lex_w(
                            0.0, #result_src_idx, #rule_idx,
                        ),
                        new_state: WpdaState::BinderRule {
                            result_src_idx: #result_src_idx,
                            rule_idx: #rule_idx,
                            body_src_idx: #body_src_idx,
                            outer_bp: _outer_bp,
                        },
                        // Mirror the singleton ConsumeAndPush structural
                        // trigger path: each ambiguous trigger branch owns
                        // the consumed keyword under its rule identity.
                        action_kind:
                            mettail_prattail::wpda_walker::ForkActionKind::PushWithTriggerTerminal,
                    }
                }
            })
            .collect();

        arms.push(quote! {
            Some(mettail_prattail::automata::TokenKind::Fixed(__trigger))
                if __trigger == #trigger && state_cat_src_idx == #result_src_idx => {
                return WpdaStepAction::Fork {
                    branches: vec![ #( #branches ),* ],
                    consume_trigger: true,
                };
            }
        });
    }
    quote! { #(#arms)* }
}

/// Phase 5: emit the body of `WpdaState::BinderRule`. Reads the marker's
/// `RuleAt(position)` from frontier_top, dispatches per-rule-per-position.
///
/// Stage 3.27d (G-PREFIX-BP, 2026-04-30): `prefix_bp_map` carries the
/// unary-prefix BP for rules whose shape matches the unary-prefix pattern.
/// ParamParse arms install `cur_bp = prefix_bp` for the operand sub-parse,
/// preventing lower-precedence trailing infix from stealing the prefix's
/// child. Non-prefix rules continue to use `cur_bp: 0`.
pub(crate) fn emit_binder_rule_body(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
    prefix_bp_map: &HashMap<(u16, u16), u8>,
    // S1-FACTORING F1 (2026-07-12, plan §2 items 2-4): the spine arms from
    // `factoring::build_spine_emission` — keyed `(cat, SPINE_ID, node_pos)`
    // where `node_pos` is the trie's preorder node id (root arm = 1, the
    // coordinate the spine trigger branch pushes). They join THIS match's
    // key space (`rule_idx = SPINE_ID ∈ 0xF800..` never collides with real
    // per-category rule indices — factoring.rs A9 asserts). EMPTY while
    // `S1_FACTORING == false` ⇒ byte-identical emission.
    s1_spine_arms: &TokenStream,
    // Task #15 (frame-bound peel, 2026-07-14): returns `(skeleton_body,
    // helpers)`. `skeleton_body` is the `WpdaState::BinderRule` arm body that
    // stays inline in the generated trait `step`; `helpers` are the
    // per-(cat,rule) `#[inline(never)]` dispatch methods that get emitted into
    // the sibling inherent `impl #engine_ident` block. The peel collapses the
    // ~1.11 MB monolithic `step` frame (whose size was the SUM of every
    // per-arm alloca at `-O0`, no stack coloring) into skeleton + one
    // helper-at-a-time. This is PURE MOTION: the `(cat,rule,position)` arm
    // bodies are relocated verbatim; the flat 3-tuple `match` arity (A2) is
    // kept so the live S1-FACTORING spine arms remain arity-compatible.
) -> (TokenStream, TokenStream) {
    // One entry per (cat, rule) group that has a binder shape:
    // (result_src_idx, rule_idx, that group's arm token streams). The arms are
    // moved verbatim into the group's `#[inline(never)]` helper below.
    let mut groups: Vec<(u16, u16, Vec<TokenStream>)> = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder_in(rule, language) else {
                continue;
            };
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            let mut group_arms: Vec<TokenStream> = Vec::with_capacity(shape.positions.len() + 1);
            // Stage 4 fix: emit a "rule complete" arm at position
            // `positions.len() + 1`. This arm fires when the marker has
            // advanced past the final syntax-pattern position (either via
            // a ConsumeAndReplace from a closing literal or a ReplaceAndPush
            // from a final ParamParse). It pops the RuleAt and fires the
            // semantic action; transitions to InfixLoop so the parent rule
            // can apply postfix/infix operators on the freshly-built result.
            let final_pos = (shape.positions.len() + 1) as u8;
            group_arms.push(quote! {
                (#result_src_idx, #rule_idx, #final_pos) => {
                    return WpdaStepAction::Pop {
                        weight: lex_one(),
                        new_state: WpdaState::InfixLoop {
                            cur_bp: *outer_bp,
                        },
                    };
                }
            });
            for (idx, position) in shape.positions.iter().enumerate() {
                let pos = (idx + 1) as u8;
                let next_pos = pos + 1;
                let arm = match position {
                    BinderPosition::TokenKindCapture { kind_name, .. } => {
                        // L9-3: mid-rule custom-kind capture — a structural clone
                        // of the Literal arm below, swapping the peek_text guard
                        // (GuardedConsumeAndReplace) for the peek_kind==Custom(K)
                        // guard (GuardedConsumeTokenKindAndReplace). The walker's
                        // kind gate runs inside the branch; a miss produces no
                        // child (cursor dies via step_fanout's empty-children
                        // pathway), and a hit interns an ActionArg::Token leaf.
                        quote! {
                            (#result_src_idx, #rule_idx, #pos) => {
                                return WpdaStepAction::Fork {
                                    branches: vec![mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::rule_at(
                                            #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                        ),
                                        weight: lex_one(),
                                        new_state: WpdaState::BinderRule {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            body_src_idx: *_body_src_idx,
                                            outer_bp: *outer_bp,
                                        },
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeTokenKindAndReplace {
                                                kind_name: #kind_name.to_string(),
                                            },
                                    }],
                                    consume_trigger: false,
                                };
                            }
                        }
                    },
                    // ★★ IF YOU ARE ADDING A NEW CAPTURE KIND, READ THIS FIRST.
                    //
                    // GREP FOR *PRODUCERS*, NOT FOR THE SYMBOL. A symbol existing is not a
                    // path working. This one arm cost three rounds to exactly that mistake:
                    //   1. `ActionArg::Ident` + `as_ident()` both existed, so the capture
                    //      was specced as "zero prattail change" — but NO fork op produced
                    //      an `ActionArg::Ident`; every ident routed through `BinderScope`.
                    //   2. `GuardedConsumeTokenKindAndReplace` existed and was assumed
                    //      exercised — a producer count across all 49 generated parsers
                    //      found 1 (this fixture) against 33 for the `...AndPush` twin.
                    //   3. This dispatcher existed and was called — but never for a
                    //      BINDER-FREE rule, so the fork below was emitted and never run.
                    //
                    // The cheap check that would have caught all three, in one command:
                    //   grep -l '<Symbol>' target/generated/*/wpda.rs | wc -l
                    // Zero or one producer (where the one is your own fixture) means the
                    // path is dead, not that you are holding it wrong.
                    //
                    // ⚠ MEASURED: THIS ARM WAS UNREACHABLE AT RUNTIME, AND THAT —
                    // not the op, not the gate, not the slot — IS WHY `m:Ident` DOES NOT
                    // WORK. Do not re-litigate the settled parts before reading this.
                    //
                    // `emit_binder_rule_body` emits into the generated
                    // `binder_rule_c<cat>_r<rule>` dispatcher, which the engine calls ONLY
                    // from `WpdaState::BinderRule`. A rule like
                    // `Tagged . m:Ident |- "tag" m : Num` has NO BINDER, so the walker
                    // never enters that state and this fork is never executed. Proven by
                    // instrumenting the emitted gate directly: with an `eprintln!` on
                    // every `GuardedConsumeTokenKindAndReplace { kind_name: "Ident" }`
                    // evaluation, a full fixture run produced ZERO hits while the
                    // generated parser demonstrably contains the fork and calls
                    // `binder_rule_c0_r2`.
                    //
                    // That single fact explains every symptom recorded on #131:
                    //   · the arg slot held `Term { type_name: "RealizedTerm" }` — the
                    //     rule was parsed by the ORDINARY path, which knows nothing of the
                    //     ident position and descends into a category there;
                    //   · both `...AndReplace` and `...AndPush` failed BYTE-IDENTICALLY —
                    //     an unexecuted fork cannot depend on its action kind;
                    //   · `# . f ( )` failed at EVERY arity — nothing to do with `Sep`.
                    //
                    // ⚠ The lexer is NOT the cause and must not be blamed: `extract_terminals`
                    // sets `BuiltinNeeds { ident: true, .. }` UNCONDITIONALLY
                    // (`prattail/src/lexer.rs:760`), so the `Ident` accept state always
                    // exists. Independently, the pre-fix run produced `Tagged("")`, which
                    // required consuming `abc`.
                    //
                    // ⇒ THE REMAINING WORK is routing: a rule carrying an `IdentTextCapture`
                    // must reach a dispatcher the engine actually calls for a binder-free
                    // rule, OR such a rule must enter `WpdaState::BinderRule`. Note the 33
                    // languages that DO capture tokens mid-rule use
                    // `GuardedConsumeTokenKindAndPush` emitted from `forks.rs`, NOT from
                    // this binder-rule body — that is the routing to compare against.
                    BinderPosition::IdentTextCapture { .. } => {
                        // `m:Ident` — the builtin-kind twin of the TokenKindCapture arm
                        // directly above. Same single-branch Fork, same position advance;
                        // the action is the EXISTING `ConsumeIdentAndReplace` op with
                        // `start_scope: false`, so the ident's text is interned as an
                        // `ActionArg::Ident` leaf and NO binder scope is opened. `false`
                        // is the whole distinction from `BinderIdent`: an inert name must
                        // not bind, or `new nth in { l.nth(0) }` would capture it.
                        quote! {
                            (#result_src_idx, #rule_idx, #pos) => {
                                return WpdaStepAction::Fork {
                                    branches: vec![mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::rule_at(
                                            #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                        ),
                                        weight: lex_one(),
                                        new_state: WpdaState::BinderRule {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            body_src_idx: *_body_src_idx,
                                            outer_bp: *outer_bp,
                                        },
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeTokenKindAndReplace {
                                                kind_name: "Ident".to_string(),
                                            },
                                    }],
                                    consume_trigger: false,
                                };
                            }
                        }
                    },
                    BinderPosition::GuestBodyCapture { open_kind, close_kind, .. } => {
                        // L9-4: mid-rule guest body — a single-branch Fork whose
                        // ConsumeGuestBodyAndReplace action scans the whole
                        // opener→body→closer region, assembles the FltNode, and
                        // advances past the closer (No-Injection via raw-mode
                        // tiling). Structural twin of the TokenKindCapture arm.
                        quote! {
                            (#result_src_idx, #rule_idx, #pos) => {
                                return WpdaStepAction::Fork {
                                    branches: vec![mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::rule_at(
                                            #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                        ),
                                        weight: lex_one(),
                                        new_state: WpdaState::BinderRule {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            body_src_idx: *_body_src_idx,
                                            outer_bp: *outer_bp,
                                        },
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::ConsumeGuestBodyAndReplace {
                                                open_kind: #open_kind.to_string(),
                                                close_kind: #close_kind.to_string(),
                                            },
                                    }],
                                    consume_trigger: false,
                                };
                            }
                        }
                    },
                    BinderPosition::Literal(text) => {
                        let previous_position = if idx > 0 {
                            shape.positions.get(idx - 1)
                        } else {
                            None
                        };
                        let required_top_cat =
                            required_top_cat_after_position(previous_position, categories);
                        let required_top_cat_tokens = match required_top_cat {
                            Some(cat) => quote! { Some(#cat) },
                            None => quote! { None },
                        };
                        quote! {
                            (#result_src_idx, #rule_idx, #pos) => {
                                // Stage 3.20 / L12 Commit F (2026-05-06):
                                // Cluster 1 compatibility closure #5. Single-branch
                                // GuardedConsumeAndReplace Fork — peek_text
                                // == #text guard runs inside the walker,
                                // failure produces no child (cursor dies via
                                // step_fanout's empty-children pathway).
                                return WpdaStepAction::Fork {
                                    branches: vec![mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::rule_at(
                                            #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                        ),
                                        weight: lex_one(),
                                        new_state: WpdaState::BinderRule {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            body_src_idx: *_body_src_idx,
                                            outer_bp: *outer_bp,
                                        },
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeAndReplace {
                                                expected_text: #text.to_string(),
                                                required_top_cat: #required_top_cat_tokens,
                                            },
                                    }],
                                    consume_trigger: false,
                                };
                            }
                        }
                    },
                    BinderPosition::BinderIdent => quote! {
                        // Phase 3.B.3 (2026-05-11): top-level
                        // BinderIdent is unreachable in
                        // `shape.positions` post-unification —
                        // `classify_binder` now converts
                        // `ParamKind::Binder` to
                        // `BinderPosition::BinderListLoop {
                        // allow_empty: false, allow_multi: false }`
                        // (single-binder collapse). This match arm
                        // is retained for enum exhaustiveness and
                        // emits no dispatch arm; if a future change
                        // re-introduces a top-level BinderIdent, the
                        // walker will surface it via the catch-all
                        // `_ => WpdaStepAction::Idle` and the parse
                        // will stall, which is loud enough to debug.
                    },
                    BinderPosition::BinderListLoop {
                        separator: _,
                        close,
                        collection_param_cat,
                        allow_empty,
                        allow_multi,
                        slot_idx,
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
                        //
                        // Phase 3.B.3 (2026-05-11): single-binder collapse
                        // — when allow_empty=false AND allow_multi=false
                        // AND collection_param_cat=None, emit a 1-branch
                        // Fork that captures the lone Ident, closes the
                        // scope atomically via EndBinderScope effect, and
                        // transitions to BinderRule {next_pos}. No
                        // BinderListLoop sub-state is entered. The action
                        // entry sees ActionArg::BinderScope with exactly
                        // one name in its names list, which the
                        // single-binder construction unwraps to a scalar
                        // Binder<String>.
                        if !*allow_empty && !*allow_multi && collection_param_cat.is_none() {
                            quote! {
                                (#result_src_idx, #rule_idx, #pos) => {
                                    return WpdaStepAction::Fork {
                                        branches: vec![
                                            mettail_prattail::wpda_walker::ForkBranch {
                                                symbol: StackSymbolV2::rule_at(
                                                    #result_src_idx, #rule_idx,
                                                    #next_pos, Some(*outer_bp),
                                                ),
                                                weight: lex_one(),
                                                new_state: WpdaState::BinderRule {
                                                    result_src_idx: #result_src_idx,
                                                    rule_idx: #rule_idx,
                                                    body_src_idx: *_body_src_idx,
                                                    outer_bp: *outer_bp,
                                                },
                                                action_kind:
                                                    mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeBinderIdentAndReplaceWithEffect {
                                                        start_scope: true,
                                                        effect:
                                                            mettail_prattail::wpda_walker::BuilderDelta::EndBinderScope,
                                                    },
                                            },
                                        ],
                                        consume_trigger: false,
                                    };
                                }
                            }
                        } else if collection_param_cat.is_some() {
                            quote! {
                                (#result_src_idx, #rule_idx, #pos) => {
                                    let _ = tokens.peek_text(_pos);
                                    return WpdaStepAction::Fork {
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
                                            mettail_prattail::wpda_walker::ForkBranch {
                                                symbol: StackSymbolV2::rule_at(
                                                    #result_src_idx, #rule_idx,
                                                    #next_pos, Some(*outer_bp),
                                                ),
                                                weight: lex_w(
                                                    0.0, #result_src_idx, #rule_idx,
                                                ),
                                                new_state: WpdaState::BinderRule {
                                                    result_src_idx: #result_src_idx,
                                                    rule_idx: #rule_idx,
                                                    body_src_idx: *_body_src_idx,
                                                    outer_bp: *outer_bp,
                                                },
                                                action_kind:
                                                    mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeAndReplaceWithMultipleEffects {
                                                        expected_text: #close.to_string(),
                                                        effects: vec![
                                                            mettail_prattail::wpda_walker::BuilderDelta::StartCollection,
                                                            // Phase 4 #2 (2026-05-12): carry the
                                                            // BinderListLoop's static slot_idx
                                                            // (was hardcoded 0u8). The walker
                                                            // resolves the live accumulator id
                                                            // from the current collection depth
                                                            // when applying this effect.
                                                            mettail_prattail::wpda_walker::BuilderDelta::PushCollectionId { id: #slot_idx },
                                                            mettail_prattail::wpda_walker::BuilderDelta::StartBinderScope {
                                                                names: Vec::new(),
                                                            },
                                                            // B8 / Issue C followup: close the
                                                            // empty scope so BinderScope arg
                                                            // is pushed before the body parse.
                                                            mettail_prattail::wpda_walker::BuilderDelta::EndBinderScope,
                                                        ],
                                                    },
                                            },
                                            // BRANCH 2: non-empty — ReplaceAndPush.
                                            // Replace outer RuleAt(rule, marker_pos)
                                            // with RuleAt(rule, next_pos) so when
                                            // CollectionMarker pops post-action,
                                            // the cursor unwinds cleanly past
                                            // the loop slot. Push CollectionMarker
                                            // for the Names accumulator;
                                            // emit_push_side_effects allocates +
                                            // pushes CollectionId arg + opens
                                            // BinderScope (is_class3_collection_per_slot).
                                            //
                                            // Phase 4 #2 (2026-05-12): use the
                                            // BinderListLoop's `slot_idx` (not
                                            // hardcoded 0) so that in multi-slot
                                            // rules (Class-3 + Class-2 siblings),
                                            // the per-slot predicate
                                            // `is_class3_collection_per_slot`
                                            // distinguishes this Class-3 slot
                                            // from Class-2 sibling slots.
                                            mettail_prattail::wpda_walker::ForkBranch {
                                                symbol: StackSymbolV2::collection_marker(
                                                    // binder-internal collection: dispatch_bp=0
                                                    // (no enclosing Pratt InfixLoop; close is
                                                    // driven by the binder rule machinery).
                                                    #result_src_idx, #rule_idx, #slot_idx, 0u8,
                                                ),
                                                weight: lex_w(
                                                    mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP,
                                                    #result_src_idx, #rule_idx,
                                                ),
                                                new_state: WpdaState::BinderListLoop {
                                                    result_src_idx: #result_src_idx,
                                                    rule_idx: #rule_idx,
                                                    body_src_idx: *_body_src_idx,
                                                    outer_bp: *outer_bp,
                                                    marker_pos: #pos,
                                                    next_pos: #next_pos,
                                                    sub_pos: 0u8,
                                                },
                                                action_kind:
                                                    mettail_prattail::wpda_walker::ForkActionKind::ReplaceAndPush {
                                                        replace_symbol: StackSymbolV2::rule_at(
                                                            #result_src_idx, #rule_idx,
                                                            #next_pos, Some(*outer_bp),
                                                        ),
                                                    },
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
                                    return WpdaStepAction::Fork {
                                        branches: vec![
                                            // BRANCH 1: empty close — GuardedConsumeAndReplaceWithEffect
                                            mettail_prattail::wpda_walker::ForkBranch {
                                                symbol: StackSymbolV2::rule_at(
                                                    #result_src_idx, #rule_idx,
                                                    #next_pos, Some(*outer_bp),
                                                ),
                                                weight: lex_w(
                                                    0.0, #result_src_idx, #rule_idx,
                                                ),
                                                new_state: WpdaState::BinderRule {
                                                    result_src_idx: #result_src_idx,
                                                    rule_idx: #rule_idx,
                                                    body_src_idx: *_body_src_idx,
                                                    outer_bp: *outer_bp,
                                                },
                                                action_kind:
                                                    // B8 / Issue C followup
                                                    // (2026-05-09): empty-list
                                                    // bootstrap MUST also close
                                                    // the scope so the action's
                                                    // BinderScope arg is pushed.
                                                    mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeAndReplaceWithMultipleEffects {
                                                        expected_text: #close.to_string(),
                                                        effects: vec![
                                                            mettail_prattail::wpda_walker::BuilderDelta::StartBinderScope {
                                                                names: Vec::new(),
                                                            },
                                                            mettail_prattail::wpda_walker::BuilderDelta::EndBinderScope,
                                                        ],
                                                    },
                                            },
                                            // BRANCH 2: first ident —
                                            // GuardedConsumeBinderIdentAndReplace.
                                            // B8 / Issue 3 (2026-05-10): use the
                                            // binder-aware variant which opens
                                            // a binder scope with [text] but
                                            // does NOT push an Ident arg
                                            // (the multi-binder rule's action
                                            // expects BinderScope arg, not
                                            // Ident). Lambda Lam-style single-
                                            // binder rules continue to use the
                                            // legacy GuardedConsumeIdentAndReplace
                                            // at their direct BinderIdent arm.
                                            mettail_prattail::wpda_walker::ForkBranch {
                                                symbol: StackSymbolV2::rule_at(
                                                    #result_src_idx, #rule_idx,
                                                    #pos, Some(*outer_bp),
                                                ),
                                                weight: lex_w(
                                                    mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP,
                                                    #result_src_idx, #rule_idx,
                                                ),
                                                new_state: WpdaState::BinderListLoop {
                                                    result_src_idx: #result_src_idx,
                                                    rule_idx: #rule_idx,
                                                    body_src_idx: *_body_src_idx,
                                                    outer_bp: *outer_bp,
                                                    marker_pos: #pos,
                                                    next_pos: #next_pos,
                                                    sub_pos: 0u8,
                                                },
                                                action_kind:
                                                    mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeBinderIdentAndReplace {
                                                        start_scope: true,
                                                    },
                                            },
                                        ],
                                        consume_trigger: false,
                                    };
                                }
                            }
                        }
                    },
                    BinderPosition::ParamParse { cat, collection } => {
                        let cat_src_idx = lookup_src_idx(cat, categories)
                        .unwrap_or_else(|| panic!("mettail: unresolvable category `{cat}` in a ParamParse position — every category param is validated against the declared type list, so this is a macro bug, not a grammar error"));
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
                                    return WpdaStepAction::ReplaceAndPush {
                                        replace_symbol: StackSymbolV2::rule_at(
                                            #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                        ),
                                        push_symbol: StackSymbolV2::category_entry(#cat_src_idx),
                                        weight: lex_one(),
                                        new_state: WpdaState::PrefixDispatch {
                                            pos: _pos,
                                            cur_bp: #cur_bp_lit,
                                        },
                                    };
                                }
                            },
                            Some(info) => {
                                // B9 / Class 2 (2026-05-08): the slot is a
                                // Sep-driven collection. Replace the rule's
                                // RuleAt marker with `next_pos` (so when the
                                // CollectionMarker pops, Unwinding-RuleAt
                                // sees the post-collection position) AND
                                // push a CollectionMarker keyed on this
                                // rule's `(result_src_idx, rule_idx, slot_idx)`.
                                //
                                // The walker's emit_push_side_effects logic
                                // sees the CollectionMarker push and pushes
                                // ActionArg::CollectionId onto the args
                                // stack. Phase 4 #1.B (2026-05-11): the
                                // marker's `bp` field carries the codegen-
                                // stamped `slot_idx`; the runtime accumulator
                                // id is recovered from
                                // `cursor.collection_stack.len() - 1` at push
                                // time (LIFO invariant). The transition
                                // state is PrefixDispatch{cur_bp: 0} — the
                                // next step's frontier_top is the marker,
                                // and the existing CollectionLoop apparatus
                                // (now 3-tuple keyed on slot_idx for
                                // disambiguating sibling slots in the same
                                // rule) parses elements separated by
                                // `separator` until `close`.
                                //
                                // On close, the CollectionMarker pops and
                                // the walker checks is_binder_internal_collection
                                // — for Class-2 rules this returns true, so
                                // FireAction is suppressed (the binder
                                // rule's terminal action will drain the
                                // CollectionId at its own RuleAt pop).
                                let slot_idx = info.slot_idx;
                                quote! {
                                    (#result_src_idx, #rule_idx, #pos) => {
                                        return WpdaStepAction::ReplaceAndPush {
                                            replace_symbol: StackSymbolV2::rule_at(
                                                #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                            ),
                                            push_symbol: StackSymbolV2::collection_marker(
                                                // binder-internal collection: dispatch_bp=0.
                                                #result_src_idx, #rule_idx, #slot_idx, 0u8,
                                            ),
                                            weight: lex_one(),
                                            new_state: WpdaState::PrefixDispatch {
                                                pos: _pos,
                                                cur_bp: 0u8,
                                            },
                                        };
                                    }
                                }
                            },
                        }
                    },
                    BinderPosition::GuardSlot => quote! {
                        (#result_src_idx, #rule_idx, #pos) => {
                            // Phase 6: parse predicate inline. Walker
                            // invokes parse_predicate_from_tokens, pushes
                            // ActionArg::Predicate, advances pos.
                            return WpdaStepAction::ParsePredicate {
                                replace_symbol: StackSymbolV2::rule_at(
                                    #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
                                ),
                                weight: lex_one(),
                                new_state: WpdaState::BinderRule {
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
                                return WpdaStepAction::Advance(
                                    WpdaState::OptionalGroup {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        group_idx: #group_idx_byte,
                                        sub_pos: 0,
                                        outer_bp: *outer_bp,
                                    },
                                );
                            }
                        }
                    },
                };
                group_arms.push(arm);
            }
            groups.push((result_src_idx, rule_idx, group_arms));
        }
    }
    if groups.is_empty() && s1_spine_arms.is_empty() {
        return (quote! { WpdaStepAction::Idle }, proc_macro2::TokenStream::new());
    }
    // Task #15: build the two-level dispatch. The skeleton (kept inline in
    // `step`) matches the flat 3-tuple and, for each real (cat, rule) group,
    // tail-calls that group's `#[inline(never)]` helper via a POSITION WILDCARD
    // arm `(cat, rule, _) => self.binder_rule_c{cat}_r{rule}(..)` (A2 — the
    // arity stays 3 so the S1 spine arms below still type-check). Each helper
    // re-matches the verbatim `(cat, rule, position)` arms.
    let mut skeleton_arms: Vec<TokenStream> = Vec::with_capacity(groups.len());
    let mut helpers: Vec<TokenStream> = Vec::with_capacity(groups.len());
    for (cat, rule, group_arms) in &groups {
        let helper_ident = format_ident!("binder_rule_c{}_r{}", cat, rule);
        skeleton_arms.push(quote! {
            (#cat, #rule, _) => self.#helper_ident(
                result_src_idx,
                rule_idx,
                position,
                _pos,
                tokens,
                _body_src_idx,
                outer_bp,
                frame_ctx,
            ),
        });
        helpers.push(quote! {
            // Task #15 (frame-bound peel): one BinderRule dispatch group,
            // relocated out of `step` so `step` reserves only skeleton +
            // one-helper frame (was: the SUM of every group's alloca in the
            // 1.11 MB monolithic frame). Pure motion — the arm bodies are
            // verbatim; state fields pass BY REFERENCE (A5) so the `*x` derefs
            // in the bodies are unchanged. `frame_ctx`/`tokens`/`_pos` are
            // over-provisioned for a uniform generic signature (N2), silenced
            // by the inherent impl's `#[allow(unused_variables)]`.
            #[inline(never)]
            fn #helper_ident(
                &self,
                result_src_idx: &u16,
                rule_idx: &u16,
                position: u8,
                _pos: usize,
                tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                _body_src_idx: &u16,
                outer_bp: &u8,
                frame_ctx: mettail_prattail::wpda_runtime::FrameCtx,
            ) -> mettail_prattail::wpda_walker::WpdaStepAction<
                mettail_prattail::automata::lex_weight::LexicographicWeight,
            > {
                match (*result_src_idx, *rule_idx, position) {
                    #(#group_arms)*
                    // A1: known-(cat,rule)-unknown-position ⇒ Idle (NEVER
                    // unreachable! — the original single catch-all returned
                    // Idle for this case, so a panic would be a behavior
                    // change).
                    _ => WpdaStepAction::Idle,
                }
            }
        });
    }
    let body = quote! {
        {
            let position: u8 = match frontier_top.map(|n| n.symbol.kind) {
                Some(mettail_prattail::wpda_runtime::SymbolKind::RuleAt(p)) => p,
                _ => return WpdaStepAction::Idle,
            };
            // The empty-list branch needs to push an empty BinderList arg
            // representing zero binders. Use a closure-based local helper.
            // (N1: dead no-op closure — inert; kept in the skeleton.)
            #[allow(unused_variables)]
            let b_pre_finalize_empty_list = || ();
            match (*result_src_idx, *rule_idx, position) {
                #(#skeleton_arms)*
                // S1-FACTORING F1 spine arms — `(cat, SPINE_ID, node_pos)`
                // keys, disjoint from every real-rule key above (SPINE_ID ∈
                // 0xF800..0xFE00). Kept UNCHANGED in the skeleton (A2). Empty
                // while `S1_FACTORING == false`.
                #s1_spine_arms
                // A1: unknown (cat, rule) ⇒ Idle.
                _ => WpdaStepAction::Idle,
            }
        }
    };
    let helpers_ts = quote! { #(#helpers)* };
    (body, helpers_ts)
}

/// B8 / Issue C (2026-05-09): emit a per-(rule, sub_pos) lookup that
/// returns `Some(slot_idx)` when the just-completed inner step
/// was a `ParamParse { collection: Some(_) }` whose parsed term
/// must be spliced into the Names accumulator. Returns `None` for
/// all other (rule, sub_pos) combinations.
///
/// The sub_pos value here is the sub_pos baked into the
/// BinderListLoopAt symbol — i.e. the NEXT sub_pos to dispatch after
/// the inner step landed. The just-completed step was
/// `inner_positions[sub_pos - 2]`.
///
/// For PInputs's inner_positions = [ParamParse{Name,Some}, Literal,
/// BinderIdent], this emits `(rule=PInputs, sub_pos=2) -> Some(0)`
/// — at sub_pos=2 the prior step (inner_positions[0]) was the Name
/// parse, so splice into accumulator 0.
pub(crate) fn emit_binderlist_inner_post_splice_lookup(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder_in(rule, language) else {
                continue;
            };
            for position in shape.positions.iter() {
                if let BinderPosition::BinderListLoop {
                    inner_positions,
                    collection_param_cat: Some(_),
                    slot_idx,
                    ..
                } = position
                {
                    for (i, inner) in inner_positions.iter().enumerate() {
                        if let BinderPosition::ParamParse { collection: Some(_), .. } = inner {
                            // Inner index i (0-based) → splice on landing
                            // at sub_pos = i + 2. (sub_pos = 1 dispatches
                            // inner_positions[0]; landing at sub_pos = 2
                            // means inner_positions[0] just completed.)
                            let cat = cat_i as u16;
                            let rule_idx = rule_i as u16;
                            let target_sub_pos = (i + 2) as u8;
                            // Phase 4 #2 (2026-05-12): carry the
                            // BinderListLoop's static names slot_idx.
                            // apply_effect_to_cursor resolves the runtime
                            // accumulator id from active collection depth,
                            // so this remains correct inside outer
                            // collections. Pre-Phase-4-#2 this hardcoded
                            // Some(0u8), which could not distinguish
                            // multi-slot Class-3 rules.
                            let slot_idx_lit = *slot_idx;
                            arms.push(quote! {
                                (#cat, #rule_idx, #target_sub_pos) => Some(#slot_idx_lit),
                            });
                        }
                    }
                }
            }
        }
    }
    if arms.is_empty() {
        quote! { None::<u8> }
    } else {
        quote! {
            match (result_src_idx, rule_idx, sub_pos) {
                #(#arms)*
                _ => None::<u8>,
            }
        }
    }
}

/// B8 / Issue 2 (2026-05-10): emit a per-(src, rule, sub_pos)
/// predicate that returns `true` when an OptionalGroupAt(sub_pos)
/// push belongs to a Class 3 BinderListLoop inner walk (and thus
/// should NOT open an optional scope). Returns `false` for genuine
/// `*opt(...)` OptionalGroup markers, including the case where a
/// rule has BOTH a Class 3 BinderListLoop AND a real *opt(...) in
/// the same rule (different sub_pos values disambiguate).
///
/// For PInputs (Class 3, inner_positions=[ParamParse{Name}, Literal,
/// BinderIdent]): returns true for sub_pos ∈ {1, 2, 3} (the inner
/// walk arms). For pure-OptionalGroup rules: returns false at all
/// sub_pos. For mixed Class3+OptionalGroup rules (hypothetical
/// future): returns true ONLY at sub_pos values within the
/// inner_positions range; false at OptionalGroup-internal sub_pos
/// values.
pub(crate) fn emit_is_class3_inner_marker_per_subpos(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder_in(rule, language) else {
                continue;
            };
            for position in shape.positions.iter() {
                if let BinderPosition::BinderListLoop {
                    inner_positions,
                    collection_param_cat: Some(_),
                    ..
                } = position
                {
                    let cat = cat_i as u16;
                    let rule_idx = rule_i as u16;
                    // Inner-walk sub_pos values: 1..=inner_positions.len()
                    // (sub_pos=0 is the close/sep peek; sub_pos=N
                    // dispatches inner_positions[N-1]).
                    for i in 1..=inner_positions.len() {
                        let sub_pos = i as u8;
                        arms.push(quote! {
                            (#cat, #rule_idx, #sub_pos) => true,
                        });
                    }
                }
            }
        }
    }
    if arms.is_empty() {
        quote! { false }
    } else {
        quote! {
            match (src_idx, rule_idx, sub_pos) {
                #(#arms)*
                _ => false,
            }
        }
    }
}

/// B8 / Issue D (2026-05-09); Phase 4 #2 (2026-05-12): emit a
/// per-(src, rule, slot_idx) predicate
/// `is_class3_collection_per_slot(src, rule, slot_idx) -> bool` that
/// returns `true` ONLY for the specific slot_idx of a Class-3
/// BinderListLoop's names accumulator. Used by the walker's
/// `emit_push_side_effects` to atomically open a BinderScope alongside
/// the Names accumulator allocation when a Class-3 CollectionMarker
/// is pushed.
///
/// Phase 4 #1 + #2 multi-slot fix: pre-Phase-4-#2 this was a per-rule
/// predicate `is_class3_collection(src, rule)`. For rules with both a
/// Class-3 BinderListLoop AND a Class-2 SimpleCollection sibling slot
/// (e.g. PInputsTagged: ns:Vec(Name) — slot 0 (Class-3) +
/// tags:Vec(Proc) — slot 1 (Class-2)), the per-rule predicate
/// incorrectly opened a BinderScope for the Class-2 sibling slot too.
/// The per-slot variant keys on slot_idx (now preserved in the
/// CollectionMarker symbol's `bp` field via Phase 4 #1) so only the
/// Class-3 slot opens the scope.
pub(crate) fn emit_is_class3_collection_per_slot(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder_in(rule, language) else {
                continue;
            };
            for position in shape.positions.iter() {
                if let BinderPosition::BinderListLoop {
                    collection_param_cat: Some(_),
                    slot_idx,
                    ..
                } = position
                {
                    let cat = cat_i as u16;
                    let rule_idx = rule_i as u16;
                    let slot_idx = *slot_idx;
                    arms.push(quote! { (#cat, #rule_idx, #slot_idx) => true, });
                }
            }
        }
    }
    if arms.is_empty() {
        quote! { false }
    } else {
        quote! {
            match (src_idx, rule_idx, slot_idx) {
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
pub(crate) fn emit_binderlist_inner_metadata(
    language: &LanguageDef,
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder_in(rule, language) else {
                continue;
            };
            for (idx, position) in shape.positions.iter().enumerate() {
                if let BinderPosition::BinderListLoop { collection_param_cat: Some(_), .. } =
                    position
                {
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

/// Phase 5b + B8 (2026-05-08): emit the body of `WpdaState::BinderListLoop`.
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
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder_in(rule, language) else {
                continue;
            };
            for (idx, position) in shape.positions.iter().enumerate() {
                if let BinderPosition::BinderListLoop {
                    separator,
                    close,
                    inner_positions,
                    collection_param_cat,
                    allow_empty: _,
                    allow_multi: _,
                    slot_idx: _,
                } = position
                {
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
                            // — caused >4000s hangs on rholang::PNew
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
                            return WpdaStepAction::Fork {
                                branches: vec![
                                    // BRANCH 1: close — GuardedConsumeAndReplace
                                    mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::rule_at(
                                            #result_src_idx, #rule_idx,
                                            #next_pos, Some(*outer_bp),
                                        ),
                                        weight: lex_w(
                                            0.0, #result_src_idx, #rule_idx,
                                        ),
                                        new_state: WpdaState::BinderRule {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            body_src_idx: *body_src_idx,
                                            outer_bp: *outer_bp,
                                        },
                                        action_kind:
                                            // B8 / Issue C followup
                                            // (2026-05-09): close the open
                                            // BinderScope so action's
                                            // BinderScope arg is pushed.
                                            mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeAndReplaceWithEffect {
                                                expected_text: #close.to_string(),
                                                effect:
                                                    mettail_prattail::wpda_walker::BuilderDelta::EndBinderScope,
                                            },
                                    },
                                    // BRANCH 2: sep — GuardedConsume
                                    mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::category_entry(0),
                                        weight: lex_w(
                                            0.0, #result_src_idx, #rule_idx,
                                        ),
                                        new_state: WpdaState::BinderListLoop {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            body_src_idx: *body_src_idx,
                                            outer_bp: *outer_bp,
                                            marker_pos: *marker_pos,
                                            next_pos: *next_pos,
                                            sub_pos: 0u8,
                                        },
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::GuardedConsume {
                                                expected_text: #separator.to_string(),
                                            },
                                    },
                                    // BRANCH 3: subsequent ident.
                                    // B8 / Issue 3 (2026-05-10): use the
                                    // binder-aware variant. start_scope
                                    // is false (scope already opened by
                                    // BRANCH 2 first-ident); EXTEND the
                                    // existing scope's names list with
                                    // this ident. Without this fix, the
                                    // captured ident leaks as ActionArg::
                                    // Ident on the args stack and the
                                    // scope's names list stays at length 1.
                                    mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::rule_at(
                                            #result_src_idx, #rule_idx,
                                            *marker_pos, Some(*outer_bp),
                                        ),
                                        weight: lex_w(
                                            mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP,
                                            #result_src_idx, #rule_idx,
                                        ),
                                        new_state: WpdaState::BinderListLoop {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            body_src_idx: *body_src_idx,
                                            outer_bp: *outer_bp,
                                            marker_pos: *marker_pos,
                                            next_pos: *next_pos,
                                            sub_pos: 0u8,
                                        },
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeBinderIdentAndReplace {
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
                        // BinderListLoopAt(rule, 1, outer_bp) without
                        // consuming a token; transitions to BinderListLoop
                        // {sub_pos:1}, where the inner walk dispatches the
                        // first inner_position.
                        arms.push(quote! {
                            (#result_src_idx, #rule_idx, 0u8) => {
                                let _ = tokens.peek_text(_pos);
                                return WpdaStepAction::Fork {
                                    branches: vec![
                                        // BRANCH 1: close → finish loop.
                                        // B8 / Issue C followup (2026-05-09):
                                        // ConsumeAndPop the CollectionMarker
                                        // (which is now on top after the
                                        // last BinderIdent's ConsumeIdentAndPop
                                        // popped its OptionalGroupAt). Log
                                        // EndBinderScope so action's
                                        // BinderScope arg is pushed. After
                                        // this, top is RuleAt(rule, next_pos)
                                        // (placed by ReplaceAndPush at
                                        // bootstrap), state=Unwinding.
                                        // Unwinding-RuleAt routes to BinderRule.
                                        mettail_prattail::wpda_walker::ForkBranch {
                                            symbol: StackSymbolV2::category_entry(0),
                                            weight: lex_w(
                                                0.0, #result_src_idx, #rule_idx,
                                            ),
                                            new_state: WpdaState::Unwinding,
                                            action_kind:
                                                mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeAndPopWithEffect {
                                                    expected_text: #close.to_string(),
                                                    effect:
                                                        mettail_prattail::wpda_walker::BuilderDelta::EndBinderScope,
                                                },
                                        },
                                        // BRANCH 2: sep → next iteration.
                                        mettail_prattail::wpda_walker::ForkBranch {
                                            symbol: StackSymbolV2::category_entry(0),
                                            weight: lex_w(
                                                0.0, #result_src_idx, #rule_idx,
                                            ),
                                            new_state: WpdaState::BinderListLoop {
                                                result_src_idx: #result_src_idx,
                                                rule_idx: #rule_idx,
                                                body_src_idx: *body_src_idx,
                                                outer_bp: *outer_bp,
                                                marker_pos: *marker_pos,
                                                next_pos: *next_pos,
                                                sub_pos: 0u8,
                                            },
                                            action_kind:
                                                mettail_prattail::wpda_walker::ForkActionKind::GuardedConsume {
                                                    expected_text: #separator.to_string(),
                                                },
                                        },
                                        // BRANCH 3: first-inner — Push
                                        // BinderListLoopAt(rule, 1, outer_bp)
                                        // and transition to sub_pos:1 where
                                        // the inner walk takes over. No
                                        // token consumed at this branch.
                                        mettail_prattail::wpda_walker::ForkBranch {
                                            symbol: StackSymbolV2::binder_list_loop_at(
                                                #result_src_idx, #rule_idx,
                                                1u8, *outer_bp,
                                            ),
                                            weight: lex_w(
                                                mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP,
                                                #result_src_idx, #rule_idx,
                                            ),
                                            new_state: WpdaState::BinderListLoop {
                                                result_src_idx: #result_src_idx,
                                                rule_idx: #rule_idx,
                                                body_src_idx: *body_src_idx,
                                                outer_bp: *outer_bp,
                                                marker_pos: *marker_pos,
                                                next_pos: *next_pos,
                                                sub_pos: 1u8,
                                            },
                                            action_kind:
                                                mettail_prattail::wpda_walker::ForkActionKind::Push,
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
                            let next_sp = if i + 1 == inner_positions.len() {
                                0u8
                            } else {
                                (i + 2) as u8
                            };
                            let arm = match inner_pos {
                                BinderPosition::Literal(text) => {
                                    let txt = text.clone();
                                    quote! {
                                        (#result_src_idx, #rule_idx, #cur_sp) => {
                                            return WpdaStepAction::Fork {
                                                branches: vec![
                                                    mettail_prattail::wpda_walker::ForkBranch {
                                                        symbol: StackSymbolV2::binder_list_loop_at(
                                                            #result_src_idx, #rule_idx,
                                                            #next_sp, *outer_bp,
                                                        ),
                                                        weight: lex_w(
                                                            0.0, #result_src_idx, #rule_idx,
                                                        ),
                                                        new_state: WpdaState::BinderListLoop {
                                                            result_src_idx: #result_src_idx,
                                                            rule_idx: #rule_idx,
                                                            body_src_idx: *body_src_idx,
                                                            outer_bp: *outer_bp,
                                                            marker_pos: *marker_pos,
                                                            next_pos: *next_pos,
                                                            sub_pos: #next_sp,
                                                        },
                                                        action_kind:
                                                            mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeAndReplace {
                                                                expected_text: #txt.to_string(),
                                                                required_top_cat: None,
                                                            },
                                                    },
                                                ],
                                                consume_trigger: false,
                                            };
                                        }
                                    }
                                },
                                BinderPosition::BinderIdent => {
                                    // Capture ident as binder name. On the
                                    // last inner step, transition back to
                                    // sub_pos=0 AND replace top with the
                                    // RuleAt marker so the next iteration
                                    // sees BinderListLoop's marker.
                                    let is_last = i + 1 == inner_positions.len();
                                    if is_last {
                                        // B8 / Issue C followup
                                        // (2026-05-09): use
                                        // ConsumeIdentAndPop so the
                                        // OptionalGroupAt is popped
                                        // (instead of replaced with
                                        // RuleAt(rule, marker_pos)) —
                                        // the next iteration sees the
                                        // CollectionMarker on top, and
                                        // sub_pos=0 close branch can
                                        // ConsumeAndPop the marker
                                        // cleanly.
                                        quote! {
                                            (#result_src_idx, #rule_idx, #cur_sp) => {
                                                return WpdaStepAction::Fork {
                                                    branches: vec![
                                                        mettail_prattail::wpda_walker::ForkBranch {
                                                            symbol: StackSymbolV2::category_entry(0),
                                                            weight: lex_w(
                                                                0.0, #result_src_idx, #rule_idx,
                                                            ),
                                                            new_state: WpdaState::BinderListLoop {
                                                                result_src_idx: #result_src_idx,
                                                                rule_idx: #rule_idx,
                                                                body_src_idx: *body_src_idx,
                                                                outer_bp: *outer_bp,
                                                                marker_pos: *marker_pos,
                                                                next_pos: *next_pos,
                                                                sub_pos: 0u8,
                                                            },
                                                            action_kind:
                                                                mettail_prattail::wpda_walker::ForkActionKind::ConsumeIdentAndPop {
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
                                                return WpdaStepAction::Fork {
                                                    branches: vec![
                                                        mettail_prattail::wpda_walker::ForkBranch {
                                                            symbol: StackSymbolV2::binder_list_loop_at(
                                                                #result_src_idx, #rule_idx,
                                                                #next_sp, *outer_bp,
                                                            ),
                                                            weight: lex_w(
                                                                0.0, #result_src_idx, #rule_idx,
                                                            ),
                                                            new_state: WpdaState::BinderListLoop {
                                                                result_src_idx: #result_src_idx,
                                                                rule_idx: #rule_idx,
                                                                body_src_idx: *body_src_idx,
                                                                outer_bp: *outer_bp,
                                                                marker_pos: *marker_pos,
                                                                next_pos: *next_pos,
                                                                sub_pos: #next_sp,
                                                            },
                                                            action_kind:
                                                                mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeIdentAndReplace {
                                                                    start_scope: false,
                                                                },
                                                        },
                                                    ],
                                                    consume_trigger: false,
                                                };
                                            }
                                        }
                                    }
                                },
                                BinderPosition::ParamParse { cat, collection: _ } => {
                                    // Push CategoryEntry, transition to
                                    // PrefixDispatch. The current top is
                                    // BinderListLoopAt(rule, cur_sp); we
                                    // replace it with BinderListLoopAt(rule,
                                    // next_sp) so on Unwinding we land at
                                    // sub_pos=next_sp.
                                    //
                                    // Note: this arm is in emit_binder_list_loop_body
                                    // — used for Class-3 ZIP-MAP-SEP inner walks
                                    // (e.g. the Name parse in `*zip(ns,xs).*map(
                                    // |n,x| n "?" x).*sep(",")`). The inner Name
                                    // ParamParse carries `collection: Some(...)`
                                    // for SPLICING into the names accumulator
                                    // (handled separately via the post-splice
                                    // lookup), but the parse itself is a normal
                                    // CategoryEntry sub-parse, not a
                                    // CollectionMarker push. The Class-2-in-*opt
                                    // CollectionMarker push case lives in
                                    // `emit_optional_group_body`, not here.
                                    let cat_src_idx = lookup_src_idx(cat, categories)
                        .unwrap_or_else(|| panic!("mettail: unresolvable category `{cat}` in a ParamParse position — every category param is validated against the declared type list, so this is a macro bug, not a grammar error"));
                                    quote! {
                                        (#result_src_idx, #rule_idx, #cur_sp) => {
                                            return WpdaStepAction::ReplaceAndPush {
                                                replace_symbol: StackSymbolV2::binder_list_loop_at(
                                                    #result_src_idx, #rule_idx,
                                                    #next_sp, *outer_bp,
                                                ),
                                                push_symbol: StackSymbolV2::category_entry(#cat_src_idx),
                                                weight: lex_one(),
                                                new_state: WpdaState::PrefixDispatch {
                                                    pos: _pos,
                                                    cur_bp: 0u8,
                                                },
                                            };
                                        }
                                    }
                                },
                                _ => {
                                    // Other inner positions (GuardSlot,
                                    // OptionalGroup, BinderListLoop) out of
                                    // pilot scope.
                                    quote! {}
                                },
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
        return quote! { WpdaStepAction::Idle };
    }
    quote! {
        {
            // Bind categories ref so the per-arm code can use
            // lookup_src_idx — though Class 3 emits cat_src_idx as
            // hard-coded literals, this is safe.
            match (*result_src_idx, *rule_idx, *sub_pos) {
                #(#arms)*
                _ => WpdaStepAction::Idle,
            }
        }
    }
}

/// Task #10 item 1: the optional-group Fork's branch emission order — TAKE
/// first, SKIP second, per the `vec![take, skip]` construction inside
/// `emit_optional_group_body` below (the Stage 3.12 Class A.i fork). These
/// constants are the fork-emission ordinal table's site-0/site-1 values
/// (`fork_emission::ForkEmissionOrdinalModel::into_tokens`), declared HERE
/// so the ordinal rows and the emitted fork order are lexically bound to
/// one source of truth; the const assert beside the vec construction pins
/// the pairing at macros compile time.
pub(crate) const OPTIONAL_GROUP_TAKE_BRANCH_INDEX: u16 = 0;
pub(crate) const OPTIONAL_GROUP_SKIP_BRANCH_INDEX: u16 = 1;

/// Opt-Group (2026-04-29): emit the body of `WpdaState::OptionalGroup`.
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
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> TokenStream {
    let mut arms: Vec<TokenStream> = Vec::new();

    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder_in(rule, language) else {
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
                let _first_set_for_diagnostics_only: Vec<&str> =
                    first_token_set.iter().map(|s| s.as_str()).collect();
                // Task #10 item 1: the fork-emission ordinal table's
                // site-0/site-1 rows ARE these indices — pinned against the
                // `vec![TAKE, SKIP]` order of the Fork constructed just
                // below (TAKE = branch 0, SKIP = branch 1).
                const _: () = assert!(
                    OPTIONAL_GROUP_TAKE_BRANCH_INDEX == 0 && OPTIONAL_GROUP_SKIP_BRANCH_INDEX == 1,
                );
                arms.push(quote! {
                    (#result_src_idx, #rule_idx, #group_idx_byte, 0u8) => {
                        // Stage 3.12 / Class A.i (2026-05-01): Opt-Group Fork.
                        return WpdaStepAction::Fork {
                            branches: vec![
                                // TAKE branch (push OptionalGroupAt(1) →
                                // walker auto-opens optional scope via
                                // emit_push_side_effects).
                                mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::optional_group_at(
                                        #result_src_idx, #rule_idx, 1u8, *outer_bp,
                                    ),
                                    weight: lex_w(
                                        0.0, #result_src_idx, #rule_idx,
                                    ),
                                    new_state: WpdaState::OptionalGroup {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        group_idx: #group_idx_byte,
                                        sub_pos: 1,
                                        outer_bp: *outer_bp,
                                    },
                                    action_kind: mettail_prattail::wpda_walker::ForkActionKind::Push,
                                },
                                // SKIP branch (mirror OptGroupAbsent: log
                                // PushOptionalAbsent + pop outer RuleAt +
                                // push advanced outer RuleAt).
                                mettail_prattail::wpda_walker::ForkBranch {
                                    // `symbol` is unused for OptGroupAbsent
                                    // action_kind — the cursor-side Fork
                                    // arm uses `replace_symbol` from
                                    // `action_kind`. We supply a stable
                                    // sentinel to satisfy the field.
                                    symbol: StackSymbolV2::category_entry(0),
                                    weight: lex_w(
                                        mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP,
                                        #result_src_idx, #rule_idx,
                                    ),
                                    new_state: WpdaState::BinderRule {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        body_src_idx: #result_src_idx,
                                        outer_bp: *outer_bp,
                                    },
                                    action_kind: mettail_prattail::wpda_walker::ForkActionKind::OptGroupAbsent {
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
                        // L9-3: a custom-kind capture INSIDE an optional group is
                        // not exercised by any current grammar (the toy uses only
                        // top-level captures). INERT — no such position is
                        // constructed, so this contributes no dispatch arm.
                        BinderPosition::TokenKindCapture { .. }
                        | BinderPosition::GuestBodyCapture { .. } => quote! {},
                        // An `m:Ident` INSIDE an `#opt(...)` group. Unlike the two capture
                        // kinds above this emits a REAL arm rather than nothing: the
                        // opt-group value extraction has a matching `IdentText` arm
                        // (`Option<String>` via `as_ident()`), so an inert dispatch here
                        // would leave that extraction permanently unreachable — the group
                        // would never advance past the ident and the `Some(..)` branch
                        // could not be produced. Structural clone of the `Literal` arm
                        // below, swapping the text guard for the ident consume.
                        BinderPosition::IdentTextCapture { .. } => quote! {
                            (#result_src_idx, #rule_idx, #group_idx_byte, #sp) => {
                                return WpdaStepAction::Fork {
                                    branches: vec![mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::optional_group_at(
                                            #result_src_idx, #rule_idx, #next_sp, *outer_bp,
                                        ),
                                        weight: lex_one(),
                                        new_state: WpdaState::OptionalGroup {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            group_idx: #group_idx_byte,
                                            sub_pos: #next_sp,
                                            outer_bp: *outer_bp,
                                        },
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::ConsumeIdentAndReplace {
                                                start_scope: false,
                                            },
                                    }],
                                    consume_trigger: false,
                                };
                            }
                        },
                        BinderPosition::Literal(text) => quote! {
                            (#result_src_idx, #rule_idx, #group_idx_byte, #sp) => {
                                // Stage 3.20 / L12 Commit F (2026-05-06):
                                // Cluster 1 compatibility closure #4 (opt-group
                                // inner mirror of site #5).
                                return WpdaStepAction::Fork {
                                    branches: vec![mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::optional_group_at(
                                            #result_src_idx, #rule_idx, #next_sp, *outer_bp,
                                        ),
                                        weight: lex_one(),
                                        new_state: WpdaState::OptionalGroup {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            group_idx: #group_idx_byte,
                                            sub_pos: #next_sp,
                                            outer_bp: *outer_bp,
                                        },
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeAndReplace {
                                                expected_text: #text.to_string(),
                                                required_top_cat: None,
                                            },
                                    }],
                                    consume_trigger: false,
                                };
                            }
                        },
                        BinderPosition::ParamParse { cat, collection } => {
                            let cat_src_idx = lookup_src_idx(cat, categories)
                        .unwrap_or_else(|| panic!("mettail: unresolvable category `{cat}` in a ParamParse position — every category param is validated against the declared type list, so this is a macro bug, not a grammar error"));
                            match collection {
                                None => quote! {
                                    (#result_src_idx, #rule_idx, #group_idx_byte, #sp) => {
                                        return WpdaStepAction::ReplaceAndPush {
                                            replace_symbol: StackSymbolV2::optional_group_at(
                                                #result_src_idx, #rule_idx, #next_sp, *outer_bp,
                                            ),
                                            push_symbol: StackSymbolV2::category_entry(#cat_src_idx),
                                            weight: lex_one(),
                                            new_state: WpdaState::PrefixDispatch {
                                                pos: _pos,
                                                // Optional-group inner ParamParse starts a
                                                // nested category parse at ordinary precedence;
                                                // prefix binding power belongs to the outer
                                                // binder dispatch path.
                                                cur_bp: 0u8,
                                            },
                                        };
                                    }
                                },
                                Some(info) => {
                                    // Phase 4 #3 (2026-05-12): Class-2
                                    // SimpleCollection inside *opt. Push
                                    // CollectionMarker(rule, slot_idx) and
                                    // replace OptionalGroupAt(cur_sp) with
                                    // OptionalGroupAt(next_sp). The
                                    // CollectionLoop apparatus parses
                                    // elements until close; on
                                    // CollectionMarker pop, binder-internal
                                    // close fires (no FireAction), and the
                                    // slot stays in live.collection_stack
                                    // until the outer rule's terminal action
                                    // drains via the Optional extractor.
                                    let slot_idx = info.slot_idx;
                                    quote! {
                                        (#result_src_idx, #rule_idx, #group_idx_byte, #sp) => {
                                            return WpdaStepAction::ReplaceAndPush {
                                                replace_symbol: StackSymbolV2::optional_group_at(
                                                    #result_src_idx, #rule_idx, #next_sp, *outer_bp,
                                                ),
                                                push_symbol: StackSymbolV2::collection_marker(
                                                    // binder-internal collection: dispatch_bp=0.
                                                    #result_src_idx, #rule_idx, #slot_idx, 0u8,
                                                ),
                                                weight: lex_one(),
                                                new_state: WpdaState::PrefixDispatch {
                                                    pos: _pos,
                                                    cur_bp: 0u8,
                                                },
                                            };
                                        }
                                    }
                                },
                            }
                        },
                        BinderPosition::BinderIdent => quote! {
                            (#result_src_idx, #rule_idx, #group_idx_byte, #sp) => {
                                // Stage 3.20 / L12 Commit F (2026-05-06):
                                // Cluster 1 compatibility closure #6 (opt-group
                                // inner mirror of site #6).
                                return WpdaStepAction::Fork {
                                    branches: vec![mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::optional_group_at(
                                            #result_src_idx, #rule_idx, #next_sp, *outer_bp,
                                        ),
                                        weight: lex_one(),
                                        new_state: WpdaState::OptionalGroup {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            group_idx: #group_idx_byte,
                                            sub_pos: #next_sp,
                                            outer_bp: *outer_bp,
                                        },
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeIdentAndReplace {
                                                start_scope: true,
                                            },
                                    }],
                                    consume_trigger: false,
                                };
                            }
                        },
                        BinderPosition::GuardSlot => quote! {
                            (#result_src_idx, #rule_idx, #group_idx_byte, #sp) => {
                                return WpdaStepAction::ParsePredicate {
                                    replace_symbol: StackSymbolV2::optional_group_at(
                                        #result_src_idx, #rule_idx, #next_sp, *outer_bp,
                                    ),
                                    weight: lex_one(),
                                    new_state: WpdaState::OptionalGroup {
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
                        },
                    };
                    arms.push(inner_arm);
                }

                // sub_pos == final_sub_pos: finalize.
                arms.push(quote! {
                    (#result_src_idx, #rule_idx, #group_idx_byte, #final_sub_pos) => {
                        return WpdaStepAction::OptGroupFinalize {
                            replace_symbol: StackSymbolV2::rule_at(
                                #result_src_idx, #rule_idx,
                                #outer_next_pos_byte, Some(*outer_bp),
                            ),
                            weight: lex_one(),
                            new_state: WpdaState::BinderRule {
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
        return quote! { WpdaStepAction::Idle };
    }
    quote! {
        {
            match (*result_src_idx, *rule_idx, *group_idx, *sub_pos) {
                #(#arms)*
                _ => WpdaStepAction::Idle,
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
    // ANY_CAT = u16::MAX; matches mettail_prattail::wpda_runtime::ANY_CAT
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
    // Phase 4 #1 (2026-05-11): track CollectionDrain sites so we can
    // emit drains in REVERSE source order after the main extract loop.
    // The runtime's `collection_stack` enforces LIFO drain (top first),
    // but the action body's `field_names` is in source order. Phase 1
    // (this loop) extracts CollectionId args into `arg_i_id`; Phase 2
    // (post-loop) drains in reverse; Phase 3 (also post-loop)
    // materializes each `arg_i` from its drained Vec<ActionArg>.
    struct CollectionDrainSite {
        arg_idx: usize,
        elem_id: Ident,
        coll_kind: CollectionType,
    }
    let mut collection_drain_sites: Vec<CollectionDrainSite> = Vec::new();

    for (i, kind) in shape.action_args.iter().enumerate() {
        let var = format_ident!("arg_{}", i);
        match kind {
            ActionArgKind::BinderName => {
                // Phase 3.B.3 (2026-05-11): post-unification, top-level
                // BinderName always extracts from ActionArg::BinderScope
                // (the runtime's BinderListLoop dispatch closes the scope
                // via EndBinderScope effect on the lone-ident branch, so
                // the args stack carries a BinderScope handle with
                // exactly one name). Unwrap names.into_iter().next() to
                // a scalar String for the existing single-binder
                // construction at `b.push_term::<Cat>(Cat::Label(...,
                // Scope::new(Binder(get_or_create_var(#binder_name)),
                // Box::new(body))))`.
                extracts.push(quote! {
                    let #var = match iter.next() {
                        Some(mettail_prattail::wpda_runtime::ActionArg::BinderScope(h)) => {
                            match h.names.into_iter().next() {
                                Some(name) => name,
                                None => return,
                            }
                        },
                        _ => return,
                    };
                });
                binder_name_holders.push(var.clone());
            },
            ActionArgKind::TokenText { .. } => {
                // L9-3: the captured custom-kind token arrives as
                // ActionArg::Token; bind its text as a `String` via
                // as_token_text() (the proven native-literal path,
                // semantic_actions.rs:918-921). Bare String field — no
                // Arc/Box wrapping (a token capture is plain text).
                extracts.push(quote! {
                    let #var: String = match iter.next() {
                        Some(a) => a.as_token_text().map(|s| s.to_string()).unwrap_or_default(),
                        None => return,
                    };
                });
                field_names.push(quote! { #var });
            },
            ActionArgKind::IdentText { .. } => {
                // The consumed builtin `Token::Ident` arrives as `ActionArg::Ident`; bind
                // its name as a bare `String` via `as_ident()`. Structurally identical to
                // the `TokenText` arm above — only the accessor differs, because the two
                // arrive in different `ActionArg` variants.
                extracts.push(quote! {
                    let #var: String = match iter.next() {
                        Some(a) => match a.as_ident() {
                            Some(s) => s.to_string(),
                            // ⚠ A consumed `Token::Ident` reaches the args stack as
                            // `ActionArg::Ident` ONLY when the SPPF terminal was interned
                            // with `pushed_via_push_ident = true`
                            // (`wpda_walker.rs:8305-8318` branches on that discriminator,
                            // NOT on `TokenKind::Ident`). Any other origin delivers
                            // `ActionArg::Token { kind: Ident, .. }` carrying the same
                            // text, so accept it rather than losing the name.
                            None => match a.as_token_text() {
                                Some(s) => s.to_string(),
                                // NEVER `unwrap_or_default()`. That silently yielded an
                                // EMPTY name and built a well-formed term with a blank
                                // field — it survived a full build, a green type-check and
                                // eight walkers before a fixture caught it. Worse, the
                                // blank was never the ident at all: the slot held a
                                // `Term { type_name: "RealizedTerm" }`, so the default was
                                // masking a WRONG READING, not a missing string. Failing
                                // the action makes the wrong reading unrealizable, which
                                // is what lets the correct one win.
                                None => return,
                            },
                        },
                        None => return,
                    };
                });
                field_names.push(quote! { #var });
            },
            ActionArgKind::GuestBody { .. } => {
                // L9-4: the assembled guest body arrives as
                // `ActionArg::GuestBody(GuestBodyData)` (prattail primitives);
                // lower it to `Arc<FltNode>` here (the generated crate depends on
                // `mettail_runtime`; prattail does not). 1:1 field map.
                extracts.push(quote! {
                    let #var: std::sync::Arc<mettail_runtime::FltNode> = match iter.next() {
                        Some(a) => match a.as_guest_body() {
                            Some(gb) => std::sync::Arc::new(mettail_runtime::FltNode {
                                tag: gb.tag.clone(),
                                body_src: gb.body_src.clone(),
                                holes: gb.holes.iter().map(|h| mettail_runtime::FltHole {
                                    name: h.name.clone(),
                                    category: h.category.clone(),
                                    offset: h.offset,
                                }).collect(),
                                position: gb.position,
                            }),
                            None => return,
                        },
                        None => return,
                    };
                });
                field_names.push(quote! { #var });
            },
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
                    field_names.push(quote! { std::sync::Arc::new(#var) });
                }
            },
            ActionArgKind::Predicate => {
                extracts.push(quote! {
                    let #var = match iter.next().and_then(|a| a.into_predicate::<mettail_runtime::BehavioralPred>()) {
                        Some(p) => p,
                        None => return,
                    };
                });
                field_names.push(quote! { #var });
            },
            ActionArgKind::BinderList => {
                extracts.push(quote! {
                    let #var = match iter.next() {
                        Some(mettail_prattail::wpda_runtime::ActionArg::BinderScope(h)) => h.names,
                        _ => return,
                    };
                });
                binder_list_holder = Some(var.clone());
            },
            ActionArgKind::CollectionDrain { elem_cat, coll_kind } => {
                // B9 / Class 2 (2026-05-08): drain the cursor's collection
                // accumulator. The CollectionMarker push at the binder rule's
                // ParamParse{collection: Some(...)} dispatch pushed an
                // ActionArg::CollectionId(id); now we consume it, drain the
                // accumulator, materialize a container of `coll_kind`, and
                // emit the bare value (no Box::new wrapping — the AST
                // variant takes a bare container per language!-macro
                // codegen convention).
                //
                // Phase 4 #1 (2026-05-11): for multi-collection-slot rules,
                // the args stack carries multiple CollectionIds in source
                // order (e.g., [CollectionId(0), CollectionId(1)] for a
                // 2-slot rule). The runtime's collection_stack requires
                // LIFO drain (drain top first), but the action body wants
                // source-order materialization for the AST variant
                // construction (e.g., Cat::Pair(xs, ys) needs xs first).
                //
                // Resolution: Phase 1 of the action body extracts ALL
                // CollectionIds without draining (saved as `arg_i_id`),
                // then Phase 2 (emitted after the main extracts loop)
                // drains in REVERSE source order so each drain matches
                // the top of the stack. Phase 3 materializes each drain
                // into the source-order `arg_i`. The materialized
                // containers are referenced in source order by
                // `field_names`.
                let elem_id = format_ident!("{}", elem_cat);
                let id_var = format_ident!("arg_{}_id", i);
                extracts.push(quote! {
                    let #id_var: u8 = match iter.next().and_then(|a| a.as_collection_id()) {
                        Some(i) => i,
                        None => return,
                    };
                });
                // Defer the drain + materialize to Phase 2/3. Track the
                // metadata for the post-loop reverse-drain emission.
                collection_drain_sites.push(CollectionDrainSite {
                    arg_idx: i,
                    elem_id,
                    coll_kind: coll_kind.clone(),
                });
                // Bare value — no Box::new wrapping (the AST variant takes
                // bare Vec<T> / HashBag<T> / HashSet<T> per language! macro
                // convention).
                field_names.push(quote! { #var });
            },
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
                        ActionArgKind::TokenText { .. } => quote! {
                            let #inner_var: Option<String> =
                                match #opt_var.as_mut() {
                                    Some(inner_iter) => inner_iter
                                        .next()
                                        .and_then(|a| a.as_token_text().map(|s| s.to_string())),
                                    None => None,
                                };
                        },
                        // The `Ident`-capture twin inside an `#opt(...)` group: same
                        // `Option<String>` destination, `as_ident()` accessor.
                        ActionArgKind::IdentText { .. } => quote! {
                            let #inner_var: Option<String> =
                                match #opt_var.as_mut() {
                                    Some(inner_iter) => inner_iter
                                        .next()
                                        .and_then(|a| a.as_ident().map(|s| s.to_string())),
                                    None => None,
                                };
                        },
                        ActionArgKind::GuestBody { .. } => quote! {
                            let #inner_var: Option<std::sync::Arc<mettail_runtime::FltNode>> =
                                match #opt_var.as_mut() {
                                    Some(inner_iter) => inner_iter.next().and_then(|a| {
                                        a.as_guest_body().map(|gb| std::sync::Arc::new(
                                            mettail_runtime::FltNode {
                                                tag: gb.tag.clone(),
                                                body_src: gb.body_src.clone(),
                                                holes: gb.holes.iter().map(|h| mettail_runtime::FltHole {
                                                    name: h.name.clone(),
                                                    category: h.category.clone(),
                                                    offset: h.offset,
                                                }).collect(),
                                                position: gb.position,
                                            }
                                        ))
                                    }),
                                    None => None,
                                };
                        },
                        ActionArgKind::Term(cat) => {
                            let cat_id = format_ident!("{}", cat);
                            quote! {
                                let #inner_var: Option<std::sync::Arc<#cat_id>> =
                                    match #opt_var.as_mut() {
                                        Some(inner_iter) => inner_iter.next()
                                            .and_then(|a| a.into_term::<#cat_id>())
                                            .map(std::sync::Arc::new),
                                        None => None,
                                    };
                            }
                        },
                        ActionArgKind::BinderName => quote! {
                            let #inner_var: Option<String> =
                                match #opt_var.as_mut() {
                                    Some(inner_iter) => match inner_iter.next() {
                                        Some(mettail_prattail::wpda_runtime::ActionArg::Ident { name, .. }) => Some(name),
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
                                        Some(mettail_prattail::wpda_runtime::ActionArg::BinderScope(h)) => Some(h.names),
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
                        ActionArgKind::CollectionDrain { elem_cat, coll_kind } => {
                            // Phase 4 #3 (2026-05-12): Class-2 SimpleCollection
                            // inside *opt. When the optional was TAKEN, the
                            // inner_iter yields ActionArg::CollectionId(id);
                            // drain the slot from live.collection_stack and
                            // materialize into the container kind. When NOT
                            // TAKEN, emit None.
                            //
                            // The drain order is locally LIFO-safe: the
                            // optional collection slot is the innermost open
                            // slot at the point this materialization fires
                            // (the optional scope is the innermost scope,
                            // and the collection inside it is its innermost
                            // child).
                            let elem_id = format_ident!("{}", elem_cat);
                            match coll_kind {
                                CollectionType::Vec => quote! {
                                    let #inner_var: Option<std::vec::Vec<#elem_id>> =
                                        match #opt_var.as_mut() {
                                            Some(inner_iter) => match inner_iter.next() {
                                                Some(arg) => match arg.as_collection_id() {
                                                    Some(id) => {
                                                        let drained = b.drain_collection(id);
                                                        Some(
                                                            drained.into_iter()
                                                                .filter_map(|a| a.into_term::<#elem_id>())
                                                                .collect()
                                                        )
                                                    },
                                                    None => None,
                                                },
                                                None => None,
                                            },
                                            None => None,
                                        };
                                },
                                CollectionType::HashBag => quote! {
                                    let #inner_var: Option<mettail_runtime::HashBag<#elem_id>> =
                                        match #opt_var.as_mut() {
                                            Some(inner_iter) => match inner_iter.next() {
                                                Some(arg) => match arg.as_collection_id() {
                                                    Some(id) => {
                                                        let drained = b.drain_collection(id);
                                                        Some(mettail_runtime::HashBag::<#elem_id>::from_iter(
                                                            drained.into_iter()
                                                                .filter_map(|a| a.into_term::<#elem_id>())
                                                        ))
                                                    },
                                                    None => None,
                                                },
                                                None => None,
                                            },
                                            None => None,
                                        };
                                },
                                CollectionType::HashSet => quote! {
                                    let #inner_var: Option<std::collections::HashSet<#elem_id>> =
                                        match #opt_var.as_mut() {
                                            Some(inner_iter) => match inner_iter.next() {
                                                Some(arg) => match arg.as_collection_id() {
                                                    Some(id) => {
                                                        let drained = b.drain_collection(id);
                                                        Some(std::collections::HashSet::<#elem_id>::from_iter(
                                                            drained.into_iter()
                                                                .filter_map(|a| a.into_term::<#elem_id>())
                                                        ))
                                                    },
                                                    None => None,
                                                },
                                                None => None,
                                            },
                                            None => None,
                                        };
                                },
                                CollectionType::HashMap | CollectionType::PathMap => quote! {
                                    let #inner_var: Option<mettail_runtime::HashMapLit<#elem_id, #elem_id>> =
                                        match #opt_var.as_mut() {
                                            Some(inner_iter) => match inner_iter.next() {
                                                Some(arg) => match arg.as_collection_id() {
                                                    Some(id) => {
                                                        let drained = b.drain_collection(id);
                                                        let mut iter_drained = drained.into_iter();
                                                        let mut container = mettail_runtime::HashMapLit::<#elem_id, #elem_id>::default();
                                                        while let Some(k_arg) = iter_drained.next() {
                                                            let v_arg = match iter_drained.next() {
                                                                Some(v) => v,
                                                                None => break,
                                                            };
                                                            if let (Some(k), Some(v)) = (
                                                                k_arg.into_term::<#elem_id>(),
                                                                v_arg.into_term::<#elem_id>(),
                                                            ) {
                                                                container.insert(k, v);
                                                            }
                                                        }
                                                        Some(container)
                                                    },
                                                    None => None,
                                                },
                                                None => None,
                                            },
                                            None => None,
                                        };
                                },
                            }
                        },
                    };
                    inner_ext.push(extract_inner);
                }
                extracts.push(quote! {
                    let mut #opt_var: Option<std::vec::IntoIter<mettail_prattail::wpda_runtime::ActionArg>> =
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
            },
        }
    }

    // Phase 4 #1 (2026-05-11): emit Phase-2 (reverse-drain) and Phase-3
    // (per-slot materialize) for CollectionDrain sites. The runtime's
    // collection_stack is LIFO, so drains must fire in REVERSE source
    // order (top-of-stack first). The materialization then assigns the
    // drained Vec<ActionArg> to the source-order `arg_i` local, which
    // `field_names` references for the AST construction.
    for site in collection_drain_sites.iter().rev() {
        let arg_idx = site.arg_idx;
        let elem_id = &site.elem_id;
        let var = format_ident!("arg_{}", arg_idx);
        let id_var = format_ident!("arg_{}_id", arg_idx);
        let materialize = match site.coll_kind {
            CollectionType::Vec => quote! {
                let #var: std::vec::Vec<#elem_id> = drained
                    .into_iter()
                    .filter_map(|a| a.into_term::<#elem_id>())
                    .collect();
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
            CollectionType::HashMap | CollectionType::PathMap => quote! {
                let mut iter_drained = drained.into_iter();
                let mut container = mettail_runtime::HashMapLit::<
                    #elem_id, #elem_id,
                >::default();
                while let Some(k_arg) = iter_drained.next() {
                    let v_arg = match iter_drained.next() {
                        Some(v) => v,
                        None => break,
                    };
                    if let (Some(k), Some(v)) = (
                        k_arg.into_term::<#elem_id>(),
                        v_arg.into_term::<#elem_id>(),
                    ) {
                        container.insert(k, v);
                    }
                }
                let #var = container;
            },
        };
        extracts.push(quote! {
            let drained = b.drain_collection(#id_var);
            #materialize
        });
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
            let scope = mettail_runtime::Scope::new(binders, std::sync::Arc::new(#body));
            b.push_term::<#cat_ident>(
                #cat_ident::#label_ident(#(#field_names,)* scope)
            );
        }
    } else if shape.has_binder {
        // Single-binder: Scope<Binder, Box<Body>>.
        // Phase 3.B.3 (2026-05-11): the scope is closed atomically by
        // the BinderListLoop dispatch's GuardedConsumeBinderIdent-
        // AndReplaceWithEffect EndBinderScope effect — no
        // pop_binder_scope_silent() needed; the names were already
        // extracted via ActionArg::BinderScope into #binder_name.
        let binder_name = binder_name_holders
            .first()
            .expect("single-binder shape must have one binder name");
        let body = body_holder.expect("single-binder shape must have body");
        quote! {
            let scope = mettail_runtime::Scope::new(
                mettail_runtime::Binder(mettail_runtime::get_or_create_var(#binder_name)),
                std::sync::Arc::new(#body),
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
        |b: &mut mettail_prattail::wpda_runtime::SemanticBuilder,
         args: Vec<mettail_prattail::wpda_runtime::ActionArg>| {
            let mut iter = args.into_iter();
            #(#extracts)*
            #construct
        }
    };
    Some(quote! {
        (#src_idx, #rule_idx) => {
            static ENTRY: mettail_prattail::wpda_runtime::ActionEntry =
                mettail_prattail::wpda_runtime::ActionEntry {
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
    use mettail_ast::grammar::{rule_fixture, GrammarRule};
    use proc_macro2::Span;
    use syn::Ident;

    fn lambda_lam_rule() -> GrammarRule {
        GrammarRule {
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
            ..rule_fixture(
                Ident::new("Lam", Span::call_site()),
                Ident::new("Term", Span::call_site()),
            )
        }
    }

    fn fraction_rule() -> GrammarRule {
        GrammarRule {
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
            ..rule_fixture(
                Ident::new("Fraction", Span::call_site()),
                Ident::new("BigRat", Span::call_site()),
            )
        }
    }

    fn fraction_alias_rule() -> GrammarRule {
        let mut rule = fraction_rule();
        rule.label = Ident::new("FractionAlt", Span::call_site());
        rule
    }

    #[test]
    fn classifies_lambda_lam_rule() {
        let shape = classify_binder_in(&lambda_lam_rule(), &synthetic_lang_for_lambda_test())
            .expect("Lam should classify");
        assert_eq!(shape.label, "Lam");
        assert!(!shape.is_multi);
        assert!(shape.has_binder);
        assert_eq!(shape.action_arity, 2);
    }

    #[test]
    fn classifies_fraction_multi_param_rule() {
        let shape = classify_binder_in(&fraction_rule(), &synthetic_lang_for_lambda_test())
            .expect("Fraction should classify");
        assert_eq!(shape.label, "Fraction");
        assert!(!shape.is_multi);
        assert!(!shape.has_binder);
        assert_eq!(shape.action_arity, 2);
        assert_eq!(shape.param_cats, vec!["BigInt", "BigInt"]);
    }

    #[test]
    fn literal_top_guard_only_follows_term_producing_params() {
        let categories = vec!["Proc".to_string()];
        let term_param = BinderPosition::ParamParse {
            cat: "Proc".to_string(),
            collection: None,
        };
        let collection_param = BinderPosition::ParamParse {
            cat: "Proc".to_string(),
            collection: Some(CollectionSepInfo {
                separator: "|".to_string(),
                close: ")".to_string(),
                elem_cat: "Proc".to_string(),
                key_val_separator: None,
                slot_idx: 0,
            }),
        };

        assert_eq!(
            required_top_cat_after_position(Some(&term_param), &categories),
            Some(0),
            "ordinary ParamParse leaves a term symbol for the following literal guard",
        );
        assert_eq!(
            required_top_cat_after_position(Some(&collection_param), &categories),
            None,
            "collection ParamParse leaves CollectionId, not a term symbol",
        );
        assert_eq!(
            required_top_cat_after_position(
                Some(&BinderPosition::Literal("(".into())),
                &categories
            ),
            None,
        );
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

    #[test]
    fn multi_rule_binder_prefix_fork_keeps_rule_identity_in_stack_and_state() {
        let categories = vec!["BigInt".to_string(), "BigRat".to_string()];
        let per_cat = vec![Vec::new(), vec![fraction_rule(), fraction_alias_rule()]];
        let language = synthetic_lang_for_lambda_test();
        let ts = emit_binder_prefix_arms(&language, &categories, &per_cat);
        let s = ts.to_string();

        assert!(s.contains("WpdaStepAction :: Fork"));
        assert!(s.contains("consume_trigger : true"));
        assert!(
            s.contains("ForkActionKind :: PushWithTriggerTerminal"),
            "each same-trigger branch must own the consumed trigger under its rule identity",
        );
        assert!(
            s.contains("StackSymbolV2 :: rule_at (1u16 , 0u16 , 1u8"),
            "first branch must keep its category/rule/position stack identity",
        );
        assert!(
            s.contains("StackSymbolV2 :: rule_at (1u16 , 1u16 , 1u8"),
            "second branch must keep its category/rule/position stack identity",
        );
        assert!(
            s.contains("rule_idx : 0u16") && s.contains("rule_idx : 1u16"),
            "same-trigger branches must remain distinct in WpdaState::BinderRule",
        );
        assert!(
            s.matches("body_src_idx : 0u16").count() >= 2,
            "both branches should parse their first operand through the declared source category",
        );
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
        let (mut ts, __ts_helpers) = emit_binder_rule_body(
            &synthetic_lang_for_lambda_test(),
            &categories,
            &per_cat,
            &prefix_bp_map,
            &proc_macro2::TokenStream::new(),
        );
        // Task #15 peel: arm bodies now live in the per-(cat,rule) helpers;
        // assert over skeleton + helpers combined.
        ts.extend(__ts_helpers);
        let s = ts.to_string();
        // Phase 3.B.3 (2026-05-11): single-binder rules are unified
        // into the BinderListLoop dispatch with allow_empty=false,
        // allow_multi=false. The emitted code uses
        // GuardedConsumeBinderIdentAndReplaceWithEffect to atomically
        // capture the lone Ident, open + close the binder scope, and
        // replace the GSS top. The "." Literal arm still uses
        // GuardedConsumeAndReplace.
        assert!(s.contains("GuardedConsumeBinderIdentAndReplaceWithEffect"));
        assert!(s.contains("EndBinderScope"));
        assert!(s.contains("GuardedConsumeAndReplace"));
        assert!(s.contains("\".\""));
    }

    #[test]
    fn emits_binder_rule_body_for_fraction() {
        let categories = vec!["BigInt".to_string(), "BigRat".to_string()];
        let per_cat = vec![Vec::new(), vec![fraction_rule()]];
        let prefix_bp_map = std::collections::HashMap::new();
        let (mut ts, __ts_helpers) = emit_binder_rule_body(
            &synthetic_lang_for_lambda_test(),
            &categories,
            &per_cat,
            &prefix_bp_map,
            &proc_macro2::TokenStream::new(),
        );
        // Task #15 peel: arm bodies now live in the per-(cat,rule) helpers;
        // assert over skeleton + helpers combined.
        ts.extend(__ts_helpers);
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
