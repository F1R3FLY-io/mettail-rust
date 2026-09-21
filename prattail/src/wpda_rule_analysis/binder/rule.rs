//! Original multi-step binder classification over immutable borrowed readers.
//!
//! The control flow is relocated from the macro classifier. Declarations use
//! the original shared explicit worklist; optional bodies use the original
//! shared frame machine. No grammar reconstruction or second classifier runs.
//!
//! `BinderRuleProjection.v` models reader correspondence, all output fields,
//! and helper/failure ordering. It does not prove arbitrary readers lawful.
//! In particular, owned-image admission must establish valid acyclic handles,
//! representable collection slots and action arities before classification.
//! Original static arithmetic and casts are retained, not silently redefined.

use super::optional::{
    classify_optional_body, optional_first_token_set, BinderSyntaxObservation, BinderSyntaxReader,
    OptionalOperationObservation,
};
use super::term_param::{
    TermParamLeafKind, TermParamLeaves, TermParamObservation, TermParamReader,
};
use super::{ActionArgKind, BinderPosition, BinderShape, CollectionSepInfo, ParamKind};
use mettail_ast::types::CollectionType;

/// Authored type constructors remain distinct; nested types are only handles.
pub enum BinderTypeObservation<'syntax, N, T> {
    Base(N),
    Collection {
        coll_type: &'syntax CollectionType,
        element: T,
    },
    Map {
        key: T,
        value: T,
    },
    Arrow {
        codomain: T,
    },
    Other(T),
}

/// Main-classifier-only operation observations. The optional reader still
/// rejects these operations without inspecting their children.
pub enum MapZipObservation<N, A, S, O> {
    Map { source: O, params: A, body: S },
    Zip { left: N, right: N },
    Other(O),
}

/// Shallow access to the exact authored rule inspected by the original binder
/// classifier. Missing contexts are distinct from present empty sequences.
/// Names must preserve both Display/ToString spelling and original equality;
/// Map key/value identity is not inferred from spelling.
///
/// In addition to the inherited syntax and term-reader laws, name indexing is
/// valid exactly below names_len. Rule, type and operation handles belong to
/// this immutable reader. Unsupported type/operation variants retain identity
/// without projecting their children.
pub trait BinderRuleReader<'syntax>:
    BinderSyntaxReader<'syntax>
    + TermParamReader<'syntax, Name = <Self as BinderSyntaxReader<'syntax>>::Name>
{
    type Rule: Copy;
    type Names: Copy;

    fn term_context(&self, rule: Self::Rule) -> Option<Self::Parameters>;
    fn syntax_pattern(&self, rule: Self::Rule) -> Option<Self::Sequence>;
    fn label(&self, rule: Self::Rule) -> <Self as BinderSyntaxReader<'syntax>>::Name;
    fn category(&self, rule: Self::Rule) -> <Self as BinderSyntaxReader<'syntax>>::Name;
    fn ty(
        &self,
        ty: Self::Type,
    ) -> BinderTypeObservation<'syntax, <Self as BinderSyntaxReader<'syntax>>::Name, Self::Type>;
    fn names_len(&self, names: Self::Names) -> usize;
    fn name_at(
        &self,
        names: Self::Names,
        index: usize,
    ) -> Option<<Self as BinderSyntaxReader<'syntax>>::Name>;
    fn names_equal(
        &self,
        left: <Self as BinderSyntaxReader<'syntax>>::Name,
        right: <Self as BinderSyntaxReader<'syntax>>::Name,
    ) -> bool;
    fn map_zip_operation(
        &self,
        operation: Self::Operation,
    ) -> MapZipObservation<
        <Self as BinderSyntaxReader<'syntax>>::Name,
        Self::Names,
        Self::Sequence,
        Self::Operation,
    >;
}

/// Derive the original binder descriptor. The resolver is deliberately lazy:
/// absent contexts and empty syntax return before category lookup. Helpers run
/// at the original callsites, including on a prefix that later rejects.
pub fn classify_binder_in<'syntax, R, D>(
    reader: &'syntax R,
    rule: R::Rule,
    resolve_declared_delimiters: impl FnOnce() -> D,
    mut guest_nested_open_kinds: impl FnMut(&str) -> Vec<String>,
    mut kv_sep_for: impl FnMut(&CollectionType, D) -> Option<String>,
) -> Option<BinderShape>
where
    R: BinderRuleReader<'syntax>,
    <R as BinderSyntaxReader<'syntax>>::Name: std::fmt::Display,
    D: Copy,
{
    let tc = reader.term_context(rule)?;
    let sp = reader.syntax_pattern(rule)?;
    if reader.sequence_len(sp) == 0 {
        return None;
    }
    // Stage 3 (2026-06-27): the declared collection delimiters for THIS rule's
    // result category, if it is declared as a collection category (`as List`/
    // `Bag`/`Map`/`Set`/`Pathmap`). It is threaded through `language` so the
    // inline-binder kv-source reads through the SAME `kv_sep_for` resolver as the
    // declared-category and lexer-terminal sources.
    //
    // ⚠ CORRECTION (2026-07-29, #151 ROOT 3). The original text here claimed:
    // "For binder rules — whose category is a host category like `Proc`/`Name`,
    // never a declared collection — this resolves to `None`". **That premise is
    // false.** The auto-injected higher-order-literal variants (`MVar`,
    // `MApplyProc`, `MApplyName`, …) are generated into *every* category,
    // including rholang's `Map` and `Pathmap`, which ARE declared collection
    // categories carrying `key_val_sep: Some(":")`. So `declared_delims` is
    // `Some(..)` for 40 of rholang's binder rules, whose collection slots are
    // `Vec<Proc>` argument lists — not maps.
    //
    // The consequence used to be that those `Vec` slots inherited `":"` and were
    // classified `is_kv` by the walker's `CollectionMarker` close, landing them
    // under the kv arity gate (`items == 2·(seps+1)`) instead of the sequence
    // gate (`items == seps+1`). The fix is in `kv_sep_for` itself, which now
    // gates on `coll_type` first: a `Vec` has no key/value separator regardless
    // of what its home category declares. This site keeps resolving the declared
    // delimiters (they legitimately supply the *spelling* for a genuine kv slot);
    // it simply no longer decides *whether* a separator exists.
    let declared_delims = resolve_declared_delimiters();
    // Position 0 is the dispatch anchor. It may be a consumed Literal trigger,
    // a leading token/guest capture, or a category-valued Param. A leading
    // category Param is parsed through an ordinary ReplaceAndPush descent; it
    // is not a cross-category projection because this rule still has its own
    // continuation and constructor action after that child returns. The
    // `.skip(1)` loop below therefore starts with the first continuation item.
    if !matches!(
        reader.at(sp, 0).expect("nonempty syntax has an anchor"),
        BinderSyntaxObservation::Literal(_)
            | BinderSyntaxObservation::TokenKind { .. }
            | BinderSyntaxObservation::GuestBody { .. }
            | BinderSyntaxObservation::Param(_)
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
    if reader.params_len(tc) == 1 {
        if matches!(
            reader.param(reader.param_at(tc, 0).expect("single parameter exists")),
            TermParamObservation::Simple { ty, .. }
                if matches!(reader.ty(ty), BinderTypeObservation::Collection { .. })
        ) {
            let class5_shape_3 = reader.sequence_len(sp) == 3
                && matches!(
                    reader.at(sp, 0).expect("nonempty syntax has an anchor"),
                    BinderSyntaxObservation::Literal(_)
                )
                && matches!(reader.at(sp, 1).expect("shape index is in bounds"), BinderSyntaxObservation::Op(operation) if matches!(reader.operation(operation), OptionalOperationObservation::Sep { source: None, .. }))
                && matches!(
                    reader.at(sp, 2).expect("shape index is in bounds"),
                    BinderSyntaxObservation::Literal(_)
                );
            let class5_shape_4 = reader.sequence_len(sp) == 4
                && matches!(
                    reader.at(sp, 0).expect("nonempty syntax has an anchor"),
                    BinderSyntaxObservation::Literal(_)
                )
                && matches!(reader.at(sp, 1).expect("shape index is in bounds"), BinderSyntaxObservation::Literal(s) if s == "(")
                && matches!(reader.at(sp, 2).expect("shape index is in bounds"), BinderSyntaxObservation::Op(operation) if matches!(reader.operation(operation), OptionalOperationObservation::Sep { source: None, .. }))
                && matches!(
                    reader.at(sp, 3).expect("shape index is in bounds"),
                    BinderSyntaxObservation::Literal(_)
                );
            if class5_shape_3 || class5_shape_4 {
                return None;
            }
        }
    }

    // Build a map: param name → (kind, type_info).
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

    for leaf in TermParamLeaves::new(reader, tc, false) {
        let in_optional = leaf.is_optional;
        if in_optional {
            match leaf.kind {
                TermParamLeafKind::Simple { name, .. }
                | TermParamLeafKind::Abstraction { binder: name, .. }
                | TermParamLeafKind::MultiAbstraction { binder: name, .. }
                | TermParamLeafKind::GuardBody { name, .. } => {
                    optional_params.insert(name.to_string());
                },
            }
        }
        match leaf.kind {
            TermParamLeafKind::Simple { name, ty, .. } => match reader.ty(ty) {
                BinderTypeObservation::Base(ident) => {
                    let cat = ident.to_string();
                    param_cats.push(cat.clone());
                    param_map.insert(name.to_string(), ParamKind::Simple { cat });
                },
                // B9 / Class 2 (2026-05-08): SimpleCollection. Supports
                // Vec / HashBag / HashSet / HashMap over a Base element
                // type. HashMap uses the grammar's key/value separator
                // while preserving the drained `[k0, v0, k1, v1, ...]`
                // invariant.
                BinderTypeObservation::Collection { coll_type, element } => {
                    match (coll_type, reader.ty(element)) {
                        (CollectionType::Vec, BinderTypeObservation::Base(elem))
                        | (CollectionType::HashBag, BinderTypeObservation::Base(elem))
                        | (CollectionType::HashSet, BinderTypeObservation::Base(elem))
                        | (CollectionType::HashMap, BinderTypeObservation::Base(elem)) => {
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
                BinderTypeObservation::Map { key, value } => {
                    match (reader.ty(key), reader.ty(value)) {
                        (
                            BinderTypeObservation::Base(k_ident),
                            BinderTypeObservation::Base(v_ident),
                        ) if reader.names_equal(k_ident, v_ident) => {
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
                    }
                },
                _ => return None,
            },
            TermParamLeafKind::Abstraction { binder, body, ty, .. } => {
                let bcat = arrow_codomain_name(reader, ty)?;
                body_cat = Some(bcat.clone());
                has_binder = true;
                param_map.insert(binder.to_string(), ParamKind::Binder);
                param_map.insert(body.to_string(), ParamKind::Body { cat: bcat });
                if in_optional {
                    optional_params.insert(body.to_string());
                }
            },
            TermParamLeafKind::MultiAbstraction { binder, body, ty, .. } => {
                let bcat = arrow_codomain_name(reader, ty)?;
                body_cat = Some(bcat.clone());
                has_binder = true;
                is_multi = true;
                param_map.insert(binder.to_string(), ParamKind::BinderList);
                param_map.insert(body.to_string(), ParamKind::Body { cat: bcat });
                if in_optional {
                    optional_params.insert(body.to_string());
                }
            },
            TermParamLeafKind::GuardBody { name, .. } => {
                param_map.insert(name.to_string(), ParamKind::Guard);
            },
        }
    }

    // A leading Param is a real first action argument. It used to be silently
    // dropped because the position walker skips the dispatch anchor. Category
    // values descend into their parser; an inert Ident uses the existing
    // leading token-family capture transition. Collection/binder/guard params
    // still require their dedicated operators.
    let (leading_category, leading_ident_capture) =
        match reader.at(sp, 0).expect("nonempty syntax has an anchor") {
            BinderSyntaxObservation::Param(name) => match param_map.get(&name.to_string())? {
                ParamKind::Body { cat } | ParamKind::Simple { cat }
                    if mettail_ast::grammar::NonTerminalKind::classify(cat)
                        != mettail_ast::grammar::NonTerminalKind::Ident =>
                {
                    (Some(cat.clone()), None)
                },
                ParamKind::Simple { cat }
                    if mettail_ast::grammar::NonTerminalKind::classify(cat)
                        == mettail_ast::grammar::NonTerminalKind::Ident =>
                {
                    (None, Some(name.to_string()))
                },
                _ => return None,
            },
            _ => (None, None),
        };

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
    if let Some(cat) = &leading_category {
        action_args.push(ActionArgKind::Term(cat.clone()));
    }
    if let Some(param_name) = &leading_ident_capture {
        action_args.push(ActionArgKind::TokenText { param_name: param_name.clone() });
    }
    // L9-3: a LEADING custom-kind capture (sp[0] is a TokenKind) is consumed by
    // the prefix dispatch, which interns its ActionArg::Token FIRST. The
    // `.skip(1)` loop treats sp[0] as the trigger and does not re-push it, so
    // PREPEND its TokenText arg here — action_args = [leading, …positions]
    // matches the runtime intern order (else the action arity is off by one).
    if let BinderSyntaxObservation::TokenKind { name, bind } =
        reader.at(sp, 0).expect("nonempty syntax has an anchor")
    {
        let param_name = bind
            .as_ref()
            .map(|b| b.to_string())
            .unwrap_or_else(|| format!("__tok_{}", name));
        action_args.push(ActionArgKind::TokenText { param_name });
    }
    // L9-4: a LEADING guest body (sp[0] is `*flt(node,…)`) is consumed by the
    // prefix dispatch, which interns its ActionArg::GuestBody FIRST — prepend
    // its arg here (same off-by-one reasoning as the leading token capture).
    if let BinderSyntaxObservation::GuestBody { bind, kind, .. } =
        reader.at(sp, 0).expect("nonempty syntax has an anchor")
    {
        action_args.push(ActionArgKind::GuestBody { param_name: bind.to_string(), kind });
    }
    let mut skip_next: bool = false;
    // Phase 4 #1.B (2026-05-11): track collection-slot index. Each
    // SimpleCollection / Class-3 BinderListLoop push increments.
    // Stamped into `CollectionSepInfo.slot_idx` / (eventually) the
    // CollectionMarker symbol's `bp` field via emit_binder_rule_body
    // so the walker's per-CollectionMarker lookups can disambiguate
    // sibling slots within the same rule.
    let mut collection_slots_so_far: u8 = 0;
    // Unique preorder identity for every optional group in this rule, including
    // groups nested inside other optional or binder-list bodies.
    let mut next_optional_group_idx: u32 = 0;
    for i in 1..reader.sequence_len(sp) {
        let item = reader.at(sp, i).expect("syntax cursor is in bounds");
        if skip_next {
            skip_next = false;
            continue;
        }
        match item {
            BinderSyntaxObservation::Literal(text) => {
                positions.push(BinderPosition::Literal(text.to_owned()));
            },
            // L9-3: a `w@Word` custom-kind capture — push a TokenKindCapture
            // position + a paired TokenText action arg (mirrors the Param→
            // position+arg pairing). An @-less capture synthesizes __tok_<name>
            // (D-5). S2.2 makes any rule containing a TokenKind a multi-step
            // ("binder") rule so it routes through this position machinery.
            BinderSyntaxObservation::TokenKind { name, bind } => {
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
            BinderSyntaxObservation::GuestBody { open, close, bind, kind } => {
                positions.push(BinderPosition::GuestBodyCapture {
                    open_kind: open.to_string(),
                    nested_open_kinds: guest_nested_open_kinds(&open.to_string()),
                    close_kind: close.to_string(),
                    param_name: bind.to_string(),
                });
                action_args.push(ActionArgKind::GuestBody { param_name: bind.to_string(), kind });
            },
            BinderSyntaxObservation::Param(name) => {
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
            BinderSyntaxObservation::Op(operation) => match reader.operation(operation) {
                OptionalOperationObservation::Sep { collection, separator, source: None } => {
                    let n = collection.to_string();
                    let kind = param_map.get(&n)?;
                    match kind {
                        ParamKind::BinderList => {
                            // Find the next Literal in syntax_pattern — that's
                            // the close delim of the binder-list loop.
                            let close = match reader.at(sp, i + 1) {
                                Some(BinderSyntaxObservation::Literal(text)) => text.to_owned(),
                                _ => return None,
                            };
                            positions.push(BinderPosition::BinderListLoop {
                                separator: separator.to_owned(),
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
                            // A following literal is an explicit terminator owned
                            // by the repetition. When no literal follows, the
                            // repetition is open-ended and yields to the enclosing
                            // continuation through a non-consuming pop. This is
                            // the direct EBNF meaning of a trailing
                            // `xs.*sep(..)`; requiring a synthetic close made the
                            // data-faithful vector form inexpressible.
                            let (close, absorbs_following_literal) = match reader.at(sp, i + 1) {
                                Some(BinderSyntaxObservation::Literal(text)) => {
                                    (text.to_owned(), true)
                                },
                                _ => (String::new(), false),
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
                                    separator: separator.to_owned(),
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
                            // Skip only a concrete close Literal at i+1 — an
                            // open-ended repetition leaves the following syntax
                            // position to the ordinary binder continuation.
                            skip_next = absorbs_following_literal;
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
                OptionalOperationObservation::Sep {
                    collection: _,
                    separator,
                    source: Some(source_op),
                } => {
                    // Source must be Map { source: Zip{left,right}, params, body }.
                    let (zip_left, zip_right, map_params, map_body) = match reader
                        .map_zip_operation(source_op)
                    {
                        MapZipObservation::Map { source, params, body } => match reader
                            .map_zip_operation(source)
                        {
                            MapZipObservation::Zip { left, right } => (left, right, params, body),
                            _ => return None,
                        },
                        _ => return None,
                    };
                    if reader.names_len(map_params) != 2 {
                        return None;
                    }
                    // Validate left/right param kinds:
                    //   - left must be SimpleCollection (the names accumulator)
                    //   - right must be BinderList (the multi-binder)
                    let (collection_elem_cat,) = match param_map.get(&zip_left.to_string()) {
                        Some(ParamKind::SimpleCollection { elem_cat, .. }) => (elem_cat.clone(),),
                        _ => return None,
                    };
                    if !matches!(param_map.get(&zip_right.to_string()), Some(ParamKind::BinderList))
                    {
                        return None;
                    }
                    // map_params[0] alias for the names-element; map_params[1]
                    // alias for the binder slot. Inside the body, Param(p1)
                    // refers to a Name parse, Param(p2) refers to the binder
                    // ident capture.
                    let map_param_n = reader
                        .name_at(map_params, 0)
                        .expect("two map aliases exist")
                        .to_string();
                    let map_param_x = reader
                        .name_at(map_params, 1)
                        .expect("two map aliases exist")
                        .to_string();
                    let close = match reader.at(sp, i + 1) {
                        Some(BinderSyntaxObservation::Literal(text)) => text.to_owned(),
                        _ => return None,
                    };
                    // Walk the map body and build the per-iteration positions
                    // used by the Class 3 dispatch.
                    let mut inner_positions: Vec<BinderPosition> = Vec::new();
                    let mut inner_action_args: Vec<ActionArgKind> = Vec::new();
                    for inner_index in 0..reader.sequence_len(map_body) {
                        let inner_item = reader
                            .at(map_body, inner_index)
                            .expect("map body cursor is in bounds");
                        match inner_item {
                            BinderSyntaxObservation::Literal(text) => {
                                inner_positions.push(BinderPosition::Literal(text.to_owned()));
                            },
                            BinderSyntaxObservation::TokenKind { .. }
                            | BinderSyntaxObservation::GuestBody { .. } => return None,
                            BinderSyntaxObservation::Param(p_name) => {
                                let pn = p_name.to_string();
                                if pn == map_param_n {
                                    // Names-element: parse as Name, splice into accumulator.
                                    inner_positions.push(BinderPosition::ParamParse {
                                        cat: collection_elem_cat.clone(),
                                        collection: Some(CollectionSepInfo {
                                            separator: separator.to_owned(),
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
                            BinderSyntaxObservation::Op(_) => return None, // nested Op out of pilot.
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
                        separator: separator.to_owned(),
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
                OptionalOperationObservation::Opt { inner } => {
                    let group_idx = next_optional_group_idx;
                    next_optional_group_idx = next_optional_group_idx.checked_add(1)?;
                    let (inner_positions, inner_action_args) = classify_optional_body(
                        reader,
                        inner,
                        &param_map,
                        &mut next_optional_group_idx,
                        &mut collection_slots_so_far,
                        &mut guest_nested_open_kinds,
                        |kind| kv_sep_for(kind, declared_delims),
                    )?;
                    if inner_positions.is_empty() {
                        return None;
                    }
                    let first_token_set = optional_first_token_set(&inner_positions);
                    positions.push(BinderPosition::OptionalGroup {
                        positions: inner_positions,
                        group_idx,
                        first_token_set,
                    });
                    action_args.push(ActionArgKind::Optional(inner_action_args));
                },
                // Op(Map/Zip) or chained ops — Phase 5c territory; skip for now.
                OptionalOperationObservation::Other(_) => return None,
            },
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
    let has_leading_capture = leading_ident_capture.is_some()
        || matches!(
            reader.at(sp, 0).expect("nonempty syntax has an anchor"),
            BinderSyntaxObservation::TokenKind { .. } | BinderSyntaxObservation::GuestBody { .. }
        );
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
        label: reader.label(rule).to_string(),
        result_cat: reader.category(rule).to_string(),
        leading_category,
        leading_ident_capture,
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
fn arrow_codomain_name<'syntax, R: BinderRuleReader<'syntax>>(
    reader: &R,
    ty: R::Type,
) -> Option<String> {
    match reader.ty(ty) {
        BinderTypeObservation::Arrow { codomain, .. } => match reader.ty(codomain) {
            BinderTypeObservation::Base(ident) => Some(ident.to_string()),
            _ => None,
        },
        _ => None,
    }
}
