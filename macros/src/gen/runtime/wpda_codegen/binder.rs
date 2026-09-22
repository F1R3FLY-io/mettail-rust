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

use mettail_ast::grammar::{DelimitedRegionKind, GrammarRule, PatternOp, SyntaxExpr, TermParam};
#[cfg(test)]
use mettail_ast::language::CollectionDelimiters;
use mettail_ast::language::LanguageDef;
use mettail_ast::types::{CollectionType, TypeExpr};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashMap;
use syn::Ident;

use super::builtin_metadata::classify_unary_prefix_shape;
use super::collection::kv_sep_for;

/// Emit a mid-rule token-family capture without collapsing a lexical lattice
/// to its primary edge.
///
/// Contextual keywords are intentionally represented by more than one lexer
/// edge (for example, both `Fixed("PPar")` and `Ident("PPar")`).  A grammar
/// capture such as `label@Ident` is therefore a predicate over every outgoing
/// edge, not merely `peek_kind`.  Each surviving edge remains explicit in the
/// WPDA branch and carries its lexer alternative index and target node through
/// application, which keeps DAG advancement and semiring tie-breaking exact.
fn emit_token_capture_and_replace(
    kind_name: &str,
    symbol: TokenStream,
    new_state: TokenStream,
) -> TokenStream {
    quote! {{
        let __capture_kind_name: &'static str = #kind_name;
        let __capture_branches =
            mettail_prattail::wpda_runtime::matching_token_capture_edges(
                tokens,
                _pos,
                __capture_kind_name,
            )
            .into_iter()
            .map(|__edge| {
                let __open_len =
                    u16::try_from(__edge.text.len()).expect("token length exceeds u16");
                let __capture_symbol = #symbol;
                mettail_prattail::wpda_walker::ForkBranch {
                    weight: lex_w_alt_with_len(
                        __open_len,
                        0.0,
                        __capture_symbol.category_src_idx,
                        __capture_symbol.rule_index_in_category,
                        __edge.alt_idx,
                    ),
                    symbol: __capture_symbol,
                    new_state: #new_state,
                    action_kind:
                        mettail_prattail::wpda_walker::ForkActionKind::ConsumeTokenKindAtAndReplace {
                            alt_idx: __edge.alt_idx,
                            kind_name: __capture_kind_name.to_string(),
                            kind: __edge.kind,
                            text: __edge.text,
                            next_pos: __edge.next_pos,
                        },
                }
            })
            .collect();
        return WpdaStepAction::Fork {
            branches: __capture_branches,
            consume_trigger: false,
        };
    }}
}

fn optional_delimited_region_extract(
    value: &Ident,
    parent: &Ident,
    kind: DelimitedRegionKind,
) -> TokenStream {
    let DelimitedRegionKind::Flt = kind;
    let gb = format_ident!("__guest_body");
    let build = flt_node_from_guest_body(&gb);
    quote! {
        let #value: Option<std::sync::Arc<mettail_runtime::FltNode>> =
            match #parent.as_mut() {
                Some(parent) => parent.next().and_then(|arg| {
                    arg.as_guest_body().and_then(|#gb| {
                        (#build).ok().map(std::sync::Arc::new)
                    })
                }),
                None => None,
            };
    }
}

fn required_delimited_region_extract(value: &Ident, kind: DelimitedRegionKind) -> TokenStream {
    let DelimitedRegionKind::Flt = kind;
    let gb = format_ident!("__guest_body");
    let build = flt_node_from_guest_body(&gb);
    quote! {
        let #value: std::sync::Arc<mettail_runtime::FltNode> = match iter.next() {
            Some(arg) => match arg.as_guest_body() {
                Some(#gb) => match #build {
                    Ok(node) => std::sync::Arc::new(node),
                    Err(_) => return,
                },
                None => return,
            },
            None => return,
        };
    }
}

fn flt_node_from_guest_body(gb: &Ident) -> TokenStream {
    quote! {
        mettail_runtime::FltNode::from_structural_parts(
            #gb.selector_name.clone(),
            #gb.category.clone(),
            #gb.open_src.clone(),
            #gb.body_src.clone(),
            #gb.holes.iter().map(|hole| mettail_runtime::FltHole {
                id: mettail_runtime::FltHoleId(hole.id),
                name: hole.name.clone(),
                category: hole.category.clone(),
                first_occurrence: mettail_runtime::FltSourceRange {
                    start: hole.first_occurrence.start,
                    end: hole.first_occurrence.end,
                },
            }).collect(),
            #gb.pieces.iter().map(|piece| match piece {
                mettail_prattail::wpda_runtime::GuestBodyPiece::Text { text, range } =>
                    mettail_runtime::FltTemplatePiece::Text {
                        text: text.clone(),
                        range: mettail_runtime::FltSourceRange {
                            start: range.start,
                            end: range.end,
                        },
                    },
                mettail_prattail::wpda_runtime::GuestBodyPiece::Hole { id, range } =>
                    mettail_runtime::FltTemplatePiece::Hole {
                        id: mettail_runtime::FltHoleId(*id),
                        range: mettail_runtime::FltSourceRange {
                            start: range.start,
                            end: range.end,
                        },
                    },
            }).collect(),
            #gb.close_src.clone(),
            #gb.position,
        )
    }
}

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
    mettail_prattail::wpda_rule_analysis::binder::build_prefix_bp_map_with(
        per_cat,
        &bp_table,
        |rule| classify_unary_prefix_shape(rule).is_some(),
        |rule| (rule.category.to_string(), rule.prefix_bp),
    )
}

#[cfg(test)]
use mettail_prattail::wpda_rule_analysis::binder::first_param_cat_from_positions;
use mettail_prattail::wpda_rule_analysis::binder::optional::{
    BinderSyntaxObservation, BinderSyntaxReader, OptionalOperationObservation,
};
#[cfg(test)]
use mettail_prattail::wpda_rule_analysis::binder::ParamKind;
pub(crate) use mettail_prattail::wpda_rule_analysis::binder::{
    binder_initial_body_cat, lookup_src_idx, required_top_cat_after_position,
};
pub use mettail_prattail::wpda_rule_analysis::binder::{
    ActionArgKind, BinderPosition, BinderShape, CollectionSepInfo,
};

#[cfg(test)]
#[path = "../../../../tests/support/binder_model_lifecycle.rs"]
mod model_lifecycle_tests;

#[cfg(test)]
#[path = "../../../../tests/support/binder_classifier_projection.rs"]
mod classifier_projection_tests;

#[cfg(test)]
#[path = "../../../../tests/support/binder_traversal_recursive_oracle.rs"]
mod traversal_recursive_oracle;

/// Caller continuation for a nested optional or binder-list frame.
///
/// The generated PDA stores this continuation in the GSS symbol immediately
/// below the entered frame. Keeping it out of `WpdaState::BinderListLoop`
/// makes the state frame-local and permits arbitrary Optional/BinderList
/// nesting without caller-specific fields or native recursion.
#[derive(Clone, Copy)]
enum TraversalResume {
    Rule { next_pos: u8 },
    Optional { group_idx: u32, next_sub_pos: u32 },
    BinderList { frame_idx: u32, next_sub_pos: u32 },
}

struct BinderListSite<'position> {
    separator: &'position str,
    close: &'position str,
    inner_positions: &'position [BinderPosition],
    collection_param_cat: &'position Option<String>,
    slot_idx: u8,
    frame_idx: u32,
    resume: TraversalResume,
}

struct OptionalSite<'position> {
    positions: &'position [BinderPosition],
    group_idx: u32,
    first_token_set: &'position [String],
    resume: TraversalResume,
}

struct TraversalSites<'position> {
    binder_lists: Vec<BinderListSite<'position>>,
    optionals: Vec<OptionalSite<'position>>,
    binder_frame_indices: HashMap<*const BinderPosition, u32>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum TraversalMarkerCoordinate {
    Optional { group_idx: u32, sub_pos: u32 },
    BinderList { frame_idx: u32, sub_pos: u32 },
}

pub(crate) struct TraversalMarkerTable {
    ids: HashMap<(u16, u16, TraversalMarkerCoordinate), u32>,
    optional_metadata: Vec<(u32, u16, u16, u32, u32)>,
    binder_metadata: Vec<(u32, u16, u16, u32, u32)>,
}

impl TraversalMarkerTable {
    pub(crate) fn build(language: &LanguageDef, per_cat: &[Vec<GrammarRule>]) -> Self {
        let mut ids = HashMap::new();
        let mut optional_metadata = Vec::new();
        let mut binder_metadata = Vec::new();
        let mut next_marker_id = 0u32;

        for (cat_i, rules) in per_cat.iter().enumerate() {
            for (rule_i, rule) in rules.iter().enumerate() {
                let Some(shape) = classify_binder_in(rule, language) else {
                    continue;
                };
                let result_src_idx = cat_i as u16;
                let rule_idx = rule_i as u16;
                let sites = traversal_sites(&shape.positions);
                for OptionalSite { positions, group_idx, .. } in sites.optionals {
                    let final_sub_pos = u32::try_from(positions.len() + 1)
                        .expect("optional marker count exceeds compact addressability");
                    for sub_pos in 0..=final_sub_pos {
                        let marker_id = next_marker_id;
                        next_marker_id = next_marker_id
                            .checked_add(1)
                            .expect("traversal marker table exceeds u32 addressability");
                        let coordinate = TraversalMarkerCoordinate::Optional { group_idx, sub_pos };
                        ids.insert((result_src_idx, rule_idx, coordinate), marker_id);
                        optional_metadata.push((
                            marker_id,
                            result_src_idx,
                            rule_idx,
                            group_idx,
                            sub_pos,
                        ));
                    }
                }
                for BinderListSite { inner_positions, frame_idx, .. } in sites.binder_lists {
                    let final_sub_pos = u32::try_from(inner_positions.len() + 1)
                        .expect("binder marker count exceeds compact addressability");
                    for sub_pos in 0..=final_sub_pos {
                        let marker_id = next_marker_id;
                        next_marker_id = next_marker_id
                            .checked_add(1)
                            .expect("traversal marker table exceeds u32 addressability");
                        let coordinate =
                            TraversalMarkerCoordinate::BinderList { frame_idx, sub_pos };
                        ids.insert((result_src_idx, rule_idx, coordinate), marker_id);
                        binder_metadata.push((
                            marker_id,
                            result_src_idx,
                            rule_idx,
                            frame_idx,
                            sub_pos,
                        ));
                    }
                }
            }
        }

        Self { ids, optional_metadata, binder_metadata }
    }

    fn id(&self, result_src_idx: u16, rule_idx: u16, coordinate: TraversalMarkerCoordinate) -> u32 {
        self.ids[&(result_src_idx, rule_idx, coordinate)]
    }
}

/// Build the recursive position forest's flat PDA-frame table iteratively.
/// Sites are emitted in deterministic preorder; depth is represented by the
/// heap-backed `pending` worklist rather than the native call stack.
fn traversal_sites(positions: &[BinderPosition]) -> TraversalSites<'_> {
    struct Pending<'position> {
        position: &'position BinderPosition,
        resume: TraversalResume,
    }

    let mut pending = Vec::with_capacity(positions.len());
    for (idx, position) in positions.iter().enumerate().rev() {
        pending.push(Pending {
            position,
            resume: TraversalResume::Rule { next_pos: (idx + 2) as u8 },
        });
    }

    let mut binder_lists = Vec::new();
    let mut optionals = Vec::new();
    let mut binder_frame_indices = HashMap::new();
    while let Some(Pending { position, resume }) = pending.pop() {
        match position {
            BinderPosition::OptionalGroup { positions, group_idx, first_token_set } => {
                optionals.push(OptionalSite {
                    positions,
                    group_idx: *group_idx,
                    first_token_set,
                    resume,
                });
                for (idx, child) in positions.iter().enumerate().rev() {
                    pending.push(Pending {
                        position: child,
                        resume: TraversalResume::Optional {
                            group_idx: *group_idx,
                            next_sub_pos: (idx + 2) as u32,
                        },
                    });
                }
            },
            BinderPosition::BinderListLoop {
                separator,
                close,
                inner_positions,
                collection_param_cat,
                slot_idx,
                ..
            } => {
                let frame_idx = u32::try_from(binder_lists.len())
                    .expect("binder-list frame count exceeds compact marker addressability");
                binder_frame_indices.insert(position as *const BinderPosition, frame_idx);
                binder_lists.push(BinderListSite {
                    separator,
                    close,
                    inner_positions,
                    collection_param_cat,
                    slot_idx: *slot_idx,
                    frame_idx,
                    resume,
                });
                let last = inner_positions.len().saturating_sub(1);
                for (idx, child) in inner_positions.iter().enumerate().rev() {
                    pending.push(Pending {
                        position: child,
                        resume: TraversalResume::BinderList {
                            frame_idx,
                            next_sub_pos: if idx == last { 0 } else { (idx + 2) as u32 },
                        },
                    });
                }
            },
            _ => {},
        }
    }

    TraversalSites {
        binder_lists,
        optionals,
        binder_frame_indices,
    }
}

fn binder_list_frame_indices(positions: &[BinderPosition]) -> HashMap<*const BinderPosition, u32> {
    traversal_sites(positions).binder_frame_indices
}

fn traversal_resume_symbol(
    resume: TraversalResume,
    result_src_idx: u16,
    rule_idx: u16,
    markers: &TraversalMarkerTable,
) -> TokenStream {
    match resume {
        TraversalResume::Rule { next_pos } => quote! {
            StackSymbolV2::rule_at(
                #result_src_idx, #rule_idx, #next_pos, Some(*outer_bp),
            )
        },
        TraversalResume::Optional { group_idx, next_sub_pos } => {
            let marker_id = markers.id(
                result_src_idx,
                rule_idx,
                TraversalMarkerCoordinate::Optional { group_idx, sub_pos: next_sub_pos },
            );
            quote! { StackSymbolV2::optional_group_at(#marker_id, *outer_bp) }
        },
        TraversalResume::BinderList { frame_idx, next_sub_pos } => {
            let marker_id = markers.id(
                result_src_idx,
                rule_idx,
                TraversalMarkerCoordinate::BinderList { frame_idx, sub_pos: next_sub_pos },
            );
            quote! { StackSymbolV2::binder_list_loop_at(#marker_id, *outer_bp) }
        },
    }
}

/// Emit the shared entry transition for a binder-list frame. The caller's
/// current marker is replaced by `resume_symbol` before control enters the
/// frame, so completion can always return through `Unwinding` regardless of
/// whether the caller is a rule, optional group, or another binder-list.
fn emit_binder_list_entry(
    position: &BinderPosition,
    frame_idx: u32,
    resume_symbol: &TokenStream,
    result_src_idx: u16,
    rule_idx: u16,
) -> TokenStream {
    let BinderPosition::BinderListLoop {
        close,
        collection_param_cat,
        allow_empty,
        allow_multi,
        slot_idx,
        ..
    } = position
    else {
        return quote! { WpdaStepAction::Idle };
    };

    if !*allow_empty && !*allow_multi && collection_param_cat.is_none() {
        return quote! {
            WpdaStepAction::Fork {
                branches: vec![mettail_prattail::wpda_walker::ForkBranch {
                    symbol: #resume_symbol,
                    weight: lex_one(),
                    new_state: WpdaState::Unwinding,
                    action_kind:
                        mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeBinderIdentAndReplaceWithEffect {
                            start_scope: true,
                            effect: mettail_prattail::wpda_walker::BuilderDelta::EndBinderScope,
                        },
                }],
                consume_trigger: false,
            }
        };
    }

    if collection_param_cat.is_some() {
        let empty_branch = allow_empty.then(|| quote! {
            mettail_prattail::wpda_walker::ForkBranch {
                symbol: #resume_symbol,
                weight: lex_w(0.0, #result_src_idx, #rule_idx),
                new_state: WpdaState::Unwinding,
                action_kind:
                    mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeAndReplaceWithMultipleEffects {
                        expected_text: #close.to_string(),
                        effects: vec![
                            mettail_prattail::wpda_walker::BuilderDelta::StartCollection,
                            mettail_prattail::wpda_walker::BuilderDelta::PushCollectionId { id: #slot_idx },
                            mettail_prattail::wpda_walker::BuilderDelta::StartBinderScope {
                                names: Vec::new(),
                            },
                            mettail_prattail::wpda_walker::BuilderDelta::EndBinderScope,
                        ],
                    },
            },
        });
        return quote! {
            WpdaStepAction::Fork {
                branches: vec![
                    #empty_branch
                    mettail_prattail::wpda_walker::ForkBranch {
                        symbol: StackSymbolV2::collection_marker(
                            #result_src_idx, #rule_idx, #slot_idx, 0u8,
                        ),
                        weight: lex_w(mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP, #result_src_idx, #rule_idx),
                        new_state: WpdaState::BinderListLoop {
                            result_src_idx: #result_src_idx,
                            rule_idx: #rule_idx,
                            frame_idx: #frame_idx,
                            outer_bp: *outer_bp,
                            sub_pos: 0u32,
                        },
                        action_kind:
                            mettail_prattail::wpda_walker::ForkActionKind::ReplaceAndPush {
                                replace_symbol: #resume_symbol,
                            },
                    },
                ],
                consume_trigger: false,
            }
        };
    }

    let empty_branch = allow_empty.then(|| quote! {
        mettail_prattail::wpda_walker::ForkBranch {
            symbol: #resume_symbol,
            weight: lex_w(0.0, #result_src_idx, #rule_idx),
            new_state: WpdaState::Unwinding,
            action_kind:
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
    });
    quote! {
        WpdaStepAction::Fork {
            branches: vec![
                #empty_branch
                mettail_prattail::wpda_walker::ForkBranch {
                    symbol: #resume_symbol,
                    weight: lex_w(mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP, #result_src_idx, #rule_idx),
                    new_state: WpdaState::BinderListLoop {
                        result_src_idx: #result_src_idx,
                        rule_idx: #rule_idx,
                        frame_idx: #frame_idx,
                        outer_bp: *outer_bp,
                        sub_pos: 0u32,
                    },
                    action_kind:
                        mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeBinderIdentAndReplace {
                            start_scope: true,
                        },
                },
            ],
            consume_trigger: false,
        }
    }
}

struct MacroBinderSyntaxReader;

impl<'syntax> BinderSyntaxReader<'syntax> for MacroBinderSyntaxReader {
    type Sequence = &'syntax [SyntaxExpr];
    type Name = &'syntax Ident;
    type Operation = &'syntax PatternOp;

    fn sequence_len(&self, sequence: Self::Sequence) -> usize {
        sequence.len()
    }

    fn at(
        &self,
        sequence: Self::Sequence,
        index: usize,
    ) -> Option<BinderSyntaxObservation<'syntax, Self::Name, Self::Operation>> {
        Some(match sequence.get(index)? {
            SyntaxExpr::Literal(text) => BinderSyntaxObservation::Literal(text),
            SyntaxExpr::Param(name) => BinderSyntaxObservation::Param(name),
            SyntaxExpr::TokenKind { name, bind } => {
                BinderSyntaxObservation::TokenKind { name, bind: bind.as_ref() }
            },
            SyntaxExpr::GuestBody { open, close, bind, kind } => {
                BinderSyntaxObservation::GuestBody { open, close, bind, kind: *kind }
            },
            SyntaxExpr::Op(operation) => BinderSyntaxObservation::Op(operation),
        })
    }

    fn operation(
        &self,
        operation: Self::Operation,
    ) -> OptionalOperationObservation<'syntax, Self::Name, Self::Sequence, Self::Operation> {
        match operation {
            PatternOp::Opt { inner } => OptionalOperationObservation::Opt { inner },
            PatternOp::Sep { collection, separator, source } => OptionalOperationObservation::Sep {
                collection,
                separator,
                source: source.as_deref(),
            },
            _ => OptionalOperationObservation::Other(operation),
        }
    }
}

#[cfg(test)]
fn classify_optional_body(
    root: &[SyntaxExpr],
    language: &LanguageDef,
    param_map: &HashMap<String, ParamKind>,
    declared_delims: Option<&CollectionDelimiters>,
    next_group_idx: &mut u32,
    collection_slots_so_far: &mut u8,
) -> Option<(Vec<BinderPosition>, Vec<ActionArgKind>)> {
    mettail_prattail::wpda_rule_analysis::binder::optional::classify_optional_body(
        &MacroBinderSyntaxReader,
        root,
        param_map,
        next_group_idx,
        collection_slots_so_far,
        |open| super::guest_body_nested_open_kinds(language, open),
        |kind| kv_sep_for(kind, declared_delims),
    )
}

/// Reuse the same shallow declaration reader as all existing macro consumers.
impl<'syntax> mettail_prattail::wpda_rule_analysis::binder::term_param::TermParamReader<'syntax>
    for MacroBinderSyntaxReader
{
    type Parameters = &'syntax [TermParam];
    type Param = &'syntax TermParam;
    type Name = &'syntax Ident;
    type Type = &'syntax TypeExpr;

    fn params_len(&self, params: Self::Parameters) -> usize {
        crate::gen::term_param_walk::MacroTermParamReader.params_len(params)
    }
    fn param_at(&self, params: Self::Parameters, index: usize) -> Option<Self::Param> {
        crate::gen::term_param_walk::MacroTermParamReader.param_at(params, index)
    }
    fn param(
        &self,
        param: Self::Param,
    ) -> mettail_prattail::wpda_rule_analysis::binder::term_param::TermParamObservation<
        Self::Name,
        Self::Parameters,
        Self::Type,
    > {
        crate::gen::term_param_walk::MacroTermParamReader.param(param)
    }
}

impl<'syntax> mettail_prattail::wpda_rule_analysis::binder::rule::BinderRuleReader<'syntax>
    for MacroBinderSyntaxReader
{
    type Rule = &'syntax GrammarRule;
    type Names = &'syntax [Ident];

    fn term_context(&self, rule: Self::Rule) -> Option<Self::Parameters> {
        rule.term_context.as_deref()
    }
    fn syntax_pattern(&self, rule: Self::Rule) -> Option<Self::Sequence> {
        rule.syntax_pattern.as_deref()
    }
    fn label(&self, rule: Self::Rule) -> &'syntax Ident {
        &rule.label
    }
    fn category(&self, rule: Self::Rule) -> &'syntax Ident {
        &rule.category
    }
    fn ty(
        &self,
        ty: Self::Type,
    ) -> mettail_prattail::wpda_rule_analysis::binder::rule::BinderTypeObservation<
        'syntax,
        &'syntax Ident,
        Self::Type,
    > {
        use mettail_prattail::wpda_rule_analysis::binder::rule::BinderTypeObservation as View;
        match ty {
            TypeExpr::Base(name) => View::Base(name),
            TypeExpr::Collection { coll_type, element } => View::Collection { coll_type, element },
            TypeExpr::Map { key, value } => View::Map { key, value },
            TypeExpr::Arrow { codomain, .. } => View::Arrow { codomain },
            _ => View::Other(ty),
        }
    }
    fn names_len(&self, names: Self::Names) -> usize {
        names.len()
    }
    fn name_at(&self, names: Self::Names, index: usize) -> Option<&'syntax Ident> {
        names.get(index)
    }
    fn names_equal(&self, left: &'syntax Ident, right: &'syntax Ident) -> bool {
        left == right
    }
    fn map_zip_operation(
        &self,
        operation: Self::Operation,
    ) -> mettail_prattail::wpda_rule_analysis::binder::rule::MapZipObservation<
        &'syntax Ident,
        Self::Names,
        Self::Sequence,
        Self::Operation,
    > {
        use mettail_prattail::wpda_rule_analysis::binder::rule::MapZipObservation as View;
        match operation {
            PatternOp::Map { source, params, body } => View::Map { source, params, body },
            PatternOp::Zip { left, right } => View::Zip { left, right },
            _ => View::Other(operation),
        }
    }
}

/// Read the macro AST shallowly and execute the shared original classifier.
pub(crate) fn classify_binder_in(
    rule: &GrammarRule,
    language: &LanguageDef,
) -> Option<BinderShape> {
    mettail_prattail::wpda_rule_analysis::binder::rule::classify_binder_in(
        &MacroBinderSyntaxReader,
        rule,
        || {
            language
                .types
                .iter()
                .find(|ty| ty.name == rule.category)
                .and_then(|ty| ty.collection_kind.as_ref())
                .map(|collection| collection.delimiters())
        },
        |open| super::guest_body_nested_open_kinds(language, open),
        kv_sep_for,
    )
}

// ═══════════════════════════════════════════════════════════════════════════
// THE category-index resolver (task #141 G1+G2)
// ═══════════════════════════════════════════════════════════════════════════
//
// ## Why this exists at all, and why it lives beside `lookup_src_idx`
//
// Every emitter that has to turn a category NAME into the `u16` index the
// generated engine keys on wrote its own lookup. Six of them ended the same
// two ways, and both endings are defects:
//
// * `.unwrap_or(0)` — an undeclared category becomes index 0, **the FIRST
//   declared category**. The build SUCCEEDS and ships a parser that sub-parses
//   the wrong category. Measured, not hypothesised: `semantic_actions.rs`'s own
//   comment (the `capture_kind` arm of `emit_infix_action_entry`) records the
//   #131 incident where `Ident` — not a declared category — resolved to index 0,
//   the action entry then advertised "this slot expects a `Num` term" while the
//   extractor at that slot read `as_ident()`, and the arg-shape gate rejected
//   every reading of a rule whose parse was otherwise correct. The user-visible
//   symptom was "no accepting branch reached end of input", **with nothing
//   naming `Ident` anywhere in the diagnostic**.
// * `.unwrap_or_else(|| panic!("mettail: unresolvable category …"))` — the #133
//   hardening, copied verbatim into FOUR places. Under this workspace's
//   `[profile.dev] codegen-backend = "cranelift"` a `panic!` inside the proc
//   macro prints **nothing at all** — measured 2026-07-29, task #141 RED-0:
//   the payload never appears; rustc dies with
//   `fatal runtime error: Rust cannot catch foreign exceptions, aborting`
//   (SIGABRT). So all four copies were four copies of a message no one could
//   ever read.
//
// One resolver, one message, one place to fix it next time. It lives beside
// [`lookup_src_idx`] — the `Option`-returning lookup the same emitters already
// share — precisely so that the next emitter needing a category index finds the
// refusing form in the same glance as the permissive one.
//
// ## The two shapes a caller can be in
//
// * **Token position** — the index is about to be interpolated into emitted
//   code (`category_entry(#idx)`, `output_cat: #idx`, `expected_input_cats:
//   &[#idx, …]`). Such a caller uses [`cat_idx_tokens`], which substitutes a
//   spanned `compile_error!` for the literal. The generated module then refuses
//   to compile and says why, which is the whole point: a `compile_error!` is a
//   TOKEN, rendered by rustc, so unlike a `panic!` it cannot be swallowed by the
//   backend (`wpda_codegen/ident_capture_routing.rs` records the same finding).
// * **Macro-time value position** — the index feeds a data structure consumed
//   later in the same expansion (`SpineItem::ParamParse { cat_src_idx }`).
//   Such a caller uses [`resolve_cat_idx`] directly and decides for itself; see
//   the note at `factoring.rs`'s `binder_items` for the one site in this shape
//   and what it would take to give it a token position.

/// A category name that is not among the language's declared categories.
///
/// Carries everything the diagnostic needs — the offending name, the rule it
/// appears on, the emitter position that asked, and the declared set it was
/// looked up in — so that the message can be rendered ONCE, by
/// [`UnresolvedCategory::message`], rather than at each of six call sites.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UnresolvedCategory {
    /// The category name that could not be resolved.
    category: String,
    /// The grammar rule the name appears on, by LABEL — never by index. A
    /// message that names `rule 7` names nothing a grammar author can act on.
    rule: String,
    /// Where in the emission the lookup happened, e.g.
    /// `"a ParamParse position"`. A short noun phrase, read as
    /// "unresolvable category `X` in <site> of rule `Y`".
    site: &'static str,
    /// The declared category list, rendered. Included in the message because
    /// the single most common cause is a typo, and the fix is visible the
    /// moment the author sees the list they meant to name.
    declared: String,
}

impl UnresolvedCategory {
    /// THE message. Six call sites, one wording.
    pub(crate) fn message(&self) -> String {
        format!(
            "mettail: unresolvable category `{category}` in {site} of rule `{rule}`. \
             `{category}` is not one of this language's declared categories \
             [{declared}], so the generated parser has no category index for it. \
             This refusal replaces a silent fallback to category index 0 — the FIRST \
             declared category — which produced a language that COMPILED and then \
             sub-parsed the wrong category, reporting only \"no accepting branch \
             reached end of input\" (tasks #131, #133, #141). Declare `{category}` in \
             the `types {{ … }}` block, or correct the category name on rule \
             `{rule}`.",
            category = self.category,
            site = self.site,
            rule = self.rule,
            declared = self.declared,
        )
    }

    /// The refusal as emitted code, spanned at `span`.
    ///
    /// `quote_spanned!` rather than `quote!` follows the tree's existing
    /// precedent (`macros/src/gen/native/eval.rs`), so the diagnostic points at
    /// the offending rule rather than at the whole `language!` invocation
    /// wherever the token stream survives to rustc unspilled.
    pub(crate) fn compile_error(&self, span: proc_macro2::Span) -> TokenStream {
        let message = self.message();
        quote::quote_spanned!(span => compile_error!(#message))
    }
}

/// Resolve a category name to the `u16` src index the generated engine keys on,
/// or refuse with everything the diagnostic needs.
///
/// This is [`lookup_src_idx`] plus the obligation to say what went wrong. Prefer
/// it at every new site; prefer [`cat_idx_tokens`] when the result is headed for
/// emitted code.
pub(crate) fn resolve_cat_idx(
    name: &str,
    categories: &[String],
    site: &'static str,
    rule: &str,
) -> Result<u16, UnresolvedCategory> {
    match lookup_src_idx(name, categories) {
        Some(idx) => Ok(idx),
        None => Err(UnresolvedCategory {
            category: name.to_string(),
            rule: rule.to_string(),
            site,
            declared: categories.join(", "),
        }),
    }
}

/// Resolve a category name straight to the tokens an emitter interpolates —
/// the `u16` literal on success, a spanned `compile_error!` on failure.
///
/// The substitution happens exactly where the wrong index would have been used,
/// so the refusal cannot drift away from the site it describes.
pub(crate) fn cat_idx_tokens(
    name: &str,
    categories: &[String],
    site: &'static str,
    rule: &str,
    span: proc_macro2::Span,
) -> TokenStream {
    match resolve_cat_idx(name, categories, site, rule) {
        Ok(idx) => quote! { #idx },
        Err(unresolved) => unresolved.compile_error(span),
    }
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
/// Per-branch `lex_w(0.0, result_src_idx, rule_idx)`
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
                        weight: lex_w(0.0, #result_src_idx, #rule_idx),
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
                        weight: lex_w(0.0, #result_src_idx, #rule_idx),
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
        let branch_count = branches.len();
        let branch_pushes = branches.iter().map(|branch| {
            quote! {
                __binder_trigger_branches.push(#branch);
            }
        });

        arms.push(quote! {
            Some(mettail_prattail::automata::TokenKind::Fixed(__trigger))
                if __trigger == #trigger && state_cat_src_idx == #result_src_idx => {
                let mut __binder_trigger_branches =
                    ::std::vec::Vec::with_capacity(#branch_count);
                #( #branch_pushes )*
                return WpdaStepAction::Fork {
                    branches: __binder_trigger_branches,
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
    markers: &TraversalMarkerTable,
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
    // Rules that may be entered through an already-pushed source
    // CategoryEntry.  This is the exact trigger table for BinderRule's
    // cross-category prelude; deriving it from the rule avoids a delimiter
    // special case in either the generated engine or walker.
    let mut category_entry_trigger_arms: Vec<TokenStream> = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder_in(rule, language) else {
                continue;
            };
            let frame_indices = binder_list_frame_indices(&shape.positions);
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            if let Some(SyntaxExpr::Literal(trigger)) = rule
                .syntax_pattern
                .as_ref()
                .and_then(|pattern| pattern.first())
            {
                category_entry_trigger_arms.push(quote! {
                    (#result_src_idx, #rule_idx) => Some(#trigger),
                });
            }
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
                        let capture = emit_token_capture_and_replace(
                            kind_name,
                            quote! {
                                StackSymbolV2::rule_at(
                                    #result_src_idx,
                                    #rule_idx,
                                    #next_pos,
                                    Some(*outer_bp),
                                )
                            },
                            quote! {
                                WpdaState::BinderRule {
                                    result_src_idx: #result_src_idx,
                                    rule_idx: #rule_idx,
                                    body_src_idx: *_body_src_idx,
                                    outer_bp: *outer_bp,
                                }
                            },
                        );
                        quote! {
                            (#result_src_idx, #rule_idx, #pos) => #capture
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
                        let capture = emit_token_capture_and_replace(
                            "Ident",
                            quote! {
                                StackSymbolV2::rule_at(
                                    #result_src_idx,
                                    #rule_idx,
                                    #next_pos,
                                    Some(*outer_bp),
                                )
                            },
                            quote! {
                                WpdaState::BinderRule {
                                    result_src_idx: #result_src_idx,
                                    rule_idx: #rule_idx,
                                    body_src_idx: *_body_src_idx,
                                    outer_bp: *outer_bp,
                                }
                            },
                        );
                        quote! {
                            (#result_src_idx, #rule_idx, #pos) => #capture
                        }
                    },
                    BinderPosition::GuestBodyCapture {
                        open_kind,
                        nested_open_kinds,
                        close_kind,
                        ..
                    } => {
                        let nested_open_kinds = nested_open_kinds
                            .iter()
                            .map(|kind| quote! { #kind.to_string() })
                            .collect::<Vec<_>>();
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
                                                nested_open_kinds: vec![#(#nested_open_kinds),*],
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
                    BinderPosition::BinderListLoop { .. } => {
                        let frame_idx = frame_indices[&(position as *const BinderPosition)];
                        let resume_symbol = traversal_resume_symbol(
                            TraversalResume::Rule { next_pos },
                            result_src_idx,
                            rule_idx,
                            markers,
                        );
                        let entry = emit_binder_list_entry(
                            position,
                            frame_idx,
                            &resume_symbol,
                            result_src_idx,
                            rule_idx,
                        );
                        quote! {
                            (#result_src_idx, #rule_idx, #pos) => {
                                let _ = tokens.peek_text(_pos);
                                return #entry;
                            }
                        }
                    },
                    BinderPosition::ParamParse { cat, collection } => {
                        // #141 G1: the ONE resolver, the ONE message. A token
                        // position, so an unresolvable category refuses as a
                        // `compile_error!` the user can read rather than as a
                        // `panic!` cranelift swallows whole.
                        let cat_src_idx = cat_idx_tokens(
                            cat,
                            categories,
                            "a ParamParse position",
                            &rule.label.to_string(),
                            rule.label.span(),
                        );
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
                                        // A typed nonterminal occurrence is a strict goal:
                                        // operators may change category while parsing the
                                        // child only when their result can still reach the
                                        // declared child category.  A goal-free entry lets
                                        // a cross-category continuation consume the
                                        // enclosing rule's following literal.
                                        push_symbol: StackSymbolV2::category_entry_goal(#cat_src_idx),
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
                        let group_idx_value = *group_idx;
                        quote! {
                            (#result_src_idx, #rule_idx, #pos) => {
                                return WpdaStepAction::Advance(
                                    WpdaState::OptionalGroup {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        group_idx: #group_idx_value,
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
    // Bound the native skeleton frame independently of the number of binder
    // rules.  The generated control graph is a fixed-depth router followed by
    // one existing per-rule transition leaf; chunks are scanned in the exact
    // former source order, so first-match behavior is unchanged.
    const BINDER_RULES_PER_ROUTER_CHUNK: usize = 24;
    let mut router_helpers: Vec<TokenStream> = Vec::new();
    let mut router_chunk_calls = TokenStream::new();
    for (chunk_idx, chunk) in skeleton_arms
        .chunks(BINDER_RULES_PER_ROUTER_CHUNK)
        .enumerate()
    {
        let chunk_helper = format_ident!("binder_rule_dispatch_chunk_{chunk_idx}");
        router_chunk_calls.extend(quote! {
            if let Some(__action) = self.#chunk_helper(
                result_src_idx,
                rule_idx,
                position,
                _pos,
                tokens,
                _body_src_idx,
                outer_bp,
                frame_ctx,
            ) {
                return Some(__action);
            }
        });
        router_helpers.push(quote! {
            #[inline(never)]
            fn #chunk_helper(
                &self,
                result_src_idx: &u16,
                rule_idx: &u16,
                position: u8,
                _pos: usize,
                tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                _body_src_idx: &u16,
                outer_bp: &u8,
                frame_ctx: mettail_prattail::wpda_runtime::FrameCtx,
            ) -> Option<
                mettail_prattail::wpda_walker::WpdaStepAction<
                    mettail_prattail::automata::lex_weight::LexicographicWeight,
                >,
            > {
                let __action = match (*result_src_idx, *rule_idx, position) {
                    #( #chunk )*
                    _ => return None,
                };
                Some(__action)
            }
        });
    }
    router_helpers.push(quote! {
        #[inline(never)]
        fn binder_rule_dispatch(
            &self,
            result_src_idx: &u16,
            rule_idx: &u16,
            position: u8,
            _pos: usize,
            tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
            _body_src_idx: &u16,
            outer_bp: &u8,
            frame_ctx: mettail_prattail::wpda_runtime::FrameCtx,
        ) -> Option<
            mettail_prattail::wpda_walker::WpdaStepAction<
                mettail_prattail::automata::lex_weight::LexicographicWeight,
            >,
        > {
            #router_chunk_calls
            None
        }
    });

    let body = quote! {
        {
            // A cross-category concrete-rule branch first pushes the source
            // CategoryEntry without consuming.  Pairing BinderRule with that
            // entry is the prelude state: validate this rule's declared
            // leading literal, consume it, and push the selected RuleAt.  The
            // resulting stack is identical to ordinary source-category
            // parsing, so source infix/postfix continuations remain active.
            if let Some(__entry) = frontier_top.filter(|node| {
                node.symbol.kind
                    == mettail_prattail::wpda_runtime::SymbolKind::CategoryEntry
            }) {
                if __entry.symbol.category_src_idx != *result_src_idx {
                    return WpdaStepAction::Error(format!(
                        "binder-rule source category mismatch: expected {}, found {}",
                        result_src_idx,
                        __entry.symbol.category_src_idx,
                    ));
                }
                let __expected_trigger: Option<&'static str> = match (*result_src_idx, *rule_idx) {
                    #( #category_entry_trigger_arms )*
                    _ => None,
                };
                let Some(__expected_trigger) = __expected_trigger else {
                    return WpdaStepAction::Error(format!(
                        "binder rule {}:{} has no literal trigger for category-entry dispatch",
                        result_src_idx,
                        rule_idx,
                    ));
                };
                if tokens.peek_text(_pos) != Some(__expected_trigger) {
                    return WpdaStepAction::Error(format!(
                        "expected binder-rule trigger {:?} at pos {}, found {:?}",
                        __expected_trigger,
                        _pos,
                        tokens.peek_text(_pos),
                    ));
                }
                return WpdaStepAction::ConsumeAndPush {
                    symbol: StackSymbolV2::rule_at(
                        *result_src_idx,
                        *rule_idx,
                        1u8,
                        Some(*outer_bp),
                    ),
                    weight: lex_one(),
                    new_state: WpdaState::BinderRule {
                        result_src_idx: *result_src_idx,
                        rule_idx: *rule_idx,
                        body_src_idx: *_body_src_idx,
                        outer_bp: *outer_bp,
                    },
                    trigger_mode:
                        mettail_prattail::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
                };
            }
            let position: u8 = match frontier_top.map(|n| n.symbol.kind) {
                Some(mettail_prattail::wpda_runtime::SymbolKind::RuleAt(p)) => p,
                _ => return WpdaStepAction::Idle,
            };
            if let Some(__action) = self.binder_rule_dispatch(
                result_src_idx,
                rule_idx,
                position,
                _pos,
                tokens,
                _body_src_idx,
                outer_bp,
                frame_ctx,
            ) {
                return __action;
            }
            match (*result_src_idx, *rule_idx, position) {
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
    let helpers_ts = quote! {
        #(#helpers)*
        #(#router_helpers)*
    };
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
            for BinderListSite {
                inner_positions,
                collection_param_cat,
                slot_idx,
                frame_idx,
                ..
            } in traversal_sites(&shape.positions).binder_lists
            {
                if collection_param_cat.is_none() {
                    continue;
                }
                for (index, inner) in inner_positions.iter().enumerate() {
                    if matches!(inner, BinderPosition::ParamParse { collection: Some(_), .. }) {
                        let cat = cat_i as u16;
                        let rule_idx = rule_i as u16;
                        let target_sub_pos = (index + 2) as u32;
                        arms.push(quote! {
                            (#cat, #rule_idx, #frame_idx, #target_sub_pos) =>
                                Some(#slot_idx),
                        });
                    }
                }
            }
        }
    }
    if arms.is_empty() {
        quote! { None::<u8> }
    } else {
        quote! {
            match (result_src_idx, rule_idx, frame_idx, sub_pos) {
                #(#arms)*
                _ => None::<u8>,
            }
        }
    }
}

pub(crate) fn emit_optional_marker_metadata_lookup(table: &TraversalMarkerTable) -> TokenStream {
    let arms = table.optional_metadata.iter().map(
        |(marker_id, result_src_idx, rule_idx, group_idx, sub_pos)| {
            quote! {
                #marker_id => Some((#result_src_idx, #rule_idx, #group_idx, #sub_pos)),
            }
        },
    );
    quote! {
        match marker_id {
            #(#arms)*
            _ => None::<(u16, u16, u32, u32)>,
        }
    }
}

pub(crate) fn emit_binder_marker_metadata_lookup(table: &TraversalMarkerTable) -> TokenStream {
    let arms = table.binder_metadata.iter().map(
        |(marker_id, result_src_idx, rule_idx, frame_idx, sub_pos)| {
            quote! {
                #marker_id => Some((#result_src_idx, #rule_idx, #frame_idx, #sub_pos)),
            }
        },
    );
    quote! {
        match marker_id {
            #(#arms)*
            _ => None::<(u16, u16, u32, u32)>,
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
            for BinderListSite { collection_param_cat, slot_idx, .. } in
                traversal_sites(&shape.positions).binder_lists
            {
                if collection_param_cat.is_some() {
                    let cat = cat_i as u16;
                    let rule_idx = rule_i as u16;
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

/// Phase 5b + B8 (2026-05-08): emit the body of `WpdaState::BinderListLoop`.
/// The state body dispatches on
/// `(result_src_idx, rule_idx, frame_idx, sub_pos)`.
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
    markers: &TraversalMarkerTable,
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder_in(rule, language) else {
                continue;
            };
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;
            let TraversalSites { binder_lists, binder_frame_indices, .. } =
                traversal_sites(&shape.positions);
            for BinderListSite {
                separator,
                close,
                inner_positions,
                collection_param_cat,
                frame_idx,
                resume,
                ..
            } in binder_lists
            {
                let resume_symbol =
                    traversal_resume_symbol(resume, result_src_idx, rule_idx, markers);

                if collection_param_cat.is_none() {
                    arms.push(quote! {
                        (#result_src_idx, #rule_idx, #frame_idx, 0u32) => {
                            let _ = tokens.peek_text(_pos);
                            return WpdaStepAction::Fork {
                                branches: vec![
                                    mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: #resume_symbol,
                                        weight: lex_w(0.0, #result_src_idx, #rule_idx),
                                        new_state: WpdaState::Unwinding,
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeAndReplaceWithEffect {
                                                expected_text: #close.to_string(),
                                                effect:
                                                    mettail_prattail::wpda_walker::BuilderDelta::EndBinderScope,
                                            },
                                    },
                                    mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::category_entry(0),
                                        weight: lex_w(0.0, #result_src_idx, #rule_idx),
                                        new_state: WpdaState::BinderListLoop {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            frame_idx: #frame_idx,
                                            outer_bp: *outer_bp,
                                            sub_pos: 0u32,
                                        },
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::GuardedConsume {
                                                expected_text: #separator.to_string(),
                                            },
                                    },
                                    mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: #resume_symbol,
                                        weight: lex_w(mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP, #result_src_idx, #rule_idx),
                                        new_state: WpdaState::BinderListLoop {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            frame_idx: #frame_idx,
                                            outer_bp: *outer_bp,
                                            sub_pos: 0u32,
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
                    continue;
                }

                let first_marker_id = markers.id(
                    result_src_idx,
                    rule_idx,
                    TraversalMarkerCoordinate::BinderList { frame_idx, sub_pos: 1 },
                );
                arms.push(quote! {
                    (#result_src_idx, #rule_idx, #frame_idx, 0u32) => {
                        let _ = tokens.peek_text(_pos);
                        return WpdaStepAction::Fork {
                            branches: vec![
                                mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::category_entry(0),
                                    weight: lex_w(0.0, #result_src_idx, #rule_idx),
                                    new_state: WpdaState::Unwinding,
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeAndPopWithEffect {
                                            expected_text: #close.to_string(),
                                            effect:
                                                mettail_prattail::wpda_walker::BuilderDelta::EndBinderScope,
                                        },
                                },
                                mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::category_entry(0),
                                    weight: lex_w(0.0, #result_src_idx, #rule_idx),
                                    new_state: WpdaState::BinderListLoop {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        frame_idx: #frame_idx,
                                        outer_bp: *outer_bp,
                                        sub_pos: 0u32,
                                    },
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::GuardedConsume {
                                            expected_text: #separator.to_string(),
                                        },
                                },
                                mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::binder_list_loop_at(
                                        #first_marker_id, *outer_bp,
                                    ),
                                    weight: lex_w(mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP, #result_src_idx, #rule_idx),
                                    new_state: WpdaState::BinderListLoop {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        frame_idx: #frame_idx,
                                        outer_bp: *outer_bp,
                                        sub_pos: 1u32,
                                    },
                                    action_kind:
                                        mettail_prattail::wpda_walker::ForkActionKind::Push,
                                },
                            ],
                            consume_trigger: false,
                        };
                    }
                });

                for (index, inner_position) in inner_positions.iter().enumerate() {
                    let sub_pos = (index + 1) as u32;
                    let next_sub_pos = (index + 2) as u32;
                    let next_marker_id = markers.id(
                        result_src_idx,
                        rule_idx,
                        TraversalMarkerCoordinate::BinderList { frame_idx, sub_pos: next_sub_pos },
                    );
                    let next_symbol = quote! {
                        StackSymbolV2::binder_list_loop_at(#next_marker_id, *outer_bp)
                    };
                    let next_state = quote! {
                        WpdaState::BinderListLoop {
                            result_src_idx: #result_src_idx,
                            rule_idx: #rule_idx,
                            frame_idx: #frame_idx,
                            outer_bp: *outer_bp,
                            sub_pos: #next_sub_pos,
                        }
                    };
                    let arm = match inner_position {
                        BinderPosition::Literal(text) => quote! {
                            (#result_src_idx, #rule_idx, #frame_idx, #sub_pos) => {
                                return WpdaStepAction::Fork {
                                    branches: vec![mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: #next_symbol,
                                        weight: lex_one(),
                                        new_state: #next_state,
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
                        BinderPosition::TokenKindCapture { kind_name, .. } => {
                            let capture = emit_token_capture_and_replace(
                                kind_name,
                                next_symbol.clone(),
                                next_state.clone(),
                            );
                            quote! {
                                (#result_src_idx, #rule_idx, #frame_idx, #sub_pos) => #capture
                            }
                        },
                        BinderPosition::IdentTextCapture { .. } => {
                            let capture = emit_token_capture_and_replace(
                                "Ident",
                                next_symbol.clone(),
                                next_state.clone(),
                            );
                            quote! {
                                (#result_src_idx, #rule_idx, #frame_idx, #sub_pos) => #capture
                            }
                        },
                        BinderPosition::GuestBodyCapture {
                            open_kind,
                            nested_open_kinds,
                            close_kind,
                            ..
                        } => {
                            let nested_open_kinds = nested_open_kinds
                                .iter()
                                .map(|kind| quote! { #kind.to_string() })
                                .collect::<Vec<_>>();
                            quote! {
                                (#result_src_idx, #rule_idx, #frame_idx, #sub_pos) => {
                                    return WpdaStepAction::Fork {
                                        branches: vec![mettail_prattail::wpda_walker::ForkBranch {
                                            symbol: #next_symbol,
                                            weight: lex_one(),
                                            new_state: #next_state,
                                            action_kind:
                                                mettail_prattail::wpda_walker::ForkActionKind::ConsumeGuestBodyAndReplace {
                                                    open_kind: #open_kind.to_string(),
                                                    nested_open_kinds: vec![#(#nested_open_kinds),*],
                                                    close_kind: #close_kind.to_string(),
                                                },
                                        }],
                                        consume_trigger: false,
                                    };
                                }
                            }
                        },
                        BinderPosition::BinderIdent => quote! {
                            (#result_src_idx, #rule_idx, #frame_idx, #sub_pos) => {
                                return WpdaStepAction::Fork {
                                    branches: vec![mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: #next_symbol,
                                        weight: lex_one(),
                                        new_state: #next_state,
                                        action_kind:
                                            mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeBinderIdentAndReplace {
                                                start_scope: false,
                                            },
                                    }],
                                    consume_trigger: false,
                                };
                            }
                        },
                        BinderPosition::ParamParse { cat, .. } => {
                            let cat_src_idx = cat_idx_tokens(
                                cat,
                                categories,
                                "a ParamParse position inside a binder-list loop",
                                &rule.label.to_string(),
                                rule.label.span(),
                            );
                            quote! {
                                (#result_src_idx, #rule_idx, #frame_idx, #sub_pos) => {
                                    return WpdaStepAction::ReplaceAndPush {
                                        replace_symbol: #next_symbol,
                                        push_symbol:
                                            StackSymbolV2::category_entry_goal(#cat_src_idx),
                                        weight: lex_one(),
                                        new_state: WpdaState::PrefixDispatch {
                                            pos: _pos,
                                            cur_bp: 0u8,
                                        },
                                    };
                                }
                            }
                        },
                        BinderPosition::GuardSlot => quote! {
                            (#result_src_idx, #rule_idx, #frame_idx, #sub_pos) => {
                                return WpdaStepAction::ParsePredicate {
                                    replace_symbol: #next_symbol,
                                    weight: lex_one(),
                                    new_state: #next_state,
                                };
                            }
                        },
                        BinderPosition::OptionalGroup { group_idx, .. } => quote! {
                            (#result_src_idx, #rule_idx, #frame_idx, #sub_pos) => {
                                return WpdaStepAction::Advance(
                                    WpdaState::OptionalGroup {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        group_idx: #group_idx,
                                        sub_pos: 0u32,
                                        outer_bp: *outer_bp,
                                    },
                                );
                            }
                        },
                        BinderPosition::BinderListLoop { .. } => {
                            let child_frame_idx =
                                binder_frame_indices[&(inner_position as *const BinderPosition)];
                            let child_resume = traversal_resume_symbol(
                                TraversalResume::BinderList { frame_idx, next_sub_pos },
                                result_src_idx,
                                rule_idx,
                                markers,
                            );
                            let entry = emit_binder_list_entry(
                                inner_position,
                                child_frame_idx,
                                &child_resume,
                                result_src_idx,
                                rule_idx,
                            );
                            quote! {
                                (#result_src_idx, #rule_idx, #frame_idx, #sub_pos) => {
                                    let _ = tokens.peek_text(_pos);
                                    return #entry;
                                }
                            }
                        },
                    };
                    arms.push(arm);
                }

                let final_sub_pos = (inner_positions.len() + 1) as u32;
                arms.push(quote! {
                    (#result_src_idx, #rule_idx, #frame_idx, #final_sub_pos) => {
                        return WpdaStepAction::Pop {
                            weight: lex_one(),
                            new_state: WpdaState::BinderListLoop {
                                result_src_idx: #result_src_idx,
                                rule_idx: #rule_idx,
                                frame_idx: #frame_idx,
                                outer_bp: *outer_bp,
                                sub_pos: 0u32,
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
            match (*result_src_idx, *rule_idx, *frame_idx, *sub_pos) {
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

/// One collection accumulator consumed by a generated binder action.
///
/// Collection accumulators are a runtime stack, so every action first extracts
/// all of its `CollectionId`s and only then drains them in reverse source order.
/// `optional` distinguishes an always-present top-level slot from a slot nested
/// under one or more optional groups: an absent optional has no accumulator to
/// drain and therefore carries `None` here.
struct CollectionDrainSite {
    id_var: Ident,
    value_var: Ident,
    elem_id: Ident,
    coll_kind: CollectionType,
    optional: bool,
}

struct OptionalActionEmission {
    extract: TokenStream,
    fields: Vec<TokenStream>,
    collection_drains: Vec<CollectionDrainSite>,
}

/// Emit extraction for an arbitrarily nested `ActionArgKind::Optional` tree.
///
/// This is a code-generation PDA: `pending` is the explicit continuation stack
/// and every generated optional iterator is a flat local identified by a
/// monotone ordinal. Consequently neither macro expansion nor the generated
/// action contains recursive Rust control flow. Leaves are emitted in preorder,
/// which is the source/field order used by `field_layout`.
fn emit_nested_optional_action(
    root_arg_idx: usize,
    inner_kinds: &[ActionArgKind],
) -> OptionalActionEmission {
    struct Pending<'kind> {
        kind: &'kind ActionArgKind,
        parent_iter: Ident,
    }

    let root_iter = format_ident!("opt_{}", root_arg_idx);
    let mut statements = vec![quote! {
        let mut #root_iter: Option<
            std::vec::IntoIter<mettail_prattail::wpda_runtime::ActionArg>
        > = match iter.next() {
            Some(arg) => arg.into_optional().flatten().map(|values| values.into_iter()),
            None => return,
        };
    }];
    let mut fields = Vec::new();
    let mut collection_drains = Vec::new();
    let mut pending = Vec::with_capacity(inner_kinds.len());
    pending.extend(
        inner_kinds
            .iter()
            .rev()
            .map(|kind| Pending { kind, parent_iter: root_iter.clone() }),
    );
    let mut ordinal = 0usize;

    while let Some(Pending { kind, parent_iter }) = pending.pop() {
        let current = ordinal;
        ordinal += 1;
        let value_var = format_ident!("nested_{}_{}", root_arg_idx, current);
        match kind {
            ActionArgKind::Optional(inner) => {
                let nested_iter = format_ident!("nested_opt_{}_{}", root_arg_idx, current);
                statements.push(quote! {
                    let mut #nested_iter: Option<
                        std::vec::IntoIter<mettail_prattail::wpda_runtime::ActionArg>
                    > = match #parent_iter.as_mut() {
                        Some(parent) => parent
                            .next()
                            .and_then(|arg| arg.into_optional())
                            .flatten()
                            .map(|values| values.into_iter()),
                        None => None,
                    };
                });
                pending.extend(
                    inner
                        .iter()
                        .rev()
                        .map(|kind| Pending { kind, parent_iter: nested_iter.clone() }),
                );
            },
            ActionArgKind::TokenText { .. } => {
                statements.push(quote! {
                    let #value_var: Option<String> = match #parent_iter.as_mut() {
                        Some(parent) => parent
                            .next()
                            .and_then(|arg| arg.as_token_text().map(str::to_string)),
                        None => None,
                    };
                });
                fields.push(quote! { #value_var });
            },
            ActionArgKind::IdentText { .. } => {
                statements.push(quote! {
                    let #value_var: Option<String> = match #parent_iter.as_mut() {
                        Some(parent) => parent.next().and_then(|arg| {
                            arg.as_ident()
                                .or_else(|| arg.as_token_text())
                                .map(str::to_string)
                        }),
                        None => None,
                    };
                });
                fields.push(quote! { #value_var });
            },
            ActionArgKind::GuestBody { kind, .. } => {
                statements.push(optional_delimited_region_extract(&value_var, &parent_iter, *kind));
                fields.push(quote! { #value_var });
            },
            ActionArgKind::Term(cat) => {
                let cat_id = format_ident!("{}", cat);
                statements.push(quote! {
                    let #value_var: Option<std::sync::Arc<#cat_id>> =
                        match #parent_iter.as_mut() {
                            Some(parent) => parent
                                .next()
                                .and_then(|arg| arg.into_term::<#cat_id>())
                                .map(std::sync::Arc::new),
                            None => None,
                        };
                });
                fields.push(quote! { #value_var });
            },
            ActionArgKind::BinderName => {
                statements.push(quote! {
                    let #value_var: Option<String> = match #parent_iter.as_mut() {
                        Some(parent) => parent
                            .next()
                            .and_then(|arg| arg.into_binder_scope())
                            .and_then(|handle| handle.names.into_iter().next()),
                        None => None,
                    };
                });
                fields.push(quote! { #value_var });
            },
            ActionArgKind::Predicate => {
                statements.push(quote! {
                    let #value_var: Option<mettail_runtime::BehavioralPred> =
                        match #parent_iter.as_mut() {
                            Some(parent) => parent.next().and_then(|arg| {
                                arg.into_predicate::<mettail_runtime::BehavioralPred>()
                            }),
                            None => None,
                        };
                });
                fields.push(quote! { #value_var });
            },
            ActionArgKind::BinderList => {
                statements.push(quote! {
                    let #value_var: Option<Vec<String>> = match #parent_iter.as_mut() {
                        Some(parent) => parent
                            .next()
                            .and_then(|arg| arg.into_binder_scope())
                            .map(|handle| handle.names),
                        None => None,
                    };
                });
                fields.push(quote! { #value_var });
            },
            ActionArgKind::CollectionDrain { elem_cat, coll_kind } => {
                let id_var = format_ident!("nested_{}_{}_id", root_arg_idx, current);
                let elem_id = format_ident!("{}", elem_cat);
                statements.push(quote! {
                    let #id_var: Option<u8> = match #parent_iter.as_mut() {
                        Some(parent) => parent.next().and_then(|arg| arg.as_collection_id()),
                        None => None,
                    };
                });
                collection_drains.push(CollectionDrainSite {
                    id_var,
                    value_var: value_var.clone(),
                    elem_id,
                    coll_kind: coll_kind.clone(),
                    optional: true,
                });
                fields.push(quote! { #value_var });
            },
        }
    }

    OptionalActionEmission {
        extract: quote! { #(#statements)* },
        fields,
        collection_drains,
    }
}

/// Opt-Group (2026-04-29): emit the body of `WpdaState::OptionalGroup`.
/// Dispatches on `(*result_src_idx, *rule_idx, *group_idx, *sub_pos)` to:
///   - sub_pos == 0: peek FIRST set, emit `Push(OptionalGroupAt(1))` (take)
///     or `OptGroupAbsent` (skip).
///   - sub_pos in 1..=inner.len(): walk inner positions (Literal,
///     ParamParse, BinderIdent, GuardSlot) — each step replaces
///     OptionalGroupAt(sub_pos) with OptionalGroupAt(sub_pos+1).
///   - sub_pos == inner.len() + 1: emit `OptGroupFinalize` to pop the
///     OptionalGroupAt marker, finalize the inner-arg scope, and unwind to
///     the typed caller continuation (rule, optional, or binder-list).
pub(crate) fn emit_optional_group_body(
    language: &LanguageDef,
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
    markers: &TraversalMarkerTable,
) -> TokenStream {
    let mut arms: Vec<TokenStream> = Vec::new();

    for (cat_i, rules) in per_cat.iter().enumerate() {
        for (rule_i, rule) in rules.iter().enumerate() {
            let Some(shape) = classify_binder_in(rule, language) else {
                continue;
            };
            let result_src_idx = cat_i as u16;
            let rule_idx = rule_i as u16;

            let TraversalSites { optionals, binder_frame_indices, .. } =
                traversal_sites(&shape.positions);

            for OptionalSite {
                positions: inner,
                first_token_set,
                group_idx,
                resume,
            } in optionals
            {
                let group_idx_value = group_idx;
                let final_sub_pos = (inner.len() + 1) as u32;
                let resume_symbol =
                    traversal_resume_symbol(resume, result_src_idx, rule_idx, markers);
                let resume_state = quote! { WpdaState::Unwinding };

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
                let take_marker_id = markers.id(
                    result_src_idx,
                    rule_idx,
                    TraversalMarkerCoordinate::Optional { group_idx: group_idx_value, sub_pos: 1 },
                );
                arms.push(quote! {
                    (#result_src_idx, #rule_idx, #group_idx_value, 0u32) => {
                        // Stage 3.12 / Class A.i (2026-05-01): Opt-Group Fork.
                        return WpdaStepAction::Fork {
                            branches: vec![
                                // TAKE branch (push OptionalGroupAt(1) →
                                // walker auto-opens optional scope via
                                // emit_push_side_effects).
                                mettail_prattail::wpda_walker::ForkBranch {
                                    symbol: StackSymbolV2::optional_group_at(
                                        #take_marker_id, *outer_bp,
                                    ),
                                    weight: lex_w(0.0, #result_src_idx, #rule_idx),
                                    new_state: WpdaState::OptionalGroup {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        group_idx: #group_idx_value,
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
                                    weight: lex_w(mettail_prattail::automata::lex_weight::EPSILON_OPT_SKIP, #result_src_idx, #rule_idx),
                                    new_state: #resume_state,
                                    action_kind: mettail_prattail::wpda_walker::ForkActionKind::OptGroupAbsent {
                                        replace_symbol: #resume_symbol,
                                    },
                                },
                            ],
                            consume_trigger: false,
                        };
                    }
                });

                // sub_pos in 1..=inner_len: walk inner positions.
                for (i, ipos) in inner.iter().enumerate() {
                    let sp = (i + 1) as u32;
                    let next_sp = sp + 1;
                    let next_marker_id = markers.id(
                        result_src_idx,
                        rule_idx,
                        TraversalMarkerCoordinate::Optional {
                            group_idx: group_idx_value,
                            sub_pos: next_sp,
                        },
                    );
                    let inner_arm = match ipos {
                        BinderPosition::TokenKindCapture { kind_name, .. } => {
                            let capture = emit_token_capture_and_replace(
                                kind_name,
                                quote! {
                                    StackSymbolV2::optional_group_at(
                                        #next_marker_id,
                                        *outer_bp,
                                    )
                                },
                                quote! {
                                    WpdaState::OptionalGroup {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        group_idx: #group_idx_value,
                                        sub_pos: #next_sp,
                                        outer_bp: *outer_bp,
                                    }
                                },
                            );
                            quote! {
                                (#result_src_idx, #rule_idx, #group_idx_value, #sp) => #capture
                            }
                        },
                        BinderPosition::GuestBodyCapture {
                            open_kind,
                            nested_open_kinds,
                            close_kind,
                            ..
                        } => {
                            let nested_open_kinds = nested_open_kinds
                                .iter()
                                .map(|kind| quote! { #kind.to_string() })
                                .collect::<Vec<_>>();
                            quote! {
                                (#result_src_idx, #rule_idx, #group_idx_value, #sp) => {
                                    return WpdaStepAction::Fork {
                                        branches: vec![mettail_prattail::wpda_walker::ForkBranch {
                                            symbol: StackSymbolV2::optional_group_at(
                                                #next_marker_id, *outer_bp,
                                            ),
                                            weight: lex_one(),
                                            new_state: WpdaState::OptionalGroup {
                                                result_src_idx: #result_src_idx,
                                                rule_idx: #rule_idx,
                                                group_idx: #group_idx_value,
                                                sub_pos: #next_sp,
                                                outer_bp: *outer_bp,
                                            },
                                            action_kind:
                                                mettail_prattail::wpda_walker::ForkActionKind::ConsumeGuestBodyAndReplace {
                                                    open_kind: #open_kind.to_string(),
                                                    nested_open_kinds: vec![#(#nested_open_kinds),*],
                                                    close_kind: #close_kind.to_string(),
                                                },
                                        }],
                                        consume_trigger: false,
                                    };
                                }
                            }
                        },
                        // An `m:Ident` INSIDE an `#opt(...)` group. Unlike the two capture
                        // kinds above this emits a REAL arm rather than nothing: the
                        // opt-group value extraction has a matching `IdentText` arm
                        // (`Option<String>` via `as_ident()`), so an inert dispatch here
                        // would leave that extraction permanently unreachable — the group
                        // would never advance past the ident and the `Some(..)` branch
                        // could not be produced. Structural clone of the `Literal` arm
                        // below, swapping the text guard for the ident consume.
                        BinderPosition::IdentTextCapture { .. } => {
                            let capture = emit_token_capture_and_replace(
                                "Ident",
                                quote! {
                                    StackSymbolV2::optional_group_at(
                                        #next_marker_id,
                                        *outer_bp,
                                    )
                                },
                                quote! {
                                    WpdaState::OptionalGroup {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        group_idx: #group_idx_value,
                                        sub_pos: #next_sp,
                                        outer_bp: *outer_bp,
                                    }
                                },
                            );
                            quote! {
                                (#result_src_idx, #rule_idx, #group_idx_value, #sp) => #capture
                            }
                        },
                        BinderPosition::Literal(text) => quote! {
                            (#result_src_idx, #rule_idx, #group_idx_value, #sp) => {
                                // Stage 3.20 / L12 Commit F (2026-05-06):
                                // Cluster 1 compatibility closure #4 (opt-group
                                // inner mirror of site #5).
                                return WpdaStepAction::Fork {
                                    branches: vec![mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::optional_group_at(
                                            #next_marker_id, *outer_bp,
                                        ),
                                        weight: lex_one(),
                                        new_state: WpdaState::OptionalGroup {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            group_idx: #group_idx_value,
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
                            // #141 G1: the ONE resolver, the ONE message.
                            let cat_src_idx = cat_idx_tokens(
                                cat,
                                categories,
                                "a ParamParse position inside an optional group",
                                &rule.label.to_string(),
                                rule.label.span(),
                            );
                            match collection {
                                None => quote! {
                                    (#result_src_idx, #rule_idx, #group_idx_value, #sp) => {
                                        return WpdaStepAction::ReplaceAndPush {
                                            replace_symbol: StackSymbolV2::optional_group_at(
                                                #next_marker_id, *outer_bp,
                                            ),
                                            push_symbol: StackSymbolV2::category_entry_goal(#cat_src_idx),
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
                                        (#result_src_idx, #rule_idx, #group_idx_value, #sp) => {
                                            return WpdaStepAction::ReplaceAndPush {
                                                replace_symbol: StackSymbolV2::optional_group_at(
                                                    #next_marker_id, *outer_bp,
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
                            (#result_src_idx, #rule_idx, #group_idx_value, #sp) => {
                                // Stage 3.20 / L12 Commit F (2026-05-06):
                                // Cluster 1 compatibility closure #6 (opt-group
                                // inner mirror of site #6).
                                return WpdaStepAction::Fork {
                                    branches: vec![mettail_prattail::wpda_walker::ForkBranch {
                                        symbol: StackSymbolV2::optional_group_at(
                                            #next_marker_id, *outer_bp,
                                        ),
                                        weight: lex_one(),
                                        new_state: WpdaState::OptionalGroup {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            group_idx: #group_idx_value,
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
                            (#result_src_idx, #rule_idx, #group_idx_value, #sp) => {
                                return WpdaStepAction::ParsePredicate {
                                    replace_symbol: StackSymbolV2::optional_group_at(
                                        #next_marker_id, *outer_bp,
                                    ),
                                    weight: lex_one(),
                                    new_state: WpdaState::OptionalGroup {
                                        result_src_idx: #result_src_idx,
                                        rule_idx: #rule_idx,
                                        group_idx: #group_idx_value,
                                        sub_pos: #next_sp,
                                        outer_bp: *outer_bp,
                                    },
                                };
                            }
                        },
                        BinderPosition::OptionalGroup { group_idx: child_group_idx, .. } => {
                            quote! {
                                (#result_src_idx, #rule_idx, #group_idx_value, #sp) => {
                                    return WpdaStepAction::Advance(
                                        WpdaState::OptionalGroup {
                                            result_src_idx: #result_src_idx,
                                            rule_idx: #rule_idx,
                                            group_idx: #child_group_idx,
                                            sub_pos: 0u32,
                                            outer_bp: *outer_bp,
                                        },
                                    );
                                }
                            }
                        },
                        BinderPosition::BinderListLoop { .. } => {
                            let child_frame_idx =
                                binder_frame_indices[&(ipos as *const BinderPosition)];
                            let child_resume = traversal_resume_symbol(
                                TraversalResume::Optional {
                                    group_idx: group_idx_value,
                                    next_sub_pos: next_sp,
                                },
                                result_src_idx,
                                rule_idx,
                                markers,
                            );
                            let entry = emit_binder_list_entry(
                                ipos,
                                child_frame_idx,
                                &child_resume,
                                result_src_idx,
                                rule_idx,
                            );
                            quote! {
                                (#result_src_idx, #rule_idx, #group_idx_value, #sp) => {
                                    let _ = tokens.peek_text(_pos);
                                    return #entry;
                                }
                            }
                        },
                    };
                    arms.push(inner_arm);
                }

                // sub_pos == final_sub_pos: finalize.
                arms.push(quote! {
                    (#result_src_idx, #rule_idx, #group_idx_value, #final_sub_pos) => {
                        return WpdaStepAction::OptGroupFinalize {
                            replace_symbol: #resume_symbol,
                            weight: lex_one(),
                            new_state: #resume_state,
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
///
/// `rule_span` is the offending rule's LABEL span, threaded from the single
/// caller (`semantic_actions::emit_action_for_body`, which holds the
/// `GrammarRule`). It exists so a category that cannot be resolved refuses AT
/// THE RULE rather than at the whole `language!` invocation — see
/// [`UnresolvedCategory`].
pub(crate) fn emit_binder_action_entry(
    src_idx: u16,
    rule_idx: u16,
    shape: &BinderShape,
    cat_ident: &Ident,
    categories: &[String],
    rule_span: proc_macro2::Span,
) -> Option<TokenStream> {
    let label_ident = format_ident!("{}", shape.label);
    let arity = shape.action_arity;
    // B13c / Candidate H (2026-05-08): per-arg expected categories for
    // binder rules. Most binder slots are non-Term (BinderName, BinderList,
    // Predicate, Optional) → ANY_CAT sentinel. Only `Term(cat)` slots have
    // a real category index. Output is shape.result_cat (the home cat,
    // since binder rules belong to one category at construction).
    //
    // ★ #141 G2 — THIS CLOSURE USED TO END IN `.unwrap_or(0)`. An unresolvable
    // category became index 0, THE FIRST DECLARED CATEGORY, and the language
    // COMPILED: `output_cat` and every `Term(cat)` slot of `expected_input_cats`
    // silently named the wrong category, so the arg-shape gate rejected readings
    // of rules whose parse was correct. The #133 sweep hardened the two siblings
    // (`emit_mixfix_parts_fn`, `classify_postfix_mixfix`) and missed this one and
    // its twin in `semantic_actions::emit_infix_action_entry`. Both now refuse
    // through [`cat_idx_tokens`], which substitutes a spanned `compile_error!`
    // exactly where the wrong index would have gone.
    let lookup_cat_idx = |name: &str| -> TokenStream {
        cat_idx_tokens(name, categories, "a binder rule's action entry", &shape.label, rule_span)
    };
    let result_cat_idx = lookup_cat_idx(&shape.result_cat);
    // ANY_CAT = u16::MAX; matches mettail_prattail::wpda_runtime::ANY_CAT
    // (this is in macros code so we can't reference the runtime constant
    // by path; we emit `&[ANY_CAT]` literally in the generated code).
    let any_cat_value: u16 = u16::MAX;
    let expected_input_cats: Vec<TokenStream> = shape
        .action_args
        .iter()
        .map(|kind| match kind {
            ActionArgKind::Term(cat) => lookup_cat_idx(cat),
            _ => quote! { #any_cat_value },
        })
        .collect();
    // #141 G2: `expected_input_cats` now holds the emitted tokens directly —
    // either a `u16` literal or the `compile_error!` that refuses in its place.
    let expected_input_cats_ts = quote! { &[#(#expected_input_cats),*] };

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
                    let #var = match iter.next().and_then(|a| a.into_binder_scope()) {
                        Some(h) => match h.names.into_iter().next() {
                            Some(name) => name,
                            None => return,
                        },
                        None => return,
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
            ActionArgKind::GuestBody { kind, .. } => {
                // L9-4: the assembled guest body arrives as
                // `ActionArg::GuestBody(GuestBodyData)` (prattail primitives);
                // lower it to `Arc<FltNode>` here (the generated crate depends on
                // `mettail_runtime`; prattail does not). 1:1 field map.
                extracts.push(required_delimited_region_extract(&var, *kind));
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
                    let #var = match iter.next().and_then(|a| a.into_binder_scope()) {
                        Some(h) => h.names,
                        None => return,
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
                    id_var,
                    value_var: var.clone(),
                    elem_id,
                    coll_kind: coll_kind.clone(),
                    optional: false,
                });
                // Bare value — no Box::new wrapping (the AST variant takes
                // bare Vec<T> / HashBag<T> / HashSet<T> per language! macro
                // convention).
                field_names.push(quote! { #var });
            },
            ActionArgKind::Optional(inner_kinds) => {
                let nested = emit_nested_optional_action(i, inner_kinds);
                extracts.push(nested.extract);
                field_names.extend(nested.fields);
                collection_drain_sites.extend(nested.collection_drains);
                continue;
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
        let elem_id = &site.elem_id;
        let var = &site.value_var;
        let id_var = &site.id_var;
        let exact_elements = quote! {
            match mettail_prattail::wpda_runtime::ActionArg::try_into_terms::<#elem_id>(drained) {
                Ok(elements) => elements,
                Err(_) => {
                    mettail_prattail::wpda_runtime::note_coll_action_downcast_abandon();
                    return;
                },
            }
        };
        let materialize_expr = match site.coll_kind {
            CollectionType::Vec => exact_elements.clone(),
            CollectionType::HashBag => quote! {
                mettail_runtime::HashBag::<#elem_id>::from_iter(
                    #exact_elements
                )
            },
            CollectionType::HashSet => quote! {
                std::collections::HashSet::<#elem_id>::from_iter(
                    #exact_elements
                )
            },
            CollectionType::HashMap | CollectionType::PathMap => quote! {
                {
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
                    container
                }
            },
        };
        if site.optional {
            extracts.push(quote! {
                let #var = match #id_var {
                    Some(id) => {
                        let drained = b.drain_collection(id);
                        Some(#materialize_expr)
                    },
                    None => None,
                };
            });
        } else {
            extracts.push(quote! {
                let drained = b.drain_collection(#id_var);
                let #var = #materialize_expr;
            });
        }
    }

    // Build the action body's construction expression based on rule shape.
    // For binder rules with auxiliary fields (e.g. PGuardedInput's
    // `(Name, BehavioralPred, Scope<...>)`), the AST variant takes the
    // auxiliary fields first, then the Scope. We emit the call as
    // `Cat::Label(field_names..., scope)` — field_names comes from
    // non-binder, non-body Term args + Predicate args in encounter order.
    //
    // ★ #139: that encounter order is SYNTAX order, and it is the order the
    // variant DEFINITION now follows too — `gen/types/enums.rs` builds its field
    // list from `gen::capture::field_layout`, which reproduces this walk. The two
    // derivations remain independent code, so [`field_order_disagreement`] holds
    // them to each other at every call site; see its header.
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

// ═══════════════════════════════════════════════════════════════════════════
// Task #139 — THE POSITIONAL GATE
// ═══════════════════════════════════════════════════════════════════════════

/// What a single AST-variant field IS, in the one vocabulary both the
/// DEFINITION and the CONSTRUCTION can speak.
///
/// Sharp enough to be worth asserting: `Term` carries the CATEGORY name, so a
/// gate over it distinguishes `Arc<Proc>` from `Arc<Name>` — the transposition
/// that type-checks and is silently wrong is a transposition of two `Term`s, and
/// it is only invisible when the two categories are equal, in which case the two
/// fields are interchangeable and no term is misbuilt.
#[derive(PartialEq, Eq, Debug, Clone)]
pub(crate) enum FieldShapeTag {
    /// A `v@Tok` capture's text — a bare `String`.
    TokenText,
    /// An `m:Ident` param's text — also a bare `String`, and therefore
    /// positionally confusable with [`FieldShapeTag::TokenText`] unless the two
    /// are told apart, which is why they are separate tags here.
    IdentText,
    /// A `*flt(…)` guest body — `Arc<FltNode>`.
    GuestBody,
    /// A parsed sub-term of the named category.
    Term(String),
    /// A collection slot: element category + container kind.
    Collection(String, CollectionType),
    /// A `?g:Guard` slot — `BehavioralPred`.
    Predicate,
    /// The trailing binder `Scope`.
    Scope,
    /// A parameter type `classify_binder_in` does not model. Unreachable from
    /// the gate (that classifier returns `None` for such a rule, so no action
    /// entry and no gate call), and named rather than silently coerced so that a
    /// future widening of the classifier shows up here instead of passing.
    Unmodelled,
}

/// One field of a variant: its shape, and whether it is `Option`-wrapped.
///
/// Flat, never nested: an `#opt(…)` group contributes one `Option<T>` field PER
/// inner parameter on both sides (`enums.rs` emits them separately, and
/// `emit_binder_action_entry`'s `Optional` arm pushes each inner ident into
/// `field_names` individually).
#[derive(PartialEq, Eq, Debug, Clone)]
pub(crate) struct FieldShape {
    pub(crate) tag: FieldShapeTag,
    pub(crate) optional: bool,
}

/// The fields the CONSTRUCTION site will pass, in the order it will pass them.
///
/// Mirrors [`emit_binder_action_entry`] exactly, including its `body_holder`
/// selection rule (the first top-level `Term` whose category is the binder
/// body's is consumed by the `Scope` rather than pushed as a field) and its
/// "`scope` appended last" rule.
pub(crate) fn constructed_field_shapes(shape: &BinderShape) -> Vec<FieldShape> {
    fn tag_of(kind: &ActionArgKind) -> Option<FieldShapeTag> {
        match kind {
            ActionArgKind::TokenText { .. } => Some(FieldShapeTag::TokenText),
            ActionArgKind::IdentText { .. } => Some(FieldShapeTag::IdentText),
            ActionArgKind::GuestBody { .. } => Some(FieldShapeTag::GuestBody),
            ActionArgKind::Term(cat) => Some(FieldShapeTag::Term(cat.clone())),
            ActionArgKind::Predicate => Some(FieldShapeTag::Predicate),
            ActionArgKind::CollectionDrain { elem_cat, coll_kind } => {
                Some(FieldShapeTag::Collection(elem_cat.clone(), coll_kind.clone()))
            },
            // Both fold into the trailing `Scope`; neither is a field.
            ActionArgKind::BinderName | ActionArgKind::BinderList => None,
            // Handled by the caller, which flattens it.
            ActionArgKind::Optional(_) => None,
        }
    }

    let mut out = Vec::with_capacity(shape.action_args.len() + 1);
    let mut body_taken = false;
    for kind in &shape.action_args {
        match kind {
            ActionArgKind::Optional(inner) => {
                for inner_kind in inner {
                    if let Some(tag) = tag_of(inner_kind) {
                        out.push(FieldShape { tag, optional: true });
                    }
                }
            },
            ActionArgKind::Term(cat)
                if shape.has_binder
                    && shape.body_cat.as_deref() == Some(cat.as_str())
                    && !body_taken =>
            {
                // The binder body — consumed by the `Scope`, not a field.
                body_taken = true;
            },
            other => {
                if let Some(tag) = tag_of(other) {
                    out.push(FieldShape { tag, optional: false });
                }
            },
        }
    }
    if shape.has_binder {
        out.push(FieldShape {
            tag: FieldShapeTag::Scope,
            optional: false,
        });
    }
    out
}

/// The fields the DEFINITION site will declare, in the order it will declare
/// them — read off the same [`crate::gen::capture::field_layout`] that
/// `gen/types/enums.rs` consumes.
pub(crate) fn declared_field_shapes(layout: &crate::gen::capture::FieldLayout) -> Vec<FieldShape> {
    use crate::gen::capture::FieldSlotSource;
    let mut out = Vec::with_capacity(layout.slots.len());
    for slot in &layout.slots {
        let tag = match &slot.source {
            FieldSlotSource::TokenText { .. } => FieldShapeTag::TokenText,
            FieldSlotSource::GuestBody { .. } => FieldShapeTag::GuestBody,
            FieldSlotSource::Param(TermParam::GuardBody { .. }) => FieldShapeTag::Predicate,
            FieldSlotSource::Param(
                TermParam::Abstraction { .. } | TermParam::MultiAbstraction { .. },
            ) => FieldShapeTag::Scope,
            FieldSlotSource::Param(TermParam::Simple { ty, .. }) => match ty {
                TypeExpr::Base(ident) => {
                    let name = ident.to_string();
                    match mettail_ast::grammar::NonTerminalKind::classify(&name) {
                        mettail_ast::grammar::NonTerminalKind::Ident => FieldShapeTag::IdentText,
                        _ => FieldShapeTag::Term(name),
                    }
                },
                TypeExpr::Collection { coll_type, element } => match element.as_ref() {
                    TypeExpr::Base(elem) => {
                        FieldShapeTag::Collection(elem.to_string(), coll_type.clone())
                    },
                    _ => FieldShapeTag::Unmodelled,
                },
                TypeExpr::Map { key, value } => match (key.as_ref(), value.as_ref()) {
                    (TypeExpr::Base(k), TypeExpr::Base(v)) if k == v => {
                        FieldShapeTag::Collection(k.to_string(), CollectionType::HashMap)
                    },
                    _ => FieldShapeTag::Unmodelled,
                },
                _ => FieldShapeTag::Unmodelled,
            },
            // `field_layout` flattens opt-groups, so an `Optional` is never a slot.
            FieldSlotSource::Param(TermParam::Optional { .. }) => FieldShapeTag::Unmodelled,
        };
        out.push(FieldShape { tag, optional: slot.optional });
    }
    out
}

/// ★ THE GATE. `Some(message)` iff the variant the DEFINITION will write and the
/// arguments the CONSTRUCTION will pass do not line up field-for-field.
///
/// # Why a gate exists at all when both sides now derive from one order
///
/// They derive from one ORDER, not from one piece of code: `field_layout` walks
/// the syntax pattern for the definition, and `classify_binder_in` walks it
/// again for the construction. Two walks of one grammar can still drift — that
/// is precisely how #139 arose, from two walks of two DIFFERENT lists. This
/// check is what makes a future drift a REFUSAL at the offending rule instead of
/// a variant whose operands are transposed and which type-checks.
///
/// It runs entirely on the macro's own data: no build of the generated crate,
/// no test fixture, no grammar corpus. Every language that compiles is gated.
pub(crate) fn field_order_disagreement(rule: &GrammarRule, shape: &BinderShape) -> Option<String> {
    let term_context = rule.term_context.as_deref()?;
    let layout = crate::gen::capture::field_layout(term_context, rule.syntax_pattern.as_deref());
    let declared = declared_field_shapes(&layout);
    let constructed = constructed_field_shapes(shape);
    if declared == constructed {
        return None;
    }
    Some(format!(
        "rule `{}`: the AST variant this rule DEFINES and the arguments its \
         semantic action CONSTRUCTS do not line up field-for-field.\n  \
         defined  (gen/types/enums.rs, via gen::capture::field_layout): {declared:?}\n  \
         emitted  (gen/runtime/wpda_codegen/binder.rs::emit_binder_action_entry): \
         {constructed:?}\n\nA positional disagreement here is NOT necessarily a compile \
         error in the generated crate: two same-typed fields transpose silently. The two \
         orders must both be the SYNTAX-PATTERN order — see the header of \
         `macros/src/gen/capture.rs`.",
        shape.label,
    ))
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
            role: Default::default(),
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
        let language = synthetic_lang_for_lambda_test();
        let markers = TraversalMarkerTable::build(&language, &per_cat);
        let (mut ts, __ts_helpers) = emit_binder_rule_body(
            &language,
            &categories,
            &per_cat,
            &prefix_bp_map,
            &markers,
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
        let language = synthetic_lang_for_lambda_test();
        let markers = TraversalMarkerTable::build(&language, &per_cat);
        let (mut ts, __ts_helpers) = emit_binder_rule_body(
            &language,
            &categories,
            &per_cat,
            &prefix_bp_map,
            &markers,
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
        assert_eq!(
            s.matches("category_entry_goal (0u16)").count(),
            2,
            "every typed BigInt child occurrence must carry its declared category goal",
        );
        assert!(s.contains("\"(\""));
        assert!(s.contains("\")\""));
        assert!(s.contains("\",\""));
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Task #141 G1+G2 / RED-2 — the shared category resolver, and the binder
    // twin of `semantic_actions`' fails-open lookup
    // ═══════════════════════════════════════════════════════════════════════
    //
    // The full argument for why this mutation is applied at the EMITTER rather
    // than to a grammar — Pass 5 makes `categories` total over `language.types`,
    // and an undeclared category is rejected by `validate_language` — is written
    // once, in `semantic_actions.rs`'s `mod tests`. These cells are the TWIN:
    // `emit_binder_action_entry` carried the identical `.unwrap_or(0)`, was
    // missed by the same #133 sweep, and must be shown to refuse independently,
    // so that repairing one site cannot make both cells pass.

    /// The category the fixture rule's `Term` slot is declared in — absent from
    /// the mutation's category list, present in the control's.
    const RED2_REFERENCED_CATEGORY: &str = "Ghost";
    const RED2_RULE_LABEL: &str = "BindGhost";

    fn red2_binder_shape() -> BinderShape {
        BinderShape {
            label: RED2_RULE_LABEL.to_string(),
            result_cat: "Term".to_string(),
            leading_category: None,
            leading_ident_capture: None,
            positions: Vec::new(),
            is_multi: false,
            has_binder: false,
            action_arity: 1,
            action_args: vec![ActionArgKind::Term(RED2_REFERENCED_CATEGORY.to_string())],
            body_cat: None,
            param_cats: vec![RED2_REFERENCED_CATEGORY.to_string()],
        }
    }

    /// The same shape with its `Term` slot pointed at `slot_category` instead —
    /// used by [`the_refusal_is_not_the_old_index_zero_answer`] to hold
    /// EVERYTHING ELSE constant.
    fn red2_binder_shape_with_slot(slot_category: &str) -> BinderShape {
        BinderShape {
            action_args: vec![ActionArgKind::Term(slot_category.to_string())],
            param_cats: vec![slot_category.to_string()],
            ..red2_binder_shape()
        }
    }

    fn red2_binder_emit(categories: &[&str]) -> String {
        red2_binder_emit_shape(&red2_binder_shape(), categories)
    }

    fn red2_binder_emit_shape(shape: &BinderShape, categories: &[&str]) -> String {
        let categories: Vec<String> = categories.iter().map(|c| (*c).to_string()).collect();
        emit_binder_action_entry(
            0u16,
            0u16,
            shape,
            &Ident::new("Term", Span::call_site()),
            &categories,
            Span::call_site(),
        )
        .expect(
            "the fixture shape must yield an action entry in BOTH arms; a `None` here \
                 would make the mutation and the control agree vacuously",
        )
        .to_string()
    }

    /// MUTATION. `Ghost` is not a declared category ⇒ the binder action entry
    /// refuses, naming the category and the rule.
    #[test]
    fn binder_action_entry_refuses_an_unresolvable_category_naming_it_and_the_rule() {
        let emitted = red2_binder_emit(&["Term"]);
        assert!(
            emitted.contains("compile_error"),
            "an unresolvable `ActionArgKind::Term` category must emit `compile_error!`, \
             not index 0. Got: {emitted}",
        );
        assert!(
            emitted.contains(RED2_REFERENCED_CATEGORY),
            "the refusal must NAME `{RED2_REFERENCED_CATEGORY}`. Got: {emitted}",
        );
        assert!(
            emitted.contains(RED2_RULE_LABEL),
            "the refusal must NAME rule `{RED2_RULE_LABEL}`. Got: {emitted}",
        );
    }

    /// CONTROL. The same shape with `Ghost` declared emits its index and does not
    /// refuse.
    #[test]
    fn binder_action_entry_emits_the_index_when_the_category_is_declared() {
        let emitted = red2_binder_emit(&["Term", "Ghost"]);
        assert!(
            !emitted.contains("compile_error"),
            "a declared category must NOT refuse. Got: {emitted}",
        );
        assert!(emitted.contains("1u16"), "`Ghost` is index 1 of [Term, Ghost]. Got: {emitted}",);
    }

    /// ★ THE FAILS-OPEN WITNESS. Index 0 is `Term`, the FIRST declared category —
    /// the exact wrong answer both sites used to give. This cell states the
    /// contrast that makes the repair meaningful: the refusal must not merely be
    /// *some* output, it must not be the OLD output.
    #[test]
    fn the_refusal_is_not_the_old_index_zero_answer() {
        // ONE category list, ONE `result_cat` (`Term`, index 0). The two emissions
        // differ in exactly one thing: whether the slot names a DECLARED category
        // (`Term`) or an unresolvable one (`Ghost`). Under HEAD's `.unwrap_or(0)`
        // they were BYTE-IDENTICAL — that indistinguishability WAS the defect, and
        // it is what this cell refuses to let return.
        //
        // ⚠ The comparison is on the ARG-CATEGORY LIST specifically, not on the whole
        // emission. The two emissions also differ in the extraction code (`param_cats`
        // puts the category NAME into `into_term::<…>()`), so a whole-string `assert_ne!`
        // would pass even under the old `.unwrap_or(0)` — measured, and rejected, while
        // writing this cell. The list is the field the defect corrupted, so the list is
        // what the cell pins.
        const INDEX_ZERO_ARG_LIST: &str = "expected_input_cats : & [0u16]";
        let categories = ["Term"];
        let unresolvable =
            red2_binder_emit_shape(&red2_binder_shape_with_slot("Ghost"), &categories);
        let honestly_zero =
            red2_binder_emit_shape(&red2_binder_shape_with_slot("Term"), &categories);
        assert!(
            honestly_zero.contains(INDEX_ZERO_ARG_LIST),
            "ANTI-VACUITY: `Term` IS index 0 of {categories:?}, so this arm must render \
             exactly `{INDEX_ZERO_ARG_LIST}`. If this fails the rendering changed and the \
             assertion below has stopped meaning anything. Got: {honestly_zero}",
        );
        assert!(
            !unresolvable.contains(INDEX_ZERO_ARG_LIST),
            "an unresolvable category must NOT render the same arg list as a genuine \
             index-0 category — that indistinguishability WAS the defect. Got: \
             {unresolvable}",
        );
    }

    /// The resolver's message is the ONE message: it names the category, the
    /// rule, the site, and the declared set it searched.
    #[test]
    fn the_resolver_message_names_category_rule_site_and_declared_set() {
        let categories = vec!["Term".to_string(), "Num".to_string()];
        let err = resolve_cat_idx("Ghost", &categories, "a ParamParse position", "SomeRule")
            .expect_err("`Ghost` is not in the declared set, so this must refuse");
        let message = err.message();
        for needle in ["Ghost", "SomeRule", "a ParamParse position", "Term", "Num"] {
            assert!(
                message.contains(needle),
                "the ONE message must contain `{needle}`. Got: {message}",
            );
        }
    }

    /// And it resolves what it should: a declared category yields its index, so
    /// the resolver is not refusing everything.
    #[test]
    fn the_resolver_resolves_a_declared_category() {
        let categories = vec!["Term".to_string(), "Num".to_string()];
        assert_eq!(resolve_cat_idx("Num", &categories, "a site", "R"), Ok(1u16));
        assert_eq!(
            cat_idx_tokens("Num", &categories, "a site", "R", Span::call_site()).to_string(),
            "1u16"
        );
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Task #139 RED — the DEFINITION's field order and the CONSTRUCTION's
    // argument order come from ONE derivation
    // ═══════════════════════════════════════════════════════════════════════
    //
    // # The defect, stated as a shape rather than as an instance
    //
    // The construction site orders its arguments by SYNTAX-PATTERN encounter.
    // Until this repair the variant DEFINITION ordered its fields by TERM-CONTEXT
    // DECLARATION. Nothing held the two lists to each other, so they agreed only
    // when the author happened to declare parameters in the order the surface
    // mentions them.
    //
    // The fixture below is the smallest rule for which they disagree:
    //
    //     Guarded . p:Proc, ?g:Guard |- "guarded" "(" g ")" p : Proc ;
    //             ╰── declaration (p, g) ──╯   ╰─ syntax (g, p) ─╯
    //
    // Under the pre-repair generator the definition was
    // `Guarded(Arc<Proc>, BehavioralPred)` while the construction was
    // `Guarded(pred, Arc::new(proc))` — E0308 in the generated crate. That
    // compile error is the LOUD member of the class. The silent member is a rule
    // whose two out-of-order parameters share a type:
    //
    //     Sub . a:Proc, b:Proc |- "sub" "(" b "," a ")" : Proc ;
    //
    // which emits `Sub(Arc::new(b), Arc::new(a))` against
    // `Sub(Arc<Proc>, Arc<Proc>)`: type-correct, operands transposed, no
    // diagnostic anywhere. Both cells below assert the ORDER, not the types, so
    // they speak to the silent member as well as the loud one.
    //
    // # Why the assertions are pinned to tokens
    //
    // Each cell names the exact bytes it expects. A whole-string `assert_ne!`
    // against the pre-repair output would pass on any incidental difference —
    // a whitespace change, a renamed local — and that vacuity mode has already
    // bitten this campaign once (see `the_refusal_is_not_the_old_index_zero_answer`).

    /// `Guarded . p:Proc, ?g:Guard |- "guarded" "(" g ")" p : Proc ;`
    ///
    /// Declaration order `(p, g)`; syntax order `(g, p)`. The one shape the
    /// repair changes.
    fn guard_order_rule() -> GrammarRule {
        GrammarRule {
            term_context: Some(vec![
                TermParam::Simple {
                    name: Ident::new("p", Span::call_site()),
                    ty: TypeExpr::Base(Ident::new("Proc", Span::call_site())),
                },
                TermParam::GuardBody { name: Ident::new("g", Span::call_site()) },
            ]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("guarded".into()),
                SyntaxExpr::Literal("(".into()),
                SyntaxExpr::Param(Ident::new("g", Span::call_site())),
                SyntaxExpr::Literal(")".into()),
                SyntaxExpr::Param(Ident::new("p", Span::call_site())),
            ]),
            ..rule_fixture(
                Ident::new("Guarded", Span::call_site()),
                Ident::new("Proc", Span::call_site()),
            )
        }
    }

    /// THE CONTROL. The same rule with the guard parameter removed:
    /// `Guarded . p:Proc |- "guarded" p : Proc ;`. One parameter, so declaration
    /// order and syntax order are the same list and the repair cannot move it.
    fn guard_order_control_rule() -> GrammarRule {
        GrammarRule {
            term_context: Some(vec![TermParam::Simple {
                name: Ident::new("p", Span::call_site()),
                ty: TypeExpr::Base(Ident::new("Proc", Span::call_site())),
            }]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("guarded".into()),
                SyntaxExpr::Param(Ident::new("p", Span::call_site())),
            ]),
            ..rule_fixture(
                Ident::new("Guarded", Span::call_site()),
                Ident::new("Proc", Span::call_site()),
            )
        }
    }

    /// The real `PGuardedInput` from `languages/tests/definitions/guarded_rho.rs`:
    /// `n:Name, ?guard:Guard, ^x.p:[Name -> Proc]` with surface
    /// `"for" "(" x "<-" n "where" guard ")" "{" p "}"`.
    ///
    /// SECOND CONTROL, and the load-bearing one: this rule's two orders ALREADY
    /// agree (non-scope declaration `n, guard`; non-scope syntax `n` then
    /// `guard`; abstraction declared last). It is the one shipped guard rule, so
    /// any movement here would mean the repair broke a case that was correct.
    fn shipped_guarded_input_rule() -> GrammarRule {
        GrammarRule {
            term_context: Some(vec![
                TermParam::Simple {
                    name: Ident::new("n", Span::call_site()),
                    ty: TypeExpr::Base(Ident::new("Name", Span::call_site())),
                },
                TermParam::GuardBody {
                    name: Ident::new("guard", Span::call_site()),
                },
                TermParam::Abstraction {
                    binder: Ident::new("x", Span::call_site()),
                    body: Ident::new("p", Span::call_site()),
                    ty: TypeExpr::Arrow {
                        domain: Box::new(TypeExpr::Base(Ident::new("Name", Span::call_site()))),
                        codomain: Box::new(TypeExpr::Base(Ident::new("Proc", Span::call_site()))),
                    },
                },
            ]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("for".into()),
                SyntaxExpr::Literal("(".into()),
                SyntaxExpr::Param(Ident::new("x", Span::call_site())),
                SyntaxExpr::Literal("<-".into()),
                SyntaxExpr::Param(Ident::new("n", Span::call_site())),
                SyntaxExpr::Literal("where".into()),
                SyntaxExpr::Param(Ident::new("guard", Span::call_site())),
                SyntaxExpr::Literal(")".into()),
                SyntaxExpr::Literal("{".into()),
                SyntaxExpr::Param(Ident::new("p", Span::call_site())),
                SyntaxExpr::Literal("}".into()),
            ]),
            ..rule_fixture(
                Ident::new("PGuardedInput", Span::call_site()),
                Ident::new("Proc", Span::call_site()),
            )
        }
    }

    /// A `LanguageDef` declaring `Proc` and `Name`, holding `rules` as its terms.
    fn lang_with(rules: Vec<GrammarRule>) -> mettail_ast::language::LanguageDef {
        use mettail_ast::language::LangType;
        let mut lang = synthetic_lang_for_lambda_test();
        lang.terms = rules;
        lang.types = vec![
            LangType {
                name: Ident::new("Proc", Span::call_site()),
                role: Default::default(),
                native_type: None,
                collection_kind: None,
            },
            LangType {
                name: Ident::new("Name", Span::call_site()),
                role: Default::default(),
                native_type: None,
                collection_kind: None,
            },
        ];
        lang
    }

    /// The action entry `emit_binder_action_entry` writes for `rule`, as tokens.
    fn emitted_action_for(rule: &GrammarRule, categories: &[&str]) -> String {
        let language = lang_with(vec![rule.clone()]);
        let shape = classify_binder_in(rule, &language)
            .expect("the fixture is literal-led and multi-position, so it must classify");
        let categories: Vec<String> = categories.iter().map(|c| (*c).to_string()).collect();
        emit_binder_action_entry(0u16, 0u16, &shape, &rule.category, &categories, Span::call_site())
            .expect("a classified binder shape must yield an action entry")
            .to_string()
    }

    /// The variant `gen/types/enums.rs` writes for `rule`, as tokens.
    fn emitted_variant_for(rule: &GrammarRule) -> String {
        let language = lang_with(vec![rule.clone()]);
        crate::gen::types::enums::variant_tokens_for_rule(rule, &language).to_string()
    }

    /// ★ THE MUTATION CELL. The guard-first rule's DEFINITION follows the
    /// SYNTAX, so it lines up with the construction field-for-field.
    #[test]
    fn the_definition_follows_the_syntax_when_declaration_order_differs() {
        let rule = guard_order_rule();

        // The DEFINITION. Pre-repair this read
        // `Guarded (std :: sync :: Arc < Proc > , mettail_runtime :: BehavioralPred)`
        // — declaration order. It is the byte sequence this repair moves, and it
        // is pinned exactly rather than compared to its own former self.
        let variant = emitted_variant_for(&rule);
        assert_eq!(
            variant, "Guarded (mettail_runtime :: BehavioralPred , std :: sync :: Arc < Proc >)",
            "the variant's field 0 must be the GUARD (syntax position 0) and field 1 the \
             PROC (syntax position 1). Got: {variant}",
        );

        // The CONSTRUCTION, pinned to the same two positions: `arg_0` is
        // extracted as a predicate and passed first; `arg_1` is extracted as a
        // `Proc` term and passed second.
        let action = emitted_action_for(&rule, &["Proc", "Name"]);
        assert!(
            action.contains(
                "let arg_0 = match iter . next () . and_then \
                 (| a | a . into_predicate :: < mettail_runtime :: BehavioralPred > ())"
            ),
            "syntax position 0 is the guard, so `arg_0` must be the PREDICATE extraction. \
             Got: {action}",
        );
        assert!(
            action.contains(
                "let arg_1 = match iter . next () . and_then (| a | a . into_term :: < Proc > ())"
            ),
            "syntax position 1 is `p:Proc`, so `arg_1` must be the TERM extraction. \
             Got: {action}",
        );
        assert!(
            action.contains("Proc :: Guarded (arg_0 , std :: sync :: Arc :: new (arg_1))"),
            "the construction must pass the predicate first and the term second, matching \
             the definition positionally. Got: {action}",
        );

        // And the gate agrees, which is the property the two pins witness.
        let language = lang_with(vec![rule.clone()]);
        let shape = classify_binder_in(&rule, &language).expect("classifies");
        assert_eq!(
            field_order_disagreement(&rule, &shape),
            None,
            "the definition and the construction must line up field-for-field",
        );
    }

    /// ★ THE ANTI-VACUITY WITNESS. The declaration order and the syntax order of
    /// this fixture really are DIFFERENT lists — otherwise the cell above would
    /// be asserting a tautology and would have passed before the repair too.
    #[test]
    fn the_fixture_really_does_declare_and_write_its_parameters_in_different_orders() {
        let rule = guard_order_rule();
        let term_context = rule
            .term_context
            .as_deref()
            .expect("fixture has a term context");

        let declared: Vec<String> = term_context
            .iter()
            .map(|p| match p {
                TermParam::Simple { name, .. } => name.to_string(),
                TermParam::GuardBody { name } => name.to_string(),
                _ => "?".to_string(),
            })
            .collect();
        assert_eq!(declared, vec!["p", "g"], "declaration order is (p, g)");

        let written: Vec<String> = rule
            .syntax_pattern
            .as_deref()
            .expect("fixture has a syntax pattern")
            .iter()
            .filter_map(|e| match e {
                SyntaxExpr::Param(id) => Some(id.to_string()),
                _ => None,
            })
            .collect();
        assert_eq!(written, vec!["g", "p"], "syntax order is (g, p)");
    }

    /// CONTROL — a rule whose two orders coincide must be BYTE-IDENTICAL to what
    /// the pre-repair generator produced. Both strings below are the pre-repair
    /// output verbatim: a single `p:Proc` param is field 0 either way, so a
    /// repair that reordered anything else would turn this cell red.
    #[test]
    fn a_rule_whose_orders_already_agree_does_not_move() {
        let rule = guard_order_control_rule();

        let variant = emitted_variant_for(&rule);
        assert_eq!(
            variant, "Guarded (std :: sync :: Arc < Proc >)",
            "one param, one field, unchanged by the repair. Got: {variant}",
        );

        let action = emitted_action_for(&rule, &["Proc", "Name"]);
        assert!(
            action.contains("Proc :: Guarded (std :: sync :: Arc :: new (arg_0))"),
            "one param, one constructor argument, unchanged by the repair. Got: {action}",
        );

        let language = lang_with(vec![rule.clone()]);
        let shape = classify_binder_in(&rule, &language).expect("classifies");
        assert_eq!(field_order_disagreement(&rule, &shape), None);
    }

    /// SECOND CONTROL — the one shipped `?g:Guard` rule. Its two orders already
    /// agree, so the pinned bytes are exactly what `target/generated/guardedrho/
    /// ast_enums.rs` holds at the commit before this repair. Movement here would
    /// mean the repair broke a correct case.
    #[test]
    fn the_shipped_guarded_input_rule_does_not_move() {
        let rule = shipped_guarded_input_rule();

        let variant = emitted_variant_for(&rule);
        assert_eq!(
            variant,
            "PGuardedInput (std :: sync :: Arc < Name > , mettail_runtime :: BehavioralPred , \
             mettail_runtime :: Scope < mettail_runtime :: Binder < String > , \
             std :: sync :: Arc < Proc >>)",
            "the shipped rule's variant is `(Arc<Name>, BehavioralPred, Scope<…>)` before and \
             after the repair. Got: {variant}",
        );

        let action = emitted_action_for(&rule, &["Proc", "Name"]);
        assert!(
            action.contains(
                "Proc :: PGuardedInput (std :: sync :: Arc :: new (arg_1) , arg_2 , scope)"
            ),
            "the construction passes `(Arc::new(name), pred, scope)` before and after the \
             repair. Got: {action}",
        );

        let language = lang_with(vec![rule.clone()]);
        let shape = classify_binder_in(&rule, &language).expect("classifies");
        assert_eq!(field_order_disagreement(&rule, &shape), None);
    }

    /// The gate is not inert: hand it a shape whose argument order has been
    /// transposed relative to the rule and it says so, naming both sequences.
    ///
    /// ★ This is the SILENT member of the class made visible. The two fields are
    /// `Predicate` and `Term("Proc")` here, but the same transposition between
    /// two `Term("Proc")`s produces a variant that type-checks and evaluates the
    /// wrong operands — which is why the gate compares POSITIONS and not types.
    #[test]
    fn the_gate_refuses_a_transposed_construction_naming_both_sequences() {
        let rule = guard_order_rule();
        let language = lang_with(vec![rule.clone()]);
        let mut shape = classify_binder_in(&rule, &language).expect("classifies");
        assert_eq!(
            field_order_disagreement(&rule, &shape),
            None,
            "ANTI-VACUITY: the un-transposed shape must AGREE, or the refusal below \
             would not be caused by the transposition",
        );

        shape.action_args.swap(0, 1);
        let message = field_order_disagreement(&rule, &shape)
            .expect("a transposed construction must be refused");
        assert!(message.contains("Guarded"), "the refusal must NAME the rule. Got: {message}",);
        assert!(
            message.contains("Predicate") && message.contains("Term(\"Proc\")"),
            "the refusal must show BOTH field sequences so the reader can see which two \
             positions swapped. Got: {message}",
        );
    }

    /// ═══════════════════════════════════════════════════════════════════════
    /// THE CORPUS GATE — order agreement for EVERY rule in EVERY bundled language
    /// ═══════════════════════════════════════════════════════════════════════
    ///
    /// The cells above pin two synthetic fixtures and one shipped rule. This one
    /// ranges over the whole corpus, and it is what keeps the rules that are
    /// merely AT RISK — every literal-led multi-parameter rule — from becoming
    /// the next instance. It derives its subject rather than listing it: a list
    /// of languages is a list that can be short.
    #[test]
    fn every_bundled_rule_defines_and_constructs_the_same_field_order() {
        let mut languages_scanned = 0usize;
        let mut rules_gated = 0usize;
        let mut disagreements: Vec<String> = Vec::new();
        for language in crate::gen::capture::bundled_corpus::bundled_languages() {
            languages_scanned += 1;
            for rule in &language.def.terms {
                let Some(shape) = classify_binder_in(rule, &language.def) else {
                    continue;
                };
                rules_gated += 1;
                if let Some(message) = field_order_disagreement(rule, &shape) {
                    disagreements.push(format!("{}: {message}", language.tag));
                }
            }
        }

        // Non-vacuity floor. "For every rule, P" is satisfied by NO rules, which
        // is the exact shape of a gate that has stopped seeing its subject.
        assert!(
            languages_scanned >= 45,
            "the census found {languages_scanned} reconstructable language(s); the corpus \
             holds around fifty, so the walk or the parse gate has changed shape and this \
             assertion would be reporting success over a domain that is not the corpus",
        );
        assert!(
            rules_gated >= 150,
            "only {rules_gated} rule(s) reached the gate. Literal-led multi-position rules \
             number in the hundreds across the corpus, so a count this low means \
             `classify_binder_in` stopped classifying and the gate is ranging over almost \
             nothing",
        );
        assert!(
            disagreements.is_empty(),
            "{} of {rules_gated} gated rule(s) define a field order their action does not \
             construct:\n\n{}",
            disagreements.len(),
            disagreements.join("\n\n"),
        );
    }
}
