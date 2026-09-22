//! The original legacy-BNF normalization loop with borrowed observations.
//!
//! This is the implementation used by `grammar::convert_items_to_term_context`,
//! not an additional normalizer. Adapters supply original items and constructors;
//! the loop retains the original preflight, order, names and refusal behavior.
//! `LegacyRuleNormalizationProjection.v` proves constructor substitution and
//! refusal/commit correspondence. Resource admission for runtime-owned inputs
//! is a separate obligation; this interface does not certify arbitrary adapters.

use crate::grammar::NonTerminalKind;

/// A shallow view of an original BNF item; no source reconstruction is needed.
pub enum LegacyItemView<'input, N, K> {
    Terminal(&'input String),
    NonTerminal {
        ident: &'input N,
        kind: NonTerminalKind,
    },
    Binder {
        category: &'input N,
    },
    Collection {
        kind: &'input K,
        element: &'input N,
        separator: &'input String,
        delimiters: Option<(&'input String, &'input String)>,
    },
}

/// Supplies stable, borrowed input and the original output constructors.
///
/// Readers must observe the same immutable input throughout both scans.
/// Constructors must be total on admitted inputs and must not publish partial
/// output: a later refusal discards the locally constructed prefix. An arena
/// adapter must therefore stage constructor effects privately until success.
/// Original names and generated names may use different owned representations.
pub trait LegacyRuleNormalizationAdapter<'input> {
    type OriginalName: Clone + 'input;
    type GeneratedName: Clone;
    type CollectionKind: Clone + 'input;
    type Param;
    type Syntax;

    fn has_term_context(&self) -> bool;
    fn has_syntax_pattern(&self) -> bool;
    fn items_len(&self) -> usize;
    fn item(
        &self,
        index: usize,
    ) -> LegacyItemView<'input, Self::OriginalName, Self::CollectionKind>;

    fn fresh_name(&mut self, index: usize) -> Self::GeneratedName;
    fn elems_name(&mut self) -> Self::GeneratedName;
    fn make_simple(
        &mut self,
        name: Self::GeneratedName,
        category: Self::OriginalName,
    ) -> Self::Param;
    fn make_abstraction(
        &mut self,
        binder: Self::GeneratedName,
        body: Self::GeneratedName,
        domain: Self::OriginalName,
        codomain: Self::OriginalName,
    ) -> Self::Param;
    fn make_collection(
        &mut self,
        name: Self::GeneratedName,
        kind: Self::CollectionKind,
        element: Self::OriginalName,
    ) -> Self::Param;
    fn make_literal(&mut self, text: String) -> Self::Syntax;
    fn make_param(&mut self, name: Self::GeneratedName) -> Self::Syntax;
    fn make_sep(&mut self, name: Self::GeneratedName, separator: String) -> Self::Syntax;
}

/// Relocated original two-scan algorithm. Only successful output may be committed.
///
/// `None` preserves the entire original rule. `Some` replaces only its term
/// context and syntax pattern, in that order. This iterative loop does not walk
/// nested syntax or types. As in the original implementation, fresh-name counts
/// must fit `usize`; runtime callers must establish that bound before entry.
pub fn normalize_legacy_rule_with<'input, A>(
    adapter: &mut A,
) -> Option<(Vec<A::Param>, Vec<A::Syntax>)>
where
    A: LegacyRuleNormalizationAdapter<'input>,
{
    if adapter.has_term_context() || adapter.has_syntax_pattern() {
        return None;
    }

    // Original complete preflight, before constructing any output.
    for index in 0..adapter.items_len() {
        if let LegacyItemView::NonTerminal { kind, .. } = adapter.item(index) {
            if kind != NonTerminalKind::Category {
                return None;
            }
        }
    }

    let mut tc: Vec<A::Param> = Vec::new();
    let mut sp: Vec<A::Syntax> = Vec::new();
    let mut next_param_id: usize = 0;
    let mut pending_binder: Option<A::OriginalName> = None;

    for index in 0..adapter.items_len() {
        match adapter.item(index) {
            LegacyItemView::Terminal(text) => {
                sp.push(adapter.make_literal(text.clone()));
            },
            LegacyItemView::NonTerminal { ident, kind: NonTerminalKind::Category } => {
                let pname = adapter.fresh_name(next_param_id);
                next_param_id += 1;

                if let Some(binder_cat) = pending_binder.take() {
                    let body_pname = adapter.fresh_name(next_param_id);
                    next_param_id += 1;
                    tc.push(adapter.make_abstraction(
                        pname.clone(),
                        body_pname.clone(),
                        binder_cat,
                        ident.clone(),
                    ));
                    sp.push(adapter.make_param(pname));
                    sp.push(adapter.make_param(body_pname));
                } else {
                    tc.push(adapter.make_simple(pname.clone(), ident.clone()));
                    sp.push(adapter.make_param(pname));
                }
            },
            // Preserve the original defensive refusal even after preflight.
            LegacyItemView::NonTerminal { .. } => return None,
            LegacyItemView::Binder { category } => {
                pending_binder = Some(category.clone());
            },
            LegacyItemView::Collection { kind, element, separator, delimiters } => {
                if let Some((open, close)) = delimiters {
                    let elems_name = adapter.elems_name();
                    tc.push(adapter.make_collection(
                        elems_name.clone(),
                        kind.clone(),
                        element.clone(),
                    ));
                    sp.push(adapter.make_literal(open.clone()));
                    sp.push(adapter.make_sep(elems_name, separator.clone()));
                    sp.push(adapter.make_literal(close.clone()));
                } else {
                    return None;
                }
            },
        }
    }

    if pending_binder.is_some() {
        return None;
    }
    if tc.is_empty() {
        return None;
    }

    Some((tc, sp))
}
