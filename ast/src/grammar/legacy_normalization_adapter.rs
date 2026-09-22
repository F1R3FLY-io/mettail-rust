//! Concrete constructors for the shared original BNF normalization loop.

use proc_macro2::Span;
use syn::Ident;

use super::{GrammarItem, GrammarRule, PatternOp, SyntaxExpr, TermParam};
use crate::legacy_rule_normalization::{LegacyItemView, LegacyRuleNormalizationAdapter};
use crate::types::{CollectionType, TypeExpr};

pub(super) struct GrammarRuleAdapter<'input> {
    pub(super) rule: &'input GrammarRule,
}

impl<'input> LegacyRuleNormalizationAdapter<'input> for GrammarRuleAdapter<'input> {
    type OriginalName = Ident;
    type GeneratedName = Ident;
    type CollectionKind = CollectionType;
    type Param = TermParam;
    type Syntax = SyntaxExpr;

    fn has_term_context(&self) -> bool {
        self.rule.term_context.is_some()
    }

    fn has_syntax_pattern(&self) -> bool {
        self.rule.syntax_pattern.is_some()
    }

    fn items_len(&self) -> usize {
        self.rule.items.len()
    }

    fn item(&self, index: usize) -> LegacyItemView<'input, Ident, CollectionType> {
        match &self.rule.items[index] {
            GrammarItem::Terminal(text) => LegacyItemView::Terminal(text),
            GrammarItem::NonTerminal { ident, kind } => {
                LegacyItemView::NonTerminal { ident, kind: *kind }
            },
            GrammarItem::Binder { category } => LegacyItemView::Binder { category },
            GrammarItem::Collection {
                coll_type,
                element_type,
                separator,
                delimiters,
            } => LegacyItemView::Collection {
                kind: coll_type,
                element: element_type,
                separator,
                delimiters: delimiters.as_ref().map(|(open, close)| (open, close)),
            },
        }
    }

    fn fresh_name(&mut self, index: usize) -> Ident {
        Ident::new(&format!("p{}", index), Span::call_site())
    }

    fn elems_name(&mut self) -> Ident {
        Ident::new("elems", Span::call_site())
    }

    fn make_simple(&mut self, name: Ident, category: Ident) -> TermParam {
        TermParam::Simple { name, ty: TypeExpr::Base(category) }
    }

    fn make_abstraction(
        &mut self,
        binder: Ident,
        body: Ident,
        domain: Ident,
        codomain: Ident,
    ) -> TermParam {
        TermParam::Abstraction {
            binder,
            body,
            ty: TypeExpr::Arrow {
                domain: Box::new(TypeExpr::Base(domain)),
                codomain: Box::new(TypeExpr::Base(codomain)),
            },
        }
    }

    fn make_collection(&mut self, name: Ident, kind: CollectionType, element: Ident) -> TermParam {
        TermParam::Simple {
            name,
            ty: TypeExpr::Collection {
                coll_type: kind,
                element: Box::new(TypeExpr::Base(element)),
            },
        }
    }

    fn make_literal(&mut self, text: String) -> SyntaxExpr {
        SyntaxExpr::Literal(text)
    }

    fn make_param(&mut self, name: Ident) -> SyntaxExpr {
        SyntaxExpr::Param(name)
    }

    fn make_sep(&mut self, name: Ident, separator: String) -> SyntaxExpr {
        SyntaxExpr::Op(PatternOp::Sep {
            collection: name,
            separator,
            source: None,
        })
    }
}
