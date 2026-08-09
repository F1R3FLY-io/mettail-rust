#![allow(warnings)]
// extern crate proc_macro; // Removed - using shim

use quote::{quote, quote_spanned};
use std::collections::{HashMap, HashSet};
use std::sync::Mutex;

use ascent_base::util::update;
use derive_syn_parse::Parse;
use itertools::{Either, Itertools};
use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use syn::parse::{Parse, ParseStream, Parser};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::{
    braced, parenthesized, parse2, Attribute, Error, Expr, ExprMacro, Generics, Ident,
    ImplGenerics, Pat, Path, Result, Token, Type, TypeGenerics, Visibility, WhereClause,
};

use super::syn_utils::{
    expr_get_vars, expr_visit_free_vars_mut, expr_visit_idents_in_macros_mut, pattern_get_vars,
    pattern_visit_vars_mut, token_stream_idents, token_stream_replace_ident,
};
use super::utils::{
    expr_to_ident, expr_to_ident_mut, flatten_punctuated, is_wild_card, pat_to_ident,
    punctuated_map, punctuated_singleton, punctuated_try_map, punctuated_try_unwrap, spans_eq,
    token_stream_replace_macro_idents, Piper,
};
use super::AscentMacroKind;

// resources:
// https://blog.rust-lang.org/2018/12/21/Procedural-Macros-in-Rust-2018.html
// https://github.com/dtolnay/syn/blob/master/examples/lazy-static/lazy-static/src/lib.rs
// https://crates.io/crates/quote
// example: https://gitlab.gnome.org/federico/gnome-class/-/blob/master/src/parser/mod.rs

mod kw {
    use derive_syn_parse::Parse;
    use proc_macro2::Span;
    use syn::Token;

    use super::super::utils::join_spans;

    syn::custom_keyword!(relation);
    syn::custom_keyword!(lattice);
    #[allow(dead_code)] // for unused fields of LongLeftArrow
    #[derive(Parse)]
    pub struct LongLeftArrow(Token![<], Token![-], Token![-]);
    #[allow(unused)]
    impl LongLeftArrow {
        pub fn span(&self) -> Span {
            join_spans([self.0.span, self.1.span, self.2.span])
        }
    }
    syn::custom_keyword!(agg);
    syn::custom_keyword!(ident);
    syn::custom_keyword!(expr);

    syn::custom_keyword!(include_source);
    syn::custom_keyword!(call);
    syn::custom_keyword!(call_schema);
    syn::custom_keyword!(with);
}

#[derive(Clone, Debug)]
pub struct Signatures {
    pub(crate) declaration: TypeSignature,
    pub(crate) implementation: Option<ImplSignature>,
}

impl Signatures {
    pub fn split_ty_generics_for_impl(
        &self,
    ) -> (ImplGenerics<'_>, TypeGenerics<'_>, Option<&'_ WhereClause>) {
        self.declaration.generics.split_for_impl()
    }

    pub fn split_impl_generics_for_impl(
        &self,
    ) -> (ImplGenerics<'_>, TypeGenerics<'_>, Option<&'_ WhereClause>) {
        let Some(signature) = &self.implementation else {
            return self.split_ty_generics_for_impl();
        };

        let (impl_generics, _, _) = signature.impl_generics.split_for_impl();
        let (_, ty_generics, where_clause) = signature.generics.split_for_impl();

        (impl_generics, ty_generics, where_clause)
    }
}

impl Parse for Signatures {
    fn parse(input: ParseStream) -> Result<Self> {
        let declaration = TypeSignature::parse(input)?;
        let implementation = if input.peek(Token![impl]) {
            Some(ImplSignature::parse(input)?)
        } else {
            None
        };
        Ok(Signatures { declaration, implementation })
    }
}

#[derive(Clone, Parse, Debug)]
pub struct TypeSignature {
    // We don't actually use the Parse impl to parse attrs.
    #[call(Attribute::parse_outer)]
    pub attrs: Vec<Attribute>,
    pub visibility: Visibility,
    pub _struct_kw: Token![struct],
    pub ident: Ident,
    #[call(parse_generics_with_where_clause)]
    pub generics: Generics,
    pub _semi: Token![;],
}

#[derive(Clone, Parse, Debug)]
pub struct ImplSignature {
    pub _impl_kw: Token![impl],
    pub impl_generics: Generics,
    pub ident: Ident,
    #[call(parse_generics_with_where_clause)]
    pub generics: Generics,
    pub _semi: Token![;],
}

/// Parse impl on Generics does not parse WhereClauses, hence this function
fn parse_generics_with_where_clause(input: ParseStream) -> Result<Generics> {
    let mut res = Generics::parse(input)?;
    if input.peek(Token![where]) {
        res.where_clause = Some(input.parse()?);
    }
    Ok(res)
}

#[derive(PartialEq, Eq, Clone)]
pub struct RelationNode {
    pub attrs: Vec<Attribute>,
    pub name: Ident,
    pub field_types: Punctuated<Type, Token![,]>,
    pub initialization: Option<Expr>,
    pub _semi_colon: Token![;],
    pub is_lattice: bool,
}

impl Parse for RelationNode {
    fn parse(input: ParseStream) -> Result<Self> {
        let is_lattice = input.peek(kw::lattice);
        if is_lattice {
            input.parse::<kw::lattice>()?;
        } else {
            input.parse::<kw::relation>()?;
        }
        let name: Ident = input.parse()?;
        let content;
        parenthesized!(content in input);
        let field_types = content.parse_terminated(Type::parse, Token![,])?;
        let initialization = if input.peek(Token![=]) {
            input.parse::<Token![=]>()?;
            Some(input.parse::<Expr>()?)
        } else {
            None
        };

        let _semi_colon = input.parse::<Token![;]>()?;
        if is_lattice && field_types.empty_or_trailing() {
            return Err(input.error("empty lattice is not allowed"));
        }
        Ok(RelationNode {
            attrs: vec![],
            name,
            field_types,
            _semi_colon,
            is_lattice,
            initialization,
        })
    }
}

#[derive(Clone, Debug)]
pub struct CallSchemaNode {
    pub name: Ident,
    pub field_types: Punctuated<Type, Token![,]>,
    pub _semi: Token![;],
}

impl Parse for CallSchemaNode {
    fn parse(input: ParseStream) -> Result<Self> {
        input.parse::<kw::call_schema>()?;
        let name: Ident = input.parse()?;
        let content;
        parenthesized!(content in input);
        let field_types = content.parse_terminated(Type::parse, Token![,])?;
        let _semi = input.parse::<Token![;]>()?;
        Ok(CallSchemaNode { name, field_types, _semi })
    }
}

#[derive(Parse)]
pub enum BodyItemNode {
    #[peek(Token![for], name = "generative clause")]
    Generator(GeneratorNode),
    #[peek(kw::agg, name = "aggregate clause")]
    Agg(AggClauseNode),
    #[peek_with(peek_macro_invocation, name = "macro invocation")]
    MacroInvocation(syn::ExprMacro),
    #[peek(kw::call, name = "call goal")]
    Call(CallGoalNode),
    #[peek(Ident, name = "body clause")]
    Clause(BodyClauseNode),
    #[peek(Token![!], name = "negation clause")]
    Negation(NegationClauseNode),
    #[peek(syn::token::Paren, name = "disjunction node")]
    Disjunction(DisjunctionNode),
    #[peek_with(peek_if_or_let, name = "if condition or let binding")]
    Cond(CondClause),
}

fn peek_macro_invocation(parse_stream: ParseStream) -> bool {
    parse_stream.peek(Ident) && parse_stream.peek2(Token![!])
}

fn peek_if_or_let(parse_stream: ParseStream) -> bool {
    parse_stream.peek(Token![if]) || parse_stream.peek(Token![let])
}

#[derive(Parse, Clone)]
enum DisjunctionToken {
    #[allow(unused)]
    #[peek(Token![||], name = "||")]
    OrOr(Token![||]),
    #[allow(unused)]
    #[peek(Token![|], name = "|")]
    Or(Token![|]),
}

pub struct DisjunctionNode {
    paren: syn::token::Paren,
    disjuncts: Punctuated<Punctuated<BodyItemNode, Token![,]>, DisjunctionToken>,
}

struct ConjunctionCloneShape {
    punctuation: Vec<Option<Token![,]>>,
}

struct DisjunctionCloneShape {
    paren: syn::token::Paren,
    conjunctions: Vec<ConjunctionCloneShape>,
    punctuation: Vec<Option<DisjunctionToken>>,
}

enum BodyItemCloneTask<'item> {
    Visit(&'item BodyItemNode),
    FinishDisjunction {
        base: usize,
        shape: DisjunctionCloneShape,
    },
}

fn push_disjunction_clone<'item>(
    disjunction: &'item DisjunctionNode,
    tasks: &mut Vec<BodyItemCloneTask<'item>>,
    base: usize,
) {
    let conjunctions = disjunction
        .disjuncts
        .iter()
        .map(|conjunction| ConjunctionCloneShape {
            punctuation: conjunction
                .pairs()
                .map(|pair| pair.punct().map(|punctuation| (*punctuation).clone()))
                .collect(),
        })
        .collect();
    let punctuation = disjunction
        .disjuncts
        .pairs()
        .map(|pair| pair.punct().map(|punctuation| (*punctuation).clone()))
        .collect();
    tasks.push(BodyItemCloneTask::FinishDisjunction {
        base,
        shape: DisjunctionCloneShape {
            paren: disjunction.paren,
            conjunctions,
            punctuation,
        },
    });
    for conjunction in disjunction.disjuncts.iter().rev() {
        tasks.extend(conjunction.iter().rev().map(BodyItemCloneTask::Visit));
    }
}

fn clone_body_item_with_tasks(mut tasks: Vec<BodyItemCloneTask<'_>>) -> BodyItemNode {
    let mut values = Vec::<BodyItemNode>::new();
    while let Some(task) = tasks.pop() {
        match task {
            BodyItemCloneTask::Visit(item) => match item {
                BodyItemNode::Generator(value) => {
                    values.push(BodyItemNode::Generator(value.clone()))
                },
                BodyItemNode::Agg(value) => values.push(BodyItemNode::Agg(value.clone())),
                BodyItemNode::MacroInvocation(value) => {
                    values.push(BodyItemNode::MacroInvocation(value.clone()))
                },
                BodyItemNode::Call(value) => values.push(BodyItemNode::Call(value.clone())),
                BodyItemNode::Clause(value) => values.push(BodyItemNode::Clause(value.clone())),
                BodyItemNode::Negation(value) => values.push(BodyItemNode::Negation(value.clone())),
                BodyItemNode::Disjunction(disjunction) => {
                    push_disjunction_clone(disjunction, &mut tasks, values.len());
                },
                BodyItemNode::Cond(value) => values.push(BodyItemNode::Cond(value.clone())),
            },
            BodyItemCloneTask::FinishDisjunction { base, shape } => {
                let mut children = values.split_off(base).into_iter();
                let mut disjuncts = Punctuated::new();
                for (conjunction_shape, separator) in
                    shape.conjunctions.into_iter().zip(shape.punctuation)
                {
                    let mut conjunction = Punctuated::new();
                    for punctuation in conjunction_shape.punctuation {
                        conjunction.push_value(
                            children
                                .next()
                                .expect("body-item clone PDA lost a conjunction member"),
                        );
                        if let Some(punctuation) = punctuation {
                            conjunction.push_punct(punctuation);
                        }
                    }
                    disjuncts.push_value(conjunction);
                    if let Some(separator) = separator {
                        disjuncts.push_punct(separator);
                    }
                }
                debug_assert!(children.next().is_none());
                values.push(BodyItemNode::Disjunction(DisjunctionNode {
                    paren: shape.paren,
                    disjuncts,
                }));
            },
        }
    }
    assert_eq!(values.len(), 1, "body-item clone PDA must produce one root");
    values.pop().expect("body-item clone PDA lost its root")
}

impl Clone for BodyItemNode {
    fn clone(&self) -> Self {
        clone_body_item_with_tasks(vec![BodyItemCloneTask::Visit(self)])
    }
}

impl Clone for DisjunctionNode {
    fn clone(&self) -> Self {
        let mut tasks = Vec::new();
        push_disjunction_clone(self, &mut tasks, 0);
        let mut cloned = clone_body_item_with_tasks(tasks);
        match &mut cloned {
            BodyItemNode::Disjunction(disjunction) => std::mem::replace(
                disjunction,
                DisjunctionNode {
                    paren: syn::token::Paren::default(),
                    disjuncts: Punctuated::new(),
                },
            ),
            _ => unreachable!("disjunction clone PDA produced a non-disjunction"),
        }
    }
}

fn take_body_item_children(item: &mut BodyItemNode, work: &mut Vec<BodyItemNode>) {
    if let BodyItemNode::Disjunction(disjunction) = item {
        for conjunction in std::mem::take(&mut disjunction.disjuncts) {
            work.extend(conjunction);
        }
    }
}

impl Drop for BodyItemNode {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_body_item_children(self, &mut work);
        while let Some(mut item) = work.pop() {
            take_body_item_children(&mut item, &mut work);
        }
    }
}

impl Parse for DisjunctionNode {
    fn parse(input: ParseStream) -> Result<Self> {
        let content;
        let paren = parenthesized!(content in input);
        let res: Punctuated<Punctuated<BodyItemNode, Token![,]>, DisjunctionToken> =
         Punctuated::<Punctuated<BodyItemNode, Token![,]>, DisjunctionToken>::parse_terminated_with(
            &content,
            Punctuated::<BodyItemNode, Token![,]>::parse_separated_nonempty,
         )?;
        if res
            .pairs()
            .any(|pair| matches!(pair.punct(), Some(DisjunctionToken::OrOr(_))))
        {
            eprintln!("WARNING: In Ascent rules, use `|` as the disjunction token instead of `||`")
        }
        Ok(DisjunctionNode { paren, disjuncts: res })
    }
}

#[derive(Parse, Clone)]
pub struct GeneratorNode {
    pub for_keyword: Token![for],
    #[call(Pat::parse_multi)]
    pub pattern: Pat,
    pub _in_keyword: Token![in],
    pub expr: Expr,
}

#[derive(Clone)]
pub struct BodyClauseNode {
    pub rel: Ident,
    pub args: Punctuated<BodyClauseArg, Token![,]>,
    pub cond_clauses: Vec<CondClause>,
}

#[derive(Clone)]
pub struct CallGoalNode {
    pub _call_kw: kw::call,
    pub rel_expr: Expr,
    pub args: Punctuated<BodyClauseArg, Token![,]>,
    pub cond_clauses: Vec<CondClause>,
    pub _with_kw: kw::with,
    pub schema_name: Ident,
}

impl Parse for CallGoalNode {
    fn parse(input: ParseStream) -> Result<Self> {
        let _call_kw: kw::call = input.parse()?;
        let content;
        parenthesized!(content in input);
        let rel_expr: Expr = content.parse()?;
        content.parse::<Token![,]>()?;
        let args = content.parse_terminated(BodyClauseArg::parse, Token![,])?;
        if !content.is_empty() {
            return Err(content.error("expected closing parenthesis after call arguments"));
        }
        let mut cond_clauses = vec![];
        while let Ok(cl) = input.parse() {
            cond_clauses.push(cl);
        }
        let _with_kw: kw::with = input.parse().map_err(|_| {
            input.error(
                "call goal requires `with schema_name` (e.g. `call(r, x, y) with edge_schema`)",
            )
        })?;
        let schema_name: Ident = input.parse()?;
        Ok(CallGoalNode {
            _call_kw,
            rel_expr,
            args,
            cond_clauses,
            _with_kw,
            schema_name,
        })
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum BodyClauseArg {
    Pat(ClauseArgPattern),
    Expr(Expr),
}

impl syn::parse::Parse for BodyClauseArg {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        if input.peek(syn::Token![?]) {
            Ok(BodyClauseArg::Pat(input.parse()?))
        } else {
            Ok(BodyClauseArg::Expr(input.parse()?))
        }
    }
}

impl BodyClauseArg {
    pub fn unwrap_expr(self) -> Expr {
        match self {
            Self::Expr(exp) => exp,
            Self::Pat(_) => panic!("unwrap_expr(): BodyClauseArg is not an expr"),
        }
    }

    pub fn unwrap_expr_ref(&self) -> &Expr {
        match self {
            Self::Expr(exp) => exp,
            Self::Pat(_) => panic!("unwrap_expr(): BodyClauseArg is not an expr"),
        }
    }

    pub fn get_vars(&self) -> Vec<Ident> {
        match self {
            BodyClauseArg::Pat(p) => pattern_get_vars(&p.pattern),
            BodyClauseArg::Expr(e) => expr_to_ident(e).into_iter().collect(),
        }
    }
}
impl ToTokens for BodyClauseArg {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            BodyClauseArg::Pat(pat) => {
                pat.huh_token.to_tokens(tokens);
                pat.pattern.to_tokens(tokens);
            },
            BodyClauseArg::Expr(exp) => exp.to_tokens(tokens),
        }
    }
}

#[derive(Parse, Clone, PartialEq, Eq, Debug)]
pub struct ClauseArgPattern {
    pub huh_token: Token![?],
    #[call(Pat::parse_multi)]
    pub pattern: Pat,
}

#[derive(Parse, Clone, PartialEq, Eq, Hash, Debug)]
pub struct IfLetClause {
    pub if_keyword: Token![if],
    pub let_keyword: Token![let],
    #[call(Pat::parse_multi)]
    pub pattern: Pat,
    pub eq_symbol: Token![=],
    pub exp: syn::Expr,
}

#[derive(Parse, Clone, PartialEq, Eq, Hash, Debug)]
pub struct IfClause {
    pub if_keyword: Token![if],
    pub cond: Expr,
}

#[derive(Parse, Clone, PartialEq, Eq, Hash, Debug)]
pub struct LetClause {
    pub let_keyword: Token![let],
    #[call(Pat::parse_multi)]
    pub pattern: Pat,
    pub eq_symbol: Token![=],
    pub exp: syn::Expr,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum CondClause {
    IfLet(IfLetClause),
    If(IfClause),
    Let(LetClause),
}

impl CondClause {
    pub fn bound_vars(&self) -> Vec<Ident> {
        match self {
            CondClause::IfLet(cl) => pattern_get_vars(&cl.pattern),
            CondClause::If(_) => vec![],
            CondClause::Let(cl) => pattern_get_vars(&cl.pattern),
        }
    }

    /// returns the expression associated with the CondClause.
    /// Useful for determining clause dependencies
    pub fn expr(&self) -> &Expr {
        match self {
            CondClause::IfLet(cl) => &cl.exp,
            CondClause::If(cl) => &cl.cond,
            CondClause::Let(cl) => &cl.exp,
        }
    }
}
impl Parse for CondClause {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Token![if]) {
            if input.peek2(Token![let]) {
                let cl: IfLetClause = input.parse()?;
                Ok(Self::IfLet(cl))
            } else {
                let cl: IfClause = input.parse()?;
                Ok(Self::If(cl))
            }
        } else if input.peek(Token![let]) {
            let cl: LetClause = input.parse()?;
            Ok(Self::Let(cl))
        } else {
            Err(input.error("expected either if clause or if let clause"))
        }
    }
}

// impl ToTokens for BodyClauseNode {
//    fn to_tokens(&self, tokens: &mut quote::__private::TokenStream) {
//       self.rel.to_tokens(tokens);
//       self.args.to_tokens(tokens);
//    }
// }

impl Parse for BodyClauseNode {
    fn parse(input: ParseStream) -> Result<Self> {
        let rel: Ident = input.parse()?;
        let args_content;
        parenthesized!(args_content in input);
        let args = args_content.parse_terminated(BodyClauseArg::parse, Token![,])?;
        let mut cond_clauses = vec![];
        while let Ok(cl) = input.parse() {
            cond_clauses.push(cl);
        }
        Ok(BodyClauseNode { rel, args, cond_clauses })
    }
}

/// Goal targeted by negation: either a named relation or a call.
#[derive(Clone)]
pub enum NegationGoal {
    Relation(Ident, Punctuated<Expr, Token![,]>),
    Call(Box<CallGoalNode>),
}

impl Parse for NegationGoal {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(kw::call) {
            Ok(NegationGoal::Call(Box::new(input.parse()?)))
        } else {
            let rel: Ident = input.parse()?;
            let args_content;
            parenthesized!(args_content in input);
            let args = args_content.parse_terminated(Expr::parse, Token![,])?;
            Ok(NegationGoal::Relation(rel, args))
        }
    }
}

#[derive(Clone)]
pub struct NegationClauseNode {
    pub neg_token: Token![!],
    pub goal: NegationGoal,
}

impl Parse for NegationClauseNode {
    fn parse(input: ParseStream) -> Result<Self> {
        let neg_token: Token![!] = input.parse()?;
        let goal = input.parse()?;
        Ok(NegationClauseNode { neg_token, goal })
    }
}

#[derive(Clone, Parse)]
pub enum HeadItemNode {
    #[peek_with(peek_macro_invocation, name = "macro invocation")]
    MacroInvocation(syn::ExprMacro),
    #[peek(Ident, name = "head clause")]
    HeadClause(HeadClauseNode),
}

impl HeadItemNode {
    pub fn clause(&self) -> &HeadClauseNode {
        match self {
            HeadItemNode::HeadClause(cl) => cl,
            HeadItemNode::MacroInvocation(_) => panic!("unexpected macro invocation"),
        }
    }
}

#[derive(Clone)]
pub struct HeadClauseNode {
    pub rel: Ident,
    pub args: Punctuated<Expr, Token![,]>,
}
impl ToTokens for HeadClauseNode {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        self.rel.to_tokens(tokens);
        self.args.to_tokens(tokens);
    }
}

impl Parse for HeadClauseNode {
    fn parse(input: ParseStream) -> Result<Self> {
        let rel: Ident = input.parse()?;
        let args_content;
        parenthesized!(args_content in input);
        let args = args_content.parse_terminated(Expr::parse, Token![,])?;
        Ok(HeadClauseNode { rel, args })
    }
}

/// The goal after `in` in an aggregate: either a named relation or a call.
#[derive(Clone)]
pub enum AggInGoal {
    Relation(Ident, Punctuated<Expr, Token![,]>),
    Call(CallGoalNode),
}

impl Parse for AggInGoal {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(kw::call) {
            Ok(AggInGoal::Call(input.parse()?))
        } else {
            let rel: Ident = input.parse()?;
            let args_content;
            parenthesized!(args_content in input);
            let args = args_content.parse_terminated(Expr::parse, Token![,])?;
            Ok(AggInGoal::Relation(rel, args))
        }
    }
}

#[derive(Clone)]
pub struct AggClauseNode {
    pub agg_kw: kw::agg,
    pub pat: Pat,
    pub _eq_token: Token![=],
    pub aggregator: AggregatorNode,
    pub bound_args: Punctuated<Ident, Token![,]>,
    pub _in_kw: Token![in],
    pub in_goal: AggInGoal,
}

impl Parse for AggClauseNode {
    fn parse(input: ParseStream) -> Result<Self> {
        let agg_kw: kw::agg = input.parse()?;
        let pat = Pat::parse_multi(input)?;
        let _eq_token: Token![=] = input.parse()?;
        let aggregator = input.parse()?;
        let bound_args_content;
        parenthesized!(bound_args_content in input);
        let bound_args = bound_args_content.parse_terminated(Ident::parse, Token![,])?;
        let _in_kw: Token![in] = input.parse()?;
        let in_goal = input.parse()?;
        Ok(AggClauseNode {
            agg_kw,
            pat,
            _eq_token,
            aggregator,
            bound_args,
            _in_kw,
            in_goal,
        })
    }
}

#[derive(Clone)]
pub enum AggregatorNode {
    Path(syn::Path),
    Expr(Expr),
}

impl Parse for AggregatorNode {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(syn::token::Paren) {
            let inside_parens;
            parenthesized!(inside_parens in input);
            Ok(AggregatorNode::Expr(inside_parens.parse()?))
        } else {
            Ok(AggregatorNode::Path(input.parse()?))
        }
    }
}
impl AggregatorNode {
    pub fn get_expr(&self) -> Expr {
        match self {
            AggregatorNode::Path(path) => parse2(quote! {#path}).unwrap(),
            AggregatorNode::Expr(expr) => expr.clone(),
        }
    }
}

pub struct RuleNode {
    pub head_clauses: Punctuated<HeadItemNode, Token![,]>,
    pub body_items: Vec<BodyItemNode>, // Punctuated<BodyItemNode, Token![,]>,
}

impl Parse for RuleNode {
    fn parse(input: ParseStream) -> Result<Self> {
        let head_clauses = if input.peek(syn::token::Brace) {
            let content;
            braced!(content in input);
            Punctuated::<HeadItemNode, Token![,]>::parse_terminated(&content)?
        } else {
            Punctuated::<HeadItemNode, Token![,]>::parse_separated_nonempty(input)?
        };

        if input.peek(Token![;]) {
            input.parse::<Token![;]>()?;
            Ok(RuleNode {
                head_clauses,
                body_items: vec![], /*Punctuated::default()*/
            })
        } else {
            input.parse::<kw::LongLeftArrow>()?;
            let body_items =
                Punctuated::<BodyItemNode, Token![,]>::parse_separated_nonempty(input)?;
            input.parse::<Token![;]>()?;
            Ok(RuleNode {
                head_clauses,
                body_items: body_items.into_iter().collect(),
            })
        }
    }
}

#[allow(dead_code)]
pub fn rule_node_summary(rule: &RuleNode) -> String {
    fn bitem_to_str(bitem: &BodyItemNode) -> String {
        enum SummaryTask<'item> {
            Item(&'item BodyItemNode),
            FinishDisjunction { base: usize, arities: Vec<usize> },
        }

        let mut tasks = vec![SummaryTask::Item(bitem)];
        let mut values = Vec::<String>::new();
        while let Some(task) = tasks.pop() {
            match task {
                SummaryTask::Item(item) => match item {
                    BodyItemNode::Generator(generator) => values.push(format!(
                        "for_{}",
                        pat_to_ident(&generator.pattern)
                            .map(|ident| ident.to_string())
                            .unwrap_or_default()
                    )),
                    BodyItemNode::Clause(clause) => values.push(clause.rel.to_string()),
                    BodyItemNode::Call(call) => {
                        values.push(format!("call(..) with {}", call.schema_name))
                    },
                    BodyItemNode::Disjunction(disjunction) => {
                        let base = values.len();
                        let arities = disjunction
                            .disjuncts
                            .iter()
                            .map(Punctuated::len)
                            .collect::<Vec<_>>();
                        tasks.push(SummaryTask::FinishDisjunction { base, arities });
                        for conjunction in disjunction.disjuncts.iter().rev() {
                            tasks.extend(conjunction.iter().rev().map(SummaryTask::Item));
                        }
                    },
                    BodyItemNode::Cond(_) => values.push("if_".to_string()),
                    BodyItemNode::Agg(aggregate) => {
                        values.push(format!("agg {}", agg_in_goal_summary(&aggregate.in_goal)))
                    },
                    BodyItemNode::Negation(negation) => {
                        values.push(format!("! {}", negation_goal_summary(&negation.goal)))
                    },
                    BodyItemNode::MacroInvocation(invocation) => {
                        values.push(format!("{:?}!(..)", invocation.mac.path))
                    },
                },
                SummaryTask::FinishDisjunction { base, arities } => {
                    let rendered = values.split_off(base);
                    let mut offset = 0usize;
                    let mut branches = Vec::with_capacity(arities.len());
                    for arity in arities {
                        let end = offset + arity;
                        branches.push(rendered[offset..end].join(","));
                        offset = end;
                    }
                    debug_assert_eq!(offset, rendered.len());
                    values.push(format!("({})", branches.join("|")));
                },
            }
        }

        assert_eq!(values.len(), 1, "rule-summary PDA must produce one item");
        values.pop().expect("rule-summary PDA lost its item")
    }
    fn hitem_to_str(hitem: &HeadItemNode) -> String {
        match hitem {
            HeadItemNode::MacroInvocation(m) => format!("{:?}!(..)", m.mac.path),
            HeadItemNode::HeadClause(cl) => cl.rel.to_string(),
        }
    }
    format!(
        "{} <-- {}",
        rule.head_clauses.iter().map(hitem_to_str).join(", "),
        rule.body_items.iter().map(bitem_to_str).join(", ")
    )
}

#[derive(Parse)]
pub struct MacroDefParam {
    _dollar: Token![$],
    name: Ident,
    _colon: Token![:],
    kind: MacroParamKind,
}

#[derive(Parse)]
#[allow(unused)]
pub enum MacroParamKind {
    #[peek(kw::ident, name = "ident")]
    Expr(Ident),
    #[peek(kw::expr, name = "expr")]
    Ident(Ident),
}

#[derive(Parse)]
pub struct MacroDefNode {
    _mac: Token![macro],
    name: Ident,
    #[paren]
    _arg_paren: syn::token::Paren,
    #[inside(_arg_paren)]
    #[call(Punctuated::parse_terminated)]
    params: Punctuated<MacroDefParam, Token![,]>,
    #[brace]
    _body_brace: syn::token::Brace,
    #[inside(_body_brace)]
    body: TokenStream,
}

#[derive(Parse)]
pub struct IncludeSourceNode {
    pub include_source_kw: kw::include_source,
    _bang: Token![!],
    #[paren]
    _arg_paren: syn::token::Paren,
    #[inside(_arg_paren)]
    #[call(syn::Path::parse_mod_style)]
    path: syn::Path,
    _semi: Token![;],
}

// #[derive(Clone)]
pub struct AscentProgram {
    pub rules: Vec<RuleNode>,
    pub relations: Vec<RelationNode>,
    pub signatures: Option<Signatures>,
    pub attributes: Vec<syn::Attribute>,
    pub macros: Vec<MacroDefNode>,
    pub call_schemas: Vec<CallSchemaNode>,
}

/// The output that should be emitted when an `include_source!()` is encountered
pub struct IncludeSourceMacroCall {
    /// the encountered `include_source!()`
    pub include_node: IncludeSourceNode,
    pub before_tokens: TokenStream,
    pub after_tokens: TokenStream,
    pub ascent_macro_name: Path,
}

impl IncludeSourceMacroCall {
    /// The output that should be emitted
    pub fn macro_call_output(&self) -> TokenStream {
        let Self {
            include_node,
            before_tokens,
            after_tokens,
            ascent_macro_name,
        } = self;
        let include_macro_callback = &include_node.path;
        quote_spanned! {include_macro_callback.span()=>
           #include_macro_callback! { {#ascent_macro_name}, {#before_tokens}, {#after_tokens} }
        }
    }
}

pub fn parse_ascent_program(
    input: ParseStream,
    ascent_macro_name: Path,
) -> Result<Either<AscentProgram, IncludeSourceMacroCall>> {
    let input_clone = input.cursor();
    let attributes = Attribute::parse_inner(input)?;
    let mut struct_attrs = Attribute::parse_outer(input)?;
    let signatures = if input.peek(Token![pub]) || input.peek(Token![struct]) {
        let mut signatures = Signatures::parse(input)?;
        signatures.declaration.attrs = std::mem::take(&mut struct_attrs);
        Some(signatures)
    } else {
        None
    };
    let mut rules = vec![];
    let mut relations = vec![];
    let mut macros = vec![];
    let mut call_schemas = vec![];
    while !input.is_empty() {
        let attrs = if !struct_attrs.is_empty() {
            std::mem::take(&mut struct_attrs)
        } else {
            Attribute::parse_outer(input)?
        };
        if input.peek(kw::relation) || input.peek(kw::lattice) {
            let mut relation_node = RelationNode::parse(input)?;
            relation_node.attrs = attrs;
            relations.push(relation_node);
        } else if input.peek(kw::call_schema) {
            if !attrs.is_empty() {
                return Err(Error::new(attrs[0].span(), "unexpected attribute(s)"));
            }
            call_schemas.push(CallSchemaNode::parse(input)?);
        } else if input.peek(Token![macro]) {
            if !attrs.is_empty() {
                return Err(Error::new(attrs[0].span(), "unexpected attribute(s)"));
            }
            macros.push(MacroDefNode::parse(input)?);
        } else if input.peek(kw::include_source) {
            if !attrs.is_empty() {
                return Err(Error::new(attrs[0].span(), "unexpected attribute(s)"));
            }
            let before_tokens = input_clone
                .token_stream()
                .into_iter()
                .take_while(|tt| !spans_eq(&tt.span(), &input.span()))
                .collect::<TokenStream>();
            let include_node = IncludeSourceNode::parse(input)?;
            let after_tokens: TokenStream = input.parse()?;
            let include_source_macro_call = IncludeSourceMacroCall {
                include_node,
                before_tokens,
                after_tokens,
                ascent_macro_name,
            };
            return Ok(Either::Right(include_source_macro_call));
        } else {
            if !attrs.is_empty() {
                return Err(Error::new(attrs[0].span(), "unexpected attribute(s)"));
            }
            rules.push(RuleNode::parse(input)?);
        }
    }
    Ok(Either::Left(AscentProgram {
        rules,
        relations,
        signatures,
        attributes,
        macros,
        call_schemas,
    }))
}

impl Parse for AscentProgram {
    fn parse(input: ParseStream) -> Result<Self> {
        match parse_ascent_program(input, AscentMacroKind::default().macro_path(Span::call_site()))?
        {
            Either::Left(parsed) => Ok(parsed),
            Either::Right(include) => Err(Error::new(
                include.include_node.include_source_kw.span(),
                "Encountered `include_source!`",
            )),
        }
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct RelationIdentity {
    pub name: Ident,
    pub field_types: Vec<Type>,
    pub is_lattice: bool,
}

impl From<&RelationNode> for RelationIdentity {
    fn from(relation_node: &RelationNode) -> Self {
        RelationIdentity {
            name: relation_node.name.clone(),
            field_types: relation_node.field_types.iter().cloned().collect(),
            is_lattice: relation_node.is_lattice,
        }
    }
}

#[derive(Clone)]
pub struct DsAttributeContents {
    pub path: syn::Path,
    pub args: TokenStream,
}

impl Parse for DsAttributeContents {
    fn parse(input: ParseStream) -> Result<Self> {
        let path = syn::Path::parse_mod_style(input)?;
        let args = if input.peek(Token![:]) {
            input.parse::<Token![:]>()?;
            TokenStream::parse(input)?
        } else {
            TokenStream::default()
        };

        Ok(Self { path, args })
    }
}

fn rule_desugar_disjunction_nodes(rule: RuleNode) -> Vec<RuleNode> {
    enum DesugarJob<'item> {
        Item(&'item BodyItemNode),
        Sequence(&'item [BodyItemNode]),
        PunctuatedSequence(&'item Punctuated<BodyItemNode, Token![,]>),
        CombineSequence(usize),
        CombineDisjunction(usize),
    }

    fn desugar_body_items(items: &[BodyItemNode]) -> Vec<Vec<BodyItemNode>> {
        let mut jobs = vec![DesugarJob::Sequence(items)];
        let mut values = Vec::<Vec<Vec<BodyItemNode>>>::new();

        while let Some(job) = jobs.pop() {
            match job {
                DesugarJob::Item(item) => match item {
                    BodyItemNode::Generator(_)
                    | BodyItemNode::Clause(_)
                    | BodyItemNode::Call(_)
                    | BodyItemNode::Cond(_)
                    | BodyItemNode::Agg(_)
                    | BodyItemNode::Negation(_) => values.push(vec![vec![item.clone()]]),
                    BodyItemNode::Disjunction(disjunction) => {
                        jobs.push(DesugarJob::CombineDisjunction(disjunction.disjuncts.len()));
                        jobs.extend(
                            disjunction
                                .disjuncts
                                .iter()
                                .rev()
                                .map(DesugarJob::PunctuatedSequence),
                        );
                    },
                    BodyItemNode::MacroInvocation(invocation) => {
                        panic!("unexpected macro invocation: {:?}", invocation.mac.path)
                    },
                },
                DesugarJob::Sequence(sequence) => {
                    if sequence.is_empty() {
                        values.push(vec![Vec::new()]);
                    } else {
                        jobs.push(DesugarJob::CombineSequence(sequence.len()));
                        jobs.extend(sequence.iter().rev().map(DesugarJob::Item));
                    }
                },
                DesugarJob::PunctuatedSequence(sequence) => {
                    if sequence.is_empty() {
                        values.push(vec![Vec::new()]);
                    } else {
                        jobs.push(DesugarJob::CombineSequence(sequence.len()));
                        jobs.extend(sequence.iter().rev().map(DesugarJob::Item));
                    }
                },
                DesugarJob::CombineSequence(arity) => {
                    let split = values
                        .len()
                        .checked_sub(arity)
                        .expect("disjunction PDA sequence underflow");
                    let item_alternatives = values.split_off(split);
                    let mut combinations = vec![Vec::new()];
                    for alternatives in item_alternatives {
                        let mut next = Vec::new();
                        for prefix in combinations {
                            for alternative in &alternatives {
                                let mut combination = prefix.clone();
                                combination.extend(alternative.iter().cloned());
                                next.push(combination);
                            }
                        }
                        combinations = next;
                    }
                    values.push(combinations);
                },
                DesugarJob::CombineDisjunction(arity) => {
                    let split = values
                        .len()
                        .checked_sub(arity)
                        .expect("disjunction PDA branch underflow");
                    let branches = values.split_off(split);
                    values.push(branches.into_iter().flatten().collect());
                },
            }
        }

        assert_eq!(values.len(), 1, "disjunction PDA must produce one root value");
        values.pop().expect("disjunction PDA lost its root value")
    }

    let mut res = vec![];
    for conjunction in desugar_body_items(&rule.body_items) {
        res.push(RuleNode {
            body_items: conjunction,
            head_clauses: rule.head_clauses.clone(),
        })
    }
    res
}

fn body_item_get_bound_vars(bi: &BodyItemNode) -> Vec<Ident> {
    let mut bound = Vec::new();
    let mut work = vec![bi];
    while let Some(item) = work.pop() {
        match item {
            BodyItemNode::Generator(generator) => {
                bound.extend(pattern_get_vars(&generator.pattern));
            },
            BodyItemNode::Agg(aggregate) => bound.extend(pattern_get_vars(&aggregate.pat)),
            BodyItemNode::Clause(clause) => {
                for argument in &clause.args {
                    bound.extend(argument.get_vars());
                }
            },
            BodyItemNode::Call(call) => {
                for argument in &call.args {
                    bound.extend(argument.get_vars());
                }
            },
            BodyItemNode::Negation(_) | BodyItemNode::MacroInvocation(_) => {},
            BodyItemNode::Disjunction(disjunction) => {
                for conjunction in disjunction.disjuncts.iter().rev() {
                    work.extend(conjunction.iter().rev());
                }
            },
            BodyItemNode::Cond(clause) => bound.extend(clause.bound_vars()),
        }
    }
    bound
}

fn body_item_visit_bound_vars_mut(bi: &mut BodyItemNode, visitor: &mut dyn FnMut(&mut Ident)) {
    let mut work = vec![bi];
    while let Some(item) = work.pop() {
        match item {
            BodyItemNode::Generator(generator) => {
                pattern_visit_vars_mut(&mut generator.pattern, visitor)
            },
            BodyItemNode::Agg(aggregate) => pattern_visit_vars_mut(&mut aggregate.pat, visitor),
            BodyItemNode::Clause(clause) => {
                for argument in &mut clause.args {
                    match argument {
                        BodyClauseArg::Pat(pattern) => {
                            pattern_visit_vars_mut(&mut pattern.pattern, visitor)
                        },
                        BodyClauseArg::Expr(expression) => {
                            if let Some(ident) = expr_to_ident_mut(expression) {
                                visitor(ident)
                            }
                        },
                    }
                }
            },
            BodyItemNode::Call(call) => {
                for argument in &mut call.args {
                    match argument {
                        BodyClauseArg::Pat(pattern) => {
                            pattern_visit_vars_mut(&mut pattern.pattern, visitor)
                        },
                        BodyClauseArg::Expr(expression) => {
                            if let Some(ident) = expr_to_ident_mut(expression) {
                                visitor(ident)
                            }
                        },
                    }
                }
            },
            BodyItemNode::Negation(_) | BodyItemNode::MacroInvocation(_) => {},
            BodyItemNode::Disjunction(disjunction) => {
                for conjunction in disjunction.disjuncts.iter_mut().rev() {
                    work.extend(conjunction.iter_mut().rev());
                }
            },
            BodyItemNode::Cond(clause) => match clause {
                CondClause::IfLet(clause) => pattern_visit_vars_mut(&mut clause.pattern, visitor),
                CondClause::If(_) => {},
                CondClause::Let(clause) => pattern_visit_vars_mut(&mut clause.pattern, visitor),
            },
        }
    }
}

fn body_item_visit_exprs_free_vars_mut(
    bi: &mut BodyItemNode,
    visitor: &mut dyn FnMut(&mut Ident),
    visit_macro_idents: bool,
) {
    fn visit_expression(
        expr: &mut Expr,
        visitor: &mut dyn FnMut(&mut Ident),
        visit_macro_idents: bool,
    ) {
        expr_visit_free_vars_mut(expr, visitor);
        if visit_macro_idents {
            expr_visit_idents_in_macros_mut(expr, visitor);
        }
    }

    let mut work = vec![bi];
    while let Some(item) = work.pop() {
        match item {
            BodyItemNode::Generator(generator) => {
                visit_expression(&mut generator.expr, visitor, visit_macro_idents)
            },
            BodyItemNode::Agg(aggregate) => {
                let mut visit =
                    |expr: &mut Expr| visit_expression(expr, visitor, visit_macro_idents);
                agg_in_goal_visit_exprs_mut(&mut aggregate.in_goal, &mut visit);
                if let AggregatorNode::Expr(expression) = &mut aggregate.aggregator {
                    visit(expression)
                }
            },
            BodyItemNode::Clause(clause) => {
                for argument in &mut clause.args {
                    if let BodyClauseArg::Expr(expression) = argument {
                        visit_expression(expression, visitor, visit_macro_idents);
                    }
                }
            },
            BodyItemNode::Negation(negation) => {
                let mut visit =
                    |expr: &mut Expr| visit_expression(expr, visitor, visit_macro_idents);
                negation_goal_visit_exprs_mut(&mut negation.goal, &mut visit);
            },
            BodyItemNode::Disjunction(disjunction) => {
                for conjunction in disjunction.disjuncts.iter_mut().rev() {
                    work.extend(conjunction.iter_mut().rev());
                }
            },
            BodyItemNode::Cond(clause) => match clause {
                CondClause::IfLet(clause) => {
                    visit_expression(&mut clause.exp, visitor, visit_macro_idents)
                },
                CondClause::If(clause) => {
                    visit_expression(&mut clause.cond, visitor, visit_macro_idents)
                },
                CondClause::Let(clause) => {
                    visit_expression(&mut clause.exp, visitor, visit_macro_idents)
                },
            },
            BodyItemNode::Call(call) => {
                visit_expression(&mut call.rel_expr, visitor, visit_macro_idents);
                for argument in &mut call.args {
                    if let BodyClauseArg::Expr(expression) = argument {
                        visit_expression(expression, visitor, visit_macro_idents);
                    }
                }
            },
            BodyItemNode::MacroInvocation(invocation) => {
                update(&mut invocation.mac.tokens, |tokens| {
                    token_stream_replace_ident(tokens, visitor)
                });
            },
        }
    }
}

#[derive(Clone)]
struct GenSym(HashMap<String, u32>, fn(&str) -> String);
impl GenSym {
    pub fn next(&mut self, ident: &str) -> String {
        match self.0.get_mut(ident) {
            Some(n) => {
                *n += 1;
                format!("{}{}", self.1(ident), *n - 1)
            },
            None => {
                self.0.insert(ident.into(), 1);
                self.1(ident)
            },
        }
    }
    pub fn next_ident(&mut self, ident: &str, span: Span) -> Ident {
        Ident::new(&self.next(ident), span)
    }
    pub fn new(transformer: fn(&str) -> String) -> Self {
        Self(Default::default(), transformer)
    }
}

impl Default for GenSym {
    fn default() -> Self {
        Self(Default::default(), |x| format!("{}_", x))
    }
}

fn body_items_rename_macro_originated_vars(
    bis: &mut [&mut BodyItemNode],
    macro_def: &MacroDefNode,
    gensym: &mut GenSym,
) {
    let bi_vars = bis
        .iter()
        .flat_map(|bi| body_item_get_bound_vars(bi))
        .collect_vec();
    let mut mac_body_idents = token_stream_idents(macro_def.body.clone());
    mac_body_idents.retain(|ident| bi_vars.contains(ident));

    let macro_originated_vars = bi_vars
        .iter()
        .filter(|v| {
            mac_body_idents
                .iter()
                .any(|ident| spans_eq(&v.span(), &ident.span()))
        })
        .cloned()
        .collect::<HashSet<_>>();

    let var_mappings = macro_originated_vars
        .iter()
        .map(|v| (v, gensym.next(&v.to_string())))
        .collect::<HashMap<_, _>>();
    let mut visitor = |ident: &mut Ident| {
        if let Some(replacement) = var_mappings.get(ident) {
            if mac_body_idents
                .iter()
                .any(|mac_ident| spans_eq(&mac_ident.span(), &ident.span()))
            {
                *ident = Ident::new(replacement, ident.span())
            }
        }
    };
    for bi in bis.iter_mut() {
        body_item_visit_bound_vars_mut(bi, &mut visitor);
        body_item_visit_exprs_free_vars_mut(bi, &mut visitor, true);
    }
}

fn rule_desugar_pattern_args(rule: RuleNode) -> RuleNode {
    fn clause_desugar_pattern_args(
        body_clause: BodyClauseNode,
        gensym: &mut GenSym,
    ) -> BodyClauseNode {
        let mut new_args = Punctuated::new();
        let mut new_cond_clauses = vec![];
        for arg in body_clause.args.into_pairs() {
            let (arg, punc) = arg.into_tuple();
            let new_arg = match arg {
                BodyClauseArg::Expr(_) => arg,
                BodyClauseArg::Pat(pat) => {
                    let pattern = pat.pattern;
                    let ident = gensym.next_ident("__arg_pattern", pattern.span());
                    let new_cond_clause = quote! { if let #pattern = #ident};
                    let new_cond_clause = CondClause::IfLet(syn::parse2(new_cond_clause).unwrap());
                    new_cond_clauses.push(new_cond_clause);
                    BodyClauseArg::Expr(syn::parse2(quote! {#ident}).unwrap())
                },
            };
            new_args.push_value(new_arg);
            if let Some(punc) = punc {
                new_args.push_punct(punc)
            }
        }
        new_cond_clauses.extend(body_clause.cond_clauses);
        BodyClauseNode {
            args: new_args,
            cond_clauses: new_cond_clauses,
            rel: body_clause.rel,
        }
    }
    fn call_desugar_pattern_args(call_node: CallGoalNode, gensym: &mut GenSym) -> CallGoalNode {
        let mut new_args = Punctuated::new();
        let mut new_cond_clauses = vec![];
        for arg in call_node.args.into_pairs() {
            let (arg, punc) = arg.into_tuple();
            let new_arg = match arg {
                BodyClauseArg::Expr(_) => arg,
                BodyClauseArg::Pat(pat) => {
                    let pattern = pat.pattern;
                    let ident = gensym.next_ident("__arg_pattern", pattern.span());
                    let new_cond_clause = quote! { if let #pattern = #ident};
                    let new_cond_clause = CondClause::IfLet(syn::parse2(new_cond_clause).unwrap());
                    new_cond_clauses.push(new_cond_clause);
                    BodyClauseArg::Expr(syn::parse2(quote! {#ident}).unwrap())
                },
            };
            new_args.push_value(new_arg);
            if let Some(punc) = punc {
                new_args.push_punct(punc)
            }
        }
        new_cond_clauses.extend(call_node.cond_clauses);
        CallGoalNode {
            _call_kw: call_node._call_kw,
            rel_expr: call_node.rel_expr,
            args: new_args,
            cond_clauses: new_cond_clauses,
            _with_kw: call_node._with_kw,
            schema_name: call_node.schema_name,
        }
    }
    let mut gensym = GenSym::default();
    RuleNode {
        body_items: rule
            .body_items
            .into_iter()
            .map(|bi| match &bi {
                BodyItemNode::Clause(clause) => {
                    BodyItemNode::Clause(clause_desugar_pattern_args(clause.clone(), &mut gensym))
                },
                BodyItemNode::Call(call) => {
                    BodyItemNode::Call(call_desugar_pattern_args(call.clone(), &mut gensym))
                },
                _ => bi,
            })
            .collect(),
        head_clauses: rule.head_clauses,
    }
}

fn rule_desugar_repeated_vars(mut rule: RuleNode) -> RuleNode {
    let mut grounded_vars = HashMap::<Ident, usize>::new();
    for i in 0..rule.body_items.len() {
        let bitem = &mut rule.body_items[i];
        match bitem {
            BodyItemNode::Clause(cl) => {
                let mut new_cond_clauses = vec![];
                for arg_ind in 0..cl.args.len() {
                    let expr = cl.args[arg_ind].unwrap_expr_ref();
                    let expr_has_vars_from_same_clause = expr_get_vars(expr).iter().any(|var| {
                        if let Some(cl_ind) = grounded_vars.get(var) {
                            *cl_ind == i
                        } else {
                            false
                        }
                    });
                    if expr_has_vars_from_same_clause {
                        let new_ident = fresh_ident(
                            &expr_to_ident(expr)
                                .map(|e| e.to_string())
                                .unwrap_or_else(|| "expr_replaced".to_string()),
                            expr.span(),
                        );
                        new_cond_clauses.push(CondClause::If(
                            parse2(quote_spanned! {expr.span()=> if #new_ident.eq(&(#expr))})
                                .unwrap(),
                        ));
                        cl.args[arg_ind] =
                            BodyClauseArg::Expr(parse2(new_ident.to_token_stream()).unwrap());
                    } else if let Some(ident) = expr_to_ident(expr) {
                        grounded_vars.entry(ident).or_insert(i);
                    }
                }
                for new_cond_cl in new_cond_clauses.into_iter().rev() {
                    cl.cond_clauses.insert(0, new_cond_cl);
                }
            },
            BodyItemNode::Generator(gen) => {
                for ident in pattern_get_vars(&gen.pattern) {
                    grounded_vars.entry(ident).or_insert(i);
                }
            },
            BodyItemNode::Cond(ref cond_cl @ CondClause::IfLet(_))
            | BodyItemNode::Cond(ref cond_cl @ CondClause::Let(_)) => {
                for ident in cond_cl.bound_vars() {
                    grounded_vars.entry(ident).or_insert(i);
                }
            },
            BodyItemNode::Cond(CondClause::If(_)) => (),
            BodyItemNode::Agg(agg) => {
                for ident in pattern_get_vars(&agg.pat) {
                    grounded_vars.entry(ident).or_insert(i);
                }
            },
            BodyItemNode::Negation(_) => (),
            BodyItemNode::Call(cl) => {
                let mut new_cond_clauses = vec![];
                for arg_ind in 0..cl.args.len() {
                    let expr = cl.args[arg_ind].unwrap_expr_ref();
                    let expr_has_vars_from_same_clause = expr_get_vars(expr).iter().any(|var| {
                        if let Some(cl_ind) = grounded_vars.get(var) {
                            *cl_ind == i
                        } else {
                            false
                        }
                    });
                    if expr_has_vars_from_same_clause {
                        let new_ident = fresh_ident(
                            &expr_to_ident(expr)
                                .map(|e| e.to_string())
                                .unwrap_or_else(|| "expr_replaced".to_string()),
                            expr.span(),
                        );
                        new_cond_clauses.push(CondClause::If(
                            parse2(quote_spanned! {expr.span()=> if #new_ident.eq(&(#expr))})
                                .unwrap(),
                        ));
                        cl.args[arg_ind] =
                            BodyClauseArg::Expr(parse2(new_ident.to_token_stream()).unwrap());
                    } else if let Some(ident) = expr_to_ident(expr) {
                        grounded_vars.entry(ident).or_insert(i);
                    }
                }
                for new_cond_cl in new_cond_clauses.into_iter().rev() {
                    cl.cond_clauses.insert(0, new_cond_cl);
                }
                for cond_cl in cl.cond_clauses.iter() {
                    for ident in cond_cl.bound_vars() {
                        grounded_vars.entry(ident).or_insert(i);
                    }
                }
            },
            BodyItemNode::Disjunction(_) => panic!("unrecognized BodyItemNode variant"),
            BodyItemNode::MacroInvocation(m) => {
                panic!("unexpected macro invocation: {:?}", m.mac.path)
            },
        }
    }
    rule
}

fn rule_desugar_wildcards(mut rule: RuleNode) -> RuleNode {
    let mut gensym = GenSym::default();
    gensym.next("_"); // to move past "_"
    for bi in &mut rule.body_items[..] {
        match bi {
            BodyItemNode::Clause(bcl) => {
                for arg in bcl.args.iter_mut() {
                    match arg {
                        BodyClauseArg::Expr(expr) => {
                            if is_wild_card(expr) {
                                let new_ident = gensym.next_ident("_", expr.span());
                                *expr = parse2(quote! {#new_ident}).unwrap();
                            }
                        },
                        BodyClauseArg::Pat(_) => (),
                    }
                }
            },
            BodyItemNode::Call(bcl) => {
                for arg in bcl.args.iter_mut() {
                    match arg {
                        BodyClauseArg::Expr(expr) => {
                            if is_wild_card(expr) {
                                let new_ident = gensym.next_ident("_", expr.span());
                                *expr = parse2(quote! {#new_ident}).unwrap();
                            }
                        },
                        BodyClauseArg::Pat(_) => (),
                    }
                }
            },
            _ => (),
        }
    }
    rule
}

fn agg_in_goal_summary(goal: &AggInGoal) -> String {
    match goal {
        AggInGoal::Relation(rel, _) => rel.to_string(),
        AggInGoal::Call(c) => format!("call(..) with {}", c.schema_name),
    }
}

fn negation_goal_summary(goal: &NegationGoal) -> String {
    match goal {
        NegationGoal::Relation(rel, _) => rel.to_string(),
        NegationGoal::Call(c) => format!("call(..) with {}", c.schema_name),
    }
}

fn agg_in_goal_visit_exprs_mut(goal: &mut AggInGoal, visit: &mut dyn FnMut(&mut Expr)) {
    match goal {
        AggInGoal::Relation(_, args) => {
            for arg in args.iter_mut() {
                visit(arg);
            }
        },
        AggInGoal::Call(c) => {
            for arg in c.args.iter_mut() {
                if let BodyClauseArg::Expr(e) = arg {
                    visit(e);
                }
            }
        },
    }
}

fn negation_goal_visit_exprs_mut(goal: &mut NegationGoal, visit: &mut dyn FnMut(&mut Expr)) {
    match goal {
        NegationGoal::Relation(_, args) => {
            for arg in args.iter_mut() {
                visit(arg);
            }
        },
        NegationGoal::Call(c) => {
            for arg in c.args.iter_mut() {
                if let BodyClauseArg::Expr(e) = arg {
                    visit(e);
                }
            }
        },
    }
}

fn rule_desugar_negation(mut rule: RuleNode) -> RuleNode {
    for bi in &mut rule.body_items[..] {
        if let BodyItemNode::Negation(neg) = bi {
            let replacement = match &neg.goal {
                NegationGoal::Relation(rel, args) => {
                    let r = quote_spanned! {neg.neg_token.span=> agg () = ::ascent::aggregators::not() in #rel(#args) };
                    parse2::<AggClauseNode>(r).unwrap()
                },
                NegationGoal::Call(call_node) => {
                    let rel_expr = &call_node.rel_expr;
                    let args = &call_node.args;
                    let schema_name = &call_node.schema_name;
                    let r = quote_spanned! {neg.neg_token.span=> agg () = ::ascent::aggregators::not() in call(#rel_expr, #args) with #schema_name };
                    parse2::<AggClauseNode>(r).unwrap()
                },
            };
            *bi = BodyItemNode::Agg(replacement);
        }
    }
    rule
}

fn invoke_macro(invocation: &ExprMacro, definition: &MacroDefNode) -> Result<TokenStream> {
    let tokens = invocation.mac.tokens.clone();

    fn parse_args(
        definition: &MacroDefNode,
        args: ParseStream,
        span: Span,
    ) -> Result<HashMap<Ident, TokenStream>> {
        let mut ident_replacement = HashMap::new();

        for pair in definition.params.pairs() {
            if args.is_empty() {
                return Err(Error::new(span, "expected more arguments"));
            }
            let (param, comma) = pair.into_tuple();
            let arg = match param.kind {
                MacroParamKind::Expr(_) => args.parse::<Ident>()?.into_token_stream(),
                MacroParamKind::Ident(_) => args.parse::<Expr>()?.into_token_stream(),
            };

            ident_replacement.insert(param.name.clone(), arg);
            if comma.is_some() {
                if args.is_empty() {
                    return Err(Error::new(span, "expected more arguments"));
                }
                args.parse::<Token![,]>()?;
            }
        }

        Ok(ident_replacement)
    }

    let args_parser = |inp: ParseStream| parse_args(definition, inp, invocation.mac.span());
    let args_parsed = Parser::parse2(args_parser, tokens)?;

    let replaced_body = token_stream_replace_macro_idents(definition.body.clone(), &args_parsed);
    Ok(replaced_body)
}

fn rule_expand_macro_invocations(
    rule: RuleNode,
    macros: &HashMap<Ident, &MacroDefNode>,
) -> Result<RuleNode> {
    const RECURSIVE_MACRO_ERROR: &'static str = "recursively defined Ascent macro";
    struct BodySequenceShape {
        punctuation: Vec<Option<Token![,]>>,
    }

    enum BodyExpansionTask<'definition> {
        Item(BodyItemNode),
        Sequence(Punctuated<BodyItemNode, Token![,]>),
        FinishSequence {
            base: usize,
            shape: BodySequenceShape,
        },
        FinishMacro {
            name: String,
            definition: &'definition MacroDefNode,
        },
        FinishDisjunction {
            base: usize,
            paren: syn::token::Paren,
            punctuation: Vec<Option<DisjunctionToken>>,
        },
    }

    fn expand_body_item(
        item: BodyItemNode,
        macros: &HashMap<Ident, &MacroDefNode>,
        gensym: &mut GenSym,
    ) -> Result<Punctuated<BodyItemNode, Token![,]>> {
        let mut tasks = vec![BodyExpansionTask::Item(item)];
        let mut values = Vec::<Punctuated<BodyItemNode, Token![,]>>::new();
        let mut active_macros = HashSet::<String>::new();

        while let Some(task) = tasks.pop() {
            match task {
                BodyExpansionTask::Item(mut item) => match &mut item {
                    BodyItemNode::MacroInvocation(invocation) => {
                        let name = invocation
                            .mac
                            .path
                            .get_ident()
                            .expect("Ascent macro invocations have identifier paths");
                        let definition = macros
                            .get(name)
                            .ok_or_else(|| Error::new(invocation.span(), "undefined macro"))?;
                        let name = name.to_string();
                        if !active_macros.insert(name.clone()) {
                            return Err(Error::new(invocation.span(), RECURSIVE_MACRO_ERROR));
                        }
                        let expanded = Parser::parse2(
                            Punctuated::<BodyItemNode, Token![,]>::parse_terminated,
                            invoke_macro(invocation, definition)?,
                        )?;
                        tasks.push(BodyExpansionTask::FinishMacro { name, definition });
                        tasks.push(BodyExpansionTask::Sequence(expanded));
                    },
                    BodyItemNode::Disjunction(disjunction) => {
                        let disjuncts = std::mem::take(&mut disjunction.disjuncts);
                        let paren = disjunction.paren;
                        let punctuation = disjuncts
                            .pairs()
                            .map(|pair| pair.punct().map(|punctuation| (*punctuation).clone()))
                            .collect::<Vec<_>>();
                        let branches = disjuncts.into_iter().collect::<Vec<_>>();
                        let base = values.len();
                        tasks.push(BodyExpansionTask::FinishDisjunction {
                            base,
                            paren,
                            punctuation,
                        });
                        tasks.extend(branches.into_iter().rev().map(BodyExpansionTask::Sequence));
                    },
                    _ => values.push(punctuated_singleton(item)),
                },
                BodyExpansionTask::Sequence(sequence) => {
                    let punctuation = sequence
                        .pairs()
                        .map(|pair| pair.punct().map(|punctuation| (*punctuation).clone()))
                        .collect();
                    let items = sequence.into_iter().collect::<Vec<_>>();
                    let base = values.len();
                    tasks.push(BodyExpansionTask::FinishSequence {
                        base,
                        shape: BodySequenceShape { punctuation },
                    });
                    tasks.extend(items.into_iter().rev().map(BodyExpansionTask::Item));
                },
                BodyExpansionTask::FinishSequence { base, shape } => {
                    let expanded = values.split_off(base);
                    debug_assert_eq!(expanded.len(), shape.punctuation.len());
                    let mut nested = Punctuated::new();
                    for (items, punctuation) in expanded.into_iter().zip(shape.punctuation) {
                        nested.push_value(items);
                        if let Some(punctuation) = punctuation {
                            nested.push_punct(punctuation);
                        }
                    }
                    values.push(flatten_punctuated(nested));
                },
                BodyExpansionTask::FinishMacro { name, definition } => {
                    let mut expanded = values
                        .pop()
                        .expect("body macro-expansion PDA lost an expanded body");
                    body_items_rename_macro_originated_vars(
                        &mut expanded.iter_mut().collect_vec(),
                        definition,
                        gensym,
                    );
                    assert!(
                        active_macros.remove(&name),
                        "body macro-expansion PDA lost its active macro"
                    );
                    values.push(expanded);
                },
                BodyExpansionTask::FinishDisjunction { base, paren, punctuation } => {
                    let branches = values.split_off(base);
                    debug_assert_eq!(branches.len(), punctuation.len());
                    let mut disjuncts = Punctuated::new();
                    for (branch, punctuation) in branches.into_iter().zip(punctuation) {
                        disjuncts.push_value(branch);
                        if let Some(punctuation) = punctuation {
                            disjuncts.push_punct(punctuation);
                        }
                    }
                    values.push(punctuated_singleton(BodyItemNode::Disjunction(DisjunctionNode {
                        paren,
                        disjuncts,
                    })));
                },
            }
        }

        assert!(active_macros.is_empty(), "body macro-expansion PDA left an active macro");
        assert_eq!(values.len(), 1, "body macro-expansion PDA must produce one root");
        Ok(values
            .pop()
            .expect("body macro-expansion PDA lost its root"))
    }

    struct HeadSequenceShape {
        punctuation: Vec<Option<Token![,]>>,
    }

    enum HeadExpansionTask {
        Item(HeadItemNode),
        Sequence(Punctuated<HeadItemNode, Token![,]>),
        FinishSequence { base: usize, shape: HeadSequenceShape },
        FinishMacro { name: String },
    }

    fn expand_head_items(
        items: Punctuated<HeadItemNode, Token![,]>,
        macros: &HashMap<Ident, &MacroDefNode>,
    ) -> Result<Punctuated<HeadItemNode, Token![,]>> {
        let mut tasks = vec![HeadExpansionTask::Sequence(items)];
        let mut values = Vec::<Punctuated<HeadItemNode, Token![,]>>::new();
        let mut active_macros = HashSet::<String>::new();

        while let Some(task) = tasks.pop() {
            match task {
                HeadExpansionTask::Item(item) => match item {
                    HeadItemNode::MacroInvocation(invocation) => {
                        let name = invocation
                            .mac
                            .path
                            .get_ident()
                            .expect("Ascent macro invocations have identifier paths");
                        let definition = macros
                            .get(name)
                            .ok_or_else(|| Error::new(invocation.span(), "undefined macro"))?;
                        let name = name.to_string();
                        if !active_macros.insert(name.clone()) {
                            return Err(Error::new(invocation.span(), RECURSIVE_MACRO_ERROR));
                        }
                        let expanded = Parser::parse2(
                            Punctuated::<HeadItemNode, Token![,]>::parse_terminated,
                            invoke_macro(&invocation, definition)?,
                        )?;
                        tasks.push(HeadExpansionTask::FinishMacro { name });
                        tasks.push(HeadExpansionTask::Sequence(expanded));
                    },
                    HeadItemNode::HeadClause(_) => values.push(punctuated_singleton(item)),
                },
                HeadExpansionTask::Sequence(sequence) => {
                    let punctuation = sequence
                        .pairs()
                        .map(|pair| pair.punct().map(|punctuation| (*punctuation).clone()))
                        .collect();
                    let items = sequence.into_iter().collect::<Vec<_>>();
                    let base = values.len();
                    tasks.push(HeadExpansionTask::FinishSequence {
                        base,
                        shape: HeadSequenceShape { punctuation },
                    });
                    tasks.extend(items.into_iter().rev().map(HeadExpansionTask::Item));
                },
                HeadExpansionTask::FinishSequence { base, shape } => {
                    let expanded = values.split_off(base);
                    debug_assert_eq!(expanded.len(), shape.punctuation.len());
                    let mut nested = Punctuated::new();
                    for (items, punctuation) in expanded.into_iter().zip(shape.punctuation) {
                        nested.push_value(items);
                        if let Some(punctuation) = punctuation {
                            nested.push_punct(punctuation);
                        }
                    }
                    values.push(flatten_punctuated(nested));
                },
                HeadExpansionTask::FinishMacro { name } => {
                    assert!(
                        active_macros.remove(&name),
                        "head macro-expansion PDA lost its active macro"
                    );
                },
            }
        }

        assert!(active_macros.is_empty(), "head macro-expansion PDA left an active macro");
        assert_eq!(values.len(), 1, "head macro-expansion PDA must produce one root");
        Ok(values
            .pop()
            .expect("head macro-expansion PDA lost its root"))
    }

    let mut gensym = GenSym::new(|s| format!("__{}_", s));

    let new_body_items = rule
        .body_items
        .into_iter()
        .map(|item| expand_body_item(item, macros, &mut gensym))
        .collect::<Result<Vec<_>>>()?
        .into_iter()
        .flatten()
        .collect_vec();

    let new_head_items = expand_head_items(rule.head_clauses, macros)?;

    Ok(RuleNode {
        body_items: new_body_items,
        head_clauses: new_head_items,
    })
}

pub fn desugar_ascent_program(mut prog: AscentProgram) -> Result<AscentProgram> {
    let macros = prog
        .macros
        .iter()
        .map(|m| (m.name.clone(), m))
        .collect::<HashMap<_, _>>();
    let rules_macro_expanded = prog
        .rules
        .into_iter()
        .map(|r| rule_expand_macro_invocations(r, &macros))
        .collect::<Result<Vec<_>>>()?;

    prog.rules = rules_macro_expanded
        .into_iter()
        .flat_map(rule_desugar_disjunction_nodes)
        .map(rule_desugar_pattern_args)
        .map(rule_desugar_wildcards)
        .map(rule_desugar_negation)
        .map(rule_desugar_repeated_vars)
        .collect_vec();

    Ok(prog)
}

lazy_static::lazy_static! {
   static ref IDENT_COUNTERS: Mutex<HashMap<String, u32>> = Mutex::new(HashMap::default());
}

#[cfg(test)]
#[path = "../../tests/support/ascent_recursive_oracle.rs"]
mod recursive_oracle;

fn fresh_ident(prefix: &str, span: Span) -> Ident {
    let mut ident_counters_lock = IDENT_COUNTERS.lock().unwrap();
    let counter = if let Some(entry) = ident_counters_lock.get_mut(prefix) {
        let counter = *entry;
        *entry = counter + 1;
        format!("{}", counter)
    } else {
        ident_counters_lock.insert(prefix.to_string(), 1);
        "".to_string()
    };

    Ident::new(&format!("{}_{}", prefix, counter), span)
}
