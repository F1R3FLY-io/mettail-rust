use crate::grammar::{convert_items_to_term_context, AstTermParamReader, GrammarRule, TermParam};
use crate::language::{
    BehavioralPred, FreshnessTarget, LanguageDef, PredArg, Premise, RewriteRule, RuleContextType,
    TypedParam,
};
use crate::pattern::{Pattern, PatternTerm};
use crate::types::{CollectionType, TypeExpr};
use mettail_grammar_core::rewrite_family::{
    plan_rewrite_families, RewriteFamilyDeclaration, RewriteFamilyError, RewriteFamilyInput,
    RewriteFamilyLocation, RewriteFamilyPlan, RewriteFamilyProblem, RewriteFamilyReader,
    RewritePatternKind, RewriteSide,
};
use mettail_grammar_core::term_param_walk::{TermParamLeaf, TermParamLeafKind, TermParamLeaves};
use proc_macro2::{Ident, Span};
use std::borrow::Cow;

#[derive(Clone, Copy)]
enum Sort<'a> {
    Category(&'a Ident),
    Expression(&'a TypeExpr),
}

struct Reader<'a> {
    language: &'a LanguageDef,
    constructors: &'a [Constructor<'a>],
}

type Parameter<'a> = TermParamLeaf<&'a TermParam, &'a Ident, &'a TypeExpr>;

struct Constructor<'a> {
    rule: &'a GrammarRule,
    parameters: Option<Vec<Parameter<'a>>>,
}

fn constructor_roster<'a>(rules: &'a [Cow<'a, GrammarRule>]) -> syn::Result<Vec<Constructor<'a>>> {
    let mut constructors = Vec::new();
    for rule in rules {
        let parameters = if let Some(parameters) = &rule.term_context {
            let mut leaves = Vec::new();
            for leaf in TermParamLeaves::new(&AstTermParamReader, parameters, false) {
                push(&mut leaves, leaf)?;
            }
            Some(leaves)
        } else {
            None
        };
        push(&mut constructors, Constructor { rule, parameters })?;
    }
    Ok(constructors)
}

fn error(message: impl std::fmt::Display) -> syn::Error {
    syn::Error::new(Span::call_site(), message)
}

fn push<T>(values: &mut Vec<T>, value: T) -> syn::Result<()> {
    values
        .try_reserve(1)
        .map_err(|_| error("rewrite-family allocation failed"))?;
    values.push(value);
    Ok(())
}

impl<'a> Reader<'a> {
    fn constructor(&self, name: &Ident) -> Option<&Constructor<'a>> {
        self.constructors
            .iter()
            .find(|constructor| constructor.rule.label == *name)
    }

    fn collection_element(
        &self,
        sort: Sort<'a>,
        explicit: Option<&CollectionType>,
    ) -> syn::Result<Option<Sort<'a>>> {
        match sort {
            Sort::Expression(TypeExpr::Base(name)) => {
                self.collection_element(Sort::Category(name), explicit)
            },
            Sort::Expression(TypeExpr::Collection { coll_type, element }) => {
                if explicit.is_some_and(|kind| kind != coll_type) {
                    return Err(error("collection pattern kind differs from its declared type"));
                }
                if matches!(coll_type, CollectionType::HashMap | CollectionType::PathMap) {
                    return Ok(None);
                }
                Ok(Some(Sort::Expression(element)))
            },
            Sort::Category(category) => {
                let Some(declaration) = self.language.get_type(category) else {
                    return Err(error(format!("unknown category `{category}`")));
                };
                let Some(collection) = &declaration.collection_kind else {
                    return Ok(None);
                };
                let kind = collection.coll_type();
                if explicit.is_some_and(|explicit| explicit != &kind) {
                    return Err(error(
                        "collection pattern kind differs from its declared category",
                    ));
                }
                if matches!(kind, CollectionType::HashMap | CollectionType::PathMap) {
                    return Ok(None);
                }
                if let Some(native) = &declaration.native_type {
                    let syn::Type::Path(native) = native else {
                        return Ok(None);
                    };
                    let Some(segment) = native.path.segments.last() else {
                        return Ok(None);
                    };
                    let syn::PathArguments::AngleBracketed(arguments) = &segment.arguments else {
                        return Ok(None);
                    };
                    let Some(syn::GenericArgument::Type(syn::Type::Path(element))) =
                        arguments.args.first()
                    else {
                        return Ok(None);
                    };
                    if element.qself.is_some()
                        || element
                            .path
                            .segments
                            .iter()
                            .any(|segment| !matches!(segment.arguments, syn::PathArguments::None))
                    {
                        return Ok(None);
                    }
                }
                let Some(element) = self.language.collection_element_type_for_category(category)
                else {
                    return Ok(None);
                };
                Ok(self
                    .language
                    .get_type(&element)
                    .map(|ty| Sort::Category(&ty.name)))
            },
            _ => Ok(None),
        }
    }
}

impl<'a> RewriteFamilyReader for Reader<'a> {
    type Node = &'a Pattern;
    type Name = &'a Ident;
    type Sort = Sort<'a>;
    type Error = syn::Error;

    fn kind(&self, node: Self::Node) -> syn::Result<RewritePatternKind<Self::Name>> {
        Ok(match node {
            Pattern::Term(PatternTerm::Var(name)) => {
                if self.language.get_constructor(name).is_some() {
                    RewritePatternKind::Application(name)
                } else {
                    RewritePatternKind::Variable(name)
                }
            },
            Pattern::Term(PatternTerm::Apply { constructor, .. }) => {
                RewritePatternKind::Application(constructor)
            },
            Pattern::Term(PatternTerm::Lambda { .. }) => {
                RewritePatternKind::Abstraction { binders: 1 }
            },
            Pattern::Term(PatternTerm::MultiLambda { binders, .. }) => {
                RewritePatternKind::Abstraction { binders: binders.len() }
            },
            Pattern::Collection { .. } => RewritePatternKind::Context,
            Pattern::Term(PatternTerm::Subst { .. } | PatternTerm::MultiSubst { .. })
            | Pattern::Map { .. }
            | Pattern::Zip { .. }
            | Pattern::IndexedVec { .. } => RewritePatternKind::Computation,
        })
    }

    fn child_count(&self, node: Self::Node) -> usize {
        match node {
            Pattern::Term(PatternTerm::Var(_)) => 0,
            Pattern::Term(PatternTerm::Apply { args, .. }) => args.len(),
            Pattern::Term(PatternTerm::Lambda { .. } | PatternTerm::MultiLambda { .. })
            | Pattern::IndexedVec { .. } => 1,
            Pattern::Term(PatternTerm::Subst { .. })
            | Pattern::Map { .. }
            | Pattern::Zip { .. } => 2,
            Pattern::Term(PatternTerm::MultiSubst { replacements, .. }) => replacements.len() + 1,
            Pattern::Collection { elements, .. } => elements.len(),
        }
    }

    fn child_at(&self, node: Self::Node, index: usize) -> Option<Self::Node> {
        match node {
            Pattern::Term(PatternTerm::Var(_)) => None,
            Pattern::Term(PatternTerm::Apply { args, .. }) => args.get(index),
            Pattern::Term(
                PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. },
            ) => (index == 0).then_some(body.as_ref()),
            Pattern::Term(PatternTerm::Subst { term, replacement, .. }) => match index {
                0 => Some(term),
                1 => Some(replacement),
                _ => None,
            },
            Pattern::Term(PatternTerm::MultiSubst { scope, replacements }) => {
                if index == 0 {
                    Some(scope)
                } else {
                    replacements.get(index - 1)
                }
            },
            Pattern::Collection { elements, .. } => elements.get(index),
            Pattern::Map { collection, body, .. } => match index {
                0 => Some(collection),
                1 => Some(body),
                _ => None,
            },
            Pattern::Zip { first, second } => match index {
                0 => Some(first),
                1 => Some(second),
                _ => None,
            },
            Pattern::IndexedVec { element, .. } => (index == 0).then_some(element.as_ref()),
        }
    }

    fn binder_at(&self, node: Self::Node, index: usize) -> Option<Self::Name> {
        match node {
            Pattern::Term(PatternTerm::Lambda { binder, .. }) => (index == 0).then_some(binder),
            Pattern::Term(PatternTerm::MultiLambda { binders, .. }) => binders.get(index),
            _ => None,
        }
    }

    fn variable_count(&self, node: Self::Node) -> usize {
        match node {
            Pattern::Term(PatternTerm::Subst { .. }) => 1,
            Pattern::Collection { rest, .. } => usize::from(rest.is_some()),
            Pattern::Map { params, .. } => params.len(),
            Pattern::IndexedVec { .. } => 2,
            _ => 0,
        }
    }

    fn variable_at(&self, node: Self::Node, index: usize) -> Option<Self::Name> {
        match node {
            Pattern::Term(PatternTerm::Subst { var, .. }) => (index == 0).then_some(var),
            Pattern::Collection { rest, .. } => {
                if index == 0 {
                    rest.as_ref()
                } else {
                    None
                }
            },
            Pattern::Map { params, .. } => params.get(index),
            Pattern::IndexedVec { collection, index: position, .. } => match index {
                0 => Some(collection),
                1 => Some(position),
                _ => None,
            },
            _ => None,
        }
    }

    fn same_header(&self, left: Self::Node, right: Self::Node) -> syn::Result<bool> {
        Ok(match (left, right) {
            (Pattern::Term(PatternTerm::Var(l)), Pattern::Term(PatternTerm::Var(r))) => l == r,
            (
                Pattern::Term(PatternTerm::Apply { constructor: l, .. }),
                Pattern::Term(PatternTerm::Apply { constructor: r, .. }),
            ) => l == r,
            (
                Pattern::Term(PatternTerm::Lambda { binder: l, .. }),
                Pattern::Term(PatternTerm::Lambda { binder: r, .. }),
            ) => l == r,
            (
                Pattern::Term(PatternTerm::MultiLambda { binders: l, .. }),
                Pattern::Term(PatternTerm::MultiLambda { binders: r, .. }),
            ) => l == r,
            (
                Pattern::Term(PatternTerm::Subst { var: l, .. }),
                Pattern::Term(PatternTerm::Subst { var: r, .. }),
            ) => l == r,
            (
                Pattern::Term(PatternTerm::MultiSubst { .. }),
                Pattern::Term(PatternTerm::MultiSubst { .. }),
            ) => true,
            (
                Pattern::Collection { coll_type: lk, rest: lr, .. },
                Pattern::Collection { coll_type: rk, rest: rr, .. },
            ) => lk == rk && lr == rr,
            (Pattern::Map { params: l, .. }, Pattern::Map { params: r, .. }) => l == r,
            (Pattern::Zip { .. }, Pattern::Zip { .. }) => true,
            (
                Pattern::IndexedVec { collection: lc, index: li, .. },
                Pattern::IndexedVec { collection: rc, index: ri, .. },
            ) => lc == rc && li == ri,
            _ => false,
        })
    }

    fn same_name(&self, left: Self::Name, right: Self::Name) -> bool {
        left == right
    }
    fn name_is(&self, name: Self::Name, spelling: &str) -> bool {
        name.to_string() == spelling
    }

    fn same_sort(&self, left: Self::Sort, right: Self::Sort) -> bool {
        match (left, right) {
            (Sort::Category(l), Sort::Category(r)) => l == r,
            (Sort::Expression(l), Sort::Expression(r)) => l == r,
            (Sort::Category(l), Sort::Expression(TypeExpr::Base(r)))
            | (Sort::Expression(TypeExpr::Base(l)), Sort::Category(r)) => l == r,
            _ => false,
        }
    }

    fn valid_sort(&self, sort: Self::Sort) -> syn::Result<bool> {
        let mut work = Vec::new();
        push(&mut work, sort)?;
        while let Some(sort) = work.pop() {
            match sort {
                Sort::Category(name) | Sort::Expression(TypeExpr::Base(name)) => {
                    if self.language.get_type(name).is_none() {
                        return Ok(false);
                    }
                },
                Sort::Expression(TypeExpr::Arrow { domain, codomain }) => {
                    push(&mut work, Sort::Expression(domain))?;
                    push(&mut work, Sort::Expression(codomain))?;
                },
                Sort::Expression(TypeExpr::MultiBinder(inner))
                | Sort::Expression(TypeExpr::Collection { element: inner, .. })
                | Sort::Expression(TypeExpr::Refined { base: inner, .. }) => {
                    push(&mut work, Sort::Expression(inner))?
                },
                Sort::Expression(TypeExpr::Map { key, value }) => {
                    push(&mut work, Sort::Expression(key))?;
                    push(&mut work, Sort::Expression(value))?;
                },
            }
        }
        Ok(true)
    }

    fn node_sort(
        &self,
        node: Self::Node,
        expected: Option<Self::Sort>,
    ) -> syn::Result<Option<Self::Sort>> {
        match node {
            Pattern::Term(PatternTerm::Apply { constructor, args }) => {
                let rule = self
                    .constructor(constructor)
                    .ok_or_else(|| error(format!("unknown constructor `{constructor}`")))?;
                if let Some(parameters) = &rule.parameters {
                    let count = parameters.len();
                    if count != args.len() {
                        return Err(error(format!("constructor `{constructor}` expects {count} semantic arguments, received {}", args.len())));
                    }
                }
                Ok(Some(Sort::Category(&rule.rule.category)))
            },
            Pattern::Term(PatternTerm::Var(name)) => Ok(self
                .constructor(name)
                .map(|rule| Sort::Category(&rule.rule.category))
                .or(expected)),
            Pattern::Term(PatternTerm::Lambda { .. }) => {
                if let Some(Sort::Expression(TypeExpr::Arrow { domain, .. })) = expected {
                    if matches!(domain.as_ref(), TypeExpr::MultiBinder(_)) {
                        return Err(error("single abstraction requires a single binder domain"));
                    }
                }
                Ok(expected)
            },
            Pattern::Term(PatternTerm::MultiLambda { .. }) => {
                if let Some(Sort::Expression(TypeExpr::Arrow { domain, .. })) = expected {
                    if !matches!(domain.as_ref(), TypeExpr::MultiBinder(_)) {
                        return Err(error(
                            "multiple abstraction requires a multiple binder domain",
                        ));
                    }
                }
                Ok(expected)
            },
            _ => Ok(expected),
        }
    }

    fn child_sort(
        &self,
        node: Self::Node,
        expected: Option<Self::Sort>,
        index: usize,
    ) -> syn::Result<Option<Self::Sort>> {
        match node {
            Pattern::Term(PatternTerm::Apply { constructor, .. }) => {
                let rule = self
                    .constructor(constructor)
                    .ok_or_else(|| error(format!("unknown constructor `{constructor}`")))?;
                let Some(parameters) = &rule.parameters else {
                    return Ok(None);
                };
                let Some(leaf) = parameters.get(index) else {
                    return Err(error("constructor parameter index is out of range"));
                };
                if leaf.is_optional {
                    return Ok(None);
                }
                Ok(match leaf.kind {
                    TermParamLeafKind::Simple { ty, .. }
                    | TermParamLeafKind::Abstraction { ty, .. }
                    | TermParamLeafKind::MultiAbstraction { ty, .. } => Some(Sort::Expression(ty)),
                    TermParamLeafKind::GuardBody { .. } => None,
                })
            },
            Pattern::Collection { coll_type, .. } => expected
                .map(|sort| self.collection_element(sort, coll_type.as_ref()))
                .transpose()
                .map(Option::flatten),
            _ => Ok(None),
        }
    }

    fn abstraction_sorts(
        &self,
        expected: Self::Sort,
        binder_count: usize,
    ) -> syn::Result<(Self::Sort, Self::Sort)> {
        let Sort::Expression(TypeExpr::Arrow { domain, codomain }) = expected else {
            return Err(error("abstraction requires a declared function type"));
        };
        let domain = match domain.as_ref() {
            TypeExpr::MultiBinder(inner) => inner.as_ref(),
            domain if binder_count == 1 => domain,
            _ => return Err(error("single abstraction requires exactly one binder")),
        };
        Ok((Sort::Expression(domain), Sort::Expression(codomain)))
    }
}

fn premise_names(premises: &[Premise]) -> syn::Result<Vec<&Ident>> {
    enum Item<'a> {
        Premise(&'a Premise),
        Predicate(&'a BehavioralPred),
    }
    let mut work = Vec::new();
    let mut names = Vec::new();
    for premise in premises.iter().rev() {
        push(&mut work, Item::Premise(premise))?;
    }
    while let Some(item) = work.pop() {
        match item {
            Item::Premise(Premise::Freshness(condition)) => {
                push(&mut names, &condition.var)?;
                let (FreshnessTarget::Var(name) | FreshnessTarget::CollectionRest(name)) =
                    &condition.term;
                push(&mut names, name)?;
            },
            Item::Premise(
                Premise::Congruence { source, target }
                | Premise::CongruenceWithheld { source, target },
            ) => {
                push(&mut names, source)?;
                push(&mut names, target)?;
            },
            Item::Premise(Premise::RelationQuery { args, .. }) => {
                for arg in args {
                    push(&mut names, arg)?;
                }
            },
            Item::Premise(Premise::ForAll { collection, param, body }) => {
                push(&mut names, collection)?;
                push(&mut names, param)?;
                push(&mut work, Item::Premise(body))?;
            },
            Item::Premise(Premise::BehavioralGuard(predicate)) => {
                push(&mut work, Item::Predicate(predicate))?
            },
            Item::Premise(Premise::SyntheticInjGuard { inner_var, .. }) => {
                push(&mut names, inner_var)?
            },
            Item::Predicate(BehavioralPred::RelationQuery { args, .. }) => {
                for arg in args {
                    if let PredArg::Var(name) = arg {
                        push(&mut names, name)?;
                    }
                }
            },
            Item::Predicate(BehavioralPred::Quantified { var, body, .. }) => {
                push(&mut names, var)?;
                push(&mut work, Item::Predicate(body))?;
            },
            Item::Predicate(
                BehavioralPred::And(left, right)
                | BehavioralPred::Or(left, right)
                | BehavioralPred::Implies(left, right),
            ) => {
                push(&mut work, Item::Predicate(right))?;
                push(&mut work, Item::Predicate(left))?;
            },
            Item::Predicate(BehavioralPred::Not(body)) => push(&mut work, Item::Predicate(body))?,
            Item::Predicate(BehavioralPred::AcMatch { bag, elements, rest }) => {
                push(&mut names, bag)?;
                for element in elements {
                    push(&mut names, element)?;
                }
                if let Some(rest) = rest {
                    push(&mut names, rest)?;
                }
            },
            Item::Predicate(BehavioralPred::Top) => {},
        }
    }
    Ok(names)
}

fn apply_pattern_plan(
    pattern: &mut Pattern,
    side: RewriteSide,
    plan: &RewriteFamilyPlan,
) -> syn::Result<()> {
    let mut replacements = plan
        .replacements
        .iter()
        .filter(|edit| edit.side == side)
        .peekable();
    let mut renames = plan.binder_renames.iter().peekable();
    let mut work = Vec::new();
    push(&mut work, pattern)?;
    let mut next = 0usize;
    while let Some(pattern) = work.pop() {
        let occurrence = next;
        next = next
            .checked_add(1)
            .ok_or_else(|| error("rewrite-family occurrence counter overflow"))?;
        if replacements
            .peek()
            .is_some_and(|edit| edit.occurrence == occurrence)
        {
            let edit = replacements
                .next()
                .ok_or_else(|| error("missing projection edit"))?;
            let family = &plan.families[edit.family];
            let name = match side {
                RewriteSide::Left => &family.source,
                RewriteSide::Right => &family.target,
            };
            let span = match pattern {
                Pattern::Term(PatternTerm::Apply { constructor, .. }) => constructor.span(),
                _ => Span::call_site(),
            };
            *pattern = Pattern::Term(PatternTerm::Var(Ident::new(name, span)));
            next = edit.subtree_end;
            continue;
        }
        while renames.peek().is_some_and(|edit| match side { RewriteSide::Left => edit.left_occurrence, RewriteSide::Right => edit.right_occurrence } == occurrence) {
            let edit = renames.next().ok_or_else(|| error("missing binder edit"))?;
            let binder = match pattern {
                Pattern::Term(PatternTerm::Lambda { binder, .. }) if edit.binder_index == 0 => binder,
                Pattern::Term(PatternTerm::MultiLambda { binders, .. }) => binders.get_mut(edit.binder_index).ok_or_else(|| error("binder edit index is out of range"))?,
                _ => return Err(error("binder edit does not identify an abstraction")),
            };
            *binder = Ident::new(&edit.name, binder.span());
        }
        match pattern {
            Pattern::Term(PatternTerm::Var(_)) => {},
            Pattern::Term(PatternTerm::Apply { args, .. }) => {
                for child in args.iter_mut().rev() {
                    push(&mut work, child)?;
                }
            },
            Pattern::Term(
                PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. },
            ) => push(&mut work, body)?,
            Pattern::Term(PatternTerm::Subst { term, replacement, .. }) => {
                push(&mut work, replacement)?;
                push(&mut work, term)?;
            },
            Pattern::Term(PatternTerm::MultiSubst { scope, replacements }) => {
                for child in replacements.iter_mut().rev() {
                    push(&mut work, child)?;
                }
                push(&mut work, scope)?;
            },
            Pattern::Collection { elements, .. } => {
                for child in elements.iter_mut().rev() {
                    push(&mut work, child)?;
                }
            },
            Pattern::Map { collection, body, .. } => {
                push(&mut work, body)?;
                push(&mut work, collection)?;
            },
            Pattern::Zip { first, second } => {
                push(&mut work, second)?;
                push(&mut work, first)?;
            },
            Pattern::IndexedVec { element, .. } => push(&mut work, element)?,
        }
    }
    if replacements.next().is_some() || renames.next().is_some() {
        return Err(error("rewrite-family edits do not match the original pattern"));
    }
    Ok(())
}

fn normalize_rule(reader: &Reader<'_>, rule: &RewriteRule) -> syn::Result<Option<RewriteRule>> {
    if !rule
        .type_context
        .iter()
        .any(|parameter| matches!(parameter.ty, RuleContextType::RewriteFamily { .. }))
    {
        return Ok(None);
    }
    let mut declarations = Vec::new();
    let mut ambient = Vec::new();
    for (context_index, parameter) in rule.type_context.iter().enumerate() {
        match &parameter.ty {
            RuleContextType::Ordinary(ty) => push(
                &mut ambient,
                RewriteFamilyInput {
                    context_index,
                    name: &parameter.name,
                    sort: Sort::Expression(ty),
                },
            )?,
            RuleContextType::RewriteFamily { domains, result } => {
                let mut types = Vec::new();
                for domain in domains {
                    push(&mut types, Sort::Expression(domain))?;
                }
                push(
                    &mut declarations,
                    RewriteFamilyDeclaration {
                        context_index,
                        name: &parameter.name,
                        domains: types,
                        result: Sort::Expression(result),
                    },
                )?;
            },
        }
    }
    let external = premise_names(&rule.premises)?;
    let mut reserved = Vec::new();
    for constructor in &reader.language.terms {
        push(&mut reserved, &constructor.label)?;
    }
    let plan = plan_rewrite_families(reader, &rule.left, &rule.right, &declarations, &ambient, &external, &reserved).map_err(|failure| {
        match failure {
            RewriteFamilyError::Reader(error) => error,
            RewriteFamilyError::Invalid {
                problem: RewriteFamilyProblem::AmbiguousBinderReference { binder_index },
                location: RewriteFamilyLocation::Pattern { side, occurrence, path },
                related,
                ..
            } => {
                let mut node = match side { RewriteSide::Left => &rule.left, RewriteSide::Right => &rule.right };
                for &child in &path {
                    let Some(next) = reader.child_at(node, child) else { return error("invalid diagnostic pattern path"); };
                    node = next;
                }
                let Some(binder) = reader.binder_at(node, binder_index) else { return error("invalid diagnostic binder index"); };
                syn::Error::new(binder.span(), format!("AmbiguousBinderReference: binder `{binder}` at {side:?} occurrence {occurrence}, path {path:?}, index {binder_index}. Conflicting reference at {related:?}"))
            },
            failure => syn::Error::new(rule.name.span(), format!("rewrite family in `{}`: {failure:?}", rule.name)),
        }
    })?;
    let mut normalized = rule.clone();
    apply_pattern_plan(&mut normalized.left, RewriteSide::Left, &plan)?;
    apply_pattern_plan(&mut normalized.right, RewriteSide::Right, &plan)?;
    normalized
        .type_context
        .retain(|parameter| matches!(parameter.ty, RuleContextType::Ordinary(_)));
    normalized
        .type_context
        .try_reserve(plan.families.len())
        .map_err(|_| error("rewrite-family context allocation failed"))?;
    normalized
        .premises
        .try_reserve(plan.families.len())
        .map_err(|_| error("rewrite-family premise allocation failed"))?;
    for family in plan.families {
        let parameter = &rule.type_context[family.context_index];
        let RuleContextType::RewriteFamily { result, .. } = &parameter.ty else {
            return Err(error("family edit does not identify a family declaration"));
        };
        let source = Ident::new(&family.source, parameter.name.span());
        let target = Ident::new(&family.target, parameter.name.span());
        normalized.type_context.push(TypedParam {
            name: source.clone(),
            ty: RuleContextType::Ordinary(result.clone()),
        });
        normalized
            .premises
            .push(Premise::Congruence { source, target });
    }
    Ok(Some(normalized))
}

pub fn normalize_rewrite_families(language: &mut LanguageDef) -> syn::Result<()> {
    for equation in &language.equations {
        if let Some(parameter) = equation
            .type_context
            .iter()
            .find(|parameter| matches!(parameter.ty, RuleContextType::RewriteFamily { .. }))
        {
            return Err(syn::Error::new(
                parameter.name.span(),
                "rewrite families require a rewrite rule, not an equation",
            ));
        }
    }
    if !language.rewrites.iter().any(|rule| {
        rule.type_context
            .iter()
            .any(|parameter| matches!(parameter.ty, RuleContextType::RewriteFamily { .. }))
    }) {
        return Ok(());
    }
    let mut constructors = Vec::new();
    for rule in &language.terms {
        let rule = if rule.term_context.is_none() && rule.syntax_pattern.is_none() {
            let mut normalized = rule.clone();
            convert_items_to_term_context(&mut normalized);
            Cow::Owned(normalized)
        } else {
            Cow::Borrowed(rule)
        };
        push(&mut constructors, rule)?;
    }
    let roster = constructor_roster(&constructors)?;
    let reader = Reader { language, constructors: &roster };
    let mut changes = Vec::new();
    for (index, rule) in language.rewrites.iter().enumerate() {
        if let Some(normalized) = normalize_rule(&reader, rule)? {
            push(&mut changes, (index, normalized))?;
        }
    }
    drop(constructors);
    for (index, normalized) in changes {
        language.rewrites[index] = normalized;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn cached_parameters_equal_original_iterator_payloads_and_optional_flags(
            shapes in prop::collection::vec((0u8..4, 0usize..8), 0..32),
        ) {
            let mut language: LanguageDef = syn::parse_str("name: Parameters, types {Name; Proc}, terms { C . n:Name, ^x.p:[Name -> Proc], ^[ys].q:[Name* -> Proc], ?guard:Guard |- \"c\" : Proc; }").unwrap();
            let originals = language.terms[0].term_context.clone().unwrap();
            let parameters = shapes.into_iter().map(|(kind, depth)| {
                let mut param = originals[usize::from(kind)].clone();
                for _ in 0..depth {
                    param = TermParam::Optional { params:vec![param] };
                }
                param
            }).collect::<Vec<_>>();
            language.terms[0].term_context = Some(parameters);
            let rules = vec![Cow::Borrowed(&language.terms[0])];
            let roster = constructor_roster(&rules).unwrap();
            let cached = roster[0].parameters.as_ref().unwrap();
            let parameters = language.terms[0].term_context.as_ref().unwrap();
            for index in 0..=cached.len() {
                let original = TermParamLeaves::new(&AstTermParamReader, parameters, false).nth(index);
                match (cached.get(index), original) {
                    (Some(cached), Some(original)) => {
                        prop_assert!(std::ptr::eq(cached.kind.param(), original.kind.param()));
                        prop_assert_eq!(std::mem::discriminant(&cached.kind), std::mem::discriminant(&original.kind));
                        prop_assert_eq!(cached.is_optional, original.is_optional);
                    },
                    (None, None) => {},
                    _ => return Err(TestCaseError::fail("cached parameter index differs from the original iterator")),
                }
            }
        }
    }

    #[test]
    fn absent_and_empty_constructor_signatures_remain_distinct() {
        let mut language: LanguageDef = syn::parse_str(
            "name: Parameters, types {Proc}, terms { C . |- \"c\" : Proc; D . |- \"d\" : Proc; }",
        )
        .unwrap();
        language.terms[0].term_context = None;
        let rules = language.terms.iter().map(Cow::Borrowed).collect::<Vec<_>>();
        let roster = constructor_roster(&rules).unwrap();
        assert!(roster[0].parameters.is_none());
        assert!(roster[1].parameters.as_ref().unwrap().is_empty());
    }
}
