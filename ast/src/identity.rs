//! Stable compiler-facing identity for parsed `language!` definitions.
//!
//! This is ordinary implementation identity data. The fingerprint prevents
//! installing a backend plan derived from one `LanguageDef` onto a generated
//! language value produced from another `LanguageDef`.

use quote::ToTokens;
use syn::Ident;

use crate::grammar::{GrammarItem, GrammarRule, PatternOp, SyntaxExpr, TermParam};
use crate::language::{
    AttributeValue, BehavioralPred, BuiltinPredicate, ChannelConfig, CollectionCategory,
    ConnectiveDecl, Equation, FreshnessTarget, GuardConfig, LanguageDef, ParamQuantifier,
    ParamType, PredArg, PredicateParam, Premise, Quantifier, RefinementPredicate, RewriteRule,
    SyncConstraint, TheoryRegistration, TokenDef, TreeConstraintExpr, TypedParam,
};
use crate::pattern::{Pattern, PatternTerm};
use crate::types::{CollectionType, EvalMode, TypeExpr};

/// Versioned stable fingerprint for a macro-expanded [`LanguageDef`].
pub fn language_definition_fingerprint(language: &LanguageDef) -> String {
    let mut out = String::new();
    write_language(language, &mut out);
    format!("mettail-langdef-v1:{:016x}", fnv1a64(out.as_bytes()))
}

/// Canonical, span-independent identity text for one rule-spec pattern.
pub fn pattern_identity(pattern: &Pattern) -> String {
    let mut out = String::new();
    write_pattern(pattern, &mut out);
    out
}

/// Canonical, span-independent identity text for a premise list.
pub fn premises_identity(premises: &[Premise]) -> String {
    let mut out = String::new();
    write_premises(premises, &mut out);
    out
}

/// Canonical, span-independent identity text for a behavioral predicate.
pub fn behavioral_predicate_identity(pred: &BehavioralPred) -> String {
    let mut out = String::new();
    write_behavioral_pred(pred, &mut out);
    out
}

/// Canonical, span-independent identity text for one grammar constructor rule.
pub fn grammar_rule_identity(rule: &GrammarRule) -> String {
    let mut out = String::new();
    write_grammar_rule(rule, &mut out);
    out
}

/// Canonical, span-independent identity text for one equation.
pub fn equation_identity(equation: &Equation) -> String {
    let mut out = String::new();
    write_equation(equation, &mut out);
    out
}

/// Canonical, span-independent identity text for one rewrite rule.
pub fn rewrite_identity(rewrite: &RewriteRule) -> String {
    let mut out = String::new();
    write_rewrite(rewrite, &mut out);
    out
}

fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in bytes {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

fn push_ident(out: &mut String, ident: &Ident) {
    out.push_str(&ident.to_string());
}

/// Append a token stream's **spacing- and span-independent** canonical text to
/// the fingerprint buffer.
///
/// This matters because the macro fingerprints `LanguageDef` values whose
/// embedded Rust token streams (native types, literal `eval: ![{ … }]` bodies,
/// theory types, logic content) are **`Span`-backed real-compiler tokens**,
/// whereas the same definition reconstructed at runtime from
/// `LanguageMetadata::definition_source()` re-parses those tokens with
/// `syn`/`proc_macro2`, producing **synthetic tokens**. The two render with
/// different inter-token spacing (`a::b(x, y)` vs `a :: b (x , y)`), and — worse
/// — re-tokenizing inside a proc-macro yields real tokens again (tight), so a
/// `from_str` round-trip is *not* a context-independent fixed point.
///
/// Whitespace between Rust tokens is not a meaningful language-identity
/// distinction, so the fingerprint must be insensitive to it. This walks the
/// token tree and emits each leaf token's own text (with explicit group
/// delimiters), joined by a single space, ignoring `Spacing` and `Span`
/// entirely. The result is identical whether the tokens are real (macro
/// expansion) or synthetic (runtime reconstruction), while leaf tokens —
/// including string/char literals whose text may contain spaces — are emitted
/// verbatim and so are never merged or split. This is what makes
/// `language_definition_fingerprint(reconstruct_language_def(definition_source()))`
/// equal the generated `definition_fingerprint()` for standalone languages.
fn push_tokens<T: ToTokens>(out: &mut String, value: &T) {
    push_token_stream_canonical(out, &value.to_token_stream());
}

/// Recursively emit a token stream in span/spacing-independent canonical form.
/// See [`push_tokens`] for why this is necessary.
fn push_token_stream_canonical(out: &mut String, stream: &proc_macro2::TokenStream) {
    let mut first = true;
    for tree in stream.clone() {
        if !first {
            out.push(' ');
        }
        first = false;
        match tree {
            proc_macro2::TokenTree::Group(group) => {
                let (open, close) = match group.delimiter() {
                    proc_macro2::Delimiter::Parenthesis => ("(", ")"),
                    proc_macro2::Delimiter::Brace => ("{", "}"),
                    proc_macro2::Delimiter::Bracket => ("[", "]"),
                    proc_macro2::Delimiter::None => ("", ""),
                };
                out.push_str(open);
                push_token_stream_canonical(out, &group.stream());
                out.push_str(close);
            },
            proc_macro2::TokenTree::Ident(ident) => out.push_str(&ident.to_string()),
            proc_macro2::TokenTree::Punct(punct) => out.push(punct.as_char()),
            proc_macro2::TokenTree::Literal(literal) => out.push_str(&literal.to_string()),
        }
    }
}

fn push_ids(out: &mut String, ids: &[Ident]) {
    out.push('[');
    for id in ids {
        push_ident(out, id);
        out.push(';');
    }
    out.push(']');
}

fn write_language(language: &LanguageDef, out: &mut String) {
    out.push_str("language(");
    push_ident(out, &language.name);
    out.push_str(");options[");
    let mut options = language.options.iter().collect::<Vec<_>>();
    options.sort_by_key(|(left, _)| *left);
    for (key, value) in options {
        out.push_str(key);
        out.push('=');
        write_attribute_value(value, out);
        out.push(';');
    }
    out.push_str("];extends");
    push_ids(out, &language.extends_names);
    out.push_str(";includes");
    push_ids(out, &language.include_names);
    out.push_str(";mixins");
    push_ids(out, &language.mixin_names);

    out.push_str(";types[");
    for ty in &language.types {
        push_ident(out, &ty.name);
        out.push(':');
        if let Some(native) = &ty.native_type {
            push_tokens(out, native);
        }
        out.push(':');
        write_collection_category_opt(&ty.collection_kind, out);
        out.push(';');
    }
    out.push_str("];refinements[");
    for refinement in &language.refinement_types {
        push_ident(out, &refinement.name);
        out.push(':');
        push_ident(out, &refinement.var);
        out.push(':');
        write_type_expr(&refinement.base_type, out);
        out.push(':');
        write_refinement_predicate(&refinement.predicate, out);
        out.push(';');
    }
    out.push_str("];tokens[");
    for token in &language.token_defs {
        write_token_def(token, out);
        out.push(';');
    }
    out.push_str("];modes[");
    for mode in &language.mode_defs {
        push_ident(out, &mode.name);
        out.push_str(":[");
        for token in &mode.token_defs {
            write_token_def(token, out);
            out.push(';');
        }
        out.push(']');
        out.push(';');
    }
    out.push_str("];sync[");
    for constraint in &language.sync_constraints {
        write_sync_constraint(constraint, out);
        out.push(';');
    }
    out.push_str("];tree-invariants[");
    for invariant in &language.tree_invariants {
        push_ident(out, &invariant.name);
        out.push(':');
        write_tree_constraint_expr(&invariant.constraint, out);
        out.push(';');
    }
    out.push_str("];terms[");
    for rule in &language.terms {
        write_grammar_rule(rule, out);
        out.push(';');
    }
    out.push_str("];equations[");
    for equation in &language.equations {
        write_equation(equation, out);
        out.push(';');
    }
    out.push_str("];rewrites[");
    for rewrite in &language.rewrites {
        write_rewrite(rewrite, out);
        out.push(';');
    }
    out.push_str("];logic[");
    if let Some(logic) = &language.logic {
        for relation in &logic.relations {
            push_ident(out, &relation.name);
            out.push('(');
            for param in &relation.param_types {
                out.push_str(param);
                out.push(',');
            }
            out.push(')');
            out.push(';');
        }
        push_tokens(out, &logic.content);
    }
    out.push_str("];guards[");
    if let Some(guards) = &language.guard_config {
        write_guard_config(guards, out);
    }
    out.push(']');
}

fn write_attribute_value(value: &AttributeValue, out: &mut String) {
    match value {
        AttributeValue::Float(value) => out.push_str(&value.to_bits().to_string()),
        AttributeValue::Int(value) => out.push_str(&value.to_string()),
        AttributeValue::Bool(value) => out.push_str(if *value { "true" } else { "false" }),
        AttributeValue::Str(value) | AttributeValue::Keyword(value) => out.push_str(value),
    }
}

fn write_token_def(token: &TokenDef, out: &mut String) {
    push_ident(out, &token.name);
    out.push(':');
    out.push_str(&token.pattern);
    out.push(':');
    if let Some(category) = &token.category {
        push_ident(out, category);
    }
    out.push(':');
    if let Some(code) = &token.rust_code {
        push_tokens(out, code);
    }
    out.push(':');
    if let Some(priority) = token.priority {
        out.push_str(&priority.to_string());
    }
    out.push(':');
    if let Some(mode) = &token.push_mode {
        push_ident(out, mode);
    }
    out.push(':');
    out.push_str(if token.is_pop { "pop" } else { "keep" });
    out.push(':');
    if let Some(stream) = &token.stream {
        push_ident(out, stream);
    }
    out.push(':');
    out.push_str(if token.from_literals {
        "literal"
    } else {
        "token"
    });
}

fn write_sync_constraint(constraint: &SyncConstraint, out: &mut String) {
    match constraint {
        SyncConstraint::Align { stream_a, stream_b, boundary_pattern } => {
            out.push_str("align(");
            push_ident(out, stream_a);
            out.push(',');
            push_ident(out, stream_b);
            out.push(',');
            out.push_str(boundary_pattern);
            out.push(')');
        },
        SyncConstraint::Track { auxiliary, primary } => {
            out.push_str("track(");
            push_ident(out, auxiliary);
            out.push(',');
            push_ident(out, primary);
            out.push(')');
        },
    }
}

fn write_tree_constraint_expr(expr: &TreeConstraintExpr, out: &mut String) {
    match expr {
        TreeConstraintExpr::ForallChildren { symbol, body } => {
            out.push_str("forall-children(");
            out.push_str(symbol);
            out.push(',');
            write_tree_constraint_expr(body, out);
            out.push(')');
        },
        TreeConstraintExpr::ExistsChild => out.push_str("exists-child"),
        TreeConstraintExpr::Not(inner) => {
            out.push_str("not(");
            write_tree_constraint_expr(inner, out);
            out.push(')');
        },
        TreeConstraintExpr::Match(symbols) => {
            out.push_str("match(");
            for symbol in symbols {
                out.push_str(symbol);
                out.push('|');
            }
            out.push(')');
        },
        TreeConstraintExpr::Atom(symbol) => {
            out.push_str("atom(");
            out.push_str(symbol);
            out.push(')');
        },
        TreeConstraintExpr::And(left, right) => {
            out.push_str("and(");
            write_tree_constraint_expr(left, out);
            out.push(',');
            write_tree_constraint_expr(right, out);
            out.push(')');
        },
        TreeConstraintExpr::Or(left, right) => {
            out.push_str("or(");
            write_tree_constraint_expr(left, out);
            out.push(',');
            write_tree_constraint_expr(right, out);
            out.push(')');
        },
    }
}

fn write_collection_type(coll_type: &CollectionType, out: &mut String) {
    out.push_str(match coll_type {
        CollectionType::HashBag => "HashBag",
        CollectionType::HashSet => "HashSet",
        CollectionType::Vec => "Vec",
        CollectionType::HashMap => "HashMap",
        CollectionType::PathMap => "PathMap",
    });
}

fn write_collection_category_opt(value: &Option<CollectionCategory>, out: &mut String) {
    match value {
        None => out.push_str("none"),
        Some(CollectionCategory::List(delims)) => {
            out.push_str("list(");
            write_delimiters(delims, out);
            out.push(')');
        },
        Some(CollectionCategory::Bag(delims)) => {
            out.push_str("bag(");
            write_delimiters(delims, out);
            out.push(')');
        },
        Some(CollectionCategory::Map(delims)) => {
            out.push_str("map(");
            write_delimiters(delims, out);
            out.push(')');
        },
        Some(CollectionCategory::Set(delims)) => {
            out.push_str("set(");
            write_delimiters(delims, out);
            out.push(')');
        },
        Some(CollectionCategory::Pathmap(delims)) => {
            out.push_str("pathmap(");
            write_delimiters(delims, out);
            out.push(')');
        },
    }
}

fn write_delimiters(delims: &crate::language::CollectionDelimiters, out: &mut String) {
    out.push_str(&delims.open);
    out.push('|');
    out.push_str(&delims.close);
    out.push('|');
    out.push_str(&delims.sep);
    out.push('|');
    if let Some(sep) = &delims.key_val_sep {
        out.push_str(sep);
    }
}

fn write_type_expr(ty: &TypeExpr, out: &mut String) {
    match ty {
        TypeExpr::Base(id) => {
            out.push_str("base(");
            push_ident(out, id);
            out.push(')');
        },
        TypeExpr::Arrow { domain, codomain } => {
            out.push_str("arrow(");
            write_type_expr(domain, out);
            out.push(',');
            write_type_expr(codomain, out);
            out.push(')');
        },
        TypeExpr::MultiBinder(inner) => {
            out.push_str("multi(");
            write_type_expr(inner, out);
            out.push(')');
        },
        TypeExpr::Collection { coll_type, element } => {
            out.push_str("collection(");
            write_collection_type(coll_type, out);
            out.push(',');
            write_type_expr(element, out);
            out.push(')');
        },
        TypeExpr::Refined { var, base, predicate_repr } => {
            out.push_str("refined(");
            push_ident(out, var);
            out.push(',');
            write_type_expr(base, out);
            out.push(',');
            out.push_str(predicate_repr);
            out.push(')');
        },
        TypeExpr::Map { key, value } => {
            out.push_str("maptype(");
            write_type_expr(key, out);
            out.push(',');
            write_type_expr(value, out);
            out.push(')');
        },
    }
}

fn write_grammar_rule(rule: &GrammarRule, out: &mut String) {
    push_ident(out, &rule.label);
    out.push(':');
    push_ident(out, &rule.category);
    out.push(':');
    for item in &rule.items {
        write_grammar_item(item, out);
        out.push(',');
    }
    out.push(':');
    for (binder, bodies) in &rule.bindings {
        out.push_str(&binder.to_string());
        out.push('>');
        for body in bodies {
            out.push_str(&body.to_string());
            out.push(',');
        }
        out.push(';');
    }
    out.push(':');
    if let Some(params) = &rule.term_context {
        write_term_params(params, out);
    }
    out.push(':');
    if let Some(pattern) = &rule.syntax_pattern {
        write_syntax_exprs(pattern, out);
    }
    out.push(':');
    if let Some(code) = &rule.rust_code {
        push_tokens(out, &code.code);
    }
    out.push(':');
    if let Some(mode) = rule.eval_mode {
        write_eval_mode(mode, out);
    }
    out.push(':');
    out.push_str(if rule.is_right_assoc { "right" } else { "left" });
    out.push(':');
    if let Some(bp) = rule.prefix_bp {
        out.push_str(&bp.to_string());
    }
    out.push(':');
    if let Some(tier) = &rule.tier_directive {
        out.push_str(&format!("tier={:?},bound={:?},force={}", tier.tier, tier.bound, tier.force));
    }
    out.push(':');
    out.push_str(if rule.is_auto_injected {
        "auto"
    } else {
        "user"
    });
}

fn write_grammar_item(item: &GrammarItem, out: &mut String) {
    match item {
        GrammarItem::Terminal(value) => {
            out.push_str("terminal(");
            out.push_str(value);
            out.push(')');
        },
        GrammarItem::NonTerminal { ident, kind } => {
            out.push_str("nonterminal(");
            push_ident(out, ident);
            out.push(',');
            out.push_str(&format!("{kind:?}"));
            out.push(')');
        },
        GrammarItem::Binder { category } => {
            out.push_str("binder(");
            push_ident(out, category);
            out.push(')');
        },
        GrammarItem::Collection {
            coll_type,
            element_type,
            separator,
            delimiters,
        } => {
            out.push_str("collection-item(");
            write_collection_type(coll_type, out);
            out.push(',');
            push_ident(out, element_type);
            out.push(',');
            out.push_str(separator);
            out.push(',');
            if let Some((open, close)) = delimiters {
                out.push_str(open);
                out.push('|');
                out.push_str(close);
            }
            out.push(')');
        },
    }
}

fn write_term_params(params: &[TermParam], out: &mut String) {
    out.push('[');
    for param in params {
        match param {
            TermParam::Simple { name, ty } => {
                out.push_str("simple(");
                push_ident(out, name);
                out.push(',');
                write_type_expr(ty, out);
                out.push(')');
            },
            TermParam::Abstraction { binder, body, ty } => {
                out.push_str("abs(");
                push_ident(out, binder);
                out.push(',');
                push_ident(out, body);
                out.push(',');
                write_type_expr(ty, out);
                out.push(')');
            },
            TermParam::MultiAbstraction { binder, body, ty } => {
                out.push_str("multiabs(");
                push_ident(out, binder);
                out.push(',');
                push_ident(out, body);
                out.push(',');
                write_type_expr(ty, out);
                out.push(')');
            },
            TermParam::GuardBody { name } => {
                out.push_str("guard(");
                push_ident(out, name);
                out.push(')');
            },
            TermParam::Optional { params } => {
                out.push_str("optional(");
                write_term_params(params, out);
                out.push(')');
            },
        }
        out.push(';');
    }
    out.push(']');
}

fn write_syntax_exprs(exprs: &[SyntaxExpr], out: &mut String) {
    out.push('[');
    for expr in exprs {
        write_syntax_expr(expr, out);
        out.push(';');
    }
    out.push(']');
}

fn write_syntax_expr(expr: &SyntaxExpr, out: &mut String) {
    match expr {
        SyntaxExpr::Literal(value) => {
            out.push_str("lit(");
            out.push_str(value);
            out.push(')');
        },
        SyntaxExpr::Param(id) => {
            out.push_str("param(");
            push_ident(out, id);
            out.push(')');
        },
        SyntaxExpr::Op(op) => write_pattern_op(op, out),
        SyntaxExpr::TokenKind { name, bind } => {
            // L9-3: fold the kind name + optional @-bind into the langdef
            // fingerprint so a rule that consumes a token KIND is distinct from
            // one that references a like-named nonterminal/param.
            out.push_str("tokenkind(");
            push_ident(out, name);
            if let Some(b) = bind {
                out.push('@');
                push_ident(out, b);
            }
            out.push(')');
        },
        SyntaxExpr::GuestBody { open, close, bind } => {
            // L9-4: fold the guest-body capture (opener/closer kinds + bind) into
            // the langdef fingerprint.
            out.push_str("guestbody(");
            push_ident(out, bind);
            out.push(',');
            push_ident(out, open);
            out.push(',');
            push_ident(out, close);
            out.push(')');
        },
    }
}

fn write_pattern_op(op: &PatternOp, out: &mut String) {
    match op {
        PatternOp::Sep { collection, separator, source } => {
            out.push_str("sep(");
            push_ident(out, collection);
            out.push(',');
            out.push_str(separator);
            out.push(',');
            if let Some(source) = source {
                write_pattern_op(source, out);
            }
            out.push(')');
        },
        PatternOp::Zip { left, right } => {
            out.push_str("zip(");
            push_ident(out, left);
            out.push(',');
            push_ident(out, right);
            out.push(')');
        },
        PatternOp::Map { source, params, body } => {
            out.push_str("map(");
            write_pattern_op(source, out);
            out.push(',');
            push_ids(out, params);
            out.push(',');
            write_syntax_exprs(body, out);
            out.push(')');
        },
        PatternOp::Opt { inner } => {
            out.push_str("opt(");
            write_syntax_exprs(inner, out);
            out.push(')');
        },
        PatternOp::Var(id) => {
            out.push_str("var(");
            push_ident(out, id);
            out.push(')');
        },
    }
}

fn write_eval_mode(mode: EvalMode, out: &mut String) {
    out.push_str(match mode {
        EvalMode::Fold => "fold",
        EvalMode::Step => "step",
    });
}

fn write_typed_params(params: &[TypedParam], out: &mut String) {
    out.push('[');
    for param in params {
        push_ident(out, &param.name);
        out.push(':');
        write_type_expr(&param.ty, out);
        out.push(';');
    }
    out.push(']');
}

fn write_premises(premises: &[Premise], out: &mut String) {
    out.push('[');
    for premise in premises {
        write_premise(premise, out);
        out.push(';');
    }
    out.push(']');
}

fn write_premise(premise: &Premise, out: &mut String) {
    match premise {
        Premise::Freshness(freshness) => {
            out.push_str("fresh(");
            push_ident(out, &freshness.var);
            out.push(',');
            write_freshness_target(&freshness.term, out);
            out.push(')');
        },
        Premise::Congruence { source, target } => {
            out.push_str("cong(");
            push_ident(out, source);
            out.push(',');
            push_ident(out, target);
            out.push(')');
        },
        // ★ (#195) A WITHHELD congruence renders under its OWN constructor name, so a
        // denial can never fingerprint-alias the assertion it denies. A language that
        // declares no withholding emits nothing here, which is why every pre-#195
        // language's `language_definition_fingerprint` is byte-identical across #195
        // (pinned by `ast/tests/congruence_withholding.rs`).
        Premise::CongruenceWithheld { source, target } => {
            out.push_str("ncong(");
            push_ident(out, source);
            out.push(',');
            push_ident(out, target);
            out.push(')');
        },
        Premise::RelationQuery { relation, args } => {
            out.push_str("rel(");
            push_ident(out, relation);
            out.push(',');
            push_ids(out, args);
            out.push(')');
        },
        Premise::ForAll { collection, param, body } => {
            out.push_str("forall(");
            push_ident(out, collection);
            out.push(',');
            push_ident(out, param);
            out.push(',');
            write_premise(body, out);
            out.push(')');
        },
        Premise::BehavioralGuard(pred) => write_behavioral_pred(pred, out),
        Premise::SyntheticInjGuard {
            inner_var,
            source_category,
            excluded_variants,
        } => {
            out.push_str("synthetic-inj(");
            push_ident(out, inner_var);
            out.push(',');
            push_ident(out, source_category);
            out.push(',');
            push_ids(out, excluded_variants);
            out.push(')');
        },
    }
}

fn write_freshness_target(target: &FreshnessTarget, out: &mut String) {
    match target {
        FreshnessTarget::Var(id) => push_ident(out, id),
        FreshnessTarget::CollectionRest(id) => {
            out.push_str("...");
            push_ident(out, id);
        },
    }
}

fn write_pattern(pattern: &Pattern, out: &mut String) {
    match pattern {
        Pattern::Term(term) => write_pattern_term(term, out),
        Pattern::Collection { coll_type, elements, rest } => {
            out.push_str("collection(");
            if let Some(coll_type) = coll_type {
                write_collection_type(coll_type, out);
            }
            out.push(':');
            for element in elements {
                write_pattern(element, out);
                out.push(',');
            }
            out.push(':');
            if let Some(rest) = rest {
                push_ident(out, rest);
            }
            out.push(')');
        },
        Pattern::Map { collection, params, body } => {
            out.push_str("pmap(");
            write_pattern(collection, out);
            out.push(',');
            push_ids(out, params);
            out.push(',');
            write_pattern(body, out);
            out.push(')');
        },
        Pattern::Zip { first, second } => {
            out.push_str("pzip(");
            write_pattern(first, out);
            out.push(',');
            write_pattern(second, out);
            out.push(')');
        },
        // Distinct prefix so no other pattern shape can collide with this one's canonical
        // form; both binders are part of the identity because `args[i:=S]` and
        // `args[j:=S]` differ as patterns (the index is usable on the RHS).
        Pattern::IndexedVec { collection, index, element } => {
            out.push_str("pidx(");
            out.push_str(&collection.to_string());
            out.push(',');
            out.push_str(&index.to_string());
            out.push(',');
            write_pattern(element, out);
            out.push(')');
        },
    }
}

fn write_pattern_term(term: &PatternTerm, out: &mut String) {
    match term {
        PatternTerm::Var(id) => {
            out.push_str("pvar(");
            push_ident(out, id);
            out.push(')');
        },
        PatternTerm::Apply { constructor, args } => {
            out.push_str("apply(");
            push_ident(out, constructor);
            out.push(':');
            for arg in args {
                write_pattern(arg, out);
                out.push(',');
            }
            out.push(')');
        },
        PatternTerm::Lambda { binder, body } => {
            out.push_str("lambda(");
            push_ident(out, binder);
            out.push(',');
            write_pattern(body, out);
            out.push(')');
        },
        PatternTerm::MultiLambda { binders, body } => {
            out.push_str("multilambda(");
            push_ids(out, binders);
            out.push(',');
            write_pattern(body, out);
            out.push(')');
        },
        PatternTerm::Subst { term, var, replacement } => {
            out.push_str("subst(");
            write_pattern(term, out);
            out.push(',');
            push_ident(out, var);
            out.push(',');
            write_pattern(replacement, out);
            out.push(')');
        },
        PatternTerm::MultiSubst { scope, replacements } => {
            out.push_str("multisubst(");
            write_pattern(scope, out);
            out.push(':');
            for replacement in replacements {
                write_pattern(replacement, out);
                out.push(',');
            }
            out.push(')');
        },
    }
}

fn write_equation(equation: &Equation, out: &mut String) {
    push_ident(out, &equation.name);
    out.push(':');
    write_typed_params(&equation.type_context, out);
    out.push(':');
    write_premises(&equation.premises, out);
    out.push(':');
    write_pattern(&equation.left, out);
    out.push('=');
    write_pattern(&equation.right, out);
}

fn write_rewrite(rewrite: &RewriteRule, out: &mut String) {
    push_ident(out, &rewrite.name);
    out.push(':');
    write_typed_params(&rewrite.type_context, out);
    out.push(':');
    write_premises(&rewrite.premises, out);
    out.push(':');
    write_pattern(&rewrite.left, out);
    out.push_str("~>");
    write_pattern(&rewrite.right, out);
    out.push(':');
    out.push_str(if rewrite.is_auto_injected {
        "auto"
    } else {
        "user"
    });
}

fn write_behavioral_pred(pred: &BehavioralPred, out: &mut String) {
    match pred {
        BehavioralPred::RelationQuery { relation_name, args, negated } => {
            out.push_str("brel(");
            push_ident(out, relation_name);
            out.push(',');
            out.push_str(if *negated { "not" } else { "pos" });
            out.push(',');
            for arg in args {
                write_pred_arg(arg, out);
                out.push(',');
            }
            out.push(')');
        },
        BehavioralPred::Quantified { quantifier, var, domain, bound, body } => {
            out.push_str("bquant(");
            write_quantifier(quantifier, out);
            out.push(',');
            push_ident(out, var);
            out.push(',');
            if let Some(domain) = domain {
                push_ident(out, domain);
            }
            out.push(',');
            if let Some(bound) = bound {
                out.push_str(&bound.to_string());
            }
            out.push(',');
            write_behavioral_pred(body, out);
            out.push(')');
        },
        BehavioralPred::And(a, b) => write_binary_pred("and", a, b, out),
        BehavioralPred::Or(a, b) => write_binary_pred("or", a, b, out),
        BehavioralPred::Not(inner) => {
            out.push_str("bnot(");
            write_behavioral_pred(inner, out);
            out.push(')');
        },
        BehavioralPred::Implies(a, b) => write_binary_pred("implies", a, b, out),
        BehavioralPred::AcMatch { bag, elements, rest } => {
            out.push_str("ac(");
            push_ident(out, bag);
            out.push(',');
            push_ids(out, elements);
            out.push(',');
            if let Some(rest) = rest {
                push_ident(out, rest);
            }
            out.push(')');
        },
        BehavioralPred::Top => out.push_str("top"),
    }
}

fn write_binary_pred(name: &str, left: &BehavioralPred, right: &BehavioralPred, out: &mut String) {
    out.push_str(name);
    out.push('(');
    write_behavioral_pred(left, out);
    out.push(',');
    write_behavioral_pred(right, out);
    out.push(')');
}

fn write_quantifier(quantifier: &Quantifier, out: &mut String) {
    out.push_str(match quantifier {
        Quantifier::ForAll => "forall",
        Quantifier::Exists => "exists",
    });
}

fn write_pred_arg(arg: &PredArg, out: &mut String) {
    match arg {
        PredArg::Var(id) => {
            out.push_str("var:");
            push_ident(out, id);
        },
        PredArg::Constant(id) => {
            out.push_str("const:");
            push_ident(out, id);
        },
    }
}

fn write_refinement_predicate(pred: &RefinementPredicate, out: &mut String) {
    out.push_str(&pred.to_string());
}

fn write_guard_config(guards: &GuardConfig, out: &mut String) {
    if let Some(predicates) = &guards.builtin_predicates {
        out.push_str("predicates[");
        for predicate in predicates {
            write_builtin_predicate(predicate, out);
            out.push(';');
        }
        out.push(']');
    }
    if let Some(connectives) = &guards.connectives {
        out.push_str("connectives[");
        for connective in connectives {
            write_connective(connective, out);
            out.push(';');
        }
        out.push(']');
    }
    out.push_str("theories[");
    for theory in &guards.theories {
        write_theory(theory, out);
        out.push(';');
    }
    out.push(']');
    if let Some(channels) = &guards.channels {
        write_channels(channels, out);
    }
}

fn write_builtin_predicate(predicate: &BuiltinPredicate, out: &mut String) {
    push_ident(out, &predicate.name);
    out.push(':');
    for param in &predicate.params {
        write_predicate_param(param, out);
        out.push(',');
    }
    out.push(':');
    for form in &predicate.syntax_forms {
        write_syntax_exprs(form, out);
        out.push('|');
    }
    out.push(':');
    if let Some(value) = predicate.annotations.selectivity {
        out.push_str(&value.to_bits().to_string());
    }
    out.push(':');
    if let Some(value) = predicate.annotations.cost {
        out.push_str(&value.to_string());
    }
}

fn write_predicate_param(param: &PredicateParam, out: &mut String) {
    push_ident(out, &param.name);
    out.push(':');
    if let Some(ty) = &param.ty {
        match ty {
            ParamType::Single(id) => push_ident(out, id),
            ParamType::Union(ids) => push_ids(out, ids),
        }
    }
    out.push(':');
    if let Some(quantifier) = &param.quantifier {
        match quantifier {
            ParamQuantifier::OneOrMore => out.push('+'),
            ParamQuantifier::ZeroOrMore => out.push('*'),
            ParamQuantifier::Range { min, max } => {
                out.push_str(&format!("{{{min},"));
                if let Some(max) = max {
                    out.push_str(&max.to_string());
                }
                out.push('}');
            },
        }
    }
}

fn write_connective(connective: &ConnectiveDecl, out: &mut String) {
    out.push_str(connective.role.as_str());
    out.push('=');
    for keyword in &connective.keywords {
        out.push_str(keyword);
        out.push('|');
    }
}

fn write_theory(theory: &TheoryRegistration, out: &mut String) {
    push_ident(out, &theory.name);
    out.push('=');
    push_tokens(out, &theory.theory_type);
    out.push(':');
    if let Some(types) = &theory.handled_types {
        push_ids(out, types);
    }
}

fn write_channels(channels: &ChannelConfig, out: &mut String) {
    out.push_str("channels[");
    for channel in &channels.channel_categories {
        push_ident(out, &channel.category);
        out.push(';');
    }
    out.push_str("];joins[");
    for join in &channels.join_patterns {
        push_ident(out, &join.label);
        out.push('(');
        for param in &join.channel_params {
            push_ident(out, &param.param_name);
            out.push(':');
            push_ident(out, &param.category);
            out.push(',');
        }
        out.push(')');
        out.push(';');
    }
    out.push(']');
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language::LanguageDef;

    #[test]
    fn fingerprint_is_stable_for_equivalent_parse() {
        let src = r#"
            name: FingerprintSmoke,
            types { Proc }
            terms {
                AddInt . a:Int, b:Int |- a "+" b : Int ;
            }
        "#;
        let left = syn::parse_str::<LanguageDef>(src).expect("left parse");
        let right = syn::parse_str::<LanguageDef>(src).expect("right parse");

        assert_eq!(language_definition_fingerprint(&left), language_definition_fingerprint(&right));
    }

    #[test]
    fn fingerprint_changes_when_compiler_visible_rule_changes() {
        let left = syn::parse_str::<LanguageDef>(
            r#"
                name: FingerprintSmoke,
                types { Proc }
                terms { AddInt . a:Int, b:Int |- a "+" b : Int ; }
            "#,
        )
        .expect("left parse");
        let right = syn::parse_str::<LanguageDef>(
            r#"
                name: FingerprintSmoke,
                types { Proc }
                terms { SubInt . a:Int, b:Int |- a "-" b : Int ; }
            "#,
        )
        .expect("right parse");

        assert_ne!(language_definition_fingerprint(&left), language_definition_fingerprint(&right));
    }

    #[test]
    fn fingerprint_changes_when_mode_token_changes() {
        let left = syn::parse_str::<LanguageDef>(
            r#"
                name: FingerprintModes,
                types { Text; Root }
                tokens {
                    Start = "[a-z]+" : Text push(detail);
                    mode detail {
                        Tail = "[0-9]+" : Text pop;
                    }
                }
                terms { TextNode . t:Text |- t : Root ; }
            "#,
        )
        .expect("left parse");
        let right = syn::parse_str::<LanguageDef>(
            r#"
                name: FingerprintModes,
                types { Text; Root }
                tokens {
                    Start = "[a-z]+" : Text push(detail);
                    mode detail {
                        Tail = "[0-9a-f]+" : Text pop;
                    }
                }
                terms { TextNode . t:Text |- t : Root ; }
            "#,
        )
        .expect("right parse");

        assert_ne!(language_definition_fingerprint(&left), language_definition_fingerprint(&right));
    }

    #[test]
    fn fingerprint_changes_when_sync_or_tree_constraint_changes() {
        let left = syn::parse_str::<LanguageDef>(
            r#"
                name: FingerprintConstraints,
                types { Text; Root }
                tokens {
                    Start = "[a-z]+" : Text -> main;
                    sync {
                        align(main, aux) on "\n";
                        track(aux, main);
                    }
                    tree_invariants {
                        no_nested: forall children of Node { Leaf };
                    }
                }
                terms { TextNode . t:Text |- t : Root ; }
            "#,
        )
        .expect("left parse");
        let right = syn::parse_str::<LanguageDef>(
            r#"
                name: FingerprintConstraints,
                types { Text; Root }
                tokens {
                    Start = "[a-z]+" : Text -> main;
                    sync {
                        align(main, aux) on "\r\n";
                        track(aux, main);
                    }
                    tree_invariants {
                        no_nested: forall children of Node { Branch };
                    }
                }
                terms { TextNode . t:Text |- t : Root ; }
            "#,
        )
        .expect("right parse");

        assert_ne!(language_definition_fingerprint(&left), language_definition_fingerprint(&right));
    }
}
