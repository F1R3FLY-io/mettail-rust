//! Synthetic grammar rules for implicit atomic literals.
//!
//! Calculator / RhoCalc / other grammars do NOT write explicit
//! `IntLit . i:Int |- i : Int` rules in their `terms { }` block —
//! the atomic-literal variant (`Int::NumLit(i32)`, `Bool::BoolLit(bool)`,
//! `Str::StringLit(String)`, etc.) is **synthesized** by
//! `macros/src/gen/types/enums.rs` directly from each `LangType.native_type`.
//!
//! To parse these implicit atomic literals via WPDS, this module fabricates
//! corresponding `GrammarRule` entries — one per category with a
//! `from_literals` `TokenDef`. The fabricated rule's shape makes it classify
//! as `AtomicShape::LiteralPatterned` in `prefix.rs::classify_atomic`.
//!
//! Synthetic rules receive stable `rule_idx` values that appear in the
//! emitted `WPDS_RULES` table alongside user-written rules. Callers
//! (`emit_rule_table`, `emit_prefix_arms_for_category`, `emit_action_for_body`)
//! consume the combined `user + synthetic` list so every downstream emission
//! stays consistent.

use mettail_ast::grammar::{GrammarItem, GrammarRule, NonTerminalKind};
use mettail_ast::language::{CollectionCategory, LanguageDef};
use mettail_ast::types::CollectionType;
use proc_macro2::Span;
use quote::format_ident;
use syn::Ident;

/// Build the full rule set per category, combining user-written rules from
/// `language.terms` with synthetic literal-patterned rules derived from
/// `language.token_defs`.
///
/// Returned `Vec<Vec<GrammarRule>>` is indexed by `categories` source-index.
/// Synthetic rules are appended after user rules so their `rule_idx` values
/// are `len(user_rules_in_cat) + k`.
pub(crate) fn build_per_category_rules(
    language: &LanguageDef,
    categories: &[String],
) -> Vec<Vec<GrammarRule>> {
    let cat_idx: std::collections::HashMap<&str, usize> = categories
        .iter()
        .enumerate()
        .map(|(i, n)| (n.as_str(), i))
        .collect();

    let mut per_cat: Vec<Vec<GrammarRule>> = vec![Vec::new(); categories.len()];

    // 1. User rules from language.terms — in source order.
    for rule in &language.terms {
        let cat = rule.category.to_string();
        if let Some(&i) = cat_idx.get(cat.as_str()) {
            per_cat[i].push(rule.clone());
        }
    }

    // 2. Synthetic literal-patterned rules.
    //
    // Two cases give a category an implicit atomic-literal variant:
    //   (a) Explicit `literals { ... }` block — `from_literals: true` TokenDef.
    //   (b) Implicit native-type — `LangType.native_type = Some(_)` without
    //       a `literals` block (e.g., BaseMath's `![i32] as Num`). The
    //       trampoline path auto-emits a `Token::Integer/Float/Boolean/String`
    //       arm with a default eval body (e.g., `parse_int_lit(text, Some(I32))`).
    //
    // Both cases produce a `LiteralPatterned`-classified rule. The rule's
    // `rust_code` carries the eval body; for case (a) it's the user's
    // `eval: ![ { ... } ]` block; for case (b) it's a synthesized default
    // matching the trampoline's behavior.
    for type_def in &language.types {
        let cat_name = type_def.name.to_string();
        let Some(&i) = cat_idx.get(cat_name.as_str()) else {
            continue;
        };
        // Skip collection-typed categories — handled separately below.
        if type_def.collection_kind.is_some() {
            continue;
        }
        // Does this category have a from_literals TokenDef?
        let _has_literal_block = language.token_defs.iter().any(|td| {
            td.from_literals
                && td.category
                    .as_ref()
                    .map(|c| c.to_string() == cat_name)
                    .unwrap_or(false)
        });
        // Skip if no native_type — a Var-only category gets a separate
        // synthetic Var rule below (Phase 5a).
        let Some(_native_type) = type_def.native_type.as_ref() else {
            continue;
        };
        // Synthesize a rule matching the `AtomicShape::LiteralPatterned`
        // classifier: single-item rule with `items[0] = NonTerminal(Category,
        // cat_name)` and `rule.category == cat_name`.
        let label = crate::gen::generate_literal_label(
            type_def
                .native_type
                .as_ref()
                .expect("native_type checked above"),
        );
        let cat_ident = Ident::new(&cat_name, Span::call_site());
        let synthetic = GrammarRule {
            label,
            category: cat_ident.clone(),
            items: vec![GrammarItem::NonTerminal {
                ident: cat_ident,
                kind: NonTerminalKind::Category,
            }],
            bindings: Vec::new(),
            term_context: None,
            syntax_pattern: None,
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
        };
        per_cat[i].push(synthetic);
    }

    // Stage 1.3: synthetic collection-literal rules for `LangType` entries
    // whose `collection_kind` is `Some(...)`. The macro pipeline emits
    // language-level `ListLit/BagLit/MapLit` constructors; the WPDS path
    // mirrors them with judgement-style rules in the shape
    // `term_context = [Simple{elems, Collection{coll_type, element}}]`,
    // `syntax_pattern = [Literal(open), Op(Sep{elems, sep}), Literal(close)]`
    // so that `classify_collection` picks them up.
    for type_def in &language.types {
        let cat_name = type_def.name.to_string();
        let Some(&i) = cat_idx.get(cat_name.as_str()) else {
            continue;
        };
        let Some(coll_kind) = type_def.collection_kind.as_ref() else {
            continue;
        };
        let (open, close, sep, kind, label_str) = match coll_kind {
            CollectionCategory::List(d) => (
                d.open.clone(),
                d.close.clone(),
                d.sep.clone(),
                CollectionType::Vec,
                "ListLit",
            ),
            CollectionCategory::Bag(d) => (
                d.open.clone(),
                d.close.clone(),
                d.sep.clone(),
                CollectionType::HashBag,
                "BagLit",
            ),
            CollectionCategory::Map(d) => (
                d.open.clone(),
                d.close.clone(),
                d.sep.clone(),
                CollectionType::HashMap,
                "MapLit",
            ),
        };
        // Resolve element category from the collection's payload type.
        let element_cat_str = language
            .collection_element_type_for_category(&type_def.name)
            .map(|i| i.to_string())
            .unwrap_or_else(|| type_def.name.to_string());
        // Trim trailing `(` from open delimiter (default form `list(` → `list`).
        //
        // **Known bug (tracked as B7)**: this 4-element split (`[Literal("list"),
        // Literal("("), Op(Sep), Literal(")")]`) is rejected by
        // `classify_collection` (collection.rs:58) which requires exactly 3
        // syntax_pattern elements. The synthetic rule therefore never
        // registers a collection prefix arm, breaking 211 tests in
        // `gen_calculator_op` that round-trip cross-cat collection terms.
        // The proper fix needs a coordinated change across (a) lexer
        // tokenization of multi-char fixed strings like `"list("`,
        // (b) synthetic.rs to emit a 3-element pattern, and (c)
        // semantic_actions.rs HashMap codegen which currently builds
        // `HashMap<K,V>` (not the wrapper `HashMapLit<K,V>` that
        // `Map::MapLit` accepts) and ignores the drained elements.
        // See `wpds-fork-action-items-2026-04-27.md` task B7.
        let trimmed_open = open.trim_end_matches('(').to_string();
        let needs_synth_paren = open != trimmed_open;
        let cat_ident = Ident::new(&cat_name, Span::call_site());
        let elems_ident = Ident::new("elems", Span::call_site());
        let element_ident = Ident::new(&element_cat_str, Span::call_site());
        let label_ident = Ident::new(label_str, Span::call_site());
        let mut sp: Vec<mettail_ast::grammar::SyntaxExpr> = Vec::new();
        sp.push(mettail_ast::grammar::SyntaxExpr::Literal(trimmed_open));
        if needs_synth_paren {
            sp.push(mettail_ast::grammar::SyntaxExpr::Literal("(".to_string()));
        }
        sp.push(mettail_ast::grammar::SyntaxExpr::Op(
            mettail_ast::grammar::PatternOp::Sep {
                collection: elems_ident.clone(),
                separator: sep,
                source: None,
            },
        ));
        sp.push(mettail_ast::grammar::SyntaxExpr::Literal(close));
        let synthetic = GrammarRule {
            label: label_ident,
            category: cat_ident,
            items: Vec::new(),
            bindings: Vec::new(),
            term_context: Some(vec![mettail_ast::grammar::TermParam::Simple {
                name: elems_ident,
                ty: mettail_ast::types::TypeExpr::Collection {
                    coll_type: kind,
                    element: Box::new(mettail_ast::types::TypeExpr::Base(element_ident)),
                },
            }]),
            syntax_pattern: Some(sp),
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
        };
        per_cat[i].push(synthetic);
    }

    // 3. Phase 5a: synthetic Var rules for user-defined categories without
    //    an explicit Var rule. The macros (`gen/types/enums.rs:113-115`)
    //    auto-generate `<First>Var(OrdVar)` variants for any category
    //    lacking an `is_var_rule` rule. Mirror that logic here so the WPDS
    //    parser can recognize bare Ident tokens as variables of the
    //    surrounding category (e.g., `x` inside `lam x . x` parses as
    //    `Term::TVar(OrdVar(Var::Free(get_or_create_var("x"))))`).
    //
    //    Conditions:
    //    - Category appears in `categories` (so it's actually parseable).
    //    - Category has no `native_type` (i.e., user-defined, not a literal
    //      type like `Int`/`Bool`/`Str`).
    //    - Category does not already have a user rule whose `items[0] =
    //      NonTerminal { kind: Var, .. }`.
    for type_def in &language.types {
        let cat_name = type_def.name.to_string();
        let Some(&i) = cat_idx.get(cat_name.as_str()) else {
            continue;
        };
        // Skip categories with a native_type (they're literal-only).
        if type_def.native_type.is_some() {
            continue;
        }
        // Skip if the user already wrote an explicit Var rule for this category.
        let has_user_var_rule = per_cat[i].iter().any(|r| {
            r.items
                .first()
                .map(|item| matches!(item, GrammarItem::NonTerminal { kind: NonTerminalKind::Var, .. }))
                .unwrap_or(false)
        });
        if has_user_var_rule {
            continue;
        }
        // Synthesize a Var rule for this category. Shape: single-item rule
        // with `items[0] = NonTerminal(Var, cat_name)`. Label = generate_var_label.
        let label = crate::gen::generate_var_label(&type_def.name);
        let cat_ident = Ident::new(&cat_name, Span::call_site());
        let synthetic = GrammarRule {
            label,
            category: cat_ident.clone(),
            items: vec![GrammarItem::NonTerminal {
                ident: cat_ident,
                kind: NonTerminalKind::Var,
            }],
            bindings: Vec::new(),
            term_context: None,
            syntax_pattern: None,
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
        };
        per_cat[i].push(synthetic);
    }

    // Silence `unused` (format_ident imported for call-site clarity).
    let _ = format_ident!("_unused");

    per_cat
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::language::{LangType, TokenDef};
    use proc_macro2::Span;
    use syn::{parse_quote, Ident};

    fn lang_with_int_and_bool_literals() -> LanguageDef {
        LanguageDef {
            name: Ident::new("Test", Span::call_site()),
            options: Default::default(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: vec![
                LangType {
                    name: Ident::new("Int", Span::call_site()),
                    native_type: Some(parse_quote!(i32)),
                    collection_kind: None,
                },
                LangType {
                    name: Ident::new("Bool", Span::call_site()),
                    native_type: Some(parse_quote!(bool)),
                    collection_kind: None,
                },
            ],
            refinement_types: Vec::new(),
            token_defs: vec![
                TokenDef {
                    name: Ident::new("Integer", Span::call_site()),
                    pattern: r"[0-9]+".to_string(),
                    category: Some(Ident::new("Int", Span::call_site())),
                    rust_code: Some(quote::quote! { Ok(0i32) }),
                    priority: None,
                    push_mode: None,
                    is_pop: false,
                    stream: None,
                    from_literals: true,
                },
                TokenDef {
                    name: Ident::new("Boolean", Span::call_site()),
                    pattern: r"true|false".to_string(),
                    category: Some(Ident::new("Bool", Span::call_site())),
                    rust_code: Some(quote::quote! { Ok(false) }),
                    priority: None,
                    push_mode: None,
                    is_pop: false,
                    stream: None,
                    from_literals: true,
                },
            ],
            mode_defs: Vec::new(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms: Vec::new(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        }
    }

    #[test]
    fn synthesizes_literal_patterned_rule_per_literal_category() {
        let lang = lang_with_int_and_bool_literals();
        let categories = vec!["Int".to_string(), "Bool".to_string()];
        let per_cat = build_per_category_rules(&lang, &categories);
        assert_eq!(per_cat.len(), 2);
        // Int: one synthetic rule labeled "NumLit".
        assert_eq!(per_cat[0].len(), 1);
        assert_eq!(per_cat[0][0].label.to_string(), "NumLit");
        assert_eq!(per_cat[0][0].category.to_string(), "Int");
        // Bool: one synthetic rule labeled "BoolLit".
        assert_eq!(per_cat[1].len(), 1);
        assert_eq!(per_cat[1][0].label.to_string(), "BoolLit");
    }

    #[test]
    fn synthesizes_for_native_type_without_literal_block() {
        // Stage 4 fix: categories with `native_type` are synthesized
        // regardless of whether they have a `from_literals` TokenDef.
        // Cross-cat projection rules referring to these as source
        // categories need a parseable target — without synthesis, the
        // cross-cat dispatch falls back to recursing into the result
        // category (e.g., Proc → Proc) and fails.
        let mut lang = lang_with_int_and_bool_literals();
        lang.token_defs.clear(); // Remove all literal blocks.
        let categories = vec!["Int".to_string(), "Bool".to_string()];
        let per_cat = build_per_category_rules(&lang, &categories);
        // Both Int and Bool have native_type so each gets a synthetic
        // literal-patterned rule even after removing token_defs.
        assert_eq!(per_cat[0].len(), 1, "Int should have 1 synthetic rule");
        assert_eq!(per_cat[1].len(), 1, "Bool should have 1 synthetic rule");
        assert_eq!(per_cat[0][0].label.to_string(), "NumLit");
        assert_eq!(per_cat[1][0].label.to_string(), "BoolLit");
    }
}
