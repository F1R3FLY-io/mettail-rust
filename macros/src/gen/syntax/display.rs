// Pretty-printing generation for MeTTaIL languages
//
// This module generates trampolined (iterative, work-stack-based) Display trait
// implementations for AST types.  Instead of recursively calling
// `write!(f, "{}", child)` — which causes stack overflow for deeply nested
// terms — the generated code pushes `DisplayTask` variants onto an explicit
// work stack and processes them iteratively.
//
// Architecture mirrors `match_pattern.rs`: a heterogeneous `DisplayTask` enum
// with one variant per category, a thread-local `Cell<Vec<DisplayTask>>` pool,
// and a single `display_iterative` driver loop.

#![allow(clippy::cmp_owned)]

use mettail_ast::{
    grammar::{GrammarItem, GrammarRule, NonTerminalKind, PatternOp, SyntaxExpr, TermParam},
    language::LanguageDef,
    types::{CollectionType, TypeExpr},
};
use crate::gen::native::has_native_type;
use crate::gen::{generate_literal_label, generate_var_label, is_literal_rule, is_var_rule};
use crate::gen::syntax::parser::prattail_bridge::language_def_to_spec;
use crate::gen::term_ops::subst::{collect_category_variants, FieldInfo, VariantKind};
use mettail_prattail::binding_power::{
    analyze_binding_powers, compute_prefix_bp, InfixRuleInfo, MixfixPart as BpMixfixPart,
};
use mettail_prattail::SyntaxItemSpec;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashMap;

// =============================================================================
// Main Entry Point
// =============================================================================

/// Binding power information for a single constructor in the Display context.
#[derive(Debug, Clone)]
struct DisplayBpInfo {
    /// Left binding power of this operator.
    left_bp: u8,
    /// Right binding power of this operator.
    right_bp: u8,
    /// Whether this is a postfix operator.
    is_postfix: bool,
    /// Whether this is a mixfix operator.
    is_mixfix: bool,
    /// Whether this is a cross-category operator (operands differ from result).
    is_cross_category: bool,
}

/// Binding power information for a unary prefix operator.
#[derive(Debug, Clone)]
struct DisplayPrefixBpInfo {
    /// Prefix binding power (child gets this as min_bp).
    prefix_bp: u8,
}

/// Lookup table for binding power information, keyed by constructor label.
#[derive(Debug, Clone)]
struct BpLookup {
    /// Infix/postfix/mixfix operators: label -> BP info.
    infix: HashMap<String, DisplayBpInfo>,
    /// Unary prefix operators: label -> prefix BP.
    prefix: HashMap<String, DisplayPrefixBpInfo>,
}

impl BpLookup {
    fn empty() -> Self {
        BpLookup {
            infix: HashMap::new(),
            prefix: HashMap::new(),
        }
    }
}

/// Build a `BpLookup` from a `LanguageDef`.
///
/// Converts the language definition to a spec, classifies rules, computes
/// binding powers, and builds a label-indexed lookup table for display codegen.
fn build_bp_lookup(language: &LanguageDef) -> BpLookup {
    let spec = language_def_to_spec(language);

    // Extract infix rules exactly as the pipeline does
    let infix_rules: Vec<InfixRuleInfo> = spec
        .rules
        .iter()
        .filter(|r| r.is_infix)
        .map(|r| {
            let (is_mixfix, mixfix_parts) = extract_mixfix_parts_for_display(&r.syntax);
            InfixRuleInfo {
                label: r.label.clone(),
                terminal: r
                    .syntax
                    .iter()
                    .find_map(|item| {
                        if let SyntaxItemSpec::Terminal(t) = item {
                            Some(t.clone())
                        } else {
                            None
                        }
                    })
                    .unwrap_or_default(),
                category: r.category.clone(),
                result_category: r.category.clone(),
                associativity: r.associativity,
                is_cross_category: r.is_cross_category,
                is_postfix: r.is_postfix,
                is_mixfix,
                mixfix_parts,
            }
        })
        .collect();

    let bp_table = analyze_binding_powers(&infix_rules);

    // Stage 3.27d-pre (2026-04-30): prefix_bp now derives from
    // `compute_prefix_bp()` (single source of truth, queries bp_table directly).
    // The local max_infix_bp HashMap was removed.

    let mut lookup = BpLookup::empty();

    // Build a terminal→same-category BP map so cross-category operators can
    // use the same parenthesization threshold as their same-category counterpart.
    // Without this, cross-category operators (e.g., LtInt: Int×Int→Bool) get
    // different BPs from same-category operators (e.g., LtBool: Bool×Bool→Bool)
    // despite sharing the same token. This causes Display to produce parenthesization
    // that doesn't roundtrip through the parser (which uses a single token-based BP).
    let mut same_cat_bp: HashMap<(String, String), (u8, u8)> = HashMap::new();
    for op in &bp_table.operators {
        if !op.is_cross_category {
            same_cat_bp.insert(
                (op.terminal.clone(), op.result_category.clone()),
                (op.left_bp, op.right_bp),
            );
        }
    }

    // Add infix/postfix/mixfix operators
    for op in &bp_table.operators {
        // For cross-category operators, use the same-category operator's BP
        // for parenthesization (own_left_bp check) since the parser uses
        // token-based BP lookup which maps to the same-category variant.
        let (display_left_bp, display_right_bp) = if op.is_cross_category {
            same_cat_bp
                .get(&(op.terminal.clone(), op.result_category.clone()))
                .copied()
                .unwrap_or((op.left_bp, op.right_bp))
        } else {
            (op.left_bp, op.right_bp)
        };
        lookup.infix.insert(
            op.label.clone(),
            DisplayBpInfo {
                left_bp: display_left_bp,
                right_bp: display_right_bp,
                is_postfix: op.is_postfix,
                is_mixfix: op.is_mixfix,
                is_cross_category: op.is_cross_category,
            },
        );
    }

    // Add unary prefix operators (Stage 3.27d-pre standardized helper)
    for rule in &spec.rules {
        if rule.is_unary_prefix {
            let prefix_bp = compute_prefix_bp(
                &rule.category,
                rule.prefix_precedence,
                &bp_table,
            );
            lookup.prefix.insert(
                rule.label.clone(),
                DisplayPrefixBpInfo { prefix_bp },
            );
        }
    }

    lookup
}

/// Extract mixfix parts from syntax items (same logic as pipeline.rs).
fn extract_mixfix_parts_for_display(syntax: &[SyntaxItemSpec]) -> (bool, Vec<BpMixfixPart>) {
    let operand_count = syntax
        .iter()
        .filter(|item| matches!(item, SyntaxItemSpec::NonTerminal { .. }))
        .count();
    let terminal_count = syntax
        .iter()
        .filter(|item| matches!(item, SyntaxItemSpec::Terminal(_)))
        .count();

    if operand_count < 3 || terminal_count < 2 {
        return (false, Vec::new());
    }

    let mut parts = Vec::with_capacity(operand_count - 1);
    let mut after_trigger = false;
    let mut skip_count = 0;

    for item in syntax {
        match item {
            SyntaxItemSpec::NonTerminal { .. } if skip_count == 0 => {
                skip_count += 1;
            },
            SyntaxItemSpec::Terminal(_) if !after_trigger => {
                after_trigger = true;
            },
            SyntaxItemSpec::NonTerminal { category, param_name } if after_trigger => {
                parts.push(BpMixfixPart {
                    operand_category: category.clone(),
                    param_name: param_name.clone(),
                    preceding_terminals: Vec::new(),
                    following_terminals: Vec::new(),
                });
            },
            SyntaxItemSpec::Terminal(t) if after_trigger => {
                // L12 follow-up B6 (2026-05-07): append literal to the
                // last part's following_terminals vec for postfix-mixfix
                // support (consecutive literals between operands).
                if let Some(last_part) = parts.last_mut() {
                    last_part.following_terminals.push(t.clone());
                }
            },
            _ => {},
        }
    }

    (true, parts)
}

/// Generate trampolined Display implementations for all exported categories.
///
/// Produces:
/// 1. `DisplayTask` enum with one variant per category + literal/string helpers
/// 2. `DISPLAY_TASK_POOL` thread-local for zero-allocation steady-state
/// 3. `display_iterative()` driver loop
/// 4. `impl Display for Cat` delegating to the iterative engine
pub fn generate_display(language: &LanguageDef) -> TokenStream {
    // Compute binding power lookup for precedence-aware parenthesization
    let bp_lookup = build_bp_lookup(language);

    let task_enum = generate_display_task_enum(language);
    let iterative_engine = generate_iterative_engine(language, &bp_lookup);
    let display_impls = generate_display_impls(language);

    quote! {
        #task_enum
        #iterative_engine
        #display_impls
    }
}

// =============================================================================
// DisplayTask Enum + TLS Pool
// =============================================================================

/// Generate the `DisplayTask` enum and thread-local pool.
fn generate_display_task_enum(language: &LanguageDef) -> TokenStream {
    let variants: Vec<TokenStream> = language
        .types
        .iter()
        .map(|t| {
            let cat = &t.name;
            let variant_name = format_ident!("Display{}", cat);
            quote! {
                #variant_name(*const #cat, u8)
            }
        })
        .collect();

    quote! {
        /// Work item for the iterative Display engine.
        ///
        /// Each category variant wraps a raw pointer to a term to be displayed,
        /// plus a `min_bp` (minimum binding power) for precedence-aware
        /// parenthesization.  When an infix operator's own `left_bp` is less
        /// than the inherited `min_bp`, the operator wraps its output in `(…)`.
        /// `WriteLiteral` and `WriteString` variants handle static and dynamic
        /// text fragments (separators, delimiters, variable names, etc.) that do
        /// not require recursive descent into child terms.
        #[allow(dead_code)]
        enum DisplayTask {
            #(#variants,)*
            /// Write a compile-time-known string (separator, delimiter, keyword).
            WriteLiteral(&'static str),
            /// Write a dynamically computed string (variable name, formatted value).
            WriteString(String),
        }

        thread_local! {
            /// Pool for reusing `DisplayTask` work stacks across Display calls.
            ///
            /// The `Cell<Vec<DisplayTask>>` pattern allows zero-allocation
            /// steady-state operation: the first call allocates, subsequent
            /// calls reuse the same buffer. Re-entrant calls (e.g. from
            /// collection element formatting) get fresh vectors; the outermost
            /// call retains capacity.
            static DISPLAY_TASK_POOL: std::cell::Cell<Vec<DisplayTask>> =
                std::cell::Cell::new(Vec::new());
        }
    }
}

// =============================================================================
// Iterative Engine
// =============================================================================

/// Generate the `display_iterative` function that processes the work stack.
fn generate_iterative_engine(language: &LanguageDef, bp_lookup: &BpLookup) -> TokenStream {
    let category_arms: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| generate_engine_category_arm(&lang_type.name, language, bp_lookup))
        .collect();

    quote! {
        /// Iterative Display engine.
        ///
        /// Pops tasks from the work stack and either writes text directly to
        /// the formatter or pushes sub-tasks for child terms.  Stack-safe for
        /// arbitrarily deep terms.
        #[allow(dead_code)]
        fn display_iterative(
            stack: &mut Vec<DisplayTask>,
            f: &mut std::fmt::Formatter,
        ) -> std::fmt::Result {
            while let Some(task) = stack.pop() {
                match task {
                    DisplayTask::WriteLiteral(s) => {
                        f.write_str(s)?;
                    }
                    DisplayTask::WriteString(s) => {
                        f.write_str(&s)?;
                    }
                    #(#category_arms)*
                }
            }
            Ok(())
        }
    }
}

/// Generate the match arm for one category inside the iterative engine.
///
/// For each variant of the category, we generate code that either:
/// - Writes text directly (literals, vars, nullary constructors)
/// - Pushes sub-tasks in REVERSE order for child terms (stack is LIFO)
fn generate_engine_category_arm(
    category: &syn::Ident,
    language: &LanguageDef,
    bp_lookup: &BpLookup,
) -> TokenStream {
    let task_variant = format_ident!("Display{}", category);

    // Group rules by category for lookup
    let mut rules_by_cat: HashMap<String, Vec<&GrammarRule>> = HashMap::new();
    for rule in &language.terms {
        let cat_name = rule.category.to_string();
        rules_by_cat.entry(cat_name).or_default().push(rule);
    }

    let rules = rules_by_cat
        .get(&category.to_string())
        .map(|v| v.as_slice())
        .unwrap_or(&[]);

    // Generate match arms for grammar-defined rules
    let mut variant_arms: Vec<TokenStream> = rules
        .iter()
        .map(|rule| generate_engine_rule_arm(rule, language, bp_lookup))
        .collect();

    // Auto-generated Var variant
    let has_var_rule = rules.iter().any(|rule| is_var_rule(rule));
    if !has_var_rule {
        variant_arms.push(generate_engine_auto_var_arm(category));
    }

    // Auto-generated Literal variant
    let has_literal_rule = rules.iter().any(|rule| is_literal_rule(rule));
    if let Some(native_type) = has_native_type(category, language) {
        if !has_literal_rule {
            // For collection-kind categories (![Vec<T>] / ![HashBag<T>] /
            // ![HashMap<K,V>] as Cat), thread the collection delimiters so
            // Display matches the parser-expected surface syntax
            // (`list(...)`, `bag(...)`, `map(k:v, ...)`) — merge plan B.1.
            let collection_kind = language
                .types
                .iter()
                .find(|t| &t.name == category)
                .and_then(|t| t.collection_kind.as_ref());
            variant_arms.push(generate_engine_auto_literal_arm(
                category,
                native_type,
                collection_kind,
            ));
        }
    }

    // Auto-generated lambda/apply variants — post-HOL-B: only for
    // (category, domain) pairs flagged by `compute_hol_domain_pairs`.
    let hol_pairs = crate::logic::common::compute_hol_domain_pairs(language);
    let category_str_disp = category.to_string();
    for domain_lang_type in &language.types {
        let domain_name = &domain_lang_type.name;

        if !hol_pairs.contains(&(category_str_disp.clone(), domain_name.to_string())) {
            continue;
        }

        // LamDomain
        let lam_variant = format_ident!("Lam{}", domain_name);
        let body_task_variant = format_ident!("Display{}", category);
        variant_arms.push(quote! {
            #category::#lam_variant(scope) => {
                let inner = scope.inner();
                let var_name = inner.unsafe_pattern.0.pretty_name.as_deref().unwrap_or("?").to_string();
                // Push in reverse: "^" name ".{" body "}"
                stack.push(DisplayTask::WriteLiteral("}"));
                stack.push(DisplayTask::#body_task_variant(&*inner.unsafe_body as *const _, 0));
                stack.push(DisplayTask::WriteLiteral(".{"));
                stack.push(DisplayTask::WriteString(var_name));
                stack.push(DisplayTask::WriteLiteral("^"));
            }
        });

        // MLamDomain
        let mlam_variant = format_ident!("MLam{}", domain_name);
        variant_arms.push(quote! {
            #category::#mlam_variant(scope) => {
                let inner = scope.inner();
                let names: Vec<_> = inner.unsafe_pattern.iter()
                    .map(|b| b.0.pretty_name.as_deref().unwrap_or("?").to_string())
                    .collect();
                // Push in reverse: "^[" names "].{" body "}"
                stack.push(DisplayTask::WriteLiteral("}"));
                stack.push(DisplayTask::#body_task_variant(&*inner.unsafe_body as *const _, 0));
                stack.push(DisplayTask::WriteLiteral("].{"));
                stack.push(DisplayTask::WriteString(names.join(",")));
                stack.push(DisplayTask::WriteLiteral("^["));
            }
        });

        // ApplyDomain
        let apply_variant = format_ident!("Apply{}", domain_name);
        let domain_lower = domain_name.to_string().to_lowercase();
        let arg_task_variant = format_ident!("Display{}", domain_name);
        let apply_prefix: String = format!("${}(", domain_lower);
        variant_arms.push(quote! {
            #category::#apply_variant(lam, arg) => {
                // Push in reverse: "$domain(" lam ", " arg ")"
                stack.push(DisplayTask::WriteLiteral(")"));
                stack.push(DisplayTask::#arg_task_variant(&**arg as *const _, 0));
                stack.push(DisplayTask::WriteLiteral(", "));
                stack.push(DisplayTask::#body_task_variant(&**lam as *const _, 0));
                stack.push(DisplayTask::WriteString(#apply_prefix.to_string()));
            }
        });

        // MApplyDomain
        let mapply_variant = format_ident!("MApply{}", domain_name);
        let mapply_prefix: String = format!("$${}", domain_lower);
        variant_arms.push(quote! {
            #category::#mapply_variant(lam, args) => {
                // Each arg is pushed as a separate Display task so the
                // iterative driver traverses them without recursion — the
                // previous inline `.to_string()` call on each arg re-entered
                // Display at an arbitrary depth determined by the arg's
                // subtree, which was a stack-overflow hazard for deep args.
                // Layout: "$$domain" "(" lam [", " arg_0 ... ", " arg_{n-1}] ")"
                stack.push(DisplayTask::WriteLiteral(")"));
                // Push args in reverse order so arg_0 is processed first (LIFO).
                // `args` is `Vec<ArgCat>` (not boxed); iter() yields `&ArgCat`
                // which can be cast directly to `*const _`.
                for (i, arg) in args.iter().enumerate().rev() {
                    stack.push(DisplayTask::#arg_task_variant(arg as *const _, 0));
                    // Comma comes BEFORE each arg (after `lam` for arg_0, after
                    // previous arg for arg_i). With reverse iteration, push the
                    // comma AFTER the arg in stack order so it prints BEFORE.
                    stack.push(DisplayTask::WriteLiteral(", "));
                    let _ = i;
                }
                stack.push(DisplayTask::#body_task_variant(&**lam as *const _, 0));
                stack.push(DisplayTask::WriteLiteral("("));
                stack.push(DisplayTask::WriteString(#mapply_prefix.to_string()));
            }
        });
    }

    quote! {
        DisplayTask::#task_variant(ptr, min_bp) => {
            // SAFETY: ptr was derived from a &Cat reference within the same
            // fmt() call; the referent is alive for the entire duration.
            let term = unsafe { &*ptr };
            // Suppress unused warning for non-operator variants.
            let _ = min_bp;
            match term {
                #(#variant_arms,)*
            }
        }
    }
}

// =============================================================================
// Per-Rule Arm Generation (for the iterative engine)
// =============================================================================

/// Generate the match arm for a single grammar rule inside the iterative engine.
fn generate_engine_rule_arm(rule: &GrammarRule, language: &LanguageDef, bp_lookup: &BpLookup) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;

    // New syntax_pattern rules
    if let (Some(syntax_pattern), Some(term_context)) = (&rule.syntax_pattern, &rule.term_context) {
        return generate_engine_syntax_pattern_arm(rule, syntax_pattern, term_context, language, bp_lookup);
    }

    // Old-style binder rules
    if !rule.bindings.is_empty() {
        return generate_engine_binder_arm(rule, language);
    }

    // Collect field names and their types
    let fields: Vec<(String, Option<&syn::Ident>)> = rule
        .items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| match item {
            GrammarItem::NonTerminal { ident, .. } => Some((format!("f{}", i), Some(ident))),
            GrammarItem::Collection { .. } => Some((format!("f{}", i), None)),
            _ => None,
        })
        .collect();

    if fields.is_empty() {
        // Nullary: write terminals directly
        let output = format_terminals(rule);
        quote! {
            #category::#label => {
                f.write_str(#output)?;
            }
        }
    } else {
        let field_names: Vec<syn::Ident> = fields
            .iter()
            .map(|(name, _)| syn::Ident::new(name, proc_macro2::Span::call_site()))
            .collect();

        // Check if any field is Var
        let has_var = fields.iter().any(|(_, nt_opt)| {
            nt_opt.as_ref().is_some_and(|nt| NonTerminalKind::classify(&nt.to_string()) == NonTerminalKind::Var)
        });

        if has_var {
            generate_engine_var_fields_arm(rule, &fields, &field_names, bp_lookup)
        } else {
            generate_engine_regular_arm(rule, &fields, &field_names, language, bp_lookup)
        }
    }
}

/// Generate arm for rules with Var fields (old syntax).
/// Var fields write their name directly, non-Var fields push DisplayTask.
fn generate_engine_var_fields_arm(
    rule: &GrammarRule,
    fields: &[(String, Option<&syn::Ident>)],
    field_names: &[syn::Ident],
    _bp_lookup: &BpLookup,
) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;

    // Build list of push operations in reverse order.
    // We construct a forward list first, then reverse.
    let mut forward_ops: Vec<TokenStream> = Vec::new();
    let mut field_iter = fields.iter().zip(field_names.iter());

    for item in &rule.items {
        match item {
            GrammarItem::Terminal(term) => {
                let escaped = term.clone();
                forward_ops.push(quote! {
                    stack.push(DisplayTask::WriteString(#escaped.to_string()));
                });
            },
            GrammarItem::NonTerminal { kind: NonTerminalKind::Var, .. } => {
                if let Some((_, field_name)) = field_iter.next() {
                    forward_ops.push(quote! {
                        stack.push(DisplayTask::WriteString(
                            match &(#field_name).0 {
                                mettail_runtime::Var::Free(fv) => fv.pretty_name.as_ref().map(|s| s.to_string()).unwrap_or_else(|| "_".to_string()),
                                mettail_runtime::Var::Bound(bv) => bv.pretty_name.as_ref().map(|s| s.to_string()).unwrap_or_else(|| "_".to_string()),
                            }
                        ));
                    });
                }
            },
            GrammarItem::NonTerminal { ident: nt, .. } => {
                if let Some((_, field_name)) = field_iter.next() {
                    let nt_str = nt.to_string();
                    // Find which category this nonterminal belongs to
                    let task_variant = format_ident!("Display{}", nt_str);
                    forward_ops.push(quote! {
                        stack.push(DisplayTask::#task_variant(&**#field_name as *const _, 0));
                    });
                }
            },
            _ => {},
        }
    }

    // Reverse the ops so stack processes them left-to-right
    forward_ops.reverse();

    quote! {
        #category::#label(#(#field_names),*) => {
            #(#forward_ops)*
        }
    }
}

/// Generate arm for regular rules (no Var fields, no binders, no syntax_pattern).
///
/// Precedence-aware: for infix/postfix/prefix operators, wraps the output in
/// parentheses when the inherited `min_bp` exceeds the operator's own binding power.
/// Non-operator rules push children with `min_bp = 0` (no parenthesization).
fn generate_engine_regular_arm(
    rule: &GrammarRule,
    fields: &[(String, Option<&syn::Ident>)],
    field_names: &[syn::Ident],
    _language: &LanguageDef,
    bp_lookup: &BpLookup,
) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;
    let label_str = label.to_string();

    // Check if this rule is an infix/postfix/mixfix operator
    let infix_info = bp_lookup.infix.get(&label_str);
    // Check if this rule is a unary prefix operator
    let prefix_info = bp_lookup.prefix.get(&label_str);

    // Determine child min_bp values for each NonTerminal field
    // For infix: first NT gets left_bp, last NT gets right_bp
    // For prefix: single NT gets prefix_bp
    // For postfix: single NT gets left_bp
    // For mixfix: first NT gets left_bp, middle NTs get 0, last NT gets right_bp
    // For non-operator: all NTs get 0
    let nt_count = rule.items.iter().filter(|i| matches!(i, GrammarItem::NonTerminal { .. })).count();

    let mut forward_ops: Vec<TokenStream> = Vec::new();
    let mut field_iter = fields.iter().zip(field_names.iter());
    let mut nt_idx: usize = 0;

    for item in &rule.items {
        match item {
            GrammarItem::Terminal(term) => {
                let escaped = term.clone();
                forward_ops.push(quote! {
                    stack.push(DisplayTask::WriteString(#escaped.to_string()));
                });
            },
            GrammarItem::NonTerminal { ident: nt, .. } => {
                if let Some(((_, _), field_name)) = field_iter.next() {
                    let nt_str = nt.to_string();
                    let task_variant = format_ident!("Display{}", nt_str);

                    let child_min_bp: u8 = if let Some(info) = infix_info {
                        if info.is_postfix {
                            // Postfix: single operand gets left_bp
                            info.left_bp
                        } else if info.is_mixfix {
                            // Mixfix: first operand = left_bp, middle = 0, last = right_bp
                            if nt_idx == 0 {
                                info.left_bp
                            } else if nt_idx == nt_count - 1 {
                                info.right_bp
                            } else {
                                0
                            }
                        } else if info.is_cross_category {
                            // Cross-category: children are in different category, reset BP
                            0
                        } else {
                            // Regular infix: left child = left_bp, right child = right_bp
                            if nt_idx == 0 {
                                info.left_bp
                            } else {
                                info.right_bp
                            }
                        }
                    } else if let Some(pinfo) = prefix_info {
                        // Unary prefix: child gets prefix_bp
                        pinfo.prefix_bp
                    } else {
                        0
                    };

                    forward_ops.push(quote! {
                        stack.push(DisplayTask::#task_variant(&**#field_name as *const _, #child_min_bp));
                    });
                    nt_idx += 1;
                }
            },
            GrammarItem::Collection { coll_type, separator, delimiters, .. } => {
                if let Some(((_, _), field_name)) = field_iter.next() {
                    // Collection fields write inline (elements may not be deeply nested)
                    let sep = separator.clone();
                    // B9 / Class 2 (2026-05-08): branch on coll_type. Vec
                    // yields bare elements; HashBag yields (elem, count)
                    // tuples; HashSet yields bare elements with order
                    // preservation via sort. The previous unconditional
                    // (elem, count) pattern only matched HashBag and
                    // failed to compile when Vec collections appeared
                    // (e.g. Class-2 binder rule with Vec<Proc> slot or a
                    // Class-5 collection rule with Vec element type).
                    let items_expr = match coll_type {
                        mettail_ast::types::CollectionType::Vec => quote! {
                            let items: Vec<String> = #field_name.iter()
                                .map(|elem| elem.to_string())
                                .collect();
                        },
                        mettail_ast::types::CollectionType::HashSet => quote! {
                            let mut items: Vec<String> = #field_name.iter()
                                .map(|elem| elem.to_string())
                                .collect();
                            items.sort();
                        },
                        mettail_ast::types::CollectionType::HashBag => quote! {
                            let mut items: Vec<String> = #field_name.iter().map(|(elem, count)| {
                                (0..count).map(|_| elem.to_string()).collect::<Vec<_>>().join(&format!(" {} ", #sep))
                            }).collect();
                            items.sort();
                        },
                        mettail_ast::types::CollectionType::HashMap => quote! {
                            // HashMap display path is handled separately;
                            // defensive fallback that yields each entry's
                            // Display form. Pilot grammars do not exercise
                            // HashMap-in-binder Class 2.
                            let mut items: Vec<String> = #field_name.iter()
                                .map(|(k, v)| format!("{} : {}", k, v))
                                .collect();
                            items.sort();
                        },
                    };
                    if let Some((open, close)) = delimiters {
                        forward_ops.push(quote! {
                            {
                                let mut s = String::from(#open);
                                #items_expr
                                if !items.is_empty() {
                                    s.push_str(&items.join(&format!(" {} ", #sep)));
                                }
                                s.push_str(#close);
                                stack.push(DisplayTask::WriteString(s));
                            }
                        });
                    } else {
                        forward_ops.push(quote! {
                            {
                                #items_expr
                                stack.push(DisplayTask::WriteString(items.join(&format!(" {} ", #sep))));
                            }
                        });
                    }
                    nt_idx += 1;
                }
            },
            GrammarItem::Binder { .. } => {
                // Handled in binder path
            },
        }
    }

    // Reverse so stack processes left-to-right
    forward_ops.reverse();

    // Wrap in parenthesization logic for infix/prefix/postfix operators
    if let Some(info) = infix_info {
        let own_left_bp = info.left_bp;
        quote! {
            #category::#label(#(#field_names),*) => {
                let needs_parens = #own_left_bp < min_bp;
                if needs_parens {
                    stack.push(DisplayTask::WriteLiteral(")"));
                }
                #(#forward_ops)*
                if needs_parens {
                    stack.push(DisplayTask::WriteLiteral("("));
                }
            }
        }
    } else if let Some(pinfo) = prefix_info {
        let own_bp = pinfo.prefix_bp;
        quote! {
            #category::#label(#(#field_names),*) => {
                let needs_parens = #own_bp < min_bp;
                if needs_parens {
                    stack.push(DisplayTask::WriteLiteral(")"));
                }
                #(#forward_ops)*
                if needs_parens {
                    stack.push(DisplayTask::WriteLiteral("("));
                }
            }
        }
    } else {
        quote! {
            #category::#label(#(#field_names),*) => {
                #(#forward_ops)*
            }
        }
    }
}

/// Generate arm for old-style binder rules.
fn generate_engine_binder_arm(rule: &GrammarRule, _language: &LanguageDef) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;

    let (binder_idx, body_indices) = &rule.bindings[0];
    let body_idx = body_indices[0];

    // Collect regular fields (not binder, not body)
    let mut regular_fields = Vec::new();
    let mut has_scope = false;
    let mut field_idx = 0;

    for (i, item) in rule.items.iter().enumerate() {
        match item {
            GrammarItem::NonTerminal { .. } if i == body_idx => {
                has_scope = true;
            },
            GrammarItem::NonTerminal { .. } => {
                regular_fields.push(format!("f{}", field_idx));
                field_idx += 1;
            },
            GrammarItem::Binder { .. } if i == *binder_idx => {
                // Skip - it's in the scope
            },
            _ => {},
        }
    }

    let mut all_fields = regular_fields.clone();
    if has_scope {
        all_fields.push("scope".to_string());
    }

    let field_idents: Vec<syn::Ident> = all_fields
        .iter()
        .map(|name| syn::Ident::new(name, proc_macro2::Span::call_site()))
        .collect();

    // Build forward push operations from items.
    // The binder name and body come from scope.inner().
    let mut forward_ops: Vec<TokenStream> = Vec::new();
    let mut regular_field_iter = regular_fields.iter();

    // Get the body category from the rule
    let body_cat = match &rule.items[body_idx] {
        GrammarItem::NonTerminal { ident: cat, .. } => cat.clone(),
        _ => panic!("Body index doesn't point to a NonTerminal"),
    };
    let body_task_variant = format_ident!("Display{}", body_cat);

    for (i, item) in rule.items.iter().enumerate() {
        match item {
            GrammarItem::Terminal(term) => {
                let escaped = term.clone();
                forward_ops.push(quote! {
                    stack.push(DisplayTask::WriteString(#escaped.to_string()));
                });
            },
            GrammarItem::NonTerminal { .. } if i == body_idx => {
                // Body from scope — binder body resets precedence context
                forward_ops.push(quote! {
                    stack.push(DisplayTask::#body_task_variant(&*inner.unsafe_body as *const _, 0));
                });
            },
            GrammarItem::NonTerminal { ident: nt, .. } => {
                // Regular field — non-binder context resets precedence
                if let Some(field_name_str) = regular_field_iter.next() {
                    let field_name = syn::Ident::new(field_name_str, proc_macro2::Span::call_site());
                    let nt_str = nt.to_string();
                    let task_variant = format_ident!("Display{}", nt_str);
                    forward_ops.push(quote! {
                        stack.push(DisplayTask::#task_variant(&**#field_name as *const _, 0));
                    });
                }
            },
            GrammarItem::Binder { .. } if i == *binder_idx => {
                // Binder name from scope
                forward_ops.push(quote! {
                    stack.push(DisplayTask::WriteString(binder_name.to_string()));
                });
            },
            GrammarItem::Binder { .. } => {},
            GrammarItem::Collection { .. } => {
                // Unlikely in binder rules, but handle gracefully
            },
        }
    }

    forward_ops.reverse();

    quote! {
        #category::#label(#(#field_idents),*) => {
            let inner = scope.inner();
            let binder_name = inner.unsafe_pattern.0.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_");
            #(#forward_ops)*
        }
    }
}

/// Generate arm for new-style syntax_pattern rules.
///
/// Precedence-aware: for infix/postfix/prefix operators, wraps the output in
/// parentheses when the inherited `min_bp` exceeds the operator's own binding power.
fn generate_engine_syntax_pattern_arm(
    rule: &GrammarRule,
    syntax_pattern: &[SyntaxExpr],
    term_context: &[TermParam],
    _language: &LanguageDef,
    bp_lookup: &BpLookup,
) -> TokenStream {
    let category = &rule.category;
    let label = &rule.label;
    let label_str = label.to_string();

    // Check if this rule is an infix/postfix/mixfix operator
    let infix_info = bp_lookup.infix.get(&label_str);
    // Check if this rule is a unary prefix operator
    let prefix_info = bp_lookup.prefix.get(&label_str);

    // W3 (Neg-zero display canonicalization): if this rule is a unary-prefix
    // `"-" a` operator over a numeric native-type category, we emit a runtime
    // pre-scan so that `Neg(…Neg(Zero)…)` renders the `a` portion without
    // the leading `-`. AST and evaluation are unchanged — Float specifically
    // retains its `-0.0` bit pattern; we just normalize the printed form.
    // Activated later in the `needs_bp_check` emission branch; here we only
    // build the pre-scan expression so the arm can reference it.
    let neg_zero_prescan: Option<TokenStream> = (|| {
        prefix_info?; // only unary-prefix rules
        if syntax_pattern.len() != 2 {
            return None;
        }
        let is_minus = matches!(
            syntax_pattern.first(),
            Some(SyntaxExpr::Literal(s)) if s == "-"
        );
        if !is_minus {
            return None;
        }
        let param_name = match syntax_pattern.get(1) {
            Some(SyntaxExpr::Param(id)) => id.to_string(),
            _ => return None,
        };
        // The unary param must be of this rule's own category (same-cat
        // negation), so the inner-variant pattern `#category::#label(inner)`
        // is well-typed for chain walking.
        let param_ty = term_context.iter().find_map(|p| match p {
            TermParam::Simple { name, ty } if name.to_string() == param_name => Some(ty),
            _ => None,
        })?;
        let TypeExpr::Base(param_cat) = param_ty else {
            return None;
        };
        if param_cat != category {
            return None;
        }
        let lang_type = _language.types.iter().find(|t| &t.name == param_cat)?;
        let native_type = lang_type.native_type.as_ref()?;
        use crate::gen::native::NativeType;
        let nt = NativeType::from_syn_type(native_type);
        let lit_label = generate_literal_label(native_type);
        let param_ident = syn::Ident::new(&param_name, proc_macro2::Span::call_site());

        // Per-type literal-zero test, applied inside the match arm that binds
        // `v` to the literal payload.
        // Use the canonical wrappers' inner accessors + `num_traits::Zero` on
        // the underlying value (the canonical types themselves don't impl Zero
        // — see `runtime/src/canonical_*.rs`). Float comes through as a value,
        // not a reference, so `==` against `0.0` covers both `+0.0` and `-0.0`
        // (which is exactly what we want — display canonicalization, not
        // bit-pattern preservation).
        let zero_check: TokenStream = match &nt {
            NativeType::Float32 | NativeType::Float64 => quote! { v.get() == 0.0 },
            NativeType::CanonicalBigRat => quote! {
                <num_rational::Ratio<num_bigint::BigInt> as num_traits::Zero>::is_zero(v.get())
            },
            NativeType::CanonicalFixedPoint => quote! {
                <num_bigint::BigInt as num_traits::Zero>::is_zero(v.unscaled())
            },
            NativeType::CanonicalBigInt => quote! {
                <num_bigint::BigInt as num_traits::Zero>::is_zero(v.get())
            },
            _ if nt.is_integer() => quote! { *v == 0 },
            _ => return None,
        };

        Some(quote! {
            {
                let mut cur: &#category = #param_ident.as_ref();
                loop {
                    match cur {
                        #category::#label(__neg_inner) => {
                            cur = __neg_inner.as_ref();
                        }
                        #category::#lit_label(v) => break #zero_check,
                        _ => break false,
                    }
                }
            }
        })
    })();

    // Analyze term_context to understand the structure
    let mut param_names: Vec<String> = Vec::new();
    let mut has_abstraction = false;
    let mut is_multi_binder = false;
    let mut abstraction_binder: Option<String> = None;
    let mut abstraction_body: Option<String> = None;
    // Map from param name -> TypeExpr for looking up category
    let mut param_types: HashMap<String, &TypeExpr> = HashMap::new();

    // Opt-Group: flatten the term context so inner params of `#opt(...)`
    // are visible to the display generator with the same name resolution
    // as top-level params. The display impl handles Option<T> wrapping
    // by emitting inner literals/params only when the Option is Some.
    fn flatten_params<'a>(params: &'a [TermParam], out: &mut Vec<&'a TermParam>) {
        for p in params {
            match p {
                TermParam::Optional { params: inner } => flatten_params(inner, out),
                _ => out.push(p),
            }
        }
    }
    let mut flat: Vec<&TermParam> = Vec::new();
    flatten_params(term_context, &mut flat);

    for param in flat {
        match param {
            TermParam::Simple { name, ty } => {
                param_names.push(name.to_string());
                param_types.insert(name.to_string(), ty);
            },
            TermParam::Abstraction { binder, body, ty: _ } => {
                has_abstraction = true;
                abstraction_binder = Some(binder.to_string());
                abstraction_body = Some(body.to_string());
                let _ = body;
            },
            TermParam::MultiAbstraction { binder, body, ty: _ } => {
                has_abstraction = true;
                is_multi_binder = true;
                abstraction_binder = Some(binder.to_string());
                abstraction_body = Some(body.to_string());
                let _ = body;
            },
            TermParam::GuardBody { name } => {
                // Phase 2E: register the guard slot's name so the
                // syntax pattern's reference resolves and the
                // per-instance BehavioralPred field is rendered.
                param_names.push(name.to_string());
            },
            TermParam::Optional { .. } => {
                // Already flattened — unreachable.
                unreachable!("Optional should have been flattened");
            },
        }
    }

    // Count non-terminal parameters for infix position tracking
    // For new-style syntax, params appearing in the syntax_pattern as base-category
    // types are the "operand" nonterminals.
    let base_cat_params: Vec<String> = param_names
        .iter()
        .filter(|name| {
            if let Some(ty) = param_types.get(name.as_str()) {
                matches!(ty, TypeExpr::Base(_))
            } else {
                false
            }
        })
        .cloned()
        .collect();
    let nt_count = base_cat_params.len();

    // Determine body category from the abstraction type for pushing tasks
    let body_cat_ident = if has_abstraction {
        // Find the abstraction's type and get the codomain
        let abs_type = term_context.iter().find_map(|p| match p {
            TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. } => Some(ty),
            _ => None,
        });
        if let Some(TypeExpr::Arrow { codomain, .. }) = abs_type {
            Some(extract_base_category_ident(codomain))
        } else {
            None
        }
    } else {
        None
    };

    // Compute a map from param name -> child min_bp for infix/prefix rules
    let child_bp_map: HashMap<String, u8> = if let Some(info) = infix_info {
        let mut map = HashMap::new();
        if info.is_cross_category {
            // Cross-category: children are in different category, reset BP
            for name in &base_cat_params {
                map.insert(name.clone(), 0u8);
            }
        } else if info.is_postfix {
            // Postfix: single operand gets left_bp
            if let Some(name) = base_cat_params.first() {
                map.insert(name.clone(), info.left_bp);
            }
        } else if info.is_mixfix {
            // Mixfix: first operand = left_bp, middle = 0, last = right_bp
            for (idx, name) in base_cat_params.iter().enumerate() {
                if idx == 0 {
                    map.insert(name.clone(), info.left_bp);
                } else if idx == nt_count - 1 {
                    map.insert(name.clone(), info.right_bp);
                } else {
                    map.insert(name.clone(), 0u8);
                }
            }
        } else {
            // Regular infix: first param = left_bp, second param = right_bp
            if let Some(name) = base_cat_params.first() {
                map.insert(name.clone(), info.left_bp);
            }
            if base_cat_params.len() >= 2 {
                map.insert(base_cat_params[1].clone(), info.right_bp);
            }
        }
        map
    } else if let Some(pinfo) = prefix_info {
        // Unary prefix: single operand gets prefix_bp
        let mut map = HashMap::new();
        if let Some(name) = base_cat_params.first() {
            map.insert(name.clone(), pinfo.prefix_bp);
        }
        map
    } else {
        HashMap::new()
    };

    // Build forward push operations from syntax_pattern
    let mut forward_ops: Vec<TokenStream> = Vec::new();

    for (i, expr) in syntax_pattern.iter().enumerate() {
        match expr {
            SyntaxExpr::Literal(s) => {
                let next_param = syntax_pattern
                    .get(i + 1)
                    .map(|e| matches!(e, SyntaxExpr::Param(_)));
                let prev_param =
                    i > 0 && matches!(syntax_pattern.get(i - 1), Some(SyntaxExpr::Param(_)));
                // Stage 3.3 (2026-04-30): broaden `is_word` to mirror the
                // lexer's keyword-recognition rule
                // (`prattail/src/lexer.rs:523`): `is_alphanumeric() || '_'`,
                // not just `is_alphabetic()`. A literal like `"r2d2"` IS an
                // identifier-like keyword to the lexer; failing to space it
                // from adjacent ident-char text would re-lex into a single
                // glommed Ident. Guard against empty literals (vacuously
                // true) and digit-leading literals (those parse as Integer,
                // not as keywords).
                let is_word = !s.is_empty()
                    && s.chars().all(|c| c.is_alphanumeric() || c == '_')
                    && !s.chars().next().unwrap().is_numeric();
                let (prefix, suffix) = if prev_param && next_param.unwrap_or(false) {
                    (" ", " ")
                } else if next_param == Some(true) && is_word {
                    ("", " ")
                } else {
                    ("", "")
                };
                let raw = format!("{}{}{}", prefix, s, suffix);
                forward_ops.push(quote! {
                    stack.push(DisplayTask::WriteString(#raw.to_string()));
                });
            },
            SyntaxExpr::Param(id) => {
                let name = id.to_string();

                if Some(&name) == abstraction_binder.as_ref() {
                    // Binder name from scope.unbind()
                    forward_ops.push(quote! {
                        stack.push(DisplayTask::WriteString(binder_name.to_string()));
                    });
                } else if Some(&name) == abstraction_body.as_ref() {
                    // Body from scope.inner() — binder body resets precedence
                    if let Some(ref body_cat) = body_cat_ident {
                        let task_variant = format_ident!("Display{}", body_cat);
                        forward_ops.push(quote! {
                            stack.push(DisplayTask::#task_variant(&*inner.unsafe_body as *const _, 0));
                        });
                    } else {
                        // Fallback: format to string
                        forward_ops.push(quote! {
                            stack.push(DisplayTask::WriteString(format!("{}", body)));
                        });
                    }
                } else {
                    // Simple parameter - determine its category and push task
                    let field_ident = syn::Ident::new(&name, proc_macro2::Span::call_site());
                    let child_bp = child_bp_map.get(&name).copied().unwrap_or(0u8);
                    if let Some(ty) = param_types.get(&name) {
                        match ty {
                            TypeExpr::Base(cat_ident) => {
                                let task_variant = format_ident!("Display{}", cat_ident);
                                forward_ops.push(quote! {
                                    stack.push(DisplayTask::#task_variant(&**#field_ident as *const _, #child_bp));
                                });
                            },
                            TypeExpr::Collection { .. } => {
                                // Collection param without #sep - format inline
                                forward_ops.push(quote! {
                                    stack.push(DisplayTask::WriteString(format!("{}", #field_ident)));
                                });
                            },
                            _ => {
                                forward_ops.push(quote! {
                                    stack.push(DisplayTask::WriteString(format!("{}", #field_ident)));
                                });
                            },
                        }
                    } else {
                        forward_ops.push(quote! {
                            stack.push(DisplayTask::WriteString(format!("{}", #field_ident)));
                        });
                    }
                }
            },
            SyntaxExpr::Op(op) => {
                // Stage 3.3 (2026-04-30): pass outer-adjacent Param flags so
                // PatternOp::Opt can apply the same word-literal spacing rules
                // the outer SyntaxExpr::Literal arm uses. Without this, an
                // optional group like `*opt("else" e)` placed after a Param
                // emits `<param><else>` with no separator → re-lex glomming
                // into Ident("<value>else").
                let prev_outer_is_param = i > 0
                    && matches!(syntax_pattern.get(i - 1), Some(SyntaxExpr::Param(_)));
                let next_outer_is_param = matches!(
                    syntax_pattern.get(i + 1),
                    Some(SyntaxExpr::Param(_))
                );
                let op_code = generate_engine_pattern_op(
                    op,
                    &abstraction_binder,
                    &abstraction_body,
                    &body_cat_ident,
                    &param_types,
                    prev_outer_is_param,
                    next_outer_is_param,
                );
                forward_ops.push(op_code);
            },
        }
    }

    // Reverse so stack processes left-to-right
    forward_ops.reverse();

    // Build field pattern
    let mut field_idents: Vec<syn::Ident> = param_names
        .iter()
        .map(|name| syn::Ident::new(name, proc_macro2::Span::call_site()))
        .collect();

    // Determine if we need parenthesization wrapping
    let needs_bp_check = infix_info.is_some() || prefix_info.is_some();
    let own_bp: u8 = if let Some(info) = infix_info {
        info.left_bp
    } else if let Some(pinfo) = prefix_info {
        pinfo.prefix_bp
    } else {
        0
    };

    {
        use std::io::Write;
    }

    if has_abstraction {
        field_idents.push(syn::Ident::new("scope", proc_macro2::Span::call_site()));

        if is_multi_binder {
            // Abstraction rules are never infix, no parenthesization needed
            quote! {
                #category::#label(#(#field_idents),*) => {
                    let inner = scope.inner();
                    let binder_names: Vec<String> = inner.unsafe_pattern.iter()
                        .map(|b| b.0.pretty_name.as_ref().map(|s| s.to_string()).unwrap_or_else(|| "_".to_string()))
                        .collect();
                    // For multi-binder, binder_name is the joined list (used by some ops)
                    let binder_name = binder_names.join(",");
                    #(#forward_ops)*
                }
            }
        } else {
            // Abstraction rules are never infix, no parenthesization needed
            quote! {
                #category::#label(#(#field_idents),*) => {
                    let inner = scope.inner();
                    let binder_name = inner.unsafe_pattern.0.pretty_name.as_ref().map(|s| s.as_str()).unwrap_or("_");
                    #(#forward_ops)*
                }
            }
        }
    } else if field_idents.is_empty() {
        quote! {
            #category::#label => {
                #(#forward_ops)*
            }
        }
    } else if needs_bp_check {
        if let Some(prescan) = neg_zero_prescan {
            // W3: Neg-zero display canonicalization.
            //
            // `forward_ops` was built left-to-right as [push("-"), push(child)]
            // then reversed to [push(child), push("-")] (pop-order = child,
            // then "-"). To suppress the "-" push when `__neg_zero` is true,
            // we split `forward_ops` by position. `forward_ops[0]` is the
            // child push (from the param); `forward_ops[1]` is the "-" push
            // (from the literal). Only emit the latter when not a zero chain.
            //
            // (Unreversed, syntax_pattern is ["-", param] → forward_ops before
            // reverse is [push("-"), push(param)]; after reverse the first
            // element emitted is the param push, second is the "-" push. We
            // gate the "-" push emission on `!__neg_zero`.)
            let (child_push, minus_push) = if forward_ops.len() == 2 {
                (forward_ops[0].clone(), forward_ops[1].clone())
            } else {
                // Unexpected shape; fall back to default emission.
                return quote! {
                    #category::#label(#(#field_idents),*) => {
                        let needs_parens = #own_bp < min_bp;
                        if needs_parens {
                            stack.push(DisplayTask::WriteLiteral(")"));
                        }
                        #(#forward_ops)*
                        if needs_parens {
                            stack.push(DisplayTask::WriteLiteral("("));
                        }
                    }
                };
            };
            quote! {
                #category::#label(#(#field_idents),*) => {
                    let needs_parens = #own_bp < min_bp;
                    let __neg_zero: bool = #prescan;
                    if needs_parens {
                        stack.push(DisplayTask::WriteLiteral(")"));
                    }
                    #child_push
                    if !__neg_zero {
                        #minus_push
                    }
                    if needs_parens {
                        stack.push(DisplayTask::WriteLiteral("("));
                    }
                }
            }
        } else {
            quote! {
                #category::#label(#(#field_idents),*) => {
                    let needs_parens = #own_bp < min_bp;
                    if needs_parens {
                        stack.push(DisplayTask::WriteLiteral(")"));
                    }
                    #(#forward_ops)*
                    if needs_parens {
                        stack.push(DisplayTask::WriteLiteral("("));
                    }
                }
            }
        }
    } else {
        quote! {
            #category::#label(#(#field_idents),*) => {
                #(#forward_ops)*
            }
        }
    }
}

/// Generate push operations for a pattern operation (Sep, Var, Opt, etc.)
/// These produce inline write-to-formatter code (since they involve loops/conditionals
/// that don't recurse deeply) and push the result as a WriteString.
///
/// `prev_outer_is_param` / `next_outer_is_param` (Stage 3.3, 2026-04-30):
/// whether the immediately-adjacent OUTER syntax-pattern position is a
/// `SyntaxExpr::Param`. Used by `PatternOp::Opt` to embed leading/trailing
/// spaces in its emitted `result` string when its first/last inner element
/// is a word-literal abutting an outer Param. The space MUST be embedded
/// (not pushed as a separate `WriteLiteral` task) so it's atomically gated
/// on the optional-group's Some/None discriminant — emitting outer-side
/// would produce trailing whitespace when the group is absent.
fn generate_engine_pattern_op(
    op: &PatternOp,
    abstraction_binder: &Option<String>,
    _abstraction_body: &Option<String>,
    _body_cat_ident: &Option<syn::Ident>,
    param_types: &HashMap<String, &TypeExpr>,
    prev_outer_is_param: bool,
    next_outer_is_param: bool,
) -> TokenStream {
    // Sep / Var ignore the outer flags; their emission already produces
    // self-contained spacing or atomic ident formatting.
    let _ = (prev_outer_is_param, next_outer_is_param);
    match op {
        PatternOp::Sep { collection, separator, source } => {
            if let Some(chain_source) = source {
                return generate_engine_chained_sep(chain_source, separator);
            }
            let coll_name = collection.to_string();
            let sep_with_spaces = format!(" {} ", separator);

            if abstraction_binder.as_ref().map(|s| s.as_str()) == Some(&coll_name) {
                // Iterate binder_names
                quote! {
                    {
                        let mut parts = Vec::new();
                        for name in &binder_names {
                            parts.push(name.clone());
                        }
                        stack.push(DisplayTask::WriteString(parts.join(#sep_with_spaces)));
                    }
                }
            } else {
                // B9 / Class 2 (2026-05-08): branch on the collection
                // param's coll_type. Vec yields bare elements; HashBag/
                // HashSet yield (elem, count) tuples (HashBag has count >= 1,
                // HashSet count == 1 by construction). Pre-B9 the
                // unconditional (item, count) iteration assumed HashBag,
                // breaking Class-5 Vec collections AND Class-2 binder-rule
                // Vec collection slots (the smoke test's `qs:Vec(Proc)`).
                let coll_kind = param_types.get(&coll_name).and_then(|ty| {
                    if let TypeExpr::Collection { coll_type, .. } = ty {
                        Some(coll_type.clone())
                    } else {
                        None
                    }
                });
                let coll_ident = syn::Ident::new(&coll_name, proc_macro2::Span::call_site());
                let iter_body = match coll_kind {
                    Some(mettail_ast::types::CollectionType::Vec) => quote! {
                        for item in #coll_ident.iter() {
                            parts.push(item.to_string());
                        }
                        // Vec preserves insertion order — no sort.
                    },
                    Some(mettail_ast::types::CollectionType::HashSet) => quote! {
                        for item in #coll_ident.iter() {
                            parts.push(item.to_string());
                        }
                        parts.sort();
                    },
                    Some(mettail_ast::types::CollectionType::HashMap) => quote! {
                        // HashMap: pair-wise iteration — defensive; pilot
                        // grammars do not exercise HashMap-in-binder.
                        for (k, v) in #coll_ident.iter() {
                            parts.push(format!("{} : {}", k, v));
                        }
                        parts.sort();
                    },
                    // Default (HashBag or unknown): preserve pre-B9 behavior.
                    Some(mettail_ast::types::CollectionType::HashBag) | None => quote! {
                        for (item, count) in #coll_ident.iter() {
                            for _ in 0..count {
                                parts.push(item.to_string());
                            }
                        }
                        parts.sort();
                    },
                };
                quote! {
                    {
                        let mut parts = Vec::new();
                        #iter_body
                        stack.push(DisplayTask::WriteString(parts.join(#sep_with_spaces)));
                    }
                }
            }
        },
        PatternOp::Var(id) => {
            let ident = syn::Ident::new(&id.to_string(), proc_macro2::Span::call_site());
            quote! {
                stack.push(DisplayTask::WriteString(format!("{}", #ident)));
            }
        },
        PatternOp::Opt { inner } => {
            // Opt-Group: emit the inner segment GATED on the first
            // Param's `is_some()`. By WPDS Opt-Group invariant, all
            // inner Param fields share the same Some/None fate (the
            // walker's optional-scope finalize/skip is atomic). Gating
            // on the first Param's discriminant suffices.
            //
            // Inside the gated block, each inner Param's variant field
            // is `Option<Box<Cat>>`; rebind to `&Cat` via
            // `unwrap_or_unchecked`-style on `as_ref().unwrap()` (safe
            // because the gating ensures Some).
            // Phase 4 #3 (2026-05-12): gating_ident now also considers
            // Op(Sep) — its `collection` param is the gating signal
            // (Option<Vec<T>> / Option<HashBag<T>> / etc.). The first
            // inner Param OR Sep-collection-param wins.
            let gating_ident: Option<syn::Ident> = inner.iter().find_map(|expr| {
                match expr {
                    SyntaxExpr::Param(id) => Some(syn::Ident::new(
                        &id.to_string(), proc_macro2::Span::call_site(),
                    )),
                    SyntaxExpr::Op(PatternOp::Sep { collection, source: None, .. }) => {
                        Some(syn::Ident::new(
                            &collection.to_string(), proc_macro2::Span::call_site(),
                        ))
                    }
                    _ => None,
                }
            });
            let inner_bindings: Vec<TokenStream> = inner.iter().filter_map(|expr| {
                match expr {
                    SyntaxExpr::Param(id) => {
                        let id_ident = syn::Ident::new(&id.to_string(), proc_macro2::Span::call_site());
                        let inner_var = quote::format_ident!("__opt_{}", id);
                        Some(quote! {
                            let #inner_var: &_ = #id_ident.as_ref()
                                .map(|__b| __b.as_ref())
                                .expect("Opt-Group: inner display ran with None");
                        })
                    }
                    // Phase 4 #3 (2026-05-12): bind the Sep collection param
                    // to a reference of the inner Vec/HashBag/etc. The field
                    // type is `Option<Container<T>>` (no Box), so as_ref()
                    // gives &Container<T> directly.
                    SyntaxExpr::Op(PatternOp::Sep { collection, source: None, .. }) => {
                        let id_ident = syn::Ident::new(&collection.to_string(), proc_macro2::Span::call_site());
                        let inner_var = quote::format_ident!("__opt_{}", collection);
                        Some(quote! {
                            let #inner_var = #id_ident.as_ref()
                                .expect("Opt-Group: inner display ran with None");
                        })
                    }
                    _ => None,
                }
            }).collect();
            // Stage 3.3 (2026-04-30): mirror the outer SyntaxExpr::Literal
            // spacing heuristic for inner positions, plus inject leading /
            // trailing spaces at inner edges when the OUTER neighbour is a
            // Param. This guarantees the Display→Parse roundtrip for any
            // optional-group position whose word-literals would otherwise
            // glom together with adjacent Param-formatted text under the
            // lexer's maximal-munch keyword recognition.
            //
            // Rules (per inner index `j`):
            //  * `is_word`: same lexer-aligned predicate as the outer arm —
            //    non-empty, ident-class chars only, non-numeric leading.
            //  * `inner_3case_force`: when the inner position is between two
            //    Params, force `(" ", " ")` — matches outer behaviour for
            //    `["a", "+", "b"]` shapes.
            //  * Leading-space sources: (a) inner-prev is a Param + is_word;
            //    (b) is_first AND outer-prev is a Param + is_word;
            //    (c) inner_3case_force.
            //  * Trailing-space sources: (a) is_word AND any inner-next exists
            //    (covers Lit→Lit-word AND Lit→Param);
            //    (b) is_last AND outer-next is a Param + is_word;
            //    (c) inner_3case_force.
            //  * Param at inner-edge with outer-adjacent Param: emit an
            //    explicit `result.push_str(" ");` because Param widths are
            //    unbounded and adjacency would re-lex into a single token.
            //  * Nested Op inside Opt: emit `compile_error!` — the parser side
            //    rejects this construction at `binder.rs:347`, so the Display
            //    side must as well, surfaced at language! macro expansion.
            let inner_parts: Vec<TokenStream> = inner
                .iter()
                .enumerate()
                .map(|(j, expr)| {
                    let inner_prev_is_param = j > 0
                        && matches!(inner.get(j - 1), Some(SyntaxExpr::Param(_)));
                    let inner_next_is_param = inner
                        .get(j + 1)
                        .map(|e| matches!(e, SyntaxExpr::Param(_)));
                    let is_first = j == 0;
                    let is_last = j + 1 == inner.len();
                    match expr {
                        SyntaxExpr::Literal(s) => {
                            let is_word = !s.is_empty()
                                && s.chars().all(|c| c.is_alphanumeric() || c == '_')
                                && !s.chars().next().unwrap().is_numeric();
                            let inner_3case_force = inner_prev_is_param
                                && inner_next_is_param.unwrap_or(false);
                            let need_prefix = (inner_prev_is_param && is_word)
                                || (is_first && prev_outer_is_param && is_word)
                                || inner_3case_force;
                            let need_suffix = (is_word && !is_last)
                                || (is_last && next_outer_is_param && is_word)
                                || inner_3case_force;
                            let prefix = if need_prefix { " " } else { "" };
                            let suffix = if need_suffix { " " } else { "" };
                            let raw = format!("{}{}{}", prefix, s, suffix);
                            quote! { result.push_str(#raw); }
                        },
                        SyntaxExpr::Param(id) => {
                            let inner_var = quote::format_ident!("__opt_{}", id);
                            let leading = if is_first && prev_outer_is_param {
                                quote! { result.push_str(" "); }
                            } else {
                                quote! {}
                            };
                            let trailing = if is_last && next_outer_is_param {
                                quote! { result.push_str(" "); }
                            } else {
                                quote! {}
                            };
                            quote! {
                                #leading
                                result.push_str(&format!("{}", #inner_var));
                                #trailing
                            }
                        },
                        SyntaxExpr::Op(PatternOp::Sep {
                            collection,
                            separator,
                            source: None,
                        }) => {
                            // Phase 4 #3 (2026-05-12): Sep inside *opt.
                            // Iterate `__opt_<coll_name>` joining elements
                            // with the separator. The container's coll_kind
                            // determines iteration shape: Vec yields bare
                            // elements; HashBag yields (item, count);
                            // HashSet yields bare elements (and sorts);
                            // HashMap yields (k, v) pair-wise.
                            let inner_var = quote::format_ident!("__opt_{}", collection);
                            let coll_name = collection.to_string();
                            let sep_with_spaces = format!(" {} ", separator);
                            let coll_kind = param_types.get(&coll_name).and_then(|ty| {
                                if let TypeExpr::Collection { coll_type, .. } = ty {
                                    Some(coll_type.clone())
                                } else {
                                    None
                                }
                            });
                            let iter_body = match coll_kind {
                                Some(mettail_ast::types::CollectionType::Vec) => quote! {
                                    for item in #inner_var.iter() {
                                        parts.push(item.to_string());
                                    }
                                },
                                Some(mettail_ast::types::CollectionType::HashSet) => quote! {
                                    for item in #inner_var.iter() {
                                        parts.push(item.to_string());
                                    }
                                    parts.sort();
                                },
                                Some(mettail_ast::types::CollectionType::HashMap) => quote! {
                                    for (k, v) in #inner_var.iter() {
                                        parts.push(format!("{} : {}", k, v));
                                    }
                                    parts.sort();
                                },
                                Some(mettail_ast::types::CollectionType::HashBag) | None => quote! {
                                    for (item, count) in #inner_var.iter() {
                                        for _ in 0..count {
                                            parts.push(item.to_string());
                                        }
                                    }
                                    parts.sort();
                                },
                            };
                            quote! {
                                {
                                    let mut parts: Vec<String> = Vec::new();
                                    #iter_body
                                    result.push_str(&parts.join(#sep_with_spaces));
                                }
                            }
                        },
                        SyntaxExpr::Op(_inner_op) => {
                            // Other nested PatternOps (Zip, Map, Var, Opt) inside
                            // *opt are out of pilot scope. The WPDS binder
                            // classifier returns None for these.
                            quote! {
                                compile_error!(
                                    "nested non-Sep PatternOp inside #opt(...) is \
                                     not supported. Rewrite the grammar to \
                                     flatten the inner ops, or open an issue if \
                                     your grammar genuinely needs nested \
                                     optionality with Zip/Map/Var/Opt."
                                );
                            }
                        },
                    }
                })
                .collect();
            if let Some(gating) = gating_ident {
                quote! {
                    {
                        if #gating.is_some() {
                            let mut result = String::new();
                            #(#inner_bindings)*
                            #(#inner_parts)*
                            stack.push(DisplayTask::WriteString(result));
                        }
                    }
                }
            } else {
                // No Param inside the optional — emit unconditional
                // (literal-only optional groups are unusual but valid).
                quote! {
                    {
                        let mut result = String::new();
                        #(#inner_parts)*
                        stack.push(DisplayTask::WriteString(result));
                    }
                }
            }
        },
        PatternOp::Zip { .. } | PatternOp::Map { .. } => {
            quote! { /* zip/map should be chained with #sep */ }
        },
    }
}

/// Generate engine code for chained #zip().#map().#sep() pattern
fn generate_engine_chained_sep(source: &PatternOp, separator: &str) -> TokenStream {
    if let PatternOp::Map { source: map_source, params, body } = source {
        if let PatternOp::Zip { left, .. } = map_source.as_ref() {
            let left_name = left.to_string();
            let left_ident = syn::Ident::new(&left_name, proc_macro2::Span::call_site());

            let format_code = generate_engine_map_body_format(params, body);
            let sep_str = format!("{} ", separator);

            return quote! {
                {
                    let mut parts = Vec::new();
                    for (i, item) in #left_ident.iter().enumerate() {
                        let binder_name = binder_names.get(i).map(|s| s.as_str()).unwrap_or("_");
                        let mut part = String::new();
                        #format_code
                        parts.push(part);
                    }
                    parts.sort();
                    stack.push(DisplayTask::WriteString(parts.join(#sep_str)));
                }
            };
        }
    }
    quote! { /* unhandled chained pattern */ }
}

/// Generate format code from map body for the engine (builds into `part` String)
fn generate_engine_map_body_format(params: &[syn::Ident], body: &[SyntaxExpr]) -> TokenStream {
    let mut format_parts: Vec<TokenStream> = Vec::new();

    for expr in body {
        match expr {
            SyntaxExpr::Literal(s) => {
                format_parts.push(quote! { part.push_str(#s); });
            },
            SyntaxExpr::Param(id) => {
                let id_str = id.to_string();
                if params.len() >= 2 {
                    let first_param = params[0].to_string();
                    let second_param = params[1].to_string();

                    if id_str == first_param {
                        format_parts.push(quote! { part.push_str(&format!("{}", item)); });
                    } else if id_str == second_param {
                        format_parts.push(quote! { part.push_str(binder_name); });
                    } else {
                        let ident = syn::Ident::new(&id_str, proc_macro2::Span::call_site());
                        format_parts.push(quote! { part.push_str(&format!("{}", #ident)); });
                    }
                } else if params.len() == 1 && id.to_string() == params[0].to_string() {
                    format_parts.push(quote! { part.push_str(&format!("{}", item)); });
                } else {
                    let ident = syn::Ident::new(&id_str, proc_macro2::Span::call_site());
                    format_parts.push(quote! { part.push_str(&format!("{}", #ident)); });
                }
            },
            SyntaxExpr::Op(_) => {},
        }
    }

    quote! { #(#format_parts)* }
}

// =============================================================================
// Auto-generated Variant Arms
// =============================================================================

/// Generate engine arm for auto-generated Var variant.
fn generate_engine_auto_var_arm(category: &syn::Ident) -> TokenStream {
    let var_label = generate_var_label(category);

    quote! {
        #category::#var_label(var) => {
            let name = match &var.0 {
                mettail_runtime::Var::Free(fv) => {
                    fv.pretty_name.as_ref().map(|s| s.to_string()).unwrap_or_else(|| "_".to_string())
                }
                mettail_runtime::Var::Bound(bv) => {
                    bv.pretty_name.as_ref().map(|s| s.to_string()).unwrap_or_else(|| "_".to_string())
                }
            };
            stack.push(DisplayTask::WriteString(name));
        }
    }
}

/// Extract the VALUE type Ident from a two-arg collection native type
/// (e.g. `HashMap<K, V>` → `Some(V)`, `HashMapLit<K, V>` → `Some(V)`).
/// Returns None for one-arg collections (Vec, HashBag, HashSet).
fn extract_map_value_ident(native_type: &syn::Type) -> Option<syn::Ident> {
    use syn::GenericArgument;
    let path = match native_type {
        syn::Type::Path(t) => &t.path,
        _ => return None,
    };
    let segment = path.segments.last()?;
    let args = match &segment.arguments {
        syn::PathArguments::AngleBracketed(a) => &a.args,
        _ => return None,
    };
    // Need at least 2 args for a key-value map.
    if args.len() < 2 {
        return None;
    }
    let second = args.iter().nth(1)?;
    match second {
        GenericArgument::Type(syn::Type::Path(t)) => t
            .path
            .get_ident()
            .cloned()
            .or_else(|| t.path.segments.last().map(|s| s.ident.clone())),
        _ => None,
    }
}

/// Generate engine arm for auto-generated literal variant (NumLit, FloatLit, etc.)
fn generate_engine_auto_literal_arm(
    category: &syn::Ident,
    native_type: &syn::Type,
    collection_kind: Option<&mettail_ast::language::CollectionCategory>,
) -> TokenStream {
    let literal_label = generate_literal_label(native_type);
    let nt = crate::gen::native::NativeType::from_syn_type(native_type);

    if nt.is_string() {
        quote! {
            #category::#literal_label(v) => {
                stack.push(DisplayTask::WriteString(
                    format!("\"{}\"", v.replace('\"', "\\\""))
                ));
            }
        }
    } else if nt.is_collection() {
        // Collection payloads. Wrap with the keyword prefix from
        // `CollectionDelimiters` (default: `list(`, `bag(`, `map(`) so
        // Display → parse roundtrip holds. Without this wrapping the
        // generated parser's auto-synthesized `ListLit`/`BagLit`/`MapLit`
        // rules would reject the Display output.
        let (open, close, sep, kv_sep): (String, String, String, Option<String>) =
            match collection_kind {
                Some(mettail_ast::language::CollectionCategory::List(d))
                | Some(mettail_ast::language::CollectionCategory::Bag(d))
                | Some(mettail_ast::language::CollectionCategory::Map(d)) => (
                    d.open.clone(),
                    d.close.clone(),
                    d.sep.clone(),
                    d.key_val_sep.clone(),
                ),
                None => ("".to_string(), "".to_string(), ", ".to_string(), None),
            };
        // Extract the element category (e.g. Vec<Proc> → Proc). Every
        // element gets pushed as a DisplayTask::Display<ElemCat> onto the
        // OUTER display stack — we STAY inside the single iterative Display
        // context instead of calling `write!(s, "{}", item)` which re-enters
        // `display_iterative` (CPU-stack-deep on nested collections). Stack-
        // safety invariant.
        let elem_ident = crate::gen::native::native_type_element_ident(native_type);
        // HashMap<K,V> / HashMapLit<K,V> take TWO generic args; extract V
        // separately. For K we still use the first generic arg (same as
        // element extraction), since HashMap's "element" concept is
        // key+value pair.
        let value_ident = extract_map_value_ident(native_type);
        let elem_display_task = elem_ident
            .as_ref()
            .map(|c| format_ident!("Display{}", c));
        let value_display_task = value_ident
            .as_ref()
            .map(|c| format_ident!("Display{}", c));

        match nt {
            crate::gen::native::NativeType::VecCollection => {
                let Some(elem_task) = elem_display_task.clone() else {
                    // Fallback for unknown element category — keep old
                    // behavior (stack-unsafe, but at least compiles).
                    return quote! {
                        #category::#literal_label(v) => {
                            use std::fmt::Write as _;
                            let mut s = String::from(#open);
                            for (i, item) in v.iter().enumerate() {
                                if i > 0 { s.push_str(#sep); s.push(' '); }
                                let _ = write!(s, "{}", item);
                            }
                            s.push_str(#close);
                            stack.push(DisplayTask::WriteString(s));
                        }
                    };
                };
                let sep_with_space = format!("{} ", sep);
                quote! {
                    #category::#literal_label(v) => {
                        // Push in reverse order so the first element is
                        // popped (and displayed) first: open, elem0, sep,
                        // elem1, sep, ..., elemN, close.
                        stack.push(DisplayTask::WriteString(#close.to_string()));
                        for (i, item) in v.iter().enumerate().rev() {
                            stack.push(DisplayTask::#elem_task(item as *const _, 0u8));
                            if i > 0 {
                                stack.push(DisplayTask::WriteString(#sep_with_space.to_string()));
                            }
                        }
                        stack.push(DisplayTask::WriteString(#open.to_string()));
                    }
                }
            }
            crate::gen::native::NativeType::HashMapCollection
            | crate::gen::native::NativeType::HashMapLitCollection => {
                let kv = kv_sep.unwrap_or_else(|| ":".to_string());
                let (Some(key_task), Some(val_task)) = (elem_display_task.clone(), value_display_task.clone()) else {
                    return quote! {
                        #category::#literal_label(v) => {
                            use std::fmt::Write as _;
                            let mut s = String::from(#open);
                            let mut entries: Vec<_> = v.iter().collect();
                            entries.sort_by(|a, b| format!("{}", a.0).cmp(&format!("{}", b.0)));
                            for (i, (k, val)) in entries.iter().enumerate() {
                                if i > 0 { s.push_str(#sep); s.push(' '); }
                                let _ = write!(s, "{}{}{}", k, #kv, val);
                            }
                            s.push_str(#close);
                            stack.push(DisplayTask::WriteString(s));
                        }
                    };
                };
                let sep_with_space = format!("{} ", sep);
                // Box the keys/vals so sorting doesn't move addresses we
                // reference via pointers. Sort by formatted key (stable
                // display order), then push Display tasks in reverse.
                quote! {
                    #category::#literal_label(v) => {
                        let mut entries: Vec<_> = v.iter().collect();
                        entries.sort_by(|a, b| format!("{}", a.0).cmp(&format!("{}", b.0)));
                        // The entries Vec holds REFERENCES into v's storage,
                        // so addresses inside v are stable across sort.
                        stack.push(DisplayTask::WriteString(#close.to_string()));
                        for (i, (k, val)) in entries.iter().enumerate().rev() {
                            stack.push(DisplayTask::#val_task(*val as *const _, 0u8));
                            stack.push(DisplayTask::WriteLiteral(#kv));
                            stack.push(DisplayTask::#key_task(*k as *const _, 0u8));
                            if i > 0 {
                                stack.push(DisplayTask::WriteString(#sep_with_space.to_string()));
                            }
                        }
                        stack.push(DisplayTask::WriteString(#open.to_string()));
                    }
                }
            }
            crate::gen::native::NativeType::HashBagCollection => {
                let Some(elem_task) = elem_display_task.clone() else {
                    return quote! {
                        #category::#literal_label(v) => {
                            use std::fmt::Write as _;
                            let mut s = String::from(#open);
                            let mut entries: Vec<_> = v.iter().collect();
                            entries.sort_by(|a, b| format!("{}", a.0).cmp(&format!("{}", b.0)));
                            let mut first = true;
                            for (item, count) in entries {
                                for _ in 0..count {
                                    if !first { s.push_str(#sep); s.push(' '); }
                                    first = false;
                                    let _ = write!(s, "{}", item);
                                }
                            }
                            s.push_str(#close);
                            stack.push(DisplayTask::WriteString(s));
                        }
                    };
                };
                let sep_with_space = format!("{} ", sep);
                quote! {
                    #category::#literal_label(v) => {
                        let mut entries: Vec<_> = v.iter().collect();
                        entries.sort_by(|a, b| format!("{}", a.0).cmp(&format!("{}", b.0)));
                        // Materialize (item_ptr, count) tuples, then flatten
                        // to a Vec of item_ptrs for uniform display. The
                        // `entries` Vec holds refs into v's storage; we
                        // convert to raw pointers before flattening.
                        let mut flat: Vec<*const _> = Vec::new();
                        for (item, count) in entries {
                            for _ in 0..count {
                                flat.push(item as *const _);
                            }
                        }
                        stack.push(DisplayTask::WriteString(#close.to_string()));
                        for (i, ptr) in flat.iter().enumerate().rev() {
                            stack.push(DisplayTask::#elem_task(*ptr, 0u8));
                            if i > 0 {
                                stack.push(DisplayTask::WriteString(#sep_with_space.to_string()));
                            }
                        }
                        stack.push(DisplayTask::WriteString(#open.to_string()));
                    }
                }
            }
            crate::gen::native::NativeType::HashSetCollection => {
                let Some(elem_task) = elem_display_task.clone() else {
                    return quote! {
                        #category::#literal_label(v) => {
                            use std::fmt::Write as _;
                            let mut s = String::from(#open);
                            let mut entries: Vec<_> = v.iter().collect();
                            entries.sort_by(|a, b| format!("{}", a).cmp(&format!("{}", b)));
                            for (i, item) in entries.iter().enumerate() {
                                if i > 0 { s.push_str(#sep); s.push(' '); }
                                let _ = write!(s, "{}", item);
                            }
                            s.push_str(#close);
                            stack.push(DisplayTask::WriteString(s));
                        }
                    };
                };
                let sep_with_space = format!("{} ", sep);
                quote! {
                    #category::#literal_label(v) => {
                        let mut entries: Vec<_> = v.iter().collect();
                        entries.sort_by(|a, b| format!("{}", a).cmp(&format!("{}", b)));
                        stack.push(DisplayTask::WriteString(#close.to_string()));
                        for (i, item) in entries.iter().enumerate().rev() {
                            stack.push(DisplayTask::#elem_task(*item as *const _, 0u8));
                            if i > 0 {
                                stack.push(DisplayTask::WriteString(#sep_with_space.to_string()));
                            }
                        }
                        stack.push(DisplayTask::WriteString(#open.to_string()));
                    }
                }
            }
            _ => quote! {
                // Fallback for any other collection native type — use Display impl.
                #category::#literal_label(v) => {
                    stack.push(DisplayTask::WriteString(format!("{}", v)));
                }
            },
        }
    } else {
        // Bare value display for all numeric types (matches main). Suffixes
        // like `n` / `r` / `u32` / `i32` are accepted at parse via optional
        // regex fragments and explicit tokens, not required in display.
        quote! {
            #category::#literal_label(v) => {
                stack.push(DisplayTask::WriteString(format!("{}", v)));
            }
        }
    }
}

// =============================================================================
// Display Impl Generation (delegates to iterative engine)
// =============================================================================

/// Generate `impl Display for Cat` blocks that delegate to the iterative engine.
fn generate_display_impls(language: &LanguageDef) -> TokenStream {
    let impls: Vec<TokenStream> = language
        .types
        .iter()
        .map(|lang_type| {
            let cat = &lang_type.name;
            let task_variant = format_ident!("Display{}", cat);

            quote! {
                impl std::fmt::Display for #cat {
                    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                        // Use try_with to avoid double-panic when Display is called
                        // during panic unwinding (e.g., proptest error formatting).
                        // Falls back to a fresh local stack if TLS is unavailable.
                        let result = DISPLAY_TASK_POOL.try_with(|cell| {
                            let mut stack = cell.take();
                            stack.clear();
                            stack.push(DisplayTask::#task_variant(self as *const #cat, 0));
                            let result = display_iterative(&mut stack, f);
                            cell.set(stack);
                            result
                        });
                        match result {
                            Ok(fmt_result) => fmt_result,
                            Err(_) => {
                                // TLS unavailable (thread shutdown or panic unwinding).
                                let mut stack = Vec::new();
                                stack.push(DisplayTask::#task_variant(self as *const #cat, 0));
                                display_iterative(&mut stack, f)
                            }
                        }
                    }
                }
            }
        })
        .collect();

    quote! {
        #(#impls)*
    }
}

// =============================================================================
// Helper Functions
// =============================================================================

/// Format just the terminals for a unit variant
fn format_terminals(rule: &GrammarRule) -> String {
    rule.items
        .iter()
        .filter_map(|item| match item {
            GrammarItem::Terminal(term) => Some(term.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join("")
}

/// Extract base category identifier from a TypeExpr
fn extract_base_category_ident(ty: &TypeExpr) -> syn::Ident {
    match ty {
        TypeExpr::Base(ident) => ident.clone(),
        TypeExpr::Collection { element, .. } => extract_base_category_ident(element),
        TypeExpr::Arrow { codomain, .. } => extract_base_category_ident(codomain),
        TypeExpr::MultiBinder(inner) => extract_base_category_ident(inner),
        TypeExpr::Refined { base, .. } => extract_base_category_ident(base),
        TypeExpr::Map { value, .. } => extract_base_category_ident(value),
    }
}
