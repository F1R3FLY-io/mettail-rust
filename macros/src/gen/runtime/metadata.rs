//! Metadata generation for REPL introspection
//!
//! This module generates static metadata about a language's types, terms,
//! equations, and rewrites. The REPL uses this to display the `info` command.

use mettail_ast::{
    grammar::{GrammarItem, GrammarRule, PatternOp, SyntaxExpr, TermParam},
    language::{
        BehavioralPred, Equation, FreshnessTarget, LanguageDef, PredArg, Premise, Quantifier,
        RewriteRule,
    },
    pattern::{Pattern, PatternTerm},
    types::{CollectionType, TypeExpr},
};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{LitByteStr, LitStr};

fn collection_type_name(coll_type: &CollectionType) -> &'static str {
    match coll_type {
        CollectionType::HashBag => "HashBag",
        CollectionType::HashSet => "HashSet",
        CollectionType::Vec => "Vec",
        CollectionType::HashMap => "HashMap",
        CollectionType::PathMap => "PathMap",
    }
}

/// Generate metadata struct and impl for a language
///
/// `definition_source` is the verbatim `language!` body text (captured in
/// `macros/src/lib.rs` before parsing). It is emitted via
/// `LanguageMetadata::definition_source` so a generated language's exact
/// augmented `LanguageDef` can be reconstructed at runtime
/// (`mettail_ast::auto_inject::reconstruct_language_def`), reproducing the same
/// `definition_fingerprint`.
///
/// `lowering_dispositions` is the language's LOWERING-DISPOSITION INVENTORY
/// (`dovetail_report::lowering_disposition_inventory`) — one entry per declared
/// equation orientation, rewrite, and fold, saying whether the runtime lowering
/// delivered it, delegated it to a named lane, suppressed it by decision, or
/// declined it outright. It is emitted here rather than recomputed at each use
/// so there is exactly ONE derivation of what became of a language's declared
/// semantics, reachable from a running program through
/// `LanguageMetadata::lowering_dispositions`.
///
/// # Errors
///
/// `Err(diagnostic)` iff the shared `LanguageDef → LanguageSpec` bridge refuses —
/// an `options { }` value it cannot decode — and so the ONE binding-power table
/// this reflection renders through cannot be built. See the `# The refusal is
/// PROPAGATED` section on [`build_reflection_bp`] for why the alternative is a
/// wrong answer rather than a degraded one.
pub fn generate_metadata(
    language: &LanguageDef,
    definition_source: &str,
    lowering_dispositions: &[crate::gen::runtime::disposition::LoweringDisposition],
) -> Result<TokenStream, String> {
    let name = &language.name;
    let name_str = name.to_string();
    let name_lit = LitStr::new(&name_str, name.span());
    let fingerprint = mettail_ast::identity::language_definition_fingerprint(language);
    let fingerprint_lit = LitStr::new(&fingerprint, name.span());
    let source_lit = LitStr::new(definition_source, Span::call_site());
    let metadata_name = format_ident!("{}Metadata", name);

    // ★ THE ONE binding-power table, built ONCE per language and threaded down to
    // every rendered equation and rewrite side. Its refusal is this function's
    // refusal; see `build_reflection_bp`.
    let bp = build_reflection_bp(language)?;

    // Generate type definitions
    let type_defs = generate_type_defs(language);

    // Generate term definitions
    let term_defs = generate_term_defs(language);

    // Generate equation definitions
    let equation_defs = generate_equation_defs(language, &bp);

    // Generate rewrite definitions
    let rewrite_defs = generate_rewrite_defs(language, &bp);

    // Raw generated languages are substrate-neutral: they do not advertise a
    // production runtime backend by default. The generated Ascent runner remains
    // available only through explicit reference-oracle calls. Dovetail/Rho
    // defaults are installed by checked runtime wrappers.
    let runtime_backend_defs = generate_runtime_backend_defs();

    // Generate logic relation and rule definitions
    let logic_relation_defs = generate_logic_relation_defs(language);
    let logic_rule_defs = generate_logic_rule_defs(language);

    // Sim-B: Generate guard configuration metadata arrays from the
    // language's `guards { }` block. When the block is absent, all
    // five generators emit `&[]`, producing the same output as the
    // default-empty trait methods on `LanguageMetadata`.
    let builtin_predicate_defs = generate_builtin_predicate_defs(language);
    let theory_defs = generate_theory_defs(language);
    let channel_defs = generate_channel_defs(language);
    let join_pattern_defs = generate_join_pattern_defs(language);
    let connective_defs = generate_connective_defs(language);

    // Task #94: the lowering-disposition inventory, emitted verbatim from the one
    // derivation every lowering consumer shares.
    let lowering_disposition_defs =
        crate::gen::runtime::disposition::emit_disposition_defs(lowering_dispositions);
    let semantic_artifact_methods = generate_semantic_artifact_methods(language);

    Ok(quote! {
        /// Static metadata for the #name language
        pub struct #metadata_name;

        impl mettail_runtime::LanguageMetadata for #metadata_name {
            fn name(&self) -> &'static str { #name_lit }

            fn definition_fingerprint(&self) -> Option<&'static str> {
                Some(#fingerprint_lit)
            }

            fn definition_source(&self) -> Option<&'static str> {
                Some(#source_lit)
            }

            #semantic_artifact_methods

            fn types(&self) -> &'static [mettail_runtime::TypeDef] {
                #type_defs
            }

            fn terms(&self) -> &'static [mettail_runtime::TermDef] {
                #term_defs
            }

            fn equations(&self) -> &'static [mettail_runtime::EquationDef] {
                #equation_defs
            }

            fn rewrites(&self) -> &'static [mettail_runtime::RewriteDef] {
                #rewrite_defs
            }

            fn runtime_backends(&self) -> &'static [mettail_runtime::BackendCapabilityDef] {
                #runtime_backend_defs
            }

            fn logic_relations(&self) -> &'static [mettail_runtime::LogicRelationDef] {
                #logic_relation_defs
            }

            fn logic_rules(&self) -> &'static [mettail_runtime::LogicRuleDef] {
                #logic_rule_defs
            }

            fn builtin_predicates(&self) -> &'static [mettail_runtime::BuiltinPredicateDef] {
                #builtin_predicate_defs
            }

            fn theories(&self) -> &'static [mettail_runtime::TheoryDef] {
                #theory_defs
            }

            fn channels(&self) -> &'static [mettail_runtime::ChannelDef] {
                #channel_defs
            }

            fn join_patterns(&self) -> &'static [mettail_runtime::JoinPatternDef] {
                #join_pattern_defs
            }

            fn connectives(&self) -> &'static [mettail_runtime::ConnectiveDef] {
                #connective_defs
            }

            fn lowering_dispositions(&self)
                -> &'static [mettail_runtime::LoweringDispositionDef]
            {
                #lowering_disposition_defs
            }
        }
    })
}

fn generate_semantic_artifact_methods(language: &LanguageDef) -> TokenStream {
    use crate::gen::runtime::dovetail_report::semantic_adapter::{
        derive_semantic_artifacts, SemanticAdapterLayout,
    };

    let result = SemanticAdapterLayout::derive(language)
        .and_then(|layout| derive_semantic_artifacts(language, &layout));
    let artifacts = match result {
        Ok(artifacts) => artifacts,
        Err(error) => {
            let refusal = LitStr::new(&error.to_string(), Span::call_site());
            return quote! {
                fn generated_semantic_artifact_refusal_v1(&self) -> Option<&'static str> {
                    Some(#refusal)
                }
            };
        },
    };

    let grammar = match postcard::to_allocvec(artifacts.grammar()) {
        Ok(bytes) => bytes,
        Err(error) => {
            let refusal = LitStr::new(
                &format!("GrammarCore artifact encoding failed: {error}"),
                Span::call_site(),
            );
            return quote! {
                fn generated_semantic_artifact_refusal_v1(&self) -> Option<&'static str> {
                    Some(#refusal)
                }
            };
        },
    };
    let signature = match postcard::to_allocvec(artifacts.signature()) {
        Ok(bytes) => bytes,
        Err(error) => {
            let refusal = LitStr::new(
                &format!("semantic-signature artifact encoding failed: {error}"),
                Span::call_site(),
            );
            return quote! {
                fn generated_semantic_artifact_refusal_v1(&self) -> Option<&'static str> {
                    Some(#refusal)
                }
            };
        },
    };
    let bindings = mettail_grammar_core::RuntimeCapabilityBindings::default();
    let machine = match artifacts.machine().encode(
        artifacts.signature(),
        artifacts.grammar(),
        &bindings,
        mettail_grammar_core::SemanticMachineAdmissionLimits::default(),
    ) {
        Ok(bytes) => bytes,
        Err(error) => {
            let refusal = LitStr::new(
                &format!("semantic-machine artifact encoding failed: {error:?}"),
                Span::call_site(),
            );
            return quote! {
                fn generated_semantic_artifact_refusal_v1(&self) -> Option<&'static str> {
                    Some(#refusal)
                }
            };
        },
    };

    let grammar = LitByteStr::new(&grammar, Span::call_site());
    let signature = LitByteStr::new(&signature, Span::call_site());
    let machine = LitByteStr::new(&machine, Span::call_site());
    quote! {
        fn generated_semantic_artifacts_v1(
            &self,
        ) -> Option<mettail_runtime::GeneratedSemanticArtifactBytesV1> {
            Some(mettail_runtime::GeneratedSemanticArtifactBytesV1 {
                semantic_key_abi:
                    mettail_runtime::GeneratedSemanticKeyAbiV1::StructuralV2,
                grammar_core_postcard: #grammar,
                semantic_signature_postcard: #signature,
                semantic_machine_image: #machine,
            })
        }
    }
}

/// Build the reflection's binding-power table, or REFUSE.
///
/// # The refusal is PROPAGATED, never substituted
///
/// [`crate::gen::syntax::display::build_bp_lookup`]'s own contract says it: an
/// empty [`BpLookup`](crate::gen::syntax::display::BpLookup) is not a degraded
/// table, it is a table that says every constructor is precedence-free. Rendering
/// through it emits no parenthesis anywhere — which is precisely the tautology
/// `X*Y*Z = X*Y*Z` that this renderer's precedence model exists to remove. A
/// reflected associativity axiom whose entire content is where the brackets go
/// would come back as a WRONG ANSWER, published through
/// `LanguageMetadata::equations` to every runtime consumer, with no diagnostic
/// anywhere in the build. Refusing costs the same expansion an error message.
///
/// # Why this is built once, at the top, and not lazily
///
/// `build_bp_lookup` runs the whole `LanguageDef → LanguageSpec` bridge. Calling
/// it per rendered side made it run twice per equation and twice per rewrite; it
/// is a pure function of `language`, so hoisting it is byte-inert in the output
/// and linear-to-constant in the work. It is also built UNCONDITIONALLY, even for
/// a language that declares no equations, because that is exactly what the
/// sibling that shares this bridge does: `generate_display` calls
/// `build_bp_lookup` at its top whether or not the grammar has an infix rule. Two
/// consumers of one bridge that disagree about WHEN it may refuse is the same
/// class of drift as two consumers that disagree about precedence.
///
/// # What this refusal is NOT: a reachable boundary path
///
/// ★ At the `language!` boundary this `Err` is unreachable today, and the code
/// still propagates it. `macros/src/lib.rs` calls `generate_all` — which calls
/// `generate_display`, which calls the same `build_bp_lookup` on the same
/// `LanguageDef` — BEFORE it calls `generate_metadata`, and refuses there first.
/// That is an argument about one caller's STATEMENT ORDER, not about this
/// function: `generate_metadata` is `pub`, this crate's own tests call it
/// directly, and the campaign that produced this note has already watched a gate
/// silently stop guarding what its doc-comment claimed because the statement
/// order around it moved (`ident_capture_routing::enforce`, hoisted in #141
/// Stage 2). A `Result` costs ten lines and needs no such argument.
fn build_reflection_bp(
    language: &LanguageDef,
) -> Result<crate::gen::syntax::display::BpLookup, String> {
    crate::gen::syntax::display::build_bp_lookup(language).map_err(|rejection| {
        format!(
            "the reflected equational theory for `{}` cannot be rendered, because the \
             binding-power table it shares with `Display` codegen could not be built: \
             {rejection}",
            language.name,
        )
    })
}

fn generate_runtime_backend_defs() -> TokenStream {
    quote! {
        mettail_runtime::NO_RUNTIME_BACKEND_CAPABILITIES
    }
}

/// Generate TypeDef array from language types
fn generate_type_defs(language: &LanguageDef) -> TokenStream {
    let defs: Vec<TokenStream> = language
        .types
        .iter()
        .enumerate()
        .map(|(i, ty)| {
            let name = ty.name.to_string();
            let name_lit = LitStr::new(&name, ty.name.span());
            let is_primary = i == 0;
            let native_type = match &ty.native_type {
                Some(t) => {
                    let t_str = quote!(#t).to_string();
                    let t_lit = LitStr::new(&t_str, Span::call_site());
                    quote! { Some(#t_lit) }
                },
                None => quote! { None },
            };

            quote! {
                mettail_runtime::TypeDef {
                    name: #name_lit,
                    native_type: #native_type,
                    is_primary: #is_primary,
                }
            }
        })
        .collect();

    quote! {
        &[#(#defs),*]
    }
}

/// Generate TermDef array from language terms
fn generate_term_defs(language: &LanguageDef) -> TokenStream {
    let defs: Vec<TokenStream> = language
        .terms
        .iter()
        .map(|rule| generate_term_def(rule, language))
        .collect();

    quote! {
        &[#(#defs),*]
    }
}

/// Generate a single TermDef
fn generate_term_def(rule: &GrammarRule, language: &LanguageDef) -> TokenStream {
    let name = rule.label.to_string();
    let type_name = rule.category.to_string();

    // Generate user syntax
    let syntax = term_to_user_syntax(rule, language);

    // Use LitStr for static string fields to avoid moving String in generated code
    let name_lit = LitStr::new(&name, rule.label.span());
    let type_name_lit = LitStr::new(&type_name, rule.category.span());
    let syntax_lit = LitStr::new(&syntax, rule.label.span());

    // Generate field definitions
    let fields = generate_field_defs(rule);

    // Stage 3.27a (2026-05-04): emit description from doc-comment text
    // captured by `parse_doc_comment` (ast/src/grammar.rs). The text is
    // wrapped via `LitStr::new` which handles all Rust string escaping
    // automatically, so multi-line and special-character doc comments
    // round-trip safely through `quote!` interpolation.
    let description = match &rule.doc_comment {
        Some(text) => {
            let lit = LitStr::new(text, rule.label.span());
            quote! { Some(#lit) }
        },
        None => quote! { None },
    };

    quote! {
        mettail_runtime::TermDef {
            name: #name_lit,
            type_name: #type_name_lit,
            syntax: #syntax_lit,
            description: #description,
            fields: #fields,
        }
    }
}

/// Generate user syntax string for a term
fn term_to_user_syntax(rule: &GrammarRule, _language: &LanguageDef) -> String {
    // If there's a syntax_pattern, use it
    if let Some(syntax_pattern) = &rule.syntax_pattern {
        return syntax_pattern_to_string(syntax_pattern);
    }

    // Otherwise, build from grammar items
    let mut parts = Vec::new();

    for item in &rule.items {
        match item {
            GrammarItem::Terminal(t) => {
                parts.push(t.clone());
            },
            GrammarItem::NonTerminal { ident: nt, .. } => {
                let name = nt.to_string().to_lowercase();
                parts.push(name);
            },
            GrammarItem::Collection { element_type, separator, delimiters, .. } => {
                let elem = element_type.to_string().to_lowercase();
                if let Some((open, close)) = delimiters {
                    parts.push(format!("{} {} ... {}", open, elem, close));
                } else {
                    parts.push(format!("{} {} ...", elem, separator));
                }
            },
            GrammarItem::Binder { category } => {
                // Use lowercase category name as a synthetic binder label.
                parts.push(category.to_string().to_lowercase());
            },
        }
    }

    parts.join("")
}

enum SyntaxStringJob<'syntax> {
    Expr(&'syntax SyntaxExpr),
    Op(&'syntax PatternOp),
    Text(&'static str),
}

fn push_syntax_exprs<'syntax>(
    jobs: &mut Vec<SyntaxStringJob<'syntax>>,
    expressions: &'syntax [SyntaxExpr],
) {
    for expression in expressions.iter().rev() {
        jobs.push(SyntaxStringJob::Expr(expression));
    }
}

fn append_syntax_string(result: &mut String, mut jobs: Vec<SyntaxStringJob<'_>>) {
    while let Some(job) = jobs.pop() {
        match job {
            SyntaxStringJob::Text(text) => result.push_str(text),
            SyntaxStringJob::Expr(SyntaxExpr::Literal(text)) => result.push_str(text),
            SyntaxStringJob::Expr(SyntaxExpr::Param(ident)) => {
                result.push_str(&ident.to_string());
            },
            SyntaxStringJob::Expr(SyntaxExpr::Op(operation)) => {
                jobs.push(SyntaxStringJob::Op(operation));
            },
            SyntaxStringJob::Expr(SyntaxExpr::TokenKind { name, bind }) => {
                if let Some(bind) = bind {
                    result.push_str(&bind.to_string());
                    result.push('@');
                }
                result.push_str(&name.to_string());
            },
            SyntaxStringJob::Expr(SyntaxExpr::GuestBody { open, close, bind, kind }) => {
                result.push('*');
                result.push_str(kind.intrinsic());
                result.push('(');
                result.push_str(&bind.to_string());
                result.push(',');
                result.push_str(&open.to_string());
                result.push(',');
                result.push_str(&close.to_string());
                result.push(')');
            },
            SyntaxStringJob::Op(PatternOp::Sep { collection, separator, source }) => {
                if let Some(source) = source {
                    if let PatternOp::Map { body, .. } = source.as_ref() {
                        jobs.push(SyntaxStringJob::Text(", ..."));
                        push_syntax_exprs(&mut jobs, body);
                    } else {
                        result.push_str("..., ...");
                    }
                } else {
                    result.push_str(&collection.to_string());
                    result.push(' ');
                    result.push_str(separator);
                    result.push_str(" ...");
                }
            },
            SyntaxStringJob::Op(PatternOp::Var(ident)) => {
                result.push_str(&ident.to_string());
            },
            SyntaxStringJob::Op(PatternOp::Opt { inner }) => {
                result.push('[');
                jobs.push(SyntaxStringJob::Text("]"));
                push_syntax_exprs(&mut jobs, inner);
            },
            SyntaxStringJob::Op(PatternOp::Zip { left, right }) => {
                result.push('(');
                result.push_str(&left.to_string());
                result.push_str(", ");
                result.push_str(&right.to_string());
                result.push(')');
            },
            SyntaxStringJob::Op(PatternOp::Map { params, body, .. }) => {
                if params.len() <= 1 {
                    result.push('|');
                    if let Some(param) = params.first() {
                        result.push_str(&param.to_string());
                    }
                    result.push_str("| ");
                }
                push_syntax_exprs(&mut jobs, body);
            },
        }
    }
}

/// Convert a syntax pattern to a user-readable string without placing source
/// nesting on the native call stack or rebuilding child strings.
fn syntax_pattern_to_string(pattern: &[SyntaxExpr]) -> String {
    let mut result = String::new();
    let mut jobs = Vec::new();
    push_syntax_exprs(&mut jobs, pattern);
    append_syntax_string(&mut result, jobs);
    result
}

fn append_pattern_op_string(result: &mut String, operation: &PatternOp) {
    append_syntax_string(result, vec![SyntaxStringJob::Op(operation)]);
}

/// Generate FieldDef array for a term
fn generate_field_defs(rule: &GrammarRule) -> TokenStream {
    // Use term_context if available (new syntax)
    if let Some(ctx) = &rule.term_context {
        fn one_param(param: &TermParam) -> Vec<TokenStream> {
            match param {
                TermParam::Simple { name, ty } => {
                    let name_str = name.to_string();
                    let ty_str = type_expr_to_string(ty);
                    let name_lit = LitStr::new(&name_str, name.span());
                    let ty_lit = LitStr::new(&ty_str, Span::call_site());
                    vec![quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: #ty_lit,
                            is_binder: false,
                        }
                    }]
                },
                TermParam::Abstraction { binder, body, ty } => {
                    let name_str = format!("^{}.{}", binder, body);
                    let ty_str = type_expr_to_string(ty);
                    let name_lit = LitStr::new(&name_str, binder.span());
                    let ty_lit = LitStr::new(&ty_str, Span::call_site());
                    vec![quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: #ty_lit,
                            is_binder: true,
                        }
                    }]
                },
                TermParam::MultiAbstraction { binder, body, ty } => {
                    let name_str = format!("^[{}].{}", binder, body);
                    let ty_str = type_expr_to_string(ty);
                    let name_lit = LitStr::new(&name_str, binder.span());
                    let ty_lit = LitStr::new(&ty_str, Span::call_site());
                    vec![quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: #ty_lit,
                            is_binder: true,
                        }
                    }]
                },
                TermParam::GuardBody { name, .. } => {
                    let name_str = format!("?{}", name);
                    let name_lit = LitStr::new(&name_str, name.span());
                    vec![quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: "Guard",
                            is_binder: false,
                        }
                    }]
                },
                TermParam::Optional { params: inner } => {
                    // Opt-Group: each inner param becomes an Option<>-wrapped
                    // FieldDef whose `ty` field is wrapped as `Option<T>`
                    // and whose `name` is suffixed with `?` so diagnostic
                    // consumers (debug print, equality, hash-cons key
                    // builder) know the field may be absent.
                    fn one_optional(param: &TermParam) -> Vec<TokenStream> {
                        match param {
                            TermParam::Simple { name, ty } => {
                                let name_str = format!("{}?", name);
                                let ty_str = format!("Option<{}>", type_expr_to_string(ty));
                                let name_lit = LitStr::new(&name_str, name.span());
                                let ty_lit = LitStr::new(&ty_str, Span::call_site());
                                vec![quote! {
                                    mettail_runtime::FieldDef {
                                        name: #name_lit,
                                        ty: #ty_lit,
                                        is_binder: false,
                                    }
                                }]
                            },
                            TermParam::Abstraction { binder, body, ty } => {
                                let name_str = format!("^{}.{}?", binder, body);
                                let ty_str = format!("Option<{}>", type_expr_to_string(ty));
                                let name_lit = LitStr::new(&name_str, binder.span());
                                let ty_lit = LitStr::new(&ty_str, Span::call_site());
                                vec![quote! {
                                    mettail_runtime::FieldDef {
                                        name: #name_lit,
                                        ty: #ty_lit,
                                        is_binder: true,
                                    }
                                }]
                            },
                            TermParam::MultiAbstraction { binder, body, ty } => {
                                let name_str = format!("^[{}].{}?", binder, body);
                                let ty_str = format!("Option<{}>", type_expr_to_string(ty));
                                let name_lit = LitStr::new(&name_str, binder.span());
                                let ty_lit = LitStr::new(&ty_str, Span::call_site());
                                vec![quote! {
                                    mettail_runtime::FieldDef {
                                        name: #name_lit,
                                        ty: #ty_lit,
                                        is_binder: true,
                                    }
                                }]
                            },
                            TermParam::GuardBody { name } => {
                                let name_str = format!("?{}?", name);
                                let name_lit = LitStr::new(&name_str, name.span());
                                vec![quote! {
                                    mettail_runtime::FieldDef {
                                        name: #name_lit,
                                        ty: "Option<Guard>",
                                        is_binder: false,
                                    }
                                }]
                            },
                            TermParam::Optional { params: nested } => {
                                // Nested Optional: flatten — Option<Option<T>>
                                // collapses to Option<T> at the outer level
                                // (the WPDS engine never produces Some(Some(...)),
                                // only Some(...) or None).
                                nested.iter().flat_map(one_optional).collect()
                            },
                        }
                    }
                    inner.iter().flat_map(one_optional).collect()
                },
            }
        }
        let defs: Vec<TokenStream> = ctx.iter().flat_map(one_param).collect();
        return quote! { &[#(#defs),*] };
    }

    // Old syntax - build from items
    let defs: Vec<TokenStream> = rule
        .items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| {
            match item {
                GrammarItem::NonTerminal { ident: nt, kind } if !kind.is_builtin() => {
                    let name_str = format!("f{}", i);
                    let ty_str = nt.to_string();
                    let name_lit = LitStr::new(&name_str, Span::call_site());
                    let ty_lit = LitStr::new(&ty_str, Span::call_site());
                    Some(quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: #ty_lit,
                            is_binder: false,
                        }
                    })
                },
                GrammarItem::Collection { element_type, coll_type, .. } => {
                    let name_str = format!("f{}", i);
                    let ty_str = format!("{}({})", collection_type_name(coll_type), element_type);
                    let name_lit = LitStr::new(&name_str, Span::call_site());
                    let ty_lit = LitStr::new(&ty_str, Span::call_site());
                    Some(quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: #ty_lit,
                            is_binder: false,
                        }
                    })
                },
                GrammarItem::Binder { category } => {
                    // Use lowercase category as a synthetic field name.
                    let name_str = category.to_string().to_lowercase();
                    let ty_str = category.to_string();
                    let name_lit = LitStr::new(&name_str, category.span());
                    let ty_lit = LitStr::new(&ty_str, category.span());
                    Some(quote! {
                        mettail_runtime::FieldDef {
                            name: #name_lit,
                            ty: #ty_lit,
                            is_binder: true,
                        }
                    })
                },
                _ => None,
            }
        })
        .collect();

    quote! { &[#(#defs),*] }
}

enum TypeExprStringJob<'ty> {
    Visit(&'ty TypeExpr),
    Text(&'static str),
}

/// Convert a [`TypeExpr`] to its metadata spelling without placing type nesting
/// on the native call stack or constructing an intermediate string per node.
fn type_expr_to_string(ty: &TypeExpr) -> String {
    let mut result = String::new();
    let mut jobs = vec![TypeExprStringJob::Visit(ty)];
    while let Some(job) = jobs.pop() {
        match job {
            TypeExprStringJob::Text(text) => result.push_str(text),
            TypeExprStringJob::Visit(TypeExpr::Base(ident)) => {
                result.push_str(&ident.to_string());
            },
            TypeExprStringJob::Visit(TypeExpr::Collection { coll_type, element }) => {
                result.push_str(collection_type_name(coll_type));
                result.push('(');
                jobs.push(TypeExprStringJob::Text(")"));
                jobs.push(TypeExprStringJob::Visit(element));
            },
            TypeExprStringJob::Visit(TypeExpr::Map { key, value }) => {
                result.push_str("HashMap(");
                jobs.push(TypeExprStringJob::Text(")"));
                jobs.push(TypeExprStringJob::Visit(value));
                jobs.push(TypeExprStringJob::Text(", "));
                jobs.push(TypeExprStringJob::Visit(key));
            },
            TypeExprStringJob::Visit(TypeExpr::Arrow { domain, codomain }) => {
                result.push('[');
                jobs.push(TypeExprStringJob::Text("]"));
                jobs.push(TypeExprStringJob::Visit(codomain));
                jobs.push(TypeExprStringJob::Text(" -> "));
                jobs.push(TypeExprStringJob::Visit(domain));
            },
            TypeExprStringJob::Visit(TypeExpr::MultiBinder(inner)) => {
                jobs.push(TypeExprStringJob::Text("*"));
                jobs.push(TypeExprStringJob::Visit(inner));
            },
            TypeExprStringJob::Visit(TypeExpr::Refined { base, .. }) => {
                jobs.push(TypeExprStringJob::Visit(base));
            },
        }
    }
    result
}

/// Generate EquationDef array
fn generate_equation_defs(
    language: &LanguageDef,
    bp: &crate::gen::syntax::display::BpLookup,
) -> TokenStream {
    let defs: Vec<TokenStream> = language
        .equations
        .iter()
        .map(|eq| generate_equation_def(eq, language, bp))
        .collect();

    quote! {
        &[#(#defs),*]
    }
}

fn premise_to_display_string(p: &Premise) -> String {
    match p {
        Premise::Freshness(fc) => {
            let target = match &fc.term {
                FreshnessTarget::Var(v) => v.to_string(),
                FreshnessTarget::CollectionRest(v) => format!("...{}", v),
            };
            format!("{} # {}", fc.var, target)
        },
        Premise::RelationQuery { relation, args } => {
            let args_str: Vec<_> = args.iter().map(|a| a.to_string()).collect();
            format!("{}({})", relation, args_str.join(", "))
        },
        Premise::Congruence { source, target } => {
            format!("{} ~> {}", source, target)
        },
        // ★ (#195) The reflected spelling of a WITHHELD congruence is the surface
        // spelling: `S ~/> T`. It must NOT render as `S ~> T` — the reflected metadata is
        // what `languages/tests/congruence_declaration_witness.rs` derives its declared
        // set from, and a denial that renders as an assertion would make that derivation
        // count a withholding as a propagating congruence.
        Premise::CongruenceWithheld { source, target } => {
            format!("{} ~/> {}", source, target)
        },
        Premise::ForAll { collection, param, body } => {
            format!("{}.*map(|{}| {})", collection, param, premise_to_display_string(body))
        },
        Premise::BehavioralGuard(pred) => {
            // Lint-D cleanup: proper unicode-formatted display instead of
            // `{:?}` Debug output. Uses the same display function as the
            // simulator metadata bridge.
            format!("guard({})", behavioral_pred_to_display(pred))
        },
        Premise::SyntheticInjGuard {
            inner_var,
            source_category,
            excluded_variants,
        } => {
            // Phase A (2026-05-16): synthetic-injection guard display.
            let variants: Vec<_> = excluded_variants.iter().map(|v| v.to_string()).collect();
            format!(
                "synthetic_inj_guard({}, {}, [{}])",
                inner_var,
                source_category,
                variants.join(", "),
            )
        },
    }
}

/// Render a `BehavioralPred` as a unicode-formatted user-facing string
/// suitable for inclusion in `EquationDef::conditions` and
/// `RewriteDef::conditions` slices visible via `LanguageMetadata`.
///
/// The rendering uses the same unicode connectives as the design doc
/// §2A surface syntax:
///
/// | Variant | Rendering |
/// |---------|-----------|
/// | `RelationQuery { name, args, negated: false }` | `name(a, b)` |
/// | `RelationQuery { negated: true }` | `¬name(a, b)` |
/// | `And(a, b)` | `a ∧ b` |
/// | `Or(a, b)`  | `a ∨ b` |
/// | `Not(inner)` | `¬inner` |
/// | `Implies(a, b)` | `a ⟹ b` |
/// | `Quantified { ForAll, var, body }` | `∀var. body` (with optional domain/bound) |
/// | `Quantified { Exists, var, body }` | `∃var. body` |
/// | `AcMatch { bag, elements, rest }` | `ac_match(bag, {e1, e2, ...rest})` |
///
/// Parentheses are added conservatively around sub-expressions to avoid
/// ambiguity: any `And`/`Or`/`Implies` operand that is itself a binary
/// combinator of lower-or-equal precedence gets wrapped.
fn behavioral_pred_to_display(pred: &BehavioralPred) -> String {
    match pred {
        BehavioralPred::RelationQuery { relation_name, args, negated } => {
            let args_str: Vec<String> = args
                .iter()
                .map(|a| match a {
                    PredArg::Var(v) => v.to_string(),
                    PredArg::Constant(c) => c.to_string(),
                })
                .collect();
            let call = format!("{}({})", relation_name, args_str.join(", "));
            if *negated {
                format!("¬{}", call)
            } else {
                call
            }
        },
        BehavioralPred::And(a, b) => {
            format!("{} ∧ {}", wrap_if_binary(a), wrap_if_binary(b),)
        },
        BehavioralPred::Or(a, b) => {
            format!("{} ∨ {}", wrap_if_binary(a), wrap_if_binary(b),)
        },
        BehavioralPred::Not(inner) => {
            format!("¬{}", wrap_if_binary(inner))
        },
        BehavioralPred::Implies(a, b) => {
            format!("{} ⟹ {}", wrap_if_binary(a), wrap_if_binary(b),)
        },
        BehavioralPred::Quantified { quantifier, var, domain, bound, body } => {
            let q = match quantifier {
                Quantifier::ForAll => "∀",
                Quantifier::Exists => "∃",
            };
            let domain_str = match (domain, bound) {
                (Some(d), Some(k)) => format!(" ∈ {}_{{k={}}}", d, k),
                (Some(d), None) => format!(" ∈ {}", d),
                (None, Some(k)) => format!(" _{{k={}}}", k),
                (None, None) => String::new(),
            };
            format!("{}{}{}. {}", q, var, domain_str, behavioral_pred_to_display(body),)
        },
        BehavioralPred::AcMatch { bag, elements, rest } => {
            let mut elems: Vec<String> = elements.iter().map(|e| e.to_string()).collect();
            if let Some(r) = rest {
                elems.push(format!("...{}", r));
            }
            format!("ac_match({}, {{{}}})", bag, elems.join(", "))
        },
        BehavioralPred::Top => "⊤".to_string(),
    }
}

/// Wrap a sub-expression in parentheses when it is a binary combinator
/// (And, Or, Implies). Leaf predicates and Not/Quantified/AcMatch pass
/// through unparenthesized because they are unambiguous at any nesting
/// depth in the rendered output.
fn wrap_if_binary(pred: &BehavioralPred) -> String {
    match pred {
        BehavioralPred::And(_, _) | BehavioralPred::Or(_, _) | BehavioralPred::Implies(_, _) => {
            format!("({})", behavioral_pred_to_display(pred))
        },
        _ => behavioral_pred_to_display(pred),
    }
}

/// Generate a single EquationDef
fn generate_equation_def(
    eq: &Equation,
    language: &LanguageDef,
    bp: &crate::gen::syntax::display::BpLookup,
) -> TokenStream {
    // Convert conditions to strings
    let conditions: Vec<String> = eq.premises.iter().map(premise_to_display_string).collect();

    let conditions_tokens: Vec<TokenStream> = conditions
        .iter()
        .map(|s| {
            let lit = LitStr::new(s, Span::call_site());
            quote! { #lit }
        })
        .collect();

    // Convert patterns to user syntax (use LitStr for static str fields)
    let lhs = pattern_to_user_syntax(&eq.left, language, bp);
    let rhs = pattern_to_user_syntax(&eq.right, language, bp);
    let lhs_lit = LitStr::new(&lhs, Span::call_site());
    let rhs_lit = LitStr::new(&rhs, Span::call_site());

    // Sim-B: detect BehavioralGuard premises on equations too.
    let is_guarded = eq
        .premises
        .iter()
        .any(|p| matches!(p, Premise::BehavioralGuard(_)));

    // ★ #97 item 4. Every equation in the grammar is NAMED, and the reflection
    // could not say which equation it was reflecting. It is the only thing that
    // identifies a rule whose two rendered surfaces legitimately coincide.
    let name_lit = LitStr::new(&eq.name.to_string(), eq.name.span());

    quote! {
        mettail_runtime::EquationDef {
            name: #name_lit,
            conditions: &[#(#conditions_tokens),*],
            lhs: #lhs_lit,
            rhs: #rhs_lit,
            is_guarded: #is_guarded,
        }
    }
}

/// Generate RewriteDef array
fn generate_rewrite_defs(
    language: &LanguageDef,
    bp: &crate::gen::syntax::display::BpLookup,
) -> TokenStream {
    let defs: Vec<TokenStream> = language
        .rewrites
        .iter()
        .enumerate()
        .map(|(i, rw)| generate_rewrite_def(rw, i, language, bp))
        .collect();

    quote! {
        &[#(#defs),*]
    }
}

/// Generate a single RewriteDef
fn generate_rewrite_def(
    rw: &RewriteRule,
    _index: usize,
    language: &LanguageDef,
    bp: &crate::gen::syntax::display::BpLookup,
) -> TokenStream {
    // Extract the rewrite rule name from the AST
    let name = {
        let name_str = rw.name.to_string();
        let name_lit = LitStr::new(&name_str, rw.name.span());
        quote! { Some(#name_lit) }
    };

    // Convert conditions to strings
    let conditions: Vec<String> = rw.premises.iter().map(premise_to_display_string).collect();

    let conditions_tokens: Vec<TokenStream> = conditions
        .iter()
        .map(|s| {
            let lit = LitStr::new(s, Span::call_site());
            quote! { #lit }
        })
        .collect();

    // Convert premise if present (use LitStr for static str)
    let premise = rw
        .premises
        .iter()
        .find_map(|p| {
            if let Premise::Congruence { source, target } = p {
                let source_str = source.to_string();
                let target_str = target.to_string();
                let source_lit = LitStr::new(&source_str, source.span());
                let target_lit = LitStr::new(&target_str, target.span());
                Some(quote! { Some((#source_lit, #target_lit)) })
            } else {
                None
            }
        })
        .unwrap_or(quote! { None });

    // Convert patterns to user syntax (use LitStr for static str fields)
    let lhs = pattern_to_user_syntax(&rw.left, language, bp);
    let rhs = pattern_to_user_syntax(&rw.right, language, bp);
    let lhs_lit = LitStr::new(&lhs, Span::call_site());
    let rhs_lit = LitStr::new(&rhs, Span::call_site());

    // Detect whether any premise guards rewrite applicability. Behavioral
    // guards are user-authored; SyntheticInjGuard is generated for NormCast
    // rewrites to bound auto-injection cascades.
    let is_guarded = rw
        .premises
        .iter()
        .any(|p| matches!(p, Premise::BehavioralGuard(_) | Premise::SyntheticInjGuard { .. }));

    quote! {
        mettail_runtime::RewriteDef {
            name: #name,
            conditions: &[#(#conditions_tokens),*],
            premise: #premise,
            lhs: #lhs_lit,
            rhs: #rhs_lit,
            is_guarded: #is_guarded,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// Task #97 — THE REFLECTION RENDERER'S PRECEDENCE MODEL
// ═══════════════════════════════════════════════════════════════════════════
//
// # The defect
//
// The renderer below turns an equation's or rewrite's `Pattern` back into the
// surface syntax a user would write. Until this repair it spliced each child
// into its parent's syntax pattern with NO context argument — no `min_bp`, no
// parent label — and therefore never emitted a parenthesis. So
//
//     Mul(Mul(X, Y), Z)  ⟼  "X" + "*" + "Y"   then + "*" + "Z"  =  X*Y*Z
//     Mul(X, Mul(Y, Z))  ⟼  "X" + "*" + "Y*Z"                   =  X*Y*Z
//
// and Monoid's associativity axiom — the one law whose entire content IS the
// bracketing — reflected as the tautology `X*Y*Z = X*Y*Z`.
//
// # The model is BORROWED, never re-derived
//
// A precedence-aware renderer already exists in the same build: the generated
// `Display` impl, whose operator arms emit `let needs_parens = <own_left_bp> <
// min_bp;` and push their left and right operands at `left_bp` / `right_bp`.
// Its table is [`BpLookup`], built once by
// `gen::syntax::display::build_bp_lookup` from
// `prattail::binding_power::analyze_binding_powers`. This renderer reads THAT
// table. Two precedence models — one for `Display`, one for the reflected
// theory — could disagree about the very brackets an associativity law is
// about, which is the failure this repair exists to remove, not to duplicate.
//
// # Consequence: the bracketing is MINIMAL, and that is correct
//
// `Mul` is left-associative (`left_bp = 2`, `right_bp = 3`), so the LEFT-nested
// side needs no bracket — `X*Y*Z` already means `(X*Y)*Z` — while the
// RIGHT-nested side does: `2 < 3`, so it renders `X*(Y*Z)`. The axiom therefore
// reflects as `X*Y*Z = X*(Y*Z)`: two different strings, each of which reparses
// to the side it came from. A renderer that bracketed both sides would be a
// SECOND model, disagreeing with `Display` about a string neither needs.

/// Everything the reflection renderer needs that is not the pattern itself.
#[derive(Clone, Copy)]
struct RenderCtx<'a> {
    language: &'a LanguageDef,
    /// The ONE binding-power table, shared with `Display` codegen.
    bp: &'a crate::gen::syntax::display::BpLookup,
}

/// A constructor's precedence: what it takes to bracket IT, and the threshold
/// each of its operands inherits.
///
/// `None` from [`rule_bp`] means the constructor is not Pratt-registered — a
/// delimited, atomic or binder rule. Such a rule brackets its own operands with
/// its own literals, so it never needs parentheses and its children inherit `0`.
/// This mirrors the `else` arm of `display.rs`'s arm generator exactly.
#[derive(Clone, Copy)]
enum ChildBpPolicy {
    Uniform(u8),
    Regular { left: u8, right: u8 },
    Mixfix { left: u8, right: u8, slots: usize },
}

#[derive(Clone, Copy)]
struct RuleBp {
    /// The rule's own left binding power — the operand strength it competes at.
    /// Bracket the rendering when this is BELOW the inherited threshold.
    own_left_bp: u8,
    /// The `min_bp` each argument slot inherits, by slot index.
    child_policy: ChildBpPolicy,
}

/// Read `label`'s precedence out of the shared table, in the same case order
/// `display.rs` uses: postfix, then mixfix, then regular infix, then unary
/// prefix, then "not an operator".
fn rule_bp(
    label: &str,
    arg_slots: usize,
    bp: &crate::gen::syntax::display::BpLookup,
) -> Option<RuleBp> {
    if let Some(info) = bp.infix.get(label) {
        let child_policy = if info.is_postfix {
            // Postfix: the single operand carries the operator's left power.
            ChildBpPolicy::Uniform(info.left_bp)
        } else if info.is_mixfix {
            // Mixfix: first operand = left_bp, last = right_bp, interior = 0
            // (an interior slot is fenced by the operator's own literals).
            ChildBpPolicy::Mixfix {
                left: info.left_bp,
                right: info.right_bp,
                slots: arg_slots,
            }
        } else {
            // Regular infix: left operand = left_bp, everything after = right_bp.
            ChildBpPolicy::Regular { left: info.left_bp, right: info.right_bp }
        };
        return Some(RuleBp { own_left_bp: info.left_bp, child_policy });
    }
    if let Some(prefix) = bp.prefix.get(label) {
        return Some(RuleBp {
            own_left_bp: prefix.prefix_bp,
            child_policy: ChildBpPolicy::Uniform(prefix.prefix_bp),
        });
    }
    None
}

/// The `min_bp` for argument slot `index`, or `0` when the rule is not
/// precedence-governed.
fn child_min_bp(bp: Option<RuleBp>, index: usize) -> u8 {
    let Some(bp) = bp else {
        return 0;
    };
    match bp.child_policy {
        ChildBpPolicy::Uniform(value) => value,
        ChildBpPolicy::Regular { left, right } => {
            if index == 0 {
                left
            } else {
                right
            }
        },
        ChildBpPolicy::Mixfix { left, right, slots } => {
            if index == 0 {
                left
            } else if index + 1 == slots {
                right
            } else {
                0
            }
        },
    }
}

/// The rule for `name` when it denotes a NULLARY constructor, else `None`.
///
/// ★ #97 item 2. A bare identifier in a pattern is parsed as
/// [`PatternTerm::Var`] whether the author meant a metavariable or a nullary
/// constructor; the rest of the system already decides between the two by
/// LOOKING THE NAME UP (`PatternTerm::is_ground_pattern` calls
/// `LanguageDef::get_constructor` for exactly this reason, and the Dovetail
/// lowering resolves the same node as a constructor leaf). The renderer used to
/// be the one place that did not, so Monoid's `Unit` — declared
/// `Unit . M ::= "e" ;` — reflected as the bare word `Unit`, which is the
/// constructor's LABEL and not anything a user can write.
///
/// "Nullary" is structural: the rule consumes no argument slot, in either
/// grammar form. A constructor that takes arguments is not what a bare
/// identifier denotes, so its label passes through unresolved.
fn nullary_constructor_rule<'language>(
    name: &syn::Ident,
    ctx: RenderCtx<'language>,
) -> Option<&'language GrammarRule> {
    let rule = ctx.language.get_constructor(name)?;
    let takes_arguments = match (&rule.term_context, &rule.syntax_pattern) {
        (Some(term_context), _) => !term_context.is_empty(),
        (None, _) => rule.items.iter().any(|item| {
            matches!(
                item,
                GrammarItem::NonTerminal { .. }
                    | GrammarItem::Collection { .. }
                    | GrammarItem::Binder { .. }
            )
        }),
    };
    if takes_arguments {
        return None;
    }
    Some(rule)
}

/// Convert a Pattern to user syntax string, at the top level (nothing outside
/// it, so nothing can require a bracket).
///
/// ⚠ `bp` is a PARAMETER, not something this function builds. Building it here
/// meant re-running the whole `LanguageDef → LanguageSpec` bridge once per
/// rendered side, and — because a `Result` has no natural answer this deep inside
/// a `String`-returning renderer — swallowing its refusal into
/// `BpLookup::empty()`. See [`build_reflection_bp`]: the one caller that can
/// refuse builds the table, once.
fn pattern_to_user_syntax(
    pattern: &Pattern,
    language: &LanguageDef,
    bp: &crate::gen::syntax::display::BpLookup,
) -> String {
    render_pattern(pattern, RenderCtx { language, bp }, 0)
}

/// Defunctionalized continuations for the reflected-pattern renderer. Every
/// variant is constant-size, and child renderings are never parked as nested
/// `String` values.
enum PatternRenderJob<'pattern> {
    Pattern(&'pattern Pattern, u8),
    Term(&'pattern PatternTerm, u8),
    ApplySyntax {
        syntax: &'pattern [SyntaxExpr],
        args: &'pattern [Pattern],
        bp: Option<RuleBp>,
        expr_index: usize,
        arg_index: usize,
        slot: usize,
        current_lambda: Option<&'pattern Pattern>,
    },
    Grammar {
        rule: &'pattern GrammarRule,
        args: &'pattern [Pattern],
        bp: Option<RuleBp>,
        item_index: usize,
        arg_index: usize,
        slot: usize,
    },
    CollectionWithSep {
        pattern: &'pattern Pattern,
        separator: &'pattern str,
    },
    Text(&'pattern str),
    Separator(&'pattern str),
    Rest(&'pattern syn::Ident),
    MapOpen(&'pattern [syn::Ident]),
    SubstClose(&'pattern syn::Ident),
}

fn append_idents(result: &mut String, idents: &[syn::Ident]) {
    for (index, ident) in idents.iter().enumerate() {
        if index != 0 {
            result.push_str(", ");
        }
        result.push_str(&ident.to_string());
    }
}

fn push_pattern_sequence<'pattern>(
    jobs: &mut Vec<PatternRenderJob<'pattern>>,
    patterns: &'pattern [Pattern],
    separator: &'static str,
) {
    for (index, pattern) in patterns.iter().enumerate().rev() {
        jobs.push(PatternRenderJob::Pattern(pattern, 0));
        if index != 0 {
            jobs.push(PatternRenderJob::Text(separator));
        }
    }
}

fn drive_pattern_renderer<'pattern>(
    mut jobs: Vec<PatternRenderJob<'pattern>>,
    ctx: RenderCtx<'pattern>,
) -> String {
    let mut result = String::new();
    while let Some(job) = jobs.pop() {
        match job {
            PatternRenderJob::Text(text) => result.push_str(text),
            PatternRenderJob::Separator(separator) => {
                result.push(' ');
                result.push_str(separator);
                result.push(' ');
            },
            PatternRenderJob::Rest(rest) => {
                result.push_str("...");
                result.push_str(&rest.to_string());
            },
            PatternRenderJob::MapOpen(params) => {
                result.push_str(".*map(|");
                append_idents(&mut result, params);
                result.push_str("| ");
            },
            PatternRenderJob::SubstClose(var) => {
                result.push('/');
                result.push_str(&var.to_string());
                result.push(']');
            },
            PatternRenderJob::Pattern(Pattern::Term(term), min_bp) => {
                jobs.push(PatternRenderJob::Term(term, min_bp));
            },
            PatternRenderJob::Pattern(Pattern::Collection { elements, rest, .. }, _) => {
                result.push('{');
                jobs.push(PatternRenderJob::Text("}"));
                if let Some(rest) = rest {
                    jobs.push(PatternRenderJob::Rest(rest));
                    if !elements.is_empty() {
                        jobs.push(PatternRenderJob::Text(" | "));
                    }
                }
                push_pattern_sequence(&mut jobs, elements, " | ");
            },
            PatternRenderJob::Pattern(Pattern::Map { collection, params, body }, _) => {
                jobs.push(PatternRenderJob::Text(")"));
                jobs.push(PatternRenderJob::Pattern(body, 0));
                jobs.push(PatternRenderJob::MapOpen(params));
                jobs.push(PatternRenderJob::Pattern(collection, 0));
            },
            PatternRenderJob::Pattern(Pattern::Zip { first, second }, _) => {
                result.push_str("*zip(");
                jobs.push(PatternRenderJob::Text(")"));
                jobs.push(PatternRenderJob::Pattern(second, 0));
                jobs.push(PatternRenderJob::Text(", "));
                jobs.push(PatternRenderJob::Pattern(first, 0));
            },
            PatternRenderJob::Pattern(Pattern::IndexedVec { collection, index, element }, _) => {
                result.push_str(&collection.to_string());
                result.push('[');
                result.push_str(&index.to_string());
                result.push_str(" := ");
                jobs.push(PatternRenderJob::Text("]"));
                jobs.push(PatternRenderJob::Pattern(element, 0));
            },
            PatternRenderJob::Term(PatternTerm::Var(name), _) => {
                if let Some(rule) = nullary_constructor_rule(name, ctx) {
                    match &rule.syntax_pattern {
                        Some(syntax) => jobs.push(PatternRenderJob::ApplySyntax {
                            syntax,
                            args: &[],
                            bp: None,
                            expr_index: 0,
                            arg_index: 0,
                            slot: 0,
                            current_lambda: None,
                        }),
                        None => jobs.push(PatternRenderJob::Grammar {
                            rule,
                            args: &[],
                            bp: None,
                            item_index: 0,
                            arg_index: 0,
                            slot: 0,
                        }),
                    }
                } else {
                    result.push_str(&name.to_string());
                }
            },
            PatternRenderJob::Term(PatternTerm::Apply { constructor, args }, min_bp) => {
                if let Some(rule) = ctx
                    .language
                    .terms
                    .iter()
                    .find(|rule| &rule.label == constructor)
                {
                    let bp = rule_bp(&constructor.to_string(), args.len(), ctx.bp);
                    if bp.is_some_and(|bp| bp.own_left_bp < min_bp) {
                        result.push('(');
                        jobs.push(PatternRenderJob::Text(")"));
                    }
                    match &rule.syntax_pattern {
                        Some(syntax) => jobs.push(PatternRenderJob::ApplySyntax {
                            syntax,
                            args,
                            bp,
                            expr_index: 0,
                            arg_index: 0,
                            slot: 0,
                            current_lambda: None,
                        }),
                        None => jobs.push(PatternRenderJob::Grammar {
                            rule,
                            args,
                            bp,
                            item_index: 0,
                            arg_index: 0,
                            slot: 0,
                        }),
                    }
                } else if args.is_empty() {
                    result.push_str(&constructor.to_string());
                } else {
                    result.push('(');
                    result.push_str(&constructor.to_string());
                    jobs.push(PatternRenderJob::Text(")"));
                    for argument in args.iter().rev() {
                        jobs.push(PatternRenderJob::Pattern(argument, 0));
                        jobs.push(PatternRenderJob::Text(" "));
                    }
                }
            },
            PatternRenderJob::Term(PatternTerm::Lambda { binder, body }, _) => {
                result.push('^');
                result.push_str(&binder.to_string());
                result.push_str(".{");
                jobs.push(PatternRenderJob::Text("}"));
                jobs.push(PatternRenderJob::Pattern(body, 0));
            },
            PatternRenderJob::Term(PatternTerm::MultiLambda { binders, body }, _) => {
                result.push_str("^[");
                append_idents(&mut result, binders);
                result.push_str("].{");
                jobs.push(PatternRenderJob::Text("}"));
                jobs.push(PatternRenderJob::Pattern(body, 0));
            },
            PatternRenderJob::Term(PatternTerm::Subst { term, var, replacement }, _) => {
                jobs.push(PatternRenderJob::SubstClose(var));
                jobs.push(PatternRenderJob::Pattern(replacement, 0));
                jobs.push(PatternRenderJob::Text("["));
                jobs.push(PatternRenderJob::Pattern(term, 0));
            },
            PatternRenderJob::Term(PatternTerm::MultiSubst { scope, replacements }, _) => {
                jobs.push(PatternRenderJob::Text("]"));
                push_pattern_sequence(&mut jobs, replacements, ", ");
                jobs.push(PatternRenderJob::Text("["));
                jobs.push(PatternRenderJob::Pattern(scope, 0));
            },
            PatternRenderJob::ApplySyntax {
                syntax,
                args,
                bp,
                mut expr_index,
                mut arg_index,
                mut slot,
                mut current_lambda,
            } => {
                while let Some(expression) = syntax.get(expr_index) {
                    expr_index += 1;
                    match expression {
                        SyntaxExpr::Literal(text) => result.push_str(text),
                        SyntaxExpr::TokenKind { name, .. } => {
                            result.push_str(&name.to_string());
                        },
                        SyntaxExpr::GuestBody { open, .. } => {
                            result.push_str(&open.to_string());
                        },
                        SyntaxExpr::Param(ident) => {
                            let ident_text = ident.to_string();
                            if let Some(Pattern::Term(PatternTerm::Lambda { binder, body })) =
                                current_lambda
                            {
                                if ident_text == binder.to_string() {
                                    result.push_str(&ident_text);
                                    continue;
                                }
                                jobs.push(PatternRenderJob::ApplySyntax {
                                    syntax,
                                    args,
                                    bp,
                                    expr_index,
                                    arg_index,
                                    slot,
                                    current_lambda: None,
                                });
                                jobs.push(PatternRenderJob::Pattern(body, 0));
                                break;
                            }
                            let Some(argument) = args.get(arg_index) else {
                                continue;
                            };
                            arg_index += 1;
                            let inherited = child_min_bp(bp, slot);
                            slot += 1;
                            if let Pattern::Term(PatternTerm::Lambda { binder, .. }) = argument {
                                current_lambda = Some(argument);
                                result.push_str(&binder.to_string());
                            } else {
                                jobs.push(PatternRenderJob::ApplySyntax {
                                    syntax,
                                    args,
                                    bp,
                                    expr_index,
                                    arg_index,
                                    slot,
                                    current_lambda,
                                });
                                jobs.push(PatternRenderJob::Pattern(argument, inherited));
                                break;
                            }
                        },
                        SyntaxExpr::Op(operation) => {
                            if let PatternOp::Sep { separator, source, .. } = operation {
                                if let Some(argument) = args.get(arg_index) {
                                    arg_index += 1;
                                    slot += 1;
                                    if source.is_some() {
                                        append_pattern_op_string(&mut result, operation);
                                        continue;
                                    }
                                    jobs.push(PatternRenderJob::ApplySyntax {
                                        syntax,
                                        args,
                                        bp,
                                        expr_index,
                                        arg_index,
                                        slot,
                                        current_lambda,
                                    });
                                    jobs.push(PatternRenderJob::CollectionWithSep {
                                        pattern: argument,
                                        separator,
                                    });
                                    break;
                                }
                            }
                            append_pattern_op_string(&mut result, operation);
                        },
                    }
                }
            },
            PatternRenderJob::Grammar {
                rule,
                args,
                bp,
                mut item_index,
                mut arg_index,
                mut slot,
            } => {
                while let Some(item) = rule.items.get(item_index) {
                    item_index += 1;
                    match item {
                        GrammarItem::Terminal(text) => result.push_str(text),
                        GrammarItem::NonTerminal { .. } => {
                            let Some(argument) = args.get(arg_index) else {
                                continue;
                            };
                            arg_index += 1;
                            let inherited = child_min_bp(bp, slot);
                            slot += 1;
                            jobs.push(PatternRenderJob::Grammar {
                                rule,
                                args,
                                bp,
                                item_index,
                                arg_index,
                                slot,
                            });
                            jobs.push(PatternRenderJob::Pattern(argument, inherited));
                            break;
                        },
                        GrammarItem::Collection { delimiters, .. } => {
                            let Some(argument) = args.get(arg_index) else {
                                continue;
                            };
                            arg_index += 1;
                            slot += 1;
                            jobs.push(PatternRenderJob::Grammar {
                                rule,
                                args,
                                bp,
                                item_index,
                                arg_index,
                                slot,
                            });
                            if let Some((open, close)) = delimiters {
                                result.push_str(open);
                                jobs.push(PatternRenderJob::Text(close));
                            }
                            jobs.push(PatternRenderJob::Pattern(argument, 0));
                            break;
                        },
                        GrammarItem::Binder { category } => {
                            result.push_str(&category.to_string().to_lowercase());
                        },
                    }
                }
            },
            PatternRenderJob::CollectionWithSep { pattern, separator } => match pattern {
                Pattern::Collection { elements, rest, .. } => {
                    if let Some(rest) = rest {
                        jobs.push(PatternRenderJob::Rest(rest));
                        if !elements.is_empty() {
                            jobs.push(PatternRenderJob::Separator(separator));
                        }
                    }
                    for (index, element) in elements.iter().enumerate().rev() {
                        jobs.push(PatternRenderJob::Pattern(element, 0));
                        if index != 0 {
                            jobs.push(PatternRenderJob::Separator(separator));
                        }
                    }
                },
                _ => jobs.push(PatternRenderJob::Pattern(pattern, 0)),
            },
        }
    }
    result
}

/// Convert a Pattern to user syntax at an inherited precedence threshold.
fn render_pattern(pattern: &Pattern, ctx: RenderCtx<'_>, min_bp: u8) -> String {
    drive_pattern_renderer(vec![PatternRenderJob::Pattern(pattern, min_bp)], ctx)
}

/// Generate LogicRelationDef array from logic block
fn generate_logic_relation_defs(language: &LanguageDef) -> TokenStream {
    let logic = match &language.logic {
        Some(l) => l,
        None => return quote! { &[] },
    };

    if logic.relations.is_empty() {
        return quote! { &[] };
    }

    let defs: Vec<TokenStream> = logic
        .relations
        .iter()
        .map(|rel| {
            let name = rel.name.to_string();
            let param_types = &rel.param_types;

            // Stage 3.27a (2026-05-04): emit description from RelationDecl
            // doc-comment when present. ascent_syntax_export currently does
            // not surface relation-level doc comments, so all paths route
            // through the `None` arm — but the wiring is in place for
            // when that gets extended.
            let description = match &rel.doc_comment {
                Some(text) => {
                    let lit = LitStr::new(text, rel.name.span());
                    quote! { Some(#lit) }
                },
                None => quote! { None },
            };

            quote! {
                mettail_runtime::LogicRelationDef {
                    name: #name,
                    param_types: &[#(#param_types),*],
                    description: #description,
                }
            }
        })
        .collect();

    quote! {
        &[#(#defs),*]
    }
}

/// Generate LogicRuleDef array from logic block
///
/// This extracts rules (non-relation declarations) from the logic content.
fn generate_logic_rule_defs(language: &LanguageDef) -> TokenStream {
    let logic = match &language.logic {
        Some(l) => l,
        None => return quote! { &[] },
    };

    // Extract rules from the token stream by splitting on semicolons
    // and filtering out relation declarations
    let content_str = logic.content.to_string();
    let rules: Vec<String> = content_str
        .split(';')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .filter(|s| !s.starts_with("relation "))
        .map(normalize_rule_whitespace)
        .collect();

    if rules.is_empty() {
        return quote! { &[] };
    }

    let defs: Vec<TokenStream> = rules
        .iter()
        .map(|rule| {
            quote! {
                mettail_runtime::LogicRuleDef {
                    rule: #rule,
                }
            }
        })
        .collect();

    quote! {
        &[#(#defs),*]
    }
}

/// Normalize whitespace in a rule string for display
fn normalize_rule_whitespace(s: &str) -> String {
    // Replace multiple whitespace with single space
    let normalized: String = s.split_whitespace().collect::<Vec<_>>().join(" ");
    // Clean up spacing around operators
    normalized
        .replace(" . ", ".")
        .replace(". ", ".")
        .replace(" .", ".")
        .replace("< - -", "<--")
        .replace("< --", "<--")
        .replace("< -", "<-")
}

// ═════════════════════════════════════════════════════════════════════════════
// Sim-B: Guard configuration metadata generators
// ═════════════════════════════════════════════════════════════════════════════
//
// Each generator reads from `language.guard_config` and emits an `&[…]`
// literal suitable for the corresponding `LanguageMetadata` trait method.
// When the `guards { }` block is absent (or the relevant sub-block is
// omitted), the generator emits `&[]`.

/// Generate the `BuiltinPredicateDef` array from direct predicate items
/// in `guards { }`.
fn generate_builtin_predicate_defs(language: &LanguageDef) -> TokenStream {
    let Some(gc) = language.guard_config.as_ref() else {
        return quote! { &[] };
    };
    let Some(preds) = gc.builtin_predicates.as_ref() else {
        return quote! { &[] };
    };

    let defs: Vec<TokenStream> = preds
        .iter()
        .map(|p| {
            let name_str = p.name.to_string();
            let name_lit = LitStr::new(&name_str, p.name.span());

            // Render the first syntax form (if any) using the existing
            // syntax-expression printer. When a predicate declares
            // alternative forms via `|`, we pick the first — this is a
            // best-effort summary, not a round-trippable rendering.
            let syntax_str = p
                .syntax_forms
                .first()
                .map(|form| {
                    form.iter()
                        .map(syntax_expr_to_display)
                        .collect::<Vec<_>>()
                        .join(" ")
                })
                .unwrap_or_default();
            let syntax_lit = LitStr::new(&syntax_str, Span::call_site());

            let selectivity = match p.annotations.selectivity {
                Some(s) => quote! { Some(#s) },
                None => quote! { None },
            };
            let cost = match p.annotations.cost {
                Some(c) => quote! { Some(#c) },
                None => quote! { None },
            };

            quote! {
                mettail_runtime::BuiltinPredicateDef {
                    name: #name_lit,
                    syntax: #syntax_lit,
                    selectivity: #selectivity,
                    cost: #cost,
                }
            }
        })
        .collect();

    quote! { &[#(#defs),*] }
}

/// Render a syntax expression as a plain string for the
/// `BuiltinPredicateDef.syntax` field.
fn syntax_expr_to_display(expr: &SyntaxExpr) -> String {
    match expr {
        SyntaxExpr::Literal(s) => format!("\"{}\"", s),
        SyntaxExpr::Param(id) => id.to_string(),
        SyntaxExpr::Op(_) => "#op".to_string(),
        SyntaxExpr::TokenKind { name, bind } => match bind {
            Some(b) => format!("{}@{}", b, name),
            None => name.to_string(),
        },
        SyntaxExpr::GuestBody { open, close, bind, kind } => {
            format!("*{}({},{},{})", kind.intrinsic(), bind, open, close)
        },
    }
}

/// Generate the `TheoryDef` array from `guards { theories { } }`.
fn generate_theory_defs(language: &LanguageDef) -> TokenStream {
    let Some(gc) = language.guard_config.as_ref() else {
        return quote! { &[] };
    };
    if gc.theories.is_empty() {
        return quote! { &[] };
    }

    let defs: Vec<TokenStream> = gc
        .theories
        .iter()
        .map(|t| {
            let name_str = t.name.to_string();
            let name_lit = LitStr::new(&name_str, t.name.span());

            let theory_type_str = {
                let ty = &t.theory_type;
                quote!(#ty).to_string()
            };
            let theory_type_lit = LitStr::new(&theory_type_str, Span::call_site());

            let handled_tokens: Vec<TokenStream> = match &t.handled_types {
                Some(cats) => cats
                    .iter()
                    .map(|c| {
                        let c_str = c.to_string();
                        let c_lit = LitStr::new(&c_str, c.span());
                        quote! { #c_lit }
                    })
                    .collect(),
                None => Vec::new(),
            };

            quote! {
                mettail_runtime::TheoryDef {
                    name: #name_lit,
                    theory_type: #theory_type_lit,
                    handled_types: &[#(#handled_tokens),*],
                }
            }
        })
        .collect();

    quote! { &[#(#defs),*] }
}

/// Generate the `ChannelDef` array from `guards { channels { channel … } }`.
fn generate_channel_defs(language: &LanguageDef) -> TokenStream {
    let Some(gc) = language.guard_config.as_ref() else {
        return quote! { &[] };
    };
    let Some(channels) = gc.channels.as_ref() else {
        return quote! { &[] };
    };

    let defs: Vec<TokenStream> = channels
        .channel_categories
        .iter()
        .map(|c| {
            let cat_str = c.category.to_string();
            let cat_lit = LitStr::new(&cat_str, c.category.span());
            quote! {
                mettail_runtime::ChannelDef { category: #cat_lit }
            }
        })
        .collect();

    quote! { &[#(#defs),*] }
}

/// Generate the `JoinPatternDef` array from `guards { channels { join … } }`.
fn generate_join_pattern_defs(language: &LanguageDef) -> TokenStream {
    let Some(gc) = language.guard_config.as_ref() else {
        return quote! { &[] };
    };
    let Some(channels) = gc.channels.as_ref() else {
        return quote! { &[] };
    };

    let defs: Vec<TokenStream> = channels
        .join_patterns
        .iter()
        .map(|jp| {
            let label_str = jp.label.to_string();
            let label_lit = LitStr::new(&label_str, jp.label.span());

            let cat_tokens: Vec<TokenStream> = jp
                .channel_params
                .iter()
                .map(|cp| {
                    let cat_str = cp.category.to_string();
                    let cat_lit = LitStr::new(&cat_str, cp.category.span());
                    quote! { #cat_lit }
                })
                .collect();

            quote! {
                mettail_runtime::JoinPatternDef {
                    label: #label_lit,
                    channel_categories: &[#(#cat_tokens),*],
                }
            }
        })
        .collect();

    quote! { &[#(#defs),*] }
}

/// Generate the `ConnectiveDef` array from `guards { connectives { } }`.
fn generate_connective_defs(language: &LanguageDef) -> TokenStream {
    let Some(gc) = language.guard_config.as_ref() else {
        return quote! { &[] };
    };
    let Some(decls) = gc.connectives.as_ref() else {
        return quote! { &[] };
    };

    let defs: Vec<TokenStream> = decls
        .iter()
        .map(|decl| {
            let role_str = decl.role.as_str();
            let role_lit = LitStr::new(role_str, Span::call_site());

            let kw_tokens: Vec<TokenStream> = decl
                .keywords
                .iter()
                .map(|kw| {
                    let kw_lit = LitStr::new(kw, Span::call_site());
                    quote! { #kw_lit }
                })
                .collect();

            quote! {
                mettail_runtime::ConnectiveDef {
                    role: #role_lit,
                    keywords: &[#(#kw_tokens),*],
                }
            }
        })
        .collect();

    quote! { &[#(#defs),*] }
}

#[cfg(test)]
#[path = "../../../tests/support/metadata_recursive_oracle.rs"]
mod metadata_recursive_oracle;

#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro2::Span;

    #[test]
    fn collection_type_name_distinguishes_hashmap_from_hashbag() {
        assert_eq!(collection_type_name(&CollectionType::HashBag), "HashBag");
        assert_eq!(collection_type_name(&CollectionType::HashMap), "HashMap");
    }

    #[test]
    fn type_expr_to_string_renders_hashmap_collection() {
        let elem = syn::Ident::new("Proc", Span::call_site());
        let ty = TypeExpr::Collection {
            coll_type: CollectionType::HashMap,
            element: Box::new(TypeExpr::Base(elem)),
        };
        assert_eq!(type_expr_to_string(&ty), "HashMap(Proc)");
    }

    #[test]
    fn metadata_embeds_checked_source_neutral_semantic_artifacts() {
        let language: LanguageDef = syn::parse_str(
            r#"
                name: MetadataArtifact,
                types { Proc },
                terms {
                    Zero . |- "0" : Proc;
                    Pair . left:Proc, right:Proc |- "(" left "," right ")" : Proc;
                },
                equations {},
                rewrites {},
            "#,
        )
        .expect("metadata artifact fixture must parse");
        let methods = generate_semantic_artifact_methods(&language).to_string();
        assert!(methods.contains("generated_semantic_artifacts_v1"));
        assert!(methods.contains("grammar_core_postcard"));
        assert!(methods.contains("semantic_signature_postcard"));
        assert!(methods.contains("semantic_machine_image"));
        assert!(methods.contains("GeneratedSemanticKeyAbiV1 :: StructuralV2"));
        assert!(!methods.contains("generated_semantic_artifact_refusal_v1"));
    }

    #[test]
    fn rewrite_metadata_marks_synthetic_injection_guard_as_guarded() {
        let proc = syn::Ident::new("Proc", Span::call_site());
        let p = syn::Ident::new("P", Span::call_site());
        let rw = RewriteRule {
            name: syn::Ident::new("NormCastProcToProcInProc", Span::call_site()),
            type_context: Vec::new(),
            premises: vec![Premise::SyntheticInjGuard {
                inner_var: p.clone(),
                source_category: proc.clone(),
                excluded_variants: vec![syn::Ident::new("PWrap", Span::call_site())],
            }],
            left: Pattern::Term(PatternTerm::Var(p.clone())),
            right: Pattern::Term(PatternTerm::Var(p)),
            is_auto_injected: true,
        };
        let language = LanguageDef {
            name: syn::Ident::new("TestLang", Span::call_site()),
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
            terms: Vec::new(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        };

        let bp = build_reflection_bp(&language)
            .expect("a fixture with no `options` block cannot make the bridge refuse");
        let rendered = generate_rewrite_def(&rw, 0, &language, &bp).to_string();
        assert!(
            rendered.contains("is_guarded : true"),
            "synthetic injection guards must be visible in metadata: {}",
            rendered
        );
        assert!(
            rendered.contains("synthetic_inj_guard"),
            "metadata should retain the synthetic guard condition display: {}",
            rendered
        );
    }

    // ═══════════════════════════════════════════════════════════════════════
    // Task #97 RED — the reflected equational theory can express BRACKETING
    // ═══════════════════════════════════════════════════════════════════════
    //
    // Monoid's associativity axiom is `(X*Y)*Z = X*(Y*Z)`. Its entire content is
    // where the brackets go, so a renderer with no precedence model reflects it
    // as `X*Y*Z = X*Y*Z` — a tautology, and the one rule in the corpus for which
    // being uninformative is indistinguishable from being wrong.
    //
    // The cells below assert over the SHIPPED spec (`languages/src/monoid.rs`,
    // read through the derived corpus) rather than a hand-built replica, so a
    // cell cannot pass against a grammar the repository does not contain.

    /// Monoid's three equations, rendered by the reflection renderer, keyed by
    /// the equation's declared name.
    fn monoid_equation_renderings() -> std::collections::HashMap<String, (String, String)> {
        let monoid = crate::gen::capture::bundled_corpus::bundled_language("Monoid");
        let bp = build_reflection_bp(&monoid.def)
            .expect("`languages/src/monoid.rs` is a shipped grammar, so its bridge converts");
        monoid
            .def
            .equations
            .iter()
            .map(|eq| {
                (
                    eq.name.to_string(),
                    (
                        pattern_to_user_syntax(&eq.left, &monoid.def, &bp),
                        pattern_to_user_syntax(&eq.right, &monoid.def, &bp),
                    ),
                )
            })
            .collect()
    }

    /// ★ THE MUTATION CELL. `Assoc`'s right-nested side brackets its operand, so
    /// the axiom no longer reflects as a tautology.
    ///
    /// ⚠ The assertion is pinned to the SUBSTRING `(Y*Z)`, never to
    /// `assert_ne!(lhs, rhs)` on whole strings: a whole-string `assert_ne!`
    /// passes on any incidental difference and is the vacuity mode that has
    /// already bitten this campaign.
    #[test]
    fn the_associativity_axiom_reflects_its_bracketing() {
        let renderings = monoid_equation_renderings();
        let (lhs, rhs) = renderings
            .get("Assoc")
            .expect("`languages/src/monoid.rs` declares an equation named `Assoc`");

        assert!(
            rhs.contains("(Y*Z)"),
            "the RIGHT-nested side must bracket its operand: `Mul` is left-associative \
             (left_bp 2, right_bp 3), so a `Mul` sitting in a right operand meets a \
             threshold above its own power and parenthesizes. Got rhs = {rhs}",
        );

        // ★ And the LEFT-nested side must NOT bracket. `X*Y*Z` already means
        // `(X*Y)*Z` for a left-associative `*`; bracketing it would be a SECOND
        // precedence model, disagreeing with the generated `Display` about a
        // string that needs no bracket. This half of the cell is what keeps the
        // repair from over-parenthesising its way to a passing `lhs != rhs`.
        assert_eq!(
            lhs, "X*Y*Z",
            "the LEFT-nested side of a left-associative operator needs no bracket. \
             Got lhs = {lhs}",
        );

        assert_ne!(lhs, rhs, "and therefore the axiom is no longer a tautology: {lhs} = {rhs}",);
    }

    /// ANTI-VACUITY for the cell above: the two sides really are DIFFERENT
    /// patterns. If `Assoc` were declared with two identical sides, the cell
    /// above would be asserting something the repair did not cause.
    #[test]
    fn the_associativity_axiom_really_does_nest_its_two_sides_differently() {
        let monoid = crate::gen::capture::bundled_corpus::bundled_language("Monoid");
        let assoc = monoid
            .def
            .equations
            .iter()
            .find(|eq| eq.name == "Assoc")
            .expect("`languages/src/monoid.rs` declares `Assoc`");

        // LHS is `(Mul (Mul X Y) Z)`: its FIRST argument is an application.
        // RHS is `(Mul X (Mul Y Z))`: its SECOND is.
        fn nested_arg_index(pattern: &Pattern) -> Option<usize> {
            let Pattern::Term(PatternTerm::Apply { args, .. }) = pattern else {
                return None;
            };
            args.iter()
                .position(|a| matches!(a, Pattern::Term(PatternTerm::Apply { .. })))
        }
        assert_eq!(
            nested_arg_index(&assoc.left),
            Some(0),
            "`Assoc`'s left side must be LEFT-nested",
        );
        assert_eq!(
            nested_arg_index(&assoc.right),
            Some(1),
            "`Assoc`'s right side must be RIGHT-nested",
        );
    }

    /// CONTROL for the precedence repair — a flat, single-level term gains NO
    /// parenthesis. An over-parenthesising renderer would reach `lhs != rhs` for
    /// `Assoc` and turn this cell red at the same time, which is exactly what a
    /// control is for.
    #[test]
    fn a_flat_term_gains_no_parenthesis() {
        let renderings = monoid_equation_renderings();
        for name in ["UnitL", "UnitR"] {
            let (lhs, rhs) = renderings
                .get(name)
                .unwrap_or_else(|| panic!("`languages/src/monoid.rs` declares `{name}`"));
            assert!(
                !lhs.contains('(') && !lhs.contains(')'),
                "`{name}`'s left side is a single `Mul` at the top level; nothing encloses \
                 it, so nothing can require a bracket. Got: {lhs}",
            );
            assert_eq!(
                rhs, "X",
                "`{name}`'s right side is the bare metavariable `X`, which neither \
                 precedence nor constructor resolution can touch. Got: {rhs}",
            );
        }
    }

    /// ★ THE SECOND MUTATION CELL (#97 item 2) — a bare identifier that names a
    /// NULLARY CONSTRUCTOR reflects as that constructor's SURFACE, not as its
    /// label.
    ///
    /// Monoid declares `Unit . M ::= "e" ;`, so `(Mul Unit X)` is written `e*X`.
    /// The renderer used to emit the label `Unit`, which is not a string any user
    /// can write, while the rest of the system already resolved the same node by
    /// name (`PatternTerm::is_ground_pattern` → `LanguageDef::get_constructor`).
    #[test]
    fn a_nullary_constructor_reflects_as_its_surface_not_its_label() {
        let renderings = monoid_equation_renderings();
        let (lhs, _) = renderings.get("UnitL").expect("Monoid declares `UnitL`");
        assert_eq!(
            lhs, "e*X",
            "`Unit` is declared `Unit . M ::= \"e\" ;`, so it reflects as `e`. Got: {lhs}",
        );
    }

    /// CONTROL for the constructor-resolution repair — a side whose leaves are
    /// all METAVARIABLES must be untouched by it. `Assoc` names `X`, `Y`, `Z`,
    /// none of which is a constructor, so its left side is byte-identical before
    /// and after.
    #[test]
    fn metavariables_are_not_resolved_against_the_constructor_table() {
        let renderings = monoid_equation_renderings();
        let (lhs, _) = renderings.get("Assoc").expect("Monoid declares `Assoc`");
        assert_eq!(
            lhs, "X*Y*Z",
            "`X`, `Y` and `Z` name no constructor, so constructor resolution must leave \
             them alone. Got: {lhs}",
        );
    }

    /// The reflected equation can now say WHICH equation it is (#97 item 4).
    #[test]
    fn the_reflected_equation_carries_its_name() {
        let monoid = crate::gen::capture::bundled_corpus::bundled_language("Monoid");
        let assoc = monoid
            .def
            .equations
            .iter()
            .find(|eq| eq.name == "Assoc")
            .expect("Monoid declares `Assoc`");
        let bp = build_reflection_bp(&monoid.def).expect("Monoid's bridge converts");
        let rendered = generate_equation_def(assoc, &monoid.def, &bp).to_string();
        assert!(
            rendered.contains("name : \"Assoc\""),
            "an `EquationDef` must carry the equation's declared name, as `RewriteDef` \
             always has. Got: {rendered}",
        );
    }

    // ═══════════════════════════════════════════════════════════════════════
    // THE CORPUS GATE — no reflected rule is vacuous without a REASON
    // ═══════════════════════════════════════════════════════════════════════

    /// ★ THE ANTI-VACUITY GATE over the whole corpus: no reflected equation or
    /// rewrite renders its two sides identically UNLESS the two sides genuinely
    /// have the same surface.
    ///
    /// # The declared exemption, and why it is a reason rather than a skip
    ///
    /// Thirteen auto-injected `NormCast<S>To<T>In<R>` rewrites render
    /// `lhs: "v", rhs: "v"`. Their shape is
    /// `(Cast<S> v) ~> (Cast<T> (<S>To<T> v))`, and every constructor in it is
    /// DISPLAY-TRANSPARENT: an injection adds no notation, so the surface really
    /// is `v` on both sides. Rendering a constructor there would invent a
    /// notation nobody can write and would contradict the generated `Display`,
    /// which is transparent for the same node. What such a rule is identified by
    /// is its NAME — `RewriteDef::name` has always carried one, and `EquationDef`
    /// now does too — so the reflection does say which retagging it is.
    ///
    /// The exemption is therefore not a list of thirteen labels but the
    /// structural property [`equal_modulo_transparent`]: two sides may render
    /// identically exactly when they ARE identical once transparent wrappers are
    /// erased. Monoid's `Assoc` does not satisfy it — its two sides differ in
    /// nesting, not in wrappers — so this gate was RED on `Assoc` before the
    /// precedence repair and is green after it.
    #[test]
    fn no_reflected_rule_is_vacuous_without_a_structural_reason() {
        let mut rules_checked = 0usize;
        let mut exempt = 0usize;
        let mut vacuous: Vec<String> = Vec::new();
        let languages = crate::gen::capture::bundled_corpus::bundled_languages();
        assert!(
            !languages.is_empty(),
            "the manifest-derived bundled-language corpus cannot be empty",
        );
        let expected_rules = languages
            .iter()
            .map(|language| language.def.equations.len() + language.def.rewrites.len())
            .sum::<usize>();
        assert!(
            expected_rules > 0,
            "the bundled-language corpus contains no reflected equations or rewrites",
        );

        for language in languages {
            let def = &language.def;
            let bp = build_reflection_bp(def).unwrap_or_else(|rejection| {
                panic!(
                    "{} is a SHIPPED grammar; the reflection's binding-power table must \
                     build for it: {rejection}",
                    language.tag,
                )
            });
            let sides: Vec<(String, &Pattern, &Pattern)> = def
                .equations
                .iter()
                .map(|eq| (format!("equation `{}`", eq.name), &eq.left, &eq.right))
                .chain(
                    def.rewrites
                        .iter()
                        .map(|rw| (format!("rewrite `{}`", rw.name), &rw.left, &rw.right)),
                )
                .collect();

            for (what, left, right) in sides {
                rules_checked += 1;
                let lhs = pattern_to_user_syntax(left, def, &bp);
                let rhs = pattern_to_user_syntax(right, def, &bp);
                if lhs != rhs {
                    continue;
                }
                if metadata_recursive_oracle::equal_modulo_transparent(left, right, def) {
                    exempt += 1;
                    continue;
                }
                vacuous.push(format!(
                    "{}: {what} reflects as `{lhs}` = `{rhs}` — identical surfaces that are \
                     NOT the same pattern once display-transparent wrappers are erased, so \
                     the reflection has lost the rule's content",
                    language.tag,
                ));
            }
        }

        // Structural non-vacuity: the walk must visit exactly the rule population derived from
        // the manifest-owned definitions. A transcribed numeric floor became stale when
        // Rholang's one-evaluator convergence removed 70 method-specific congruences.
        assert_eq!(
            rules_checked, expected_rules,
            "the reflection gate did not visit every equation and rewrite in its derived corpus",
        );
        // And the exemption is REACHED: if it were not, the structural predicate
        // would be untested and could silently stop matching the class it exists
        // to describe.
        assert!(
            exempt > 0,
            "the display-transparent exemption matched NOTHING. The auto-injected \
             `NormCast*` family is supposed to reach it, so either the family stopped \
             being generated or `equal_modulo_transparent` stopped recognising it — in \
             which case the exemption is an untested branch",
        );
        assert!(
            vacuous.is_empty(),
            "{} of {rules_checked} reflected rule(s) are vacuous with no structural \
             reason:\n\n{}",
            vacuous.len(),
            vacuous.join("\n"),
        );
    }

    // ═══════════════════════════════════════════════════════════════════════
    // #141 Part A RED — the reflection REFUSES; it does not render bracket-free
    // ═══════════════════════════════════════════════════════════════════════
    //
    // `build_bp_lookup` became fallible in `042476d9` and its doc-comment says why
    // an empty table must not be substituted for its refusal. `d71555ef` wired
    // this renderer to it with `Err(_) => BpLookup::empty()` anyway — a fails-open
    // fallback on a refusal path. With an empty table NOTHING is
    // precedence-governed, so every operator renders unbracketed and Monoid's
    // associativity axiom comes back as the tautology `X*Y*Z = X*Y*Z`: the exact
    // wrong answer `d71555ef` exists to remove, published through
    // `LanguageMetadata::equations`, with no diagnostic anywhere in the build.
    //
    // ⚠ These cells do NOT expect a panic (no `#[should_panic]`, no
    // `catch_unwind`); they read the value the generator returns.

    /// Monoid, plus one `options { }` value the shared bridge cannot decode.
    ///
    /// `beam_width` accepts the keywords the bridge enumerates; `aggressive` is
    /// not among them, and `prattail_bridge`'s own
    /// `an_out_of_domain_option_value_refuses_instead_of_asserting` pins that same
    /// pair. Using a value that fails IN THE BRIDGE — rather than one this module
    /// invents — is what makes this cell exercise the real refusal.
    fn monoid_with_an_undecodable_option() -> LanguageDef {
        let mut def = crate::gen::capture::bundled_corpus::bundled_language("Monoid").def;
        def.options.insert(
            "beam_width".to_string(),
            mettail_ast::language::AttributeValue::Keyword("aggressive".to_string()),
        );
        def
    }

    /// ★ THE MUTATION CELL. An undecodable `options` value produces a DIAGNOSTIC
    /// that names the language and the option — not an empty lookup.
    #[test]
    fn an_undecodable_option_refuses_the_reflection_instead_of_rendering_it_bracket_free() {
        let mutated = monoid_with_an_undecodable_option();
        let control = crate::gen::capture::bundled_corpus::bundled_language("Monoid").def;

        // ── the mutation really was applied, and is the ONLY difference ──
        assert!(
            !control.options.contains_key("beam_width"),
            "the control fixture must not already carry the mutated option, or the two \
             fixtures differ in nothing",
        );
        assert!(
            matches!(
                mutated.options.get("beam_width"),
                Some(mettail_ast::language::AttributeValue::Keyword(kw)) if kw == "aggressive",
            ),
            "the mutation must be present in the fixture handed to the generator",
        );
        assert_eq!(
            mutated.equations.len(),
            control.equations.len(),
            "the mutation changes an OPTION, never the equations being reflected",
        );

        let rejection = generate_metadata(&mutated, "", &[]).expect_err(
            "an `options` value the bridge cannot decode must REFUSE the reflection: \
             rendering it through an empty binding-power table emits no parenthesis \
             anywhere, which turns the associativity axiom into a tautology",
        );

        // ── pinned to specific tokens, never a whole-string `assert_ne!` ──
        assert!(
            rejection.contains("Monoid"),
            "the diagnostic must name the LANGUAGE it refused — one `rustc` process \
             expands every bundled grammar: {rejection}",
        );
        assert!(
            rejection.contains("beam_width"),
            "the diagnostic must name the OPTION whose value it could not decode: \
             {rejection}",
        );
        assert!(
            rejection.contains("the keyword `aggressive`"),
            "the bridge's own description of the offending SHAPE must survive the hop \
             to this generator, not be replaced by a summary: {rejection}",
        );
        assert!(
            rejection.contains("reflected equational theory"),
            "and the diagnostic must say WHICH generator refused, since `Display` \
             codegen refuses on the same bridge for the same value: {rejection}",
        );
    }

    /// ★ THE CONTROL, which must NOT discriminate: unmutated Monoid still renders,
    /// and renders the SAME bytes as before this repair.
    ///
    /// The bracket in `rhs` is the load-bearing token. If threading the table down
    /// from `generate_metadata` had changed which table a side is rendered
    /// against, `X*(Y*Z)` would be the first thing to move — it is the one
    /// rendering in the corpus that exists only because the table is populated.
    #[test]
    fn a_well_formed_options_value_renders_the_same_bytes_as_before() {
        let monoid = crate::gen::capture::bundled_corpus::bundled_language("Monoid").def;
        let tokens = generate_metadata(&monoid, "", &[])
            .expect("`languages/src/monoid.rs` is shipped, so its reflection must render")
            .to_string();

        assert!(
            tokens.contains(r#"lhs : "X*Y*Z""#),
            "the LEFT-nested side of a left-associative `*` needs no bracket: {tokens}",
        );
        assert!(
            tokens.contains(r#"rhs : "X*(Y*Z)""#),
            "the RIGHT-nested side must still bracket — this is the byte that proves \
             the hoisted table is the SAME table the per-side calls built: {tokens}",
        );
        assert!(
            tokens.contains(r#"name : "Assoc""#),
            "and the reflected equation still says which equation it is: {tokens}",
        );
    }

    /// ★ THE DISCRIMINATION WITNESS — what the deleted fallback actually produced.
    ///
    /// This cell renders Monoid's associativity axiom through the very table the
    /// `Err(_) => BpLookup::empty()` arm substituted, and shows the answer is
    /// WRONG rather than degraded: both sides come back `X*Y*Z`, the tautology,
    /// and the two are equal. It is kept permanently so the argument for
    /// propagating the refusal is a measurement in the suite rather than a claim
    /// in a commit message.
    #[test]
    fn an_empty_binding_power_table_reflects_the_axiom_as_a_tautology() {
        let monoid = crate::gen::capture::bundled_corpus::bundled_language("Monoid").def;
        let assoc = monoid
            .equations
            .iter()
            .find(|eq| eq.name == "Assoc")
            .expect("Monoid declares `Assoc`");
        let empty = crate::gen::syntax::display::BpLookup::empty();

        let lhs = pattern_to_user_syntax(&assoc.left, &monoid, &empty);
        let rhs = pattern_to_user_syntax(&assoc.right, &monoid, &empty);

        assert_eq!(
            rhs, "X*Y*Z",
            "an empty table makes NOTHING precedence-governed, so the right-nested side \
             loses the bracket that is the axiom's entire content. Got: {rhs}",
        );
        assert_eq!(
            lhs, rhs,
            "…and the axiom therefore reflects as a tautology. This is the answer the \
             fails-open fallback published; it is wrong, not merely unhelpful",
        );

        // And the populated table — the one the generator now insists on — does not.
        let bp = build_reflection_bp(&monoid).expect("Monoid's bridge converts");
        assert_eq!(
            pattern_to_user_syntax(&assoc.right, &monoid, &bp),
            "X*(Y*Z)",
            "the real table brackets it",
        );
    }

    /// ANTI-VACUITY for the mutation cell: the refusal must come from the OPTION,
    /// not from anything else about the fixture. The same fixture minus the
    /// mutation converts.
    #[test]
    fn the_refusal_is_caused_by_the_option_and_by_nothing_else() {
        let control = crate::gen::capture::bundled_corpus::bundled_language("Monoid").def;
        assert!(
            build_reflection_bp(&control).is_ok(),
            "unmutated Monoid must build its table — otherwise the mutation cell proves \
             only that this generator refuses everything",
        );
        assert!(
            build_reflection_bp(&monoid_with_an_undecodable_option()).is_err(),
            "and the mutated twin must not",
        );
    }
}
