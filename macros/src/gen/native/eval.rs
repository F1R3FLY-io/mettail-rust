use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashMap;

/// Generate eval() method for native types
use crate::ast::grammar::{GrammarItem, GrammarRule, TermParam};
use crate::ast::language::{BuiltinOp, LanguageDef, SemanticOperation};
use crate::gen::native::native_type_to_string;
use crate::gen::{generate_literal_label, generate_var_label, is_integer_rule};

/// Extract parameter names from term_context in the same order as generated variant fields.
/// Used for rust_code eval arms: param names match constructor field names.
fn term_context_param_names(term_context: &[TermParam]) -> Vec<syn::Ident> {
    let mut names = Vec::new();
    for p in term_context {
        match p {
            TermParam::Simple { name, .. } => names.push(name.clone()),
            TermParam::Abstraction { binder, body, .. } => {
                names.push(binder.clone());
                names.push(body.clone());
            },
            TermParam::MultiAbstraction { binder, body, .. } => {
                names.push(binder.clone());
                names.push(body.clone());
            },
        }
    }
    names
}

pub fn generate_eval_method(language: &LanguageDef) -> TokenStream {
    let mut impls = Vec::new();

    for lang_type in &language.types {
        let category = &lang_type.name;

        // Only generate for native types
        let native_type = match lang_type.native_type.as_ref() {
            Some(ty) => ty,
            None => continue,
        };

        // Find all rules for this category
        let rules: Vec<&GrammarRule> = language
            .terms
            .iter()
            .filter(|r| r.category == *category)
            .collect();

        if rules.is_empty() {
            continue;
        }

        // Build map of constructor -> semantic operation
        // Skip rules that already have HOL Rust code blocks (they get their own eval arms)
        let mut semantics_map: HashMap<String, BuiltinOp> = HashMap::new();
        for semantic_rule in &language.semantics {
            if let Some(rule) = rules.iter().find(|r| r.label == semantic_rule.constructor) {
                if rule.category == *category && rule.rust_code.is_none() {
                    let SemanticOperation::Builtin(op) = &semantic_rule.operation;
                    semantics_map.insert(semantic_rule.constructor.to_string(), *op);
                }
            }
        }

        // Generate match arms
        let mut match_arms = Vec::new();

        // Check for existing rules
        let has_integer_rule = rules.iter().any(|rule| is_integer_rule(rule));

        // Add arm for auto-generated literal if no explicit Integer rule
        if !has_integer_rule {
            let literal_label = generate_literal_label(native_type);
            let type_str = native_type_to_string(native_type);
            // String is not Copy; use clone() for str/String
            let literal_arm = if type_str == "str" || type_str == "String" {
                quote! { #category::#literal_label(n) => n.clone(), }
            } else {
                quote! { #category::#literal_label(n) => *n, }
            };
            match_arms.push(literal_arm);
        }

        // Add arm for auto-generated Var variant if no explicit Var rule
        let var_label = generate_var_label(category);
        let panic_msg = format!(
            "Cannot evaluate {} - variables must be substituted via rewrites first",
            var_label
        );
        match_arms.push(quote! {
            #category::#var_label(_) => loop { panic!(#panic_msg) },
        });

        for rule in &rules {
            let label = &rule.label;
            let label_str = label.to_string();

            // Check if this is an Integer rule (literal with native type)
            if is_integer_rule(rule) {
                match_arms.push(quote! {
                    #category::#label(n) => *n,
                });
            }
            // HOL syntax: rule with Rust code block - generate eval from rust_code
            else if let Some(ref rust_code_block) = rule.rust_code {
                let param_names = rule
                    .term_context
                    .as_ref()
                    .map(|ctx| term_context_param_names(ctx))
                    .unwrap_or_default();
                let param_count = param_names.len();
                let param_bindings: Vec<_> = param_names
                    .iter()
                    .map(|name| quote! { let #name = #name.as_ref().eval(); })
                    .collect();
                let rust_code = &rust_code_block.code;
                let match_arm = match param_count {
                    0 => quote! {
                        #category::#label => (#rust_code),
                    },
                    1 => {
                        let p0 = &param_names[0];
                        quote! {
                            #category::#label(#p0) => {
                                #(#param_bindings)*
                                (#rust_code)
                            },
                        }
                    },
                    2 => {
                        let p0 = &param_names[0];
                        let p1 = &param_names[1];
                        quote! {
                            #category::#label(#p0, #p1) => {
                                #(#param_bindings)*
                                (#rust_code)
                            },
                        }
                    },
                    3 => {
                        let p0 = &param_names[0];
                        let p1 = &param_names[1];
                        let p2 = &param_names[2];
                        quote! {
                            #category::#label(#p0, #p1, #p2) => {
                                #(#param_bindings)*
                                (#rust_code)
                            },
                        }
                    },
                    _ => continue, // 4+ params: skip or extend later
                };
                match_arms.push(match_arm);
            }
            // Check if this has semantics (operator)
            else if let Some(op) = semantics_map.get(&label_str) {
                // Count non-terminal arguments (excluding terminals)
                let arg_count = rule
                    .items
                    .iter()
                    .filter(|item| matches!(item, GrammarItem::NonTerminal(_)))
                    .count();

                if arg_count == 2 {
                    // Binary operator
                    let op_token = match op {
                        BuiltinOp::Add => quote! { + },
                        BuiltinOp::Sub => quote! { - },
                        BuiltinOp::Mul => quote! { * },
                        BuiltinOp::Div => quote! { / },
                        BuiltinOp::Rem => quote! { % },
                        BuiltinOp::BitAnd => quote! { & },
                        BuiltinOp::BitOr => quote! { | },
                        BuiltinOp::BitXor => quote! { ^ },
                        BuiltinOp::Shl => quote! { << },
                        BuiltinOp::Shr => quote! { >> },
                    };

                    match_arms.push(quote! {
                        #category::#label(a, b) => a.as_ref().eval() #op_token b.as_ref().eval(),
                    });
                } else {
                    // Unary or other arity - skip for now
                    continue;
                }
            }
            // Handle rules with recursive self-reference and Var (like Assign . Int ::= Var "=" Int)
            // These evaluate to the value of the recursive argument
            else {
                // Find non-terminals in the rule
                let non_terminals: Vec<_> = rule
                    .items
                    .iter()
                    .filter_map(|item| match item {
                        GrammarItem::NonTerminal(nt) => Some(nt.to_string()),
                        _ => None,
                    })
                    .collect();

                // Check if this has Var and a recursive reference
                let has_var = non_terminals.iter().any(|nt| nt == "Var");
                let has_recursive = non_terminals.iter().any(|nt| *nt == category.to_string());

                if has_var && has_recursive {
                    // This is like Assign - evaluate the recursive part
                    // The constructor has (OrdVar, Box<T>) where T is the recursive part
                    // Need to dereference the Box to call eval()
                    match_arms.push(quote! {
                        #category::#label(_, expr) => expr.as_ref().eval(),
                    });
                }
                // Other constructors without semantics - skip
            }
        }

        if !match_arms.is_empty() {
            // str is unsized; use String as return type for eval()
            let return_type = if native_type_to_string(native_type) == "str" {
                quote! { std::string::String }
            } else {
                quote! { #native_type }
            };
            let impl_block = quote! {
                impl #category {
                    /// Evaluate the expression to its native type value.
                    /// Variables must be substituted via rewrites before evaluation.
                    pub fn eval(&self) -> #return_type {
                        match self {
                            #(#match_arms)*
                            _ => panic!("Cannot evaluate expression - contains unevaluated terms. Apply rewrites first."),
                        }
                    }
                }
            };
            impls.push(impl_block);
        }
    }

    quote! {
        #(#impls)*
    }
}
