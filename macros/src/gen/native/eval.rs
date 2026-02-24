use proc_macro2::TokenStream;
use quote::quote;

/// Generate eval() method for native types
use crate::ast::grammar::{GrammarItem, GrammarRule, TermParam};
use crate::ast::language::LanguageDef;
use crate::gen::native::native_type_to_string;
use crate::gen::{
    generate_literal_label, generate_var_label, is_literal_rule, literal_rule_nonterminal,
};

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

        // Find all rules for this category (may be empty for native types that only
        // get literal/Var from the grammar, e.g. Int with no explicit term rules)
        let rules: Vec<&GrammarRule> = language
            .terms
            .iter()
            .filter(|r| r.category == *category)
            .collect();

        // Literal label for try_fold_to_literal (resolve once)
        let has_literal_rule = rules.iter().any(|rule| is_literal_rule(rule));
        let literal_label = if has_literal_rule {
            rules
                .iter()
                .find(|r| is_literal_rule(r))
                .map(|r| r.label.clone())
                .unwrap_or_else(|| generate_literal_label(native_type))
        } else {
            generate_literal_label(native_type)
        };

        // Generate match arms for eval()
        let mut match_arms = Vec::new();

        // Add arm for auto-generated literal if no explicit literal rule
        if !has_literal_rule {
            let type_str = native_type_to_string(native_type);
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

        // Match arms for try_eval() -> Option<T> (Var and catch-all => None, rest => Some(...))
        let mut try_eval_arms: Vec<TokenStream> = Vec::new();

        if !has_literal_rule {
            let type_str = native_type_to_string(native_type);
            let try_literal_arm = if type_str == "str" || type_str == "String" {
                quote! { #category::#literal_label(n) => Some(n.clone()), }
            } else {
                quote! { #category::#literal_label(n) => Some(*n), }
            };
            try_eval_arms.push(try_literal_arm);
        }
        try_eval_arms.push(quote! {
            #category::#var_label(_) => None,
        });

        for rule in &rules {
            let label = &rule.label;

            // Literal rule: copy or clone depending on nonterminal (StringLiteral => clone)
            if is_literal_rule(rule) {
                let use_clone = literal_rule_nonterminal(rule).as_deref() == Some("StringLiteral");
                if use_clone {
                    match_arms.push(quote! {
                        #category::#label(n) => n.clone(),
                    });
                    try_eval_arms.push(quote! {
                        #category::#label(n) => Some(n.clone()),
                    });
                } else {
                    match_arms.push(quote! {
                        #category::#label(n) => *n,
                    });
                    try_eval_arms.push(quote! {
                        #category::#label(n) => Some(*n),
                    });
                }
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
                let try_param_bindings: Vec<_> = param_names
                    .iter()
                    .map(|name| quote! { let #name = #name.as_ref().try_eval()?; })
                    .collect();
                let rust_code = &rust_code_block.code;
                let match_arm = if param_count == 0 {
                    quote! {
                        #category::#label => (#rust_code),
                    }
                } else {
                    quote! {
                        #category::#label(#(#param_names),*) => {
                            #(#param_bindings)*
                            (#rust_code)
                        },
                    }
                };
                match_arms.push(match_arm);
                let try_arm = if param_count == 0 {
                    quote! { #category::#label => Some((#rust_code)), }
                } else {
                    quote! {
                        #category::#label(#(#param_names),*) => {
                            #(#try_param_bindings)*
                            Some((#rust_code))
                        },
                    }
                };
                try_eval_arms.push(try_arm);
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
                    match_arms.push(quote! {
                        #category::#label(_, expr) => expr.as_ref().eval(),
                    });
                    try_eval_arms.push(quote! {
                        #category::#label(_, expr) => expr.as_ref().try_eval(),
                    });
                }
            }
        }

        if !match_arms.is_empty() {
            let type_str = native_type_to_string(native_type);
            let return_type = if type_str == "str" || type_str == "String" {
                quote! { std::string::String }
            } else if type_str == "f32" {
                quote! { mettail_runtime::CanonicalFloat32 }
            } else if type_str == "f64" {
                quote! { mettail_runtime::CanonicalFloat64 }
            } else {
                quote! { #native_type }
            };
            try_eval_arms.push(quote! { _ => None, });
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
                    /// Like eval but returns None for unevaluable terms (e.g. Var) instead of panicking.
                    pub fn try_eval(&self) -> std::option::Option<#return_type> {
                        match self {
                            #(#try_eval_arms)*
                        }
                    }
                    /// If this term is fully evaluable, return its value as a literal; otherwise None.
                    pub fn try_fold_to_literal(&self) -> std::option::Option<Self> {
                        self.try_eval().map(|v| #category::#literal_label(v))
                    }
                }
            };
            impls.push(impl_block);

            // Implement arithmetic ops for numeric native types so rust_code in other categories
            // (e.g. Proc::Add with CastInt(a), CastInt(b) => a + b) can use +, -, etc. on term types.
            let type_str = native_type_to_string(native_type);
            let is_numeric = matches!(
                type_str.as_str(),
                "i32" | "i64" | "u32" | "u64" | "isize" | "usize" | "f32" | "f64"
            );
            if is_numeric {
                let ops_impl = quote! {
                    impl std::ops::Add for #category {
                        type Output = #category;
                        fn add(self, rhs: #category) -> #category {
                            #category::#literal_label(self.eval() + rhs.eval())
                        }
                    }
                    impl std::ops::Sub for #category {
                        type Output = #category;
                        fn sub(self, rhs: #category) -> #category {
                            #category::#literal_label(self.eval() - rhs.eval())
                        }
                    }
                    impl std::ops::Mul for #category {
                        type Output = #category;
                        fn mul(self, rhs: #category) -> #category {
                            #category::#literal_label(self.eval() * rhs.eval())
                        }
                    }
                    impl std::ops::Div for #category {
                        type Output = #category;
                        fn div(self, rhs: #category) -> #category {
                            #category::#literal_label(self.eval() / rhs.eval())
                        }
                    }
                    impl std::ops::Rem for #category {
                        type Output = #category;
                        fn rem(self, rhs: #category) -> #category {
                            #category::#literal_label(self.eval() % rhs.eval())
                        }
                    }
                };
                impls.push(ops_impl);
            }
        }
    }

    quote! {
        #(#impls)*
    }
}
