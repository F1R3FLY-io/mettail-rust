//! Environment type generation for theory definitions
//!
//! Generates per-category environment types and a combined environment struct
//! for storing named term bindings in the REPL.
//!
//! Uses `IndexMap` to preserve insertion order for consistent display.
//!
//! ## Generated Types
//!
//! For a theory with `types { Proc; Name; }`:
//!
//! ```rust,ignore
//! // Per-category environments (preserves insertion order)
//! pub struct ProcEnv(pub IndexMap<String, Proc>);
//! pub struct NameEnv(pub IndexMap<String, Name>);
//!
//! // Combined environment
//! pub struct RhoCalcEnv {
//!     pub proc: ProcEnv,
//!     pub name: NameEnv,
//!     pub comments: HashMap<String, String>,  // Optional comments per binding
//! }
//! ```
//!
//! ## Usage
//!
//! ```rust,ignore
//! let mut env = RhoCalcEnv::new();
//! env.proc.set("p".to_string(), some_proc);
//! env.comments.insert("p".to_string(), "My comment".to_string());
//! let substituted = term.substitute_env(&env);
//! ```

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::ast::language::LanguageDef;

/// Generate environment types for all exported categories
pub fn generate_environments(language: &LanguageDef) -> TokenStream {
    let language_name = &language.name;
    
    // Filter to only categories without native types (native types like i32 don't have variables)
    let categories: Vec<_> = language.types.iter()
        .filter(|t| t.native_type.is_none())
        .collect();
    
    if categories.is_empty() {
        return quote! {};
    }
    
    // Generate per-category environment structs
    let category_envs: Vec<TokenStream> = categories.iter().map(|lang_type| {
        let cat_name = &lang_type.name;
        let env_name = format_ident!("{}Env", cat_name);
        
        quote! {
            /// Per-category environment for storing named term bindings (preserves insertion order)
            #[derive(Debug, Clone, Default)]
            pub struct #env_name(pub indexmap::IndexMap<String, #cat_name>);
            
            impl #env_name {
                /// Create a new empty environment
                pub fn new() -> Self {
                    Self(indexmap::IndexMap::new())
                }
                
                /// Get a term by name
                pub fn get(&self, name: &str) -> Option<&#cat_name> {
                    self.0.get(name)
                }
                
                /// Set a term binding (maintains insertion order for new entries)
                pub fn set(&mut self, name: String, value: #cat_name) {
                    self.0.insert(name, value);
                }
                
                /// Remove a term binding (maintains order of remaining entries)
                pub fn remove(&mut self, name: &str) -> Option<#cat_name> {
                    self.0.shift_remove(name)
                }
                
                /// Iterate over all bindings in insertion order
                pub fn iter(&self) -> impl Iterator<Item = (&String, &#cat_name)> {
                    self.0.iter()
                }
                
                /// Check if environment is empty
                pub fn is_empty(&self) -> bool {
                    self.0.is_empty()
                }
                
                /// Get the number of bindings
                pub fn len(&self) -> usize {
                    self.0.len()
                }
                
                /// Clear all bindings
                pub fn clear(&mut self) {
                    self.0.clear()
                }
            }
        }
    }).collect();
    
    // Generate combined environment struct
    let env_struct_name = format_ident!("{}Env", language_name);
    
    let field_defs: Vec<TokenStream> = categories.iter().map(|lang_type| {
        let cat_name = &lang_type.name;
        let field_name = format_ident!("{}", cat_name.to_string().to_lowercase());
        let env_name = format_ident!("{}Env", cat_name);
        
        quote! {
            pub #field_name: #env_name
        }
    }).collect();
    
    let field_defaults: Vec<TokenStream> = categories.iter().map(|lang_type| {
        let cat_name = &lang_type.name;
        let field_name = format_ident!("{}", cat_name.to_string().to_lowercase());
        let env_name = format_ident!("{}Env", cat_name);
        
        quote! {
            #field_name: #env_name::new()
        }
    }).collect();
    
    let field_clears: Vec<TokenStream> = categories.iter().map(|lang_type| {
        let cat_name = &lang_type.name;
        let field_name = format_ident!("{}", cat_name.to_string().to_lowercase());
        
        quote! {
            self.#field_name.clear()
        }
    }).collect();
    
    let field_empty_checks: Vec<TokenStream> = categories.iter().map(|lang_type| {
        let cat_name = &lang_type.name;
        let field_name = format_ident!("{}", cat_name.to_string().to_lowercase());
        
        quote! {
            self.#field_name.is_empty()
        }
    }).collect();
    
    let combined_env = quote! {
        /// Combined environment for all categories in this theory
        #[derive(Debug, Clone, Default)]
        pub struct #env_struct_name {
            #(#field_defs),*,
            /// Optional comments for each binding (keyed by binding name)
            pub comments: std::collections::HashMap<String, String>,
        }
        
        impl #env_struct_name {
            /// Create a new empty environment
            pub fn new() -> Self {
                Self {
                    #(#field_defaults),*,
                    comments: std::collections::HashMap::new(),
                }
            }
            
            /// Clear all bindings from all categories
            pub fn clear(&mut self) {
                #(#field_clears);*;
                self.comments.clear();
            }
            
            /// Check if all environments are empty
            pub fn is_empty(&self) -> bool {
                #(#field_empty_checks)&&*
            }
            
            /// Set a comment for a binding
            pub fn set_comment(&mut self, name: &str, comment: String) {
                self.comments.insert(name.to_string(), comment);
            }
            
            /// Get the comment for a binding
            pub fn get_comment(&self, name: &str) -> Option<&String> {
                self.comments.get(name)
            }
            
            /// Remove a comment for a binding
            pub fn remove_comment(&mut self, name: &str) {
                self.comments.remove(name);
            }
        }
    };
    
    quote! {
        #(#category_envs)*
        
        #combined_env
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::language::{LanguageDef, LangType};
    use syn::parse_quote;

    #[test]
    fn test_generate_environments() {
        let language = LanguageDef {
            name: parse_quote!(RhoCalc),
            types: vec![
                LangType {
                    name: parse_quote!(Proc),
                    native_type: None,
                },
                LangType {
                    name: parse_quote!(Name),
                    native_type: None,
                },
            ],
            terms: vec![],
            equations: vec![],
            rewrites: vec![],
            semantics: vec![],
        };

        let output = generate_environments(&language);
        let output_str = output.to_string();

        // Check for per-category environments
        assert!(output_str.contains("ProcEnv"));
        assert!(output_str.contains("NameEnv"));
        
        // Check for combined environment
        assert!(output_str.contains("RhoCalcEnv"));
        
        // Check for field names
        assert!(output_str.contains("proc"));
        assert!(output_str.contains("name"));
        
        // Check for IndexMap usage (order preservation)
        assert!(output_str.contains("indexmap :: IndexMap"));
        
        // Check for comments field
        assert!(output_str.contains("comments"));
    }

    #[test]
    fn test_generate_environments_with_native_type() {
        // Native types should be excluded (they don't have variables)
        let language = LanguageDef {
            name: parse_quote!(Calculator),
            types: vec![
                LangType {
                    name: parse_quote!(Int),
                    native_type: Some(parse_quote!(i32)),
                },
            ],
            terms: vec![],
            equations: vec![],
            rewrites: vec![],
            semantics: vec![],
        };

        let output = generate_environments(&language);
        let output_str = output.to_string();

        // Should be empty since Int is a native type
        assert!(!output_str.contains("IntEnv"));
    }
}
