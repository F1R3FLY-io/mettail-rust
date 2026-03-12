//! Fragment definitions for reusable grammar building blocks.
//!
//! A fragment defines types + terms only (no equations/rewrites/logic — those are
//! language-specific). Multiple languages can mix in the same fragment via `mixins:`.
//!
//! ```ignore
//! language_fragment! {
//!     name: ArithOps,
//!     types { ![i32] as Int },
//!     terms {
//!         NumLit . |- Integer : Int;
//!         Add . a:Int, b:Int |- a "+" b : Int ![ a + b ] fold;
//!     }
//! }
//! ```

use std::collections::{HashMap, HashSet};

use syn::{
    parse::{Parse, ParseStream},
    Ident, Result as SynResult, Token,
};

use super::grammar::{parse_terms, GrammarItem, GrammarRule};
use super::language::{LangType, LanguageDef, ModeDef, TokenDef};

/// A reusable grammar fragment: types + tokens + terms.
pub struct FragmentDef {
    pub name: Ident,
    pub types: Vec<LangType>,
    /// Custom token definitions (merged into the consuming language's default mode).
    pub token_defs: Vec<TokenDef>,
    /// Named lexer modes (merged by name with the consuming language's modes).
    pub mode_defs: Vec<ModeDef>,
    pub terms: Vec<GrammarRule>,
}

impl Parse for FragmentDef {
    fn parse(input: ParseStream) -> SynResult<Self> {
        // Parse: name: Identifier
        let name_kw = input.parse::<Ident>()?;
        if name_kw != "name" {
            return Err(syn::Error::new(name_kw.span(), "expected 'name'"));
        }
        let _ = input.parse::<Token![:]>()?;
        let name = input.parse::<Ident>()?;
        let _ = input.parse::<Token![,]>()?;

        // Parse: types { ... }
        let types = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "types" {
                super::language::parse_types_public(input)?
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
        };

        // Parse: tokens { ... } (optional)
        let (token_defs, mode_defs) = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "tokens" {
                super::language::parse_tokens_public(input)?
            } else {
                (Vec::new(), Vec::new())
            }
        } else {
            (Vec::new(), Vec::new())
        };

        // Parse: terms { ... }
        let terms = if input.peek(Ident) {
            let lookahead = input.fork().parse::<Ident>()?;
            if lookahead == "terms" {
                parse_terms(input)?
            } else {
                Vec::new()
            }
        } else {
            Vec::new()
        };

        Ok(FragmentDef { name, types, token_defs, mode_defs, terms })
    }
}

impl FragmentDef {
    /// Convert this fragment into a partial `LanguageDef` for registry storage.
    /// Equations, rewrites, and logic are empty.
    pub fn to_language_def(&self) -> LanguageDef {
        LanguageDef {
            name: self.name.clone(),
            options: HashMap::new(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: self.types.clone(),
            token_defs: self.token_defs.clone(),
            mode_defs: self.mode_defs.clone(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms: self.terms.clone(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
        }
    }
}

/// Validate a fragment definition:
/// - All category references in terms must exist in the fragment's types
///   or be built-in types (Var, Integer, Boolean, etc.)
pub fn validate_fragment(frag: &FragmentDef) -> Result<(), String> {
    let type_names: HashSet<String> = frag.types.iter().map(|t| t.name.to_string()).collect();
    let defined_cats: HashSet<String> = frag.terms.iter().map(|r| r.category.to_string()).collect();

    // Built-in nonterminals that don't need declaration
    let builtins: HashSet<&str> = ["Var", "Integer", "Boolean", "StringLiteral", "FloatLiteral"]
        .iter()
        .copied()
        .collect();

    for rule in &frag.terms {
        // Check result category
        let cat = rule.category.to_string();
        if !type_names.contains(&cat) {
            return Err(format!(
                "Fragment '{}': rule '{}' produces category '{}' which is not declared in types",
                frag.name, rule.label, cat
            ));
        }

        // Check referenced categories in items
        for item in &rule.items {
            let ref_name = match item {
                GrammarItem::NonTerminal(ident) => ident.to_string(),
                GrammarItem::Binder { category } => category.to_string(),
                GrammarItem::Collection { element_type, .. } => element_type.to_string(),
                GrammarItem::Terminal(_) => continue,
            };
            if builtins.contains(ref_name.as_str()) {
                continue;
            }
            if !type_names.contains(&ref_name) && !defined_cats.contains(&ref_name) {
                return Err(format!(
                    "Fragment '{}': rule '{}' references category '{}' which is not declared",
                    frag.name, rule.label, ref_name
                ));
            }
        }
    }

    // Check for duplicate labels within the fragment
    let mut seen_labels: HashSet<String> = HashSet::new();
    for rule in &frag.terms {
        let label = rule.label.to_string();
        if !seen_labels.insert(label.clone()) {
            return Err(format!(
                "Fragment '{}': duplicate rule label '{}'",
                frag.name, label
            ));
        }
    }

    Ok(())
}
