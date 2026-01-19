//! Pattern types for rule specification
//!
//! Patterns are the rule specification language, used in both LHS and RHS
//! of equations and rewrite rules. They extend Term with collection metasyntax.
//!
//! Key types:
//! - `PatternTerm`: Mirrors `Term` but allows `Pattern` in sub-expression positions
//! - `Pattern`: Wraps `PatternTerm` plus collection metasyntax (Collection, Map, Zip)
//!
//! The interpretation of patterns differs by position:
//! - LHS: pattern matching, variable binding
//! - RHS: term construction

use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use super::term::Term;
use super::theory::TheoryDef;
use super::grammar::GrammarItem;

/// Term-like structure for rule specification.
/// Mirrors `Term` but allows `Pattern` in sub-expression positions.
/// This lets metasyntax (#map, #zip, etc.) appear anywhere in a term.
#[derive(Debug, Clone)]
pub enum PatternTerm {
    /// Variable (binds on LHS, references on RHS)
    Var(Ident),
    
    /// Constructor application: (Cons arg0 arg1 ...)
    /// Note: args are Pattern, allowing metasyntax in any position
    Apply {
        constructor: Ident,
        args: Vec<Pattern>,
    },
    
    /// Lambda: \x.body
    Lambda {
        binder: Ident,
        body: Box<Pattern>,
    },
    
    /// Multi-lambda: ^[x0,x1,...].body
    MultiLambda {
        binders: Vec<Ident>,
        body: Box<Pattern>,
    },
    
    /// Substitution: subst(term, var, replacement)
    Subst {
        term: Box<Pattern>,
        var: Ident,
        replacement: Box<Pattern>,
    },
    
    /// Multi-substitution: multisubst(scope, r0, r1, ...)
    MultiSubst {
        scope: Box<Pattern>,
        replacements: Vec<Pattern>,
    },
}

/// Pattern for rule specification (both LHS and RHS).
/// Wraps `PatternTerm` for "normal" patterns, adds metasyntax variants.
///
/// Interpretation differs by position:
/// - LHS: pattern matching, variable binding
/// - RHS: term construction
#[derive(Debug, Clone)]
pub enum Pattern {
    /// A term-like pattern (the common case)
    Term(PatternTerm),
    
    // --- Collection metasyntax ---
    
    /// Collection: {P, Q, ...rest}
    /// LHS: match elements, bind remainder to `rest`
    /// RHS: construct collection, merge with `rest`
    Collection {
        /// Constructor label (e.g., PPar) - inferred if not provided
        constructor: Option<Ident>,
        /// Elements in the collection (can be patterns)
        elements: Vec<Pattern>,
        /// If Some, binds/merges with the remainder
        rest: Option<Ident>,
    },
    
    /// Map: xs.#map(|x| body)
    /// LHS: for each x in xs (if xs bound), match body, extract unbound vars
    /// RHS: transform each element by body
    Map {
        /// The collection to map over
        collection: Box<Pattern>,
        /// Parameters for the map function
        params: Vec<Ident>,
        /// Body pattern to apply to each element
        body: Box<Pattern>,
    },
    
    /// Zip: #zip(xs, ys)
    /// LHS: if one unbound, search/join; if both bound, parallel iterate
    /// RHS: pair-wise combination
    Zip {
        /// Collections to zip together
        collections: Vec<Pattern>,
    },
}

// ============================================================================
// PatternTerm implementations
// ============================================================================

impl PatternTerm {
    /// Collect free variables in this pattern term
    pub fn free_vars(&self) -> HashSet<String> {
        match self {
            PatternTerm::Var(v) => {
                let mut set = HashSet::new();
                set.insert(v.to_string());
                set
            }
            PatternTerm::Apply { args, .. } => {
                let mut vars = HashSet::new();
                for arg in args {
                    vars.extend(arg.free_vars());
                }
                vars
            }
            PatternTerm::Lambda { binder, body } => {
                let mut vars = body.free_vars();
                vars.remove(&binder.to_string());
                vars
            }
            PatternTerm::MultiLambda { binders, body } => {
                let mut vars = body.free_vars();
                for binder in binders {
                    vars.remove(&binder.to_string());
                }
                vars
            }
            PatternTerm::Subst { term, var, replacement } => {
                let mut vars = term.free_vars();
                vars.insert(var.to_string());
                vars.extend(replacement.free_vars());
                vars
            }
            PatternTerm::MultiSubst { scope, replacements } => {
                let mut vars = scope.free_vars();
                for repl in replacements {
                    vars.extend(repl.free_vars());
                }
                vars
            }
        }
    }
    
    /// Check if this pattern term contains any metasyntax in its sub-patterns
    pub fn has_metasyntax(&self) -> bool {
        match self {
            PatternTerm::Var(_) => false,
            PatternTerm::Apply { args, .. } => args.iter().any(|a| a.has_metasyntax()),
            PatternTerm::Lambda { body, .. } => body.has_metasyntax(),
            PatternTerm::MultiLambda { body, .. } => body.has_metasyntax(),
            PatternTerm::Subst { term, replacement, .. } => {
                term.has_metasyntax() || replacement.has_metasyntax()
            }
            PatternTerm::MultiSubst { scope, replacements } => {
                scope.has_metasyntax() || replacements.iter().any(|r| r.has_metasyntax())
            }
        }
    }
}

// ============================================================================
// Pattern implementations
// ============================================================================

impl Pattern {
    /// Collect free variables in this pattern
    pub fn free_vars(&self) -> HashSet<String> {
        match self {
            Pattern::Term(pt) => pt.free_vars(),
            Pattern::Collection { elements, rest, .. } => {
                let mut vars = HashSet::new();
                for elem in elements {
                    vars.extend(elem.free_vars());
                }
                if let Some(r) = rest {
                    vars.insert(r.to_string());
                }
                vars
            }
            Pattern::Map { collection, params, body } => {
                let mut vars = collection.free_vars();
                // Body vars, minus the params (which are bound by the map)
                let mut body_vars = body.free_vars();
                for param in params {
                    body_vars.remove(&param.to_string());
                }
                vars.extend(body_vars);
                vars
            }
            Pattern::Zip { collections } => {
                let mut vars = HashSet::new();
                for coll in collections {
                    vars.extend(coll.free_vars());
                }
                vars
            }
        }
    }
    
    /// Check if this pattern contains any metasyntax
    /// Returns true for Collection, Map, Zip (these cannot be converted to Term)
    pub fn has_metasyntax(&self) -> bool {
        match self {
            Pattern::Term(pt) => pt.has_metasyntax(),
            // All collection variants are metasyntax
            Pattern::Collection { .. } | Pattern::Map { .. } | Pattern::Zip { .. } => true,
        }
    }
    
    /// Check if this pattern is a collection match
    pub fn has_collection_match(&self) -> bool {
        matches!(self, Pattern::Collection { .. })
    }
    
    /// Get the constructor name if this is a constructor application or collection
    pub fn constructor_name(&self) -> Option<&Ident> {
        match self {
            Pattern::Term(PatternTerm::Apply { constructor, .. }) => Some(constructor),
            Pattern::Collection { constructor, .. } => constructor.as_ref(),
            _ => None,
        }
    }
    
    /// Get a reference to the inner PatternTerm if this is a Term pattern
    pub fn as_pattern_term(&self) -> Option<&PatternTerm> {
        match self {
            Pattern::Term(pt) => Some(pt),
            _ => None,
        }
    }
    
    /// Create a variable pattern
    pub fn var(name: Ident) -> Self {
        Pattern::Term(PatternTerm::Var(name))
    }
    
    /// Create a constructor application pattern
    pub fn apply(constructor: Ident, args: Vec<Pattern>) -> Self {
        Pattern::Term(PatternTerm::Apply { constructor, args })
    }
    
    // -------------------------------------------------------------------------
    // Category inference
    // -------------------------------------------------------------------------
    
    /// Infer the category this pattern produces (if determinable)
    /// 
    /// Returns `Some(category)` if the pattern unambiguously produces that category.
    /// Returns `None` for variables (unknown without context) or errors.
    pub fn category<'a>(&self, theory: &'a TheoryDef) -> Option<&'a Ident> {
        match self {
            Pattern::Term(pt) => pt.category(theory),
            Pattern::Collection { constructor, .. } => {
                constructor.as_ref().and_then(|c| theory.category_of_constructor(c))
            }
            Pattern::Map { collection, .. } => collection.category(theory),
            Pattern::Zip { collections } => {
                // Zip produces a collection of tuples - category depends on usage
                collections.first().and_then(|c| c.category(theory))
            }
        }
    }
    
    // -------------------------------------------------------------------------
    // Variable occurrence tracking (for duplicate detection)
    // -------------------------------------------------------------------------
    
    /// Collect all variable occurrences with their counts.
    /// Useful for detecting duplicate variables that need equational checks.
    pub fn var_occurrences(&self) -> HashMap<String, usize> {
        let mut counts = HashMap::new();
        self.collect_var_occurrences(&mut counts);
        counts
    }
    
    fn collect_var_occurrences(&self, counts: &mut HashMap<String, usize>) {
        match self {
            Pattern::Term(pt) => pt.collect_var_occurrences(counts),
            Pattern::Collection { elements, rest, .. } => {
                for elem in elements {
                    elem.collect_var_occurrences(counts);
                }
                if let Some(r) = rest {
                    *counts.entry(r.to_string()).or_insert(0) += 1;
                }
            }
            Pattern::Map { collection, params, body } => {
                collection.collect_var_occurrences(counts);
                // params are binders, not occurrences
                // body occurrences that match params are bound
                let mut body_counts = HashMap::new();
                body.collect_var_occurrences(&mut body_counts);
                let param_names: HashSet<_> = params.iter().map(|p| p.to_string()).collect();
                for (var, count) in body_counts {
                    if !param_names.contains(&var) {
                        *counts.entry(var).or_insert(0) += count;
                    }
                }
            }
            Pattern::Zip { collections } => {
                for coll in collections {
                    coll.collect_var_occurrences(counts);
                }
            }
        }
    }
    
    /// Get variables that appear more than once (need equational matching on LHS)
    pub fn duplicate_vars(&self) -> HashSet<String> {
        self.var_occurrences()
            .into_iter()
            .filter(|(_, count)| *count > 1)
            .map(|(var, _)| var)
            .collect()
    }
}

impl PatternTerm {
    /// Infer the category this pattern term produces
    pub fn category<'a>(&self, theory: &'a TheoryDef) -> Option<&'a Ident> {
        match self {
            PatternTerm::Var(_) => None, // Variables need context
            PatternTerm::Apply { constructor, .. } => theory.category_of_constructor(constructor),
            PatternTerm::Lambda { body, .. } => body.category(theory),
            PatternTerm::MultiLambda { body, .. } => body.category(theory),
            PatternTerm::Subst { term, .. } => term.category(theory),
            PatternTerm::MultiSubst { scope, .. } => scope.category(theory),
        }
    }
    
    fn collect_var_occurrences(&self, counts: &mut HashMap<String, usize>) {
        match self {
            PatternTerm::Var(v) => {
                *counts.entry(v.to_string()).or_insert(0) += 1;
            }
            PatternTerm::Apply { args, .. } => {
                for arg in args {
                    arg.collect_var_occurrences(counts);
                }
            }
            PatternTerm::Lambda { binder, body } => {
                // binder is bound, not an occurrence
                let mut body_counts = HashMap::new();
                body.collect_var_occurrences(&mut body_counts);
                body_counts.remove(&binder.to_string());
                for (var, count) in body_counts {
                    *counts.entry(var).or_insert(0) += count;
                }
            }
            PatternTerm::MultiLambda { binders, body } => {
                let mut body_counts = HashMap::new();
                body.collect_var_occurrences(&mut body_counts);
                for binder in binders {
                    body_counts.remove(&binder.to_string());
                }
                for (var, count) in body_counts {
                    *counts.entry(var).or_insert(0) += count;
                }
            }
            PatternTerm::Subst { term, var, replacement } => {
                term.collect_var_occurrences(counts);
                *counts.entry(var.to_string()).or_insert(0) += 1;
                replacement.collect_var_occurrences(counts);
            }
            PatternTerm::MultiSubst { scope, replacements } => {
                scope.collect_var_occurrences(counts);
                for repl in replacements {
                    repl.collect_var_occurrences(counts);
                }
            }
        }
    }
}

// ============================================================================
// AscentClauses: Result of pattern-to-clause conversion
// ============================================================================

/// Result of converting a pattern to Ascent clauses.
/// This is the unified abstraction for LHS pattern matching.
#[derive(Default)]
pub struct AscentClauses {
    /// The clauses to add to the rule body (if let ..., for loops, etc.)
    pub clauses: Vec<TokenStream>,
    /// Variable bindings: var_name -> expression to access it
    pub bindings: HashMap<String, TokenStream>,
    /// Category assignments for variables
    pub variable_categories: HashMap<String, Ident>,
    /// Equational checks needed for duplicate variables
    pub equational_checks: Vec<TokenStream>,
}

impl Pattern {
    /// Generate Ascent clauses for LHS pattern matching.
    ///
    /// This is the core abstraction that replaces the scattered logic in
    /// equations.rs, rewrites/patterns.rs, etc.
    ///
    /// # Arguments
    /// * `term_var` - The Ascent variable holding the term to match
    /// * `category` - Expected category of the term
    /// * `theory` - Theory definition for constructor lookups
    /// * `duplicate_vars` - Variables appearing more than once (need eq checks)
    pub fn to_ascent_clauses(
        &self,
        term_var: &Ident,
        category: &Ident,
        theory: &TheoryDef,
        duplicate_vars: &HashSet<String>,
    ) -> AscentClauses {
        let mut result = AscentClauses::default();
        let mut first_occurrences = HashSet::new();
        let mut iter_counter = 0usize; // Global counter for iteration variables
        
        self.generate_clauses(
            term_var,
            category,
            theory,
            duplicate_vars,
            &mut result,
            &mut first_occurrences,
            &mut iter_counter,
        );
        
        result
    }
    
    fn generate_clauses(
        &self,
        term_var: &Ident,
        category: &Ident,
        theory: &TheoryDef,
        duplicate_vars: &HashSet<String>,
        result: &mut AscentClauses,
        first_occurrences: &mut HashSet<String>,
        iter_counter: &mut usize,
    ) {
        match self {
            Pattern::Term(pt) => {
                pt.generate_clauses(term_var, category, theory, duplicate_vars, result, first_occurrences, iter_counter);
            }
            
            Pattern::Collection { constructor, elements, rest } => {
                // NOTE: When nested inside PatternTerm::Apply, term_var is already the bag field.
                // We do NOT generate `if let` here - the parent Apply already destructured.
                // The constructor is used to look up element type, not for destructuring.
                
                let cons = constructor.as_ref()
                    .expect("Collection pattern must have constructor for LHS matching");
                
                // Get element category from constructor
                let elem_cat = theory.collection_element_type(cons)
                    .expect("Collection constructor must have element type");
                
                // term_var IS the bag - iterate directly over it
                let bag_var = term_var;
                
                // For each element, iterate and match
                let mut elem_vars = Vec::new();
                for (i, elem) in elements.iter().enumerate() {
                    let elem_var = format_ident!("{}_e{}", term_var, i);
                    let count_var = format_ident!("_count_{}", *iter_counter);
                    *iter_counter += 1; // Increment global counter for next iteration
                    elem_vars.push(elem_var.clone());
                    
                    // for (elem_var, _count_N) in bag_var.iter()
                    result.clauses.push(quote! {
                        for (#elem_var, #count_var) in #bag_var.iter()
                    });
                    
                    // Distinctness checks: each element must be different from previous
                    for prev in &elem_vars[..i] {
                        result.clauses.push(quote! {
                            if &#elem_var != &#prev
                        });
                    }
                    
                    // Recursively process element pattern
                    elem.generate_clauses(
                        &elem_var, elem_cat, theory, duplicate_vars, result, first_occurrences, iter_counter
                    );
                }
                
                // Bind rest variable if present
                if let Some(rest_var) = rest {
                    let rest_ident = format_ident!("{}_rest", term_var);
                    if !elem_vars.is_empty() {
                        result.clauses.push(quote! {
                            let #rest_ident = {
                                let mut bag = #bag_var.clone();
                                #(bag.remove(&#elem_vars);)*
                                bag
                            }
                        });
                    } else {
                        result.clauses.push(quote! {
                            let #rest_ident = #bag_var.clone()
                        });
                    }
                    result.bindings.insert(rest_var.to_string(), quote! { #rest_ident.clone() });
                }
            }
            
            Pattern::Map { .. } => {
                // Map on LHS: for each element matching the pattern, extract bindings
                // This is complex - defer to future implementation
                unimplemented!("Map patterns in LHS not yet implemented")
            }
            
            Pattern::Zip { .. } => {
                // Zip on LHS: parallel iteration over multiple collections
                unimplemented!("Zip patterns in LHS not yet implemented")
            }
        }
    }
}

impl PatternTerm {
    fn generate_clauses(
        &self,
        term_var: &Ident,
        category: &Ident,
        theory: &TheoryDef,
        duplicate_vars: &HashSet<String>,
        result: &mut AscentClauses,
        first_occurrences: &mut HashSet<String>,
        iter_counter: &mut usize,
    ) {
        match self {
            PatternTerm::Var(v) => {
                let var_name = v.to_string();
                
                if duplicate_vars.contains(&var_name) {
                    // Duplicate variable - need equational check
                    if first_occurrences.insert(var_name.clone()) {
                        // First occurrence: bind it
                        result.bindings.insert(var_name.clone(), quote! { #term_var.clone() });
                        result.variable_categories.insert(var_name, category.clone());
                    } else {
                        // Subsequent occurrence: emit eq check
                        let existing = result.bindings.get(&var_name).unwrap().clone();
                        let eq_rel = format_ident!("eq_{}", category.to_string().to_lowercase());
                        result.equational_checks.push(quote! {
                            #eq_rel(#existing, #term_var.clone())
                        });
                    }
                } else {
                    // Single-occurrence variable: just bind
                    result.bindings.insert(var_name.clone(), quote! { #term_var.clone() });
                    result.variable_categories.insert(var_name, category.clone());
                }
            }
            
            PatternTerm::Apply { constructor, args } => {
                let rule = theory.get_constructor(constructor)
                    .expect("Unknown constructor in pattern");
                
                // Generate field variables
                let field_vars: Vec<Ident> = (0..args.len())
                    .map(|i| format_ident!("{}_f{}", term_var, i))
                    .collect();
                
                // Generate destructuring pattern: if let Cat::Cons(f0, f1, ...) = term_var
                result.clauses.push(quote! {
                    if let #category::#constructor(#(ref #field_vars),*) = #term_var
                });
                
                // Recursively process each argument
                let mut field_idx = 0;
                for item in &rule.items {
                    match item {
                        GrammarItem::NonTerminal(field_cat) => {
                            if field_idx < args.len() {
                                let field_var = &field_vars[field_idx];
                                
                                // Handle Box<T> - need to dereference for all non-terminals except:
                                // - Var (stored as OrdVar, not Box<OrdVar>)
                                // - Integer (stored as native type like i32, not Box<i32>)
                                let field_cat_str = field_cat.to_string();
                                let is_unboxed = field_cat_str == "Var" || field_cat_str == "Integer";
                                let deref_var = if is_unboxed {
                                    field_var.clone()
                                } else {
                                    let dv = format_ident!("{}_deref", field_var);
                                    result.clauses.push(quote! {
                                        let #dv = &**#field_var
                                    });
                                    dv
                                };
                                
                                args[field_idx].generate_clauses(
                                    &deref_var, field_cat, theory, duplicate_vars, result, first_occurrences, iter_counter
                                );
                                field_idx += 1;
                            }
                        }
                        GrammarItem::Collection { element_type, .. } => {
                            if field_idx < args.len() {
                                // Collection field - delegate to collection handling
                                args[field_idx].generate_clauses(
                                    &field_vars[field_idx], element_type, theory, duplicate_vars, result, first_occurrences, iter_counter
                                );
                                field_idx += 1;
                            }
                        }
                        GrammarItem::Binder { category: _binder_cat } => {
                            // Binder field - handle scope using UNSAFE accessors for stable identity!
                            // Note: _binder_cat is the domain type (what the binder binds, e.g., Name)
                            // The body category comes from the grammar rule's category (the codomain, e.g., Proc)
                            if field_idx < args.len() {
                                let field_var = &field_vars[field_idx];
                                let binder_var = format_ident!("{}_binder", field_var);
                                let body_boxed_var = format_ident!("{}_body_boxed", field_var);
                                let body_var = format_ident!("{}_body", field_var);
                                
                                // Use unsafe accessors to preserve binder identity (no freshening!)
                                result.clauses.push(quote! {
                                    let #binder_var = #field_var.unsafe_pattern().clone()
                                });
                                result.clauses.push(quote! {
                                    let #body_boxed_var = #field_var.unsafe_body()
                                });
                                
                                // Dereference the Box to get the actual body
                                result.clauses.push(quote! {
                                    let #body_var = &**#body_boxed_var
                                });
                                
                                // The body type is the constructor's category (codomain of the binder type)
                                // For PNew in Proc, the body is also Proc
                                let body_cat = &rule.category;
                                
                                // Check if arg is a Lambda pattern - if so, extract binder/body directly
                                if let Pattern::Term(PatternTerm::Lambda { binder, body }) = &args[field_idx] {
                                    // Bind the Lambda's binder name to the inner FreeVar (Binder.0)
                                    // This is needed because substitute methods expect FreeVar<String>, not Binder<String>
                                    result.bindings.insert(binder.to_string(), quote! { #binder_var.0.clone() });
                                    
                                    // Also bind the full binder for RHS reconstruction
                                    result.bindings.insert(format!("__binder_{}", binder), quote! { #binder_var.clone() });
                                    
                                    // Process the Lambda's body with body_var
                                    body.generate_clauses(
                                        &body_var, body_cat, theory, duplicate_vars, result, first_occurrences, iter_counter
                                    );
                                } else {
                                    // Non-Lambda pattern in binder position - just process normally
                                    args[field_idx].generate_clauses(
                                        &body_var, body_cat, theory, duplicate_vars, result, first_occurrences, iter_counter
                                    );
                                }
                                field_idx += 1;
                            }
                        }
                        GrammarItem::Terminal(_) => {
                            // Skip terminals
                        }
                    }
                }
            }
            
            PatternTerm::Lambda { binder, body } => {
                // Match a lambda/scope using UNSAFE accessors to preserve binder identity!
                // Using unbind() creates fresh variables each time, causing infinite loops
                // in equations because the same term produces different outputs.
                let binder_var = format_ident!("{}_binder", term_var);
                let body_var = format_ident!("{}_body", term_var);
                let body_boxed_var = format_ident!("{}_body_boxed", term_var);
                
                // Access binder and body directly without freshening
                result.clauses.push(quote! {
                    let #binder_var = #term_var.unsafe_pattern().clone()
                });
                result.clauses.push(quote! {
                    let #body_boxed_var = #term_var.unsafe_body()
                });
                result.clauses.push(quote! {
                    let #body_var = &**#body_boxed_var
                });
                
                // Bind the binder variable - use .0 to get FreeVar from Binder
                // This is needed because substitute methods expect FreeVar<String>, not Binder<String>
                result.bindings.insert(binder.to_string(), quote! { #binder_var.0.clone() });
                
                // Also bind the full binder for RHS reconstruction
                result.bindings.insert(format!("__binder_{}", binder), quote! { #binder_var.clone() });
                
                // Recursively process body
                // The body has the same category as the enclosing term (from context)
                // For Scope<Binder, Body>, both the Scope and Body have the same category
                body.generate_clauses(
                    &body_var, category, theory, duplicate_vars, result, first_occurrences, iter_counter
                );
            }
            
            PatternTerm::MultiLambda { binders, body } => {
                // Multi-lambda: use unsafe accessors for stable identity
                let binders_var = format_ident!("{}_binders", term_var);
                let body_var = format_ident!("{}_body", term_var);
                let body_boxed_var = format_ident!("{}_body_boxed", term_var);
                
                result.clauses.push(quote! {
                    let #binders_var = #term_var.unsafe_pattern().clone()
                });
                result.clauses.push(quote! {
                    let #body_boxed_var = #term_var.unsafe_body()
                });
                result.clauses.push(quote! {
                    let #body_var = &**#body_boxed_var
                });
                
                // Bind each binder variable (as the whole binders vec for now)
                // TODO: Support destructuring individual binders
                for binder in binders {
                    result.bindings.insert(binder.to_string(), quote! { #binders_var.clone() });
                }
                
                // Recursively process body with the same category as the enclosing term
                body.generate_clauses(
                    &body_var, category, theory, duplicate_vars, result, first_occurrences, iter_counter
                );
            }
            
            PatternTerm::Subst { .. } => {
                // Substitution in LHS is unusual
                unimplemented!("Subst in LHS patterns not supported")
            }
            
            PatternTerm::MultiSubst { .. } => {
                unimplemented!("MultiSubst in LHS patterns not supported")
            }
        }
    }
}

// ============================================================================
// RHS Construction: Pattern → TokenStream
// ============================================================================

impl Pattern {
    /// Generate RHS construction expression.
    ///
    /// # Arguments
    /// * `bindings` - Variables bound by LHS → their Ascent expressions
    /// * `theory` - Theory definition for constructor lookups
    ///
    /// # Example
    /// For RHS `(PNew x (PPar {P, Q}))` with bindings `{"x" -> x_binder, "P" -> p, "Q" -> q}`:
    /// ```text
    /// Proc::PNew(x_binder.clone(), Box::new(Proc::PPar({
    ///     let mut bag = HashBag::new();
    ///     bag.insert(p.clone());
    ///     bag.insert(q.clone());
    ///     bag
    /// })))
    /// ```
    pub fn to_ascent_rhs(
        &self,
        bindings: &HashMap<String, TokenStream>,
        theory: &TheoryDef,
    ) -> TokenStream {
        match self {
            Pattern::Term(pt) => pt.to_ascent_rhs(bindings, theory),
            Pattern::Collection { constructor, elements, rest } => {
                self.generate_collection_rhs(constructor.as_ref(), elements, rest.as_ref(), bindings, theory)
            }
            Pattern::Map { collection, params, body } => {
                self.generate_map_rhs(collection, params, body, bindings, theory)
            }
            Pattern::Zip { collections } => {
                self.generate_zip_rhs(collections, bindings, theory)
            }
        }
    }
    
    fn generate_collection_rhs(
        &self,
        constructor: Option<&Ident>,
        elements: &[Pattern],
        rest: Option<&Ident>,
        bindings: &HashMap<String, TokenStream>,
        theory: &TheoryDef,
    ) -> TokenStream {
        let elem_exprs: Vec<_> = elements.iter()
            .map(|e| e.to_ascent_rhs(bindings, theory))
            .collect();
        
        let coll_type = quote! { mettail_runtime::HashBag };
        
        // Get category and insert helper if constructor provided
        let (category, insert_helper) = if let Some(cons) = constructor {
            if let Some(cat) = theory.category_of_constructor(cons) {
                let cons_lower = format_ident!("{}", cons.to_string().to_lowercase());
                let helper = format_ident!("insert_into_{}", cons_lower);
                (Some(cat.clone()), Some(helper))
            } else {
                (None, None)
            }
        } else {
            (None, None)
        };
        
        if let Some(rest_var) = rest {
            // TODO: Variable binding will be handled by unified rule generation
            let rest_name = rest_var.to_string();
            let rest_ident = quote::format_ident!("{}", rest_name);
            let rest_binding = bindings.get(&rest_name)
                .cloned()
                .unwrap_or_else(|| quote! { #rest_ident });
            
            if let (Some(cat), Some(helper)) = (&category, &insert_helper) {
                // Use flatten helper
                quote! {
                    {
                        let mut bag = (#rest_binding).clone();
                        #(#cat::#helper(&mut bag, #elem_exprs);)*
                        bag
                    }
                }
            } else {
                // Plain insert
                quote! {
                    {
                        let mut bag = (#rest_binding).clone();
                        #(bag.insert(#elem_exprs);)*
                        bag
                    }
                }
            }
        } else {
            if let (Some(cat), Some(helper)) = (&category, &insert_helper) {
                quote! {
                    {
                        let mut bag = #coll_type::new();
                        #(#cat::#helper(&mut bag, #elem_exprs);)*
                        bag
                    }
                }
            } else {
                quote! {
                    {
                        let mut bag = #coll_type::new();
                        #(bag.insert(#elem_exprs);)*
                        bag
                    }
                }
            }
        }
    }
    
    fn generate_map_rhs(
        &self,
        collection: &Pattern,
        params: &[Ident],
        body: &Pattern,
        bindings: &HashMap<String, TokenStream>,
        theory: &TheoryDef,
    ) -> TokenStream {
        // Generate: iterate collection, apply body to each element
        let coll_expr = collection.to_ascent_rhs(bindings, theory);
        let param = &params[0]; // Assume single param for now
        
        // Create bindings with param bound for body evaluation
        // This is a simplification - full implementation needs proper scoping
        let body_expr = body.to_ascent_rhs(bindings, theory);
        
        quote! {
            {
                let mut result = mettail_runtime::HashBag::new();
                for (#param, _count) in (#coll_expr).iter() {
                    let mapped = #body_expr;
                    result.insert(mapped);
                }
                result
            }
        }
    }
    
    fn generate_zip_rhs(
        &self,
        _collections: &[Pattern],
        _bindings: &HashMap<String, TokenStream>,
        _theory: &TheoryDef,
    ) -> TokenStream {
        // Zip on RHS - pair-wise combination of collections
        unimplemented!("Zip in RHS not yet implemented")
    }
}

impl PatternTerm {
    pub fn to_ascent_rhs(
        &self,
        bindings: &HashMap<String, TokenStream>,
        theory: &TheoryDef,
    ) -> TokenStream {
        match self {
            PatternTerm::Var(v) => {
                let var_name = v.to_string();
                bindings.get(&var_name)
                    .map(|b| quote! { (#b).clone() })
                    .unwrap_or_else(|| {
                        // Check if it's a nullary constructor
                        if let Some(rule) = theory.get_constructor(v) {
                            let category = &rule.category;
                            quote! { #category::#v }
                        } else {
                            // TODO: Variable binding will be handled by unified rule generation
                            let var_ident = quote::format_ident!("{}", var_name);
                            quote! { #var_ident.clone() }
                        }
                    })
            }
            
            PatternTerm::Apply { constructor, args } => {
                let category = theory.category_of_constructor(constructor)
                    .expect("Unknown constructor");
                let rule = theory.get_constructor(constructor).unwrap();
                
                let arg_exprs: Vec<_> = args.iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        let expr = arg.to_ascent_rhs(bindings, theory);
                        
                        // Check if this arg needs Box wrapping
                        let needs_box = needs_box_for_field(rule, i, theory);
                        let is_collection = is_collection_field(rule, i);
                        
                        if is_collection || !needs_box {
                            expr
                        } else {
                            quote! { Box::new(#expr) }
                        }
                    })
                    .collect();
                
                quote! { #category::#constructor(#(#arg_exprs),*) }
            }
            
            PatternTerm::Lambda { binder, body } => {
                // Construct a Scope using from_parts_unsafe to preserve binder identity!
                // Using Scope::new would re-close the body with a different binder ID,
                // causing infinite loops in equations.
                let body_expr = body.to_ascent_rhs(bindings, theory);
                let binder_name = binder.to_string();
                let full_binder_key = format!("__binder_{}", binder);
                
                let binder_expr = if let Some(full_binder) = bindings.get(&full_binder_key) {
                    // Use the full original Binder from LHS (preserves identity!)
                    quote! { #full_binder.clone() }
                } else if let Some(bound_freevar) = bindings.get(&binder_name) {
                    // Fallback: wrap the FreeVar in a new Binder
                    quote! { mettail_runtime::Binder(#bound_freevar.clone()) }
                } else {
                    // Create fresh binder (fallback, shouldn't happen in well-formed patterns)
                    quote! { mettail_runtime::Binder(mettail_runtime::FreeVar::fresh_named(#binder_name)) }
                };
                
                quote! {
                    mettail_runtime::Scope::from_parts_unsafe(
                        #binder_expr,
                        Box::new(#body_expr)
                    )
                }
            }
            
            PatternTerm::MultiLambda { binders, body } => {
                // Construct a multi-binder Scope using from_parts_unsafe
                let body_expr = body.to_ascent_rhs(bindings, theory);
                let binder_exprs: Vec<_> = binders.iter().map(|b| {
                    let binder_name = b.to_string();
                    let full_binder_key = format!("__binder_{}", b);
                    if let Some(full_binder) = bindings.get(&full_binder_key) {
                        quote! { #full_binder.clone() }
                    } else if let Some(bound_freevar) = bindings.get(&binder_name) {
                        quote! { mettail_runtime::Binder(#bound_freevar.clone()) }
                    } else {
                        quote! { mettail_runtime::Binder(mettail_runtime::FreeVar::fresh_named(#binder_name)) }
                    }
                }).collect();
                
                quote! {
                    mettail_runtime::Scope::from_parts_unsafe(
                        vec![#(#binder_exprs),*],
                        Box::new(#body_expr)
                    )
                }
            }
            
            PatternTerm::Subst { term, var, replacement } => {
                let term_expr = term.to_ascent_rhs(bindings, theory);
                let var_binding = bindings.get(&var.to_string())
                    .expect("Substitution variable not bound");
                let repl_expr = replacement.to_ascent_rhs(bindings, theory);
                
                // Determine category of replacement for method name
                let repl_cat = replacement.category(theory)
                    .map(|c| c.to_string().to_lowercase())
                    .unwrap_or_else(|| "unknown".to_string());
                let subst_method = format_ident!("substitute_{}", repl_cat);
                
                quote! {
                    (#term_expr).#subst_method(&#var_binding, &#repl_expr)
                }
            }
            
            PatternTerm::MultiSubst { scope, replacements } => {
                // Multi-substitution
                let scope_expr = scope.to_ascent_rhs(bindings, theory);
                let repl_exprs: Vec<_> = replacements.iter()
                    .map(|r| r.to_ascent_rhs(bindings, theory))
                    .collect();
                
                // Determine category from first replacement
                let repl_cat = replacements.first()
                    .and_then(|r| r.category(theory))
                    .map(|c| c.to_string().to_lowercase())
                    .unwrap_or_else(|| "unknown".to_string());
                let subst_method = format_ident!("multi_substitute_{}", repl_cat);
                
                quote! {
                    {
                        let (__binders, __body) = (#scope_expr).unbind();
                        let __vars: Vec<&mettail_runtime::FreeVar<String>> = __binders.iter()
                            .map(|b| &b.0)
                            .collect();
                        let __repls = vec![#(#repl_exprs),*];
                        (*__body).#subst_method(&__vars, &__repls)
                    }
                }
            }
        }
    }
}

/// Helper: Check if field i needs Box wrapping
/// ALL non-terminal fields are boxed EXCEPT:
/// - Var (which is OrdVar, not Box<OrdVar>)
/// - Integer (which is native type like i32, not Box<i32>)
fn needs_box_for_field(rule: &super::grammar::GrammarRule, i: usize, _theory: &TheoryDef) -> bool {
    let mut field_idx = 0;
    for item in &rule.items {
        match item {
            GrammarItem::NonTerminal(cat) => {
                if field_idx == i {
                    // Box all non-terminals except Var and Integer
                    let cat_str = cat.to_string();
                    return cat_str != "Var" && cat_str != "Integer";
                }
                field_idx += 1;
            }
            GrammarItem::Collection { .. } | GrammarItem::Binder { .. } => {
                field_idx += 1;
            }
            GrammarItem::Terminal(_) => {}
        }
    }
    false
}

/// Helper: Check if field i is a collection field
fn is_collection_field(rule: &super::grammar::GrammarRule, i: usize) -> bool {
    let mut field_idx = 0;
    for item in &rule.items {
        match item {
            GrammarItem::Collection { .. } => {
                if field_idx == i {
                    return true;
                }
                field_idx += 1;
            }
            GrammarItem::NonTerminal(_) | GrammarItem::Binder { .. } => {
                field_idx += 1;
            }
            GrammarItem::Terminal(_) => {}
        }
    }
    false
}

// ============================================================================
// Conversion functions: Term <-> Pattern
// ============================================================================

/// Convert a Term to a Pattern (no metasyntax, just lifting)
pub fn term_to_pattern(term: &Term) -> Pattern {
    Pattern::Term(term_to_pattern_term(term))
}

/// Convert a Term to a PatternTerm
pub fn term_to_pattern_term(term: &Term) -> PatternTerm {
    match term {
        Term::Var(v) => PatternTerm::Var(v.clone()),
        Term::Apply { constructor, args } => PatternTerm::Apply {
            constructor: constructor.clone(),
            args: args.iter().map(term_to_pattern).collect(),
        },
        Term::Lambda { binder, body } => PatternTerm::Lambda {
            binder: binder.clone(),
            body: Box::new(term_to_pattern(body)),
        },
        Term::MultiLambda { binders, body } => PatternTerm::MultiLambda {
            binders: binders.clone(),
            body: Box::new(term_to_pattern(body)),
        },
        Term::Subst { term, var, replacement } => PatternTerm::Subst {
            term: Box::new(term_to_pattern(term)),
            var: var.clone(),
            replacement: Box::new(term_to_pattern(replacement)),
        },
        Term::MultiSubst { scope, replacements } => PatternTerm::MultiSubst {
            scope: Box::new(term_to_pattern(scope)),
            replacements: replacements.iter().map(term_to_pattern).collect(),
        },
        // NOTE: Term::CollectionConstruct has been removed.
        // Collections are now Pattern::Collection (metasyntax), not part of Term.
    }
}

/// Try to convert a Pattern to a Term (fails if pattern contains metasyntax)
pub fn pattern_to_term(pattern: &Pattern) -> Option<Term> {
    match pattern {
        Pattern::Term(pt) => pattern_term_to_term(pt),
        // Metasyntax cannot be converted to Term
        Pattern::Collection { .. } | Pattern::Map { .. } | Pattern::Zip { .. } => None,
    }
}

/// Try to convert a PatternTerm to a Term
pub fn pattern_term_to_term(pt: &PatternTerm) -> Option<Term> {
    match pt {
        PatternTerm::Var(v) => Some(Term::Var(v.clone())),
        PatternTerm::Apply { constructor, args } => {
            let term_args: Option<Vec<Term>> = args.iter().map(pattern_to_term).collect();
            term_args.map(|a| Term::Apply {
                constructor: constructor.clone(),
                args: a,
            })
        }
        PatternTerm::Lambda { binder, body } => {
            pattern_to_term(body).map(|b| Term::Lambda {
                binder: binder.clone(),
                body: Box::new(b),
            })
        }
        PatternTerm::MultiLambda { binders, body } => {
            pattern_to_term(body).map(|b| Term::MultiLambda {
                binders: binders.clone(),
                body: Box::new(b),
            })
        }
        PatternTerm::Subst { term, var, replacement } => {
            let t = pattern_to_term(term)?;
            let r = pattern_to_term(replacement)?;
            Some(Term::Subst {
                term: Box::new(t),
                var: var.clone(),
                replacement: Box::new(r),
            })
        }
        PatternTerm::MultiSubst { scope, replacements } => {
            let s = pattern_to_term(scope)?;
            let rs: Option<Vec<Term>> = replacements.iter().map(pattern_to_term).collect();
            rs.map(|r| Term::MultiSubst {
                scope: Box::new(s),
                replacements: r,
            })
        }
    }
}

// ============================================================================
// Backwards compatibility aliases (to be removed after migration)
// ============================================================================

/// Type alias for backwards compatibility
pub type LhsPattern = Pattern;

/// Alias for Collection variant (backwards compatibility)
impl Pattern {
    /// Create a CollectionMatch pattern (backwards compatibility name)
    pub fn collection_match(
        constructor: Option<Ident>,
        elements: Vec<Pattern>,
        rest: Option<Ident>,
    ) -> Self {
        Pattern::Collection { constructor, elements, rest }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use quote::format_ident;
    
    #[test]
    fn test_pattern_term_var_free_vars() {
        let pt = PatternTerm::Var(format_ident!("x"));
        let vars = pt.free_vars();
        assert!(vars.contains("x"));
        assert_eq!(vars.len(), 1);
    }
    
    #[test]
    fn test_pattern_term_lambda_free_vars() {
        // \x. (App x y) - x is bound, y is free
        let pt = PatternTerm::Lambda {
            binder: format_ident!("x"),
            body: Box::new(Pattern::Term(PatternTerm::Apply {
                constructor: format_ident!("App"),
                args: vec![
                    Pattern::Term(PatternTerm::Var(format_ident!("x"))),
                    Pattern::Term(PatternTerm::Var(format_ident!("y"))),
                ],
            })),
        };
        let vars = pt.free_vars();
        assert!(!vars.contains("x"), "x should be bound");
        assert!(vars.contains("y"), "y should be free");
    }
    
    #[test]
    fn test_pattern_collection_free_vars() {
        // {P, Q, ...rest}
        let p = Pattern::Collection {
            constructor: Some(format_ident!("PPar")),
            elements: vec![
                Pattern::Term(PatternTerm::Var(format_ident!("P"))),
                Pattern::Term(PatternTerm::Var(format_ident!("Q"))),
            ],
            rest: Some(format_ident!("rest")),
        };
        let vars = p.free_vars();
        assert!(vars.contains("P"));
        assert!(vars.contains("Q"));
        assert!(vars.contains("rest"));
    }
    
    #[test]
    fn test_pattern_map_free_vars() {
        // xs.#map(|x| (F x y)) - xs and y are free, x is bound by map
        let p = Pattern::Map {
            collection: Box::new(Pattern::Term(PatternTerm::Var(format_ident!("xs")))),
            params: vec![format_ident!("x")],
            body: Box::new(Pattern::Term(PatternTerm::Apply {
                constructor: format_ident!("F"),
                args: vec![
                    Pattern::Term(PatternTerm::Var(format_ident!("x"))),
                    Pattern::Term(PatternTerm::Var(format_ident!("y"))),
                ],
            })),
        };
        let vars = p.free_vars();
        assert!(vars.contains("xs"), "xs should be free");
        assert!(vars.contains("y"), "y should be free");
        assert!(!vars.contains("x"), "x should be bound by map params");
    }
    
    #[test]
    fn test_has_metasyntax() {
        // Simple term - no metasyntax
        let simple = Pattern::Term(PatternTerm::Var(format_ident!("x")));
        assert!(!simple.has_metasyntax());
        
        // Collection - has metasyntax
        let collection = Pattern::Collection {
            constructor: None,
            elements: vec![],
            rest: None,
        };
        assert!(collection.has_metasyntax());
        
        // Map - has metasyntax
        let map = Pattern::Map {
            collection: Box::new(Pattern::Term(PatternTerm::Var(format_ident!("xs")))),
            params: vec![format_ident!("x")],
            body: Box::new(Pattern::Term(PatternTerm::Var(format_ident!("x")))),
        };
        assert!(map.has_metasyntax());
        
        // Term containing Map in args - has metasyntax
        let nested = Pattern::Term(PatternTerm::Apply {
            constructor: format_ident!("App"),
            args: vec![map.clone()],
        });
        assert!(nested.has_metasyntax());
    }
    
    #[test]
    fn test_term_to_pattern_roundtrip() {
        // Create a simple Term
        let term = Term::Apply {
            constructor: format_ident!("Add"),
            args: vec![
                Term::Var(format_ident!("x")),
                Term::Var(format_ident!("y")),
            ],
        };
        
        // Convert to Pattern and back
        let pattern = term_to_pattern(&term);
        let back = pattern_to_term(&pattern);
        
        assert!(back.is_some());
        if let Some(Term::Apply { constructor, args }) = back {
            assert_eq!(constructor.to_string(), "Add");
            assert_eq!(args.len(), 2);
        } else {
            panic!("Expected Apply");
        }
    }
    
    #[test]
    fn test_pattern_to_term_fails_with_metasyntax() {
        let pattern = Pattern::Collection {
            constructor: Some(format_ident!("PPar")),
            elements: vec![Pattern::Term(PatternTerm::Var(format_ident!("P")))],
            rest: Some(format_ident!("rest")),
        };
        
        assert!(pattern_to_term(&pattern).is_none());
    }
}
