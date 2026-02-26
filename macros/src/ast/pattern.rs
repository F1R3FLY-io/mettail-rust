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

use super::grammar::GrammarItem;
use super::language::LanguageDef;
use super::types::CollectionType;
use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};

/// Term-like structure for rule specification.
/// Mirrors `Term` but allows `Pattern` in sub-expression positions.
/// This lets metasyntax (#map, #zip, etc.) appear anywhere in a term.
#[derive(Debug, Clone)]
pub enum PatternTerm {
    /// Variable (binds on LHS, references on RHS)
    Var(Ident),

    /// Constructor application: (Cons arg0 arg1 ...)
    /// Note: args are Pattern, allowing metasyntax in any position
    Apply { constructor: Ident, args: Vec<Pattern> },

    /// Lambda: \x.body
    Lambda { binder: Ident, body: Box<Pattern> },

    /// Multi-lambda: ^[x0,x1,...].body
    MultiLambda { binders: Vec<Ident>, body: Box<Pattern> },

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
    /// Collection literal: {P, Q, ...rest}
    /// NOTE: Does NOT include constructor - that's in PatternTerm::Apply
    /// LHS: match elements, bind remainder to `rest`
    /// RHS: construct collection, merge with `rest`
    ///
    /// Example: (PPar {P, Q, ...rest}) parses as:
    ///   Pattern::Term(PatternTerm::Apply {
    ///     constructor: PPar,
    ///     args: [Pattern::Collection { coll_type: None, elements: [P, Q], rest }]
    ///   })
    Collection {
        /// Collection type (HashBag, Vec, HashSet)
        /// None means infer from enclosing constructor's grammar rule
        coll_type: Option<CollectionType>,
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

    /// Zip: #zip(first, second)
    /// LHS: correlated search - iterate first, search for matches, extract into second
    /// RHS: pair-wise combination
    Zip {
        /// First collection (iterated on LHS)
        first: Box<Pattern>,
        /// Second collection (extracted on LHS, paired on RHS)
        second: Box<Pattern>,
    },
}

// ============================================================================
// PatternTerm implementations
// ============================================================================

impl PatternTerm {
    /// Collect free variables in this pattern term
    #[allow(dead_code)]
    pub fn free_vars(&self) -> HashSet<String> {
        match self {
            PatternTerm::Var(v) => {
                let mut set = HashSet::new();
                set.insert(v.to_string());
                set
            },
            PatternTerm::Apply { args, .. } => {
                let mut vars = HashSet::new();
                for arg in args {
                    vars.extend(arg.free_vars());
                }
                vars
            },
            PatternTerm::Lambda { binder, body } => {
                let mut vars = body.free_vars();
                vars.remove(&binder.to_string());
                vars
            },
            PatternTerm::MultiLambda { binders, body } => {
                let mut vars = body.free_vars();
                for binder in binders {
                    vars.remove(&binder.to_string());
                }
                vars
            },
            PatternTerm::Subst { term, var, replacement } => {
                let mut vars = term.free_vars();
                vars.insert(var.to_string());
                vars.extend(replacement.free_vars());
                vars
            },
            PatternTerm::MultiSubst { scope, replacements } => {
                let mut vars = scope.free_vars();
                for repl in replacements {
                    vars.extend(repl.free_vars());
                }
                vars
            },
        }
    }
}

// ============================================================================
// Pattern implementations
// ============================================================================

impl Pattern {
    /// Collect free variables in this pattern
    #[allow(dead_code)]
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
            },
            Pattern::Map { collection, params, body } => {
                let mut vars = collection.free_vars();
                // Body vars, minus the params (which are bound by the map)
                let mut body_vars = body.free_vars();
                for param in params {
                    body_vars.remove(&param.to_string());
                }
                vars.extend(body_vars);
                vars
            },
            Pattern::Zip { first, second } => {
                let mut vars = first.free_vars();
                vars.extend(second.free_vars());
                vars
            },
        }
    }

    /// Check if this pattern is just a variable (no constructor or structure)
    /// Used to avoid generating equation rules that match everything.
    /// Example: For equation `@(*N) == N`, the RHS `N` is just a variable,
    /// so we shouldn't generate the backward direction N => @(*N).
    pub fn is_just_variable(&self) -> bool {
        matches!(self, Pattern::Term(PatternTerm::Var(_)))
    }

    /// Get the constructor name if this is a constructor application
    /// NOTE: Collection patterns no longer have constructors - they get it from enclosing Apply
    #[allow(dead_code)]
    pub fn constructor_name(&self) -> Option<&Ident> {
        match self {
            Pattern::Term(PatternTerm::Apply { constructor, .. }) => Some(constructor),
            // Collections don't have constructors anymore - that's in the parent Apply
            _ => None,
        }
    }

    /// Infer the category this pattern produces (if determinable)
    ///
    /// Returns `Some(category)` if the pattern unambiguously produces that category.
    /// Returns `None` for variables (unknown without context) or errors.
    ///
    /// NOTE: Collection patterns return None - they get their category from
    /// the enclosing PatternTerm::Apply which knows the constructor.
    pub fn category<'a>(&self, language: &'a LanguageDef) -> Option<&'a Ident> {
        match self {
            Pattern::Term(pt) => pt.category(language),
            // Collections don't know their category - it comes from enclosing Apply
            Pattern::Collection { .. } => None,
            // Map produces elements of the body's category
            Pattern::Map { body, .. } => body.category(language),
            Pattern::Zip { first, .. } => {
                // Zip produces a collection of tuples - category depends on first
                first.category(language)
            },
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
            },
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
            },
            Pattern::Zip { first, second } => {
                first.collect_var_occurrences(counts);
                second.collect_var_occurrences(counts);
            },
        }
    }
}

impl PatternTerm {
    /// Infer the category this pattern term produces
    pub fn category<'a>(&self, language: &'a LanguageDef) -> Option<&'a Ident> {
        match self {
            PatternTerm::Var(_) => None, // Variables need context
            PatternTerm::Apply { constructor, .. } => language.category_of_constructor(constructor),
            PatternTerm::Lambda { body, .. } => body.category(language),
            PatternTerm::MultiLambda { body, .. } => body.category(language),
            PatternTerm::Subst { term, .. } => term.category(language),
            PatternTerm::MultiSubst { scope, .. } => scope.category(language),
        }
    }

    fn collect_var_occurrences(&self, counts: &mut HashMap<String, usize>) {
        match self {
            PatternTerm::Var(v) => {
                *counts.entry(v.to_string()).or_insert(0) += 1;
            },
            PatternTerm::Apply { args, .. } => {
                for arg in args {
                    arg.collect_var_occurrences(counts);
                }
            },
            PatternTerm::Lambda { binder, body } => {
                // binder is bound, not an occurrence
                let mut body_counts = HashMap::new();
                body.collect_var_occurrences(&mut body_counts);
                body_counts.remove(&binder.to_string());
                for (var, count) in body_counts {
                    *counts.entry(var).or_insert(0) += count;
                }
            },
            PatternTerm::MultiLambda { binders, body } => {
                let mut body_counts = HashMap::new();
                body.collect_var_occurrences(&mut body_counts);
                for binder in binders {
                    body_counts.remove(&binder.to_string());
                }
                for (var, count) in body_counts {
                    *counts.entry(var).or_insert(0) += count;
                }
            },
            PatternTerm::Subst { term, var, replacement } => {
                term.collect_var_occurrences(counts);
                *counts.entry(var.to_string()).or_insert(0) += 1;
                replacement.collect_var_occurrences(counts);
            },
            PatternTerm::MultiSubst { scope, replacements } => {
                scope.collect_var_occurrences(counts);
                for repl in replacements {
                    repl.collect_var_occurrences(counts);
                }
            },
        }
    }
}

// ============================================================================
// AscentClauses: Result of pattern-to-clause conversion
// ============================================================================

/// Result of converting a pattern to Ascent clauses.
/// This is the unified abstraction for LHS pattern matching.
/// Whether a scope variable is single-binder or multi-binder
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeKind {
    /// Single binder: Scope<Binder<String>, Box<T>>
    Single,
    /// Multi binder: Scope<Vec<Binder<String>>, Box<T>>
    Multi,
    /// Collection variable capturing the entire Vec<Binder<String>>
    /// Used when a single variable in ^[xs] matches all binders of a multi-abstraction
    MultiCollection,
}

#[derive(Debug, Clone)]
pub struct VariableBinding {
    pub expression: TokenStream,
    pub lang_type: Ident,
    pub scope_kind: Option<ScopeKind>,
}

#[derive(Default)]
pub struct AscentClauses {
    /// The clauses to add to the rule body (if let ..., for loops, etc.)
    pub clauses: Vec<TokenStream>,
    pub bindings: HashMap<String, VariableBinding>,
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
        language: &LanguageDef,
        duplicate_vars: &HashSet<String>,
    ) -> AscentClauses {
        let mut result = AscentClauses::default();
        let mut first_occurrences = HashSet::new();
        let mut iter_counter = 0usize; // Global counter for iteration variables

        self.generate_clauses(
            term_var,
            category,
            language,
            duplicate_vars,
            &mut result,
            &mut first_occurrences,
            &mut iter_counter,
            None, // No enclosing search_context at top level
        );

        result
    }

    #[allow(clippy::too_many_arguments)]
    fn generate_clauses(
        &self,
        term_var: &Ident,
        category: &Ident,
        language: &LanguageDef,
        duplicate_vars: &HashSet<String>,
        result: &mut AscentClauses,
        first_occurrences: &mut HashSet<String>,
        iter_counter: &mut usize,
        search_context: Option<&Ident>, // Enclosing collection for Zip correlated search
    ) {
        match self {
            Pattern::Term(pt) => {
                pt.generate_clauses(
                    term_var,
                    category,
                    language,
                    duplicate_vars,
                    result,
                    first_occurrences,
                    iter_counter,
                    search_context,
                );
            },

            Pattern::Collection { elements, rest, .. } => {
                // NOTE: Collection patterns appear inside PatternTerm::Apply.
                // The parent Apply already:
                //   1. Destructured to get the bag field as term_var
                //   2. Passed the element type as `category`
                // So here, term_var IS the bag and `category` IS the element type.

                let elem_cat = category;
                let bag_var = term_var;

                // This collection becomes the search_context for nested Map patterns
                let nested_search_context = Some(bag_var);

                // Track variables for rest calculation:
                // - elem_vars: single elements bound via iteration
                // - matched_indices_vars: sets of indices from Map patterns (which match multiple elements)
                let mut elem_vars = Vec::new();
                let mut matched_indices_vars: Vec<Ident> = Vec::new();

                for (i, elem) in elements.iter().enumerate() {
                    // Map patterns match MULTIPLE elements and collect them
                    // They handle their own iteration and track matched indices
                    if matches!(elem, Pattern::Map { .. }) {
                        // Map pattern - will generate its own search and track matched indices
                        let idx_var = format_ident!("__map_matched_indices_{}", *iter_counter);
                        matched_indices_vars.push(idx_var);

                        elem.generate_clauses(
                            bag_var,
                            elem_cat,
                            language,
                            duplicate_vars,
                            result,
                            first_occurrences,
                            iter_counter,
                            nested_search_context,
                        );
                        continue;
                    }

                    // Standard element: iterate and match ONE element
                    let elem_var = format_ident!("{}_e{}", term_var, i);
                    let count_var = format_ident!("_count_{}", *iter_counter);
                    *iter_counter += 1;
                    elem_vars.push(elem_var.clone());

                    result.clauses.push(quote! {
                        for (#elem_var, #count_var) in #bag_var.iter()
                    });

                    // Distinctness: each element must be different from previous single elements
                    for prev in &elem_vars[..elem_vars.len() - 1] {
                        result.clauses.push(quote! {
                            if &#elem_var != &#prev
                        });
                    }

                    elem.generate_clauses(
                        &elem_var,
                        elem_cat,
                        language,
                        duplicate_vars,
                        result,
                        first_occurrences,
                        iter_counter,
                        nested_search_context,
                    );
                }

                // Bind rest variable if present
                if let Some(rest_var) = rest {
                    let rest_ident = format_ident!("{}_rest", term_var);

                    if elem_vars.is_empty() && matched_indices_vars.is_empty() {
                        result.clauses.push(quote! {
                            let #rest_ident = #bag_var.clone()
                        });
                    } else {
                        // Remove ALL matched elements:
                        // 1. Single elements (elem_vars)
                        // 2. All elements at indices from Map patterns (matched_indices_vars)
                        let remove_singles = if elem_vars.is_empty() {
                            quote! {}
                        } else {
                            quote! { #(bag.remove(&#elem_vars);)* }
                        };

                        let remove_map_matched = if matched_indices_vars.is_empty() {
                            quote! {}
                        } else {
                            quote! {
                                let __ctx_vec: Vec<_> = #bag_var.iter().collect();
                                #(
                                    for __idx in #matched_indices_vars.iter() {
                                        if let Some((elem, _)) = __ctx_vec.get(*__idx) {
                                            bag.remove(elem);
                                        }
                                    }
                                )*
                            }
                        };

                        result.clauses.push(quote! {
                            let #rest_ident = {
                                let mut bag = #bag_var.clone();
                                #remove_singles
                                #remove_map_matched
                                bag
                            }
                        });
                    }
                    result.bindings.insert(
                        rest_var.to_string(),
                        VariableBinding {
                            expression: quote! { #rest_ident.clone() },
                            lang_type: category.clone(),
                            scope_kind: None,
                        },
                    );
                }
            },

            Pattern::Map { collection, params, body } => {
                // Map on LHS: search for elements in a collection where each element
                // matches the body pattern after binding the params
                //
                // Special case: when collection is a Zip, this is a correlated search.
                // #zip(first, second).#map(|a, b| Body(a, b)): first is bound from context;
                // for each a in first we search search_context for elements matching Body(a, b),
                // and collect b's into second. We enumerate all valid matchings (one context
                // element per first element, distinct indices) so rules fire for every possibility.
                if let Pattern::Zip { first, second } = collection.as_ref() {
                    // Correlated search: Zip + Map. First is bound; second collects from matches.

                    let Some(ctx) = search_context else {
                        panic!("Zip+Map pattern requires search_context from enclosing Collection");
                    };

                    // Get variable names from first and second
                    let first_var_name = match first.as_ref() {
                        Pattern::Term(PatternTerm::Var(v)) => v.to_string(),
                        _ => panic!("Zip first must be a variable"),
                    };
                    let second_var_name = match second.as_ref() {
                        Pattern::Term(PatternTerm::Var(v)) => v.to_string(),
                        _ => panic!("Zip second must be a variable"),
                    };

                    // first should already be bound - get its binding
                    // remove immutable borrow of result.bindings
                    let first_binding = result
                        .bindings
                        .get_mut(&first_var_name)
                        .map(|b| &b.expression)
                        .unwrap()
                        .clone();

                    if params.len() != 2 {
                        panic!("Zip+Map requires exactly 2 params, got {}", params.len());
                    }
                    let first_param = &params[0]; // bound to each element of first
                    let second_param = &params[1]; // extracted from matching context element

                    let iter_idx = *iter_counter;
                    *iter_counter += 1;

                    let first_elem = format_ident!("__zip_first_{}", iter_idx);
                    let search_elem = format_ident!("__zip_search_{}", iter_idx);
                    let collected_var = format_ident!("__zip_collected_{}", iter_idx);

                    // Bind first_param to first_elem for body pattern matching
                    result.bindings.insert(
                        first_param.to_string(),
                        VariableBinding {
                            expression: quote! { #first_elem.clone() },
                            lang_type: category.clone(),
                            scope_kind: None,
                        },
                    );

                    let (constructor, body_args) = match body.as_ref() {
                        Pattern::Term(PatternTerm::Apply { constructor, args }) => {
                            (constructor.clone(), args.clone())
                        },
                        _ => panic!("Zip+Map body must be a constructor pattern"),
                    };

                    // Find which arg position corresponds to first_param and second_param
                    let mut first_param_idx = None;
                    let mut second_param_idx = None;
                    for (i, arg) in body_args.iter().enumerate() {
                        if let Pattern::Term(PatternTerm::Var(v)) = arg {
                            if *v == *first_param {
                                first_param_idx = Some(i);
                            }
                            if *v == *second_param {
                                second_param_idx = Some(i);
                            }
                        }
                    }

                    let first_idx = first_param_idx.expect("first_param not found in body pattern");
                    let second_idx =
                        second_param_idx.expect("second_param not found in body pattern");

                    // Generate field variables for the constructor match
                    let field_vars: Vec<Ident> = (0..body_args.len())
                        .map(|i| format_ident!("__match_f{}_{}", i, iter_idx))
                        .collect();

                    let first_field = &field_vars[first_idx];
                    let second_field = &field_vars[second_idx];

                    // Generate the correlated search. Fields are Box<T> (deref &**).
                    // Enumerate all valid matchings: one context element per first element,
                    // distinct indices, so the rule fires once per possibility (e.g. multiple
                    // sends on the same name yield multiple rewrites).
                    let matched_indices_var = format_ident!("__map_matched_indices_{}", iter_idx);
                    let all_matchings_var = format_ident!("__all_matchings_{}", iter_idx);

                    // 1) Build candidates: per first-element, list of (context_index, payload) for matching body
                    result.clauses.push(quote! {
                        let #all_matchings_var = {
                            let __ctx_vec: Vec<_> = #ctx.iter().collect();
                            let mut __candidates = Vec::new();
                            for #first_elem in #first_binding.iter() {
                                let mut __row = Vec::new();
                                for (__idx, (#search_elem, _)) in __ctx_vec.iter().enumerate() {
                                    if let #category::#constructor(#(ref #field_vars),*) = #search_elem {
                                        if &**#first_field == #first_elem {
                                            __row.push((__idx, (**#second_field).clone()));
                                        }
                                    }
                                }
                                __candidates.push(__row);
                            }
                            mettail_runtime::enumerate_matchings(&__candidates)
                        }
                    });

                    // 2) For each valid matching, bind collected payloads and matched indices
                    result.clauses.push(quote! {
                        for (#collected_var, #matched_indices_var) in #all_matchings_var.into_iter()
                    });

                    // One payload per first-element (full matching)
                    result.clauses.push(quote! {
                        if #collected_var.len() == #first_binding.len()
                    });

                    // Bind second (qs) to the collected results
                    result.bindings.insert(
                        second_var_name,
                        VariableBinding {
                            expression: quote! { #collected_var.clone() },
                            lang_type: category.clone(),
                            scope_kind: None,
                        },
                    );
                } else {
                    // Regular map: iterate over collection

                    // First, process the collection to get its binding
                    collection.generate_clauses(
                        &format_ident!("__map_coll"),
                        category,
                        language,
                        duplicate_vars,
                        result,
                        first_occurrences,
                        iter_counter,
                        search_context,
                    );

                    // For LHS map, we need to generate iteration over the collection
                    // and for each element, check if it matches the body pattern
                    let iter_idx = *iter_counter;
                    *iter_counter += 1;
                    let elem_var = format_ident!("__map_elem_{}", iter_idx);

                    // Bind each param to the element (or element parts for multi-param)
                    if params.len() == 1 {
                        let param = &params[0];
                        result.bindings.insert(
                            param.to_string(),
                            VariableBinding {
                                expression: quote! { #elem_var },
                                lang_type: category.clone(),
                                scope_kind: None,
                            },
                        );
                    } else if params.len() == 2 {
                        // For zipped pairs
                        result.bindings.insert(
                            params[0].to_string(),
                            VariableBinding {
                                expression: quote! { #elem_var.0 },
                                lang_type: category.clone(),
                                scope_kind: None,
                            },
                        );
                        result.bindings.insert(
                            params[1].to_string(),
                            VariableBinding {
                                expression: quote! { #elem_var.1 },
                                lang_type: category.clone(),
                                scope_kind: None,
                            },
                        );
                    }

                    // Generate iteration clause
                    result.clauses.push(quote! {
                        for (#elem_var, _) in __map_coll.iter()
                    });

                    // Process body pattern with elem_var bindings
                    // This adds match clauses for the body pattern
                    body.generate_clauses(
                        &elem_var,
                        category,
                        language,
                        duplicate_vars,
                        result,
                        first_occurrences,
                        iter_counter,
                        search_context,
                    );
                }
            },

            Pattern::Zip { first, second } => {
                // Zip on LHS: standalone usage (rare)
                //
                // When Zip appears chained with Map (e.g., #zip(ns, qs).#map(...)),
                // the Map handles the correlated search logic. This case handles
                // standalone Zip which just sets up variable bindings.
                //
                // Standalone Zip without Map is unusual and limited in functionality.

                // Get variable names if they're simple vars
                let first_var_name = match first.as_ref() {
                    Pattern::Term(PatternTerm::Var(v)) => Some(v.to_string()),
                    _ => None,
                };
                let second_var_name = match second.as_ref() {
                    Pattern::Term(PatternTerm::Var(v)) => Some(v.to_string()),
                    _ => None,
                };

                // Set up bindings for both variables
                if let Some(first_name) = &first_var_name {
                    if !result.bindings.contains_key(first_name) {
                        let first_ident = format_ident!("{}", first_name);
                        result.bindings.insert(
                            first_name.clone(),
                            VariableBinding {
                                expression: quote! { #first_ident.clone() },
                                lang_type: category.clone(),
                                scope_kind: None,
                            },
                        );
                    }
                }

                if let Some(second_name) = &second_var_name {
                    if !result.bindings.contains_key(second_name) {
                        let second_ident = format_ident!("{}", second_name);
                        result.bindings.insert(
                            second_name.clone(),
                            VariableBinding {
                                expression: quote! { #second_ident.clone() },
                                lang_type: category.clone(),
                                scope_kind: None,
                            },
                        );
                    }
                }

                // If patterns are more complex (not just variables), process them
                if first_var_name.is_none() {
                    first.generate_clauses(
                        &format_ident!("__zip_first"),
                        category,
                        language,
                        duplicate_vars,
                        result,
                        first_occurrences,
                        iter_counter,
                        search_context,
                    );
                }

                if second_var_name.is_none() {
                    second.generate_clauses(
                        &format_ident!("__zip_second"),
                        category,
                        language,
                        duplicate_vars,
                        result,
                        first_occurrences,
                        iter_counter,
                        search_context,
                    );
                }
            },
        }
    }
}

impl PatternTerm {
    #[allow(clippy::too_many_arguments)]
    fn generate_clauses(
        &self,
        term_var: &Ident,
        category: &Ident,
        language: &LanguageDef,
        duplicate_vars: &HashSet<String>,
        result: &mut AscentClauses,
        first_occurrences: &mut HashSet<String>,
        iter_counter: &mut usize,
        search_context: Option<&Ident>, // Enclosing collection for Zip correlated search
    ) {
        match self {
            PatternTerm::Var(v) => {
                let var_name = v.to_string();

                if duplicate_vars.contains(&var_name) {
                    // Duplicate variable - need equational check
                    if first_occurrences.insert(var_name.clone()) {
                        // First occurrence: bind it
                        result.bindings.insert(
                            var_name.clone(),
                            VariableBinding {
                                expression: quote! { #term_var.clone() },
                                lang_type: category.clone(),
                                scope_kind: None,
                            },
                        );
                    } else {
                        // Subsequent occurrence: emit eq check
                        let existing = result
                            .bindings
                            .get(&var_name)
                            .map(|b| &b.expression)
                            .unwrap();
                        let eq_rel = format_ident!("eq_{}", category.to_string().to_lowercase());
                        result.equational_checks.push(quote! {
                            #eq_rel(#existing, #term_var.clone())
                        });
                    }
                } else {
                    // Single-occurrence variable: just bind
                    result.bindings.insert(
                        var_name.clone(),
                        VariableBinding {
                            expression: quote! { #term_var.clone() },
                            lang_type: category.clone(),
                            scope_kind: None,
                        },
                    );
                }
            },

            PatternTerm::Apply { constructor, args } => {
                let rule = language
                    .get_constructor(constructor)
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
                                let is_unboxed =
                                    field_cat_str == "Var" || field_cat_str == "Integer";
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
                                    &deref_var,
                                    field_cat,
                                    language,
                                    duplicate_vars,
                                    result,
                                    first_occurrences,
                                    iter_counter,
                                    search_context,
                                );
                                field_idx += 1;
                            }
                        },
                        GrammarItem::Collection { element_type, .. } => {
                            if field_idx < args.len() {
                                // Collection field - delegate to collection handling
                                // Pass the field variable as search_context for nested Zip patterns
                                let field_var = &field_vars[field_idx];
                                args[field_idx].generate_clauses(
                                    field_var,
                                    element_type,
                                    language,
                                    duplicate_vars,
                                    result,
                                    first_occurrences,
                                    iter_counter,
                                    Some(field_var),
                                );
                                field_idx += 1;
                            }
                        },
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
                                if let Pattern::Term(PatternTerm::Lambda { binder, body }) =
                                    &args[field_idx]
                                {
                                    // Single binder: binder_var is Binder<String>
                                    // Bind the Lambda's binder name to the inner FreeVar (Binder.0)
                                    result.bindings.insert(
                                        binder.to_string(),
                                        VariableBinding {
                                            expression: quote! { #binder_var.0.clone() },
                                            lang_type: category.clone(),
                                            scope_kind: Some(ScopeKind::Single),
                                        },
                                    );

                                    // Also bind the full binder for RHS reconstruction
                                    result.bindings.insert(
                                        format!("__binder_{}", binder),
                                        VariableBinding {
                                            expression: quote! { #binder_var.clone() },
                                            lang_type: category.clone(),
                                            scope_kind: Some(ScopeKind::Single),
                                        },
                                    );

                                    // Process the Lambda's body with body_var
                                    body.generate_clauses(
                                        &body_var,
                                        body_cat,
                                        language,
                                        duplicate_vars,
                                        result,
                                        first_occurrences,
                                        iter_counter,
                                        search_context,
                                    );
                                } else if let Pattern::Term(PatternTerm::MultiLambda {
                                    binders,
                                    body,
                                }) = &args[field_idx]
                                {
                                    // Detect collection-variable mode: single binder name
                                    // matching a MultiAbstraction captures the entire Vec<Binder<String>>
                                    let is_collection_var = binders.len() == 1
                                        && rule.term_context.as_ref().is_some_and(|tc| {
                                            tc.iter().any(|p| {
                                                matches!(
                                                    p,
                                                    super::grammar::TermParam::MultiAbstraction { .. }
                                                )
                                            })
                                        });

                                    if is_collection_var {
                                        let var_name = &binders[0];
                                        result.bindings.insert(
                                            var_name.to_string(),
                                            VariableBinding {
                                                expression: quote! { #binder_var.clone() },
                                                lang_type: category.clone(),
                                                scope_kind: Some(ScopeKind::MultiCollection),
                                            },
                                        );
                                    } else {
                                        // Individual binder matching: bind each to its position
                                        for (i, binder) in binders.iter().enumerate() {
                                            let binder_elem_var =
                                                format_ident!("{}_b{}", field_var, i);
                                            let idx = syn::Index::from(i);

                                            result.clauses.push(quote! {
                                                let #binder_elem_var = #binder_var[#idx].clone()
                                            });

                                            result.bindings.insert(
                                                binder.to_string(),
                                                VariableBinding {
                                                    expression: quote! { #binder_elem_var.0.clone() },
                                                    lang_type: category.clone(),
                                                    scope_kind: Some(ScopeKind::Multi),
                                                },
                                            );

                                            result.bindings.insert(
                                                format!("__binder_{}", binder),
                                                VariableBinding {
                                                    expression: quote! { #binder_elem_var.clone() },
                                                    lang_type: category.clone(),
                                                    scope_kind: Some(ScopeKind::Multi),
                                                },
                                            );
                                        }
                                    }

                                    // Process the MultiLambda's body with body_var
                                    body.generate_clauses(
                                        &body_var,
                                        body_cat,
                                        language,
                                        duplicate_vars,
                                        result,
                                        first_occurrences,
                                        iter_counter,
                                        search_context,
                                    );
                                } else if let Pattern::Term(PatternTerm::Var(v)) = &args[field_idx]
                                {
                                    // Simple variable in binder position - bind to the FULL SCOPE
                                    // This is for patterns like (PInputs ns scope) where scope
                                    // should capture the entire Scope object for later use with multisubst
                                    result.bindings.insert(
                                        v.to_string(),
                                        VariableBinding {
                                            expression: quote! { #field_var.clone() },
                                            lang_type: category.clone(),
                                            scope_kind: None,
                                        },
                                    );

                                    // Determine if this is a single or multi-binder scope from term_context
                                    let scope_kind = if let Some(ref term_context) =
                                        rule.term_context
                                    {
                                        // Count which abstraction param this is
                                        let mut binder_count = 0;
                                        let mut found_kind = ScopeKind::Single; // default
                                        for item in &rule.items[..=field_idx] {
                                            if matches!(item, GrammarItem::Binder { .. }) {
                                                // Look for the corresponding abstraction param
                                                let mut abs_count = 0;
                                                for param in term_context {
                                                    match param {
                                                        super::grammar::TermParam::Abstraction { .. } => {
                                                            if abs_count == binder_count {
                                                                found_kind = ScopeKind::Single;
                                                            }
                                                            abs_count += 1;
                                                        }
                                                        super::grammar::TermParam::MultiAbstraction { .. } => {
                                                            if abs_count == binder_count {
                                                                found_kind = ScopeKind::Multi;
                                                            }
                                                            abs_count += 1;
                                                        }
                                                        _ => {}
                                                    }
                                                }
                                                binder_count += 1;
                                            }
                                        }
                                        found_kind
                                    } else {
                                        // No term_context, assume single binder (old syntax)
                                        ScopeKind::Single
                                    };
                                    result.bindings.insert(
                                        v.to_string(),
                                        VariableBinding {
                                            expression: quote! { #field_var.clone() },
                                            lang_type: category.clone(),
                                            scope_kind: Some(scope_kind),
                                        },
                                    );
                                } else {
                                    // Other pattern in binder position - process as body pattern
                                    args[field_idx].generate_clauses(
                                        &body_var,
                                        body_cat,
                                        language,
                                        duplicate_vars,
                                        result,
                                        first_occurrences,
                                        iter_counter,
                                        search_context,
                                    );
                                }
                                field_idx += 1;
                            }
                        },
                        GrammarItem::Terminal(_) => {
                            // Skip terminals
                        },
                    }
                }
            },

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
                result.bindings.insert(
                    binder.to_string(),
                    VariableBinding {
                        expression: quote! { #binder_var.0.clone() },
                        lang_type: category.clone(),
                        scope_kind: Some(ScopeKind::Single),
                    },
                );

                // Also bind the full binder for RHS reconstruction
                result.bindings.insert(
                    format!("__binder_{}", binder),
                    VariableBinding {
                        expression: quote! { #binder_var.clone() },
                        lang_type: category.clone(),
                        scope_kind: Some(ScopeKind::Single),
                    },
                );

                // Recursively process body
                // The body has the same category as the enclosing term (from context)
                // For Scope<Binder, Body>, both the Scope and Body have the same category
                body.generate_clauses(
                    &body_var,
                    category,
                    language,
                    duplicate_vars,
                    result,
                    first_occurrences,
                    iter_counter,
                    search_context,
                );
            },

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

                // Bind each binder variable to its corresponding element in the Vec
                // For ^[x,y].body: bind x to binders[0], y to binders[1]
                for (i, binder) in binders.iter().enumerate() {
                    let binder_elem_var = format_ident!("{}_b{}", term_var, i);
                    let idx = syn::Index::from(i);

                    // Extract the i-th binder from the Vec
                    result.clauses.push(quote! {
                        let #binder_elem_var = #binders_var[#idx].clone()
                    });

                    // Bind the binder name to its FreeVar (the .0 field)
                    result.bindings.insert(
                        binder.to_string(),
                        VariableBinding {
                            expression: quote! { #binder_elem_var.0.clone() },
                            lang_type: category.clone(),
                            scope_kind: Some(ScopeKind::Multi),
                        },
                    );

                    // Also bind the full binder for RHS reconstruction
                    result.bindings.insert(
                        format!("__binder_{}", binder),
                        VariableBinding {
                            expression: quote! { #binder_elem_var.clone() },
                            lang_type: category.clone(),
                            scope_kind: Some(ScopeKind::Multi),
                        },
                    );
                }

                // Recursively process body with the same category as the enclosing term
                body.generate_clauses(
                    &body_var,
                    category,
                    language,
                    duplicate_vars,
                    result,
                    first_occurrences,
                    iter_counter,
                    search_context,
                );
            },

            PatternTerm::Subst { .. } => {
                // Substitution in LHS is unusual
                unimplemented!("Subst in LHS patterns not supported")
            },

            PatternTerm::MultiSubst { .. } => {
                unimplemented!("MultiSubst in LHS patterns not supported")
            },
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
        bindings: &HashMap<String, VariableBinding>,
        language: &LanguageDef,
    ) -> TokenStream {
        match self {
            Pattern::Term(pt) => pt.to_ascent_rhs(bindings, language),
            Pattern::Collection { coll_type, elements, rest } => self.generate_collection_rhs(
                coll_type.as_ref(),
                elements,
                rest.as_ref(),
                bindings,
                language,
            ),
            Pattern::Map { collection, params, body } => {
                self.generate_map_rhs(collection, params, body, bindings, language)
            },
            Pattern::Zip { first, second } => {
                self.generate_zip_rhs(first, second, bindings, language)
            },
        }
    }

    fn generate_collection_rhs(
        &self,
        coll_type: Option<&CollectionType>,
        elements: &[Pattern],
        rest: Option<&Ident>,
        bindings: &HashMap<String, VariableBinding>,
        language: &LanguageDef,
    ) -> TokenStream {
        let elem_exprs: Vec<_> = elements
            .iter()
            .map(|e| e.to_ascent_rhs(bindings, language))
            .collect();

        // Use coll_type if provided, default to HashBag
        let coll_type_tok = match coll_type {
            Some(CollectionType::Vec) => quote! { Vec },
            Some(CollectionType::HashSet) => quote! { std::collections::HashSet },
            Some(CollectionType::HashBag) | None => quote! { mettail_runtime::HashBag },
        };

        // Generate insert/push based on collection type
        let use_vec = matches!(coll_type, Some(CollectionType::Vec));

        if let Some(rest_var) = rest {
            let rest_name = rest_var.to_string();
            let rest_ident = quote::format_ident!("{}", rest_name);
            let rest_binding = bindings
                .get(&rest_name)
                .map(|b| b.expression.clone())
                .unwrap_or_else(|| quote! { #rest_ident });

            if use_vec {
                quote! {
                    {
                        let mut coll = (#rest_binding).clone();
                        #(coll.push(#elem_exprs);)*
                        coll
                    }
                }
            } else {
                quote! {
                    {
                        let mut bag = (#rest_binding).clone();
                        #(bag.insert(#elem_exprs);)*
                        bag
                    }
                }
            }
        } else if use_vec {
            quote! {
                {
                    let mut coll = Vec::new();
                    #(coll.push(#elem_exprs);)*
                    coll
                }
            }
        } else {
            quote! {
                {
                    let mut bag = #coll_type_tok::new();
                    #(bag.insert(#elem_exprs);)*
                    bag
                }
            }
        }
    }
}

/// Generate collection RHS with constructor context for proper insert helpers
fn generate_collection_rhs_with_constructor(
    coll_type: Option<&CollectionType>,
    elements: &[Pattern],
    rest: Option<&Ident>,
    constructor: Option<&Ident>,
    category: &Ident,
    bindings: &HashMap<String, VariableBinding>,
    language: &LanguageDef,
) -> TokenStream {
    let elem_exprs: Vec<_> = elements
        .iter()
        .map(|e| e.to_ascent_rhs(bindings, language))
        .collect();

    // Use coll_type if provided, default to HashBag
    let coll_type_tok = match coll_type {
        Some(CollectionType::Vec) => quote! { Vec },
        Some(CollectionType::HashSet) => quote! { std::collections::HashSet },
        Some(CollectionType::HashBag) | None => quote! { mettail_runtime::HashBag },
    };

    let use_vec = matches!(coll_type, Some(CollectionType::Vec));

    // Get insert helper if constructor is provided (for flattening)
    let insert_helper = constructor.map(|cons| {
        let cons_lower = format_ident!("{}", cons.to_string().to_lowercase());
        format_ident!("insert_into_{}", cons_lower)
    });

    if let Some(rest_var) = rest {
        let rest_name = rest_var.to_string();
        let rest_ident = quote::format_ident!("{}", rest_name);
        let rest_binding = bindings
            .get(&rest_name)
            .map(|b| b.expression.clone())
            .unwrap_or_else(|| quote! { #rest_ident });

        if use_vec {
            quote! {
                {
                    let mut coll = (#rest_binding).clone();
                    #(coll.push(#elem_exprs);)*
                    coll
                }
            }
        } else if let Some(helper) = &insert_helper {
            // Use insert helper for flattening
            quote! {
                {
                    let mut bag = (#rest_binding).clone();
                    #(#category::#helper(&mut bag, #elem_exprs);)*
                    bag
                }
            }
        } else {
            quote! {
                {
                    let mut bag = (#rest_binding).clone();
                    #(bag.insert(#elem_exprs);)*
                    bag
                }
            }
        }
    } else if use_vec {
        quote! {
            {
                let mut coll = Vec::new();
                #(coll.push(#elem_exprs);)*
                coll
            }
        }
    } else if let Some(helper) = &insert_helper {
        // Use insert helper for flattening
        quote! {
            {
                let mut bag = #coll_type_tok::new();
                #(#category::#helper(&mut bag, #elem_exprs);)*
                bag
            }
        }
    } else {
        quote! {
            {
                let mut bag = #coll_type_tok::new();
                #(bag.insert(#elem_exprs);)*
                bag
            }
        }
    }
}

impl Pattern {
    fn generate_map_rhs(
        &self,
        collection: &Pattern,
        params: &[Ident],
        body: &Pattern,
        bindings: &HashMap<String, VariableBinding>,
        language: &LanguageDef,
    ) -> TokenStream {
        // Generate: iterate collection, apply body transform to each element
        let coll_expr = collection.to_ascent_rhs(bindings, language);

        // Determine if source collection is Vec or HashBag
        // For now, check if collection is a Pattern::Collection with coll_type
        let is_vec =
            matches!(collection, Pattern::Collection { coll_type: Some(CollectionType::Vec), .. });

        // Get a default lang_type for iteration variables (use first binding's type or a placeholder)
        let default_lang_type = bindings
            .values()
            .next()
            .map(|b| b.lang_type.clone())
            .unwrap_or_else(|| format_ident!("Unknown"));

        if params.len() == 1 {
            // Single param: xs.#map(|x| body)
            let param = &params[0];
            let param_name = param.to_string();

            // Create extended bindings with param bound to iteration variable
            let mut body_bindings = bindings.clone();
            body_bindings.insert(
                param_name,
                VariableBinding {
                    expression: quote! { __elem },
                    lang_type: default_lang_type.clone(),
                    scope_kind: None,
                },
            );

            let body_expr = body.to_ascent_rhs(&body_bindings, language);

            if is_vec {
                quote! {
                    {
                        let __coll = #coll_expr;
                        let mut __result = Vec::new();
                        for __elem in __coll.iter() {
                            let __mapped = #body_expr;
                            __result.push(__mapped);
                        }
                        __result
                    }
                }
            } else {
                quote! {
                    {
                        let __coll = #coll_expr;
                        let mut __result = mettail_runtime::HashBag::new();
                        for (__elem, __count) in __coll.iter() {
                            let __mapped = #body_expr;
                            for _ in 0..__count {
                                __result.insert(__mapped.clone());
                            }
                        }
                        __result
                    }
                }
            }
        } else if params.len() == 2 {
            // Two params: typically from zip - (xs, ys).#map(|x, y| body)
            let param0 = &params[0];
            let param1 = &params[1];

            // Create extended bindings
            let mut body_bindings = bindings.clone();
            body_bindings.insert(
                param0.to_string(),
                VariableBinding {
                    expression: quote! { __elem.0 },
                    lang_type: default_lang_type.clone(),
                    scope_kind: None,
                },
            );
            body_bindings.insert(
                param1.to_string(),
                VariableBinding {
                    expression: quote! { __elem.1 },
                    lang_type: default_lang_type.clone(),
                    scope_kind: None,
                },
            );

            let body_expr = body.to_ascent_rhs(&body_bindings, language);

            // When mapping over zipped pairs, always produce Vec
            quote! {
                {
                    let __coll = #coll_expr;
                    let mut __result = Vec::new();
                    for __elem in __coll.iter() {
                        let __mapped = #body_expr;
                        __result.push(__mapped);
                    }
                    __result
                }
            }
        } else {
            // More than 2 params - not yet supported
            quote! { compile_error!("Map with more than 2 params not yet supported") }
        }
    }

    fn generate_zip_rhs(
        &self,
        first: &Pattern,
        second: &Pattern,
        bindings: &HashMap<String, VariableBinding>,
        language: &LanguageDef,
    ) -> TokenStream {
        // Zip on RHS - pair-wise combination of collections
        // #zip(xs, ys) produces Vec<(X, Y)>
        let first_expr = first.to_ascent_rhs(bindings, language);
        let second_expr = second.to_ascent_rhs(bindings, language);

        quote! {
            {
                let __first: Vec<_> = (#first_expr).iter().cloned().collect();
                let __second: Vec<_> = (#second_expr).iter().cloned().collect();
                __first.into_iter().zip(__second.into_iter()).collect::<Vec<_>>()
            }
        }
    }
}

impl PatternTerm {
    pub fn to_ascent_rhs(
        &self,
        bindings: &HashMap<String, VariableBinding>,
        language: &LanguageDef,
    ) -> TokenStream {
        match self {
            PatternTerm::Var(v) => {
                let var_name = v.to_string();
                bindings
                    .get(&var_name)
                    .map(|b| {
                        let expr = &b.expression;
                        quote! { (#expr).clone() }
                    })
                    .unwrap_or_else(|| {
                        // Check if it's a nullary constructor
                        if let Some(rule) = language.get_constructor(v) {
                            let category = &rule.category;
                            quote! { #category::#v }
                        } else {
                            // TODO: Variable binding will be handled by unified rule generation
                            let var_ident = quote::format_ident!("{}", var_name);
                            quote! { #var_ident.clone() }
                        }
                    })
            },

            PatternTerm::Apply { constructor, args } => {
                let category = language
                    .category_of_constructor(constructor)
                    .expect("Unknown constructor");
                let rule = language.get_constructor(constructor).unwrap();

                let arg_exprs: Vec<_> = args
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        // Check if this arg needs Box wrapping
                        let needs_box = needs_box_for_field(rule, i, language);
                        let is_collection = is_collection_field(rule, i);

                        // For Collection args, pass the constructor for proper insert helper
                        let expr = if is_collection {
                            if let Pattern::Collection { coll_type, elements, rest } = arg {
                                // Generate collection RHS with constructor context
                                generate_collection_rhs_with_constructor(
                                    coll_type.as_ref(),
                                    elements,
                                    rest.as_ref(),
                                    Some(constructor),
                                    category,
                                    bindings,
                                    language,
                                )
                            } else {
                                arg.to_ascent_rhs(bindings, language)
                            }
                        } else {
                            arg.to_ascent_rhs(bindings, language)
                        };

                        if is_collection || !needs_box {
                            expr
                        } else {
                            quote! { Box::new(#expr) }
                        }
                    })
                    .collect();

                quote! { #category::#constructor(#(#arg_exprs),*) }
            },

            PatternTerm::Lambda { binder, body } => {
                // Construct a Scope using from_parts_unsafe to preserve binder identity!
                // Using Scope::new would re-close the body with a different binder ID,
                // causing infinite loops in equations.
                let body_expr = body.to_ascent_rhs(bindings, language);
                let binder_name = binder.to_string();
                let full_binder_key = format!("__binder_{}", binder);

                let binder_expr = if let Some(full_binder) = bindings.get(&full_binder_key) {
                    // Use the full original Binder from LHS (preserves identity!)
                    let expr = &full_binder.expression;
                    quote! { #expr.clone() }
                } else if let Some(bound_freevar) = bindings.get(&binder_name) {
                    // Fallback: wrap the FreeVar in a new Binder
                    let expr = &bound_freevar.expression;
                    quote! { mettail_runtime::Binder(#expr.clone()) }
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
            },

            PatternTerm::MultiLambda { binders, body } => {
                let body_expr = body.to_ascent_rhs(bindings, language);

                // Collection-variable mode: single binder capturing entire Vec<Binder<String>>
                if binders.len() == 1 {
                    let name = binders[0].to_string();
                    if let Some(binding) = bindings.get(&name) {
                        if binding.scope_kind == Some(ScopeKind::MultiCollection) {
                            let binder_expr = &binding.expression;
                            return quote! {
                                mettail_runtime::Scope::from_parts_unsafe(
                                    #binder_expr,
                                    Box::new(#body_expr)
                                )
                            };
                        }
                    }
                }

                // Individual binder construction
                let binder_exprs: Vec<_> = binders.iter().map(|b| {
                    let binder_name = b.to_string();
                    let full_binder_key = format!("__binder_{}", b);
                    if let Some(full_binder) = bindings.get(&full_binder_key) {
                        let expr = &full_binder.expression;
                        quote! { #expr.clone() }
                    } else if let Some(bound_freevar) = bindings.get(&binder_name) {
                        let expr = &bound_freevar.expression;
                        quote! { mettail_runtime::Binder(#expr.clone()) }
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
            },

            PatternTerm::Subst { term, var, replacement } => {
                let term_expr = term.to_ascent_rhs(bindings, language);
                let repl_expr = replacement.to_ascent_rhs(bindings, language);

                // Determine category of replacement for method name
                // First try structural category inference, then fall back to bindings
                let repl_cat = replacement
                    .category(language)
                    .map(|c| c.to_string().to_lowercase())
                    .or_else(|| {
                        // If replacement is a variable, look up its category from LHS bindings
                        if let Pattern::Term(PatternTerm::Var(v)) = replacement.as_ref() {
                            bindings
                                .get(&v.to_string())
                                .map(|b| b.lang_type.to_string().to_lowercase())
                        } else {
                            None
                        }
                    })
                    .unwrap_or_else(|| {
                        // Last resort: try the binder's category (from the scope type)
                        bindings
                            .get(&var.to_string())
                            .map(|b| b.lang_type.to_string().to_lowercase())
                            .unwrap_or_else(|| "unknown".to_string())
                    });
                let subst_method = format_ident!("substitute_{}", repl_cat);

                // Check if we have the full Binder (from ^x.p pattern matching)
                // If so, we need to reconstruct the Scope and unbind to get consistent FreeVars
                // because the body was "closed" and contains BoundVars, not FreeVars
                let full_binder_key = format!("__binder_{}", var);
                if let Some(full_binder) = bindings.get(&full_binder_key) {
                    let binder_expr = &full_binder.expression;
                    // We matched a lambda pattern: reconstruct Scope, unbind, then substitute
                    quote! {{
                        // Reconstruct a Scope from the binder and body
                        let __scope = mettail_runtime::Scope::from_parts_unsafe(
                            #binder_expr.clone(),
                            Box::new(#term_expr)
                        );
                        // Unbind to get fresh, consistent FreeVar and body
                        let (__fresh_binder, __fresh_body) = __scope.unbind();
                        // Now substitute - the body has FreeVars that match __fresh_binder
                        // substitute_* methods expect &FreeVar<String>, not &OrdVar
                        __fresh_body.#subst_method(&__fresh_binder.0, &#repl_expr)
                    }}
                } else {
                    // Old style: var is bound directly to a FreeVar
                    let var_binding = bindings
                        .get(&var.to_string())
                        .expect("Substitution variable not bound");
                    let var_expr = &var_binding.expression;
                    quote! {
                        (#term_expr).#subst_method(&#var_expr, &#repl_expr)
                    }
                }
            },

            PatternTerm::MultiSubst { scope, replacements } => {
                // Multi-substitution for multi-binder scopes, OR single-binder scopes
                // New syntax: (subst ^[xs].body repls) or (subst scope repls)
                // Legacy syntax: (multisubst scope r0 r1 ...)

                // Get a default lang_type for temp bindings
                let default_lang_type = bindings
                    .values()
                    .next()
                    .map(|b| b.lang_type.clone())
                    .unwrap_or_else(|| format_ident!("Unknown"));

                // Determine category from first replacement
                // First try structural category inference, then fall back to bindings
                let repl_cat = replacements
                    .first()
                    .and_then(|r| r.category(language))
                    .map(|c| c.to_string().to_lowercase())
                    .or_else(|| {
                        // If first replacement is a variable, look up its category
                        if let Some(Pattern::Term(PatternTerm::Var(v))) = replacements.first() {
                            bindings
                                .get(&v.to_string())
                                .map(|b| b.lang_type.to_string().to_lowercase())
                        } else {
                            None
                        }
                    })
                    .unwrap_or_else(|| "unknown".to_string());

                // Helper to build replacements expression
                let build_repls_expr =
                    |bindings: &HashMap<String, VariableBinding>, default_lang_type: &Ident| {
                        if replacements.len() == 1 {
                            if let Pattern::Map { collection, params, body: map_body } =
                                &replacements[0]
                            {
                                let coll_expr = collection.to_ascent_rhs(bindings, language);
                                if params.len() == 1 {
                                    let param_name = params[0].to_string();
                                    let mut body_bindings = bindings.clone();
                                    body_bindings.insert(
                                        param_name,
                                        VariableBinding {
                                            expression: quote! { __elem },
                                            lang_type: default_lang_type.clone(),
                                            scope_kind: None,
                                        },
                                    );
                                    let body_expr =
                                        map_body.to_ascent_rhs(&body_bindings, language);
                                    quote! {{ let __map_coll = #coll_expr; __map_coll.iter().map(|__elem| #body_expr).collect::<Vec<_>>() }}
                                } else {
                                    let param0 = params[0].to_string();
                                    let param1 =
                                        params.get(1).map(|p| p.to_string()).unwrap_or_default();
                                    let mut body_bindings = bindings.clone();
                                    body_bindings.insert(
                                        param0,
                                        VariableBinding {
                                            expression: quote! { __elem.0 },
                                            lang_type: default_lang_type.clone(),
                                            scope_kind: None,
                                        },
                                    );
                                    body_bindings.insert(
                                        param1,
                                        VariableBinding {
                                            expression: quote! { __elem.1 },
                                            lang_type: default_lang_type.clone(),
                                            scope_kind: None,
                                        },
                                    );
                                    let body_expr =
                                        map_body.to_ascent_rhs(&body_bindings, language);
                                    quote! {{ let __map_coll = #coll_expr; __map_coll.iter().map(|__elem| #body_expr).collect::<Vec<_>>() }}
                                }
                            } else if let Pattern::Term(PatternTerm::Var(v)) = &replacements[0] {
                                // Variable bound to zip-collected payloads (e.g. qs = __zip_collected_1):
                                // use the collection as __repls, mapping each element to the replacement
                                // category (e.g. Name::NQuote) so arity matches the multi-binder.
                                if let Some(binding) = bindings.get(&v.to_string()) {
                                    let expr = &binding.expression;
                                    quote! { (#expr).iter().map(|__e| #default_lang_type::NQuote(Box::new(__e.clone()))).collect::<Vec<_>>() }
                                } else {
                                    let expr = replacements[0].to_ascent_rhs(bindings, language);
                                    quote! { vec![#expr] }
                                }
                            } else {
                                let expr = replacements[0].to_ascent_rhs(bindings, language);
                                quote! { vec![#expr] }
                            }
                        } else {
                            let repl_exprs: Vec<_> = replacements
                                .iter()
                                .map(|r| r.to_ascent_rhs(bindings, language))
                                .collect();
                            quote! { vec![#(#repl_exprs),*] }
                        }
                    };

                // Check if scope is a literal MultiLambda - if so, use bindings directly
                // This avoids constructing a Scope just to unbind it immediately
                if let Pattern::Term(PatternTerm::MultiLambda { binders, body }) = scope.as_ref() {
                    let subst_method = format_ident!("multi_substitute_{}", repl_cat);
                    let repls_expr = build_repls_expr(bindings, &default_lang_type);

                    // Direct access to binders and body via bindings
                    let body_expr = body.to_ascent_rhs(bindings, language);
                    let var_exprs: Vec<_> = binders
                        .iter()
                        .map(|b| {
                            let binder_name = b.to_string();
                            if let Some(bound_var) = bindings.get(&binder_name) {
                                let expr = &bound_var.expression;
                                quote! { &#expr }
                            } else {
                                panic!(
                                    "Binder {} not found in bindings for MultiSubst",
                                    binder_name
                                );
                            }
                        })
                        .collect();

                    quote! {
                        {
                            let __vars: Vec<&mettail_runtime::FreeVar<String>> = vec![#(#var_exprs),*];
                            let __repls = #repls_expr;
                            (#body_expr).#subst_method(&__vars, &__repls)
                        }
                    }
                } else if let Pattern::Term(PatternTerm::Var(scope_var)) = scope.as_ref() {
                    // Variable scope - check if single or multi-binder
                    let scope_kind = bindings
                        .get(&scope_var.to_string())
                        .and_then(|b| b.scope_kind)
                        .unwrap_or(ScopeKind::Multi); // Default to multi for backward compat

                    let scope_expr = scope.to_ascent_rhs(bindings, language);

                    if scope_kind == ScopeKind::Single {
                        // Single-binder scope: unbind returns (Binder, Box<T>)
                        let subst_method = format_ident!("substitute_{}", repl_cat);

                        // For single-binder, we expect exactly one replacement
                        let repl_expr = replacements[0].to_ascent_rhs(bindings, language);

                        quote! {
                            {
                                let (__binder, __body) = (#scope_expr).unbind();
                                (*__body).#subst_method(&__binder.0, &#repl_expr)
                            }
                        }
                    } else {
                        // Multi-binder scope: unbind returns (Vec<Binder>, Box<T>)
                        let subst_method = format_ident!("multi_substitute_{}", repl_cat);
                        let repls_expr = build_repls_expr(bindings, &default_lang_type);

                        quote! {
                            {
                                let (__binders, __body) = (#scope_expr).unbind();
                                let __vars: Vec<&mettail_runtime::FreeVar<String>> = __binders.iter()
                                    .map(|b| &b.0)
                                    .collect();
                                let __repls = #repls_expr;
                                (*__body).#subst_method(&__vars, &__repls)
                            }
                        }
                    }
                } else {
                    // Other pattern - assume multi-binder for backward compatibility
                    let subst_method = format_ident!("multi_substitute_{}", repl_cat);
                    let scope_expr = scope.to_ascent_rhs(bindings, language);
                    let repls_expr = build_repls_expr(bindings, &default_lang_type);

                    quote! {
                        {
                            let (__binders, __body) = (#scope_expr).unbind();
                            let __vars: Vec<&mettail_runtime::FreeVar<String>> = __binders.iter()
                                .map(|b| &b.0)
                                .collect();
                            let __repls = #repls_expr;
                            (*__body).#subst_method(&__vars, &__repls)
                        }
                    }
                }
            },
        }
    }
}

/// Helper: Check if field i needs Box wrapping
/// ALL non-terminal fields are boxed EXCEPT:
/// - Var (which is OrdVar, not Box<OrdVar>)
/// - Integer (which is native type like i32, not Box<i32>)
fn needs_box_for_field(
    rule: &super::grammar::GrammarRule,
    i: usize,
    _language: &LanguageDef,
) -> bool {
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
            },
            GrammarItem::Collection { .. } | GrammarItem::Binder { .. } => {
                field_idx += 1;
            },
            GrammarItem::Terminal(_) => {},
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
            },
            GrammarItem::NonTerminal(_) | GrammarItem::Binder { .. } => {
                field_idx += 1;
            },
            GrammarItem::Terminal(_) => {},
        }
    }
    false
}
