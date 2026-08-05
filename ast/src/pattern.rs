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
use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use std::fmt;

/// Term-like structure for rule specification.
/// Mirrors `Term` but allows `Pattern` in sub-expression positions.
/// This lets metasyntax (#map, #zip, etc.) appear anywhere in a term.
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

    /// Indexed positional element: `args[i := S]`.
    ///
    /// ★ ONE ELEMENT OF AN ORDERED COLLECTION, AT A BOUND POSITION
    ///
    /// LHS: iterate `args` positionally, bind the index to `i` and the element to the
    /// sub-pattern `S`, leaving every other element untouched.
    /// RHS: rebuild `args` with position `i` replaced by the sub-pattern's construction.
    ///
    /// This is the missing dual of [`Self::Collection`]. `Collection` matches an
    /// ORDER-FREE payload (`HashBag`/`HashSet`) — it may permute elements freely, which
    /// is exactly why it cannot express "the third argument stepped and the rest stayed
    /// put". A `Vec` payload is ORDERED, and a congruence over one argument of an
    /// argument list must preserve the other arguments' positions exactly.
    ///
    /// ⚠ WHY THIS IS NOT A CONVENIENCE. Before it, a rewrite rule could only reach a
    /// `Vec` payload as a WHOLE (bind the entire `Vec` to one variable), so there was no
    /// way to write "some element reduces". MEASURED CONSEQUENCE: **24 `Vec`-payload
    /// rules across the 49 shipped language definitions, and not one of them carries an
    /// element congruence** — every one of them is a term whose payload can contain a
    /// redex that can never fire. The single collection congruence that does exist in
    /// Rholang (`ParCong`) works only because `PPar` is a `HashBag` and could therefore
    /// use [`Self::Collection`].
    ///
    /// The index binder `i` is a genuine pattern variable: it is bound by the match and
    /// is in scope on the RHS, which is what lets the RHS say "the same position".
    /// Writing the RHS with a *different* index variable is how one would express a
    /// permutation, and the codegen does not special-case the two being equal.
    IndexedVec {
        /// The `Vec`-typed field being indexed (`args`).
        collection: Ident,
        /// Binder for the position (`i`) — bound on the LHS, usable on the RHS.
        index: Ident,
        /// Sub-pattern matched against / constructed at that position (`S`).
        element: Box<Pattern>,
    },
}

#[derive(Clone, Copy)]
enum PatternNode<'pattern> {
    Pattern(&'pattern Pattern),
    Term(&'pattern PatternTerm),
}

enum PatternCloneTask<'pattern> {
    Visit(PatternNode<'pattern>),
    WrapTerm(usize),
    Collection(&'pattern Pattern, usize),
    Map(&'pattern Pattern, usize),
    Zip(usize),
    IndexedVec(&'pattern Pattern, usize),
    Apply(&'pattern PatternTerm, usize),
    Lambda(&'pattern PatternTerm, usize),
    MultiLambda(&'pattern PatternTerm, usize),
    Subst(&'pattern PatternTerm, usize),
    MultiSubst(&'pattern PatternTerm, usize),
}

enum ClonedPatternNode {
    Pattern(Pattern),
    Term(PatternTerm),
}

fn cloned_pattern(value: ClonedPatternNode) -> Pattern {
    match value {
        ClonedPatternNode::Pattern(pattern) => pattern,
        ClonedPatternNode::Term(_) => panic!("pattern clone PDA expected a Pattern result"),
    }
}

fn cloned_term(value: ClonedPatternNode) -> PatternTerm {
    match value {
        ClonedPatternNode::Term(term) => term,
        ClonedPatternNode::Pattern(_) => panic!("pattern clone PDA expected a PatternTerm result"),
    }
}

fn clone_pattern_node(root: PatternNode<'_>) -> ClonedPatternNode {
    let mut tasks = vec![PatternCloneTask::Visit(root)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            PatternCloneTask::Visit(PatternNode::Pattern(pattern)) => match pattern {
                Pattern::Term(term) => {
                    tasks.push(PatternCloneTask::WrapTerm(values.len()));
                    tasks.push(PatternCloneTask::Visit(PatternNode::Term(term)));
                },
                Pattern::Collection { elements, .. } => {
                    tasks.push(PatternCloneTask::Collection(pattern, values.len()));
                    tasks.extend(
                        elements
                            .iter()
                            .rev()
                            .map(|child| PatternCloneTask::Visit(PatternNode::Pattern(child))),
                    );
                },
                Pattern::Map { collection, body, .. } => {
                    tasks.push(PatternCloneTask::Map(pattern, values.len()));
                    tasks.push(PatternCloneTask::Visit(PatternNode::Pattern(body)));
                    tasks.push(PatternCloneTask::Visit(PatternNode::Pattern(collection)));
                },
                Pattern::Zip { first, second } => {
                    tasks.push(PatternCloneTask::Zip(values.len()));
                    tasks.push(PatternCloneTask::Visit(PatternNode::Pattern(second)));
                    tasks.push(PatternCloneTask::Visit(PatternNode::Pattern(first)));
                },
                Pattern::IndexedVec { element, .. } => {
                    tasks.push(PatternCloneTask::IndexedVec(pattern, values.len()));
                    tasks.push(PatternCloneTask::Visit(PatternNode::Pattern(element)));
                },
            },
            PatternCloneTask::Visit(PatternNode::Term(term)) => match term {
                PatternTerm::Var(ident) => {
                    values.push(ClonedPatternNode::Term(PatternTerm::Var(ident.clone())));
                },
                PatternTerm::Apply { args, .. } => {
                    tasks.push(PatternCloneTask::Apply(term, values.len()));
                    tasks.extend(
                        args.iter()
                            .rev()
                            .map(|child| PatternCloneTask::Visit(PatternNode::Pattern(child))),
                    );
                },
                PatternTerm::Lambda { body, .. } => {
                    tasks.push(PatternCloneTask::Lambda(term, values.len()));
                    tasks.push(PatternCloneTask::Visit(PatternNode::Pattern(body)));
                },
                PatternTerm::MultiLambda { body, .. } => {
                    tasks.push(PatternCloneTask::MultiLambda(term, values.len()));
                    tasks.push(PatternCloneTask::Visit(PatternNode::Pattern(body)));
                },
                PatternTerm::Subst { term: value, replacement, .. } => {
                    tasks.push(PatternCloneTask::Subst(term, values.len()));
                    tasks.push(PatternCloneTask::Visit(PatternNode::Pattern(replacement)));
                    tasks.push(PatternCloneTask::Visit(PatternNode::Pattern(value)));
                },
                PatternTerm::MultiSubst { scope, replacements } => {
                    tasks.push(PatternCloneTask::MultiSubst(term, values.len()));
                    tasks.push(PatternCloneTask::Visit(PatternNode::Pattern(scope)));
                    tasks.extend(
                        replacements
                            .iter()
                            .rev()
                            .map(|child| PatternCloneTask::Visit(PatternNode::Pattern(child))),
                    );
                },
            },
            PatternCloneTask::WrapTerm(value_base) => {
                let term = cloned_term(
                    values
                        .pop()
                        .expect("pattern clone PDA lost a PatternTerm result"),
                );
                values.truncate(value_base);
                values.push(ClonedPatternNode::Pattern(Pattern::Term(term)));
            },
            PatternCloneTask::Collection(source, value_base) => {
                let Pattern::Collection { coll_type, rest, .. } = source else {
                    unreachable!("collection clone task carries a collection source")
                };
                let elements = values.drain(value_base..).map(cloned_pattern).collect();
                values.push(ClonedPatternNode::Pattern(Pattern::Collection {
                    coll_type: coll_type.clone(),
                    elements,
                    rest: rest.clone(),
                }));
            },
            PatternCloneTask::Map(source, value_base) => {
                let Pattern::Map { params, .. } = source else {
                    unreachable!("map clone task carries a map source")
                };
                let body = cloned_pattern(values.pop().expect("pattern clone PDA lost map body"));
                let collection =
                    cloned_pattern(values.pop().expect("pattern clone PDA lost map collection"));
                values.truncate(value_base);
                values.push(ClonedPatternNode::Pattern(Pattern::Map {
                    collection: Box::new(collection),
                    params: params.clone(),
                    body: Box::new(body),
                }));
            },
            PatternCloneTask::Zip(value_base) => {
                let second = cloned_pattern(values.pop().expect("pattern clone PDA lost zip RHS"));
                let first = cloned_pattern(values.pop().expect("pattern clone PDA lost zip LHS"));
                values.truncate(value_base);
                values.push(ClonedPatternNode::Pattern(Pattern::Zip {
                    first: Box::new(first),
                    second: Box::new(second),
                }));
            },
            PatternCloneTask::IndexedVec(source, value_base) => {
                let Pattern::IndexedVec { collection, index, .. } = source else {
                    unreachable!("indexed clone task carries an IndexedVec source")
                };
                let element = cloned_pattern(
                    values
                        .pop()
                        .expect("pattern clone PDA lost indexed element"),
                );
                values.truncate(value_base);
                values.push(ClonedPatternNode::Pattern(Pattern::IndexedVec {
                    collection: collection.clone(),
                    index: index.clone(),
                    element: Box::new(element),
                }));
            },
            PatternCloneTask::Apply(source, value_base) => {
                let PatternTerm::Apply { constructor, .. } = source else {
                    unreachable!("apply clone task carries an Apply source")
                };
                let args = values.drain(value_base..).map(cloned_pattern).collect();
                values.push(ClonedPatternNode::Term(PatternTerm::Apply {
                    constructor: constructor.clone(),
                    args,
                }));
            },
            PatternCloneTask::Lambda(source, value_base) => {
                let PatternTerm::Lambda { binder, .. } = source else {
                    unreachable!("lambda clone task carries a Lambda source")
                };
                let body =
                    cloned_pattern(values.pop().expect("pattern clone PDA lost lambda body"));
                values.truncate(value_base);
                values.push(ClonedPatternNode::Term(PatternTerm::Lambda {
                    binder: binder.clone(),
                    body: Box::new(body),
                }));
            },
            PatternCloneTask::MultiLambda(source, value_base) => {
                let PatternTerm::MultiLambda { binders, .. } = source else {
                    unreachable!("multi-lambda clone task carries a MultiLambda source")
                };
                let body = cloned_pattern(
                    values
                        .pop()
                        .expect("pattern clone PDA lost multi-lambda body"),
                );
                values.truncate(value_base);
                values.push(ClonedPatternNode::Term(PatternTerm::MultiLambda {
                    binders: binders.clone(),
                    body: Box::new(body),
                }));
            },
            PatternCloneTask::Subst(source, value_base) => {
                let PatternTerm::Subst { var, .. } = source else {
                    unreachable!("substitution clone task carries a Subst source")
                };
                let replacement = cloned_pattern(
                    values
                        .pop()
                        .expect("pattern clone PDA lost substitution replacement"),
                );
                let term = cloned_pattern(
                    values
                        .pop()
                        .expect("pattern clone PDA lost substitution term"),
                );
                values.truncate(value_base);
                values.push(ClonedPatternNode::Term(PatternTerm::Subst {
                    term: Box::new(term),
                    var: var.clone(),
                    replacement: Box::new(replacement),
                }));
            },
            PatternCloneTask::MultiSubst(source, value_base) => {
                let PatternTerm::MultiSubst { .. } = source else {
                    unreachable!("multi-substitution clone task carries a MultiSubst source")
                };
                let scope = cloned_pattern(
                    values
                        .pop()
                        .expect("pattern clone PDA lost multi-substitution scope"),
                );
                let replacements = values.drain(value_base..).map(cloned_pattern).collect();
                values.push(ClonedPatternNode::Term(PatternTerm::MultiSubst {
                    scope: Box::new(scope),
                    replacements,
                }));
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values.pop().expect("pattern clone PDA produced no result")
}

impl Clone for Pattern {
    fn clone(&self) -> Self {
        cloned_pattern(clone_pattern_node(PatternNode::Pattern(self)))
    }
}

impl Clone for PatternTerm {
    fn clone(&self) -> Self {
        cloned_term(clone_pattern_node(PatternNode::Term(self)))
    }
}

fn pattern_placeholder() -> Pattern {
    Pattern::Term(PatternTerm::Var(Ident::new("_", Span::call_site())))
}

fn take_pattern_box(child: &mut Box<Pattern>, work: &mut Vec<Pattern>) {
    work.push(*std::mem::replace(child, Box::new(pattern_placeholder())));
}

fn take_pattern_term_children(term: &mut PatternTerm, work: &mut Vec<Pattern>) {
    match term {
        PatternTerm::Var(_) => {},
        PatternTerm::Apply { args, .. } => work.append(args),
        PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
            take_pattern_box(body, work);
        },
        PatternTerm::Subst { term, replacement, .. } => {
            take_pattern_box(term, work);
            take_pattern_box(replacement, work);
        },
        PatternTerm::MultiSubst { scope, replacements } => {
            take_pattern_box(scope, work);
            work.append(replacements);
        },
    }
}

fn take_pattern_children(pattern: &mut Pattern, work: &mut Vec<Pattern>) {
    match pattern {
        Pattern::Term(term) => take_pattern_term_children(term, work),
        Pattern::Collection { elements, .. } => work.append(elements),
        Pattern::Map { collection, body, .. } => {
            take_pattern_box(collection, work);
            take_pattern_box(body, work);
        },
        Pattern::Zip { first, second } => {
            take_pattern_box(first, work);
            take_pattern_box(second, work);
        },
        Pattern::IndexedVec { element, .. } => take_pattern_box(element, work),
    }
}

fn drain_pattern_descendants(work: &mut Vec<Pattern>) {
    while let Some(pattern) = work.pop() {
        drain_owned_pattern(pattern, work);
    }
}

fn drain_owned_pattern(pattern: Pattern, work: &mut Vec<Pattern>) {
    // `pattern` is a descendant whose recursive fields are being destroyed by
    // this outer worklist. Suppressing its `Drop` avoids allocating and entering
    // a fresh worklist once per node. Every field is moved out exactly once below;
    // scalar fields are dropped immediately and child Patterns join `work`.
    let mut pattern = std::mem::ManuallyDrop::new(pattern);
    match &mut *pattern {
        Pattern::Term(term) => {
            // SAFETY: `pattern` is ManuallyDrop, this field is read exactly once,
            // and `drain_owned_pattern_term` consumes every field of the value.
            let term = unsafe { std::ptr::read(term) };
            drain_owned_pattern_term(term, work);
        },
        Pattern::Collection { coll_type, elements, rest } => {
            // SAFETY: all three fields belong to a ManuallyDrop value and each is
            // read exactly once. The moved values assume normal destruction here.
            drop(unsafe { std::ptr::read(coll_type) });
            work.extend(unsafe { std::ptr::read(elements) });
            drop(unsafe { std::ptr::read(rest) });
        },
        Pattern::Map { collection, params, body } => {
            // SAFETY: each field is read exactly once from the ManuallyDrop node.
            work.push(*unsafe { std::ptr::read(collection) });
            drop(unsafe { std::ptr::read(params) });
            work.push(*unsafe { std::ptr::read(body) });
        },
        Pattern::Zip { first, second } => {
            // SAFETY: each Box is read exactly once from the ManuallyDrop node.
            work.push(*unsafe { std::ptr::read(first) });
            work.push(*unsafe { std::ptr::read(second) });
        },
        Pattern::IndexedVec { collection, index, element } => {
            // SAFETY: each field is read exactly once from the ManuallyDrop node.
            drop(unsafe { std::ptr::read(collection) });
            drop(unsafe { std::ptr::read(index) });
            work.push(*unsafe { std::ptr::read(element) });
        },
    }
}

fn drain_owned_pattern_term(term: PatternTerm, work: &mut Vec<Pattern>) {
    let mut term = std::mem::ManuallyDrop::new(term);
    match &mut *term {
        PatternTerm::Var(ident) => {
            // SAFETY: the Ident is read exactly once from the ManuallyDrop node.
            drop(unsafe { std::ptr::read(ident) });
        },
        PatternTerm::Apply { constructor, args } => {
            // SAFETY: both fields are read exactly once from the ManuallyDrop node.
            drop(unsafe { std::ptr::read(constructor) });
            work.extend(unsafe { std::ptr::read(args) });
        },
        PatternTerm::Lambda { binder, body } => {
            // SAFETY: both fields are read exactly once from the ManuallyDrop node.
            drop(unsafe { std::ptr::read(binder) });
            work.push(*unsafe { std::ptr::read(body) });
        },
        PatternTerm::MultiLambda { binders, body } => {
            // SAFETY: both fields are read exactly once from the ManuallyDrop node.
            drop(unsafe { std::ptr::read(binders) });
            work.push(*unsafe { std::ptr::read(body) });
        },
        PatternTerm::Subst { term, var, replacement } => {
            // SAFETY: all fields are read exactly once from the ManuallyDrop node.
            work.push(*unsafe { std::ptr::read(term) });
            drop(unsafe { std::ptr::read(var) });
            work.push(*unsafe { std::ptr::read(replacement) });
        },
        PatternTerm::MultiSubst { scope, replacements } => {
            // SAFETY: both fields are read exactly once from the ManuallyDrop node.
            work.push(*unsafe { std::ptr::read(scope) });
            work.extend(unsafe { std::ptr::read(replacements) });
        },
    }
}

impl Drop for Pattern {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_pattern_children(self, &mut work);
        drain_pattern_descendants(&mut work);
    }
}

impl Drop for PatternTerm {
    fn drop(&mut self) {
        let mut work = Vec::new();
        take_pattern_term_children(self, &mut work);
        drain_pattern_descendants(&mut work);
    }
}

enum ScopedPatternTask<'pattern> {
    Visit(PatternNode<'pattern>),
    MapBody(&'pattern [Ident], &'pattern Pattern),
    BindOne(&'pattern Ident, &'pattern Pattern),
    BindMany(&'pattern [Ident], &'pattern Pattern),
    ExitOne(&'pattern Ident),
    ExitMany(&'pattern [Ident]),
}

fn visit_free_pattern_variables(root: PatternNode<'_>, mut visit: impl FnMut(&Ident)) {
    let mut tasks = vec![ScopedPatternTask::Visit(root)];
    let mut bound: HashMap<String, usize> = HashMap::new();
    let visit_if_free =
        |ident: &Ident, bound: &HashMap<String, usize>, visit: &mut dyn FnMut(&Ident)| {
            if !bound.contains_key(&ident.to_string()) {
                visit(ident);
            }
        };

    while let Some(task) = tasks.pop() {
        match task {
            ScopedPatternTask::Visit(PatternNode::Pattern(pattern)) => match pattern {
                Pattern::Term(term) => {
                    tasks.push(ScopedPatternTask::Visit(PatternNode::Term(term)));
                },
                Pattern::Collection { elements, rest, .. } => {
                    tasks.extend(
                        elements
                            .iter()
                            .rev()
                            .map(|child| ScopedPatternTask::Visit(PatternNode::Pattern(child))),
                    );
                    if let Some(rest) = rest {
                        visit_if_free(rest, &bound, &mut visit);
                    }
                },
                Pattern::Map { collection, params, body } => {
                    tasks.push(ScopedPatternTask::MapBody(params, body));
                    tasks.push(ScopedPatternTask::Visit(PatternNode::Pattern(collection)));
                },
                Pattern::Zip { first, second } => {
                    tasks.push(ScopedPatternTask::Visit(PatternNode::Pattern(second)));
                    tasks.push(ScopedPatternTask::Visit(PatternNode::Pattern(first)));
                },
                Pattern::IndexedVec { collection, index, element } => {
                    visit_if_free(collection, &bound, &mut visit);
                    visit_if_free(index, &bound, &mut visit);
                    tasks.push(ScopedPatternTask::Visit(PatternNode::Pattern(element)));
                },
            },
            ScopedPatternTask::Visit(PatternNode::Term(term)) => match term {
                PatternTerm::Var(ident) => visit_if_free(ident, &bound, &mut visit),
                PatternTerm::Apply { args, .. } => {
                    tasks.extend(
                        args.iter()
                            .rev()
                            .map(|child| ScopedPatternTask::Visit(PatternNode::Pattern(child))),
                    );
                },
                PatternTerm::Lambda { binder, body } => {
                    tasks.push(ScopedPatternTask::BindOne(binder, body));
                },
                PatternTerm::MultiLambda { binders, body } => {
                    tasks.push(ScopedPatternTask::BindMany(binders, body));
                },
                PatternTerm::Subst { term, var, replacement } => {
                    tasks.push(ScopedPatternTask::Visit(PatternNode::Pattern(replacement)));
                    visit_if_free(var, &bound, &mut visit);
                    tasks.push(ScopedPatternTask::Visit(PatternNode::Pattern(term)));
                },
                PatternTerm::MultiSubst { scope, replacements } => {
                    tasks.extend(
                        replacements
                            .iter()
                            .rev()
                            .map(|child| ScopedPatternTask::Visit(PatternNode::Pattern(child))),
                    );
                    tasks.push(ScopedPatternTask::Visit(PatternNode::Pattern(scope)));
                },
            },
            ScopedPatternTask::MapBody(params, body)
            | ScopedPatternTask::BindMany(params, body) => {
                for ident in params {
                    *bound.entry(ident.to_string()).or_default() += 1;
                }
                tasks.push(ScopedPatternTask::ExitMany(params));
                tasks.push(ScopedPatternTask::Visit(PatternNode::Pattern(body)));
            },
            ScopedPatternTask::BindOne(ident, body) => {
                *bound.entry(ident.to_string()).or_default() += 1;
                tasks.push(ScopedPatternTask::ExitOne(ident));
                tasks.push(ScopedPatternTask::Visit(PatternNode::Pattern(body)));
            },
            ScopedPatternTask::ExitOne(ident) => {
                let name = ident.to_string();
                let depth = bound.get_mut(&name).expect("entered binder must be active");
                *depth -= 1;
                if *depth == 0 {
                    bound.remove(&name);
                }
            },
            ScopedPatternTask::ExitMany(idents) => {
                for ident in idents {
                    let name = ident.to_string();
                    let depth = bound.get_mut(&name).expect("entered binder must be active");
                    *depth -= 1;
                    if *depth == 0 {
                        bound.remove(&name);
                    }
                }
            },
        }
    }
}

fn collect_pattern_constructor_labels(root: PatternNode<'_>, labels: &mut HashSet<String>) {
    let mut work = vec![root];
    while let Some(node) = work.pop() {
        match node {
            PatternNode::Pattern(pattern) => match pattern {
                Pattern::Term(term) => work.push(PatternNode::Term(term)),
                Pattern::Collection { elements, .. } => {
                    work.extend(elements.iter().rev().map(PatternNode::Pattern));
                },
                Pattern::Map { collection, body, .. } => {
                    work.push(PatternNode::Pattern(body));
                    work.push(PatternNode::Pattern(collection));
                },
                Pattern::Zip { first, second } => {
                    work.push(PatternNode::Pattern(second));
                    work.push(PatternNode::Pattern(first));
                },
                Pattern::IndexedVec { element, .. } => {
                    work.push(PatternNode::Pattern(element));
                },
            },
            PatternNode::Term(term) => match term {
                PatternTerm::Var(_) => {},
                PatternTerm::Apply { constructor, args } => {
                    labels.insert(constructor.to_string());
                    work.extend(args.iter().rev().map(PatternNode::Pattern));
                },
                PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
                    work.push(PatternNode::Pattern(body));
                },
                PatternTerm::Subst { term, replacement, .. } => {
                    work.push(PatternNode::Pattern(replacement));
                    work.push(PatternNode::Pattern(term));
                },
                PatternTerm::MultiSubst { scope, replacements } => {
                    work.extend(replacements.iter().rev().map(PatternNode::Pattern));
                    work.push(PatternNode::Pattern(scope));
                },
            },
        }
    }
}

fn pattern_node_span(mut node: PatternNode<'_>) -> Span {
    loop {
        match node {
            PatternNode::Pattern(pattern) => match pattern {
                Pattern::Term(term) => node = PatternNode::Term(term),
                Pattern::Collection { elements, .. } => {
                    let Some(first) = elements.first() else {
                        return Span::call_site();
                    };
                    node = PatternNode::Pattern(first);
                },
                Pattern::Map { collection, .. } => node = PatternNode::Pattern(collection),
                Pattern::Zip { first, .. } => node = PatternNode::Pattern(first),
                Pattern::IndexedVec { collection, .. } => return collection.span(),
            },
            PatternNode::Term(term) => match term {
                PatternTerm::Var(ident) => return ident.span(),
                PatternTerm::Apply { constructor, .. } => return constructor.span(),
                PatternTerm::Lambda { binder, .. } => return binder.span(),
                PatternTerm::MultiLambda { binders, .. } => {
                    return binders
                        .first()
                        .map_or(Span::call_site(), |binder| binder.span());
                },
                PatternTerm::Subst { var, .. } => return var.span(),
                PatternTerm::MultiSubst { scope, .. } => node = PatternNode::Pattern(scope),
            },
        }
    }
}

fn pattern_node_category<'language>(
    mut node: PatternNode<'_>,
    language: &'language LanguageDef,
) -> Option<&'language Ident> {
    loop {
        match node {
            PatternNode::Pattern(pattern) => match pattern {
                Pattern::Term(term) => node = PatternNode::Term(term),
                Pattern::Collection { .. } | Pattern::IndexedVec { .. } => return None,
                Pattern::Map { body, .. } => node = PatternNode::Pattern(body),
                Pattern::Zip { first, .. } => node = PatternNode::Pattern(first),
            },
            PatternNode::Term(term) => match term {
                PatternTerm::Var(_) => return None,
                PatternTerm::Apply { constructor, .. } => {
                    return language.category_of_constructor(constructor);
                },
                PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
                    node = PatternNode::Pattern(body);
                },
                PatternTerm::Subst { term, .. } => node = PatternNode::Pattern(term),
                PatternTerm::MultiSubst { scope, .. } => node = PatternNode::Pattern(scope),
            },
        }
    }
}

fn pattern_node_is_ground(root: PatternNode<'_>, language: &LanguageDef) -> bool {
    let mut work = vec![root];
    while let Some(node) = work.pop() {
        match node {
            PatternNode::Pattern(pattern) => match pattern {
                Pattern::Term(term) => work.push(PatternNode::Term(term)),
                Pattern::Collection { elements, rest, .. } => {
                    if rest.is_some() {
                        return false;
                    }
                    work.extend(elements.iter().rev().map(PatternNode::Pattern));
                },
                Pattern::Map { .. } | Pattern::Zip { .. } | Pattern::IndexedVec { .. } => {
                    return false;
                },
            },
            PatternNode::Term(term) => match term {
                PatternTerm::Var(ident) => {
                    if language.get_constructor(ident).is_none() {
                        return false;
                    }
                },
                PatternTerm::Apply { args, .. } => {
                    work.extend(args.iter().rev().map(PatternNode::Pattern));
                },
                PatternTerm::Lambda { .. }
                | PatternTerm::MultiLambda { .. }
                | PatternTerm::Subst { .. }
                | PatternTerm::MultiSubst { .. } => return false,
            },
        }
    }
    true
}

enum PatternDebugTask<'pattern> {
    Node(PatternNode<'pattern>, usize),
    PatternList(&'pattern [Pattern], usize),
    Ident(&'pattern Ident, usize),
    IdentList(&'pattern [Ident], usize),
    OptionIdent(&'pattern Option<Ident>, usize),
    OptionCollectionType(&'pattern Option<CollectionType>, usize),
    FieldNode(&'static str, PatternNode<'pattern>, usize),
    FieldPatternList(&'static str, &'pattern [Pattern], usize),
    FieldIdent(&'static str, &'pattern Ident, usize),
    FieldIdentList(&'static str, &'pattern [Ident], usize),
    FieldOptionIdent(&'static str, &'pattern Option<Ident>, usize),
    FieldOptionCollectionType(&'static str, &'pattern Option<CollectionType>, usize),
    Text(&'static str),
    Indent(usize),
    CloseTuple(usize),
    CloseStruct(usize),
    CloseList(usize),
}

fn write_debug_indent(f: &mut fmt::Formatter<'_>, indent: usize) -> fmt::Result {
    for _ in 0..indent {
        f.write_str("    ")?;
    }
    Ok(())
}

fn collection_type_name(collection_type: &CollectionType) -> &'static str {
    match collection_type {
        CollectionType::HashBag => "HashBag",
        CollectionType::HashSet => "HashSet",
        CollectionType::Vec => "Vec",
        CollectionType::HashMap => "HashMap",
        CollectionType::PathMap => "PathMap",
    }
}

fn fmt_debug_ident(
    ident: &Ident,
    indent: usize,
    pretty: bool,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    if pretty {
        f.write_str("Ident {\n")?;
        write_debug_indent(f, indent + 1)?;
        write!(f, "sym: {},\n", ident)?;
        write_debug_indent(f, indent)?;
        f.write_str("}")
    } else {
        write!(f, "Ident {{ sym: {ident} }}")
    }
}

fn push_compact_pattern_list<'pattern>(
    tasks: &mut Vec<PatternDebugTask<'pattern>>,
    patterns: &'pattern [Pattern],
) {
    tasks.push(PatternDebugTask::Text("]"));
    for (index, pattern) in patterns.iter().enumerate().rev() {
        tasks.push(PatternDebugTask::Node(PatternNode::Pattern(pattern), 0));
        if index > 0 {
            tasks.push(PatternDebugTask::Text(", "));
        }
    }
}

fn push_pretty_pattern_list<'pattern>(
    tasks: &mut Vec<PatternDebugTask<'pattern>>,
    patterns: &'pattern [Pattern],
    indent: usize,
) {
    tasks.push(PatternDebugTask::CloseList(indent));
    for pattern in patterns.iter().rev() {
        tasks.push(PatternDebugTask::Text(",\n"));
        tasks.push(PatternDebugTask::Node(PatternNode::Pattern(pattern), indent + 1));
        tasks.push(PatternDebugTask::Indent(indent + 1));
    }
}

fn fmt_pattern_debug(root: PatternNode<'_>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let pretty = f.alternate();
    let mut tasks = vec![PatternDebugTask::Node(root, 0)];
    while let Some(task) = tasks.pop() {
        match task {
            PatternDebugTask::Text(text) => f.write_str(text)?,
            PatternDebugTask::Indent(indent) => write_debug_indent(f, indent)?,
            PatternDebugTask::CloseTuple(indent) => {
                f.write_str(",\n")?;
                write_debug_indent(f, indent)?;
                f.write_str(")")?;
            },
            PatternDebugTask::CloseStruct(indent) => {
                write_debug_indent(f, indent)?;
                f.write_str("}")?;
            },
            PatternDebugTask::CloseList(indent) => {
                write_debug_indent(f, indent)?;
                f.write_str("]")?;
            },
            PatternDebugTask::Ident(ident, indent) => {
                fmt_debug_ident(ident, indent, pretty, f)?;
            },
            PatternDebugTask::IdentList(idents, indent) => {
                if !pretty || idents.is_empty() {
                    f.write_str("[")?;
                    for (index, ident) in idents.iter().enumerate() {
                        if index > 0 {
                            f.write_str(", ")?;
                        }
                        fmt_debug_ident(ident, indent, false, f)?;
                    }
                    f.write_str("]")?;
                } else {
                    f.write_str("[\n")?;
                    for ident in idents {
                        write_debug_indent(f, indent + 1)?;
                        fmt_debug_ident(ident, indent + 1, true, f)?;
                        f.write_str(",\n")?;
                    }
                    write_debug_indent(f, indent)?;
                    f.write_str("]")?;
                }
            },
            PatternDebugTask::OptionIdent(ident, indent) => match ident {
                None => f.write_str("None")?,
                Some(ident) if pretty => {
                    f.write_str("Some(\n")?;
                    write_debug_indent(f, indent + 1)?;
                    fmt_debug_ident(ident, indent + 1, true, f)?;
                    f.write_str(",\n")?;
                    write_debug_indent(f, indent)?;
                    f.write_str(")")?;
                },
                Some(ident) => {
                    f.write_str("Some(")?;
                    fmt_debug_ident(ident, indent, false, f)?;
                    f.write_str(")")?;
                },
            },
            PatternDebugTask::OptionCollectionType(collection_type, indent) => {
                match collection_type {
                    None => f.write_str("None")?,
                    Some(collection_type) if pretty => {
                        f.write_str("Some(\n")?;
                        write_debug_indent(f, indent + 1)?;
                        f.write_str(collection_type_name(collection_type))?;
                        f.write_str(",\n")?;
                        write_debug_indent(f, indent)?;
                        f.write_str(")")?;
                    },
                    Some(collection_type) => {
                        write!(f, "Some({})", collection_type_name(collection_type))?;
                    },
                }
            },
            PatternDebugTask::PatternList(patterns, indent) => {
                if pretty && !patterns.is_empty() {
                    f.write_str("[\n")?;
                    push_pretty_pattern_list(&mut tasks, patterns, indent);
                } else {
                    f.write_str("[")?;
                    push_compact_pattern_list(&mut tasks, patterns);
                }
            },
            PatternDebugTask::FieldNode(name, node, indent) => {
                write_debug_indent(f, indent)?;
                write!(f, "{name}: ")?;
                tasks.push(PatternDebugTask::Text(",\n"));
                tasks.push(PatternDebugTask::Node(node, indent));
            },
            PatternDebugTask::FieldPatternList(name, patterns, indent) => {
                write_debug_indent(f, indent)?;
                write!(f, "{name}: ")?;
                tasks.push(PatternDebugTask::Text(",\n"));
                tasks.push(PatternDebugTask::PatternList(patterns, indent));
            },
            PatternDebugTask::FieldIdent(name, ident, indent) => {
                write_debug_indent(f, indent)?;
                write!(f, "{name}: ")?;
                tasks.push(PatternDebugTask::Text(",\n"));
                tasks.push(PatternDebugTask::Ident(ident, indent));
            },
            PatternDebugTask::FieldIdentList(name, idents, indent) => {
                write_debug_indent(f, indent)?;
                write!(f, "{name}: ")?;
                tasks.push(PatternDebugTask::Text(",\n"));
                tasks.push(PatternDebugTask::IdentList(idents, indent));
            },
            PatternDebugTask::FieldOptionIdent(name, ident, indent) => {
                write_debug_indent(f, indent)?;
                write!(f, "{name}: ")?;
                tasks.push(PatternDebugTask::Text(",\n"));
                tasks.push(PatternDebugTask::OptionIdent(ident, indent));
            },
            PatternDebugTask::FieldOptionCollectionType(name, collection_type, indent) => {
                write_debug_indent(f, indent)?;
                write!(f, "{name}: ")?;
                tasks.push(PatternDebugTask::Text(",\n"));
                tasks.push(PatternDebugTask::OptionCollectionType(collection_type, indent));
            },
            PatternDebugTask::Node(PatternNode::Pattern(pattern), indent) => match pattern {
                Pattern::Term(term) => {
                    if pretty {
                        f.write_str("Term(\n")?;
                        tasks.push(PatternDebugTask::CloseTuple(indent));
                        tasks.push(PatternDebugTask::Node(PatternNode::Term(term), indent + 1));
                        tasks.push(PatternDebugTask::Indent(indent + 1));
                    } else {
                        f.write_str("Term(")?;
                        tasks.push(PatternDebugTask::Text(")"));
                        tasks.push(PatternDebugTask::Node(PatternNode::Term(term), 0));
                    }
                },
                Pattern::Collection { coll_type, elements, rest } => {
                    if pretty {
                        f.write_str("Collection {\n")?;
                        tasks.push(PatternDebugTask::CloseStruct(indent));
                        tasks.push(PatternDebugTask::FieldOptionIdent("rest", rest, indent + 1));
                        tasks.push(PatternDebugTask::FieldPatternList(
                            "elements",
                            elements,
                            indent + 1,
                        ));
                        tasks.push(PatternDebugTask::FieldOptionCollectionType(
                            "coll_type",
                            coll_type,
                            indent + 1,
                        ));
                    } else {
                        f.write_str("Collection { coll_type: ")?;
                        tasks.push(PatternDebugTask::Text(" }"));
                        tasks.push(PatternDebugTask::OptionIdent(rest, 0));
                        tasks.push(PatternDebugTask::Text(", rest: "));
                        tasks.push(PatternDebugTask::PatternList(elements, 0));
                        tasks.push(PatternDebugTask::Text(", elements: "));
                        tasks.push(PatternDebugTask::OptionCollectionType(coll_type, 0));
                    }
                },
                Pattern::Map { collection, params, body } => {
                    if pretty {
                        f.write_str("Map {\n")?;
                        tasks.push(PatternDebugTask::CloseStruct(indent));
                        tasks.push(PatternDebugTask::FieldNode(
                            "body",
                            PatternNode::Pattern(body),
                            indent + 1,
                        ));
                        tasks.push(PatternDebugTask::FieldIdentList("params", params, indent + 1));
                        tasks.push(PatternDebugTask::FieldNode(
                            "collection",
                            PatternNode::Pattern(collection),
                            indent + 1,
                        ));
                    } else {
                        f.write_str("Map { collection: ")?;
                        tasks.push(PatternDebugTask::Text(" }"));
                        tasks.push(PatternDebugTask::Node(PatternNode::Pattern(body), 0));
                        tasks.push(PatternDebugTask::Text(", body: "));
                        tasks.push(PatternDebugTask::IdentList(params, 0));
                        tasks.push(PatternDebugTask::Text(", params: "));
                        tasks.push(PatternDebugTask::Node(PatternNode::Pattern(collection), 0));
                    }
                },
                Pattern::Zip { first, second } => {
                    if pretty {
                        f.write_str("Zip {\n")?;
                        tasks.push(PatternDebugTask::CloseStruct(indent));
                        tasks.push(PatternDebugTask::FieldNode(
                            "second",
                            PatternNode::Pattern(second),
                            indent + 1,
                        ));
                        tasks.push(PatternDebugTask::FieldNode(
                            "first",
                            PatternNode::Pattern(first),
                            indent + 1,
                        ));
                    } else {
                        f.write_str("Zip { first: ")?;
                        tasks.push(PatternDebugTask::Text(" }"));
                        tasks.push(PatternDebugTask::Node(PatternNode::Pattern(second), 0));
                        tasks.push(PatternDebugTask::Text(", second: "));
                        tasks.push(PatternDebugTask::Node(PatternNode::Pattern(first), 0));
                    }
                },
                Pattern::IndexedVec { collection, index, element } => {
                    if pretty {
                        f.write_str("IndexedVec {\n")?;
                        tasks.push(PatternDebugTask::CloseStruct(indent));
                        tasks.push(PatternDebugTask::FieldNode(
                            "element",
                            PatternNode::Pattern(element),
                            indent + 1,
                        ));
                        tasks.push(PatternDebugTask::FieldIdent("index", index, indent + 1));
                        tasks.push(PatternDebugTask::FieldIdent(
                            "collection",
                            collection,
                            indent + 1,
                        ));
                    } else {
                        f.write_str("IndexedVec { collection: ")?;
                        tasks.push(PatternDebugTask::Text(" }"));
                        tasks.push(PatternDebugTask::Node(PatternNode::Pattern(element), 0));
                        tasks.push(PatternDebugTask::Text(", element: "));
                        tasks.push(PatternDebugTask::Ident(index, 0));
                        tasks.push(PatternDebugTask::Text(", index: "));
                        tasks.push(PatternDebugTask::Ident(collection, 0));
                    }
                },
            },
            PatternDebugTask::Node(PatternNode::Term(term), indent) => match term {
                PatternTerm::Var(ident) => {
                    if pretty {
                        f.write_str("Var(\n")?;
                        tasks.push(PatternDebugTask::CloseTuple(indent));
                        tasks.push(PatternDebugTask::Ident(ident, indent + 1));
                        tasks.push(PatternDebugTask::Indent(indent + 1));
                    } else {
                        f.write_str("Var(")?;
                        tasks.push(PatternDebugTask::Text(")"));
                        tasks.push(PatternDebugTask::Ident(ident, 0));
                    }
                },
                PatternTerm::Apply { constructor, args } => {
                    if pretty {
                        f.write_str("Apply {\n")?;
                        tasks.push(PatternDebugTask::CloseStruct(indent));
                        tasks.push(PatternDebugTask::FieldPatternList("args", args, indent + 1));
                        tasks.push(PatternDebugTask::FieldIdent(
                            "constructor",
                            constructor,
                            indent + 1,
                        ));
                    } else {
                        f.write_str("Apply { constructor: ")?;
                        tasks.push(PatternDebugTask::Text(" }"));
                        tasks.push(PatternDebugTask::PatternList(args, 0));
                        tasks.push(PatternDebugTask::Text(", args: "));
                        tasks.push(PatternDebugTask::Ident(constructor, 0));
                    }
                },
                PatternTerm::Lambda { binder, body } => {
                    if pretty {
                        f.write_str("Lambda {\n")?;
                        tasks.push(PatternDebugTask::CloseStruct(indent));
                        tasks.push(PatternDebugTask::FieldNode(
                            "body",
                            PatternNode::Pattern(body),
                            indent + 1,
                        ));
                        tasks.push(PatternDebugTask::FieldIdent("binder", binder, indent + 1));
                    } else {
                        f.write_str("Lambda { binder: ")?;
                        tasks.push(PatternDebugTask::Text(" }"));
                        tasks.push(PatternDebugTask::Node(PatternNode::Pattern(body), 0));
                        tasks.push(PatternDebugTask::Text(", body: "));
                        tasks.push(PatternDebugTask::Ident(binder, 0));
                    }
                },
                PatternTerm::MultiLambda { binders, body } => {
                    if pretty {
                        f.write_str("MultiLambda {\n")?;
                        tasks.push(PatternDebugTask::CloseStruct(indent));
                        tasks.push(PatternDebugTask::FieldNode(
                            "body",
                            PatternNode::Pattern(body),
                            indent + 1,
                        ));
                        tasks.push(PatternDebugTask::FieldIdentList(
                            "binders",
                            binders,
                            indent + 1,
                        ));
                    } else {
                        f.write_str("MultiLambda { binders: ")?;
                        tasks.push(PatternDebugTask::Text(" }"));
                        tasks.push(PatternDebugTask::Node(PatternNode::Pattern(body), 0));
                        tasks.push(PatternDebugTask::Text(", body: "));
                        tasks.push(PatternDebugTask::IdentList(binders, 0));
                    }
                },
                PatternTerm::Subst { term, var, replacement } => {
                    if pretty {
                        f.write_str("Subst {\n")?;
                        tasks.push(PatternDebugTask::CloseStruct(indent));
                        tasks.push(PatternDebugTask::FieldNode(
                            "replacement",
                            PatternNode::Pattern(replacement),
                            indent + 1,
                        ));
                        tasks.push(PatternDebugTask::FieldIdent("var", var, indent + 1));
                        tasks.push(PatternDebugTask::FieldNode(
                            "term",
                            PatternNode::Pattern(term),
                            indent + 1,
                        ));
                    } else {
                        f.write_str("Subst { term: ")?;
                        tasks.push(PatternDebugTask::Text(" }"));
                        tasks.push(PatternDebugTask::Node(PatternNode::Pattern(replacement), 0));
                        tasks.push(PatternDebugTask::Text(", replacement: "));
                        tasks.push(PatternDebugTask::Ident(var, 0));
                        tasks.push(PatternDebugTask::Text(", var: "));
                        tasks.push(PatternDebugTask::Node(PatternNode::Pattern(term), 0));
                    }
                },
                PatternTerm::MultiSubst { scope, replacements } => {
                    if pretty {
                        f.write_str("MultiSubst {\n")?;
                        tasks.push(PatternDebugTask::CloseStruct(indent));
                        tasks.push(PatternDebugTask::FieldPatternList(
                            "replacements",
                            replacements,
                            indent + 1,
                        ));
                        tasks.push(PatternDebugTask::FieldNode(
                            "scope",
                            PatternNode::Pattern(scope),
                            indent + 1,
                        ));
                    } else {
                        f.write_str("MultiSubst { scope: ")?;
                        tasks.push(PatternDebugTask::Text(" }"));
                        tasks.push(PatternDebugTask::PatternList(replacements, 0));
                        tasks.push(PatternDebugTask::Text(", replacements: "));
                        tasks.push(PatternDebugTask::Node(PatternNode::Pattern(scope), 0));
                    }
                },
            },
        }
    }
    Ok(())
}

impl fmt::Debug for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_pattern_debug(PatternNode::Pattern(self), f)
    }
}

impl fmt::Debug for PatternTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_pattern_debug(PatternNode::Term(self), f)
    }
}

// ============================================================================
// PatternTerm implementations
// ============================================================================

impl PatternTerm {
    /// Collect free variables in this pattern term
    #[allow(dead_code)]
    pub fn free_vars(&self) -> HashSet<String> {
        let mut vars = HashSet::new();
        visit_free_pattern_variables(PatternNode::Term(self), |ident| {
            vars.insert(ident.to_string());
        });
        vars
    }

    /// Collect all constructor labels referenced in this pattern term.
    ///
    /// Walks the pattern tree recursively and inserts `PatternTerm::Apply { constructor }`
    /// identifiers into `labels`. Used for transitive liveness analysis in dead-rule detection:
    /// if an equation/rewrite/logic rule references a constructor, that constructor is
    /// semantically live even if parsing never dispatches to it.
    pub fn collect_constructor_labels(&self, labels: &mut HashSet<String>) {
        collect_pattern_constructor_labels(PatternNode::Term(self), labels);
    }

    /// Return the most representative span for this pattern term.
    pub fn span(&self) -> Span {
        pattern_node_span(PatternNode::Term(self))
    }
}

// ============================================================================
// Pattern implementations
// ============================================================================

impl Pattern {
    /// Return the most representative span for this pattern.
    pub fn span(&self) -> Span {
        pattern_node_span(PatternNode::Pattern(self))
    }

    /// Collect all constructor labels referenced in this pattern.
    ///
    /// Recursively walks the pattern tree and collects `PatternTerm::Apply { constructor }`
    /// identifiers. Used for transitive liveness analysis: equations, rewrites, and logic
    /// blocks reference constructors that must not be flagged as dead rules.
    pub fn collect_constructor_labels(&self, labels: &mut HashSet<String>) {
        collect_pattern_constructor_labels(PatternNode::Pattern(self), labels);
    }

    /// Collect free variables in this pattern
    #[allow(dead_code)]
    pub fn free_vars(&self) -> HashSet<String> {
        let mut vars = HashSet::new();
        visit_free_pattern_variables(PatternNode::Pattern(self), |ident| {
            vars.insert(ident.to_string());
        });
        vars
    }

    /// Check if this pattern is just a variable (no constructor or structure)
    /// Used to avoid generating equation rules that match everything.
    /// Example: For equation `@(*N) == N`, the RHS `N` is just a variable,
    /// so we shouldn't generate the backward direction N => @(*N).
    pub fn is_just_variable(&self) -> bool {
        matches!(self, Pattern::Term(PatternTerm::Var(_)))
    }

    /// Check if this pattern is ground (no free variables at any position).
    ///
    /// A ground pattern consists entirely of concrete constructors, literals,
    /// and nullary constructors — no `Var`, `Lambda`, `MultiLambda`, `Subst`,
    /// `MultiSubst`, `Map`, or `Zip` nodes. Collection patterns are ground if
    /// all elements are ground and there is no rest variable.
    ///
    /// Used by B-CG04 (GroundShortCircuit) to detect rewrite rules whose LHS
    /// can match at most one specific term shape, enabling direct seed insertion
    /// at Ascent initialization instead of per-iteration pattern matching.
    pub fn is_ground_pattern(&self, language: &LanguageDef) -> bool {
        pattern_node_is_ground(PatternNode::Pattern(self), language)
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
        pattern_node_category(PatternNode::Pattern(self), language)
    }

    // -------------------------------------------------------------------------
    // Variable occurrence tracking (for duplicate detection)
    // -------------------------------------------------------------------------

    /// Collect all variable occurrences with their counts.
    /// Useful for detecting duplicate variables that need equational checks.
    pub fn var_occurrences(&self) -> HashMap<String, usize> {
        let mut counts = HashMap::new();
        visit_free_pattern_variables(PatternNode::Pattern(self), |ident| {
            *counts.entry(ident.to_string()).or_insert(0) += 1;
        });
        counts
    }
}

impl PatternTerm {
    /// Check if this pattern term is ground (no free variables).
    ///
    /// - `Var` is never ground (it's a free variable).
    /// - `Apply` is ground if all args are ground (nullary constructors are ground).
    /// - `Lambda`, `MultiLambda`, `Subst`, `MultiSubst` are never ground
    ///   (they involve variable binding/substitution, which is non-ground by design).
    pub fn is_ground_pattern(&self, language: &LanguageDef) -> bool {
        pattern_node_is_ground(PatternNode::Term(self), language)
    }

    /// Infer the category this pattern term produces
    pub fn category<'a>(&self, language: &'a LanguageDef) -> Option<&'a Ident> {
        pattern_node_category(PatternNode::Term(self), language)
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
    /// BCG01: Maps each binding variable name to the clause index at which it
    /// becomes available. Populated by `record_binding()`. Used by join ordering
    /// to determine the earliest clause position where a condition's required
    /// variables are all satisfied.
    pub binding_clause_index: HashMap<String, usize>,
}

impl AscentClauses {
    /// Record a new variable binding and associate it with the current clause index.
    ///
    /// BCG01: This tracks when each variable becomes available in the clause
    /// sequence, enabling join ordering to interleave condition checks at the
    /// earliest valid position for fail-fast evaluation.
    pub fn record_binding(&mut self, name: String, binding: VariableBinding) {
        // The binding becomes available at the current clause count.
        // If no clauses have been pushed yet (clause index 0), the variable
        // is available from the start (bound by the initial relation lookup).
        let clause_idx = self.clauses.len();
        self.binding_clause_index
            .entry(name.clone())
            .or_insert(clause_idx);
        self.bindings.insert(name, binding);
    }
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
                    result.record_binding(
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

                    // ★ #141 G6. All five refusals in this arm are reachable from a
                    // MALFORMED PATTERN a user can write — `*zip`/`*map` shape is not
                    // checked before lowering — and they were `panic!`s in a crate
                    // (`ast`) that is not a proc macro, so nothing rendered them. The
                    // idiom used instead is the one `PatternTerm::Subst` two hundred
                    // lines below already uses: push a `compile_error!` into
                    // `result.clauses` and return. A `compile_error!` is a TOKEN,
                    // rendered by `rustc`, so unlike a panic it survives the
                    // cranelift-compiled proc-macro boundary (#141 RED-0).
                    macro_rules! refuse_zip_map {
                        ($message:expr) => {{
                            let message: &str = $message;
                            result.clauses.push(quote! { compile_error!(#message); });
                            return;
                        }};
                    }

                    let Some(ctx) = search_context else {
                        refuse_zip_map!(
                            "mettail: a `*zip(…).*map(…)` pattern is a CORRELATED SEARCH \
                             over an enclosing collection, so it is only meaningful inside \
                             one. Wrap it in the collection pattern whose elements it \
                             searches."
                        );
                    };

                    // Get variable names from first and second
                    let Pattern::Term(PatternTerm::Var(first_var)) = first.as_ref() else {
                        refuse_zip_map!(
                            "mettail: the FIRST argument of `*zip(…, …)` must be a \
                             variable — it names the already-bound collection the search \
                             iterates. Bind it with a variable on the left-hand side first."
                        );
                    };
                    let first_var_name = first_var.to_string();
                    let Pattern::Term(PatternTerm::Var(second_var)) = second.as_ref() else {
                        refuse_zip_map!(
                            "mettail: the SECOND argument of `*zip(…, …)` must be a \
                             variable — it names the collection the search COLLECTS into. \
                             Use a fresh variable there."
                        );
                    };
                    let second_var_name = second_var.to_string();

                    // first should already be bound - get its binding
                    // remove immutable borrow of result.bindings
                    let first_binding = result
                        .bindings
                        .get_mut(&first_var_name)
                        .map(|b| &b.expression)
                        .unwrap()
                        .clone();

                    if params.len() != 2 {
                        refuse_zip_map!(
                            "mettail: the closure of a `*zip(…, …).*map(|…| …)` takes \
                             exactly two parameters — one element of the first collection \
                             and one of the second."
                        );
                    }
                    let first_param = &params[0]; // bound to each element of first
                    let second_param = &params[1]; // extracted from matching context element

                    let iter_idx = *iter_counter;
                    *iter_counter += 1;

                    let first_elem = format_ident!("__zip_first_{}", iter_idx);
                    let search_elem = format_ident!("__zip_search_{}", iter_idx);
                    let collected_var = format_ident!("__zip_collected_{}", iter_idx);

                    // Bind first_param to first_elem for body pattern matching
                    result.record_binding(
                        first_param.to_string(),
                        VariableBinding {
                            expression: quote! { #first_elem.clone() },
                            lang_type: category.clone(),
                            scope_kind: None,
                        },
                    );

                    let Pattern::Term(PatternTerm::Apply { constructor, args: body_args }) =
                        body.as_ref()
                    else {
                        refuse_zip_map!(
                            "mettail: the body of a `*zip(…, …).*map(|…| …)` must be a \
                             CONSTRUCTOR pattern — it is the shape each searched element \
                             is matched against, so it has to name a constructor."
                        );
                    };
                    let (constructor, body_args) = (constructor.clone(), body_args.clone());

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
                    result.record_binding(
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
                        result.record_binding(
                            param.to_string(),
                            VariableBinding {
                                expression: quote! { #elem_var },
                                lang_type: category.clone(),
                                scope_kind: None,
                            },
                        );
                    } else if params.len() == 2 {
                        // For zipped pairs
                        result.record_binding(
                            params[0].to_string(),
                            VariableBinding {
                                expression: quote! { #elem_var.0 },
                                lang_type: category.clone(),
                                scope_kind: None,
                            },
                        );
                        result.record_binding(
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
                        result.record_binding(
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
                        result.record_binding(
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
            // ★ NOT LOWERED HERE, AND THAT IS NOT AN OMISSION.
            //
            // `generate_clauses` emits `AscentClauses` for the ASCENT backend, which was
            // RETIRED (the `AscentClauses` type has no reference anywhere outside this
            // file — the live rewrite lowering is Dovetail, in
            // `macros/src/gen/runtime/dovetail_report/`). Writing an indexed-`Vec`
            // lowering here would be code no caller can reach and no test can exercise,
            // which is precisely the kind of unverifiable "implementation" that hides a
            // defect.
            //
            // Refusing loudly is the honest behavior, and it matches the existing
            // precedent for a pattern a backend cannot express (`dovetail_report.rs`'s
            // `AstPattern::Zip => Err(...)`). If the Ascent backend is ever revived, this
            // is the exact site to implement, and it will announce itself rather than
            // silently matching nothing.
            // ★ #141 G6. Still a refusal, and still for the reason the paragraph
            // above gives — but as a `compile_error!` rather than a `panic!`, so it
            // is READ. `ast` is not a proc-macro crate and a panic here surfaces as
            // an aborted `rustc` with no message at all.
            Pattern::IndexedVec { collection, index, .. } => {
                let message = format!(
                    "mettail: indexed-vec pattern `{collection}[{index} := …]` reached the \
                     RETIRED Ascent clause generator. The live rewrite backend is Dovetail; \
                     this path has no caller. Report this as a macro bug."
                );
                result.clauses.push(quote! { compile_error!(#message); });
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
                        result.record_binding(
                            var_name.clone(),
                            VariableBinding {
                                expression: quote! { #term_var.clone() },
                                lang_type: category.clone(),
                                scope_kind: None,
                            },
                        );
                    } else {
                        // Subsequent occurrence: emit eq check inline (Sprint 7).
                        //
                        // Interleaving the eq check here — at its earliest valid
                        // position — rather than batching all eq checks after the
                        // full LHS clause sequence enables fail-fast evaluation.
                        // Both `existing` (bound at first occurrence) and `term_var`
                        // (bound by a preceding destructuring clause) are already
                        // available, so the check is valid at this point.
                        let existing = result
                            .bindings
                            .get(&var_name)
                            .map(|b| &b.expression)
                            .unwrap();
                        let eq_rel = format_ident!("eq_{}", category.to_string().to_lowercase());
                        // F1: Eqrel dereference fix — bind fresh temporaries from the
                        // eqrel join to handle &&T vs &T in ascent_par! mode.
                        let eq_tmp_suffix = var_name.to_string().to_ascii_lowercase();
                        let eq_tmp_a = format_ident!("__eqpat_a_{}", eq_tmp_suffix);
                        let eq_tmp_b = format_ident!("__eqpat_b_{}", eq_tmp_suffix);
                        result.clauses.push(quote! {
                            #eq_rel(#eq_tmp_a, #eq_tmp_b),
                            if #existing == #eq_tmp_a.clone(),
                            if #term_var.clone() == #eq_tmp_b.clone()
                        });
                    }
                } else {
                    // Single-occurrence variable: just bind
                    result.record_binding(
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
                        GrammarItem::NonTerminal { ident: field_cat, kind } => {
                            if field_idx < args.len() {
                                let field_var = &field_vars[field_idx];

                                // Handle Box<T> - need to dereference for all non-terminals except:
                                // - Var (stored as OrdVar, not Box<OrdVar>)
                                // - Integer (stored as native type like i32, not Box<i32>)
                                let is_unboxed = kind.is_builtin();
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
                                    result.record_binding(
                                        binder.to_string(),
                                        VariableBinding {
                                            expression: quote! { #binder_var.0.clone() },
                                            lang_type: category.clone(),
                                            scope_kind: Some(ScopeKind::Single),
                                        },
                                    );

                                    // Also bind the full binder for RHS reconstruction
                                    result.record_binding(
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
                                        result.record_binding(
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

                                            result.record_binding(
                                                binder.to_string(),
                                                VariableBinding {
                                                    expression: quote! { #binder_elem_var.0.clone() },
                                                    lang_type: category.clone(),
                                                    scope_kind: Some(ScopeKind::Multi),
                                                },
                                            );

                                            result.record_binding(
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
                                    result.record_binding(
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
                                    result.record_binding(
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
                result.record_binding(
                    binder.to_string(),
                    VariableBinding {
                        expression: quote! { #binder_var.0.clone() },
                        lang_type: category.clone(),
                        scope_kind: Some(ScopeKind::Single),
                    },
                );

                // Also bind the full binder for RHS reconstruction
                result.record_binding(
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
                    result.record_binding(
                        binder.to_string(),
                        VariableBinding {
                            expression: quote! { #binder_elem_var.0.clone() },
                            lang_type: category.clone(),
                            scope_kind: Some(ScopeKind::Multi),
                        },
                    );

                    // Also bind the full binder for RHS reconstruction
                    result.record_binding(
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
                result.clauses.push(quote! {
                    compile_error!("Substitution patterns in LHS of equations/rewrite rules \
                        are not supported. Bind the expression with a variable on the LHS \
                        and apply the substitution on the RHS instead.")
                });
            },

            PatternTerm::MultiSubst { .. } => {
                result.clauses.push(quote! {
                    compile_error!("Multi-substitution patterns in LHS of equations/rewrite \
                        rules are not supported. Bind the scope with a variable on the LHS \
                        and apply multisubst on the RHS instead.")
                });
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
            // Retired-Ascent RHS construction — the mirror of the LHS refusal in
            // `generate_clauses`. See that arm for why an unreachable backend is not
            // implemented rather than filled in with untestable code.
            // ★ #141 G6 — the RHS twin of the LHS refusal above; same reasoning,
            // and this function returns the tokens, so the refusal simply IS them.
            Pattern::IndexedVec { collection, index, .. } => {
                let message = format!(
                    "mettail: indexed-vec pattern `{collection}[{index} := …]` reached the \
                     RETIRED Ascent RHS generator. The live rewrite backend is Dovetail; \
                     this path has no caller. Report this as a macro bug."
                );
                quote! { compile_error!(#message) }
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
        let use_vec = matches!(coll_type, Some(CollectionType::Vec));
        // When building List (Vec) or Bag, wrap List/Bag elements in ProcList/ProcBag so push/insert get Proc.
        let elem_cat_opt = if use_vec {
            language
                .list_type_name()
                .and_then(|name| language.collection_element_type_for_category(name))
                .or_else(|| {
                    language
                        .list_type_name()
                        .map(|_| quote::format_ident!("Proc"))
                })
        } else {
            language
                .bag_type_name()
                .and_then(|name| language.collection_element_type_for_category(name))
                .or_else(|| {
                    language
                        .bag_type_name()
                        .map(|_| quote::format_ident!("Proc"))
                })
        };
        // When building List (Vec<Proc>) or Bag (HashBag<Proc>), wrap any List/Bag element in ProcList/ProcBag so push/insert get Proc.
        let elem_cat = elem_cat_opt.unwrap_or_else(|| quote::format_ident!("Proc"));
        let wrapped_exprs: Vec<_> = elements
            .iter()
            .map(|e| {
                let expr = e.to_ascent_rhs(bindings, language);
                let cat_str = e.category(language).map(|c| c.to_string()).or_else(|| {
                    if let Pattern::Term(PatternTerm::Var(v)) = e {
                        bindings
                            .get(&v.to_string())
                            .map(|b| b.lang_type.to_string())
                    } else {
                        None
                    }
                });
                match cat_str.as_deref() {
                    Some("List") => {
                        let label = language
                            .injection_term_label_for_collection("List")
                            .unwrap_or_else(|| quote::format_ident!("ProcList"));
                        quote! { #elem_cat::#label(std::sync::Arc::new(#expr)) }
                    },
                    Some("Bag") => {
                        let label = language
                            .injection_term_label_for_collection("Bag")
                            .unwrap_or_else(|| quote::format_ident!("ProcBag"));
                        quote! { #elem_cat::#label(std::sync::Arc::new(#expr)) }
                    },
                    _ => expr,
                }
            })
            .collect();

        // Use coll_type if provided, default to HashBag
        let coll_type_tok = match coll_type {
            Some(CollectionType::Vec) => quote! { Vec },
            Some(CollectionType::HashSet) => quote! { std::collections::HashSet },
            // Map/PathMap patterns are not supported yet; treat as bag-shaped for codegen.
            Some(CollectionType::HashMap) | Some(CollectionType::PathMap) => {
                quote! { mettail_runtime::HashBag }
            },
            Some(CollectionType::HashBag) | None => quote! { mettail_runtime::HashBag },
        };

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
                        #(coll.push(#wrapped_exprs);)*
                        coll
                    }
                }
            } else {
                quote! {
                    {
                        let mut bag = (#rest_binding).clone();
                        #(bag.insert(#wrapped_exprs);)*
                        bag
                    }
                }
            }
        } else if use_vec {
            quote! {
                {
                    let mut coll = Vec::new();
                    #(coll.push(#wrapped_exprs);)*
                    coll
                }
            }
        } else {
            quote! {
                {
                    let mut bag = #coll_type_tok::new();
                    #(bag.insert(#wrapped_exprs);)*
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
    // When collection element type is Proc, wrap any List/Bag element in ProcList/ProcBag so push/insert get Proc.
    let elem_cat_opt = language
        .collection_element_type_for_category(category)
        .or_else(|| {
            let cat_str = category.to_string();
            if cat_str == "List" || cat_str == "Bag" {
                Some(quote::format_ident!("Proc"))
            } else {
                None
            }
        });
    let wrapped_exprs: Vec<_> = match elem_cat_opt {
        None => elements
            .iter()
            .map(|e| e.to_ascent_rhs(bindings, language))
            .collect(),
        Some(elem_cat) => elements
            .iter()
            .map(|e| {
                let expr = e.to_ascent_rhs(bindings, language);
                let cat_str = e.category(language).map(|c| c.to_string()).or_else(|| {
                    if let Pattern::Term(PatternTerm::Var(v)) = e {
                        bindings
                            .get(&v.to_string())
                            .map(|b| b.lang_type.to_string())
                    } else {
                        None
                    }
                });
                match cat_str.as_deref() {
                    Some("List") => {
                        let label = language
                            .injection_term_label_for_collection("List")
                            .unwrap_or_else(|| quote::format_ident!("ProcList"));
                        quote! { #elem_cat::#label(std::sync::Arc::new(#expr)) }
                    },
                    Some("Bag") => {
                        let label = language
                            .injection_term_label_for_collection("Bag")
                            .unwrap_or_else(|| quote::format_ident!("ProcBag"));
                        quote! { #elem_cat::#label(std::sync::Arc::new(#expr)) }
                    },
                    _ => expr,
                }
            })
            .collect(),
    };

    // Use coll_type if provided, default to HashBag
    let coll_type_tok = match coll_type {
        Some(CollectionType::Vec) => quote! { Vec },
        Some(CollectionType::HashSet) => quote! { std::collections::HashSet },
        // Map/PathMap patterns are not supported yet; treat as bag-shaped for codegen.
        Some(CollectionType::HashMap) | Some(CollectionType::PathMap) => {
            quote! { mettail_runtime::HashBag }
        },
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
                    #(coll.push(#wrapped_exprs);)*
                    coll
                }
            }
        } else if let Some(helper) = &insert_helper {
            // Use insert helper for flattening
            quote! {
                {
                    let mut bag = (#rest_binding).clone();
                    #(#category::#helper(&mut bag, #wrapped_exprs);)*
                    bag
                }
            }
        } else {
            quote! {
                {
                    let mut bag = (#rest_binding).clone();
                    #(bag.insert(#wrapped_exprs);)*
                    bag
                }
            }
        }
    } else if use_vec {
        quote! {
            {
                let mut coll = Vec::new();
                #(coll.push(#wrapped_exprs);)*
                coll
            }
        }
    } else if let Some(helper) = &insert_helper {
        // Use insert helper for flattening
        quote! {
            {
                let mut bag = #coll_type_tok::new();
                #(#category::#helper(&mut bag, #wrapped_exprs);)*
                bag
            }
        }
    } else {
        quote! {
            {
                let mut bag = #coll_type_tok::new();
                #(bag.insert(#wrapped_exprs);)*
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

        // Get a default lang_type for iteration variables from the first binding, or `Term`.
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
            // N params (>2): generalized tuple destructuring
            let mut body_bindings = bindings.clone();
            for (i, param) in params.iter().enumerate() {
                let idx = syn::Index::from(i);
                body_bindings.insert(
                    param.to_string(),
                    VariableBinding {
                        expression: quote! { __elem.#idx },
                        lang_type: default_lang_type.clone(),
                        scope_kind: None,
                    },
                );
            }
            let body_expr = body.to_ascent_rhs(&body_bindings, language);
            quote! {{
                let __coll = #coll_expr;
                let mut __result = Vec::new();
                for __elem in __coll.iter() {
                    let __mapped = #body_expr;
                    __result.push(__mapped);
                }
                __result
            }}
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
                            // Unbound variable: reference by Rust identifier name.
                            // If reached in an equation/rewrite context, the variable
                            // should have been bound by the LHS pattern.
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
                            quote! { std::sync::Arc::new(#expr) }
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
                        std::sync::Arc::new(#body_expr)
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
                                    std::sync::Arc::new(#body_expr)
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
                        std::sync::Arc::new(#body_expr)
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
                            std::sync::Arc::new(#term_expr)
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
                                    quote! { (#expr).iter().map(|__e| #default_lang_type::NQuote(std::sync::Arc::new(__e.clone()))).collect::<Vec<_>>() }
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
                                // ★ #141 G6. Reachable from a rule whose RHS
                                // multi-substitutes over a binder its LHS never
                                // bound — a grammar-author mistake, not an internal
                                // one. This closure yields the argument's tokens, so
                                // the refusal simply IS the argument.
                                let message = format!(
                                    "mettail: the multi-substitution names the binder \
                                     `{binder_name}`, which no pattern on the left-hand \
                                     side binds. Bind it on the left before substituting \
                                     for it on the right."
                                );
                                quote! { compile_error!(#message) }
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
            GrammarItem::NonTerminal { kind, .. } => {
                if field_idx == i {
                    // Box all non-terminals except built-ins (Var, Integer, Boolean, etc.)
                    return !kind.is_builtin();
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
            GrammarItem::NonTerminal { .. } | GrammarItem::Binder { .. } => {
                field_idx += 1;
            },
            GrammarItem::Terminal(_) => {},
        }
    }
    false
}

// ══════════════════════════════════════════════════════════════════════════════
// Cancellation pair detection
// ══════════════════════════════════════════════════════════════════════════════

/// A detected cancellation pair from an equation.
///
/// Represents the pattern `Outer(Inner(X)) = X` where `Outer` and `Inner` are
/// single-argument constructors (possibly from different categories) whose
/// composition is the identity. The equation is suppressed from `eqrel` generation
/// and handled by an eagerly-applied normalize arm instead.
///
/// Example: `PDrop(NQuote(P)) = P` — PDrop (Proc→Name) and NQuote (Name→Proc)
/// cancel each other when composed.
#[derive(Debug, Clone)]
pub struct CancellationPair {
    /// The outer constructor (e.g., PDrop)
    pub outer_constructor: Ident,
    /// The category the outer constructor belongs to (e.g., Proc)
    pub outer_category: Ident,
    /// The inner constructor (e.g., NQuote)
    pub inner_constructor: Ident,
    /// The category the inner constructor belongs to (e.g., Name)
    pub inner_category: Ident,
    /// Index into `language.equations`
    pub equation_index: usize,
    /// The equation's name identifier (e.g., QuoteDrop, ExecEq)
    pub equation_name: Ident,
}

/// Detect if an equation represents a cancellation pair.
///
/// A cancellation pair has the form `Outer(Inner(X)) = X` where:
/// - One side is a bare variable `X`
/// - The other side is `Apply(Outer, [Apply(Inner, [Var(X)])])` with the same `X`
/// - Both constructors have exactly one non-terminal argument and no binders
///
/// Checks both orientations: `LHS = RHS` and `RHS = LHS`.
pub fn detect_cancellation_pair(
    eq_idx: usize,
    eq: &super::language::Equation,
    language: &LanguageDef,
) -> Option<CancellationPair> {
    try_detect_cancellation(eq_idx, eq, &eq.left, &eq.right, language)
        .or_else(|| try_detect_cancellation(eq_idx, eq, &eq.right, &eq.left, language))
}

/// Try to detect a cancellation pair with `structured` as the composed side
/// and `variable` as the bare variable side.
fn try_detect_cancellation(
    eq_idx: usize,
    eq: &super::language::Equation,
    structured: &Pattern,
    variable: &Pattern,
    language: &LanguageDef,
) -> Option<CancellationPair> {
    // Variable side must be a bare variable
    let var_name = match variable {
        Pattern::Term(PatternTerm::Var(v)) => v,
        _ => return None,
    };

    // Structured side must be Apply(Outer, [inner_pattern])
    let (outer_ctor, inner_pattern) = match structured {
        Pattern::Term(PatternTerm::Apply { constructor, args }) if args.len() == 1 => {
            (constructor, &args[0])
        },
        _ => return None,
    };

    // Inner pattern must be Apply(Inner, [Var(same_name)])
    let (inner_ctor, innermost_var) = match inner_pattern {
        Pattern::Term(PatternTerm::Apply { constructor, args }) if args.len() == 1 => {
            (constructor, &args[0])
        },
        _ => return None,
    };

    // Innermost must be Var with same name as the variable side
    let inner_var = match innermost_var {
        Pattern::Term(PatternTerm::Var(v)) => v,
        _ => return None,
    };
    if var_name != inner_var {
        return None;
    }

    // Look up both constructors in language.terms
    let outer_rule = language.terms.iter().find(|r| r.label == *outer_ctor)?;
    let inner_rule = language.terms.iter().find(|r| r.label == *inner_ctor)?;

    // Both must have exactly 1 non-terminal field and no binders
    let outer_nt_count = outer_rule
        .items
        .iter()
        .filter(|item| matches!(item, GrammarItem::NonTerminal { .. }))
        .count();
    let inner_nt_count = inner_rule
        .items
        .iter()
        .filter(|item| matches!(item, GrammarItem::NonTerminal { .. }))
        .count();
    if outer_nt_count != 1 || inner_nt_count != 1 {
        return None;
    }
    if !outer_rule.bindings.is_empty() || !inner_rule.bindings.is_empty() {
        return None;
    }

    Some(CancellationPair {
        outer_constructor: outer_ctor.clone(),
        outer_category: outer_rule.category.clone(),
        inner_constructor: inner_ctor.clone(),
        inner_category: inner_rule.category.clone(),
        equation_index: eq_idx,
        equation_name: eq.name.clone(),
    })
}

/// Detect all cancellation pairs from equations.
///
/// Returns `(pairs, suppressed_indices)` where `suppressed_indices` is the set of
/// equation indices to suppress from `eqrel` generation.
pub fn detect_cancellation_pairs(
    language: &LanguageDef,
) -> (Vec<CancellationPair>, HashSet<usize>) {
    let mut pairs = Vec::new();
    let mut suppressed = HashSet::new();
    for (idx, eq) in language.equations.iter().enumerate() {
        if let Some(pair) = detect_cancellation_pair(idx, eq, language) {
            suppressed.insert(idx);
            pairs.push(pair);
        }
    }
    (pairs, suppressed)
}
