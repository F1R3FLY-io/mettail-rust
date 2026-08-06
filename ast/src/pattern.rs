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
use proc_macro2::{Ident, Span};
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
        Pattern::Collection { coll_type: _, elements, rest } => {
            // SAFETY: both destructor-bearing fields belong to a ManuallyDrop
            // value and are read exactly once. The moved values assume normal
            // destruction here.
            // `CollectionType` has no destructor.  The parent is forgotten
            // after its recursive children are moved to `work`, so there is
            // no lifecycle action to perform for this field.
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
        writeln!(f, "sym: {},", ident)?;
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
