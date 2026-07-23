//! L9-4: `FltNode` — the native, opaque representation of a parsed FLT
//! (foreign-language template) guest body.
//!
//! # What it is
//!
//! A guest-body production (`SyntaxExpr::GuestBody`) captures a delimited region
//! written in a FOREIGN language — e.g. ``lam`App(${f}, K)` `` — WITHOUT the
//! host parser interpreting it. The host lexer's mode stack balances the
//! opener/closer (a distinct token KIND per delimiter form) so the host parser
//! sees a bracketed `FltOpen … FltClose` sequence; the `GuestBody` codegen then
//! assembles this `FltNode` from the token source:
//!
//! - `tag`      — the opener's payload (e.g. `lam`), naming which guest grammar
//!   elaborates the body (resolved by a `FltResolver` at lowering time, L9-6).
//! - `body_src` — ONE verbatim slice `input[open.end .. close.start]` of the
//!   original source. Storing a single contiguous slice (not a re-concatenation
//!   of tokens) is the **No-Injection** guarantee: the body is guest-parsed
//!   exactly once; no host token ever re-enters it, and a delimiter rendered
//!   into a later fill can never re-open the host grammar.
//! - `holes`    — the `${name}` / `${name:Cat}` metavariables found in the body,
//!   each with its byte `offset` INTO `body_src` (so the guest parser can splice
//!   `Var::Free` metavars at exactly the right positions).
//! - `position` — the opener's start position in the original source (for
//!   diagnostics and stable ordering).
//!
//! # Why it is an opaque leaf
//!
//! From the HOST's perspective `FltNode` is atomic data — a captured span, not a
//! host term. It therefore implements [`moniker::BoundTerm`] as a LEAF (like the
//! canonical numeric wrappers): it binds no variables, contributes no free
//! variables, and is identity under `close_term` / `open_term`. Elaboration into
//! actual host structure happens later (L9-6, `lower_proc`'s `PFlt` arm), never
//! during host binding/substitution.

use moniker::BoundTerm;

/// A `${name}` / `${name:Cat}` metavariable inside a guest body, positioned by
/// its byte offset into [`FltNode::body_src`].
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FltHole {
    /// The metavariable name (`f` in `${f}` or `${f:Proc}`).
    pub name: String,
    /// The optional declared category (`Proc` in `${f:Proc}`), `None` for a bare
    /// `${f}`. The guest reflector uses it for the single admission check (L9-6).
    pub category: Option<String>,
    /// The hole's byte offset INTO `body_src` (`hole.start - open.end`). The
    /// guest parser splices a `Var::Free` metavar at this position.
    pub offset: usize,
}

/// The native capture of a delimited FLT guest body. See the module docs.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FltNode {
    /// The opener's payload — the guest-grammar tag (e.g. `lam`).
    pub tag: String,
    /// The verbatim guest-body source `input[open.end .. close.start]` (ONE
    /// contiguous slice — the No-Injection guarantee).
    pub body_src: String,
    /// The `${…}` holes, in source order, offset into `body_src`.
    pub holes: Vec<FltHole>,
    /// The opener's start position in the original source.
    pub position: usize,
}

impl FltNode {
    /// Construct an `FltNode` from the assembled parts (used by the `GuestBody`
    /// WPDA codegen).
    pub fn new(tag: String, body_src: String, holes: Vec<FltHole>, position: usize) -> Self {
        Self { tag, body_src, holes, position }
    }
}

// `FltNode` is an opaque host-side leaf: no bound/free variables, identity under
// every scope operation. Mirrors the canonical numeric wrappers
// (`runtime/src/canonical_*.rs`).
impl BoundTerm<String> for FltNode {
    fn term_eq(&self, other: &Self) -> bool {
        self == other
    }

    fn close_term(
        &mut self,
        _state: moniker::ScopeState,
        _on_free: &impl moniker::OnFreeFn<String>,
    ) {
    }

    fn open_term(
        &mut self,
        _state: moniker::ScopeState,
        _on_bound: &impl moniker::OnBoundFn<String>,
    ) {
    }

    fn visit_vars(&self, _on_var: &mut impl FnMut(&moniker::Var<String>)) {}

    fn visit_mut_vars(&mut self, _on_var: &mut impl FnMut(&mut moniker::Var<String>)) {}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flt_node_is_a_value_leaf() {
        let n = FltNode::new(
            "lam".into(),
            "App(${f}, K)".into(),
            vec![FltHole { name: "f".into(), category: None, offset: 4 }],
            0,
        );
        // Equal by value; distinct tags/bodies differ.
        assert_eq!(n.clone(), n);
        assert_ne!(
            n,
            FltNode::new("id".into(), "App(${f}, K)".into(), n.holes.clone(), 0)
        );
        // `body_src[offset..]` locates the hole verbatim.
        assert_eq!(&n.body_src[n.holes[0].offset..n.holes[0].offset + 4], "${f}");
    }
}
