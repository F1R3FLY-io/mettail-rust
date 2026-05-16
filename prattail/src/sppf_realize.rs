//! AST realization from an SPPF.
//!
//! Given an `Sppf` and a root `SppfId`, the realization pass walks the forest
//! and produces user AST values by invoking each Packing's action function
//! recursively. For ambiguous parses, it fans out over all packings linked to
//! each Symbol, producing a `Vec` of materializations.
//!
//! ## Why this exists
//!
//! Under Option C (see `~/.claude/plans/option-c-sppf-on-wpda.md`), the walker
//! no longer eagerly fires `action_fn` during reduce — instead, each reduce
//! interns a `Packing` SPPF node, and the user-AST type is constructed at
//! extraction time by traversing the SPPF.
//!
//! This decoupling has two payoffs:
//!
//! 1. Ambiguity is preserved (multiple Packings per Symbol → multiple AST
//!    realizations).
//! 2. The walker's hot path drops the Arc-clone-and-mutate of `SemanticBuilder`,
//!    yielding the memory budget compliance (plan §6).
//!
//! ## Pluggable `ActionResolver`
//!
//! Realization is parameterized over an `ActionResolver` trait so that this
//! module can be tested with synthetic resolvers (`StringResolver`, etc.)
//! before the WPDA engine is plumbed.
//!
//! ## Iteration over recursion
//!
//! Realization avoids host-stack recursion via an explicit work-stack frame
//! type (`RealizeFrame`). This honors the project's "no host-stack recursion"
//! mandate (cf. `prattail/src/wpda_walker.rs` trampoline design).

use crate::sppf::{Sppf, SppfId, SppfNode};

// ══════════════════════════════════════════════════════════════════════════════
// ActionResolver trait
// ══════════════════════════════════════════════════════════════════════════════

/// User-supplied resolver that turns SPPF nodes into AST values of type `Out`.
///
/// Implementations choose how to map `(rule_idx, children)` to an output:
/// the walker's downstream consumer plugs in a `WpdaEngineActionResolver`
/// that calls the codegen-emitted `action_fn`; tests can plug in a
/// `StringResolver` that builds s-expressions.
///
/// All methods are `&self` — resolvers are pure factories. Side effects (e.g.
/// gensyms) must derive determinism from the SPPF data itself, not from
/// process-global state. See plan §10.1.
pub trait ActionResolver {
    /// The user AST type.
    type Out: Clone;

    /// Resolve a `Terminal` leaf into an AST value.
    fn resolve_terminal(
        &self,
        token_kind: &crate::automata::TokenKind,
        text: &str,
        pos: crate::sppf::PosOrSynth,
    ) -> Self::Out;

    /// Resolve an `Epsilon` (empty production) into an AST value.
    fn resolve_epsilon(&self, pos: u32) -> Self::Out;

    /// Resolve a `Packing` into an AST value given its rule index and
    /// already-resolved children.
    ///
    /// The slice of children matches the order they were interned into the
    /// `Packing.children` Vec.
    fn resolve_packing(&self, rule_idx: u32, children: &[Self::Out]) -> Self::Out;

    /// Resolve a `CollectionId` placeholder by materializing the collection
    /// contents. The walker-side `sppf_collection_arena` lookup happens
    /// inside the resolver impl (which has access to the walker context).
    /// Default impl panics; concrete walker-aware resolvers override.
    fn resolve_collection_id(&self, id: u32) -> Self::Out {
        panic!("ActionResolver::resolve_collection_id called with id={} but resolver does not support collections", id);
    }

    /// Resolve an `OptAbsent` leaf — the user AST gets a "None" value.
    fn resolve_opt_absent(&self, _pos: u32) -> Self::Out {
        panic!("ActionResolver::resolve_opt_absent called but resolver does not support optional groups");
    }

    /// Resolve a `Predicate` payload reference. The handle is into the
    /// walker's `sppf_predicate_arena`.
    fn resolve_predicate(&self, handle: u32) -> Self::Out {
        panic!("ActionResolver::resolve_predicate called with handle={} but resolver does not support predicates", handle);
    }

    /// Resolve a `BinderScope` leaf. The user AST gets an
    /// `ActionArg::BinderScope(BinderHandle{names, depth})`-shaped value.
    fn resolve_binder_scope(&self, names: Vec<String>, depth: u16) -> Self::Out {
        let _ = (names, depth);
        panic!("ActionResolver::resolve_binder_scope called but resolver does not support binder scopes");
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Realization API
// ══════════════════════════════════════════════════════════════════════════════

/// Realize all distinct AST values rooted at `root`.
///
/// Returns the cross-product of all packing choices along the path from `root`
/// down to the leaves. For a non-ambiguous parse this is a 1-element Vec.
/// For an n-way ambiguous parse it contains n entries (or more if ambiguity
/// is nested).
///
/// `limit` caps the realization at the first `limit` results to bound
/// exponential AST counts on adversarial inputs (plan §4.3). `None` means
/// unbounded.
pub fn realize_all<R: ActionResolver>(
    sppf: &Sppf,
    root: SppfId,
    resolver: &R,
    limit: Option<usize>,
) -> Vec<R::Out> {
    let mut out = Vec::new();
    realize_into(sppf, root, resolver, limit, &mut out);
    out
}

/// As `realize_all`, but appends to a caller-supplied `Vec`.
pub fn realize_into<R: ActionResolver>(
    sppf: &Sppf,
    root: SppfId,
    resolver: &R,
    limit: Option<usize>,
    out: &mut Vec<R::Out>,
) {
    // Realization is a recursive structural unfold. Concretely:
    //
    //   realize(Terminal)       = [resolver.resolve_terminal(...)]
    //   realize(Epsilon)        = [resolver.resolve_epsilon(...)]
    //   realize(Packing(r, cs)) = [resolver.resolve_packing(r, ks)
    //                              | ks <- cartesian(map(realize, cs))]
    //   realize(Symbol(nt, lo, hi)) =
    //       concat([realize(p) | p <- sppf.packings_of(sym)])
    //
    // We compute this iteratively via memoization keyed by SppfId. Because
    // the arena is a DAG (no cycles — packings can only reference earlier
    // ids, since each reduce interns a packing AFTER its children), one
    // bottom-up pass over the relevant subgraph suffices.
    //
    // To honor the "no host-stack recursion" mandate, we drive the unfold
    // via an explicit visit-stack.

    let mut memo: std::collections::HashMap<SppfId, Vec<R::Out>> =
        std::collections::HashMap::new();

    // Visit-stack of (id, phase). Phase 0 = needs children visited;
    // phase 1 = children done, ready to combine.
    enum Phase {
        Enter,
        Leave,
    }
    let mut stack: Vec<(SppfId, Phase)> = vec![(root, Phase::Enter)];

    while let Some((id, phase)) = stack.pop() {
        if memo.contains_key(&id) {
            continue;
        }
        match phase {
            Phase::Enter => {
                // Schedule the combine pass after children are ready.
                stack.push((id, Phase::Leave));
                // Push children dependencies onto the stack.
                match sppf.node(id) {
                    Some(SppfNode::Terminal { .. })
                    | Some(SppfNode::Epsilon { .. })
                    | Some(SppfNode::CollectionId { .. })
                    | Some(SppfNode::OptAbsent { .. })
                    | Some(SppfNode::Predicate { .. })
                    | Some(SppfNode::BinderScope { .. }) => {
                        // No children.
                    }
                    Some(SppfNode::Symbol { .. }) => {
                        for &packing_id in sppf.packings_of(id) {
                            if !memo.contains_key(&packing_id) {
                                stack.push((packing_id, Phase::Enter));
                            }
                        }
                    }
                    Some(SppfNode::Packing { children, .. }) => {
                        for &child_id in children {
                            if !memo.contains_key(&child_id) {
                                stack.push((child_id, Phase::Enter));
                            }
                        }
                    }
                    None => {
                        // Out-of-range id — produce empty result.
                        memo.insert(id, Vec::new());
                    }
                }
            }
            Phase::Leave => {
                let results = match sppf.node(id) {
                    Some(SppfNode::Terminal {
                        token_kind,
                        text_handle,
                        pos,
                        pushed_via_push_ident: _,
                    }) => {
                        let text = sppf.text(*text_handle);
                        vec![resolver.resolve_terminal(token_kind, text, *pos)]
                    }
                    Some(SppfNode::Epsilon { pos }) => {
                        vec![resolver.resolve_epsilon(*pos)]
                    }
                    Some(SppfNode::CollectionId { id: cid }) => {
                        vec![resolver.resolve_collection_id(*cid)]
                    }
                    Some(SppfNode::OptAbsent { pos }) => {
                        vec![resolver.resolve_opt_absent(*pos)]
                    }
                    Some(SppfNode::Predicate { handle }) => {
                        vec![resolver.resolve_predicate(*handle)]
                    }
                    Some(SppfNode::BinderScope { names_text, depth }) => {
                        let names: Vec<String> = names_text
                            .iter()
                            .map(|&h| sppf.text(h).to_string())
                            .collect();
                        vec![resolver.resolve_binder_scope(names, *depth)]
                    }
                    Some(SppfNode::Symbol { .. }) => {
                        // Concatenate all packings' realizations.
                        let mut acc: Vec<R::Out> = Vec::new();
                        for &packing_id in sppf.packings_of(id) {
                            let packing_results = memo
                                .get(&packing_id)
                                .expect("packing visited before its parent symbol");
                            for v in packing_results {
                                if let Some(cap) = limit {
                                    if acc.len() >= cap {
                                        break;
                                    }
                                }
                                acc.push(v.clone());
                            }
                            if let Some(cap) = limit {
                                if acc.len() >= cap {
                                    break;
                                }
                            }
                        }
                        acc
                    }
                    Some(SppfNode::Packing { rule_idx, children }) => {
                        // Cartesian product of children's realizations, then
                        // resolve_packing for each.
                        let mut combos: Vec<Vec<R::Out>> = vec![Vec::with_capacity(children.len())];
                        for &child_id in children {
                            let child_results = memo
                                .get(&child_id)
                                .expect("child visited before its parent packing");
                            let mut next: Vec<Vec<R::Out>> =
                                Vec::with_capacity(combos.len() * child_results.len().max(1));
                            for combo in &combos {
                                for child_value in child_results {
                                    let mut extended = combo.clone();
                                    extended.push(child_value.clone());
                                    next.push(extended);
                                    if let Some(cap) = limit {
                                        if next.len() >= cap {
                                            break;
                                        }
                                    }
                                }
                                if let Some(cap) = limit {
                                    if next.len() >= cap {
                                        break;
                                    }
                                }
                            }
                            combos = next;
                        }
                        combos
                            .into_iter()
                            .map(|child_values| resolver.resolve_packing(*rule_idx, &child_values))
                            .collect()
                    }
                    None => Vec::new(),
                };
                memo.insert(id, results);
            }
        }
    }

    if let Some(results) = memo.remove(&root) {
        match limit {
            Some(cap) => out.extend(results.into_iter().take(cap.saturating_sub(out.len()))),
            None => out.extend(results),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::TokenKind;
    use crate::sppf::{PosOrSynth, Sppf};

    /// Builds s-expressions for testing.
    struct StringResolver;

    impl ActionResolver for StringResolver {
        type Out = String;

        fn resolve_terminal(
            &self,
            token_kind: &TokenKind,
            text: &str,
            _pos: PosOrSynth,
        ) -> String {
            match (token_kind, text.is_empty()) {
                (TokenKind::Fixed(s), _) => s.clone(),
                (_, false) => text.to_string(),
                (other, true) => format!("{:?}", other),
            }
        }

        fn resolve_epsilon(&self, _pos: u32) -> String {
            "ε".to_string()
        }

        fn resolve_packing(&self, rule_idx: u32, children: &[String]) -> String {
            format!("(r{} {})", rule_idx, children.join(" "))
        }
    }

    fn k_fixed(s: &str) -> TokenKind {
        TokenKind::Fixed(s.to_string())
    }

    #[test]
    fn realize_single_terminal() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(0), Some("x"), false);
        let results = realize_all(&s, t, &StringResolver, None);
        assert_eq!(results, vec!["x"]);
    }

    #[test]
    fn realize_single_packing() {
        let mut s = Sppf::new();
        let t1 = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(0), Some("x"), false);
        let t2 = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(1), None, false);
        let t3 = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(2), Some("y"), false);
        let p = s.intern_packing(0, vec![t1, t2, t3]);
        let results = realize_all(&s, p, &StringResolver, None);
        assert_eq!(results.len(), 1);
        assert!(results[0].contains("x"));
        assert!(results[0].contains("y"));
    }

    #[test]
    fn realize_symbol_with_one_packing() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(0), Some("x"), false);
        let p = s.intern_packing(0, vec![t]);
        let sym = s.intern_symbol(0, 0, 1);
        s.link_packing_to_symbol(sym, p);
        let results = realize_all(&s, sym, &StringResolver, None);
        assert_eq!(results, vec!["(r0 x)"]);
    }

    #[test]
    fn realize_symbol_with_multiple_packings() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(0), Some("x"), false);
        let p1 = s.intern_packing(0, vec![t]);
        let p2 = s.intern_packing(1, vec![t]);
        let sym = s.intern_symbol(0, 0, 1);
        s.link_packing_to_symbol(sym, p1);
        s.link_packing_to_symbol(sym, p2);
        let results = realize_all(&s, sym, &StringResolver, None);
        assert_eq!(results.len(), 2);
        assert!(results.contains(&"(r0 x)".to_string()));
        assert!(results.contains(&"(r1 x)".to_string()));
    }

    #[test]
    fn realize_tomita_ambiguous_expression_yields_two() {
        // Same grammar as sppf::tests::tomita_ambiguous_expression.
        let mut s = Sppf::new();
        let nt_e: u32 = 0;
        const RULE_ADD: u32 = 0;
        const RULE_MUL: u32 = 1;
        const RULE_VAR: u32 = 2;

        let t_a = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(0), Some("a"), false);
        let t_plus = s.intern_terminal(k_fixed("+"), PosOrSynth::Real(1), None, false);
        let t_b = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(2), Some("b"), false);
        let t_mul = s.intern_terminal(k_fixed("*"), PosOrSynth::Real(3), None, false);
        let t_c = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(4), Some("c"), false);

        let p_a = s.intern_packing(RULE_VAR, vec![t_a]);
        let p_b = s.intern_packing(RULE_VAR, vec![t_b]);
        let p_c = s.intern_packing(RULE_VAR, vec![t_c]);
        let e_a = s.intern_symbol(nt_e, 0, 1);
        let e_b = s.intern_symbol(nt_e, 2, 3);
        let e_c = s.intern_symbol(nt_e, 4, 5);
        s.link_packing_to_symbol(e_a, p_a);
        s.link_packing_to_symbol(e_b, p_b);
        s.link_packing_to_symbol(e_c, p_c);

        let p_bc_mul = s.intern_packing(RULE_MUL, vec![e_b, t_mul, e_c]);
        let e_bc = s.intern_symbol(nt_e, 2, 5);
        s.link_packing_to_symbol(e_bc, p_bc_mul);

        let p_ab_add = s.intern_packing(RULE_ADD, vec![e_a, t_plus, e_b]);
        let e_ab = s.intern_symbol(nt_e, 0, 3);
        s.link_packing_to_symbol(e_ab, p_ab_add);

        let p_top_add = s.intern_packing(RULE_ADD, vec![e_a, t_plus, e_bc]);
        let p_top_mul = s.intern_packing(RULE_MUL, vec![e_ab, t_mul, e_c]);
        let e_top = s.intern_symbol(nt_e, 0, 5);
        s.link_packing_to_symbol(e_top, p_top_add);
        s.link_packing_to_symbol(e_top, p_top_mul);

        let results = realize_all(&s, e_top, &StringResolver, None);
        // Both derivations should appear; no cross-product overcounting.
        assert_eq!(
            results.len(),
            2,
            "expected exactly 2 derivations (RULE_ADD-top and RULE_MUL-top), got {} results: {:?}",
            results.len(),
            results
        );
        // Each top-level packing's realization is wrapped through E(a), E(bc),
        // E(ab), E(c) symbol Realizations, which all wrap their child Packing
        // via resolve_packing. So the strings include rule_idx wrappers for
        // each Symbol level. Sanity-check both forms appear.
        let has_add_top = results
            .iter()
            .any(|r| r.starts_with("(r0 ") && r.contains("+") && r.contains("*"));
        let has_mul_top = results
            .iter()
            .any(|r| r.starts_with("(r1 ") && r.contains("+") && r.contains("*"));
        assert!(
            has_add_top && has_mul_top,
            "missing one of the two derivations; got: {:?}",
            results
        );
    }

    #[test]
    fn realize_respects_limit() {
        // Symbol with 5 packings, limit=2.
        let mut s = Sppf::new();
        let t = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(0), Some("x"), false);
        let sym = s.intern_symbol(0, 0, 1);
        for rule in 0..5u32 {
            let p = s.intern_packing(rule, vec![t]);
            s.link_packing_to_symbol(sym, p);
        }
        let results = realize_all(&s, sym, &StringResolver, Some(2));
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn realize_epsilon() {
        let mut s = Sppf::new();
        let eps = s.intern_epsilon(3);
        let results = realize_all(&s, eps, &StringResolver, None);
        assert_eq!(results, vec!["ε"]);
    }

    #[test]
    fn realize_packing_with_epsilon_child() {
        let mut s = Sppf::new();
        let t = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(0), Some("x"), false);
        let eps = s.intern_epsilon(1);
        let p = s.intern_packing(0, vec![t, eps]);
        let results = realize_all(&s, p, &StringResolver, None);
        assert_eq!(results, vec!["(r0 x ε)"]);
    }

    /// Property: parsing the same Tomita example from scratch (twice) yields
    /// the same SPPF and same realization. Determinism guard (plan §11.5 I3).
    #[test]
    fn determinism_independent_rebuilds_realize_identically() {
        fn build() -> (Sppf, SppfId) {
            let mut s = Sppf::new();
            let nt_e: u32 = 0;
            let t_a = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(0), Some("a"), false);
            let t_b = s.intern_terminal(TokenKind::Ident, PosOrSynth::Real(1), Some("b"), false);
            let p1 = s.intern_packing(0, vec![t_a, t_b]);
            let p2 = s.intern_packing(1, vec![t_a, t_b]);
            let sym = s.intern_symbol(nt_e, 0, 2);
            s.link_packing_to_symbol(sym, p1);
            s.link_packing_to_symbol(sym, p2);
            (s, sym)
        }
        let (s1, r1) = build();
        let (s2, r2) = build();
        let v1 = realize_all(&s1, r1, &StringResolver, None);
        let v2 = realize_all(&s2, r2, &StringResolver, None);
        assert_eq!(v1, v2);
        assert_eq!(r1, r2);
    }
}
