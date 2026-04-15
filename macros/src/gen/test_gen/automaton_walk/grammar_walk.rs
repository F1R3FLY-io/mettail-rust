//! Grammar-driven string generation, top-down over `LanguageDef.terms`.
//!
//! For each category the macro emits a helper — `arb_<cat>_surface_string`
//! — that walks the grammar rules, picks one tape-byte-per-rule via a
//! `SelectionPolicy`, emits terminals verbatim, recurses into
//! non-terminals, and delegates token-class terminals to the classified
//! sampler (from [`super::classify`]).
//!
//! **Architectural choice (hybrid):** this module provides a
//! grammar-walk *view* on top of the existing AST-tape builder — the
//! AST builder already understands binders, abstractions, and
//! collections correctly, and its generated Display code produces
//! parseable surface text for those complex constructs (by design of
//! the original Display emitter). Rewriting all of that in a separate
//! string-walker would duplicate tens of thousands of lines of
//! display-correct logic.
//!
//! The actual string the generator produces is **`Display(arb_cat_ast())`**
//! where `arb_cat_ast` is the grammar-walked AST. The improvement over
//! the pre-existing behaviour is the *literal-emission* layer:
//! literals now go through the classifier (see
//! [`super::classify::classify_token`]) and through a grammar-aware
//! projection in `strategies::generate_literal_build_code`.
//!
//! The `SelectionPolicy` trait below is the selection hook the plan
//! promised for distributional control.

use mettail_ast::language::LanguageDef;

/// A selection policy over grammar rules applicable at a given
/// non-terminal. Implementations consume tape bytes to pick a rule.
///
/// The default [`UniformPolicy`] picks uniformly over applicable
/// rules. Custom policies can bias toward rare constructors to
/// improve coverage.
pub trait SelectionPolicy: Send + Sync {
    /// Given the set of applicable rules and a tape byte, return the
    /// index of the chosen rule.
    fn pick(&self, num_rules: usize, tape_byte: u8) -> usize;
}

/// Uniform policy over rules applicable to a category.
pub struct UniformPolicy;

impl SelectionPolicy for UniformPolicy {
    fn pick(&self, num_rules: usize, tape_byte: u8) -> usize {
        if num_rules == 0 { 0 } else { (tape_byte as usize) % num_rules }
    }
}

/// Weighted policy — pick among rules with non-uniform probability.
/// Weights are indexed by rule order in the grammar.
pub struct WeightedPolicy {
    pub weights: Vec<u32>,
}

impl SelectionPolicy for WeightedPolicy {
    fn pick(&self, num_rules: usize, tape_byte: u8) -> usize {
        if num_rules == 0 {
            return 0;
        }
        let total: u32 = self.weights.iter().take(num_rules).sum();
        if total == 0 {
            return (tape_byte as usize) % num_rules;
        }
        let target = (tape_byte as u32) % total;
        let mut acc = 0u32;
        for (i, w) in self.weights.iter().take(num_rules).enumerate() {
            acc += *w;
            if target < acc {
                return i;
            }
        }
        num_rules - 1
    }
}

/// Count applicable rules for a category in a language definition.
///
/// Used by codegen to size the modulo at rule-selection sites so the
/// tape byte maps to a valid rule index.
pub fn applicable_rules_for(category_name: &str, language: &LanguageDef) -> usize {
    language
        .terms
        .iter()
        .filter(|r| r.category == category_name)
        .count()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uniform_policy_picks_in_range() {
        let p = UniformPolicy;
        for b in 0u8..=255u8 {
            let idx = p.pick(5, b);
            assert!(idx < 5);
        }
    }

    #[test]
    fn uniform_policy_zero_rules_returns_zero() {
        let p = UniformPolicy;
        assert_eq!(p.pick(0, 42), 0);
    }

    #[test]
    fn weighted_policy_respects_weights() {
        let p = WeightedPolicy { weights: vec![1, 3] };
        // Total = 4. 0 → idx 0 (acc=1 > 0); 1,2,3 → idx 1 (acc=4 > 1,2,3).
        assert_eq!(p.pick(2, 0), 0);
        assert_eq!(p.pick(2, 1), 1);
        assert_eq!(p.pick(2, 2), 1);
        assert_eq!(p.pick(2, 3), 1);
    }

    #[test]
    fn weighted_policy_all_zero_weights_falls_back_uniform() {
        let p = WeightedPolicy { weights: vec![0, 0, 0] };
        for b in 0u8..=255u8 {
            let idx = p.pick(3, b);
            assert!(idx < 3);
        }
    }
}
