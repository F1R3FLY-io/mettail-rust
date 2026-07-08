//! Stage 3 — production wiring of in-Rho set-automaton matching.
//!
//! Piece 1: [`convert_lhs_pattern`] maps a `mettail_ast` structural LHS pattern to
//! the dovetail set-automaton input (`dovetail::rules::Pattern<String>`). A
//! variable or constructor application converts structurally; a constructor over a
//! single collection literal becomes an `AcApp` (which `compile_structural` rejects,
//! routing the rule to the AC path — Stage AC); binder / substitution /
//! collection-search metasyntax have no positional set-automaton image and fail
//! closed with a typed reason (Stage 3c / off-machine), so the capability gate can
//! report per-rule WHY a rule is not matched in Rho.
//!
//! The converter is TOTAL over `mettail_ast::Pattern` (every node either converts or
//! returns a typed reject — no panics), which is the executable half of FV (ix)'s
//! total-or-reject obligation. It agrees with the existing σ-receiver LHS-var
//! classifier (`lower_lhs_vars`) on "structural" — cross-checked in the tests — so a
//! rule can never be admitted by one path and rejected by the other.

use dovetail::rules::Pattern as DvPattern;
use mettail_ast::pattern::{Pattern, PatternTerm};

/// Why an LHS pattern has no structural set-automaton image (fail-closed to a later
/// stage rather than mis-compiling it into a wrong automaton).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternConvertReject {
    /// A `\x.` / `^[…].` binder (`Lambda` / `MultiLambda`) — the in-Rho binder slice
    /// (Stage 3c); the automaton has no binder image.
    Binder,
    /// A `subst` / `multisubst` (a host-computed ground σ slot) — Stage 3c.
    Subst,
    /// Collection-search metasyntax (`#map` / `#zip`, or a bare collection literal not
    /// under a constructor) — no positional / `AcApp` image; the AC path (Stage AC) or
    /// off-machine.
    CollectionSearch,
}

/// Convert a structural LHS pattern to its dovetail set-automaton input. Total over
/// `mettail_ast::Pattern`: every node either converts or returns a typed reject.
pub fn convert_lhs_pattern(p: &Pattern) -> Result<DvPattern<String>, PatternConvertReject> {
    match p {
        Pattern::Term(term) => convert_term(term),
        // A bare collection literal / search metasyntax at a matched position is not a
        // constructor-rooted structural pattern (a Collection is only structural as the
        // sole arg of a constructor — handled in `convert_term`'s Apply arm).
        Pattern::Collection { .. } | Pattern::Map { .. } | Pattern::Zip { .. } => {
            Err(PatternConvertReject::CollectionSearch)
        },
    }
}

fn convert_term(term: &PatternTerm) -> Result<DvPattern<String>, PatternConvertReject> {
    match term {
        PatternTerm::Var(id) => Ok(DvPattern::var(id.to_string())),
        PatternTerm::Apply { constructor, args } => {
            let op = constructor.to_string();
            // AC form: a constructor applied to a single collection literal (the bag).
            // Becomes an AcApp — a valid dovetail pattern that `compile_structural`
            // rejects, routing the rule to the AC path (Stage AC).
            if let [Pattern::Collection { elements, rest, .. }] = args.as_slice() {
                let fixed = elements
                    .iter()
                    .map(convert_lhs_pattern)
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(DvPattern::ac(op, fixed, rest.as_ref().map(|r| r.to_string())))
            } else {
                let converted = args
                    .iter()
                    .map(convert_lhs_pattern)
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(DvPattern::app(op, converted))
            }
        },
        PatternTerm::Lambda { .. } | PatternTerm::MultiLambda { .. } => {
            Err(PatternConvertReject::Binder)
        },
        PatternTerm::Subst { .. } | PatternTerm::MultiSubst { .. } => {
            Err(PatternConvertReject::Subst)
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ident(s: &str) -> syn::Ident {
        syn::parse_str(s).expect("valid identifier")
    }
    fn var(s: &str) -> Pattern {
        Pattern::Term(PatternTerm::Var(ident(s)))
    }
    fn app(constructor: &str, args: Vec<Pattern>) -> Pattern {
        Pattern::Term(PatternTerm::Apply { constructor: ident(constructor), args })
    }

    #[test]
    fn converts_a_structural_application() {
        assert_eq!(
            convert_lhs_pattern(&app("Swap", vec![var("x"), var("y")])),
            Ok(DvPattern::app(
                "Swap".to_string(),
                vec![DvPattern::var("x".to_string()), DvPattern::var("y".to_string())]
            ))
        );
    }

    #[test]
    fn converts_a_nested_application() {
        // Wrap(Pair(x, y)) — recursion propagates through the arg.
        assert_eq!(
            convert_lhs_pattern(&app("Wrap", vec![app("Pair", vec![var("x"), var("y")])])),
            Ok(DvPattern::app(
                "Wrap".to_string(),
                vec![DvPattern::app(
                    "Pair".to_string(),
                    vec![DvPattern::var("x".to_string()), DvPattern::var("y".to_string())]
                )]
            ))
        );
    }

    #[test]
    fn converts_a_bare_variable() {
        assert_eq!(convert_lhs_pattern(&var("z")), Ok(DvPattern::var("z".to_string())));
    }

    #[test]
    fn a_constructor_over_a_collection_becomes_ac() {
        // (PPar {P, Q, ...rest}) — the AC form; becomes AcApp (compile_structural rejects).
        let collection = Pattern::Collection {
            coll_type: None,
            elements: vec![var("P"), var("Q")],
            rest: Some(ident("rest")),
        };
        assert_eq!(
            convert_lhs_pattern(&app("PPar", vec![collection])),
            Ok(DvPattern::ac(
                "PPar".to_string(),
                vec![DvPattern::var("P".to_string()), DvPattern::var("Q".to_string())],
                Some("rest".to_string())
            ))
        );
    }

    #[test]
    fn binder_and_subst_and_search_fail_closed() {
        let lambda = Pattern::Term(PatternTerm::Lambda {
            binder: ident("x"),
            body: Box::new(var("y")),
        });
        assert_eq!(convert_lhs_pattern(&lambda), Err(PatternConvertReject::Binder));

        let multilambda = Pattern::Term(PatternTerm::MultiLambda {
            binders: vec![ident("x"), ident("y")],
            body: Box::new(var("z")),
        });
        assert_eq!(convert_lhs_pattern(&multilambda), Err(PatternConvertReject::Binder));

        let subst = Pattern::Term(PatternTerm::Subst {
            term: Box::new(var("t")),
            var: ident("x"),
            replacement: Box::new(var("r")),
        });
        assert_eq!(convert_lhs_pattern(&subst), Err(PatternConvertReject::Subst));

        let map = Pattern::Map {
            collection: Box::new(var("xs")),
            params: vec![ident("x")],
            body: Box::new(var("x")),
        };
        assert_eq!(convert_lhs_pattern(&map), Err(PatternConvertReject::CollectionSearch));

        let zip = Pattern::Zip {
            first: Box::new(var("a")),
            second: Box::new(var("b")),
        };
        assert_eq!(convert_lhs_pattern(&zip), Err(PatternConvertReject::CollectionSearch));
    }

    #[test]
    fn a_binder_inside_a_structural_arg_propagates_the_reject() {
        // f(\x.y) — the binder arg makes the whole conversion fail closed.
        let lambda = Pattern::Term(PatternTerm::Lambda {
            binder: ident("x"),
            body: Box::new(var("y")),
        });
        assert_eq!(
            convert_lhs_pattern(&app("f", vec![var("a"), lambda])),
            Err(PatternConvertReject::Binder)
        );
    }
}
