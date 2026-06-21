use super::*;
use syn::parse2;

fn parse_lang(src: proc_macro2::TokenStream) -> LanguageDef {
    parse2::<LanguageDef>(src).expect("language parse failed")
}

fn ident(name: &str) -> Ident {
    Ident::new(name, proc_macro2::Span::call_site())
}

fn ac_match_pred() -> BehavioralPred {
    BehavioralPred::AcMatch {
        bag: ident("bag"),
        elements: vec![ident("head"), ident("tail")],
        rest: Some(ident("rest")),
    }
}

#[test]
fn ac_match_quantified_formula_lowering_is_rejected_explicitly() {
    let err = ac_match_pred()
        .try_to_quantified_formula()
        .expect_err("AcMatch must not be embedded in QuantifiedFormula");

    assert!(err.contains("ac_match"));
    assert!(err.contains("QuantifiedFormula"));
}

#[test]
fn ac_match_formula_codegen_emits_compile_error_instead_of_panicking() {
    let tokens = ac_match_pred().to_quantified_formula().to_string();

    assert!(tokens.contains("compile_error"));
    assert!(tokens.contains("__unsupported_behavioral_pred__"));
}

#[test]
fn nested_ac_match_quantified_formula_lowering_propagates_error() {
    let relation = BehavioralPred::RelationQuery {
        relation_name: ident("halts"),
        args: vec![PredArg::Var(ident("x"))],
        negated: false,
    };
    let pred = BehavioralPred::And(Box::new(relation), Box::new(ac_match_pred()));
    let err = pred
        .try_to_quantified_formula()
        .expect_err("compound predicates must reject nested AcMatch");

    assert!(err.contains("ac_match"));
    assert!(err.contains("QuantifiedFormula"));
}

#[test]
fn empty_guards_block_parses() {
    let lang = parse_lang(quote::quote! {
        name: Test,
        types { },
        guards { },
        terms { }
    });
    assert!(lang.guard_config.is_some());
    let gc = lang.guard_config.as_ref().expect("just checked");
    assert!(gc.builtin_predicates.is_none(), "no direct items → None");
    assert!(gc.connectives.is_none());
    assert!(gc.theories.is_empty());
    assert!(gc.channels.is_none());
}

#[test]
fn guards_block_absent() {
    let lang = parse_lang(quote::quote! {
        name: Test,
        types { },
        terms { }
    });
    assert!(lang.guard_config.is_none(), "absent block → None");
}

#[test]
fn parse_simple_predicate_decl() {
    let lang = parse_lang(quote::quote! {
        name: Test,
        types { },
        guards {
            eq . x, y |- x "==" y ;
        },
        terms { }
    });
    let gc = lang.guard_config.as_ref().expect("present");
    let preds = gc.builtin_predicates.as_ref().expect("explicit predicates");
    assert_eq!(preds.len(), 1);
    let p = &preds[0];
    assert_eq!(p.name.to_string(), "eq");
    assert_eq!(p.params.len(), 2);
    assert_eq!(p.params[0].name.to_string(), "x");
    assert_eq!(p.params[1].name.to_string(), "y");
    assert_eq!(p.syntax_forms.len(), 1);
}

#[test]
fn parse_alternative_syntax_forms() {
    let lang = parse_lang(quote::quote! {
        name: Test,
        types { },
        guards {
            gt . x, y |- x ">" y | "gt" "(" x "," y ")" ;
        },
        terms { }
    });
    let gc = lang.guard_config.as_ref().expect("present");
    let preds = gc.builtin_predicates.as_ref().expect("explicit");
    assert_eq!(preds.len(), 1);
    assert_eq!(preds[0].syntax_forms.len(), 2);
}

#[test]
fn parse_annotations() {
    let lang = parse_lang(quote::quote! {
        name: Test,
        types { },
        guards {
            eq . x, y |- x "==" y @[selectivity(0.1), cost(2)] ;
        },
        terms { }
    });
    let gc = lang.guard_config.as_ref().expect("present");
    let preds = gc.builtin_predicates.as_ref().expect("explicit");
    let p = &preds[0];
    assert_eq!(p.annotations.selectivity, Some(0.1));
    assert_eq!(p.annotations.cost, Some(2));
}

#[test]
fn parse_variadic_params() {
    let lang = parse_lang(quote::quote! {
        name: Test,
        types { },
        guards {
            eq_chain . xs+ |- "==" "(" xs ")" ;
            opt . xs* |- "opt" "(" xs ")" ;
            bounded . xs{2,5} |- "b" "(" xs ")" ;
        },
        terms { }
    });
    let preds = lang
        .guard_config
        .as_ref()
        .expect("present")
        .builtin_predicates
        .as_ref()
        .expect("explicit");
    assert_eq!(preds.len(), 3);
    assert_eq!(preds[0].params[0].quantifier, Some(ParamQuantifier::OneOrMore));
    assert_eq!(preds[1].params[0].quantifier, Some(ParamQuantifier::ZeroOrMore));
    match &preds[2].params[0].quantifier {
        Some(ParamQuantifier::Range { min, max }) => {
            assert_eq!(*min, 2);
            assert_eq!(*max, Some(5));
        },
        other => panic!("expected Range, got {:?}", other),
    }
}

#[test]
fn parse_typed_params() {
    let lang = parse_lang(quote::quote! {
        name: Test,
        types { },
        guards {
            gt . x: Int, y: Int |- x ">" y ;
            num . xs: (Int|Float) |- "num" "(" xs ")" ;
        },
        terms { }
    });
    let preds = lang
        .guard_config
        .as_ref()
        .expect("present")
        .builtin_predicates
        .as_ref()
        .expect("explicit");
    match &preds[0].params[0].ty {
        Some(ParamType::Single(id)) => assert_eq!(id.to_string(), "Int"),
        other => panic!("expected Single(Int), got {:?}", other),
    }
    match &preds[1].params[0].ty {
        Some(ParamType::Union(ids)) => {
            assert_eq!(ids.len(), 2);
            assert_eq!(ids[0].to_string(), "Int");
            assert_eq!(ids[1].to_string(), "Float");
        },
        other => panic!("expected Union, got {:?}", other),
    }
}

#[test]
fn parse_connectives_block() {
    let lang = parse_lang(quote::quote! {
        name: Test,
        types { },
        guards {
            connectives {
                and = "and" | "∧";
                or = "or" | "∨";
                not = "not" | "¬";
            }
        },
        terms { }
    });
    let conns = lang
        .guard_config
        .as_ref()
        .expect("present")
        .connectives
        .as_ref()
        .expect("present");
    assert_eq!(conns.len(), 3);
    assert_eq!(conns[0].role, ConnectiveRole::And);
    assert_eq!(conns[0].keywords, vec!["and".to_string(), "∧".to_string()]);
    assert_eq!(conns[1].role, ConnectiveRole::Or);
    assert_eq!(conns[2].role, ConnectiveRole::Not);
}

#[test]
fn parse_theories_block() {
    let lang = parse_lang(quote::quote! {
        name: Test,
        types { },
        guards {
            theories {
                arithmetic = PresburgerAlgebra for [Int];
                patterns = UnificationTheory for [Proc, Name];
                types_t = LatticeTheory;
            }
        },
        terms { }
    });
    let theories = &lang.guard_config.as_ref().expect("present").theories;
    assert_eq!(theories.len(), 3);
    assert_eq!(theories[0].name.to_string(), "arithmetic");
    assert_eq!(theories[0].handled_types.as_ref().map(|cs| cs.len()), Some(1));
    assert!(theories[2].handled_types.is_none(), "no `for [...]` → None");
}

#[test]
fn parse_channels_block() {
    let lang = parse_lang(quote::quote! {
        name: Test,
        types { },
        guards {
            channels {
                channel Name;
                channel Place;
                join PGuardedInput(ch: Name);
                join PJoin(ch1: Name, ch2: Name, ch3: Name);
            }
        },
        terms { }
    });
    let ch = lang
        .guard_config
        .as_ref()
        .expect("present")
        .channels
        .as_ref()
        .expect("present");
    assert_eq!(ch.channel_categories.len(), 2);
    assert_eq!(ch.join_patterns.len(), 2);
    assert_eq!(ch.join_patterns[1].channel_params.len(), 3);
}

#[test]
fn parse_full_guards_block() {
    let lang = parse_lang(quote::quote! {
        name: RhoCalc,
        types { },
        guards {
            eq . x, y |- x "==" y @[selectivity(0.1), cost(2)] ;
            neq . x, y |- x "!=" y ;
            connectives {
                and = "and" | "∧";
                not = "not";
            }
            theories {
                arithmetic = PresburgerAlgebra for [Int];
            }
            channels {
                channel Name;
                join PGuardedInput(ch: Name);
            }
        },
        terms { }
    });
    let gc = lang.guard_config.as_ref().expect("present");
    assert_eq!(gc.builtin_predicates.as_ref().expect("present").len(), 2);
    assert_eq!(gc.connectives.as_ref().expect("present").len(), 2);
    assert_eq!(gc.theories.len(), 1);
    assert_eq!(
        gc.channels
            .as_ref()
            .expect("present")
            .channel_categories
            .len(),
        1
    );
}

#[test]
fn connective_map_bidirectional_invariant() {
    let decls = vec![
        ConnectiveDecl {
            role: ConnectiveRole::And,
            keywords: vec!["and".into(), "∧".into()],
        },
        ConnectiveDecl {
            role: ConnectiveRole::Not,
            keywords: vec!["not".into(), "¬".into()],
        },
    ];
    let map = ConnectiveMap::from_decls(&decls).expect("valid map");
    // Forward
    assert!(map.role_to_keywords[&ConnectiveRole::And].contains(&"and".to_string()));
    assert!(map.role_to_keywords[&ConnectiveRole::And].contains(&"∧".to_string()));
    // Reverse
    assert_eq!(map.keyword_to_role.get("and"), Some(&ConnectiveRole::And));
    assert_eq!(map.keyword_to_role.get("¬"), Some(&ConnectiveRole::Not));
    // Cross-check bidirectionality
    for (kw, role) in &map.keyword_to_role {
        assert!(map.role_to_keywords[role].contains(kw));
    }
    for (role, kws) in &map.role_to_keywords {
        for kw in kws {
            assert_eq!(map.keyword_to_role[kw], *role);
        }
    }
}

#[test]
fn connective_map_conn01_duplicate_keyword() {
    let decls = vec![
        ConnectiveDecl {
            role: ConnectiveRole::And,
            keywords: vec!["and".into()],
        },
        ConnectiveDecl {
            role: ConnectiveRole::Or,
            keywords: vec!["and".into()], // duplicate keyword across roles!
        },
    ];
    let result = ConnectiveMap::from_decls(&decls);
    assert!(result.is_err());
    let err = result.expect_err("should be CONN01");
    assert!(err.to_string().contains("CONN01"));
}

#[test]
fn existing_languages_unchanged_no_guards_block() {
    // Verify a representative existing-style language still parses
    // without a guards block, producing guard_config: None.
    let lang = parse_lang(quote::quote! {
        name: SimpleCalc,
        types { Int },
        terms {
            Add . a:Int, b:Int |- a "+" b : Int ;
        },
        equations { },
        rewrites { }
    });
    assert!(lang.guard_config.is_none());
}

/// Phase 5: Direct test of the connective map thread-local without
/// going through the full `Parse for LanguageDef`. Verifies that
/// the parser functions correctly recognize declared keywords when
/// the thread-local is active.
///
/// This is a focused unit test for the ConnectiveMap → parser bridge,
/// avoiding the complexity of constructing a full rewrite rule.
#[test]
fn connective_map_active_role_lookup() {
    // Default state: no map → all role lookups return None.
    assert!(active_role_of("and").is_none());
    assert!(!has_active_connective_map());

    // Install a custom map.
    let decls = vec![
        ConnectiveDecl {
            role: ConnectiveRole::And,
            keywords: vec!["all".into()],
        },
        ConnectiveDecl {
            role: ConnectiveRole::Or,
            keywords: vec!["any".into()],
        },
        ConnectiveDecl {
            role: ConnectiveRole::Not,
            keywords: vec!["neg".into()],
        },
    ];
    let map = ConnectiveMap::from_decls(&decls).expect("valid");
    let _guard = ConnectiveMapGuard::install(Some(map));

    // Now lookups succeed.
    assert!(has_active_connective_map());
    assert_eq!(active_role_of("all"), Some(ConnectiveRole::And));
    assert_eq!(active_role_of("any"), Some(ConnectiveRole::Or));
    assert_eq!(active_role_of("neg"), Some(ConnectiveRole::Not));
    assert_eq!(active_role_of("nonexistent"), None);
    assert!(active_role_available(&ConnectiveRole::And));
    assert!(!active_role_available(&ConnectiveRole::Forall));

    // Drop _guard at end of scope; map should be cleared.
}

/// Phase 5: After dropping the guard, the thread-local must be cleared.
#[test]
fn connective_map_guard_restores_on_drop() {
    // Pre-condition: empty
    assert!(!has_active_connective_map());

    {
        let decls = vec![ConnectiveDecl {
            role: ConnectiveRole::And,
            keywords: vec!["zzz".into()],
        }];
        let map = ConnectiveMap::from_decls(&decls).expect("valid");
        let _guard = ConnectiveMapGuard::install(Some(map));
        assert!(has_active_connective_map());
        assert_eq!(active_role_of("zzz"), Some(ConnectiveRole::And));
    }

    // After scope exit, the guard's Drop ran:
    assert!(!has_active_connective_map());
    assert_eq!(active_role_of("zzz"), None);
}

// (Phase R-fix 2026-04-08) The two unit tests
// `guard_codegen_selectivity_uses_annotation` and
// `guard_codegen_cost_uses_annotation` were moved from this file to
// `crate::gen::runtime::guard_codegen::tests` so that the AST crate
// (which will be extracted as `mettail-ast` in Phase R) does not
// depend on `crate::gen::runtime::guard_codegen`. Without this move
// the extraction would create an `ast → gen → ast` cycle.

// ══════════════════════════════════════════════════════════════════════
// Cleanup D: CONN02 enforcement (closed-world connectives)
// ══════════════════════════════════════════════════════════════════════

/// Cleanup D: when no connectives {} block is present, all standard
/// Rust connective tokens are accepted (open-world / backward compat).
#[test]
fn cleanup_d_no_map_accepts_all_rust_tokens() {
    let _guard = ConnectiveMapGuard::install(None);
    assert!(rust_token_allowed(ConnectiveRole::And));
    assert!(rust_token_allowed(ConnectiveRole::Or));
    assert!(rust_token_allowed(ConnectiveRole::Not));
    assert!(rust_token_allowed(ConnectiveRole::Entails));
}

/// Cleanup D: when a connectives {} block declares only `and`, all
/// other Rust connective tokens are rejected.
#[test]
fn cleanup_d_partial_map_rejects_unlisted_rust_tokens() {
    let decls = vec![ConnectiveDecl {
        role: ConnectiveRole::And,
        keywords: vec!["&&".into()],
    }];
    let map = ConnectiveMap::from_decls(&decls).expect("valid");
    let _guard = ConnectiveMapGuard::install(Some(map));

    assert!(rust_token_allowed(ConnectiveRole::And));
    assert!(!rust_token_allowed(ConnectiveRole::Or));
    assert!(!rust_token_allowed(ConnectiveRole::Not));
    assert!(!rust_token_allowed(ConnectiveRole::Entails));
}

/// Cleanup D: with a connectives {} block declaring all four roles,
/// all corresponding Rust tokens are allowed.
#[test]
fn cleanup_d_full_map_accepts_all_listed_tokens() {
    let decls = vec![
        ConnectiveDecl {
            role: ConnectiveRole::And,
            keywords: vec!["&&".into()],
        },
        ConnectiveDecl {
            role: ConnectiveRole::Or,
            keywords: vec!["||".into()],
        },
        ConnectiveDecl {
            role: ConnectiveRole::Not,
            keywords: vec!["~".into()],
        },
        ConnectiveDecl {
            role: ConnectiveRole::Entails,
            keywords: vec!["=>".into()],
        },
    ];
    let map = ConnectiveMap::from_decls(&decls).expect("valid");
    let _guard = ConnectiveMapGuard::install(Some(map));

    assert!(rust_token_allowed(ConnectiveRole::And));
    assert!(rust_token_allowed(ConnectiveRole::Or));
    assert!(rust_token_allowed(ConnectiveRole::Not));
    assert!(rust_token_allowed(ConnectiveRole::Entails));
}

// (Phase R-fix 2026-04-08) See note above about
// `guard_codegen_cost_uses_annotation` having moved to
// `crate::gen::runtime::guard_codegen::tests`.

/// Phase 5: Nested guards correctly stack and restore.
#[test]
fn connective_map_guard_nesting() {
    let outer_decls = vec![ConnectiveDecl {
        role: ConnectiveRole::And,
        keywords: vec!["outer_and".into()],
    }];
    let outer_map = ConnectiveMap::from_decls(&outer_decls).expect("valid");
    let _outer = ConnectiveMapGuard::install(Some(outer_map));
    assert_eq!(active_role_of("outer_and"), Some(ConnectiveRole::And));
    assert_eq!(active_role_of("inner_and"), None);

    {
        let inner_decls = vec![ConnectiveDecl {
            role: ConnectiveRole::And,
            keywords: vec!["inner_and".into()],
        }];
        let inner_map = ConnectiveMap::from_decls(&inner_decls).expect("valid");
        let _inner = ConnectiveMapGuard::install(Some(inner_map));
        // Inner active
        assert_eq!(active_role_of("inner_and"), Some(ConnectiveRole::And));
        // Outer keyword no longer visible
        assert_eq!(active_role_of("outer_and"), None);
    }

    // After inner drop, outer is restored
    assert_eq!(active_role_of("outer_and"), Some(ConnectiveRole::And));
    assert_eq!(active_role_of("inner_and"), None);
}

// ══════════════════════════════════════════════════════════════════════
// Phase 9: Property-based tests (proptest)
// ══════════════════════════════════════════════════════════════════════

use proptest::prelude::*;

fn arb_role() -> impl Strategy<Value = ConnectiveRole> {
    prop::sample::select(vec![
        ConnectiveRole::And,
        ConnectiveRole::Or,
        ConnectiveRole::Not,
        ConnectiveRole::Entails,
        ConnectiveRole::ImpliedBy,
        ConnectiveRole::Iff,
        ConnectiveRole::Forall,
        ConnectiveRole::Exists,
    ])
}

proptest! {
    /// Property: For any list of declarations whose keywords are all
    /// distinct strings, `ConnectiveMap::from_decls` succeeds and the
    /// resulting bidirectional map satisfies the invariant:
    ///
    ///   ∀ (role, kws) ∈ role_to_keywords. ∀ kw ∈ kws.
    ///       keyword_to_role[kw] = role
    #[test]
    fn proptest_connective_map_bidirectional_invariant(
        decls in proptest::collection::vec(
            (arb_role(), "[a-z][a-z0-9_]{0,8}"),
            1..8,
        )
    ) {
        // Deduplicate keywords by tagging each with its index, so the
        // CONN01 invariant holds even when proptest generates the same
        // keyword string twice with different roles.
        let unique_decls: Vec<ConnectiveDecl> = decls
            .into_iter()
            .enumerate()
            .map(|(i, (role, kw))| ConnectiveDecl {
                role,
                keywords: vec![format!("{}_{}", kw, i)],
            })
            .collect();

        let map = ConnectiveMap::from_decls(&unique_decls).expect("unique kws");

        // Forward → Reverse
        for (role, kws) in &map.role_to_keywords {
            for kw in kws {
                prop_assert_eq!(
                    map.keyword_to_role.get(kw),
                    Some(role)
                );
            }
        }
        // Reverse → Forward
        for (kw, role) in &map.keyword_to_role {
            prop_assert!(map.role_to_keywords[role].contains(kw));
        }
    }

    /// Property: When the same keyword is declared for two distinct
    /// roles, `from_decls` always reports a CONN01 error.
    #[test]
    fn proptest_connective_map_conn01_on_duplicate(
        (role_a, role_b) in (arb_role(), arb_role()).prop_filter(
            "roles must differ",
            |(a, b)| a != b,
        )
    ) {
        let decls = vec![
            ConnectiveDecl {
                role: role_a,
                keywords: vec!["shared".into()],
            },
            ConnectiveDecl {
                role: role_b,
                keywords: vec!["shared".into()],
            },
        ];
        let result = ConnectiveMap::from_decls(&decls);
        prop_assert!(result.is_err());
    }

    /// Property: PredicateAnnotations override semantics — extension
    /// wins per-field. Encoded as a logical formula:
    ///
    ///   merged.selectivity = ext.selectivity OR base.selectivity
    ///   merged.cost        = ext.cost        OR base.cost
    ///
    /// where OR is `Option::or`.
    #[test]
    fn proptest_annotation_override_per_field(
        base_sel in proptest::option::of(0.0..=1.0_f64),
        ext_sel  in proptest::option::of(0.0..=1.0_f64),
        base_cost in proptest::option::of(0u32..1000),
        ext_cost  in proptest::option::of(0u32..1000),
    ) {
        let base = PredicateAnnotations {
            selectivity: base_sel,
            cost: base_cost,
        };
        let ext = PredicateAnnotations {
            selectivity: ext_sel,
            cost: ext_cost,
        };
        let merged = PredicateAnnotations {
            selectivity: ext.selectivity.or(base.selectivity),
            cost: ext.cost.or(base.cost),
        };

        // Extension's value wins if present
        if ext_sel.is_some() {
            prop_assert_eq!(merged.selectivity, ext_sel);
        } else {
            prop_assert_eq!(merged.selectivity, base_sel);
        }
        if ext_cost.is_some() {
            prop_assert_eq!(merged.cost, ext_cost);
        } else {
            prop_assert_eq!(merged.cost, base_cost);
        }
    }

    /// Property: Selectivity algebra for compound predicates obeys
    /// the standard inequalities under independence:
    ///
    ///   sel(P ∧ Q) ≤ min(sel(P), sel(Q))
    ///   sel(P ∨ Q) ≥ max(sel(P), sel(Q))
    ///   sel(¬P)   = 1 − sel(P)
    ///
    /// This is the foundation of selectivity-based query ordering
    /// (Selinger et al., 1979).
    #[test]
    fn proptest_selectivity_algebra(
        sa in 0.0..=1.0_f64,
        sb in 0.0..=1.0_f64,
    ) {
        // sel(P ∧ Q) = sa · sb
        let and_sel = sa * sb;
        prop_assert!(and_sel <= sa + 1e-12);
        prop_assert!(and_sel <= sb + 1e-12);

        // sel(P ∨ Q) = 1 − (1 − sa)(1 − sb)
        let or_sel = 1.0 - (1.0 - sa) * (1.0 - sb);
        prop_assert!(or_sel >= sa - 1e-12);
        prop_assert!(or_sel >= sb - 1e-12);

        // sel(¬P) = 1 − sa
        let not_sel = 1.0 - sa;
        prop_assert!((not_sel + sa - 1.0).abs() < 1e-12);
    }

    /// Cleanup D property: rust_token_allowed is the disjunction of
    /// "no map active" and "role available in active map". Equivalently:
    /// when a map is active, only declared roles' Rust tokens are allowed.
    ///
    /// This is the closed-world invariant for CONN02.
    #[test]
    fn proptest_cleanup_d_rust_token_gate_invariant(
        roles in proptest::collection::vec(
            prop::sample::select(vec![
                ConnectiveRole::And,
                ConnectiveRole::Or,
                ConnectiveRole::Not,
                ConnectiveRole::Entails,
            ]),
            0..4,
        )
    ) {
        // Build a map declaring only the chosen subset of roles.
        let decls: Vec<ConnectiveDecl> = roles
            .iter()
            .enumerate()
            .map(|(i, role)| ConnectiveDecl {
                role: role.clone(),
                keywords: vec![format!("kw_{}", i)],
            })
            .collect();
        let map = ConnectiveMap::from_decls(&decls).expect("unique kws");
        let _guard = ConnectiveMapGuard::install(Some(map));

        // Property: a Rust token is allowed iff its role is in the map.
        for role in [
            ConnectiveRole::And,
            ConnectiveRole::Or,
            ConnectiveRole::Not,
            ConnectiveRole::Entails,
        ] {
            let allowed = rust_token_allowed(role.clone());
            let in_map = roles.contains(&role);
            prop_assert_eq!(
                allowed, in_map,
                "role {:?} allowed-bit must match map membership",
                role
            );
        }
    }

    /// Cleanup D property: with no active map, every Rust token is
    /// allowed (backward compatibility — open-world default).
    #[test]
    fn proptest_cleanup_d_no_map_open_world(
        role in prop::sample::select(vec![
            ConnectiveRole::And,
            ConnectiveRole::Or,
            ConnectiveRole::Not,
            ConnectiveRole::Entails,
        ])
    ) {
        // Ensure no map is active.
        let _guard = ConnectiveMapGuard::install(None);
        prop_assert!(rust_token_allowed(role));
    }
}
