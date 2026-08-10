use dovetail::set_automaton::AutomatonNode;
use mettail_ast::language::LanguageDef;
use mettail_rholang_codegen::{compile_in_rho_matching_ruleset, LAMBDA_REFLECT_LABEL};

const ALPHA_BINDER_RULES: &str = r#"
name: AlphaBinderRules,
options { emit_simulator: false, emit_blockly: false, },
types { Term },
terms {
    Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term ;
    App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term ;
},
equations {},
rewrites {
    BetaOne . |- (App (Lam fun) arg) ~> (eval fun arg) ;
    BetaTwo . |- (App (Lam body) value) ~> (eval body value) ;
    BetaNested . |- (App (Lam (Lam inner)) actual) ~> (eval inner actual) ;
}
"#;

#[test]
fn binder_lowering_shares_alpha_shapes_but_preserves_depth_specificity() {
    let def: LanguageDef = syn::parse_str(ALPHA_BINDER_RULES).expect("binder fixture parses");
    mettail_ast::validation::validate_language(&def).expect("binder fixture validates");
    let ruleset = compile_in_rho_matching_ruleset(&def);
    assert!(
        ruleset.deferred.is_empty(),
        "all three substitution rewrites have binder-aware automaton images: {:?}",
        ruleset.deferred
    );

    let view = ruleset.automaton.view();
    assert_eq!(view.entry_count(), 3);
    assert_eq!(
        view.state_count(),
        5,
        "Var, lambda(Var), App(lambda,Var), lambda(lambda), and the deeper App"
    );
    assert_eq!(
        view.entry_root_state(0),
        view.entry_root_state(1),
        "renaming fun/arg to body/value must share the canonical binder state"
    );
    assert_ne!(
        view.entry_root_state(0),
        view.entry_root_state(2),
        "an additional binder level is a different structural pattern"
    );
    assert_eq!(view.entry_slot_names(0), ["fun", "arg"]);
    assert_eq!(view.entry_slot_names(1), ["body", "value"]);
    assert_eq!(view.entry_slot_names(2), ["inner", "actual"]);

    let alpha_root = view.entry_root_state(0);
    let lambda_state = match view.node(alpha_root) {
        AutomatonNode::App { op, args } => {
            assert_eq!(op, "App");
            assert_eq!(args.len(), 2);
            args[0].state()
        },
        AutomatonNode::Var => panic!("the beta root is an application"),
    };
    match view.node(lambda_state) {
        AutomatonNode::App { op, args } => {
            assert_eq!(op, LAMBDA_REFLECT_LABEL, "binder lowering uses the wire tag");
            assert_eq!(args.len(), 1);
        },
        AutomatonNode::Var => panic!("the beta function child is a reflected binder"),
    }
}
