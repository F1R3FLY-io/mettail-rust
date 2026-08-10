//! Production persistent-root admission: semantic envelope, fallback boundary,
//! and ordinary-stack depth evidence.

use mettail_rholang_codegen::{
    compile_in_rho_matching_ruleset, persistent_root_drive_certificate, reconstruct_language_def,
    GroundTerm, BOUND_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL,
};

const LAMBDA_SOURCE: &str = r#"
    name: Lambda,
    types { Term },
    terms {
        Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term;
        App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term;
    },
    equations {},
    rewrites {
        Beta . |- (App (Lam fun) arg) ~> (eval fun arg);
        AppCongL . | M0 ~> M1 |- (App M0 N) ~> (App M1 N);
        AppCongR . | N0 ~> N1 |- (App M N0) ~> (App M N1);
        LamCong . | S ~> T |- (Lam ^x.S) ~> (Lam ^x.T);
    },
"#;

fn node(label: &str, children: Vec<GroundTerm>) -> GroundTerm {
    GroundTerm::new(label, children)
}

fn identity() -> GroundTerm {
    node(
        LAMBDA_REFLECT_LABEL,
        vec![node(
            BOUND_VAR_REFLECT_LABEL,
            vec![GroundTerm::nullary(PEANO_ZERO_REFLECT_LABEL)],
        )],
    )
}

fn identity_spine(depth: usize) -> GroundTerm {
    let mut term = GroundTerm::nullary("K");
    for _ in 0..depth {
        term = node("App", vec![identity(), term]);
    }
    term
}

#[test]
fn certificate_accepts_the_complete_identity_spine_and_rejects_congruence_work() {
    let def = reconstruct_language_def(LAMBDA_SOURCE).expect("Lambda source reconstructs");
    let ruleset = compile_in_rho_matching_ruleset(&def);

    let chain = identity_spine(8);
    let certificate = persistent_root_drive_certificate(&def, &ruleset, &chain)
        .expect("a root-only identity-beta spine is total under R3");
    assert_eq!(certificate.root_constructor, "App");
    assert_eq!(certificate.rule_label, "Beta");
    assert_eq!(certificate.contractions, 8);

    let nested_work = node("App", vec![identity_spine(1), identity()]);
    assert!(
        persistent_root_drive_certificate(&def, &ruleset, &nested_work).is_none(),
        "a fun-position spine needs congruence and must retain the general driver"
    );
    let non_identity = node(
        "App",
        vec![
            node(LAMBDA_REFLECT_LABEL, vec![GroundTerm::nullary("Body")]),
            GroundTerm::nullary("K"),
        ],
    );
    assert!(
        persistent_root_drive_certificate(&def, &ruleset, &non_identity).is_none(),
        "a non-identity beta redex is outside the shortening proof"
    );
}

#[test]
fn certificate_is_stack_safe_at_depth_20_000() {
    std::thread::Builder::new()
        .name("persistent-root-certificate-20k".to_string())
        .stack_size(256 * 1024)
        .spawn(|| {
            let def = reconstruct_language_def(LAMBDA_SOURCE).expect("Lambda source reconstructs");
            let ruleset = compile_in_rho_matching_ruleset(&def);
            let subject = identity_spine(20_000);
            let certificate = persistent_root_drive_certificate(&def, &ruleset, &subject)
                .expect("the arbitrary-depth identity spine is certified");
            assert_eq!(certificate.contractions, 20_000);
        })
        .expect("the 256 KiB proof thread starts")
        .join()
        .expect("the iterative admission proof and cleanup complete without stack growth");
}
