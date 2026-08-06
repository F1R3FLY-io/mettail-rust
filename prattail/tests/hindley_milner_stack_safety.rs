use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use mettail_prattail::hindley_milner::{infer, unify, HmEnv, HmTerm, HmType, Substitution};

const DEPTH: usize = 20_000;
const STACK_BYTES: usize = 256 * 1024;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[allow(dead_code)]
enum TypeOracle {
    Var(String),
    Mono(String),
    Arrow(Box<TypeOracle>, Box<TypeOracle>),
    Forall(Vec<String>, Box<TypeOracle>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(dead_code)]
enum TermOracle {
    Var(String),
    Abs {
        param: String,
        body: Box<TermOracle>,
    },
    App {
        f: Box<TermOracle>,
        arg: Box<TermOracle>,
    },
    Let {
        name: String,
        value: Box<TermOracle>,
        body: Box<TermOracle>,
    },
    LitInt(i64),
    LitBool(bool),
    LitStr(String),
}

fn hash(value: &impl Hash) -> u64 {
    let mut state = DefaultHasher::new();
    value.hash(&mut state);
    state.finish()
}

fn nested_arrow(depth: usize) -> HmType {
    let mut ty = HmType::Var("free".into());
    for _ in 0..depth {
        ty = HmType::Arrow(Box::new(HmType::Mono("Int".into())), Box::new(ty));
    }
    ty
}

fn right_arrow_depth(ty: &HmType) -> usize {
    let mut depth = 0;
    let mut current = ty;
    while let HmType::Arrow(_, codomain) = current {
        depth += 1;
        current = codomain;
    }
    depth
}

fn nested_abs(depth: usize) -> HmTerm {
    let mut term = HmTerm::Var(format!("x{}", depth - 1));
    for index in (0..depth).rev() {
        term = HmTerm::Abs {
            param: format!("x{index}"),
            body: Box::new(term),
        };
    }
    term
}

fn abstraction_depth(term: &HmTerm) -> usize {
    let mut depth = 0;
    let mut current = term;
    loop {
        match current {
            HmTerm::Abs { body, .. } => {
                depth += 1;
                current = body;
            },
            HmTerm::Var(_) => return depth,
            other => panic!("unexpected HM term node: {other:?}"),
        }
    }
}

#[test]
fn hindley_milner_lifecycle_matches_recursive_derive_oracles() {
    let ty = HmType::Forall(
        vec!["a".into()],
        Box::new(HmType::Arrow(
            Box::new(HmType::Var("a".into())),
            Box::new(HmType::Mono("Int".into())),
        )),
    );
    let ty_oracle = TypeOracle::Forall(
        vec!["a".into()],
        Box::new(TypeOracle::Arrow(
            Box::new(TypeOracle::Var("a".into())),
            Box::new(TypeOracle::Mono("Int".into())),
        )),
    );
    assert_eq!(format!("{ty:?}"), format!("{ty_oracle:?}"));
    assert_eq!(format!("{:?}", ty.clone()), format!("{ty_oracle:?}"));
    assert_eq!(hash(&ty), hash(&ty_oracle));
    assert_eq!(ty.to_string(), "∀a. a → Int");

    let term = HmTerm::Let {
        name: "id".into(),
        value: Box::new(HmTerm::Abs {
            param: "x".into(),
            body: Box::new(HmTerm::Var("x".into())),
        }),
        body: Box::new(HmTerm::App {
            f: Box::new(HmTerm::Var("id".into())),
            arg: Box::new(HmTerm::LitInt(1)),
        }),
    };
    let term_oracle = TermOracle::Let {
        name: "id".into(),
        value: Box::new(TermOracle::Abs {
            param: "x".into(),
            body: Box::new(TermOracle::Var("x".into())),
        }),
        body: Box::new(TermOracle::App {
            f: Box::new(TermOracle::Var("id".into())),
            arg: Box::new(TermOracle::LitInt(1)),
        }),
    };
    assert_eq!(format!("{term:?}"), format!("{term_oracle:?}"));
    assert_eq!(term, term.clone());
}

#[test]
fn hindley_milner_types_and_terms_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(|| {
            let ty = nested_arrow(DEPTH);
            let cloned_ty = ty.clone();
            assert_eq!(ty, cloned_ty);
            assert_eq!(right_arrow_depth(&cloned_ty), DEPTH);
            assert_eq!(ty.free_type_vars(), vec!["free"]);
            assert!(format!("{ty:?}").starts_with("Arrow(Mono(\"Int\"), Arrow("));
            assert!(ty.to_string().starts_with("Int → Int → "));
            let _ = hash(&ty);

            let mut substitution = Substitution::empty();
            substitution.insert("free".into(), HmType::Mono("Bool".into()));
            let applied = substitution.apply(&ty);
            assert!(applied.to_string().ends_with("Bool"));
            let unified = unify(&ty, &cloned_ty).expect("identical deep arrows unify");
            assert_eq!(unified.apply(&HmType::Var("z".into())), HmType::Var("z".into()));

            let term = nested_abs(DEPTH);
            let cloned_term = term.clone();
            assert_eq!(term, cloned_term);
            assert_eq!(abstraction_depth(&cloned_term), DEPTH);
            assert!(format!("{term:?}").starts_with("Abs { param: \"x0\", body: Abs {"));

            let (_, inferred) = infer(&HmEnv::new(), &term).expect("deep lambda infers");
            assert_eq!(right_arrow_depth(&inferred), DEPTH);

            drop(inferred);
            drop(cloned_term);
            drop(term);
            drop(applied);
            drop(cloned_ty);
            drop(ty);
        })
        .expect("spawn HM depth-gate thread")
        .join()
        .expect("HM stack-safety gate");
}
