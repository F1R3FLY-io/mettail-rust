use std::any::Any;
use std::sync::Arc;

use mettail_prattail::wpda_runtime::{ActionArg, BinderHandle};

const DEPTH: usize = 20_000;
const STACK_BYTES: usize = 256 * 1024;

fn nested_optional(depth: usize) -> ActionArg {
    let mut arg = ActionArg::UnsetCollectionValue;
    for _ in 0..depth {
        arg = ActionArg::Optional(Some(vec![arg]));
    }
    arg
}

fn optional_depth(arg: &ActionArg) -> usize {
    let mut depth = 0;
    let mut current = arg;
    loop {
        match current {
            ActionArg::Optional(Some(args)) if args.len() == 1 => {
                depth += 1;
                current = &args[0];
            },
            ActionArg::UnsetCollectionValue => return depth,
            other => panic!("unexpected optional-chain node: {other:?}"),
        }
    }
}

#[test]
fn action_arg_clone_preserves_type_erased_arc_identity() {
    let payload = Arc::new(42_u64);
    let erased: Arc<dyn Any + Send + Sync> = payload.clone();
    let cloned = ActionArg::Term { value: erased, type_name: "u64" }
        .clone()
        .into_term_arc::<u64>()
        .expect("cloned term payload");

    assert!(Arc::ptr_eq(&payload, &cloned));
}

#[test]
fn action_arg_consuming_scalar_accessors_move_payloads_out_of_drop_type() {
    let handle = ActionArg::BinderScope(BinderHandle::new(vec!["x".into(), "y".into()], 3))
        .into_binder_scope()
        .expect("binder scope");
    assert_eq!(handle.names, ["x", "y"]);
    assert_eq!(handle.depth, 3);

    let name = ActionArg::Ident { name: "bound".into(), pos: 7 }
        .into_ident_name()
        .expect("identifier");
    assert_eq!(name, "bound");
}

#[test]
fn action_arg_optional_clone_extract_and_drop_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(|| {
            let arg = nested_optional(DEPTH);
            let cloned = arg.clone();
            assert_eq!(optional_depth(&arg), DEPTH);
            assert_eq!(optional_depth(&cloned), DEPTH);
            assert_eq!(format!("{arg:?}"), "Optional { present: true, len: 1 }");

            let mismatch = cloned.clone().try_into_term::<u64>();
            assert!(mismatch.is_err());

            let outer = cloned.into_optional().expect("outer optional variant");
            assert_eq!(optional_depth(&outer.expect("present optional")[0]), DEPTH - 1);

            drop(arg);
        })
        .expect("spawn depth-gate thread")
        .join()
        .expect("action-argument stack-safety gate");
}
