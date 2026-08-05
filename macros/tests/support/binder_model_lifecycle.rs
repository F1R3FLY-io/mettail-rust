use super::{first_param_cat_from_positions, ActionArgKind, BinderPosition};

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

#[test]
fn binder_codegen_models_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .name("binder-model-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let mut position = BinderPosition::ParamParse {
                cat: "Expr".to_string(),
                collection: None,
            };
            let mut action = ActionArgKind::Term("Expr".to_string());
            for depth in 0..DEPTH {
                if depth % 2 == 0 {
                    position = BinderPosition::OptionalGroup {
                        positions: vec![position],
                        group_idx: 0,
                        first_token_set: vec!["x".to_string()],
                    };
                } else {
                    position = BinderPosition::BinderListLoop {
                        separator: ",".to_string(),
                        close: ")".to_string(),
                        inner_positions: vec![position],
                        collection_param_cat: None,
                        allow_empty: true,
                        allow_multi: true,
                        slot_idx: 0,
                    };
                }
                action = ActionArgKind::Optional(vec![action]);
            }

            assert_eq!(
                first_param_cat_from_positions(std::slice::from_ref(&position)),
                Some("Expr")
            );
            let position_clone = position.clone();
            let action_clone = action.clone();
            assert_eq!(format!("{position:?}"), format!("{position_clone:?}"));
            assert_eq!(format!("{action:?}"), format!("{action_clone:?}"));

            drop(position_clone);
            drop(position);
            drop(action_clone);
            drop(action);
        })
        .expect("spawn binder-model small-stack gate")
        .join()
        .expect("binder-model small-stack gate panicked");
}

#[test]
fn binder_codegen_model_debug_preserves_compact_contracts() {
    let position = BinderPosition::OptionalGroup {
        positions: vec![BinderPosition::BinderListLoop {
            separator: ",".to_string(),
            close: ")".to_string(),
            inner_positions: vec![BinderPosition::BinderIdent],
            collection_param_cat: Some("Name".to_string()),
            allow_empty: false,
            allow_multi: true,
            slot_idx: 2,
        }],
        group_idx: 3,
        first_token_set: vec!["new".to_string()],
    };
    assert_eq!(
        format!("{position:?}"),
        "OptionalGroup { positions: [BinderListLoop { separator: \",\", close: \")\", inner_positions: [BinderIdent], collection_param_cat: Some(\"Name\"), allow_empty: false, allow_multi: true, slot_idx: 2 }], group_idx: 3, first_token_set: [\"new\"] }"
    );

    let action = ActionArgKind::Optional(vec![
        ActionArgKind::TokenText { param_name: "name".to_string() },
        ActionArgKind::Optional(vec![ActionArgKind::Term("Expr".to_string())]),
    ]);
    assert_eq!(
        format!("{action:?}"),
        "Optional([TokenText { param_name: \"name\" }, Optional([Term(\"Expr\")])])"
    );
}
