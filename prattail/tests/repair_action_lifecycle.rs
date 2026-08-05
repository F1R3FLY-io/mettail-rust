use mettail_prattail::recovery::RepairAction;

const DEPTH: usize = 20_000;
const SMALL_STACK_BYTES: usize = 256 * 1024;

#[test]
fn repair_action_lifecycle_and_walkers_are_stack_safe_at_depth_20k() {
    std::thread::Builder::new()
        .name("repair-action-small-stack".to_string())
        .stack_size(SMALL_STACK_BYTES)
        .spawn(|| {
            let mut action = RepairAction::DeleteToken;
            for _ in 0..DEPTH {
                action = RepairAction::Composite { steps: vec![action] };
            }

            let cloned = action.clone();
            assert_eq!(action, cloned);
            assert_eq!(action.to_string(), "delete token");
            assert_eq!(action.describe(&[]), "delete unexpected token");
            assert_eq!(action.edit_cost().0, 1);
            let debug = format!("{action:?}");
            assert!(debug.starts_with("Composite { steps: [Composite"));
            assert!(debug.contains("DeleteToken"));

            drop(cloned);
            drop(action);
        })
        .expect("spawn repair-action small-stack gate")
        .join()
        .expect("repair-action small-stack gate panicked");
}

#[test]
fn repair_action_formatting_preserves_compact_contracts() {
    let action = RepairAction::Composite {
        steps: vec![
            RepairAction::InsertToken { token: 2 },
            RepairAction::CategorySwitch {
                from_category: "Expr".to_string(),
                to_category: "Name".to_string(),
            },
        ],
    };
    assert_eq!(action.to_string(), "insert token 2, switch Expr → Name");
    assert_eq!(
        format!("{action:?}"),
        "Composite { steps: [InsertToken { token: 2 }, CategorySwitch { from_category: \"Expr\", to_category: \"Name\" }] }"
    );

    let empty_nested = RepairAction::Composite {
        steps: vec![RepairAction::Composite { steps: vec![] }, RepairAction::DeleteToken],
    };
    assert_eq!(empty_nested.to_string(), ", delete token");
    assert_eq!(empty_nested.describe(&[]), ", delete unexpected token");
}
