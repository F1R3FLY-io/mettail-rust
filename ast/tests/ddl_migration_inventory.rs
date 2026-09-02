use mettail_ast::ddl_migration_inventory::{discover_language_declarations, DeclarationKind};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("ast crate has a workspace parent")
        .to_path_buf()
}

#[test]
fn live_inventory_is_total_unique_and_partitions_the_rholang_seed() {
    let inventory = discover_language_declarations(&workspace_root())
        .expect("the live language declaration inventory must be total");
    let keys = inventory
        .iter()
        .map(|declaration| declaration.source_key.as_str())
        .collect::<BTreeSet<_>>();
    let artifact_paths = inventory
        .iter()
        .map(|declaration| declaration.ddl_artifact_path())
        .collect::<BTreeSet<_>>();
    assert_eq!(keys.len(), inventory.len(), "source keys must be injective");
    assert_eq!(
        artifact_paths.len(),
        inventory.len(),
        "derived DDL artifact paths must be injective",
    );

    let rholang = inventory
        .iter()
        .filter(|declaration| declaration.is_rholang_seed())
        .collect::<Vec<_>>();
    assert_eq!(rholang.len(), 1, "there must be exactly one authoritative Rholang seed");

    let guests = inventory
        .iter()
        .filter(|declaration| !declaration.is_rholang_seed())
        .collect::<Vec<_>>();
    assert_eq!(
        guests.len() + rholang.len(),
        inventory.len(),
        "every declaration must belong to exactly one bootstrap partition",
    );
    assert!(
        guests.iter().any(|declaration| declaration.parse_only),
        "syntax-only grammars must remain visible in the migration corpus",
    );
    assert!(
        inventory
            .iter()
            .any(|declaration| declaration.kind == DeclarationKind::Fragment),
        "reusable language fragments must remain visible in the migration corpus",
    );
}
