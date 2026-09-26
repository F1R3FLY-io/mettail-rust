use super::*;
use crate::binding_power::MixfixPart;
use std::cell::RefCell;

fn binary(label: &str, terminal: &str, left_bp: u8) -> InfixOperator {
    InfixOperator {
        terminal: terminal.into(),
        category: "Pattern".into(),
        result_category: "Pattern".into(),
        left_bp,
        right_bp: left_bp + 1,
        label: label.into(),
        is_cross_category: false,
        is_postfix: false,
        is_mixfix: false,
        mixfix_parts: vec![],
        nullary_literals: vec![],
    }
}

#[test]
fn original_missing_literal_query_is_none_but_binary_some_keeps_every_field() {
    let table = BindingPowerTable { operators: vec![binary("PAlt", "|", 2)] };
    let labels = HashMap::from([(("Pattern".into(), "PAlt".into()), (3, 4))]);
    let absent = query(&table, "Pattern", &labels, &HashMap::new());
    assert!(absent.disjointness.is_empty());
    assert!(absent.arms.is_empty());
    assert_eq!(absent.lookup(3, 4), None);
    let present = query(&table, "Pattern", &labels, &HashMap::from([("Pattern".into(), 5)]));
    assert_eq!(
        present.lookup(3, 4),
        Some(BorrowedIterAbsorbSpec {
            left_bp: 2,
            right_bp: 3,
            assoc_right: false,
            is_mixfix: false,
            op_cat_src_idx: 3,
            op_rule_idx: 4,
            atom_cat_src_idx: 3,
            atom_lit_rule_idx: 5,
            trigger: "",
            sep: "",
        })
    );
}

#[test]
fn terminal_disjointness_and_bp_conflict_are_separate_original_scans() {
    let mut table = BindingPowerTable {
        operators: vec![binary("First", "|", 2), binary("Second", "|", 4)],
    };
    let labels = HashMap::from([
        (("Pattern".into(), "First".into()), (0, 0)),
        (("Pattern".into(), "Second".into()), (0, 1)),
    ]);
    let literals = HashMap::from([("Pattern".into(), 2)]);
    let distinct_bp = query(&table, "Pattern", &labels, &literals);
    assert_eq!(
        distinct_bp
            .disjointness
            .iter()
            .map(|(op, clash)| (op.label.as_str(), clash.label.as_str()))
            .collect::<Vec<_>>(),
        vec![("First", "Second"), ("Second", "First")]
    );
    assert_eq!(distinct_bp.arms.len(), 2, "diagnostics do not replace the arm scan");
    table.operators[1].left_bp = 2;
    let same_bp = query(&table, "Pattern", &labels, &literals);
    assert_eq!(same_bp.disjointness.len(), 2);
    assert!(same_bp.arms.is_empty(), "both original pointer-distinct conflicts refuse arms");
}

#[test]
fn source_order_first_match_and_mixfix_terminal_borrows_are_retained() {
    let mut ternary = binary("Ternary", "?", 6);
    ternary.is_mixfix = true;
    ternary.mixfix_parts = [vec![":".into()], vec![]]
        .into_iter()
        .map(|following_terminals| MixfixPart {
            operand_category: "Pattern".into(),
            param_name: "operand".into(),
            preceding_terminals: vec![],
            following_terminals,
            repetition: None,
            capture_kind: None,
        })
        .collect();
    let table = BindingPowerTable {
        operators: vec![ternary, binary("Binary", "|", 2)],
    };
    let labels = HashMap::from([
        (("Pattern".into(), "Ternary".into()), (0, 0)),
        (("Pattern".into(), "Binary".into()), (0, 0)),
    ]);
    let result = query(&table, "Pattern", &labels, &HashMap::from([("Pattern".into(), 1)]));
    assert_eq!(result.arms.len(), 2);
    let first = result.lookup(0, 0).expect("first emitted match arm");
    assert!(first.is_mixfix);
    assert_eq!((first.trigger, first.sep), ("?", ":"));
    assert_eq!(first.trigger.as_ptr(), table.operators[0].terminal.as_ptr());
    assert_eq!(
        first.sep.as_ptr(),
        table.operators[0].mixfix_parts[0].following_terminals[0].as_ptr()
    );
}

#[test]
fn native_gate_skips_label_and_label_error_stops_later_declarations() {
    let trace = RefCell::new(Vec::new());
    let declarations = [("Pattern", None), ("Nat", Some("NumLit")), ("Later", Some("Lit"))];
    let result = try_literal_rule_indices(
        &declarations,
        &HashMap::new(),
        |(name, _)| {
            trace.borrow_mut().push((*name, "name"));
            (*name).into()
        },
        |(name, native)| {
            trace.borrow_mut().push((*name, "native"));
            *native
        },
        |label| {
            trace.borrow_mut().push((label, "label"));
            Err::<String, _>("unavailable")
        },
    );
    assert_eq!(result, Err("unavailable"));
    assert_eq!(
        *trace.borrow(),
        vec![
            ("Pattern", "name"),
            ("Pattern", "native"),
            ("Nat", "name"),
            ("Nat", "native"),
            ("NumLit", "label"),
        ]
    );
}
