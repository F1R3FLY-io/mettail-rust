//! Compiled regression for cross-category binder-body reconstruction.

#![cfg(feature = "dovetail-codegen")]
#![allow(non_local_definitions)]

#[path = "definitions/cross_category_binder_inverse_demo.rs"]
mod cross_category_binder_inverse_demo;

use cross_category_binder_inverse_demo::{
    CrossCategoryBinderInverseDemoLanguage, CrossCategoryBinderInverseDemoTerm,
    CrossCategoryBinderInverseDemoTermInner, Proc, Wrapper,
};

#[test]
fn declared_proc_body_survives_wrapper_reconstruction() {
    let binder = mettail_runtime::Binder(mettail_runtime::FreeVar::fresh_named("x"));
    let scope = mettail_runtime::Scope::new(binder, std::sync::Arc::new(Proc::Zero));
    let subject = Proc::Probe(std::sync::Arc::new(Wrapper::Wrap(scope)));
    let wrapped =
        CrossCategoryBinderInverseDemoTerm(CrossCategoryBinderInverseDemoTermInner::Proc(subject));

    let report = CrossCategoryBinderInverseDemoLanguage::dovetail_report_for(&wrapped, 8, 1_024)
        .expect("cross-category binder lowering and reconstruction must complete");

    assert!(
        report.rule_firings.iter().any(|firing| {
            firing.label.as_deref() == Some("CrossCategoryBinderInverseDemo::fold::Proc_Probe")
                && firing.count >= 1
        }),
        "the Probe fold can fire only after reconstructing Wrapper::Wrap with its Proc body: \
         {report:#?}",
    );
    assert!(
        report.terms.iter().any(|term| {
            term.is_root && term.op_display == "CrossCategoryBinderInverseDemo::Proc::Hit"
        }),
        "the reconstructed binder must reach the fold body and reduce to Hit: {report:#?}",
    );
}
