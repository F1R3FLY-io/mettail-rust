//! **D10 — the GSLT omnibus's SYNCHRONOUS π `Comm` is REALIZED by the Rho backend.**
//!
//! `languages/src/pi.rs` proves the paper's verbatim `Comm`
//! (`omnibus.tex:1988-1989`) FIRES on the host reducer. That is only half of
//! closing D10. The modality generator's realization fence (the design's
//! §18.4: *"never generate a modality from a rule that is not the rule that
//! fires"*) reads the **backend lowering disposition**, not the declaration —
//! so a rule that fires on the host but lowers to
//! [`RhoNetLoweredRule::Unsupported`] in Rho is still the trap D10 is about,
//! merely moved one layer down. Before the generalization that is exactly what
//! happened:
//!
//! ```text
//! rule:rewrite:0:Comm      -> Unsupported     ← the paper's own clause
//! rule:rewrite:1:CommAsync -> CommRewrite     ← the workaround
//! comm injection sites      = ["CommAsync"]
//! ```
//!
//! This file pins the fixed state against the REAL conformance spec (it reads
//! `languages/src/pi.rs` itself, so a drift in the spec is a failure
//! here rather than a stale copy): **both** communication rules lower to
//! `CommRewrite`, and **both** surface a Comm σ-injection site — the paper's
//! `Comm` first.
//!
//! The companion classifier/receiver/injection-site unit tests live beside the
//! code in `rholang-codegen/src/rho_net_lower.rs`
//! (`synchronous_pi_comm_is_a_comm_shape_with_a_two_element_reduct`,
//! `synchronous_comm_receiver_carries_one_slot_per_reduct_element`,
//! `synchronous_comm_injection_site_names_its_reduct_slots`,
//! `an_unconsumed_abstraction_scope_is_not_a_comm_shape`).

use mettail_ast::language::LanguageDef;
use mettail_rholang_codegen::{
    lower_language_def, reconstruct_language_def, rho_net_comm_injection_sites, RhoNetLoweredRule,
    RhoNetProgram,
};

/// Extract the verbatim `language! { … }` body from a source file by BRACE
/// MATCHING from the invocation's opening brace.
///
/// This is `a_s5c_production_language_gates::extract_language_body` with the
/// closing brace found by BRACE MATCHING rather than by `rfind('}')`. The
/// production helper assumes the `language!` invocation is the last item in its
/// file; that held for `omnibus_pi.rs` only because nothing followed the test
/// suite, and it holds for `languages/src/pi.rs` today, but brace matching does
/// not depend on it at all. Anchoring on a line-leading `language! {` also skips
/// the module doc-comment's prose mentions of `language!`.
fn extract_language_body(source: &str) -> &str {
    let macro_at = source
        .find("\nlanguage! {")
        .expect("the conformance spec must invoke language! at the start of a line")
        + 1;
    let open = source[macro_at..]
        .find('{')
        .map(|offset| macro_at + offset)
        .expect("the language! invocation must open a brace");
    let mut depth = 0usize;
    let mut close = None;
    for (index, byte) in source.as_bytes().iter().enumerate().skip(open) {
        match byte {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    close = Some(index);
                    break;
                }
            },
            _ => {},
        }
    }
    &source[open + 1..close.expect("the language! invocation must close its brace")]
}

/// The omnibus `Pi` conformance spec, reconstructed through the SAME
/// `reconstruct_language_def` path the production installer and the generated
/// `rho_net_program()` accessor use.
fn pi_def() -> LanguageDef {
    let body = extract_language_body(include_str!("../../languages/src/pi.rs"));
    reconstruct_language_def(body).expect("the omnibus Pi body must reconstruct")
}

/// The lowered family name of each rewrite rule, keyed by the rewrite's name.
fn rewrite_families(def: &LanguageDef) -> Vec<(String, String)> {
    let lowering = lower_language_def(def);
    let program = RhoNetProgram::from_language_def(def, &lowering);
    let lowered = program.lower_to_par(def, &lowering);
    lowered
        .rules()
        .iter()
        .filter_map(|rule| {
            let id = rule.rule_id().to_string();
            // Rewrite rule ids are `rule:rewrite:<index>:<name>`.
            let name = id.strip_prefix("rule:rewrite:")?.split_once(':')?.1.to_string();
            let family = match rule {
                RhoNetLoweredRule::CommRewrite { .. } => "CommRewrite",
                RhoNetLoweredRule::StructuralAcRewrite { .. } => "StructuralAcRewrite",
                RhoNetLoweredRule::AcRewrite { .. } => "AcRewrite",
                RhoNetLoweredRule::BaseRewrite { .. } => "BaseRewrite",
                RhoNetLoweredRule::Unsupported { .. } => "Unsupported",
                RhoNetLoweredRule::CongruenceExemptRewrite { .. } => "CongruenceExemptRewrite",
                _ => "other",
            };
            Some((name, family.to_string()))
        })
        .collect()
}

/// ★★ The paper's SYNCHRONOUS `Comm` — whose reduct is the TWO-element bag
/// `{(eval ^x.p m), q, ...rest}` — lowers to a `CommRewrite`, no longer
/// `Unsupported`. This is the property the modality generator's realization
/// fence reads.
#[test]
fn omnibus_pi_synchronous_comm_lowers_to_a_comm_rewrite() {
    let families = rewrite_families(&pi_def());
    let comm = families
        .iter()
        .find(|(name, _)| name == "Comm")
        .unwrap_or_else(|| panic!("the omnibus Pi spec must declare `Comm`; got {families:?}"));
    assert_eq!(
        comm.1, "CommRewrite",
        "the paper's synchronous Comm must be REALIZED by the Rho backend, not fail closed; \
         got {families:?}"
    );
}

/// The ASYNCHRONOUS `CommAsync` extra still lowers to a `CommRewrite` — the
/// arity generalization is conservative, not a replacement.
#[test]
fn omnibus_pi_asynchronous_comm_still_lowers_to_a_comm_rewrite() {
    let families = rewrite_families(&pi_def());
    let comm_async = families
        .iter()
        .find(|(name, _)| name == "CommAsync")
        .unwrap_or_else(|| panic!("the omnibus Pi spec must declare `CommAsync`; got {families:?}"));
    assert_eq!(comm_async.1, "CommRewrite", "got {families:?}");
}

/// Both communication rules surface a Comm σ-injection site, the paper's own
/// clause FIRST (declaration order) — so an injection for `Comm` targets a
/// receiver that is really installed.
#[test]
fn omnibus_pi_surfaces_a_comm_injection_site_for_the_verbatim_rule() {
    let def = pi_def();
    let sites = rho_net_comm_injection_sites(&def);
    let labels: Vec<&str> = sites.iter().map(|site| site.rule_label.as_str()).collect();
    assert_eq!(
        labels,
        vec!["Comm", "CommAsync"],
        "both π communication rules must be executable injection sites"
    );

    let comm = &sites[0];
    assert_eq!(comm.op, "PPar");
    assert_eq!(comm.nonlinear_var, "n", "the shared channel is `n`");
    assert_eq!(comm.rest_var, "rest");
    assert_eq!(comm.scope_var, "p", "`^x.p` contributes its body variable");
    assert_eq!(comm.arg_var, "m");
    assert_eq!(comm.element_constructors, vec!["PIn".to_string(), "POut".to_string()]);
    // ★ The D10 property at the injection seam: TWO reduct slots — the ONE
    // host-computed substitution (`None`) and the σ-delivered output
    // continuation `q`.
    assert_eq!(comm.reduct_slots, vec![None, Some("q".to_string())]);

    let comm_async = &sites[1];
    assert_eq!(comm_async.element_constructors, vec![
        "PIn".to_string(),
        "POutAsync".to_string()
    ]);
    assert_eq!(
        comm_async.reduct_slots,
        vec![None],
        "the asynchronous reduct is the single host-computed substitution"
    );
}
