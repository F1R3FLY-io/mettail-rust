//! FLT Phase 3 Track A: two production languages co-installed on one RSpace.
//!
//! Lambda and Ambient are lowered with symmetric [`CoInstallManifest`]s and their
//! generated programs are installed together.  Every assertion below executes the
//! combined network once; no host reducer or per-language replay substitutes for the
//! generated `^float`/`^drive`/`^subst` machines.  The cases cover root re-entry,
//! structural descent, foreign opacity under substitution/float, disjoint ledgers,
//! wrong-driver rejection, binder crossing, fuel ownership, and the fingerprint-less
//! empty-soup identity.
#![cfg(all(feature = "lambda-runtime", feature = "ambient-runtime"))]

use mettail_languages::ambient::AmbientLanguage;
use mettail_languages::lambda::LambdaLanguage;
use mettail_rholang_codegen::{
    ac_soup_channel, ground_marker_tag_par, is_marked_object_label, lower_language_def,
    par_carries_ground_marker, reconstruct_language_def, reflect_ground_term_par,
    reflected_tag_string, rho_net_drive_call_par_with_fuel, rho_net_drive_float_call_par_with_fuel,
    CoInstallManifest, CollectionType, GroundTerm, NativeShiftSpec, RhoNetProgram,
    BOUND_VAR_REFLECT_LABEL, FREE_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
    PEANO_SUCC_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL,
};
use mettail_rholang_runtime::{
    native_shift_definitions_for,
    run_installed_program_with_call_definitions_and_read_observation_sets,
    DriveObservationChannels, DriveObservationSet,
};
use mettail_runtime::{Language, RuntimeObservationValue};
use models::rhoapi::Par;
use models::rust::rholang::implicits::GPrivateBuilder;
use models::rust::utils::{new_elist_par, new_gstring_par, new_send_par};

const FUEL: i64 = 16;

struct CoInstalled {
    program: Par,
    lambda_fp: String,
    ambient_fp: String,
    shift_specs: Vec<NativeShiftSpec>,
}

fn language_def(language: &dyn Language) -> mettail_ast::language::LanguageDef {
    reconstruct_language_def(
        language
            .metadata()
            .definition_source()
            .expect("a generated production language exposes its definition"),
    )
    .expect("the production definition reconstructs")
}

fn coinstalled() -> CoInstalled {
    let lambda = language_def(&LambdaLanguage);
    let ambient = language_def(&AmbientLanguage);
    let lambda_lowering = lower_language_def(&lambda);
    let ambient_lowering = lower_language_def(&ambient);
    let lambda_program = RhoNetProgram::from_language_def(&lambda, &lambda_lowering);
    let ambient_plan = RhoNetProgram::from_language_def(&ambient, &ambient_lowering);
    let lambda_manifest =
        CoInstallManifest::from_definitions(&lambda, &[&ambient]).expect("disjoint fingerprints");
    let ambient_manifest =
        CoInstallManifest::from_definitions(&ambient, &[&lambda]).expect("disjoint fingerprints");
    let shift_specs = vec![
        NativeShiftSpec::for_language_with_coinstall_manifest(
            &lambda,
            lambda_manifest.self_fingerprint(),
            &lambda_manifest,
        )
        .expect("Lambda native shift domain agrees with its manifest"),
        NativeShiftSpec::for_language_with_coinstall_manifest(
            &ambient,
            ambient_manifest.self_fingerprint(),
            &ambient_manifest,
        )
        .expect("Ambient native shift domain agrees with its manifest"),
    ];
    let lambda_lowered = lambda_program
        .lower_to_par_with_coinstall_manifest(&lambda, &lambda_lowering, &lambda_manifest)
        .expect("Lambda manifest owns Lambda");
    let ambient_lowered = ambient_plan
        .lower_to_par_with_coinstall_manifest(&ambient, &ambient_lowering, &ambient_manifest)
        .expect("Ambient manifest owns Ambient");
    let lambda_fp = lambda_lowered.language_fingerprint.clone();
    let ambient_fp = ambient_lowered.language_fingerprint.clone();
    let lambda_program = lambda_lowered
        .installed_program_par()
        .expect("Lambda is fully installable");
    let ambient_program = ambient_lowered
        .installed_program_par()
        .expect("Ambient is fully installable");
    let program = lambda_program.append(ambient_program);
    CoInstalled {
        program,
        lambda_fp,
        ambient_fp,
        shift_specs,
    }
}

fn g_node(label: &str, children: Vec<GroundTerm>) -> GroundTerm {
    GroundTerm::new(label, children)
}

fn g_bound(depth: usize) -> GroundTerm {
    let mut peano = GroundTerm::nullary(PEANO_ZERO_REFLECT_LABEL);
    for _ in 0..depth {
        peano = g_node(PEANO_SUCC_REFLECT_LABEL, vec![peano]);
    }
    g_node(BOUND_VAR_REFLECT_LABEL, vec![peano])
}

fn g_lambda(body: GroundTerm) -> GroundTerm {
    g_node(LAMBDA_REFLECT_LABEL, vec![body])
}

fn g_id() -> GroundTerm {
    g_lambda(g_bound(0))
}

fn g_k() -> GroundTerm {
    g_lambda(g_lambda(g_bound(1)))
}

fn g_app(fun: GroundTerm, arg: GroundTerm) -> GroundTerm {
    g_node("App", vec![fun, arg])
}

fn g_free(name: &str) -> GroundTerm {
    g_node(FREE_VAR_REFLECT_LABEL, vec![GroundTerm::nullary(name)])
}

fn g_zero() -> GroundTerm {
    GroundTerm::nullary("PZero")
}

fn g_name(name: &str) -> GroundTerm {
    g_free(name)
}

fn g_bag(elements: Vec<GroundTerm>) -> GroundTerm {
    GroundTerm::collection(CollectionType::HashBag, "PPar", elements)
}

fn g_ambient(name: GroundTerm, body: GroundTerm) -> GroundTerm {
    g_node("PAmb", vec![name, body])
}

fn g_open(name: GroundTerm, continuation: GroundTerm) -> GroundTerm {
    g_node("POpen", vec![name, continuation])
}

fn g_open_redex() -> GroundTerm {
    let name = g_name("n");
    g_bag(vec![g_open(name.clone(), g_zero()), g_ambient(name, g_bag(vec![g_zero()]))])
}

fn mixed_tagged(fingerprint: &str, label: &str, children: Vec<Par>) -> Par {
    let mut items = Vec::with_capacity(children.len() + 2);
    items.push(GPrivateBuilder::new_par_from_string(reflected_tag_string(fingerprint, label)));
    if is_marked_object_label(label) {
        let ground = match label {
            BOUND_VAR_REFLECT_LABEL => false,
            FREE_VAR_REFLECT_LABEL => true,
            _ => children
                .iter()
                .all(|child| par_carries_ground_marker(child, fingerprint)),
        };
        items.push(ground_marker_tag_par(fingerprint, ground));
    }
    items.extend(children);
    new_elist_par(items, Vec::new(), false, None, Vec::new(), false)
}

fn mixed_bag(fingerprint: &str, elements: Vec<Par>) -> Par {
    let channel = ac_soup_channel(fingerprint, "PPar");
    elements.into_iter().fold(Par::default(), |bag, element| {
        bag.append(new_send_par(
            new_gstring_par(channel.clone(), Vec::new(), false),
            vec![element],
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        ))
    })
}

fn oterm(label: &str, children: Vec<RuntimeObservationValue>) -> RuntimeObservationValue {
    RuntimeObservationValue::Term { constructor: label.to_string(), children }
}

fn onullary(label: &str) -> RuntimeObservationValue {
    oterm(label, Vec::new())
}

fn opeano(depth: usize) -> RuntimeObservationValue {
    let mut peano = onullary(PEANO_ZERO_REFLECT_LABEL);
    for _ in 0..depth {
        peano = oterm(PEANO_SUCC_REFLECT_LABEL, vec![peano]);
    }
    peano
}

fn obound(depth: usize) -> RuntimeObservationValue {
    oterm(BOUND_VAR_REFLECT_LABEL, vec![opeano(depth)])
}

fn olambda(body: RuntimeObservationValue) -> RuntimeObservationValue {
    oterm(LAMBDA_REFLECT_LABEL, vec![body])
}

fn ok() -> RuntimeObservationValue {
    olambda(olambda(obound(1)))
}

fn ofree(name: &str) -> RuntimeObservationValue {
    oterm(FREE_VAR_REFLECT_LABEL, vec![onullary(name)])
}

fn oapp(fun: RuntimeObservationValue, arg: RuntimeObservationValue) -> RuntimeObservationValue {
    oterm("App", vec![fun, arg])
}

fn oambient(
    name: RuntimeObservationValue,
    body: RuntimeObservationValue,
) -> RuntimeObservationValue {
    oterm("PAmb", vec![name, body])
}

fn obag(elements: Vec<RuntimeObservationValue>) -> RuntimeObservationValue {
    let mut counts = std::collections::BTreeMap::new();
    for element in elements {
        *counts.entry(element).or_insert(0usize) += 1;
    }
    RuntimeObservationValue::Bag(counts.into_iter().collect())
}

async fn run(
    installed: &CoInstalled,
    call: Par,
    out: &str,
) -> (DriveObservationSet, DriveObservationSet) {
    mettail_runtime::clear_var_cache();
    let channels = [
        DriveObservationChannels::for_fingerprint(&installed.lambda_fp, out),
        DriveObservationChannels::for_fingerprint(&installed.ambient_fp, out),
    ];
    let definitions =
        native_shift_definitions_for(&installed.shift_specs).expect("disjoint native shift band");
    let sets = run_installed_program_with_call_definitions_and_read_observation_sets(
        &installed.program,
        &call,
        definitions,
        &channels,
    )
    .await
    .expect("the co-installed network reaches a resting state");
    let [lambda, ambient]: [DriveObservationSet; 2] = sets
        .try_into()
        .expect("two requested channel sets yield two observations");
    (lambda, ambient)
}

fn assert_green(set: &DriveObservationSet) {
    assert!(set.err_data.is_empty(), "no typed driver error: {:?}", set.err_data);
    assert!(set.fuel_data.is_empty(), "no fuel exhaustion: {:?}", set.fuel_data);
}

#[tokio::test]
async fn phase3_two_language_coinstall_has_complete_separated_operational_behavior() {
    let installed = coinstalled();

    // 1. A-only: Lambda reduces under its own driver and ledger.
    let lambda_subject = reflect_ground_term_par(&g_app(g_id(), g_k()), &installed.lambda_fp);
    let (lambda, ambient) = run(
        &installed,
        rho_net_drive_call_par_with_fuel(&installed.lambda_fp, lambda_subject, FUEL, "OUT-A"),
        "OUT-A",
    )
    .await;
    assert_eq!(lambda.out_values, vec![ok()]);
    assert_eq!(lambda.fired_labels().expect("Lambda ledger"), vec!["Beta"]);
    assert!(ambient.fired_data.is_empty());
    assert_green(&lambda);
    assert_green(&ambient);

    // 2. B-only: Ambient reduces under its own float/drive network.
    let ambient_subject = reflect_ground_term_par(&g_open_redex(), &installed.ambient_fp);
    let (lambda, ambient) = run(
        &installed,
        rho_net_drive_float_call_par_with_fuel(
            &installed.ambient_fp,
            ambient_subject,
            FUEL,
            "OUT-B",
        ),
        "OUT-B",
    )
    .await;
    assert_eq!(ambient.out_values, vec![obag(vec![onullary("PZero"), onullary("PZero")])]);
    assert_eq!(ambient.fired_labels().expect("Ambient ledger"), vec!["OpenRule"]);
    assert!(lambda.fired_data.is_empty());
    assert_green(&lambda);
    assert_green(&ambient);

    // 3. A rewrite returns a B root: contractum re-entry dispatches to B; ledgers
    // partition one mixed execution exactly by the language that fired each rule.
    let mixed = mixed_tagged(
        &installed.lambda_fp,
        "App",
        vec![
            reflect_ground_term_par(&g_id(), &installed.lambda_fp),
            reflect_ground_term_par(&g_open_redex(), &installed.ambient_fp),
        ],
    );
    let (lambda, ambient) = run(
        &installed,
        rho_net_drive_call_par_with_fuel(&installed.lambda_fp, mixed, FUEL, "OUT-AB"),
        "OUT-AB",
    )
    .await;
    assert_eq!(lambda.out_values, vec![obag(vec![onullary("PZero"), onullary("PZero")])]);
    assert_eq!(lambda.fired_labels().expect("Lambda ledger"), vec!["Beta"]);
    assert_eq!(ambient.fired_labels().expect("Ambient ledger"), vec!["OpenRule"]);
    assert_green(&lambda);
    assert_green(&ambient);

    // 4. The explicit wrong driver remains a veto: root seeding never auto-corrects.
    let wrong = reflect_ground_term_par(&g_open_redex(), &installed.ambient_fp);
    let (lambda, ambient) = run(
        &installed,
        rho_net_drive_call_par_with_fuel(&installed.lambda_fp, wrong, FUEL, "OUT-WRONG"),
        "OUT-WRONG",
    )
    .await;
    assert!(lambda.out_values.is_empty());
    assert_eq!(lambda.err_data.len(), 1, "the A driver rejects the B root once");
    assert!(lambda.fired_data.is_empty());
    assert!(ambient.fired_data.is_empty());
    assert!(ambient.err_data.is_empty());

    // 5. A foreign closed value is an identity graft in an A slot.
    let inert_b = reflect_ground_term_par(&g_zero(), &installed.ambient_fp);
    let graft = mixed_tagged(
        &installed.lambda_fp,
        "App",
        vec![reflect_ground_term_par(&g_free("f"), &installed.lambda_fp), inert_b],
    );
    let expected = oapp(ofree("f"), onullary("PZero"));
    let (lambda, ambient) = run(
        &installed,
        rho_net_drive_call_par_with_fuel(&installed.lambda_fp, graft, FUEL, "OUT-GRAFT"),
        "OUT-GRAFT",
    )
    .await;
    assert_eq!(lambda.out_values, vec![expected]);
    assert!(lambda.fired_data.is_empty() && ambient.fired_data.is_empty());
    assert_green(&lambda);
    assert_green(&ambient);

    // 6. Depth-two alternation A[B[A]]: A descends to B; B's float treats A as
    // opaque; B's drive re-dispatches the nested A redex back to A.
    let nested_a = reflect_ground_term_par(&g_app(g_id(), g_k()), &installed.lambda_fp);
    let nested_b = mixed_tagged(
        &installed.ambient_fp,
        "PAmb",
        vec![reflect_ground_term_par(&g_name("n"), &installed.ambient_fp), nested_a],
    );
    let alternating = mixed_tagged(
        &installed.lambda_fp,
        "App",
        vec![reflect_ground_term_par(&g_free("f"), &installed.lambda_fp), nested_b],
    );
    let (lambda, ambient) = run(
        &installed,
        rho_net_drive_call_par_with_fuel(&installed.lambda_fp, alternating, FUEL, "OUT-ALT"),
        "OUT-ALT",
    )
    .await;
    assert_eq!(lambda.out_values, vec![oapp(ofree("f"), oambient(ofree("n"), ok()))]);
    assert_eq!(lambda.fired_labels().expect("nested A ledger"), vec!["Beta"]);
    assert!(ambient.fired_data.is_empty());
    assert_green(&lambda);
    assert_green(&ambient);

    // 7. A binder may contain a closed B term: A substitution/shift never enters B.
    let binder_crossing = mixed_tagged(
        &installed.lambda_fp,
        LAMBDA_REFLECT_LABEL,
        vec![reflect_ground_term_par(&g_zero(), &installed.ambient_fp)],
    );
    let (lambda, ambient) = run(
        &installed,
        rho_net_drive_call_par_with_fuel(&installed.lambda_fp, binder_crossing, FUEL, "OUT-BINDER"),
        "OUT-BINDER",
    )
    .await;
    assert_eq!(lambda.out_values, vec![olambda(onullary("PZero"))]);
    assert!(lambda.fired_data.is_empty() && ambient.fired_data.is_empty());
    assert_green(&lambda);
    assert_green(&ambient);

    // 8. Fuel exhaustion belongs to the selected child driver, never its parent.
    let omega_half = g_lambda(g_app(g_bound(0), g_bound(0)));
    let omega =
        reflect_ground_term_par(&g_app(omega_half.clone(), omega_half), &installed.lambda_fp);
    let ambient_with_omega = mixed_tagged(
        &installed.ambient_fp,
        "PAmb",
        vec![reflect_ground_term_par(&g_name("n"), &installed.ambient_fp), omega],
    );
    let (lambda, ambient) = run(
        &installed,
        rho_net_drive_float_call_par_with_fuel(
            &installed.ambient_fp,
            ambient_with_omega,
            1,
            "OUT-FUEL",
        ),
        "OUT-FUEL",
    )
    .await;
    assert!(lambda.out_values.is_empty());
    assert_eq!(lambda.fired_labels().expect("one Lambda firing"), vec!["Beta"]);
    assert_eq!(lambda.fuel_data.len(), 1, "the exhausted Lambda child is reported by Lambda");
    assert!(lambda.err_data.is_empty());
    assert!(ambient.fuel_data.is_empty() && ambient.err_data.is_empty());

    // 9. Nil has no fingerprint. The union bag gate lets a bag-free A driver return
    // an empty B soup encountered as a structural child without inventing an owner.
    let empty_guest = mixed_bag(&installed.ambient_fp, Vec::new());
    let with_empty = mixed_tagged(
        &installed.lambda_fp,
        "App",
        vec![reflect_ground_term_par(&g_free("f"), &installed.lambda_fp), empty_guest],
    );
    let (lambda, ambient) = run(
        &installed,
        rho_net_drive_call_par_with_fuel(&installed.lambda_fp, with_empty, FUEL, "OUT-NIL"),
        "OUT-NIL",
    )
    .await;
    assert_eq!(lambda.out_values, vec![oapp(ofree("f"), obag(Vec::new()))]);
    assert!(lambda.fired_data.is_empty() && ambient.fired_data.is_empty());
    assert_green(&lambda);
    assert_green(&ambient);
}
