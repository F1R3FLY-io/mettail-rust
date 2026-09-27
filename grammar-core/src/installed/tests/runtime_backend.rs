//! Recording-backend tests of the installed interface, not WPDA recognition.
use super::*;
use crate::{DynamicValue, ParseWeight};
use std::sync::atomic::AtomicUsize;

#[derive(Debug)]
struct Invocation {
    fingerprint: [u8; 32],
    category: Option<CategoryId>,
    policy: RuntimePolicy,
    input_end: usize,
    hole: Option<u32>,
}

#[derive(Default)]
struct RecordingState {
    preparations: AtomicUsize,
    drops: AtomicUsize,
    invocations: Mutex<Vec<Invocation>>,
    error: Mutex<Option<RuntimeError>>,
    revoke: Mutex<Option<(Arc<InstalledLanguageTable>, LanguageRevocationAuthority)>>,
}

pub(super) struct RecordingFactory {
    state: Arc<RecordingState>,
    epoch: [u8; 32],
    fail_at: Option<usize>,
}

impl Default for RecordingFactory {
    fn default() -> Self {
        Self {
            state: Arc::new(RecordingState::default()),
            epoch: [47; 32],
            fail_at: None,
        }
    }
}

impl RuntimeParserFactory for RecordingFactory {
    fn semantic_commitment(&self) -> [u8; 32] {
        self.epoch
    }

    fn prepare(
        &self,
        admission: RuntimeParserAdmission<'_>,
    ) -> Result<Arc<dyn RuntimeParserBackend>, RuntimeError> {
        let grammar = admission.grammar();
        let image = admission.image();
        assert_eq!(grammar.fingerprint().expect("fixture fingerprint"), image.core_fingerprint);
        let ordinal = self.state.preparations.fetch_add(1, Ordering::SeqCst) + 1;
        if self.fail_at == Some(ordinal) {
            return Err(RuntimeError::Reduction("recording preparation refused".into()));
        }
        Ok(Arc::new(RecordingBackend { state: self.state.clone() }))
    }
}

struct RecordingBackend {
    state: Arc<RecordingState>,
}

impl Drop for RecordingBackend {
    fn drop(&mut self) {
        self.state.drops.fetch_add(1, Ordering::SeqCst);
    }
}

fn original_weight() -> rigail::LexicographicWeight {
    rigail::LexicographicWeight {
        primary: rigail::TropicalWeight(1.25),
        open_len: 11,
        lex_alt_idx: 13,
        src_idx: 17,
        rule_idx: 19,
    }
}

impl RuntimeParserBackend for RecordingBackend {
    fn parse(
        &self,
        session: &RuntimeLexicalSession<'_, '_, '_>,
        category: Option<CategoryId>,
        policy: RuntimePolicy,
    ) -> Result<Vec<WeightedParse>, RuntimeError> {
        let hole = session.hole_at(0);
        self.state
            .invocations
            .lock()
            .expect("invocation log")
            .push(Invocation {
                fingerprint: session.image().core_fingerprint,
                category,
                policy,
                input_end: session.input_end(),
                hole: hole.map(|hole| hole.id),
            });
        if let Some((table, authority)) = self.state.revoke.lock().expect("revocation slot").take()
        {
            table
                .revoke(authority)
                .expect("revoke during recording call");
        }
        if let Some(error) = self.state.error.lock().expect("error slot").clone() {
            return Err(error);
        }
        let value = hole.map_or(DynamicValue::Unit, |hole| DynamicValue::TemplateHole {
            id: hole.id,
            category: hole.category.expect("fixture declares its hole category"),
        });
        Ok(vec![WeightedParse {
            syntax: value.clone(),
            value,
            weight: ParseWeight::SharedWpda(original_weight()),
            production: None,
        }])
    }
}

fn request(name: &str) -> RuntimeLanguageInstall {
    let core = core(name);
    RuntimeLanguageInstall {
        image: image(&core),
        core,
        granted_rights: LanguageRights::all(),
    }
}

#[test]
fn direct_factory_admission_preserves_exact_borrows_and_limits() {
    let grammar = core("Direct");
    let image = image(&grammar);
    let limits = ParserImageAdmissionLimits::default();
    let admission = RuntimeParserAdmission::verify(&grammar, &image, COMPILER, UNICODE, limits)
        .expect("original executable-image verifier admits fixture");
    assert!(std::ptr::eq(admission.grammar(), &grammar));
    let admitted_grammar = admission.admitted_grammar();
    let copied_grammar = admitted_grammar;
    assert!(std::ptr::eq(admitted_grammar.grammar(), &grammar));
    assert!(std::ptr::eq(copied_grammar.grammar(), &grammar));
    assert!(std::ptr::eq(admission.image(), &image));
    assert_eq!(admission.limits(), limits);
    let factory = RecordingFactory::default();
    let _backend = factory.prepare(admission).expect("prepare admitted input");
    assert_eq!(factory.state.preparations.load(Ordering::SeqCst), 1);
}

#[test]
fn lexical_session_admission_preserves_exact_grammar_borrow() {
    let grammar = core("SessionAdmission");
    let image = image(&grammar);
    let parser = RuntimeParser::new(&grammar, &image, COMPILER, UNICODE, &DefaultRuntimeHost)
        .expect("original parser construction verifies fixture");
    // This shared recording fixture has no tokens; its admitted source is empty.
    let session = parser.lexical_session("").expect("original lexer session");
    let admitted = session.admitted_grammar();
    assert!(std::ptr::eq(admitted.grammar(), &grammar));
    assert!(std::ptr::eq(admitted.grammar(), session.grammar()));
}

#[test]
fn direct_factory_admission_refuses_stale_malformed_abi_and_over_limit_inputs() {
    let grammar = core("DirectRejected");
    let original = image(&grammar);
    let limits = ParserImageAdmissionLimits::default();
    let mut stale = original.clone();
    stale.core_fingerprint = [0; 32];
    assert!(matches!(
        RuntimeParserAdmission::verify(&grammar, &stale, COMPILER, UNICODE, limits),
        Err(ImageError::CoreFingerprintMismatch)
    ));
    assert!(matches!(
        RuntimeParserAdmission::verify(&grammar, &original, "other-compiler", UNICODE, limits),
        Err(ImageError::CompilerAbiMismatch)
    ));
    assert!(matches!(
        RuntimeParserAdmission::verify(&grammar, &original, COMPILER, "other-unicode", limits),
        Err(ImageError::UnicodeVersionMismatch)
    ));
    let mut malformed = original.clone();
    malformed.engine.nonterminal_count += 1;
    assert!(
        RuntimeParserAdmission::verify(&grammar, &malformed, COMPILER, UNICODE, limits).is_err()
    );
    // Executable verification checks structural limits, not the wire decoder's
    // max_encoded_bytes guard. Ensure this fixture exercises an actual limit.
    assert!(!original.lexer.states.is_empty());
    assert!(RuntimeParserAdmission::verify(
        &grammar,
        &original,
        COMPILER,
        UNICODE,
        ParserImageAdmissionLimits { max_lexer_states: 0, ..limits }
    )
    .is_err());
    let mut invalid = grammar.clone();
    invalid.abi = crate::GRAMMAR_CORE_ABI_V6;
    assert!(matches!(
        RuntimeParserAdmission::verify(&invalid, &original, COMPILER, UNICODE, limits),
        Err(ImageError::InvalidGrammar(_))
    ));
}

#[test]
fn absent_factory_refuses_runtime_installation_without_publication() {
    let table = InstalledLanguageTable::new();
    let grammar = core("NoFactory");
    assert!(matches!(
        table.install_runtime(
            grammar.clone(),
            image(&grammar),
            LanguageRights::all(),
            COMPILER,
            UNICODE,
            "caps/1",
            [7; 32]
        ),
        Err(InstallLanguageError::MissingRuntimeFactory)
    ));
    assert_eq!(table.installed_count().expect("count"), 0);
}

#[test]
fn late_backend_preparation_failure_drops_unpublished_prefix() {
    let factory = Arc::new(RecordingFactory { fail_at: Some(2), ..Default::default() });
    let table = InstalledLanguageTable::with_runtime_factory(factory.clone());
    assert!(matches!(
        table.install_runtime_batch(vec![request("First"), request("Second")], COMPILER, UNICODE, "caps/1", [7; 32]),
        Err(InstallLanguageError::RuntimeBackend(RuntimeError::Reduction(message)))
            if message == "recording preparation refused"
    ));
    assert_eq!(factory.state.preparations.load(Ordering::SeqCst), 2);
    assert_eq!(factory.state.drops.load(Ordering::SeqCst), 1);
    assert_eq!(table.installed_count().expect("count"), 0);
    assert!(factory.state.invocations.lock().expect("calls").is_empty());
}

#[test]
fn runtime_sessions_reuse_prepared_backend_and_preserve_weight_and_holes() {
    let factory = Arc::new(RecordingFactory::default());
    let table = InstalledLanguageTable::with_runtime_factory(factory.clone());
    let mut grammar = core("Session");
    grammar.categories[0].admits_variables = true;
    grammar.limits.max_input_bytes = 128;
    grammar.limits.max_parse_items = 129;
    grammar.limits.max_forest_nodes = 130;
    grammar.limits.max_semantic_results = 131;
    let fingerprint = grammar.fingerprint().expect("fingerprint");
    let grant = table
        .install_runtime(
            grammar.clone(),
            image(&grammar),
            LanguageRights::all(),
            COMPILER,
            UNICODE,
            "caps/1",
            [7; 32],
        )
        .expect("recording install");
    let policy = RuntimePolicy::default();
    let parsed = table
        .parse(&grant.handle, "", Some(CategoryId(0)), &DefaultRuntimeHost, policy)
        .expect("recorded source");
    assert!(parsed[0].weight.exact().is_none());
    let weight = parsed[0]
        .weight
        .shared_wpda()
        .expect("original WPDA weight");
    assert_eq!(weight, &original_weight());
    assert_eq!(weight.primary.0.to_bits(), original_weight().primary.0.to_bits());
    assert_eq!(parsed[0].syntax, DynamicValue::Unit);
    assert_eq!(parsed[0].value, DynamicValue::Unit);
    assert_eq!(parsed[0].production, None);
    let pieces = [RuntimeTemplatePiece::Hole(0)];
    let holes = [RuntimeTemplateHole { id: 0, category: Some(CategoryId(0)) }];
    for _ in 0..2 {
        let parsed = table
            .parse_template(
                &grant.handle,
                &pieces,
                &holes,
                Some(CategoryId(0)),
                &DefaultRuntimeHost,
                policy,
                LanguageRight::Construct,
            )
            .expect("recorded template");
        assert_eq!(parsed[0].syntax, DynamicValue::TemplateHole { id: 0, category: CategoryId(0) });
        assert_eq!(parsed[0].weight.shared_wpda(), Some(&original_weight()));
    }
    assert_eq!(factory.state.preparations.load(Ordering::SeqCst), 1);
    let calls = factory.state.invocations.lock().expect("calls");
    assert_eq!(calls.len(), 2, "one source call and one uncached template call");
    assert_eq!(calls[0].input_end, 0);
    assert_eq!(calls[0].hole, None);
    assert_eq!(calls[1].input_end, 1);
    assert_eq!(calls[1].hole, Some(0));
    for call in calls.iter() {
        assert_eq!(call.fingerprint, fingerprint);
        assert_eq!(call.category, Some(CategoryId(0)));
        assert_eq!(call.policy.max_input_bytes, 128);
        assert_eq!(call.policy.max_parse_items, 129);
        assert_eq!(call.policy.max_forest_nodes, 130);
        assert_eq!(call.policy.max_semantic_results, 131);
    }
}

#[test]
fn backend_errors_are_not_cached_or_converted_to_no_parse() {
    let factory = Arc::new(RecordingFactory::default());
    *factory.state.error.lock().expect("error") = Some(RuntimeError::SemanticResultLimit);
    let table = InstalledLanguageTable::with_runtime_factory(factory.clone());
    let grant = install(&table, LanguageRights::all());
    for _ in 0..2 {
        assert!(matches!(
            table.parse_template(
                &grant.handle,
                &[],
                &[],
                None,
                &DefaultRuntimeHost,
                RuntimePolicy::default(),
                LanguageRight::Construct
            ),
            Err(InstalledParseError::Parse(RuntimeError::SemanticResultLimit))
        ));
    }
    assert_eq!(factory.state.invocations.lock().expect("calls").len(), 2);
}

#[test]
fn authority_checks_bracket_backend_execution() {
    let factory = Arc::new(RecordingFactory::default());
    let table = Arc::new(InstalledLanguageTable::with_runtime_factory(factory.clone()));
    let grant = install(&table, LanguageRights::all());
    let denied = grant.handle.attenuate(&LanguageRights::none());
    assert!(matches!(
        table.parse(&denied, "", None, &DefaultRuntimeHost, RuntimePolicy::default()),
        Err(InstalledParseError::Access(LanguageAccessError::MissingRight(
            LanguageRight::Parse
        )))
    ));
    assert!(factory.state.invocations.lock().expect("calls").is_empty());
    *factory.state.revoke.lock().expect("revocation") = Some((table.clone(), grant.revocation));
    assert!(matches!(
        table.parse(&grant.handle, "", None, &DefaultRuntimeHost, RuntimePolicy::default()),
        Err(InstalledParseError::Access(LanguageAccessError::Revoked))
            | Err(InstalledParseError::Access(LanguageAccessError::StaleHandle))
    ));
    assert_eq!(factory.state.invocations.lock().expect("calls").len(), 1);
}

#[test]
fn engine_epoch_is_part_of_installation_and_template_identity() {
    let mut keys = Vec::new();
    for epoch in [[47; 32], [48; 32]] {
        let factory = Arc::new(RecordingFactory { epoch, ..Default::default() });
        let table = InstalledLanguageTable::with_runtime_factory(factory);
        let grant = install(&table, LanguageRights::all());
        let language = table
            .authorize(&grant.handle, LanguageRight::Parse)
            .expect("language");
        assert_eq!(language.commitment().runtime_backend_commitment, Some(epoch));
        assert_eq!(language.commitment().parser_kind, InstalledParserKind::RuntimeImage);
        assert!(language.parser_image().is_some());
        keys.push(
            language.symbolic_template_cache_key(
                language
                    .template_semantic_commitments(&DefaultRuntimeHost)
                    .expect("commitments"),
                &[],
                &[],
                None,
                RuntimePolicy::default(),
            ),
        );
    }
    assert_ne!(keys[0], keys[1]);
}

#[test]
fn invalid_category_and_input_budget_refuse_before_backend_invocation() {
    let factory = Arc::new(RecordingFactory::default());
    let table = InstalledLanguageTable::with_runtime_factory(factory.clone());
    let grant = install(&table, LanguageRights::all());
    // This source has no lexical reading in the fixture. Category validation
    // must nevertheless precede lexing, as it did on the original route.
    assert!(matches!(
        table.parse(
            &grant.handle,
            "unlexable",
            Some(CategoryId(1)),
            &DefaultRuntimeHost,
            RuntimePolicy::default()
        ),
        Err(InstalledParseError::Parse(RuntimeError::InvalidCategory(CategoryId(1))))
    ));
    assert!(matches!(
        table.parse_template(
            &grant.handle,
            &[RuntimeTemplatePiece::Text("unlexable".into())],
            &[],
            Some(CategoryId(1)),
            &DefaultRuntimeHost,
            RuntimePolicy::default(),
            LanguageRight::Construct
        ),
        Err(InstalledParseError::Parse(RuntimeError::InvalidCategory(CategoryId(1))))
    ));
    let policy = RuntimePolicy {
        max_input_bytes: 0,
        ..RuntimePolicy::default()
    };
    assert!(matches!(
        table.parse(&grant.handle, "x", None, &DefaultRuntimeHost, policy),
        Err(InstalledParseError::Parse(RuntimeError::InputTooLarge))
    ));
    assert!(factory.state.invocations.lock().expect("calls").is_empty());
}
