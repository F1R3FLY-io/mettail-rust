//! Doc 28's golden artifacts (`docs/architecture/rho-native-integration/
//! 28-translation-rule-system.md`).
//!
//! Two worked whole languages back that document's acceptance criteria:
//!
//! - **TriDemo (28 §6)** — three base rewrites whose second and third LHSs share
//!   the whole `Pair(x, y)` sub-pattern. The tests here pin the §6.2 interning
//!   trace's outcome (8 states from 11 raw nodes, the shared state with two
//!   parents) and BOTH admission gates: the AC-free automaton compile (gate 1,
//!   inside `compile_in_rho_matching_ruleset`) and the serializer admission
//!   (gate 2, `multi_pattern_receiver_network_par` returns `Ok`).
//! - **TwoRuleLambda (28 §7)** — lambdademo's grammar with `Beta` plus one plain
//!   base rewrite `Unwrap`. The golden test builds the installed program through
//!   the PRODUCTION path (`plan_rho_default_backend` →
//!   `installed_rho_net_program_par`, the same chain the runtime invocations and
//!   the benchmark harness compile through), renders it with the deterministic
//!   structural renderer below, and pins the rendering against BOTH the listing
//!   file `docs/architecture/rho-native-integration/listings/
//!   28-two-rule-lambda-installed.txt` AND the fenced block embedded in doc 28
//!   §7.2 (between the two `doc28-golden-listing` marker comments) — so the
//!   document can never drift from the emitters.
//!
//! The ONLY non-structural transformation the renderer performs is the one doc
//! 28 §7.2 states: every occurrence of the language fingerprint
//! (`mettail-langdef-v1:{16 hex digits}`) in the rendered text is replaced by
//! `fp`, and a `GPrivate` whose id is the prost-encoded tag string is printed
//! as `priv(tag)`. Everything else is rendered verbatim, in prost field order,
//! with no hashing and no reordering — deterministic by construction.

use dovetail::set_automaton::{AutomatonNode, StateId};
use mettail_ast::language::LanguageDef;
use mettail_rholang_codegen::{
    compile_in_rho_matching_ruleset, lower_language_def, multi_pattern_receiver_network_par,
    plan_rho_default_backend, suggest_rejected_rule_dispositions, AutomatonAcceptTarget,
    RhoCoverageEvidence, RhoDefaultBackendRequirements, RhoGuardCoverageEvidence,
};
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::g_unforgeable::UnfInstance;
use models::rhoapi::var::VarInstance;
use models::rhoapi::{Expr, Match, New, Par, Receive, Send, Var};

// ─────────────────────────────────────────────────────────────────────────────
// The two worked languages, exactly as doc 28 §6.1 / §7.1 display them.
// ─────────────────────────────────────────────────────────────────────────────

/// Doc 28 §6.1's TriDemo body (also compile-validated as a `language!` body by
/// `macros/src/doc_examples.rs::tri_demo_doc_example_parses_as_language_def`).
const TRI_DEMO: &str = r#"
name: TriDemo,
options { emit_simulator: false, emit_blockly: false, },
types { Term },
terms {
    Pair . a:Term, b:Term |- "pair" "(" a "," b ")" : Term ;
    Swap . a:Term, b:Term |- "swap" "(" a "," b ")" : Term ;
    Wrap . t:Term |- "wrap" "(" t ")" : Term ;
    Flip . t:Term |- "flip" "(" t ")" : Term ;
},
equations {},
rewrites {
    SwapRule . |- (Swap a b) ~> (Pair b a) ;
    WrapRule . |- (Wrap (Pair x y)) ~> (Pair x y) ;
    FlipRule . |- (Flip (Pair x y)) ~> (Pair y x) ;
}
"#;

/// Doc 28 §7.1's TwoRuleLambda body: lambdademo's grammar (`languages/src/
/// lambdademo.rs`) with `Beta` kept and the plain base rewrite `Unwrap` added.
const TWO_RULE_LAMBDA: &str = r#"
name: TwoRuleLambda,
options { emit_simulator: false, emit_blockly: false, },
types { Term },
terms {
    Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term ;
    App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term ;
    F . a:Term |- "f" "(" a ")" : Term ;
    A . |- "A" : Term ;
},
equations {},
rewrites {
    Beta . |- (App (Lam fun) arg) ~> (eval fun arg) ;
    Unwrap . |- (F a) ~> a ;
}
"#;

fn parse_language(source: &str) -> LanguageDef {
    let def: LanguageDef =
        syn::parse_str(source).expect("the doc 28 language body must parse as a LanguageDef");
    mettail_ast::validation::validate_language(&def)
        .expect("the doc 28 language body must satisfy language validation");
    def
}

// ─────────────────────────────────────────────────────────────────────────────
// TriDemo (doc 28 §6): the interning-trace outcome and both admission gates.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn tridemo_interns_three_rules_into_eight_states_sharing_pair() {
    let def = parse_language(TRI_DEMO);
    let ruleset = compile_in_rho_matching_ruleset(&def);

    // Gate 1 (the AC-free automaton compile) admitted every rewrite: nothing was
    // routed off the positional automaton.
    assert!(
        ruleset.deferred.is_empty(),
        "TriDemo's three base rewrites must all be automaton entries, got {:?}",
        ruleset.deferred
    );

    let view = ruleset.automaton.view();
    assert_eq!(view.entry_count(), 3, "one entry per rewrite");
    // The §6.2 interning trace: 11 intern() calls, 3 table hits, 8 states.
    assert_eq!(
        view.state_count(),
        8,
        "TriDemo interns 8 distinct sub-patterns from 11 raw pattern nodes"
    );

    // The shared state s5 = App{Pair, [s3, s4]}: the Wrap and Flip entries'
    // argument states are THE SAME StateId (doc 28 §6.2, figure 28-3).
    let mut swap_args: Option<Vec<StateId>> = None;
    let mut wrap_arg: Option<StateId> = None;
    let mut flip_arg: Option<StateId> = None;
    for entry in 0..view.entry_count() {
        match view.node(view.entry_root_state(entry)) {
            AutomatonNode::App { op, args } => match op.as_str() {
                "Swap" => {
                    assert_eq!(args.len(), 2, "Swap root arity");
                    swap_args = Some(args.to_vec());
                },
                "Wrap" => {
                    assert_eq!(args.len(), 1, "Wrap root arity");
                    wrap_arg = Some(args[0]);
                },
                "Flip" => {
                    assert_eq!(args.len(), 1, "Flip root arity");
                    flip_arg = Some(args[0]);
                },
                other => panic!("unexpected TriDemo root op {other}"),
            },
            AutomatonNode::Var(name) => panic!("unexpected bare-Var root {name}"),
        }
    }
    let wrap_arg = wrap_arg.expect("a Wrap-rooted entry must exist");
    let flip_arg = flip_arg.expect("a Flip-rooted entry must exist");
    assert_eq!(
        wrap_arg, flip_arg,
        "WrapRule and FlipRule share ONE interned Pair(x, y) state (s5)"
    );
    match view.node(wrap_arg) {
        AutomatonNode::App { op, args } => {
            assert_eq!(op.as_str(), "Pair", "the shared state is the Pair application");
            assert_eq!(args.len(), 2, "Pair arity");
            // Variable-name-awareness (21 §7.1): SwapRule's Var(a)/Var(b) states
            // are DISJOINT from the shared Pair's Var(x)/Var(y) states.
            let swap_args = swap_args.expect("a Swap-rooted entry must exist");
            for shared_child in args {
                assert!(
                    !swap_args.contains(shared_child),
                    "Var(a)/Var(b) must not alias Var(x)/Var(y): the quotient is name-aware"
                );
            }
        },
        AutomatonNode::Var(name) => panic!("the shared state must be an App, got Var({name})"),
    }

    // Gate 2 (the serializer admission): the multi-pattern network serializes —
    // one FLAT case (Swap) and two NESTED cases (Wrap, Flip) under one Match.
    let targets: Vec<AutomatonAcceptTarget> = ruleset
        .accept_channels
        .iter()
        .map(|(pattern, accept_channel)| AutomatonAcceptTarget {
            pattern: *pattern,
            accept_channel: accept_channel.clone(),
            out_channel: "doc28:out".to_string(),
        })
        .collect();
    assert_eq!(targets.len(), 3, "one accept target per entry");
    multi_pattern_receiver_network_par(&view, "site0", &targets, &ruleset.language_fingerprint)
        .expect("TriDemo passes the serializer admission gate (gate 2)");
}

// ─────────────────────────────────────────────────────────────────────────────
// TwoRuleLambda (doc 28 §7): the automaton size and the pinned installed Par.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn two_rule_lambda_interns_six_states() {
    let def = parse_language(TWO_RULE_LAMBDA);
    let ruleset = compile_in_rho_matching_ruleset(&def);
    assert!(
        ruleset.deferred.is_empty(),
        "Beta (via the ^lambda remap) and Unwrap must both be automaton entries, got {:?}",
        ruleset.deferred
    );
    let view = ruleset.automaton.view();
    assert_eq!(view.entry_count(), 2, "one entry per rewrite");
    assert_eq!(view.state_count(), 6, "doc 28 §7.1: the six states s0..s5");
}

#[test]
fn two_rule_lambda_installed_par_matches_the_pinned_listing() {
    let def = parse_language(TWO_RULE_LAMBDA);
    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("TwoRuleLambda passes the Rho-default backend flip gate");
    let installed = plan
        .installed_rho_net_program_par()
        .expect("the fail-closed install gate admits TwoRuleLambda");
    let fingerprint = plan.definition_fingerprint().to_string();

    let rendered = render_par_program(&installed, &fingerprint);
    // Printed unconditionally so a listing update is a copy from the test log,
    // never a hand-transcription.
    eprintln!("== doc28 rendered listing begin ==\n{rendered}== doc28 rendered listing end ==");

    // Pin 1: the listing file the document links.
    let listing_path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../docs/architecture/rho-native-integration/listings/28-two-rule-lambda-installed.txt"
    );
    let pinned = std::fs::read_to_string(listing_path)
        .expect("the doc 28 listing file must exist (listings/28-two-rule-lambda-installed.txt)");
    assert_eq!(
        rendered.trim_end(),
        pinned.trim_end(),
        "the rendered installed Par must equal the pinned listing file"
    );

    // Pin 2: the fenced block embedded in doc 28 §7.2 itself.
    let doc_path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../docs/architecture/rho-native-integration/28-translation-rule-system.md"
    );
    let doc = std::fs::read_to_string(doc_path).expect("doc 28 must exist");
    let embedded = extract_marked_listing(&doc);
    assert_eq!(
        rendered.trim_end(),
        embedded.trim_end(),
        "the rendered installed Par must equal doc 28 §7.2's embedded fenced block"
    );
}

/// Extract the fenced listing between the two `doc28-golden-listing` marker
/// comments in doc 28 §7.2: the first fence line after the begin marker opens
/// the block, the next fence line closes it.
fn extract_marked_listing(doc: &str) -> String {
    let begin = doc
        .find("<!-- doc28-golden-listing:begin -->")
        .expect("doc 28 must carry the doc28-golden-listing:begin marker");
    let end = doc
        .find("<!-- doc28-golden-listing:end -->")
        .expect("doc 28 must carry the doc28-golden-listing:end marker");
    let region = &doc[begin..end];
    let fence_open = region
        .find("```")
        .expect("a fenced block must follow the begin marker");
    let after_open = &region[fence_open..];
    let body_start = after_open
        .find('\n')
        .expect("the opening fence line must end")
        + 1;
    let body = &after_open[body_start..];
    let fence_close = body
        .find("```")
        .expect("the fenced block must close before the end marker");
    body[..fence_close].to_string()
}

// ─────────────────────────────────────────────────────────────────────────────
// The deterministic structural renderer (doc 28 §7.2's stated syntax).
// ─────────────────────────────────────────────────────────────────────────────

fn render_par_program(par: &Par, fingerprint: &str) -> String {
    let rendered = render_par_block(par, 0);
    // The ONE mechanical elision doc 28 §7.2 states: the language fingerprint
    // is shortened to `fp` wherever it occurs in the rendered text.
    rendered.replace(fingerprint, "fp")
}

fn pad(indent: usize) -> String {
    "  ".repeat(indent)
}

/// Render a Par as a block of ` |`-joined components, one per line group, in
/// prost field order: unforgeables, exprs, sends, receives, news, matches.
fn render_par_block(par: &Par, indent: usize) -> String {
    assert!(par.bundles.is_empty(), "no bundles occur in an installed rho-net program");
    assert!(par.connectives.is_empty(), "no connectives occur outside receive patterns here");
    let mut components: Vec<String> = Vec::with_capacity(
        par.unforgeables.len()
            + par.exprs.len()
            + par.sends.len()
            + par.receives.len()
            + par.news.len()
            + par.matches.len(),
    );
    for unf in &par.unforgeables {
        components.push(format!("{}{}", pad(indent), render_unforgeable(unf)));
    }
    for expr in &par.exprs {
        components.push(format!("{}{}", pad(indent), render_expr(expr)));
    }
    for send in &par.sends {
        components.push(render_send(send, indent));
    }
    for receive in &par.receives {
        components.push(render_receive(receive, indent));
    }
    for new in &par.news {
        components.push(render_new(new, indent));
    }
    for m in &par.matches {
        components.push(render_match(m, indent));
    }
    if components.is_empty() {
        return format!("{}Nil\n", pad(indent));
    }
    let mut out = String::with_capacity(components.iter().map(String::len).sum::<usize>() + 16);
    let last = components.len() - 1;
    for (index, component) in components.into_iter().enumerate() {
        out.push_str(&component);
        if index != last {
            out.push_str(" |");
        }
        out.push('\n');
    }
    out
}

/// Render a Par in INLINE position (a channel, a send argument, a match target,
/// a match-case pattern): exactly one component is expected there.
fn render_par_inline(par: &Par) -> String {
    let component_count = par.sends.len()
        + par.receives.len()
        + par.news.len()
        + par.exprs.len()
        + par.matches.len()
        + par.unforgeables.len()
        + par.bundles.len()
        + par.connectives.len();
    if component_count == 0 {
        return "Nil".to_string();
    }
    assert_eq!(
        component_count, 1,
        "an inline par must carry exactly one component, got {par:?}"
    );
    if let Some(unf) = par.unforgeables.first() {
        return render_unforgeable(unf);
    }
    if let Some(expr) = par.exprs.first() {
        return render_expr(expr);
    }
    panic!("unsupported inline par component: {par:?}");
}

fn render_unforgeable(unf: &models::rhoapi::GUnforgeable) -> String {
    match unf
        .unf_instance
        .as_ref()
        .expect("an unforgeable must carry its instance")
    {
        UnfInstance::GPrivateBody(private) => format!("priv({})", decode_gprivate(&private.id)),
        other => panic!("unsupported unforgeable in the installed program: {other:?}"),
    }
}

/// A `GPrivateBuilder::new_par_from_string` id is the prost encoding of the tag
/// string (field 1, length-delimited): `0x0A`, one length byte, the UTF-8 tag.
/// Decode it back to the tag; anything else is rendered as hex.
fn decode_gprivate(id: &[u8]) -> String {
    if id.len() >= 2 && id[0] == 0x0A && usize::from(id[1]) == id.len() - 2 {
        if let Ok(tag) = std::str::from_utf8(&id[2..]) {
            return tag.to_string();
        }
    }
    id.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn render_expr(expr: &Expr) -> String {
    match expr
        .expr_instance
        .as_ref()
        .expect("an expr must carry its instance")
    {
        ExprInstance::EListBody(list) => {
            // E-2-D: the `^subst`/`^shift` hereditary-ground ENTRY guard matches
            // `[ _, ^gnd, ...rest ]` — an EList pattern WITH a wildcard remainder. Render it.
            let mut elements: Vec<String> = list.ps.iter().map(render_par_inline).collect();
            if let Some(remainder) = list.remainder.as_ref() {
                elements.push(format!("...{}", render_var(remainder)));
            }
            format!("[{}]", elements.join(", "))
        },
        ExprInstance::EVarBody(evar) => {
            render_var(evar.v.as_ref().expect("an EVar must carry its var"))
        },
        ExprInstance::GString(value) => format!("\"{value}\""),
        ExprInstance::GInt(value) => value.to_string(),
        other => panic!("unsupported expr in the installed program: {other:?}"),
    }
}

fn render_var(var: &Var) -> String {
    match var
        .var_instance
        .as_ref()
        .expect("a var must carry its instance")
    {
        VarInstance::BoundVar(index) => format!("bv({index})"),
        VarInstance::FreeVar(index) => format!("fv({index})"),
        VarInstance::Wildcard(_) => "_".to_string(),
    }
}

fn render_send(send: &Send, indent: usize) -> String {
    let chan = render_par_inline(send.chan.as_ref().expect("a send must carry its channel"));
    let bang = if send.persistent { "!!" } else { "!" };
    let data: Vec<String> = send.data.iter().map(render_par_inline).collect();
    format!("{}{chan}{bang}({})", pad(indent), data.join(", "))
}

fn render_receive(receive: &Receive, indent: usize) -> String {
    assert!(!receive.peek, "no peek receives occur in an installed rho-net program");
    let arrow = if receive.persistent { "<=" } else { "<-" };
    let binds: Vec<String> = receive
        .binds
        .iter()
        .map(|bind| {
            assert!(bind.remainder.is_none(), "no bind remainder occurs here");
            let patterns: Vec<String> = bind.patterns.iter().map(render_par_inline).collect();
            let source =
                render_par_inline(bind.source.as_ref().expect("a bind must carry its source"));
            format!("{} {arrow} {source}", patterns.join(", "))
        })
        .collect();
    let condition = match &receive.condition {
        Some(cond) => format!(" where({})", render_par_inline(cond)),
        None => String::new(),
    };
    let body = render_par_block(
        receive
            .body
            .as_ref()
            .expect("a receive must carry its body"),
        indent + 1,
    );
    format!(
        "{}for ({}){condition} {{\n{body}{}}}",
        pad(indent),
        binds.join(" ; "),
        pad(indent)
    )
}

fn render_new(new: &New, indent: usize) -> String {
    assert!(new.uri.is_empty(), "no uri-bound news occur here");
    assert!(new.injections.is_empty(), "no injections occur here");
    let body = render_par_block(new.p.as_ref().expect("a new must carry its body"), indent + 1);
    format!("{}new {} {{\n{body}{}}}", pad(indent), new.bind_count, pad(indent))
}

fn render_match(m: &Match, indent: usize) -> String {
    let target = render_par_inline(m.target.as_ref().expect("a match must carry its target"));
    let mut out = format!("{}match {target} {{\n", pad(indent));
    let last = m.cases.len().saturating_sub(1);
    for (index, case) in m.cases.iter().enumerate() {
        assert!(case.guard.is_none(), "no case guards occur here");
        let pattern = render_par_inline(
            case.pattern
                .as_ref()
                .expect("a case must carry its pattern"),
        );
        let body =
            render_par_block(case.source.as_ref().expect("a case must carry its body"), indent + 2);
        out.push_str(&format!("{}{pattern} => {{\n{body}{}}}", pad(indent + 1), pad(indent + 1)));
        if index != last {
            out.push_str(" |");
        }
        out.push('\n');
    }
    out.push_str(&format!("{}}}", pad(indent)));
    out
}
