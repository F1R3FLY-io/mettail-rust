//! (A4) The TOKEN-TEXT LEAF fixture — the language the capability-A red proofs run on.
//!
//! It exists to put every discrimination A makes into ONE generated op-enum, so each
//! assertion's control is produced by the SAME walk over the SAME language as the assertion
//! itself. A control drawn from a different fixture cannot tell "the split is per-KIND" apart
//! from "the two languages differ".
//!
//! ```text
//!  ┌────────────┬──────────────────────────┬──────────────────────────────────────────────┐
//!  │ constructor│ field shape              │ what it is evidence FOR                      │
//!  ├────────────┼──────────────────────────┼──────────────────────────────────────────────┤
//!  │ `Named`    │ `m:Ident`                │ ★ the subject: a token-text leaf that is      │
//!  │            │                          │   LABELLED (`FieldTokenText`), INVERTIBLE     │
//!  │            │                          │   (`build_token_text_d`) and FOLD-READABLE    │
//!  │            │                          │   (the body dispatches on `m.as_str()`)       │
//!  │ `Call`     │ `recv:Proc, m:Ident`      │ the MIXED variant — `Arc<Proc>` beside a bare │
//!  │            │                          │   `String`; proves reconstruction is per-FIELD│
//!  │            │                          │   rather than all-or-nothing for the variant  │
//!  │ `Wrap`     │ `p:Proc`                  │ CONTROL: an object-only fold, so "the text    │
//!  │            │                          │   round-tripped" is distinguishable from      │
//!  │            │                          │   "the fold machinery ran at all"             │
//!  │ `Guest`    │ `*flt(node, …)`           │ CONTROL: an `OpaqueLeafKind::GuestBody` leaf  │
//!  │            │                          │   that must STAY `FieldOpaque` and must STAY  │
//!  │            │                          │   non-reflectable — the split is per-KIND     │
//!  │ `Bind`     │ `^x.p:[Proc -> Proc]`     │ CONTROL ×2: a genuinely unsupported fold      │
//!  │            │                          │   param (still Declined, in                   │
//!  │            │                          │   `describe_term_param`'s exact wording), AND │
//!  │            │                          │   a binder, so "a binder in scope captures the │
//!  │            │                          │   name" is testable rather than assumed       │
//!  └────────────┴──────────────────────────┴──────────────────────────────────────────────┘
//! ```
//!
//! ⚠ `Proc` is NOT native-typed (`![i32] as Proc`). A native-typed category makes the macro
//! emit a stack-safe `try_eval` frame for EVERY rule, and that frame's classifier
//! (`classify_hol_rule_for_pda`) rejects parameter shapes unrelated to this fixture's subject —
//! so a failure here would be attributable to the wrong mechanism. Rholang's own `Proc` is
//! likewise not native-typed.
//!
//! ⚠ Every fold body RECONSTRUCTS rather than merely returning its parameter. An identity body
//! (`p.clone()`) is classified as an INERT GROUPING (`grammar_shapes::classify_inert_grouping_
//! shape`) and routed through the surface-synonymy machinery, which is a different mechanism
//! from the one under test.

// As a `#[path]`-included module this file inherits no crate-level attributes, and each
// consumer exercises a different slice of the generated surface, so `dead_code` /
// `unused_imports` are expected here rather than a signal.
#![allow(
    dead_code,
    unused_imports,
    non_local_definitions,
    clippy::crate_in_macro_def,
    clippy::empty_line_after_outer_attr
)]

use mettail_macros::language;

language! {
    name: TokenTextLeafDemo,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        Proc
    },

    tokens {
        // The guest-body delimiters for `Guest` below — the CONTROL leaf kind. Copied in
        // shape from `languages/tests/l9_flt_toy.rs`, which is the L9-4 gate for this
        // machinery; nothing here tests the FLT lexer itself, only that a `GuestBody` field
        // keeps the lossy, non-invertible, non-reflectable treatment a token-text field loses.
        //
        // ⚠ The fixed explicit selector/category brace form (`box:Proc{`), not a broad
        // backtick-opener regex. This
        // fixture also declares `m:Ident` positions, and an opener whose prefix is an
        // arbitrary lowercase word makes the lexer co-accept `Ident` at every such state —
        // the DFA blow-up `NonTerminalKind::Ident`'s own doc measured and rejected. A
        // reserved tag has no bare-identifier ambiguity at all.
        FltOpenBrace = "box:Proc\\{" push(flt_body_brace) ;

        raw mode flt_body_brace {
            FltCloseBrace = "\\}" pop ;
            GuestChunk = "[^{}]+" ;
        }
    },

    terms {
        Nil . |- "0" : Proc ;

        // ★ THE SUBJECT. A fold whose body reads the CAPTURED NAME and dispatches on it.
        //
        // Before A this fold was DECLINED by the lowering gate, and the declination was
        // accurate: the fold body is lowered against the Dovetail derivation, each parameter
        // is bound through a reconstructor, and an `Ident` field had none because its lowered
        // leaf (`FieldOpaque(format!("{:?}", …))`) had no inverse. A supplies the inverse, so
        // the parameter binds like any other.
        //
        // The body is TOTAL on the name — an unknown name reconstructs the term unchanged
        // rather than returning `None`. `None` would DEFER the fold forever and leave the term
        // stuck, which is a stuck reduction rather than an answer. Any collapsed method
        // surface built on this capability inherits the same obligation.
        Named . m:Ident |- "tag" m : Proc ![{
            match m.as_str() {
                "zero" => Proc::Nil,
                _ => Proc::Named(m.clone()),
            }
        }] fold;

        // Exact optional token text uses the same verbatim token leaf when
        // present and the field-indexed absence leaf when omitted. Both cases
        // must reach the fold body without parsing a display representation.
        MaybeNamed . *opt(m:Ident) |- "maybe-tag" *opt(m) : Proc ;

        // The category-child analogue. A present child remains a typed child
        // derivation; absence is `FieldNone` at this constructor field's exact
        // index. The inverse must preserve the Option boundary in both cases.
        MaybeProc . *opt(p:Proc) |- "maybe-proc" *opt(p) : Proc ;

        // Required and absent-optional category fields deliberately share one
        // constructor. Reconstruction schedules both as deferred actions so
        // the value stack retains declaration order under the LIFO worklist.
        MixedMaybe . head:Proc, *opt(tail:Proc)
            |- "mixed-maybe" "(" head *opt("," tail) ")" : Proc ;

        // Ordered optional containers retain both the Option boundary and
        // element order in their category-labelled sequence leaf.
        MaybeMany . *opt(ps:Vec(Proc))
            |- "maybe-many" *opt("[" ps.*sep(",") "]") : Proc ;

        // A required object parameter makes the fold dispatcher reconstruct
        // its complete child through the generated inverse PDA.  Matching the
        // optional constructors here observes their exact Some/None carriers
        // without pretending optional groups are themselves fold parameters.
        Probe . p:Proc |- "probe" "(" p ")" : Proc ![{
            match p {
                Proc::MaybeNamed(Some(text)) if text == "zero" =>
                    Proc::Named("optional-token-present".to_string()),
                Proc::MaybeNamed(None) =>
                    Proc::Named("optional-token-absent".to_string()),
                Proc::MaybeProc(Some(child)) if matches!(child.as_ref(), Proc::Nil) =>
                    Proc::Named("optional-child-present".to_string()),
                Proc::MaybeProc(None) =>
                    Proc::Named("optional-child-absent".to_string()),
                Proc::MixedMaybe(head, None) if matches!(head.as_ref(), Proc::Nil) =>
                    Proc::Named("mixed-required-then-absent".to_string()),
                Proc::MixedMaybe(head, Some(tail))
                    if matches!(head.as_ref(), Proc::Nil)
                        && matches!(tail.as_ref(), Proc::Nil) =>
                    Proc::Named("mixed-required-then-present".to_string()),
                Proc::MaybeMany(Some(values))
                    if values.len() == 1 && matches!(values.first(), Some(Proc::Nil)) =>
                    Proc::Named("optional-sequence-present".to_string()),
                Proc::MaybeMany(None) =>
                    Proc::Named("optional-sequence-absent".to_string()),
                other => other.clone(),
            }
        }] fold;

        // The MIXED variant: a category child beside a token-text leaf. Its reconstruction
        // needs `Arc::new(build_proc_d(child0)?)` for field 0 and the UNWRAPPED
        // `build_token_text_d(child1)?` for field 1 — the two shapes the per-field builder
        // exists to tell apart. If the builder ever wrapped both the same way this rule would
        // not compile, which is the desired failure mode.
        // ⚠ The body must OBSERVABLY CHANGE the term for at least one input. A fold whose
        // contractum is its own redex merges an e-class with itself, which is a no-op the
        // saturation records as no firing — so a self-reconstructing body proves nothing
        // about whether the reconstruction ran. `Call(Nil, "nth")` folds to a DIFFERENT
        // constructor, and it does so only if BOTH children reconstructed: the `Arc<Proc>`
        // through `build_proc_d` and the bare `String` through `build_token_text_d`.
        Call . recv:Proc, m:Ident |- "call" "(" recv "," m ")" : Proc ![{
            match (recv, m.as_str()) {
                (Proc::Nil, "nth") => Proc::Named("nil-dot-nth".to_string()),
                _ => Proc::Call(std::sync::Arc::new(recv.clone()), m.clone()),
            }
        }] fold;

        // CONTROL: an object-only fold on the same language, in the same walk. Without it,
        // "the token-text fold fired" cannot be told apart from "the fold machinery ran".
        // Its body READS `p` and changes the term for `Wrap(Nil)`, for the same reason
        // `Call`'s does — a self-reconstructing body is unobservable.
        Wrap . p:Proc |- "<" p ">" : Proc ![{
            match p {
                Proc::Nil => Proc::Named("wrapped-nil".to_string()),
                _ => Proc::Wrap(std::sync::Arc::new(p.clone())),
            }
        }] fold;

        // CONTROL: an `OpaqueLeafKind::GuestBody` capture. It must keep lowering to
        // `FieldOpaque` and must keep failing rho-native reflection CLOSED — an `Arc<FltNode>`
        // has no lossless `Debug` inverse and no ground image, so promoting it would be a
        // claim about recoverability rather than a capability.
        Guest . |- *flt(node, FltOpenBrace, FltCloseBrace) : Proc ;

        // CONTROL, and it wears two hats.
        //
        // (a) A BINDER, so the claim "a binder in scope cannot capture a method name" is a
        //     test rather than an assertion. `m:Ident` yields a `String`; only `m:Var` would
        //     yield an `OrdVar`, which `subst` canonicalises under unify.
        //
        // (b) A fold whose parameter is a BINDER ABSTRACTION — genuinely unsupported by the
        //     fold gate, which must still decline it in `describe_term_param`'s exact
        //     wording. Without such a control, "no declination mentions `Ident`" could pass
        //     by the gate having been disabled outright.
        //
        // ⚠ The control was originally a `?g:Guard` slot, which is what the design brief
        // names. It is a binder abstraction instead because a `p:Proc, ?g:Guard` rule hits a
        // PRE-EXISTING, unrelated defect in the WPDA action emitter: it builds
        // `Proc::Guarded(pred, Arc::new(proc))` against an AST variant declared
        // `Guarded(Arc<Proc>, BehavioralPred)` — the two positional arguments are SWAPPED, so
        // the generated language does not compile. That is a guard field-order bug in
        // `wpda_codegen`, not in this capability; a binder abstraction exercises the same
        // gate property (`describe_term_param` names the offender) through machinery this
        // change does touch.
        Bind . ^x.p:[Proc -> Proc] |- "new" x "." p : Proc ![{
            Proc::Wrap(std::sync::Arc::new(p.clone()))
        }] fold;
    },

    equations {},
}
