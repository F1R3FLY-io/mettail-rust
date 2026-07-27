//! **G3 — additive inertness.** The standing witness that adding a `language!` whose
//! requirements are ALREADY covered requires no hand edit anywhere else.
//!
//! # What used to happen, and why it was worth removing
//!
//! Both specification audits asserted that the set of language names they discovered
//! EQUALLED the names written out in
//! `dovetail/formal/rocq/theories/Requirements/LanguageDefInventory.v`. Adding a language
//! therefore turned a Rocq-facing test red for a purely clerical reason: no proof in that
//! file depends on a name — they range over the requirements — so the failure carried no
//! formal content, and the remedy was to paste a line into a `.v` file. That is a bad
//! thing to teach about a formal gate, because it makes "edit the proof file until the
//! test goes green" the normal response to one going red.
//!
//! Task #69 S5 split the mechanical half out into `LanguageDefInventoryGenerated.v`, which
//! is DERIVED from the declarations and regenerated with `METTAIL_BLESS=1`. What remains
//! asserted is the property that carries content: every requirement the corpus declares
//! lies inside the taxonomy Rocq proves covered.
//!
//! # Why a canary rather than a comment
//!
//! "Adding a covered language is inert" is a claim about what does NOT happen, and claims
//! of that shape rot silently — nothing fails when they stop being true, because nobody
//! adds a language on the day the coupling is reintroduced. `AdditiveInertnessCanary` is a
//! language that HAS been added and is deliberately absent from the hand-written formal
//! file. `dovetail/tests/language_inventory.rs::adding_a_covered_language_is_inert` checks
//! both halves of the claim against it on every run.
//!
//! If someone reinstates name-level equality, this canary is what fails, immediately and
//! by name, instead of the next person to add a language discovering the coupling the hard
//! way.
//!
//! # Why it declares what it declares
//!
//! One native carrier and one directional `step` rewrite: the smallest language that
//! classifies to a NON-EMPTY requirement set (both audits reject a language that
//! classifies to nothing), and whose single requirement — `ReqDirectionalRewrite` — is the
//! most thoroughly covered one in the taxonomy. Being minimal keeps its macro expansion
//! cheap; being real keeps it from rotting into an unexercised fixture, which is why it is
//! parsed and evaluated below.
//!
//! It emits no tests, no simulator and no Blockly output, so it also adds nothing for
//! `macros/tests/generated_output_locality.rs` to find outside `target/`.

#![allow(unused_imports, dead_code)]

use mettail_macros::language;
use mettail_runtime::Language;

language! {
    name: AdditiveInertnessCanary,

    options {
        emit_tests: false,
        emit_simulator: false,
        emit_blockly: false,
    },

    types {
        ![i64] as Count
    },

    terms {
        Bump . a:Count |- "bump" a : Count ;
    },

    equations {
    },

    rewrites {
        BumpStep . |- (Bump a) ~> a ;
    },
}

#[test]
fn the_canary_language_is_real() {
    assert_eq!(AdditiveInertnessCanaryLanguage.name(), "AdditiveInertnessCanary");
    let metadata = AdditiveInertnessCanaryLanguage.metadata();
    assert!(
        !metadata.terms().is_empty(),
        "the canary must carry a term, or it classifies to no requirement and both audits \
         reject it for the wrong reason"
    );
}
