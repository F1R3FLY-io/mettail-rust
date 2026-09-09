//! Shared, node-independent guard-obligation analysis.

use std::collections::BTreeSet;

use crate::grammar::{GrammarRule, TermParam};
use crate::language::{
    BehavioralPred, GuardConfig, GuardSlotDecl, LanguageDef, Premise, RewriteRule,
};
#[cfg(test)]
use crate::types::TypeExpr;

/// Class of predicated-type / guard obligation induced by a `LanguageDef`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RhoGuardObligationKind {
    /// Runtime predicate over matched values, facts, channels, or named
    /// predicate relations.
    BehavioralPredicate,
    /// Structural pattern predicate such as AC matching, binding shape, or
    /// guarded rewrite pattern structure.
    StructuralPattern,
    /// Registered predicate theory that must supply an effective Boolean
    /// algebra or an equivalent verified theory adapter.
    TheoryRegistration,
    /// Rho-native guarded receive/join/channel scheduling obligation.
    RhoNativeJoin,
}

/// One guard/predicated-type obligation that must be covered before the Rho
/// backend may become the default runtime for a language.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RhoGuardObligation {
    pub id: String,
    pub kind: RhoGuardObligationKind,
}

impl RhoGuardObligation {
    fn new(id: impl Into<String>, kind: RhoGuardObligationKind) -> Self {
        Self { id: id.into(), kind }
    }
}

fn pred_has_structural_component(pred: &BehavioralPred) -> bool {
    let mut work = vec![pred];
    while let Some(pred) = work.pop() {
        match pred {
            BehavioralPred::AcMatch { .. } => return true,
            BehavioralPred::Quantified { body, .. } | BehavioralPred::Not(body) => {
                work.push(body);
            },
            BehavioralPred::And(left, right)
            | BehavioralPred::Or(left, right)
            | BehavioralPred::Implies(left, right) => {
                work.push(right);
                work.push(left);
            },
            BehavioralPred::RelationQuery { .. } | BehavioralPred::Top => {},
        }
    }
    false
}

fn guard_pred_obligation_kind(pred: &BehavioralPred) -> RhoGuardObligationKind {
    if pred_has_structural_component(pred) {
        RhoGuardObligationKind::StructuralPattern
    } else {
        RhoGuardObligationKind::BehavioralPredicate
    }
}

/// Induce the guard obligations of one `terms { }` rule.
///
/// A term parameter is a semantic-predicate slot in exactly two ways, and both induce the SAME
/// obligation id — `term:<Label>:guard:<param>` — so no downstream consumer can tell them apart:
///
/// | surface | how it is recognized |
/// |---|---|
/// | `?param:Guard` | by its **type**: a [`TermParam::GuardBody`] |
/// | `param:SomeCategory` + a `guards { guard_slots { Label(param); } }` declaration | by the author's **declaration** |
///
/// The second exists for a language whose guard sublanguage IS its own expression language.
/// Rholang's `where` is the case: its guard is an ordinary `Proc`, which is what keeps
/// `where x + y < 10` and `where t matches {phi | psi}` writable — neither is expressible as a
/// `BehavioralPred`, whose grammar is relation queries, quantifiers and AC-matches with no
/// comparison, no arithmetic and no nesting inside arguments. Retyping the slot to `Guard` would
/// therefore not "make the guard a semantic predicate"; it would delete most of the guard
/// language. The declaration says the same thing without the loss.
///
/// ★ It is a DECLARATION, never an inference. Nothing here reads the rule's syntax form, so no
/// `"where"` literal and no parameter *name* is load-bearing — recognition by spelling is the
/// drift this tree forbids, and `rholang/formula.rs` states the rule outright:
/// *"Recognition is by CONSTRUCTOR, never by spelling."*
fn collect_term_guard_obligations(
    rule: &GrammarRule,
    declared_slots: &[GuardSlotDecl],
    out: &mut BTreeSet<RhoGuardObligation>,
) {
    if let Some(params) = rule.term_context.as_ref() {
        let label = rule.label.to_string();
        let declared: BTreeSet<String> = declared_slots
            .iter()
            .filter(|decl| decl.label == label)
            .map(|decl| decl.param.to_string())
            .collect();
        collect_term_param_guard_obligations(&label, params, &declared, out);
    }
}

fn collect_term_param_guard_obligations(
    label: &str,
    params: &[TermParam],
    declared: &BTreeSet<String>,
    out: &mut BTreeSet<RhoGuardObligation>,
) {
    let mut work: Vec<_> = params.iter().rev().collect();
    while let Some(param) = work.pop() {
        match param {
            TermParam::GuardBody { name } => {
                out.insert(RhoGuardObligation::new(
                    format!("term:{label}:guard:{name}"),
                    RhoGuardObligationKind::BehavioralPredicate,
                ));
            },
            // A category-typed parameter the author DECLARED to be a guard slot.
            TermParam::Simple { name, .. } if declared.contains(&name.to_string()) => {
                out.insert(RhoGuardObligation::new(
                    format!("term:{label}:guard:{name}"),
                    RhoGuardObligationKind::BehavioralPredicate,
                ));
            },
            TermParam::Optional { params } => work.extend(params.iter().rev()),
            TermParam::Simple { .. }
            | TermParam::Abstraction { .. }
            | TermParam::MultiAbstraction { .. } => {},
        }
    }
}

fn collect_premise_guard_obligations(
    owner_kind: &str,
    owner_name: &str,
    premises: &[Premise],
    out: &mut BTreeSet<RhoGuardObligation>,
) {
    for (index, premise) in premises.iter().enumerate() {
        let mut premise = premise;
        loop {
            match premise {
                Premise::ForAll { body, .. } => premise = body,
                Premise::BehavioralGuard(pred) => {
                    out.insert(RhoGuardObligation::new(
                        format!("{owner_kind}:{owner_name}:guard:{index}"),
                        guard_pred_obligation_kind(pred),
                    ));
                    break;
                },
                // ★ (#195) `CongruenceWithheld` carries no guard obligation for the same
                // reason `Congruence` does not: neither is a semantic predicate. It is
                // listed explicitly (not defaulted) so the day a polarity acquires an
                // obligation, the compiler asks about BOTH.
                Premise::Freshness(_)
                | Premise::Congruence { .. }
                | Premise::CongruenceWithheld { .. }
                | Premise::RelationQuery { .. }
                | Premise::SyntheticInjGuard { .. } => break,
            }
        }
    }
}

fn collect_rewrite_guard_obligations(
    rewrite: &RewriteRule,
    out: &mut BTreeSet<RhoGuardObligation>,
) {
    collect_premise_guard_obligations("rewrite", &rewrite.name.to_string(), &rewrite.premises, out);
}

/// `true` iff the language can actually reach the built-in predicate vocabulary.
///
/// The vocabulary is consumed by the **predicate sublanguage**, and the only way into that
/// sublanguage is a `?name:Guard` term parameter — a `TermParam::GuardBody`, which lowers to the
/// parser's `GuardExpression` item. A language with no such slot never parses a predicate, so
/// there is no built-in-predicate work to induce an obligation for.
fn language_reaches_the_builtin_predicate_vocabulary(def: &LanguageDef) -> bool {
    def.terms
        .iter()
        .filter_map(|rule| rule.term_context.as_ref())
        .any(|params| params_have_guard_body(params))
}

fn params_have_guard_body(params: &[TermParam]) -> bool {
    let mut work: Vec<_> = params.iter().collect();
    while let Some(param) = work.pop() {
        match param {
            TermParam::GuardBody { .. } => return true,
            TermParam::Optional { params } => work.extend(params),
            TermParam::Simple { .. }
            | TermParam::Abstraction { .. }
            | TermParam::MultiAbstraction { .. } => {},
        }
    }
    false
}

#[cfg(test)]
#[path = "../../tests/support/guard_obligations_recursive_oracle.rs"]
mod recursive_oracle;

fn collect_guard_config_obligations(
    guard_config: &GuardConfig,
    reaches_builtin_vocabulary: bool,
    out: &mut BTreeSet<RhoGuardObligation>,
) {
    match guard_config.builtin_predicates.as_ref() {
        Some(predicates) => {
            for predicate in predicates {
                out.insert(RhoGuardObligation::new(
                    format!("predicate:{}", predicate.name),
                    RhoGuardObligationKind::BehavioralPredicate,
                ));
            }
        },
        // ★ OPEN-WORLD built-ins — but only where they are REACHABLE (2026-07-26).
        //
        // The `None` arm means "the standard built-in predicates are available to the predicate
        // sublanguage", and that is a claim about the sublanguage, not about the `guards { }`
        // block. Firing it for the mere PRESENCE of a block conflated two different facts, and
        // the conflation surfaced the moment a language declared a `guards { }` block for
        // something else: Rholang's `guard_slots` declaration induced an uncovered
        // `predicate:standard-builtins` obligation for a vocabulary it cannot reach, because it
        // has no `?name:Guard` slot and therefore never enters the predicate sublanguage.
        //
        // Every language that DOES have such a slot is unaffected — GuardedRho still induces it —
        // and every language with explicit built-ins takes the `Some` arm above.
        None if reaches_builtin_vocabulary => {
            out.insert(RhoGuardObligation::new(
                "predicate:standard-builtins",
                RhoGuardObligationKind::BehavioralPredicate,
            ));
        },
        None => {},
    }

    for theory in &guard_config.theories {
        out.insert(RhoGuardObligation::new(
            format!("theory:{}", theory.name),
            RhoGuardObligationKind::TheoryRegistration,
        ));
    }

    if let Some(channels) = guard_config.channels.as_ref() {
        for channel in &channels.channel_categories {
            out.insert(RhoGuardObligation::new(
                format!("channel:{}", channel.category),
                RhoGuardObligationKind::RhoNativeJoin,
            ));
        }
        for join in &channels.join_patterns {
            out.insert(RhoGuardObligation::new(
                format!("join:{}", join.label),
                RhoGuardObligationKind::RhoNativeJoin,
            ));
        }
    }
}

/// Collect the exact guard/predicated-type obligation set induced by a
/// `LanguageDef`.
pub fn collect_guard_obligations(def: &LanguageDef) -> Vec<RhoGuardObligation> {
    let mut obligations = BTreeSet::new();

    if let Some(guard_config) = def.guard_config.as_ref() {
        collect_guard_config_obligations(
            guard_config,
            language_reaches_the_builtin_predicate_vocabulary(def),
            &mut obligations,
        );
    }

    let declared_guard_slots: &[GuardSlotDecl] = def
        .guard_config
        .as_ref()
        .map_or(&[], |config| config.guard_slots.as_slice());
    for rule in &def.terms {
        collect_term_guard_obligations(rule, declared_guard_slots, &mut obligations);
    }
    for equation in &def.equations {
        collect_premise_guard_obligations(
            "equation",
            &equation.name.to_string(),
            &equation.premises,
            &mut obligations,
        );
    }
    for rewrite in &def.rewrites {
        collect_rewrite_guard_obligations(rewrite, &mut obligations);
    }

    obligations.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::language::{ChannelConfig, ChannelDecl, JoinPatternDecl};

    fn ident(value: &str) -> syn::Ident {
        syn::parse_str(value).expect("test identifier must parse")
    }

    fn plain_language() -> LanguageDef {
        syn::parse_str(
            r#"
            name: PureGuardAnalysis,
            types { Proc },
            terms { Check . q:Proc |- "check" q : Proc; }
        "#,
        )
        .expect("guard analysis fixture must parse")
    }

    #[test]
    fn ordinary_category_slot_requires_declaration_not_spelling() {
        let mut def = plain_language();
        assert!(collect_guard_obligations(&def).is_empty());
        def.guard_config = Some(GuardConfig::default());
        assert!(collect_guard_obligations(&def).is_empty());
        def.guard_config
            .as_mut()
            .expect("config exists")
            .guard_slots
            .push(GuardSlotDecl { label: ident("Check"), param: ident("q") });
        assert_eq!(
            collect_guard_obligations(&def),
            vec![RhoGuardObligation::new(
                "term:Check:guard:q",
                RhoGuardObligationKind::BehavioralPredicate,
            )]
        );
    }

    #[test]
    fn standard_builtins_require_reachable_guard_body_and_open_configuration() {
        let mut def = plain_language();
        def.guard_config = Some(GuardConfig::default());
        def.terms[0].term_context = Some(vec![TermParam::Optional {
            params: vec![TermParam::GuardBody { name: ident("q") }],
        }]);
        assert_eq!(
            collect_guard_obligations(&def),
            vec![
                RhoGuardObligation::new(
                    "predicate:standard-builtins",
                    RhoGuardObligationKind::BehavioralPredicate
                ),
                RhoGuardObligation::new(
                    "term:Check:guard:q",
                    RhoGuardObligationKind::BehavioralPredicate
                ),
            ]
        );
        def.guard_config
            .as_mut()
            .expect("config exists")
            .builtin_predicates = Some(vec![]);
        assert_eq!(
            collect_guard_obligations(&def),
            vec![RhoGuardObligation::new(
                "term:Check:guard:q",
                RhoGuardObligationKind::BehavioralPredicate,
            )]
        );
    }

    #[test]
    fn guard_roster_is_sorted_and_deduplicated_across_declarations() {
        let mut def = plain_language();
        let slot = GuardSlotDecl { label: ident("Check"), param: ident("q") };
        def.guard_config = Some(GuardConfig {
            guard_slots: vec![slot.clone(), slot],
            channels: Some(ChannelConfig {
                channel_categories: vec![
                    ChannelDecl { category: ident("Z") },
                    ChannelDecl { category: ident("A") },
                    ChannelDecl { category: ident("Z") },
                ],
                join_patterns: vec![JoinPatternDecl {
                    label: ident("Check"),
                    channel_params: vec![],
                }],
            }),
            ..GuardConfig::default()
        });
        def.terms.push(def.terms[0].clone());
        let expected = vec![
            RhoGuardObligation::new("channel:A", RhoGuardObligationKind::RhoNativeJoin),
            RhoGuardObligation::new("channel:Z", RhoGuardObligationKind::RhoNativeJoin),
            RhoGuardObligation::new("join:Check", RhoGuardObligationKind::RhoNativeJoin),
            RhoGuardObligation::new(
                "term:Check:guard:q",
                RhoGuardObligationKind::BehavioralPredicate,
            ),
        ];
        assert_eq!(collect_guard_obligations(&def), expected);
        def.guard_config
            .as_mut()
            .expect("config exists")
            .channels
            .as_mut()
            .expect("channels exist")
            .channel_categories
            .reverse();
        def.terms.reverse();
        assert_eq!(collect_guard_obligations(&def), expected);
    }
}
