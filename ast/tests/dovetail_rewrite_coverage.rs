use mettail_ast::language::{BehavioralPred, Condition, Premise};
use mettail_ast::pattern::{Pattern, PatternTerm};
use mettail_ast::types::EvalMode;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Coverage {
    DovetailCore,
    LoweringContract,
    NativeHandlerContract,
}

fn join(left: Coverage, right: Coverage) -> Coverage {
    use Coverage::{DovetailCore, LoweringContract, NativeHandlerContract};

    match (left, right) {
        (NativeHandlerContract, _) | (_, NativeHandlerContract) => NativeHandlerContract,
        (LoweringContract, _) | (_, LoweringContract) => LoweringContract,
        (DovetailCore, DovetailCore) => DovetailCore,
    }
}

fn classify_eval_mode(mode: EvalMode) -> Coverage {
    match mode {
        EvalMode::Fold => Coverage::NativeHandlerContract,
        EvalMode::Step => Coverage::DovetailCore,
    }
}

fn classify_premise(premise: &Premise) -> Coverage {
    match premise {
        Premise::Freshness(_) => Coverage::DovetailCore,
        Premise::Congruence { .. } => Coverage::DovetailCore,
        Premise::RelationQuery { .. } => Coverage::DovetailCore,
        Premise::ForAll { body, .. } => classify_premise(body),
        Premise::BehavioralGuard(pred) => classify_behavioral_pred(pred),
        Premise::SyntheticInjGuard { .. } => Coverage::DovetailCore,
    }
}

fn classify_condition(condition: &Condition) -> Coverage {
    match condition {
        Condition::Freshness(_) => Coverage::DovetailCore,
        Condition::EnvQuery { .. } => Coverage::DovetailCore,
        Condition::ForAll { body, .. } => classify_condition(body),
        Condition::BehavioralGuard(pred) => classify_behavioral_pred(pred),
        Condition::SyntheticInjGuard { .. } => Coverage::DovetailCore,
    }
}

fn classify_behavioral_pred(pred: &BehavioralPred) -> Coverage {
    match pred {
        BehavioralPred::RelationQuery { .. } => Coverage::DovetailCore,
        BehavioralPred::Quantified { body, .. } => {
            join(Coverage::NativeHandlerContract, classify_behavioral_pred(body))
        },
        BehavioralPred::And(left, right)
        | BehavioralPred::Or(left, right)
        | BehavioralPred::Implies(left, right) => {
            join(classify_behavioral_pred(left), classify_behavioral_pred(right))
        },
        BehavioralPred::Not(body) => classify_behavioral_pred(body),
        BehavioralPred::AcMatch { .. } => Coverage::LoweringContract,
        BehavioralPred::Top => Coverage::DovetailCore,
    }
}

fn classify_pattern(pattern: &Pattern) -> Coverage {
    match pattern {
        Pattern::Term(term) => classify_pattern_term(term),
        Pattern::Collection { elements, .. } => elements
            .iter()
            .map(classify_pattern)
            .fold(Coverage::DovetailCore, join),
        Pattern::Map { collection, body, .. } => {
            join(classify_pattern(collection), classify_pattern(body))
        },
        Pattern::Zip { first, second } => join(classify_pattern(first), classify_pattern(second)),
    }
}

fn classify_pattern_term(term: &PatternTerm) -> Coverage {
    match term {
        PatternTerm::Var(_) => Coverage::DovetailCore,
        PatternTerm::Apply { args, .. } => args
            .iter()
            .map(classify_pattern)
            .fold(Coverage::DovetailCore, join),
        PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
            join(Coverage::LoweringContract, classify_pattern(body))
        },
        PatternTerm::Subst { term, replacement, .. } => join(
            Coverage::LoweringContract,
            join(classify_pattern(term), classify_pattern(replacement)),
        ),
        PatternTerm::MultiSubst { scope, replacements } => replacements
            .iter()
            .map(classify_pattern)
            .fold(join(Coverage::LoweringContract, classify_pattern(scope)), join),
    }
}

#[test]
fn rewrite_surface_has_exhaustive_dovetail_coverage_classification() {
    let _premise: fn(&Premise) -> Coverage = classify_premise;
    let _condition: fn(&Condition) -> Coverage = classify_condition;
    let _behavioral_pred: fn(&BehavioralPred) -> Coverage = classify_behavioral_pred;
    let _pattern: fn(&Pattern) -> Coverage = classify_pattern;
    let _pattern_term: fn(&PatternTerm) -> Coverage = classify_pattern_term;

    assert_eq!(classify_eval_mode(EvalMode::Step), Coverage::DovetailCore);
    assert_eq!(classify_eval_mode(EvalMode::Fold), Coverage::NativeHandlerContract);
}
