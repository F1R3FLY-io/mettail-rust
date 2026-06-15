//! Generated scalar invocation planning for Rho-backed languages.
//!
//! `lower_language_def` decides which scalar contracts exist and emits their
//! normalized Rho AST plus [`crate::lower::RhoScalarContractAbi`]. This module
//! derives the generated-language dispatch plan from that same ABI and the
//! macro-expanded [`LanguageDef`]. It does not inspect display strings.

use std::collections::BTreeMap;

use mettail_ast::grammar::{GrammarRule, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::TypeExpr;

use crate::{
    ast::RhoAstLiteral,
    lower::{
        category_rho_native_scalar, rho_native_scalar_type, RhoLowering, RhoScalarContractAbi,
        RhoScalarContractShape, RhoScalarType,
    },
};

/// One operand that generated invocation code must extract from a typed term
/// constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoScalarInvocationOperand {
    pub field_position: usize,
    pub parameter_name: String,
    pub category: String,
    pub scalar_type: RhoScalarType,
}

/// Dispatch plan for one generated scalar contract call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoScalarInvocationPlan {
    pub rule_label: String,
    pub result_category: String,
    pub result_scalar_type: RhoScalarType,
    pub abi: RhoScalarContractAbi,
    pub operands: Vec<RhoScalarInvocationOperand>,
}

/// Dynamic scalar-contract call emitted by generated language code.
///
/// This type intentionally lives in `mettail-rho-codegen`, not
/// `mettail-rho-runtime`, so generated language crates can compile an AST-first
/// invocation description without depending on the Rho machine runtime. Runtime
/// adapters validate and normalize this payload with
/// `mettail_rho_runtime::build_scalar_contract_invocation_from_contract`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoScalarContractInvocation {
    pub abi: RhoScalarContractAbi,
    pub arguments: Vec<RhoAstLiteral>,
    pub out_channel: String,
}

impl RhoScalarContractInvocation {
    pub fn new(
        abi: RhoScalarContractAbi,
        arguments: Vec<RhoAstLiteral>,
        out_channel: impl Into<String>,
    ) -> Self {
        Self {
            abi,
            arguments,
            out_channel: out_channel.into(),
        }
    }
}

/// Inconsistency between a `LanguageDef` and the scalar ABI inventory derived
/// from it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RhoScalarInvocationPlanError {
    MissingRule {
        rule_label: String,
    },
    MissingTermContext {
        rule_label: String,
    },
    UnsupportedOperandShape {
        rule_label: String,
        field_position: usize,
    },
    NonBaseOperandType {
        rule_label: String,
        field_position: usize,
    },
    OperandCountMismatch {
        rule_label: String,
        expected: usize,
        actual: usize,
    },
    OperandTypeMismatch {
        rule_label: String,
        field_position: usize,
        expected: RhoScalarType,
        actual: Option<RhoScalarType>,
    },
    ResultTypeMismatch {
        rule_label: String,
        expected: RhoScalarType,
        actual: Option<RhoScalarType>,
    },
}

fn base_category_name(ty: &TypeExpr) -> Option<String> {
    match ty {
        TypeExpr::Base(category) => Some(category.to_string()),
        _ => None,
    }
}

fn expected_operand_types(shape: RhoScalarContractShape) -> Vec<RhoScalarType> {
    match shape {
        RhoScalarContractShape::UnaryPrefix { argument, .. } => vec![argument],
        RhoScalarContractShape::BinaryInfix { left, right, .. } => vec![left, right],
    }
}

fn rule_by_label(def: &LanguageDef) -> BTreeMap<String, &GrammarRule> {
    def.terms
        .iter()
        .map(|rule| (rule.label.to_string(), rule))
        .collect()
}

/// Derive the generated-language scalar invocation plan from the same
/// `LanguageDef` and `RhoLowering` that selected the Rho backend.
pub fn plan_scalar_invocations(
    def: &LanguageDef,
    lowering: &RhoLowering,
) -> Result<Vec<RhoScalarInvocationPlan>, RhoScalarInvocationPlanError> {
    let rules = rule_by_label(def);
    let mut plans = Vec::with_capacity(lowering.scalar_contract_abi.len());

    for abi in &lowering.scalar_contract_abi {
        let rule_label = abi.rule_label.clone();
        let rule =
            rules
                .get(&rule_label)
                .ok_or_else(|| RhoScalarInvocationPlanError::MissingRule {
                    rule_label: rule_label.clone(),
                })?;
        let term_context = rule.term_context.as_ref().ok_or_else(|| {
            RhoScalarInvocationPlanError::MissingTermContext { rule_label: rule_label.clone() }
        })?;
        let expected = expected_operand_types(abi.shape);
        if term_context.len() != expected.len() {
            return Err(RhoScalarInvocationPlanError::OperandCountMismatch {
                rule_label,
                expected: expected.len(),
                actual: term_context.len(),
            });
        }

        let mut operands = Vec::with_capacity(expected.len());
        for (field_position, (param, expected_scalar_type)) in term_context
            .iter()
            .zip(expected.iter().copied())
            .enumerate()
        {
            let TermParam::Simple { name, ty } = param else {
                return Err(RhoScalarInvocationPlanError::UnsupportedOperandShape {
                    rule_label: abi.rule_label.clone(),
                    field_position,
                });
            };
            let category = base_category_name(ty).ok_or_else(|| {
                RhoScalarInvocationPlanError::NonBaseOperandType {
                    rule_label: abi.rule_label.clone(),
                    field_position,
                }
            })?;
            let actual_scalar_type = rho_native_scalar_type(def, ty);
            if actual_scalar_type != Some(expected_scalar_type) {
                return Err(RhoScalarInvocationPlanError::OperandTypeMismatch {
                    rule_label: abi.rule_label.clone(),
                    field_position,
                    expected: expected_scalar_type,
                    actual: actual_scalar_type,
                });
            }
            operands.push(RhoScalarInvocationOperand {
                field_position,
                parameter_name: name.to_string(),
                category,
                scalar_type: expected_scalar_type,
            });
        }

        let actual_result_type = category_rho_native_scalar(def, &rule.category);
        if actual_result_type != Some(abi.result_type()) {
            return Err(RhoScalarInvocationPlanError::ResultTypeMismatch {
                rule_label: abi.rule_label.clone(),
                expected: abi.result_type(),
                actual: actual_result_type,
            });
        }

        plans.push(RhoScalarInvocationPlan {
            rule_label: abi.rule_label.clone(),
            result_category: rule.category.to_string(),
            result_scalar_type: abi.result_type(),
            abi: abi.clone(),
            operands,
        });
    }

    Ok(plans)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower::{lower_language_def, RhoScalarContractAbi, RhoScalarContractShape};

    const CALC_SCALAR_FRAGMENT: &str = r#"
        name: CalcScalarFrag,
        types {
            ![i32] as Int
            ![bool] as Bool
            ![str] as Str
        }
        terms {
            AddInt . a:Int, b:Int |- a "+" b : Int ;
            Not . a:Bool |- "not" a : Bool ;
            AddStr . a:Str, b:Str |- a "+" b : Str ;
        }
    "#;

    const RENAMED_NATIVE_SCALAR_FRAGMENT: &str = r#"
        name: RenamedScalarFrag,
        types {
            ![i32] as Number
            ![bool] as Truth
            ![str] as Text
        }
        terms {
            AddNumber . a:Number, b:Number |- a "+" b : Number ;
            EqNumber . a:Number, b:Number |- a "==" b : Truth ;
            AddText . a:Text, b:Text |- a "+" b : Text ;
        }
    "#;

    const SCALAR_NAMED_STRUCTURAL_FRAGMENT: &str = r#"
        name: ScalarNamedStructuralFrag,
        types {
            Int
            Bool
            Str
        }
        terms {
            AddInt . a:Int, b:Int |- a "+" b : Int ;
            Not . a:Bool |- "not" a : Bool ;
            AddStr . a:Str, b:Str |- a "+" b : Str ;
        }
    "#;

    fn parse(fragment: &str) -> LanguageDef {
        syn::parse_str::<LanguageDef>(fragment).expect("fragment must parse")
    }

    #[test]
    fn scalar_invocation_plan_follows_lowering_abi_order() {
        let def = parse(CALC_SCALAR_FRAGMENT);
        let lowering = lower_language_def(&def);
        let plans =
            plan_scalar_invocations(&def, &lowering).expect("lowering ABI must plan cleanly");

        assert_eq!(
            plans
                .iter()
                .map(|plan| plan.rule_label.as_str())
                .collect::<Vec<_>>(),
            vec!["AddInt", "Not", "AddStr"]
        );
        assert_eq!(plans[0].result_category, "Int");
        assert_eq!(plans[0].result_scalar_type, RhoScalarType::Int);
        assert_eq!(
            plans[0].operands,
            vec![
                RhoScalarInvocationOperand {
                    field_position: 0,
                    parameter_name: "a".to_string(),
                    category: "Int".to_string(),
                    scalar_type: RhoScalarType::Int,
                },
                RhoScalarInvocationOperand {
                    field_position: 1,
                    parameter_name: "b".to_string(),
                    category: "Int".to_string(),
                    scalar_type: RhoScalarType::Int,
                },
            ]
        );
        assert_eq!(
            plans[1].operands,
            vec![RhoScalarInvocationOperand {
                field_position: 0,
                parameter_name: "a".to_string(),
                category: "Bool".to_string(),
                scalar_type: RhoScalarType::Bool,
            }]
        );
        assert_eq!(plans[2].result_scalar_type, RhoScalarType::Str);
        assert_eq!(
            plans[2].abi.shape,
            RhoScalarContractShape::BinaryInfix {
                left: RhoScalarType::Str,
                right: RhoScalarType::Str,
                result: RhoScalarType::Str,
            }
        );
    }

    #[test]
    fn scalar_invocation_plan_uses_native_payloads_not_category_names() {
        let def = parse(RENAMED_NATIVE_SCALAR_FRAGMENT);
        let lowering = lower_language_def(&def);
        let plans = plan_scalar_invocations(&def, &lowering).expect("renamed native ABI must plan");

        assert_eq!(
            plans
                .iter()
                .map(|plan| (
                    plan.rule_label.as_str(),
                    plan.result_category.as_str(),
                    plan.result_scalar_type
                ))
                .collect::<Vec<_>>(),
            vec![
                ("AddNumber", "Number", RhoScalarType::Int),
                ("EqNumber", "Truth", RhoScalarType::Bool),
                ("AddText", "Text", RhoScalarType::Str),
            ]
        );
        assert_eq!(plans[2].operands[0].category, "Text");
        assert_eq!(plans[2].operands[0].scalar_type, RhoScalarType::Str);
    }

    #[test]
    fn scalar_invocation_plan_has_no_entries_for_rejected_structural_categories() {
        let def = parse(SCALAR_NAMED_STRUCTURAL_FRAGMENT);
        let lowering = lower_language_def(&def);
        assert!(lowering.scalar_contract_abi.is_empty());
        let plans =
            plan_scalar_invocations(&def, &lowering).expect("empty ABI inventory should plan");
        assert!(plans.is_empty());
    }

    #[test]
    fn scalar_invocation_plan_rejects_abi_language_drift() {
        let def = parse(CALC_SCALAR_FRAGMENT);
        let mut lowering = lower_language_def(&def);
        lowering.scalar_contract_abi.push(RhoScalarContractAbi {
            rule_label: "MissingRule".to_string(),
            shape: RhoScalarContractShape::UnaryPrefix {
                argument: RhoScalarType::Int,
                result: RhoScalarType::Int,
            },
        });

        let err = plan_scalar_invocations(&def, &lowering)
            .expect_err("stale ABI labels must fail planning");
        assert_eq!(
            err,
            RhoScalarInvocationPlanError::MissingRule { rule_label: "MissingRule".to_string() }
        );
    }
}
