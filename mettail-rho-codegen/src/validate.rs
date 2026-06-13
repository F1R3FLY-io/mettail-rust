//! Validation for generated Rho backend artifacts.
//!
//! Direct `RhoRuntime::inj` bypasses the source parser/normalizer, so codegen
//! must own the normalized-`Par` invariants it relies on. This validator checks
//! the scalar-contract artifact emitted by `lower_language_def`.

use models::create_bit_vector;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::var::VarInstance;
use models::rhoapi::{Par, Receive, ReceiveBind};

use crate::lower::{RhoArtifactKind, RhoAstProgram, RhoProgram};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RhoValidationError {
    TopLevelHasNonContractProcess,
    TopLevelMetadataMismatch,
    ContractNotPersistent { index: usize },
    ContractHasPeek { index: usize },
    ContractHasCondition { index: usize },
    ContractMetadataMismatch { index: usize },
    ContractBindCountMismatch { index: usize },
    ContractBindShape { index: usize },
    ContractSourceNotGroundString { index: usize },
    ContractSourceMetadataMismatch { index: usize },
    ContractPatternMismatch { index: usize },
    ContractPatternMetadataMismatch { index: usize },
    ContractBodyShape { index: usize },
    ContractBodyMetadataMismatch { index: usize },
    ContractReturnChannelNotNewestBinding { index: usize },
    ContractReturnChannelMetadataMismatch { index: usize },
    ContractResultShape { index: usize },
    ContractResultMetadataMismatch { index: usize },
    ContractOperandMetadataMismatch { index: usize },
}

#[derive(Debug, Clone, PartialEq)]
pub struct ValidatedRhoAstProgram {
    par: Par,
    text_annotation: String,
}

impl ValidatedRhoAstProgram {
    pub fn par(&self) -> &Par {
        &self.par
    }

    /// Reader/debug annotation. This text is not parsed as the execution path.
    pub fn text_annotation(&self) -> &str {
        &self.text_annotation
    }
}

impl From<RhoAstProgram> for ValidatedRhoAstProgram {
    fn from(program: RhoAstProgram) -> Self {
        Self {
            par: program.par,
            text_annotation: program.text_annotation,
        }
    }
}

/// Rho artifact whose generated shape has passed codegen validation.
///
/// Production generated-backend execution should consume this typestate instead
/// of arbitrary `Par`. Low-level raw-`Par` execution remains available in
/// `mettail-rho-runtime` for host oracle tests and debugging.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq)]
pub enum ValidatedRhoProgram {
    Ast(ValidatedRhoAstProgram),
}

impl ValidatedRhoProgram {
    pub fn artifact_kind(&self) -> RhoArtifactKind {
        match self {
            Self::Ast(_) => RhoArtifactKind::NormalizedAst,
        }
    }

    pub fn ast_par(&self) -> Option<&Par> {
        match self {
            Self::Ast(program) => Some(program.par()),
        }
    }

    /// Reader/debug annotation. This text is not parsed as the execution path.
    pub fn text_annotation(&self) -> &str {
        match self {
            Self::Ast(program) => program.text_annotation(),
        }
    }
}

impl TryFrom<RhoProgram> for ValidatedRhoProgram {
    type Error = Vec<RhoValidationError>;

    fn try_from(program: RhoProgram) -> Result<Self, Self::Error> {
        validate_rho_program(&program)?;
        match program {
            RhoProgram::Ast(ast) => Ok(Self::Ast(ast.into())),
        }
    }
}

pub fn validate_rho_program(program: &RhoProgram) -> Result<(), Vec<RhoValidationError>> {
    match program {
        RhoProgram::Ast(ast) => validate_contract_program(ast.par()),
    }
}

fn validate_contract_program(par: &Par) -> Result<(), Vec<RhoValidationError>> {
    let mut errors = Vec::new();
    if !par.sends.is_empty()
        || !par.news.is_empty()
        || !par.exprs.is_empty()
        || !par.matches.is_empty()
        || !par.bundles.is_empty()
        || !par.unforgeables.is_empty()
        || !par.connectives.is_empty()
        || !par.conditionals.is_empty()
    {
        errors.push(RhoValidationError::TopLevelHasNonContractProcess);
    }
    if !par.locally_free.is_empty() || par.connective_used {
        errors.push(RhoValidationError::TopLevelMetadataMismatch);
    }

    for (index, receive) in par.receives.iter().enumerate() {
        validate_receive(index, receive, &mut errors);
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn validate_receive(index: usize, receive: &Receive, errors: &mut Vec<RhoValidationError>) {
    if !receive.persistent {
        errors.push(RhoValidationError::ContractNotPersistent { index });
    }
    if receive.peek {
        errors.push(RhoValidationError::ContractHasPeek { index });
    }
    if receive.condition.is_some() {
        errors.push(RhoValidationError::ContractHasCondition { index });
    }
    if !receive.locally_free.is_empty() || receive.connective_used {
        errors.push(RhoValidationError::ContractMetadataMismatch { index });
    }

    let [bind] = receive.binds.as_slice() else {
        errors.push(RhoValidationError::ContractBindShape { index });
        return;
    };
    let formal_count = validate_bind_shape(index, receive, bind, errors);
    match bind.source.as_ref() {
        Some(source) => {
            if !metadata_eq(source, &[], false) {
                errors.push(RhoValidationError::ContractSourceMetadataMismatch { index });
            }
            if ground_string(source).is_none() {
                errors.push(RhoValidationError::ContractSourceNotGroundString { index });
            }
        },
        None => errors.push(RhoValidationError::ContractSourceNotGroundString { index }),
    }
    for (expected, pattern) in bind.patterns.iter().enumerate() {
        if !metadata_eq(pattern, &[], true) {
            errors.push(RhoValidationError::ContractPatternMetadataMismatch { index });
            break;
        }
        if free_var_index(pattern) != Some(expected as i32) {
            errors.push(RhoValidationError::ContractPatternMismatch { index });
            break;
        }
    }

    let Some(formal_count) = formal_count else {
        return;
    };
    let Some(body) = receive.body.as_ref() else {
        errors.push(RhoValidationError::ContractBodyShape { index });
        return;
    };
    let all_formals = all_formal_bits(formal_count);
    if !metadata_eq(body, &all_formals, false) || !only_sends(body) {
        errors.push(RhoValidationError::ContractBodyMetadataMismatch { index });
    }
    let [send] = body.sends.as_slice() else {
        errors.push(RhoValidationError::ContractBodyShape { index });
        return;
    };
    if send.persistent || send.data.len() != 1 {
        errors.push(RhoValidationError::ContractBodyShape { index });
    }
    match send.chan.as_ref() {
        Some(chan) => {
            if !metadata_eq(chan, &bitvec(&[0]), false) {
                errors.push(RhoValidationError::ContractReturnChannelMetadataMismatch { index });
            }
            if bound_var_index(Some(chan)) != Some(0) {
                errors.push(RhoValidationError::ContractReturnChannelNotNewestBinding { index });
            }
        },
        None => errors.push(RhoValidationError::ContractReturnChannelNotNewestBinding { index }),
    }
    if send.locally_free != all_formals || send.connective_used {
        errors.push(RhoValidationError::ContractBodyMetadataMismatch { index });
    }

    let [result] = send.data.as_slice() else {
        errors.push(RhoValidationError::ContractBodyShape { index });
        return;
    };
    validate_result_expr(index, formal_count, result, errors);
}

fn validate_bind_shape(
    index: usize,
    receive: &Receive,
    bind: &ReceiveBind,
    errors: &mut Vec<RhoValidationError>,
) -> Option<usize> {
    let bind_count = usize::try_from(receive.bind_count).ok();
    let free_count = usize::try_from(bind.free_count).ok();

    let mut is_valid = true;
    if bind_count.is_none()
        || free_count.is_none()
        || bind_count != free_count
        || bind_count == Some(0)
    {
        errors.push(RhoValidationError::ContractBindCountMismatch { index });
        is_valid = false;
    }

    match free_count {
        Some(count) if bind.patterns.len() == count && bind.remainder.is_none() => {},
        _ => {
            errors.push(RhoValidationError::ContractBindShape { index });
            is_valid = false;
        },
    }

    is_valid.then_some(bind_count?)
}

fn validate_result_expr(
    index: usize,
    formal_count: usize,
    result: &Par,
    errors: &mut Vec<RhoValidationError>,
) {
    let Some(expr) = only_expr_instance(result) else {
        errors.push(RhoValidationError::ContractResultShape { index });
        return;
    };

    match expr {
        ExprInstance::EPlusBody(op) => validate_binary_operands(
            index,
            formal_count,
            result,
            op.p1.as_ref(),
            op.p2.as_ref(),
            errors,
        ),
        ExprInstance::EMinusBody(op) => validate_binary_operands(
            index,
            formal_count,
            result,
            op.p1.as_ref(),
            op.p2.as_ref(),
            errors,
        ),
        ExprInstance::EMultBody(op) => validate_binary_operands(
            index,
            formal_count,
            result,
            op.p1.as_ref(),
            op.p2.as_ref(),
            errors,
        ),
        ExprInstance::EDivBody(op) => validate_binary_operands(
            index,
            formal_count,
            result,
            op.p1.as_ref(),
            op.p2.as_ref(),
            errors,
        ),
        ExprInstance::EModBody(op) => validate_binary_operands(
            index,
            formal_count,
            result,
            op.p1.as_ref(),
            op.p2.as_ref(),
            errors,
        ),
        ExprInstance::EEqBody(op) => validate_binary_operands(
            index,
            formal_count,
            result,
            op.p1.as_ref(),
            op.p2.as_ref(),
            errors,
        ),
        ExprInstance::ENeqBody(op) => validate_binary_operands(
            index,
            formal_count,
            result,
            op.p1.as_ref(),
            op.p2.as_ref(),
            errors,
        ),
        ExprInstance::ELtBody(op) => validate_binary_operands(
            index,
            formal_count,
            result,
            op.p1.as_ref(),
            op.p2.as_ref(),
            errors,
        ),
        ExprInstance::EGtBody(op) => validate_binary_operands(
            index,
            formal_count,
            result,
            op.p1.as_ref(),
            op.p2.as_ref(),
            errors,
        ),
        ExprInstance::ELteBody(op) => validate_binary_operands(
            index,
            formal_count,
            result,
            op.p1.as_ref(),
            op.p2.as_ref(),
            errors,
        ),
        ExprInstance::EGteBody(op) => validate_binary_operands(
            index,
            formal_count,
            result,
            op.p1.as_ref(),
            op.p2.as_ref(),
            errors,
        ),
        ExprInstance::EAndBody(op) => validate_binary_operands(
            index,
            formal_count,
            result,
            op.p1.as_ref(),
            op.p2.as_ref(),
            errors,
        ),
        ExprInstance::EOrBody(op) => validate_binary_operands(
            index,
            formal_count,
            result,
            op.p1.as_ref(),
            op.p2.as_ref(),
            errors,
        ),
        ExprInstance::EPlusPlusBody(op) => validate_binary_operands(
            index,
            formal_count,
            result,
            op.p1.as_ref(),
            op.p2.as_ref(),
            errors,
        ),
        ExprInstance::ENotBody(op) => {
            validate_unary_operand(index, formal_count, result, op.p.as_ref(), errors)
        },
        ExprInstance::ENegBody(op) => {
            validate_unary_operand(index, formal_count, result, op.p.as_ref(), errors)
        },
        _ => errors.push(RhoValidationError::ContractResultShape { index }),
    }
}

fn validate_binary_operands(
    index: usize,
    formal_count: usize,
    result: &Par,
    lhs: Option<&Par>,
    rhs: Option<&Par>,
    errors: &mut Vec<RhoValidationError>,
) {
    if formal_count != 3 {
        errors.push(RhoValidationError::ContractResultShape { index });
        return;
    }
    if !metadata_eq(result, &bitvec(&[1, 2]), false) {
        errors.push(RhoValidationError::ContractResultMetadataMismatch { index });
    }
    validate_bound_operand(index, lhs, 2, errors);
    validate_bound_operand(index, rhs, 1, errors);
}

fn validate_unary_operand(
    index: usize,
    formal_count: usize,
    result: &Par,
    operand: Option<&Par>,
    errors: &mut Vec<RhoValidationError>,
) {
    if formal_count != 2 {
        errors.push(RhoValidationError::ContractResultShape { index });
        return;
    }
    if !metadata_eq(result, &bitvec(&[1]), false) {
        errors.push(RhoValidationError::ContractResultMetadataMismatch { index });
    }
    validate_bound_operand(index, operand, 1, errors);
}

fn validate_bound_operand(
    index: usize,
    operand: Option<&Par>,
    expected_index: i32,
    errors: &mut Vec<RhoValidationError>,
) {
    let Some(operand) = operand else {
        errors.push(RhoValidationError::ContractOperandMetadataMismatch { index });
        return;
    };
    if !metadata_eq(operand, &bitvec(&[expected_index as usize]), false)
        || bound_var_index(Some(operand)) != Some(expected_index)
    {
        errors.push(RhoValidationError::ContractOperandMetadataMismatch { index });
    }
}

fn bitvec(indices: &[usize]) -> Vec<u8> {
    if indices.is_empty() {
        Vec::new()
    } else {
        create_bit_vector(indices)
    }
}

fn all_formal_bits(formal_count: usize) -> Vec<u8> {
    bitvec(&(0..formal_count).collect::<Vec<_>>())
}

fn metadata_eq(par: &Par, locally_free: &[u8], connective_used: bool) -> bool {
    par.locally_free == locally_free && par.connective_used == connective_used
}

fn only_sends(par: &Par) -> bool {
    par.receives.is_empty()
        && par.news.is_empty()
        && par.exprs.is_empty()
        && par.matches.is_empty()
        && par.bundles.is_empty()
        && par.unforgeables.is_empty()
        && par.connectives.is_empty()
        && par.conditionals.is_empty()
}

fn only_expr_instance(par: &Par) -> Option<&ExprInstance> {
    if !par.sends.is_empty()
        || !par.receives.is_empty()
        || !par.news.is_empty()
        || !par.matches.is_empty()
        || !par.bundles.is_empty()
        || !par.unforgeables.is_empty()
        || !par.connectives.is_empty()
        || !par.conditionals.is_empty()
    {
        return None;
    }
    match par.exprs.as_slice() {
        [expr] => expr.expr_instance.as_ref(),
        _ => None,
    }
}

fn ground_string(par: &Par) -> Option<&str> {
    match only_expr_instance(par)? {
        ExprInstance::GString(value) => Some(value.as_str()),
        _ => None,
    }
}

fn free_var_index(par: &Par) -> Option<i32> {
    match only_expr_instance(par)? {
        ExprInstance::EVarBody(var) => match var.v.as_ref()?.var_instance.as_ref()? {
            VarInstance::FreeVar(index) => Some(*index),
            _ => None,
        },
        _ => None,
    }
}

fn bound_var_index(par: Option<&Par>) -> Option<i32> {
    match only_expr_instance(par?)? {
        ExprInstance::EVarBody(var) => match var.v.as_ref()?.var_instance.as_ref()? {
            VarInstance::BoundVar(index) => Some(*index),
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower::lower_language_def;
    use mettail_ast::language::LanguageDef;

    const FRAGMENT: &str = r#"
        name: ValidateScalar,
        types { Proc }
        terms {
            AddInt . a:Int, b:Int |- a "+" b : Int ;
        }
    "#;

    #[test]
    fn validates_generated_scalar_contract_ast() {
        let def = syn::parse_str::<LanguageDef>(FRAGMENT).expect("fragment parses");
        let lowering = lower_language_def(&def);
        validate_rho_program(&lowering.program).expect("generated scalar contract is valid");
    }

    #[test]
    fn validated_program_carries_only_checked_ast_artifact() {
        let def = syn::parse_str::<LanguageDef>(FRAGMENT).expect("fragment parses");
        let lowering = lower_language_def(&def);

        let validated = ValidatedRhoProgram::try_from(lowering.program)
            .expect("generated scalar contract validates");

        assert_eq!(validated.artifact_kind(), RhoArtifactKind::NormalizedAst);
        assert_eq!(
            validated
                .ast_par()
                .expect("validated AST exists")
                .receives
                .len(),
            1
        );
        assert!(
            validated.text_annotation().contains("contract @\"AddInt\""),
            "validated artifact keeps reader annotation without using source text for execution"
        );
    }

    #[test]
    fn rejects_mutated_nonpersistent_contract() {
        let def = syn::parse_str::<LanguageDef>(FRAGMENT).expect("fragment parses");
        let lowering = lower_language_def(&def);
        let RhoProgram::Ast(mut ast) = lowering.program;
        ast.par.receives[0].persistent = false;
        let errors = validate_rho_program(&RhoProgram::Ast(ast)).expect_err("mutation is invalid");
        assert_eq!(errors, vec![RhoValidationError::ContractNotPersistent { index: 0 }]);
    }

    #[test]
    fn rejects_mutated_top_level_metadata() {
        let def = syn::parse_str::<LanguageDef>(FRAGMENT).expect("fragment parses");
        let lowering = lower_language_def(&def);
        let RhoProgram::Ast(mut ast) = lowering.program;
        ast.par.connective_used = true;
        let errors = validate_rho_program(&RhoProgram::Ast(ast)).expect_err("mutation is invalid");
        assert_eq!(errors, vec![RhoValidationError::TopLevelMetadataMismatch]);
    }

    #[test]
    fn rejects_mutated_pattern_metadata() {
        let def = syn::parse_str::<LanguageDef>(FRAGMENT).expect("fragment parses");
        let lowering = lower_language_def(&def);
        let RhoProgram::Ast(mut ast) = lowering.program;
        ast.par.receives[0].binds[0].patterns[0].connective_used = false;
        let errors = validate_rho_program(&RhoProgram::Ast(ast)).expect_err("mutation is invalid");
        assert_eq!(errors, vec![RhoValidationError::ContractPatternMetadataMismatch { index: 0 }]);
    }

    #[test]
    fn rejects_mutated_body_metadata() {
        let def = syn::parse_str::<LanguageDef>(FRAGMENT).expect("fragment parses");
        let lowering = lower_language_def(&def);
        let RhoProgram::Ast(mut ast) = lowering.program;
        ast.par.receives[0]
            .body
            .as_mut()
            .expect("body exists")
            .locally_free = Vec::new();
        let errors = validate_rho_program(&RhoProgram::Ast(ast)).expect_err("mutation is invalid");
        assert_eq!(errors, vec![RhoValidationError::ContractBodyMetadataMismatch { index: 0 }]);
    }

    #[test]
    fn rejects_huge_bind_count_without_allocating_from_it() {
        let def = syn::parse_str::<LanguageDef>(FRAGMENT).expect("fragment parses");
        let lowering = lower_language_def(&def);
        let RhoProgram::Ast(mut ast) = lowering.program;
        ast.par.receives[0].bind_count = i32::MAX;

        let errors = validate_rho_program(&RhoProgram::Ast(ast)).expect_err("mutation is invalid");
        assert_eq!(errors, vec![RhoValidationError::ContractBindCountMismatch { index: 0 }]);
    }

    #[test]
    fn rejects_mutated_operand_metadata() {
        let def = syn::parse_str::<LanguageDef>(FRAGMENT).expect("fragment parses");
        let lowering = lower_language_def(&def);
        let RhoProgram::Ast(mut ast) = lowering.program;
        let result = &mut ast.par.receives[0]
            .body
            .as_mut()
            .expect("body exists")
            .sends[0]
            .data[0];
        let ExprInstance::EPlusBody(add) = result.exprs[0]
            .expr_instance
            .as_mut()
            .expect("result expression exists")
        else {
            panic!("test fragment should lower to EPlusBody");
        };
        add.p1.as_mut().expect("lhs exists").locally_free = Vec::new();

        let errors = validate_rho_program(&RhoProgram::Ast(ast)).expect_err("mutation is invalid");
        assert_eq!(errors, vec![RhoValidationError::ContractOperandMetadataMismatch { index: 0 }]);
    }
}
