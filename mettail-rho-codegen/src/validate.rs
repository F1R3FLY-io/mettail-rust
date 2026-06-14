//! Validation for generated Rho backend artifacts.
//!
//! Direct `RhoRuntime::inj` bypasses the source parser/normalizer, so codegen
//! must own the normalized-`Par` invariants it relies on. This validator checks
//! the scalar-contract artifact emitted by `lower_language_def`.

use models::create_bit_vector;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::var::VarInstance;
use models::rhoapi::{Par, Receive, ReceiveBind};

use crate::lower::{RhoArtifactKind, RhoAstProgram, RhoAstValidationProfile, RhoProgram};

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
    CallByNeedTopLevelShape,
    CallByNeedNewShape,
    CallByNeedBodyShape,
    CallByNeedInitialStateSeed,
    CallByNeedMemoSeed,
    CallByNeedThunkContractShape,
    CallByNeedObserverShape,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ValidatedRhoAstProgram {
    par: Par,
    text_annotation: String,
    validation_profile: RhoAstValidationProfile,
}

impl ValidatedRhoAstProgram {
    fn from_validated(program: RhoAstProgram) -> Self {
        Self {
            par: program.par,
            text_annotation: program.text_annotation,
            validation_profile: program.validation_profile,
        }
    }

    pub fn par(&self) -> &Par {
        &self.par
    }

    /// Reader/debug annotation. This text is not parsed as the execution path.
    pub fn text_annotation(&self) -> &str {
        &self.text_annotation
    }

    pub fn validation_profile(&self) -> RhoAstValidationProfile {
        self.validation_profile
    }
}

/// Rho artifact whose generated shape has passed codegen validation.
///
/// Production generated-backend execution should consume this typestate instead
/// of arbitrary `Par`. Low-level raw-`Par` execution remains available in
/// `mettail-rho-runtime` for host oracle tests and debugging.
#[derive(Debug, Clone, PartialEq)]
pub struct ValidatedRhoProgram {
    inner: ValidatedRhoArtifact,
}

#[derive(Debug, Clone, PartialEq)]
enum ValidatedRhoArtifact {
    Ast(ValidatedRhoAstProgram),
}

impl ValidatedRhoProgram {
    pub fn artifact_kind(&self) -> RhoArtifactKind {
        match &self.inner {
            ValidatedRhoArtifact::Ast(_) => RhoArtifactKind::NormalizedAst,
        }
    }

    pub fn ast_par(&self) -> Option<&Par> {
        match &self.inner {
            ValidatedRhoArtifact::Ast(program) => Some(program.par()),
        }
    }

    /// Reader/debug annotation. This text is not parsed as the execution path.
    pub fn text_annotation(&self) -> &str {
        match &self.inner {
            ValidatedRhoArtifact::Ast(program) => program.text_annotation(),
        }
    }
}

impl TryFrom<RhoProgram> for ValidatedRhoProgram {
    type Error = Vec<RhoValidationError>;

    fn try_from(program: RhoProgram) -> Result<Self, Self::Error> {
        validate_rho_program(&program)?;
        match program {
            RhoProgram::Ast(ast) => Ok(Self {
                inner: ValidatedRhoArtifact::Ast(ValidatedRhoAstProgram::from_validated(ast)),
            }),
        }
    }
}

pub fn validate_rho_program(program: &RhoProgram) -> Result<(), Vec<RhoValidationError>> {
    match program {
        RhoProgram::Ast(ast) => match ast.validation_profile() {
            RhoAstValidationProfile::ScalarContracts => validate_contract_program(ast.par()),
            RhoAstValidationProfile::CallByNeedThunk => {
                validate_call_by_need_thunk_program(ast.par())
            },
        },
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

fn validate_call_by_need_thunk_program(par: &Par) -> Result<(), Vec<RhoValidationError>> {
    let mut errors = Vec::new();
    if par.news.len() != 1
        || !par.sends.is_empty()
        || !par.receives.is_empty()
        || !par.exprs.is_empty()
        || !par.matches.is_empty()
        || !par.bundles.is_empty()
        || !par.unforgeables.is_empty()
        || !par.connectives.is_empty()
        || !par.conditionals.is_empty()
        || !metadata_eq(par, &[], false)
    {
        errors.push(RhoValidationError::CallByNeedTopLevelShape);
    }

    let Some(new_scope) = par.news.first() else {
        return Err(errors);
    };
    if new_scope.bind_count != 5
        || new_scope.p.is_none()
        || !new_scope.uri.is_empty()
        || !new_scope.injections.is_empty()
        || !new_scope.locally_free.is_empty()
    {
        errors.push(RhoValidationError::CallByNeedNewShape);
    }

    let Some(body) = new_scope.p.as_ref() else {
        return Err(errors);
    };
    if !body.news.is_empty()
        || !body.exprs.is_empty()
        || !body.matches.is_empty()
        || !body.bundles.is_empty()
        || !body.unforgeables.is_empty()
        || !body.connectives.is_empty()
        || !body.conditionals.is_empty()
        || body.receives.len() != 3
        || !matches!(body.sends.len(), 2 | 3)
    {
        errors.push(RhoValidationError::CallByNeedBodyShape);
    }

    let initial_state = body
        .sends
        .first()
        .and_then(|send| validate_bound_string_send(send, 3, false));
    match initial_state {
        Some("cold") if body.sends.len() == 2 => {},
        Some("hot") if body.sends.len() == 3 => {
            if body
                .sends
                .get(1)
                .and_then(|send| validate_bound_string_send(send, 2, true))
                != Some("value")
            {
                errors.push(RhoValidationError::CallByNeedMemoSeed);
            }
        },
        _ => errors.push(RhoValidationError::CallByNeedInitialStateSeed),
    }

    let thunk_send_index = body.sends.len().saturating_sub(1);
    if body
        .sends
        .get(thunk_send_index)
        .and_then(|send| validate_bound_name_send(send, 4, 1, false))
        .is_none()
    {
        errors.push(RhoValidationError::CallByNeedBodyShape);
    }

    if !body
        .receives
        .iter()
        .any(|receive| validate_simple_receive_source(receive, 4, true, false))
    {
        errors.push(RhoValidationError::CallByNeedThunkContractShape);
    }
    if !body
        .receives
        .iter()
        .any(|receive| validate_simple_receive_source(receive, 1, false, false))
        || !body
            .receives
            .iter()
            .any(|receive| validate_simple_receive_source(receive, 0, false, false))
    {
        errors.push(RhoValidationError::CallByNeedObserverShape);
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

fn validate_simple_receive_source(
    receive: &Receive,
    source_index: i32,
    persistent: bool,
    peek: bool,
) -> bool {
    if receive.persistent != persistent
        || receive.peek != peek
        || receive.condition.is_some()
        || receive.bind_count != 1
        || receive.body.is_none()
        || receive.binds.len() != 1
    {
        return false;
    }
    let bind = &receive.binds[0];
    bind.patterns.len() == 1
        && bind.free_count == 1
        && bind.remainder.is_none()
        && free_var_index(&bind.patterns[0]) == Some(0)
        && bound_var_index(bind.source.as_ref()) == Some(source_index)
}

fn validate_bound_string_send(
    send: &models::rhoapi::Send,
    channel_index: i32,
    persistent: bool,
) -> Option<&str> {
    if send.persistent != persistent || send.data.len() != 1 {
        return None;
    }
    if bound_var_index(send.chan.as_ref()) != Some(channel_index) {
        return None;
    }
    ground_string(&send.data[0])
}

fn validate_bound_name_send(
    send: &models::rhoapi::Send,
    channel_index: i32,
    data_index: i32,
    persistent: bool,
) -> Option<()> {
    if send.persistent != persistent || send.data.len() != 1 {
        return None;
    }
    (bound_var_index(send.chan.as_ref()) == Some(channel_index)
        && bound_var_index(send.data.first()) == Some(data_index))
    .then_some(())
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
    use crate::need::{
        build_call_by_need_thunk_ast, build_call_by_need_thunk_program, CallByNeedInitialState,
    };
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
        let ValidatedRhoArtifact::Ast(ast) = &validated.inner;
        assert_eq!(ast.validation_profile(), RhoAstValidationProfile::ScalarContracts);
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
    fn validates_call_by_need_thunk_programs() {
        for initial_state in [CallByNeedInitialState::Cold, CallByNeedInitialState::Hot] {
            let program = build_call_by_need_thunk_program(initial_state);
            validate_rho_program(&program).expect("call-by-need thunk validates");

            let validated = ValidatedRhoProgram::try_from(program)
                .expect("call-by-need thunk converts to validated artifact");
            let ValidatedRhoArtifact::Ast(ast) = &validated.inner;
            assert_eq!(validated.artifact_kind(), RhoArtifactKind::NormalizedAst);
            assert_eq!(ast.validation_profile(), RhoAstValidationProfile::CallByNeedThunk);
            assert!(
                validated
                    .text_annotation()
                    .contains("call-by-need thunk AST"),
                "validated CBN artifact must retain reader annotation without source parsing"
            );
        }
    }

    #[test]
    fn raw_call_by_need_thunk_does_not_pass_scalar_contract_profile() {
        let raw = build_call_by_need_thunk_ast(CallByNeedInitialState::Cold);
        let scalar_profile_program = RhoProgram::Ast(RhoAstProgram::new(
            raw.par().clone(),
            raw.text_annotation().to_string(),
        ));

        let errors = validate_rho_program(&scalar_profile_program)
            .expect_err("CBN network is not a scalar contract artifact");
        assert!(
            errors.contains(&RhoValidationError::TopLevelHasNonContractProcess),
            "scalar contract validation must reject top-level CBN new/sends shape: {errors:?}"
        );
    }

    #[test]
    fn rejects_mutated_call_by_need_hot_memo_seed() {
        let RhoProgram::Ast(mut ast) =
            build_call_by_need_thunk_program(CallByNeedInitialState::Hot);
        let body = ast.par.news[0].p.as_mut().expect("CBN new body exists");
        body.sends.remove(1);

        let errors = validate_rho_program(&RhoProgram::Ast(ast))
            .expect_err("hot CBN thunk without memo seed is invalid");
        assert!(
            errors.contains(&RhoValidationError::CallByNeedInitialStateSeed)
                || errors.contains(&RhoValidationError::CallByNeedMemoSeed),
            "hot CBN validation must catch missing memo seed: {errors:?}"
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
