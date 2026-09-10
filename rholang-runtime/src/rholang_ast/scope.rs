//! Checked lexical resolution over the existing two-domain environment.
//!
//! This is not a source admission session or a second scope traversal. The
//! existing driver supplies opened moniker variables and ordered receive slots.
//! Node resource reservation belongs to construction; these checks establish
//! integer representability before calling index-sized node constructors.

use super::*;

/// Whether unresolved term references reject or use the explicit oracle ABI.
/// Guard-discharge options do not select source admission policy.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceAdmissionMode {
    Public,
    Harness,
}

impl BoundEnv {
    /// Construct an explicitly empty lexical environment with declared policy.
    ///
    /// This low-level context does not enroll caller URI injections, perform
    /// whole-source admission or create a prepared node program. Those inputs
    /// must be supplied by the enclosing preparation session; a caller must not
    /// use this constructor to discard an existing lexical environment.
    pub fn empty_with_admission(
        resolver: Arc<dyn FltResolve>,
        options: LoweringOptions,
        admission: SourceAdmissionMode,
    ) -> Self {
        Self {
            options,
            admission,
            binders: HashMap::new(),
            hole_binders: HashMap::new(),
            resolver,
            free_vars_are_patterns: false,
        }
    }

    pub(super) fn without_lexical_bindings(&self) -> Self {
        Self {
            options: self.options,
            admission: self.admission,
            binders: HashMap::new(),
            hole_binders: HashMap::new(),
            resolver: Arc::clone(&self.resolver),
            free_vars_are_patterns: self.free_vars_are_patterns,
        }
    }
}

pub(super) fn checked_shift(index: usize, width: usize) -> Result<usize, RholangAstLowerError> {
    index
        .checked_add(width)
        .ok_or(RholangAstLowerError::ScopeIndexOverflow)
}

pub(super) fn next_environment_index(length: usize) -> Result<u32, RholangAstLowerError> {
    length
        .checked_add(1)
        .and_then(|next| u32::try_from(next).ok())
        .ok_or(RholangAstLowerError::ScopeArenaOverflow)
}

fn checked_bound_index(index: usize) -> Result<i32, RholangAstLowerError> {
    i32::try_from(index).map_err(|_| RholangAstLowerError::BoundIndexOutOfRange { index })
}

pub(super) fn lower_bound_index(index: usize) -> Result<Par, RholangAstLowerError> {
    let index = checked_bound_index(index)?;
    Ok(new_boundvar_par(index, Vec::new(), false))
}

#[derive(Clone, Copy)]
pub(super) enum ReferenceRole {
    Name,
    Process,
}

enum Resolution<'a> {
    Bound(i32),
    Wildcard,
    Harness(&'a str),
}

/// Resolve without allocating a node or consulting string data for authority.
/// Identity lookup precedes the enclosing FLT-hole-name fallback in both modes.
fn resolve<'a>(
    var: &'a OrdVar,
    env: &BoundEnv,
    role: ReferenceRole,
) -> Result<Resolution<'a>, RholangAstLowerError> {
    let free_var = match &var.0 {
        Var::Free(free_var) => free_var,
        Var::Bound(_) => {
            return Err(match role {
                ReferenceRole::Name => {
                    RholangAstLowerError::UnsupportedName("unopened bound name variable")
                },
                ReferenceRole::Process => {
                    RholangAstLowerError::UnsupportedProc("unopened bound process variable")
                },
            });
        },
    };
    let index = env
        .binders
        .get(free_var)
        .copied()
        .or_else(|| flt_hole_bound_level(free_var, env));
    match index {
        Some(index) => Ok(Resolution::Bound(checked_bound_index(index)?)),
        None if env.free_vars_are_patterns => Ok(Resolution::Wildcard),
        None => match env.admission {
            SourceAdmissionMode::Public => Err(match role {
                ReferenceRole::Name => RholangAstLowerError::UnresolvedNameReference,
                ReferenceRole::Process => RholangAstLowerError::UnresolvedProcessReference,
            }),
            SourceAdmissionMode::Harness => Ok(Resolution::Harness(pretty_var_name(free_var)?)),
        },
    }
}

pub(super) fn lower_reference(
    var: &OrdVar,
    env: &BoundEnv,
    role: ReferenceRole,
) -> Result<Par, RholangAstLowerError> {
    Ok(match resolve(var, env, role)? {
        Resolution::Bound(index) => new_boundvar_par(index, Vec::new(), false),
        Resolution::Wildcard => new_wildcard_par(Vec::new(), true),
        Resolution::Harness(name) => {
            let marker = new_gstring_par(format!("{FREE_NAME_PREFIX}{name}"), Vec::new(), false);
            match role {
                ReferenceRole::Name => marker,
                ReferenceRole::Process => send_par(
                    new_gstring_par(FREE_PROC_OUTPUT.to_string(), Vec::new(), false),
                    vec![marker],
                ),
            }
        },
    })
}

#[cfg(test)]
#[path = "scope_tests.rs"]
mod tests;
