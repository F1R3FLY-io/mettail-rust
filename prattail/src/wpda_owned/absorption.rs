//! Receipts from the original absorption query, including its explicit None.
//! The existing walker stores static mixfix strings: a borrowed mixfix Some is
//! therefore an explicit compatibility error, not permission to disable it.

use super::engine::AbsorptionRows;
use crate::binding_power::IterAbsorbSpec;
use crate::wpda_rule_analysis::authored_declarations::{
    AuthoredDeclarationReader, AuthoredDeclarationReaderError,
};
use crate::wpda_rule_analysis::authored_descriptors::OwnedWpdaDescriptors;
use crate::wpda_rule_analysis::census::CategoryCensusReader;
use crate::wpda_rule_analysis::iter_absorption::{self, BorrowedIterAbsorbSpec};
use mettail_grammar_core::{
    constructor_labels::try_generate_literal_label_observed, GrammarCoreV1, SourceObservation,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AbsorptionObservationError {
    Declarations(AuthoredDeclarationReaderError),
    UnavailableByteObservation,
    UnavailableNativeObservation,
    AbsentNativeObservation,
    CategoryIndexOverflow(usize),
    Disjointness {
        category: String,
        operator: String,
        clash: String,
    },
    BorrowedMixfixSpec {
        result: u16,
        rule: u16,
    },
}

fn runtime_spec(
    spec: BorrowedIterAbsorbSpec<'_>,
) -> Result<IterAbsorbSpec, AbsorptionObservationError> {
    if spec.is_mixfix {
        return Err(AbsorptionObservationError::BorrowedMixfixSpec {
            result: spec.op_cat_src_idx,
            rule: spec.op_rule_idx,
        });
    }
    Ok(IterAbsorbSpec {
        left_bp: spec.left_bp,
        right_bp: spec.right_bp,
        assoc_right: spec.assoc_right,
        is_mixfix: spec.is_mixfix,
        op_cat_src_idx: spec.op_cat_src_idx,
        op_rule_idx: spec.op_rule_idx,
        atom_cat_src_idx: spec.atom_cat_src_idx,
        atom_lit_rule_idx: spec.atom_lit_rule_idx,
        trigger: "",
        sep: "",
    })
}

/// Derive receipts using the same workers as the static emitter. No missing
/// query row is substituted for a None answer; no Some is silently discarded.
pub fn derive_absorption_rows<P>(
    core: &GrammarCoreV1,
    descriptors: &OwnedWpdaDescriptors<P>,
) -> Result<AbsorptionRows, AbsorptionObservationError> {
    use AbsorptionObservationError as Error;
    let mut declarations = AuthoredDeclarationReader::new(core).map_err(Error::Declarations)?;
    let literal_indices = iter_absorption::try_literal_rule_indices(
        &declarations.header().categories,
        &descriptors.label_index,
        |category| declarations.type_name(category),
        |category| category.native.as_ref().map(|_| category),
        |native| {
            try_generate_literal_label_observed(
                || match native.byte_observation {
                    SourceObservation::Known(value) => Ok(value),
                    SourceObservation::Unavailable => Err(Error::UnavailableByteObservation),
                },
                || match &native.literal_observation {
                    SourceObservation::Known(Some(value)) => Ok(value.clone()),
                    SourceObservation::Known(None) => Err(Error::AbsentNativeObservation),
                    SourceObservation::Unavailable => Err(Error::UnavailableNativeObservation),
                },
                |label| Ok(label.to_owned()),
            )
        },
    )?;
    let mut rows = AbsorptionRows::new();
    for (category_index, category) in descriptors.synthesis.categories.iter().enumerate() {
        let category_index = u16::try_from(category_index)
            .map_err(|_| Error::CategoryIndexOverflow(category_index))?;
        let query = iter_absorption::query(
            &descriptors.binding_powers,
            category,
            &descriptors.label_index,
            &literal_indices,
        );
        if let Some((operator, clash)) = query.disjointness.first() {
            return Err(Error::Disjointness {
                category: category.clone(),
                operator: operator.label.clone(),
                clash: clash.label.clone(),
            });
        }
        for op in descriptors
            .binding_powers
            .operators
            .iter()
            .filter(|op| op.category == *category && op.is_iterative_candidate())
        {
            let Some(&(rs, ri)) = descriptors
                .label_index
                .get(&(op.result_category.clone(), op.label.clone()))
            else {
                continue;
            };
            let answer = query.lookup(rs, ri).map(runtime_spec).transpose()?;
            rows.insert((category_index, rs, ri), answer);
        }
    }
    Ok(rows)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn borrowed_mixfix_some_is_an_error_not_a_none_receipt() {
        let mut spec = BorrowedIterAbsorbSpec {
            left_bp: 2,
            right_bp: 1,
            assoc_right: true,
            is_mixfix: false,
            op_cat_src_idx: 3,
            op_rule_idx: 4,
            atom_cat_src_idx: 3,
            atom_lit_rule_idx: 5,
            trigger: "",
            sep: "",
        };
        let binary = runtime_spec(spec).expect("original binary strings are static empty");
        assert_eq!((binary.left_bp, binary.right_bp, binary.atom_lit_rule_idx), (2, 1, 5));
        assert_eq!((binary.trigger, binary.sep), ("", ""));
        spec.is_mixfix = true;
        spec.trigger = "?";
        spec.sep = ":";
        assert_eq!(
            runtime_spec(spec),
            Err(AbsorptionObservationError::BorrowedMixfixSpec { result: 3, rule: 4 })
        );
    }
}
