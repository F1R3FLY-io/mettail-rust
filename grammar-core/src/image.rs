use crate::{ExactWeight, GrammarCoreV1, GrammarLimits, ProductionId, ReductionPlan, TokenId};
use serde::{Deserialize, Serialize};

pub const PARSER_IMAGE_MAGIC: [u8; 8] = *b"MTILIMG1";
pub const PARSER_IMAGE_ABI_V1: u16 = 1;

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ParserImageV1 {
    pub magic: [u8; 8],
    pub abi: u16,
    pub compiler_abi: String,
    pub unicode_version: String,
    pub core_fingerprint: [u8; 32],
    pub kind: ParserImageKind,
    pub index_width: IndexWidth,
    pub exact: bool,
    pub lexer: LexerImage,
    pub programs: Vec<DecisionProgram>,
    pub reductions: Vec<ReductionPlan>,
    pub engine: EngineTables,
    pub limits: GrammarLimits,
}

impl ParserImageV1 {
    /// Construct a non-executable image header for tooling and registry
    /// negotiation. This must never be installed as a parser.
    pub fn metadata_only(
        core: &GrammarCoreV1,
        compiler_abi: impl Into<String>,
        unicode_version: impl Into<String>,
    ) -> Result<Self, ImageBuildError> {
        core.validate().map_err(ImageBuildError::InvalidGrammar)?;
        if !core.weight_profile.is_consensus_safe() {
            return Err(ImageBuildError::NonExactProfile);
        }
        let index_width = IndexWidth::for_max(
            core.categories
                .len()
                .max(core.tokens.len())
                .max(core.productions.len()),
        );
        Ok(Self {
            magic: PARSER_IMAGE_MAGIC,
            abi: PARSER_IMAGE_ABI_V1,
            compiler_abi: compiler_abi.into(),
            unicode_version: unicode_version.into(),
            core_fingerprint: core.fingerprint().map_err(ImageBuildError::Encode)?,
            kind: ParserImageKind::MetadataOnly,
            index_width,
            exact: true,
            lexer: LexerImage::default(),
            programs: Vec::new(),
            reductions: core.reductions.clone(),
            engine: EngineTables::default(),
            limits: core.limits,
        })
    }

    pub fn encode(&self) -> Result<Vec<u8>, postcard::Error> {
        postcard::to_allocvec(self)
    }

    pub fn decode_verified(bytes: &[u8], expected_core: [u8; 32]) -> Result<Self, ImageError> {
        let image: Self = postcard::from_bytes(bytes).map_err(ImageError::Decode)?;
        image.verify(expected_core)?;
        Ok(image)
    }

    /// Decode an executable cache image and verify every field that is derived
    /// from, or selected for, the authoritative grammar.
    pub fn decode_executable_verified(
        bytes: &[u8],
        core: &GrammarCoreV1,
        compiler_abi: &str,
        unicode_version: &str,
    ) -> Result<Self, ImageError> {
        let image: Self = postcard::from_bytes(bytes).map_err(ImageError::Decode)?;
        image.verify_executable(core, compiler_abi, unicode_version)?;
        Ok(image)
    }

    pub fn verify(&self, expected_core: [u8; 32]) -> Result<(), ImageError> {
        if self.magic != PARSER_IMAGE_MAGIC {
            return Err(ImageError::BadMagic);
        }
        if self.abi != PARSER_IMAGE_ABI_V1 {
            return Err(ImageError::UnsupportedAbi(self.abi));
        }
        if self.core_fingerprint != expected_core {
            return Err(ImageError::CoreFingerprintMismatch);
        }
        if !self.exact {
            return Err(ImageError::NonExactImage);
        }
        for (index, program) in self.programs.iter().enumerate() {
            program
                .verify()
                .map_err(|error| ImageError::Program { index: index as u32, error })?;
        }
        self.lexer.verify()?;
        Ok(())
    }

    pub fn verify_executable(
        &self,
        core: &GrammarCoreV1,
        compiler_abi: &str,
        unicode_version: &str,
    ) -> Result<(), ImageError> {
        core.validate().map_err(ImageError::InvalidGrammar)?;
        let fingerprint = core.fingerprint().map_err(ImageError::EncodeCore)?;
        self.verify(fingerprint)?;
        if self.kind != ParserImageKind::Executable {
            return Err(ImageError::NotExecutable);
        }
        if self.compiler_abi != compiler_abi {
            return Err(ImageError::CompilerAbiMismatch);
        }
        if self.unicode_version != unicode_version {
            return Err(ImageError::UnicodeVersionMismatch);
        }
        if self.limits != core.limits {
            return Err(ImageError::LimitsMismatch);
        }
        if self.reductions != core.reductions {
            return Err(ImageError::ReductionsMismatch);
        }
        let expected_width = IndexWidth::for_max(
            core.categories
                .len()
                .max(core.tokens.len())
                .max(core.productions.len()),
        );
        if self.index_width != expected_width {
            return Err(ImageError::IndexWidthMismatch);
        }
        if !core.productions.is_empty() && self.programs.is_empty() {
            return Err(ImageError::MissingPrograms);
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ParserImageKind {
    MetadataOnly,
    Executable,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum IndexWidth {
    U8,
    U16,
    U32,
}

impl IndexWidth {
    pub fn for_max(max: usize) -> Self {
        if max <= u8::MAX as usize {
            Self::U8
        } else if max <= u16::MAX as usize {
            Self::U16
        } else {
            Self::U32
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct LexerImage {
    pub mode_starts: Vec<u32>,
    pub states: Vec<LexerState>,
    pub transitions: Vec<LexerTransition>,
}

impl LexerImage {
    fn verify(&self) -> Result<(), ImageError> {
        for start in &self.mode_starts {
            if *start as usize >= self.states.len() && !self.states.is_empty() {
                return Err(ImageError::BadLexerState(*start));
            }
        }
        for transition in &self.transitions {
            if transition.target as usize >= self.states.len() {
                return Err(ImageError::BadLexerState(transition.target));
            }
            if transition.start > transition.end {
                return Err(ImageError::BadCharacterRange);
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LexerState {
    pub transition_start: u32,
    pub transition_len: u32,
    pub accept: Vec<TokenId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LexerTransition {
    pub start: char,
    pub end: char,
    pub target: u32,
}

/// Acyclic decision program. Tests branch forward; a return terminates a step.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecisionProgram {
    pub code: Vec<Instruction>,
}

impl DecisionProgram {
    pub fn verify(&self) -> Result<(), ProgramError> {
        if self.code.is_empty() {
            return Err(ProgramError::Empty);
        }
        for (pc, instruction) in self.code.iter().enumerate() {
            match instruction {
                Instruction::TestToken { yes, no, .. }
                | Instruction::TestText { yes, no, .. }
                | Instruction::TestBindingPower { yes, no, .. } => {
                    for target in [*yes, *no] {
                        if target as usize >= self.code.len() {
                            return Err(ProgramError::BadTarget { pc, target });
                        }
                        if target as usize <= pc {
                            return Err(ProgramError::BackwardEdge { pc, target });
                        }
                    }
                },
                Instruction::Return(_) => {},
            }
        }
        if !matches!(self.code.last(), Some(Instruction::Return(_))) {
            return Err(ProgramError::NoTerminalReturn);
        }
        Ok(())
    }

    pub fn execute(&self, input: VmInput<'_>) -> Result<VmAction, ProgramError> {
        self.verify()?;
        let mut pc = 0usize;
        loop {
            match &self.code[pc] {
                Instruction::TestToken { token, yes, no } => {
                    pc = if input.token == Some(*token) {
                        *yes
                    } else {
                        *no
                    } as usize;
                },
                Instruction::TestText { text, yes, no } => {
                    pc = if input.text == Some(text.as_str()) {
                        *yes
                    } else {
                        *no
                    } as usize;
                },
                Instruction::TestBindingPower { minimum, yes, no } => {
                    pc = if input.binding_power >= *minimum {
                        *yes
                    } else {
                        *no
                    } as usize;
                },
                Instruction::Return(action) => return Ok(action.clone()),
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Instruction {
    TestToken { token: TokenId, yes: u32, no: u32 },
    TestText { text: String, yes: u32, no: u32 },
    TestBindingPower { minimum: u16, yes: u32, no: u32 },
    Return(VmAction),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum VmAction {
    Advance {
        state: u32,
    },
    Push {
        symbol: u32,
        state: u32,
        weight: ExactWeight,
    },
    Pop {
        state: u32,
        weight: ExactWeight,
    },
    Replace {
        symbol: u32,
        state: u32,
        weight: ExactWeight,
    },
    Consume {
        state: u32,
    },
    ConsumeAndPush {
        symbol: u32,
        state: u32,
        weight: ExactWeight,
    },
    Fork {
        branches: Vec<VmBranch>,
        consume: bool,
    },
    Reduce {
        production: ProductionId,
        state: u32,
    },
    Accept,
    Error {
        code: u32,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VmBranch {
    pub action: Box<VmAction>,
    pub weight: ExactWeight,
    pub declaration_ordinal: u32,
}

#[derive(Clone, Copy, Debug)]
pub struct VmInput<'a> {
    pub token: Option<TokenId>,
    pub text: Option<&'a str>,
    pub binding_power: u16,
}

/// Tables for non-step queries made by the generalized WPDA walker.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct EngineTables {
    pub action_by_rule: Vec<Option<u32>>,
    pub chain_atoms: Vec<ChainAtomEntry>,
    pub non_atom_prefixes: Vec<TokenSetEntry>,
    pub parikh_classes: Vec<Option<u8>>,
    pub parikh_must_masks: Vec<ParikhMaskEntry>,
    pub collection_rules: Vec<CollectionRuleEntry>,
    pub category_min_spans: Vec<u16>,
    pub coercions: Vec<CoercionEntry>,
    pub operator_floors: Vec<OperatorFloorEntry>,
    pub structural_open_tokens: Vec<TokenId>,
    pub structural_close_tokens: Vec<TokenId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChainAtomEntry {
    pub category: u32,
    pub token: TokenId,
    pub productions: Vec<ProductionId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TokenSetEntry {
    pub category: u32,
    pub tokens: Vec<TokenId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParikhMaskEntry {
    pub category: u32,
    pub production: u32,
    pub position: u16,
    pub mask: u128,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CollectionRuleEntry {
    pub production: ProductionId,
    pub element_category: u32,
    pub separator: String,
    pub key_value_separator: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoercionEntry {
    pub source: u32,
    pub target: u32,
    pub production: ProductionId,
    pub weight: ExactWeight,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OperatorFloorEntry {
    pub category: u32,
    pub token: TokenId,
    pub minimum_binding_power: u16,
}

#[derive(Debug)]
pub enum ImageBuildError {
    InvalidGrammar(Vec<crate::ValidationError>),
    NonExactProfile,
    Encode(postcard::Error),
}

#[derive(Debug)]
pub enum ImageError {
    Decode(postcard::Error),
    EncodeCore(postcard::Error),
    InvalidGrammar(Vec<crate::ValidationError>),
    BadMagic,
    UnsupportedAbi(u16),
    CoreFingerprintMismatch,
    NonExactImage,
    NotExecutable,
    CompilerAbiMismatch,
    UnicodeVersionMismatch,
    LimitsMismatch,
    ReductionsMismatch,
    IndexWidthMismatch,
    MissingPrograms,
    BadLexerState(u32),
    BadCharacterRange,
    Program { index: u32, error: ProgramError },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProgramError {
    Empty,
    BadTarget { pc: usize, target: u32 },
    BackwardEdge { pc: usize, target: u32 },
    NoTerminalReturn,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Carrier, Category, CategoryId};

    #[test]
    fn decision_program_is_verified_and_executable() {
        let program = DecisionProgram {
            code: vec![
                Instruction::TestToken { token: TokenId(2), yes: 1, no: 2 },
                Instruction::Return(VmAction::Accept),
                Instruction::Return(VmAction::Error { code: 7 }),
            ],
        };
        assert_eq!(
            program
                .execute(VmInput {
                    token: Some(TokenId(2)),
                    text: None,
                    binding_power: 0,
                })
                .expect("valid decision program"),
            VmAction::Accept
        );
    }

    #[test]
    fn parser_image_rejects_a_different_grammar() {
        let mut core = GrammarCoreV1::new("A");
        core.categories.push(Category {
            id: CategoryId(0),
            name: "Term".into(),
            carrier: Carrier::Dynamic,
            primary: true,
            admits_variables: false,
        });
        let image =
            ParserImageV1::metadata_only(&core, "test", "15.1").expect("valid image metadata");
        let mut other = core.clone();
        other.name = "B".into();
        assert!(matches!(
            image.verify(other.fingerprint().expect("fingerprint")),
            Err(ImageError::CoreFingerprintMismatch)
        ));
    }

    #[test]
    fn metadata_image_is_never_executable() {
        let mut core = GrammarCoreV1::new("A");
        core.categories.push(Category {
            id: CategoryId(0),
            name: "Term".into(),
            carrier: Carrier::Dynamic,
            primary: true,
            admits_variables: false,
        });
        let image =
            ParserImageV1::metadata_only(&core, "test", "15.1").expect("valid image metadata");
        assert!(matches!(
            image.verify_executable(&core, "test", "15.1"),
            Err(ImageError::NotExecutable)
        ));
    }
}
