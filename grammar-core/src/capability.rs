use crate::{GrammarCoreV1, NativeEvaluation, SyntaxItem, TokenDecoder};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

const MAX_CAPABILITY_NAME_BYTES: usize = 512;
const MAX_CAPABILITY_ABI_BYTES: usize = 256;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum RuntimeCapabilityKind {
    TokenDecoder,
    NativeEvaluator,
    ForeignBridge,
    /// Exact, fingerprint-scoped codec for a structural atom which cannot be
    /// represented by a built-in canonical byte encoding.
    StructuralCodec,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum RuntimeEffect {
    Reduce,
    Bridge,
    /// Reflect a typed value to or from its canonical structural image.
    Reflect,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct RuntimeCapabilityKey {
    pub language_fingerprint: [u8; 32],
    pub kind: RuntimeCapabilityKind,
    pub name: String,
}

impl RuntimeCapabilityKey {
    pub fn token_decoder(language_fingerprint: [u8; 32], name: impl Into<String>) -> Self {
        Self {
            language_fingerprint,
            kind: RuntimeCapabilityKind::TokenDecoder,
            name: name.into(),
        }
    }

    pub fn native_evaluator(language_fingerprint: [u8; 32], name: impl Into<String>) -> Self {
        Self {
            language_fingerprint,
            kind: RuntimeCapabilityKind::NativeEvaluator,
            name: name.into(),
        }
    }

    pub fn foreign_bridge(language_fingerprint: [u8; 32], open: &str, close: &str) -> Self {
        let mut hasher = blake3::Hasher::new();
        hash_field(&mut hasher, b"mettail-foreign-bridge/1");
        hash_field(&mut hasher, open.as_bytes());
        hash_field(&mut hasher, close.as_bytes());
        Self {
            language_fingerprint,
            kind: RuntimeCapabilityKind::ForeignBridge,
            name: format!("bridge/{}", hasher.finalize().to_hex()),
        }
    }

    pub fn structural_codec(language_fingerprint: [u8; 32], name: impl Into<String>) -> Self {
        Self {
            language_fingerprint,
            kind: RuntimeCapabilityKind::StructuralCodec,
            name: name.into(),
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeLogicalCost {
    pub base: u64,
    pub per_input_byte: u64,
    pub per_value: u64,
    pub maximum: u64,
}

impl RuntimeLogicalCost {
    pub fn charge(self, input_bytes: usize, values: usize) -> Option<u64> {
        let input_bytes = u64::try_from(input_bytes).ok()?;
        let values = u64::try_from(values).ok()?;
        let charge = self
            .base
            .checked_add(self.per_input_byte.checked_mul(input_bytes)?)?
            .checked_add(self.per_value.checked_mul(values)?)?;
        (charge <= self.maximum).then_some(charge)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RuntimeCapabilityManifest {
    pub key: RuntimeCapabilityKey,
    pub code_commitment: [u8; 32],
    pub abi: String,
    pub effects: BTreeSet<RuntimeEffect>,
    pub cost: RuntimeLogicalCost,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuntimeCapabilityError {
    InvalidRequest(&'static str),
    Missing(Box<RuntimeCapabilityKey>),
    KeyMismatch {
        expected: Box<RuntimeCapabilityKey>,
        actual: Box<RuntimeCapabilityKey>,
    },
    EmptyAbi(Box<RuntimeCapabilityKey>),
    AbiTooLarge(Box<RuntimeCapabilityKey>),
    MissingEffect {
        key: Box<RuntimeCapabilityKey>,
        effect: RuntimeEffect,
    },
    Changed(Box<RuntimeCapabilityKey>),
    CostExceeded(Box<RuntimeCapabilityKey>),
    Encode(String),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RuntimeCapabilityBindings {
    manifests: BTreeMap<RuntimeCapabilityKey, RuntimeCapabilityManifest>,
}

impl RuntimeCapabilityBindings {
    pub fn get(&self, key: &RuntimeCapabilityKey) -> Option<&RuntimeCapabilityManifest> {
        self.manifests.get(key)
    }

    pub fn iter(&self) -> impl Iterator<Item = &RuntimeCapabilityManifest> {
        self.manifests.values()
    }

    pub fn is_empty(&self) -> bool {
        self.manifests.is_empty()
    }

    pub fn commitment(&self) -> Result<[u8; 32], RuntimeCapabilityError> {
        let encoded = postcard::to_allocvec(&self.manifests)
            .map_err(|error| RuntimeCapabilityError::Encode(error.to_string()))?;
        Ok(*blake3::hash(&encoded).as_bytes())
    }

    pub fn bind(
        requirements: &[RuntimeCapabilityRequirement],
        mut lookup: impl FnMut(&RuntimeCapabilityKey) -> Option<RuntimeCapabilityManifest>,
    ) -> Result<Self, RuntimeCapabilityError> {
        let mut manifests = BTreeMap::new();
        for requirement in requirements {
            let manifest = lookup(&requirement.key).ok_or_else(|| {
                RuntimeCapabilityError::Missing(Box::new(requirement.key.clone()))
            })?;
            validate_manifest(requirement, &manifest)?;
            manifests.insert(requirement.key.clone(), manifest);
        }
        let bindings = Self { manifests };
        // Revalidate the complete immutable snapshot. This second iterative
        // pass prevents a changing provider from publishing mixed bindings.
        for committed in bindings.manifests.values() {
            let current = lookup(&committed.key)
                .ok_or_else(|| RuntimeCapabilityError::Changed(Box::new(committed.key.clone())))?;
            if current != *committed {
                return Err(RuntimeCapabilityError::Changed(Box::new(committed.key.clone())));
            }
        }
        Ok(bindings)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct RuntimeCapabilityRequirement {
    pub key: RuntimeCapabilityKey,
    pub effect: RuntimeEffect,
}

/// Collect external callback requirements with an explicit worklist. The
/// ordered set makes the installation query order deterministic and removes
/// duplicates without recursive traversal.
pub fn runtime_capability_requirements(
    core: &GrammarCoreV1,
    language_fingerprint: [u8; 32],
) -> Result<Vec<RuntimeCapabilityRequirement>, RuntimeCapabilityError> {
    let mut requirements = BTreeSet::new();
    for token in &core.tokens {
        if let TokenDecoder::Capability(name) = &token.decoder {
            insert_requirement(
                &mut requirements,
                RuntimeCapabilityKey::token_decoder(language_fingerprint, name.clone()),
                RuntimeEffect::Reduce,
            )?;
        }
        if let Some(NativeEvaluation::Handler(name)) = &token.evaluation {
            insert_requirement(
                &mut requirements,
                RuntimeCapabilityKey::native_evaluator(language_fingerprint, name.clone()),
                RuntimeEffect::Reduce,
            )?;
        }
    }
    for reduction in &core.reductions {
        if let Some(NativeEvaluation::Handler(name)) = &reduction.evaluation {
            insert_requirement(
                &mut requirements,
                RuntimeCapabilityKey::native_evaluator(language_fingerprint, name.clone()),
                RuntimeEffect::Reduce,
            )?;
        }
    }
    let mut pending = Vec::new();
    for production in core.productions.iter().rev() {
        pending.extend(production.syntax.iter().rev());
    }
    while let Some(item) = pending.pop() {
        match item {
            SyntaxItem::ForeignLanguage { open, close, .. } => insert_requirement(
                &mut requirements,
                RuntimeCapabilityKey::foreign_bridge(language_fingerprint, open, close),
                RuntimeEffect::Bridge,
            )?,
            SyntaxItem::Repeat { body, .. }
            | SyntaxItem::Sequence(body)
            | SyntaxItem::Zip { body, .. }
            | SyntaxItem::Optional(body) => pending.extend(body.iter().rev()),
            SyntaxItem::Separated { source, .. } => pending.push(source),
            SyntaxItem::Mapped { source, body, .. } => {
                pending.push(source);
                pending.extend(body.iter().rev());
            },
            SyntaxItem::Token(_)
            | SyntaxItem::Category { .. }
            | SyntaxItem::CaptureIdent { .. }
            | SyntaxItem::CaptureToken { .. }
            | SyntaxItem::Binder { .. }
            | SyntaxItem::Collection { .. }
            | SyntaxItem::Guard { .. } => {},
        }
    }
    Ok(requirements.into_iter().collect())
}

fn insert_requirement(
    requirements: &mut BTreeSet<RuntimeCapabilityRequirement>,
    key: RuntimeCapabilityKey,
    effect: RuntimeEffect,
) -> Result<(), RuntimeCapabilityError> {
    if key.name.is_empty() {
        return Err(RuntimeCapabilityError::InvalidRequest("empty capability name"));
    }
    if key.name.len() > MAX_CAPABILITY_NAME_BYTES {
        return Err(RuntimeCapabilityError::InvalidRequest("capability name exceeds bound"));
    }
    requirements.insert(RuntimeCapabilityRequirement { key, effect });
    Ok(())
}

fn validate_manifest(
    requirement: &RuntimeCapabilityRequirement,
    manifest: &RuntimeCapabilityManifest,
) -> Result<(), RuntimeCapabilityError> {
    if manifest.key != requirement.key {
        return Err(RuntimeCapabilityError::KeyMismatch {
            expected: Box::new(requirement.key.clone()),
            actual: Box::new(manifest.key.clone()),
        });
    }
    if manifest.abi.is_empty() {
        return Err(RuntimeCapabilityError::EmptyAbi(Box::new(manifest.key.clone())));
    }
    if manifest.abi.len() > MAX_CAPABILITY_ABI_BYTES {
        return Err(RuntimeCapabilityError::AbiTooLarge(Box::new(manifest.key.clone())));
    }
    if !manifest.effects.contains(&requirement.effect) {
        return Err(RuntimeCapabilityError::MissingEffect {
            key: Box::new(manifest.key.clone()),
            effect: requirement.effect,
        });
    }
    Ok(())
}

fn hash_field(hasher: &mut blake3::Hasher, bytes: &[u8]) {
    hasher.update(&(bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Carrier, Category, CategoryId, ConstructorId, Precedence, Production, ProductionClass,
        ProductionId, ReductionPlan,
    };

    fn manifest(requirement: &RuntimeCapabilityRequirement) -> RuntimeCapabilityManifest {
        RuntimeCapabilityManifest {
            key: requirement.key.clone(),
            code_commitment: [7; 32],
            abi: "test-capability/1".into(),
            effects: [requirement.effect].into_iter().collect(),
            cost: RuntimeLogicalCost {
                base: 1,
                per_input_byte: 1,
                per_value: 1,
                maximum: 1024,
            },
        }
    }

    #[test]
    fn nested_foreign_requirements_use_an_iterative_worklist() {
        let mut grammar = GrammarCoreV1::new("nested");
        grammar.categories.push(Category {
            id: CategoryId(0),
            name: "Term".into(),
            carrier: Carrier::Dynamic,
            primary: true,
            admits_variables: false,
        });
        grammar.reductions.push(ReductionPlan {
            output_category: CategoryId(0),
            constructor: ConstructorId(0),
            input_arity: 1,
            fields: vec![crate::FieldSource::Input(0)],
            evaluation: None,
            evaluation_mode: None,
            tier: None,
        });
        let mut item = SyntaxItem::ForeignLanguage {
            slot: "guest".into(),
            open: "{{".into(),
            close: "}}".into(),
        };
        for _ in 0..20_000 {
            item = SyntaxItem::Optional(vec![item]);
        }
        grammar.productions.push(Production {
            id: ProductionId(0),
            constructor: ConstructorId(0),
            label: "Guest".into(),
            result: CategoryId(0),
            syntax: vec![item],
            precedence: Precedence::default(),
            classification: ProductionClass::default(),
            reduction: 0,
            provenance: None,
        });
        let requirements = runtime_capability_requirements(&grammar, [3; 32]).expect("collect");
        assert_eq!(requirements.len(), 1);
        assert_eq!(requirements[0].effect, RuntimeEffect::Bridge);
        // Avoid recursively dropping the deliberately deep test value.
        let production = grammar.productions.pop().expect("production");
        let mut pending = production.syntax;
        while let Some(node) = pending.pop() {
            if let SyntaxItem::Optional(mut body) = node {
                pending.append(&mut body);
            }
        }
    }

    #[test]
    fn binding_is_atomic_and_revalidates_the_catalog() {
        let key = RuntimeCapabilityKey::token_decoder([1; 32], "decoder");
        let requirement = RuntimeCapabilityRequirement {
            key: key.clone(),
            effect: RuntimeEffect::Reduce,
        };
        let expected = manifest(&requirement);
        let mut calls = 0;
        let bound = RuntimeCapabilityBindings::bind(&[requirement], |_| {
            calls += 1;
            Some(expected.clone())
        })
        .expect("stable binding");
        assert_eq!(calls, 2);
        assert_eq!(bound.get(&key), Some(&expected));
    }

    #[test]
    fn logical_cost_is_checked_without_float_arithmetic() {
        let cost = RuntimeLogicalCost {
            base: 2,
            per_input_byte: 3,
            per_value: 5,
            maximum: 20,
        };
        assert_eq!(cost.charge(1, 2), Some(15));
        assert_eq!(cost.charge(2, 3), None);
    }
}
