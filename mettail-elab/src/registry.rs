//! Versioned Registry language records and parser-image cache validation.
//!
//! The canonical `language/2` value is always authoritative. The optional
//! parser image is derived, untrusted cache data and is accepted only after the
//! caller has lowered the value to `GrammarCoreV1` and every cache contract
//! field has been verified against that result.

use crate::canonical::RhoValue;
use mettail_grammar_core::{GrammarCoreV1, ParserImageV1};

pub const REGISTRY_LANGUAGE_SCHEMA_V1: &str = "mettail-registry-language/1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegistryLanguageRecord {
    pub schema: String,
    pub spec: RhoValue,
    pub parser_image: Option<Vec<u8>>,
}

impl RegistryLanguageRecord {
    pub fn new(spec: RhoValue) -> Self {
        Self {
            schema: REGISTRY_LANGUAGE_SCHEMA_V1.into(),
            spec,
            parser_image: None,
        }
    }

    /// Prepare installation by lowering the authoritative value first, then
    /// probing the optional cache against the resulting core.
    pub fn prepare_install<E>(
        &self,
        compiler_abi: &str,
        unicode_version: &str,
        lower: impl FnOnce(&RhoValue) -> Result<GrammarCoreV1, E>,
    ) -> Result<PreparedRegistryLanguage, PrepareRegistryError<E>> {
        if self.schema != REGISTRY_LANGUAGE_SCHEMA_V1 {
            return Err(PrepareRegistryError::UnsupportedSchema(self.schema.clone()));
        }
        let core = lower(&self.spec).map_err(PrepareRegistryError::Lowering)?;
        core.validate()
            .map_err(PrepareRegistryError::InvalidGrammar)?;
        let cache = match &self.parser_image {
            None => ParserCache::Missing,
            Some(bytes) => match ParserImageV1::decode_executable_verified(
                bytes,
                &core,
                compiler_abi,
                unicode_version,
            ) {
                Ok(image) => ParserCache::Verified(Box::new(image)),
                Err(error) => ParserCache::Rejected(format!("{error:?}")),
            },
        };
        Ok(PreparedRegistryLanguage {
            authoritative_spec: self.spec.clone(),
            core,
            cache,
        })
    }
}

pub struct PreparedRegistryLanguage {
    pub authoritative_spec: RhoValue,
    pub core: GrammarCoreV1,
    pub cache: ParserCache,
}

pub enum ParserCache {
    Missing,
    Verified(Box<ParserImageV1>),
    /// The cache is discarded. The caller may compile a fresh image from
    /// `PreparedRegistryLanguage::core`; it must not install these bytes.
    Rejected(String),
}

#[derive(Debug)]
pub enum PrepareRegistryError<E> {
    UnsupportedSchema(String),
    Lowering(E),
    InvalidGrammar(Vec<mettail_grammar_core::ValidationError>),
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_grammar_core::{Carrier, Category, CategoryId};

    fn core(name: &str) -> GrammarCoreV1 {
        let mut core = GrammarCoreV1::new(name);
        core.categories.push(Category {
            id: CategoryId(0),
            name: "Term".into(),
            carrier: Carrier::Dynamic,
            primary: true,
            admits_variables: false,
        });
        core
    }

    #[test]
    fn metadata_cache_is_rejected_after_authoritative_lowering() {
        let spec = RhoValue::String("authority".into());
        let authoritative_core = core("A");
        let metadata = ParserImageV1::metadata_only(&authoritative_core, "compiler/1", "15.1")
            .expect("valid metadata")
            .encode()
            .expect("encodable metadata");
        let mut record = RegistryLanguageRecord::new(spec.clone());
        record.parser_image = Some(metadata);
        let prepared = record
            .prepare_install("compiler/1", "15.1", |value| {
                assert_eq!(value, &spec);
                Ok::<_, ()>(authoritative_core.clone())
            })
            .expect("valid authoritative spec");
        assert!(matches!(prepared.cache, ParserCache::Rejected(_)));
        assert_eq!(prepared.authoritative_spec, spec);
    }

    #[test]
    fn mismatched_cache_is_discarded_not_promoted_to_authority() {
        let spec = RhoValue::String("authority".into());
        let cached_core = core("cached");
        let authoritative_core = core("authoritative");
        let mut metadata = ParserImageV1::metadata_only(&cached_core, "compiler/1", "15.1")
            .expect("valid metadata");
        metadata.kind = mettail_grammar_core::ParserImageKind::Executable;
        let mut record = RegistryLanguageRecord::new(spec);
        record.parser_image = Some(metadata.encode().expect("encodable image"));
        let prepared = record
            .prepare_install("compiler/1", "15.1", |_| Ok::<_, ()>(authoritative_core.clone()))
            .expect("valid authoritative spec");
        assert!(matches!(prepared.cache, ParserCache::Rejected(_)));
        assert_eq!(prepared.core.name, "authoritative");
    }
}
