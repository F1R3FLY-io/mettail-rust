//! Canonical ordinary-Rholang `module/1` values.
//!
//! Greg and Mike's surface elaborates through this representation. The same
//! closed value can be assembled and analyzed directly by a Rholang process;
//! both paths therefore share module identity, dependency commitments, export
//! order, and language lowering.

use crate::canonical::{admit_canonical_value, RhoValue, ValueDecodeError};
use crate::resolve::ModuleRef;
use std::collections::{BTreeMap, BTreeSet};

pub const CANONICAL_MODULE_SCHEMA_V1: &str = "module/1";
pub const MAX_CANONICAL_MODULE_DEPENDENCIES: usize = 256;
pub const MAX_CANONICAL_MODULE_EXPORTS: usize = 1_024;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonicalModuleDependency {
    pub reference: ModuleRef,
    pub commitment: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonicalModuleExport {
    pub name: String,
    pub spec: RhoValue,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonicalModuleValue {
    pub name: String,
    pub dependencies: Vec<CanonicalModuleDependency>,
    pub exports: Vec<CanonicalModuleExport>,
}

impl CanonicalModuleValue {
    pub fn from_rho_value(value: &RhoValue) -> Result<Self, ValueDecodeError> {
        admit_canonical_value(value)?;
        let record = expect_map(value, "$".into())?;
        require_keys(record, &["mettail", "name", "dependencies", "exports"], "$".into())?;
        if expect_string(required(record, "mettail", "$".into())?, "$.mettail".into())?
            != CANONICAL_MODULE_SCHEMA_V1
        {
            return error("$.mettail", format!("expected `{CANONICAL_MODULE_SCHEMA_V1}`"));
        }
        let name = canonical_identifier(
            expect_string(required(record, "name", "$".into())?, "$.name".into())?,
            "$.name",
        )?;

        let dependency_values =
            expect_list(required(record, "dependencies", "$".into())?, "$.dependencies".into())?;
        if dependency_values.len() > MAX_CANONICAL_MODULE_DEPENDENCIES {
            return error(
                "$.dependencies",
                format!("module exceeds {MAX_CANONICAL_MODULE_DEPENDENCIES} dependencies"),
            );
        }
        let mut dependency_references = BTreeSet::new();
        let mut dependencies = Vec::with_capacity(dependency_values.len());
        for (index, value) in dependency_values.iter().enumerate() {
            let path = format!("$.dependencies[{index}]");
            let dependency = expect_map(value, path.clone())?;
            require_keys(dependency, &["uri", "commitment"], path.clone())?;
            let external =
                expect_string(required(dependency, "uri", path.clone())?, format!("{path}.uri"))?;
            let reference = ModuleRef::parse(external).map_err(|reason| {
                ValueDecodeError::new(format!("{path}.uri"), reason.to_string())
            })?;
            if !dependency_references.insert(reference.clone()) {
                return error(format!("{path}.uri"), "duplicate module dependency");
            }
            let bytes = expect_bytes(
                required(dependency, "commitment", path.clone())?,
                format!("{path}.commitment"),
            )?;
            let commitment: [u8; 32] = bytes.try_into().map_err(|_| {
                ValueDecodeError::new(
                    format!("{path}.commitment"),
                    "a module commitment must contain exactly 32 bytes",
                )
            })?;
            dependencies.push(CanonicalModuleDependency { reference, commitment });
        }

        let export_values =
            expect_list(required(record, "exports", "$".into())?, "$.exports".into())?;
        if export_values.is_empty() {
            return error("$.exports", "a module must export at least one language");
        }
        if export_values.len() > MAX_CANONICAL_MODULE_EXPORTS {
            return error(
                "$.exports",
                format!("module exceeds {MAX_CANONICAL_MODULE_EXPORTS} exports"),
            );
        }
        let mut export_names = BTreeSet::new();
        let mut exports = Vec::with_capacity(export_values.len());
        for (index, value) in export_values.iter().enumerate() {
            let path = format!("$.exports[{index}]");
            let export = expect_map(value, path.clone())?;
            require_keys(export, &["name", "spec"], path.clone())?;
            let name = canonical_identifier(
                expect_string(required(export, "name", path.clone())?, format!("{path}.name"))?,
                &format!("{path}.name"),
            )?;
            if !export_names.insert(name.clone()) {
                return error(format!("{path}.name"), format!("duplicate export `{name}`"));
            }
            let spec = required(export, "spec", path.clone())?.clone();
            // This enforces value limits here. The language/2 decoder remains
            // the authority for the export's schema and semantic closure.
            admit_canonical_value(&spec)?;
            exports.push(CanonicalModuleExport { name, spec });
        }

        Ok(Self { name, dependencies, exports })
    }

    pub fn to_rho_value(&self) -> RhoValue {
        RhoValue::Map(BTreeMap::from([
            ("mettail".into(), RhoValue::String(CANONICAL_MODULE_SCHEMA_V1.into())),
            ("name".into(), RhoValue::String(self.name.clone())),
            (
                "dependencies".into(),
                RhoValue::List(
                    self.dependencies
                        .iter()
                        .map(|dependency| {
                            RhoValue::Map(BTreeMap::from([
                                (
                                    "uri".into(),
                                    RhoValue::String(dependency.reference.external_form()),
                                ),
                                (
                                    "commitment".into(),
                                    RhoValue::Bytes(dependency.commitment.to_vec()),
                                ),
                            ]))
                        })
                        .collect(),
                ),
            ),
            (
                "exports".into(),
                RhoValue::List(
                    self.exports
                        .iter()
                        .map(|export| {
                            RhoValue::Map(BTreeMap::from([
                                ("name".into(), RhoValue::String(export.name.clone())),
                                ("spec".into(), export.spec.clone()),
                            ]))
                        })
                        .collect(),
                ),
            ),
        ]))
    }

    pub fn fingerprint(&self) -> [u8; 32] {
        self.to_rho_value().fingerprint()
    }
}

fn required<'a>(
    record: &'a BTreeMap<String, RhoValue>,
    key: &str,
    path: String,
) -> Result<&'a RhoValue, ValueDecodeError> {
    record
        .get(key)
        .ok_or_else(|| ValueDecodeError::new(format!("{path}.{key}"), "required field is absent"))
}

fn require_keys(
    record: &BTreeMap<String, RhoValue>,
    required: &[&str],
    path: String,
) -> Result<(), ValueDecodeError> {
    for key in record.keys() {
        if !required.contains(&key.as_str()) {
            return error(format!("{path}.{key}"), "unknown field");
        }
    }
    for key in required {
        if !record.contains_key(*key) {
            return error(format!("{path}.{key}"), "required field is absent");
        }
    }
    Ok(())
}

fn expect_map(
    value: &RhoValue,
    path: String,
) -> Result<&BTreeMap<String, RhoValue>, ValueDecodeError> {
    match value {
        RhoValue::Map(value) => Ok(value),
        _ => error(path, "expected a map"),
    }
}

fn expect_list(value: &RhoValue, path: String) -> Result<&[RhoValue], ValueDecodeError> {
    match value {
        RhoValue::List(value) => Ok(value),
        _ => error(path, "expected a list"),
    }
}

fn expect_string(value: &RhoValue, path: String) -> Result<&str, ValueDecodeError> {
    match value {
        RhoValue::String(value) => Ok(value),
        _ => error(path, "expected a string"),
    }
}

fn expect_bytes(value: &RhoValue, path: String) -> Result<&[u8], ValueDecodeError> {
    match value {
        RhoValue::Bytes(value) => Ok(value),
        _ => error(path, "expected a byte array"),
    }
}

fn canonical_identifier(value: &str, path: &str) -> Result<String, ValueDecodeError> {
    let mut chars = value.chars();
    if !chars
        .next()
        .is_some_and(|ch| ch.is_ascii_alphabetic() || ch == '_')
        || !chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
    {
        return error(path, format!("`{value}` is not an ASCII identifier"));
    }
    Ok(value.into())
}

fn error<T>(path: impl Into<String>, message: impl Into<String>) -> Result<T, ValueDecodeError> {
    Err(ValueDecodeError::new(path, message))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn language(name: &str) -> RhoValue {
        RhoValue::Map(BTreeMap::from([
            ("mettail".into(), RhoValue::String("language/2".into())),
            ("name".into(), RhoValue::String(name.into())),
            ("types".into(), RhoValue::List(vec![RhoValue::String("Expr".into())])),
        ]))
    }

    fn module() -> CanonicalModuleValue {
        CanonicalModuleValue {
            name: "Pair".into(),
            dependencies: vec![CanonicalModuleDependency {
                reference: ModuleRef::Registry("rho:base".into()),
                commitment: [0x42; 32],
            }],
            exports: vec![
                CanonicalModuleExport {
                    name: "Left".into(),
                    spec: language("Left"),
                },
                CanonicalModuleExport {
                    name: "Right".into(),
                    spec: language("Right"),
                },
            ],
        }
    }

    #[test]
    fn canonical_module_round_trip_preserves_source_order_and_bytes() {
        let module = module();
        let decoded = CanonicalModuleValue::from_rho_value(&module.to_rho_value())
            .expect("canonical module decodes");
        assert_eq!(decoded, module);
    }

    #[test]
    fn duplicate_exports_are_rejected() {
        let mut module = module();
        module.exports[1].name = "Left".into();
        let error = CanonicalModuleValue::from_rho_value(&module.to_rho_value())
            .expect_err("duplicate exports fail closed");
        assert!(error.to_string().contains("duplicate export `Left`"));
    }

    #[test]
    fn commitments_have_an_exact_width() {
        let mut value = module().to_rho_value();
        let RhoValue::Map(record) = &mut value else {
            unreachable!()
        };
        let RhoValue::List(dependencies) = record.get_mut("dependencies").unwrap() else {
            unreachable!()
        };
        let RhoValue::Map(dependency) = &mut dependencies[0] else {
            unreachable!()
        };
        dependency.insert("commitment".into(), RhoValue::Bytes(vec![0; 31]));
        let error = CanonicalModuleValue::from_rho_value(&value)
            .expect_err("truncated commitment fails closed");
        assert!(error.to_string().contains("exactly 32 bytes"));
    }
}
