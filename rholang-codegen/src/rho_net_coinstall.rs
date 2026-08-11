//! Cross-language installation metadata for the in-Rho driver families.
//!
//! A reflected MeTTaIL term carries its language fingerprint in every constructor
//! tag and in every non-site-keyed AC carrier.  [`CoInstallManifest`] records the
//! finite set of such shapes that may occur below one host language's terms.  The
//! generated `^drive`, `^subst`, and `^shift` machines use this one canonical
//! inventory for cross-language dispatch and opacity; an empty manifest therefore
//! emits exactly the isolated single-language machines.

use std::collections::BTreeSet;

use mettail_ast::identity::language_definition_fingerprint;
use mettail_ast::language::LanguageDef;

use crate::rho_net_lower::{
    BOUND_VAR_REFLECT_LABEL, FREE_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
    MULTILAMBDA_REFLECT_LABEL,
};
use crate::rho_net_subst_trs::{is_binder_term, object_congruence_constructors};

/// The reflected root shapes owned by one co-installed foreign language.
///
/// Both vectors are deterministic: constructor order follows the source
/// declaration, with the reserved binder/free/bound shapes appended once; AC
/// operators follow their source declarations.  A caller can consequently build
/// the same manifest independently on every node without negotiating runtime IDs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoInstallLanguageShape {
    /// The complete language-definition fingerprint embedded in reflected tags.
    pub fingerprint: String,
    /// Tagged reflected roots as `(label, structural arity)`.
    pub tagged_roots: Vec<(String, usize)>,
    /// HashBag carrier operators whose bare soup channel is fingerprint-scoped.
    pub ac_operators: Vec<String>,
    /// Whether a value entering this language from a foreign boundary must pass
    /// through its installed `^float` canonicalizer before `^drive`.
    pub float_before_drive: bool,
}

impl CoInstallLanguageShape {
    /// Derive the complete dispatch/opacity inventory from a language definition.
    pub fn from_language_def(def: &LanguageDef) -> Self {
        let fingerprint = language_definition_fingerprint(def);
        let mut tagged_roots = object_congruence_constructors(def);

        let has_binder = def.terms.iter().any(is_binder_term);
        if has_binder {
            // A generated driver currently admits only the single-binder arm, but
            // substitution opacity must also recognize a future/foreign multi-binder
            // root.  Including both is harmless because the fingerprint makes them
            // disjoint from the host's reserved roots.
            tagged_roots.push((LAMBDA_REFLECT_LABEL.to_string(), 1));
            tagged_roots.push((MULTILAMBDA_REFLECT_LABEL.to_string(), 2));
        }
        tagged_roots.push((FREE_VAR_REFLECT_LABEL.to_string(), 1));
        tagged_roots.push((BOUND_VAR_REFLECT_LABEL.to_string(), 1));

        let mut seen = BTreeSet::new();
        tagged_roots.retain(|root| seen.insert(root.clone()));

        let ac_operators = crate::rho_net_drive::hashbag_collection_ops(def);
        let float_before_drive = crate::rho_net_float::language_is_float_bearing(def);
        Self {
            fingerprint,
            tagged_roots,
            ac_operators,
            float_before_drive,
        }
    }
}

/// A host language plus the finite, fingerprint-disjoint foreign languages that
/// may occur inside its reflected terms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoInstallManifest {
    self_fingerprint: String,
    foreign: Vec<CoInstallLanguageShape>,
}

/// A fail-closed manifest construction error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CoInstallManifestError {
    /// A foreign definition has the same fingerprint as the host or another
    /// foreign definition, so dispatch could not select exactly one owner.
    DuplicateFingerprint { fingerprint: String },
}

impl std::fmt::Display for CoInstallManifestError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DuplicateFingerprint { fingerprint } => {
                write!(f, "co-install manifest contains the duplicate fingerprint {fingerprint:?}")
            },
        }
    }
}

impl std::error::Error for CoInstallManifestError {}

impl CoInstallManifest {
    /// The isolated-language manifest.  Its empty foreign inventory is the
    /// byte-identity route used by every existing single-language lowering.
    pub fn isolated(def: &LanguageDef) -> Self {
        Self::isolated_at_fingerprint(language_definition_fingerprint(def))
    }

    /// Construct the empty manifest for a builder that is intentionally exercised
    /// with an explicit fingerprint (notably byte pins and isolated receiver tests).
    pub(crate) fn isolated_at_fingerprint(fingerprint: impl Into<String>) -> Self {
        Self {
            self_fingerprint: fingerprint.into(),
            foreign: Vec::new(),
        }
    }

    /// Build a canonical manifest for `host` from co-installed foreign definitions.
    ///
    /// Foreign entries are sorted by fingerprint, so input order is not observable.
    /// Duplicate fingerprints are rejected rather than choosing an owner by order.
    pub fn from_definitions(
        host: &LanguageDef,
        foreign: &[&LanguageDef],
    ) -> Result<Self, CoInstallManifestError> {
        let self_fingerprint = language_definition_fingerprint(host);
        let mut shapes: Vec<_> = foreign
            .iter()
            .map(|def| CoInstallLanguageShape::from_language_def(def))
            .collect();
        shapes.sort_by(|left, right| left.fingerprint.cmp(&right.fingerprint));

        let mut seen = BTreeSet::from([self_fingerprint.clone()]);
        for shape in &shapes {
            if !seen.insert(shape.fingerprint.clone()) {
                return Err(CoInstallManifestError::DuplicateFingerprint {
                    fingerprint: shape.fingerprint.clone(),
                });
            }
        }
        Ok(Self { self_fingerprint, foreign: shapes })
    }

    /// Fingerprint of the host whose generated machines consume this manifest.
    pub fn self_fingerprint(&self) -> &str {
        &self.self_fingerprint
    }

    /// Canonically ordered foreign shape inventory.
    pub fn foreign(&self) -> &[CoInstallLanguageShape] {
        &self.foreign
    }

    /// Whether any co-installed language (including the host) needs an empty-bag
    /// identity arm.  The host bag flag is supplied by the caller because this
    /// manifest deliberately stores only foreign shapes.
    pub(crate) fn any_foreign_ac(&self) -> bool {
        self.foreign
            .iter()
            .any(|shape| !shape.ac_operators.is_empty())
    }

    /// Whether `fingerprint` names a foreign language whose boundary route must
    /// canonicalize through `^float` before entering `^drive`.
    pub(crate) fn foreign_float_before_drive(&self, fingerprint: &str) -> Option<bool> {
        self.foreign
            .iter()
            .find(|shape| shape.fingerprint == fingerprint)
            .map(|shape| shape.float_before_drive)
    }

    /// Validate that this manifest is being used for the language it was derived for.
    pub(crate) fn validate_host(&self, fingerprint: &str) -> Result<(), String> {
        if self.self_fingerprint == fingerprint {
            Ok(())
        } else {
            Err(format!(
                "co-install manifest host fingerprint {:?} does not match lowering fingerprint {:?}",
                self.self_fingerprint, fingerprint
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower::lower_language_def;
    use crate::rho_net::RhoNetProgram;

    fn def(name: &str, ctor: &str) -> LanguageDef {
        syn::parse_str(&format!(
            r#"
            name: {name},
            types {{ Term }},
            terms {{ {ctor} . child:Term |- "{ctor}" child : Term ; }},
            equations {{}},
            rewrites {{}},
            "#
        ))
        .expect("fixture language parses")
    }

    fn lambda_def() -> LanguageDef {
        syn::parse_str(
            r#"
            name: Lambda,
            types { Term },
            terms {
                Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term ;
                App . fun:Term, arg:Term |- "(" fun "," arg ")" : Term ;
            },
            equations {},
            rewrites {
                Beta . |- (App (Lam fun) arg) ~> (eval fun arg) ;
                AppCongL . | M0 ~> M1 |- (App M0 N) ~> (App M1 N) ;
                AppCongR . | N0 ~> N1 |- (App M N0) ~> (App M N1) ;
                LamCong . | S ~> T |- (Lam ^x.S) ~> (Lam ^x.T) ;
            },
            "#,
        )
        .expect("Lambda fixture parses")
    }

    #[test]
    fn foreign_order_is_canonical_and_isolated_is_empty() {
        let host = def("Host", "H");
        let a = def("GuestA", "A");
        let b = def("GuestB", "B");
        let left = CoInstallManifest::from_definitions(&host, &[&a, &b]).expect("manifest");
        let right = CoInstallManifest::from_definitions(&host, &[&b, &a]).expect("manifest");
        assert_eq!(left, right);
        assert!(CoInstallManifest::isolated(&host).foreign().is_empty());
    }

    #[test]
    fn duplicate_language_fingerprint_is_rejected() {
        let host = def("Host", "H");
        let guest = def("Guest", "G");
        let error = CoInstallManifest::from_definitions(&host, &[&guest, &guest])
            .expect_err("duplicate owner must fail closed");
        assert!(matches!(error, CoInstallManifestError::DuplicateFingerprint { .. }));
    }

    #[test]
    fn explicit_isolated_lowering_is_byte_identical_to_the_default_route() {
        let def = lambda_def();
        let lowering = lower_language_def(&def);
        let program = RhoNetProgram::from_language_def(&def, &lowering);
        let default = program.lower_to_par(&def, &lowering);
        let explicit = program
            .lower_to_par_with_coinstall_manifest(
                &def,
                &lowering,
                &CoInstallManifest::isolated(&def),
            )
            .expect("the manifest belongs to Lambda");
        assert_eq!(
            explicit, default,
            "an empty foreign inventory must preserve every isolated lowering byte"
        );
    }

    #[test]
    fn a_manifest_for_another_host_fails_before_lowering() {
        let host = lambda_def();
        let other = def("Other", "OtherNode");
        let lowering = lower_language_def(&host);
        let program = RhoNetProgram::from_language_def(&host, &lowering);
        let error = program
            .lower_to_par_with_coinstall_manifest(
                &host,
                &lowering,
                &CoInstallManifest::isolated(&other),
            )
            .expect_err("a cross-host manifest must fail closed");
        assert!(error.contains("does not match lowering fingerprint"), "{error}");
    }
}
