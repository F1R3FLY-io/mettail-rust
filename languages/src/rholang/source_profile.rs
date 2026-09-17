//! Closed host policy for the generated borrowed source-profile checker.
//!
//! Admission selects supported source constructors, not a new grammar or a
//! semantic type checker. Every generated constructor absent from the table is
//! refused. Original child occurrences retain their structural role; guest FLT
//! payloads remain opaque and are checked by their separate preparation stage.

use super::{source_constructor, SourceConstructor, SourceProfile};

#[path = "source_profile_policy.rs"]
mod policy;

/// The interpretation context carried alongside an original source occurrence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceRole {
    Term,
    Name,
    Pattern,
    NamePattern,
    Guard,
    Declaration,
}

/// The public-source subset understood by the bounded Rholang preparation path.
#[derive(Clone, Copy, Debug, Default)]
pub struct RholangSourceProfile;

type Transition = fn(SourceRole) -> SourceRole;

fn term(_: SourceRole) -> SourceRole {
    SourceRole::Term
}
fn name(_: SourceRole) -> SourceRole {
    SourceRole::Name
}
fn pattern(_: SourceRole) -> SourceRole {
    SourceRole::Pattern
}
fn name_pattern(_: SourceRole) -> SourceRole {
    SourceRole::NamePattern
}
fn guard(_: SourceRole) -> SourceRole {
    SourceRole::Guard
}
fn declaration(_: SourceRole) -> SourceRole {
    SourceRole::Declaration
}
fn inherit(role: SourceRole) -> SourceRole {
    role
}
fn quote(role: SourceRole) -> SourceRole {
    match role {
        SourceRole::NamePattern => SourceRole::Pattern,
        _ => SourceRole::Term,
    }
}
fn boolean(role: SourceRole) -> SourceRole {
    match role {
        SourceRole::Guard => SourceRole::Guard,
        _ => SourceRole::Term,
    }
}

macro_rules! transition {
    (Opaque) => {
        None
    };
    (T) => {
        Some(term as Transition)
    };
    (N) => {
        Some(name as Transition)
    };
    (P) => {
        Some(pattern as Transition)
    };
    (PN) => {
        Some(name_pattern as Transition)
    };
    (G) => {
        Some(guard as Transition)
    };
    (D) => {
        Some(declaration as Transition)
    };
    (I) => {
        Some(inherit as Transition)
    };
    (Q) => {
        Some(quote as Transition)
    };
    (B) => {
        Some(boolean as Transition)
    };
}

macro_rules! define_profile {
    ($( $category:ident :: $constructor:ident => [$( $field:ty => $role:ident ),*]; )*) => {
        impl SourceProfile for RholangSourceProfile {
            type Role = SourceRole;

            fn fields(&self, tag: SourceConstructor) -> Option<&'static [Option<Transition>]> {
                match tag {
                    $(SourceConstructor::$category(source_constructor::$category::$constructor) => {
                        Some(&[$(transition!($role)),*])
                    },)*
                    _ => None,
                }
            }
        }
    };
}

policy::rholang_source_profile_rows!(define_profile);
