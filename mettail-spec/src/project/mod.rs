//! Backend projection from NTIR to host languages.

mod rust;

pub use rust::{
    parse_projected_language_def, project_rust_file, project_rust_source,
    project_rust_source_with_spaces, verify_projection_sources, write_projected_rs,
    write_projected_rs_with_spaces,
};
