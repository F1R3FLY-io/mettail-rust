//! Reuse the existing syntax gates against the isolated compilation of the
//! same language definition. No copied fixtures or alternative parser.

extern crate mettail_rholang_syntax as mettail_languages;

#[path = "../../languages/tests/rholang_mettail_ddl.rs"]
mod ddl;
#[path = "../../languages/tests/l9_flt_rholang.rs"]
mod flt;
#[path = "../../languages/tests/rholang_new_official_syntax.rs"]
mod new_binding;
