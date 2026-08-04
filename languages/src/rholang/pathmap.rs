//! Rholang PathMap literal carrier.
//!
//! Method, algebra, and zipper semantics live in f1r3node's native `EPathMap` reducer. The
//! language layer retains only the typed literal payload needed by the generated AST and lowerer.

use mettail_runtime::PathMapLit;

use super::Proc;

pub(crate) type ProcPathMap = PathMapLit<Proc, Proc>;
