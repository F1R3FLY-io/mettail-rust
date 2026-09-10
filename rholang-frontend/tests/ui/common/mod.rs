#![allow(unused_imports, dead_code)]
pub use mettail_rholang_frontend::{
    arena::{with_neutral_target, ConstructionLimits},
    construction::{ValueOp, ValueTarget},
};
pub const LIMITS: ConstructionLimits = ConstructionLimits {
    nodes: 10,
    edges: 20,
    payload_bytes: 100,
    work: 100,
};
