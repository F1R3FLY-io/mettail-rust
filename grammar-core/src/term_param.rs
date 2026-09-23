//! Shallow authored parameter observations shared by the original consumers.

/// One authored term parameter, observed without following its child handles.
pub enum TermParamObservation<N, S, T> {
    Simple { name: N, ty: T },
    GuardBody { name: N },
    Abstraction { binder: N, body: N, ty: T },
    MultiAbstraction { binder: N, body: N, ty: T },
    Optional { params: S },
}

/// Immutable, shallow access to authored declarations.
///
/// Every handle must belong to this reader. `param_at` succeeds exactly at
/// indices below `params_len`, and all observations remain stable for the
/// iterator's lifetime. Names and types stay opaque: callers retain their
/// original spelling, identity, and type constructors without reconstructing
/// an AST. The macro adapter supplies borrowed slices and nodes.
///
/// The projection, reverse-push order, leaf identities, and inherited optional
/// flags are modeled in `TermParamReaderProjection.v`. That finite-execution
/// proof does not certify arbitrary readers, allocation, or termination of
/// cyclic handle stores; runtime admission must validate its own input graph.
pub trait TermParamReader<'syntax> {
    type Parameters: Copy;
    type Param: Copy;
    type Name: Copy;
    type Type: Copy;

    fn params_len(&self, params: Self::Parameters) -> usize;
    fn param_at(&self, params: Self::Parameters, index: usize) -> Option<Self::Param>;
    fn param(
        &self,
        param: Self::Param,
    ) -> TermParamObservation<Self::Name, Self::Parameters, Self::Type>;
}
