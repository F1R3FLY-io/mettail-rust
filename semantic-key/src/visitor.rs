//! Callable bodies relocated from the generated semantic-hash visitor.
//! The source-backed contract is modeled by OwnedSemanticVisitor.v.
//! These are parser-local exact keys, not a new portable value encoding.

pub trait SemanticSink: std::hash::Hasher {
    const COMPOSES_KEYS: bool;

    fn max_key_bytes(&self) -> usize {
        usize::MAX
    }

    fn record_key_error(&mut self, _error: crate::ContentKeyCacheError) {}

    fn write_exact_key(&mut self, key: crate::ContentKey) {
        self.write(key.as_bytes());
    }

    fn begin_node(&mut self, _identity: crate::ContentKeyNodeIdentity, _cacheable: bool) -> bool {
        false
    }

    fn finish_node(&mut self, _identity: crate::ContentKeyNodeIdentity, _cacheable: bool) {}
}

pub struct FlatSemanticSink<'a, H>(pub &'a mut H);

impl<H: std::hash::Hasher> std::hash::Hasher for FlatSemanticSink<'_, H> {
    fn finish(&self) -> u64 {
        self.0.finish()
    }
    fn write(&mut self, bytes: &[u8]) {
        self.0.write(bytes);
    }
    fn write_u8(&mut self, value: u8) {
        self.0.write_u8(value);
    }
    fn write_u16(&mut self, value: u16) {
        self.0.write_u16(value);
    }
    fn write_u32(&mut self, value: u32) {
        self.0.write_u32(value);
    }
    fn write_u64(&mut self, value: u64) {
        self.0.write_u64(value);
    }
    fn write_u128(&mut self, value: u128) {
        self.0.write_u128(value);
    }
    fn write_usize(&mut self, value: usize) {
        self.0.write_usize(value);
    }
    fn write_i8(&mut self, value: i8) {
        self.0.write_i8(value);
    }
    fn write_i16(&mut self, value: i16) {
        self.0.write_i16(value);
    }
    fn write_i32(&mut self, value: i32) {
        self.0.write_i32(value);
    }
    fn write_i64(&mut self, value: i64) {
        self.0.write_i64(value);
    }
    fn write_i128(&mut self, value: i128) {
        self.0.write_i128(value);
    }
    fn write_isize(&mut self, value: isize) {
        self.0.write_isize(value);
    }
}

impl<H: std::hash::Hasher> SemanticSink for FlatSemanticSink<'_, H> {
    const COMPOSES_KEYS: bool = false;
}

impl SemanticSink for crate::SemanticKeyBuilder {
    const COMPOSES_KEYS: bool = true;

    fn max_key_bytes(&self) -> usize {
        crate::SemanticKeyBuilder::max_key_bytes(self)
    }

    fn write_exact_key(&mut self, key: crate::ContentKey) {
        self.push_framed_key(key);
    }
}

pub struct ComposingSemanticSink<'transaction, 'cache> {
    transaction: &'transaction mut crate::ContentKeyCacheTransaction<'cache>,
    frames: Vec<crate::SemanticKeyBuilder>,
    orphan: crate::SemanticKeyBuilder,
    root: Option<crate::ContentKey>,
    error: Option<crate::ContentKeyCacheError>,
}

impl<'transaction, 'cache> ComposingSemanticSink<'transaction, 'cache> {
    /// # Safety
    /// Every cacheable identity supplied during this traversal must name an
    /// immutable descendant of the transaction's retained root.
    pub unsafe fn new(
        transaction: &'transaction mut crate::ContentKeyCacheTransaction<'cache>,
    ) -> Self {
        let max_key_bytes = transaction.max_key_bytes();
        Self {
            transaction,
            frames: Vec::new(),
            orphan: crate::SemanticKeyBuilder::with_max_bytes(max_key_bytes),
            root: None,
            error: None,
        }
    }

    fn current(&mut self) -> &mut crate::SemanticKeyBuilder {
        let Some(current) = self.frames.last_mut() else {
            self.error
                .get_or_insert(crate::ContentKeyCacheError::ConstructionInvariant);
            return &mut self.orphan;
        };
        current
    }

    fn append_key(&mut self, key: crate::ContentKey) {
        if let Some(parent) = self.frames.last_mut() {
            parent.push_key(key);
        } else if self.root.is_none() {
            self.root = Some(key);
        } else {
            self.error
                .get_or_insert(crate::ContentKeyCacheError::ConstructionInvariant);
        }
    }

    pub fn into_result(mut self) -> Result<crate::ContentKey, crate::ContentKeyCacheError> {
        if !self.frames.is_empty() {
            return Err(crate::ContentKeyCacheError::ConstructionInvariant);
        }
        if let Some(error) = self.error.take() {
            return Err(error);
        }
        self.root
            .take()
            .ok_or(crate::ContentKeyCacheError::ConstructionInvariant)
    }
}

impl std::hash::Hasher for ComposingSemanticSink<'_, '_> {
    fn finish(&self) -> u64 {
        self.frames.last().map_or(0, std::hash::Hasher::finish)
    }
    fn write(&mut self, bytes: &[u8]) {
        self.current().write(bytes);
    }
    fn write_u8(&mut self, value: u8) {
        self.current().write_u8(value);
    }
    fn write_u16(&mut self, value: u16) {
        self.current().write_u16(value);
    }
    fn write_u32(&mut self, value: u32) {
        self.current().write_u32(value);
    }
    fn write_u64(&mut self, value: u64) {
        self.current().write_u64(value);
    }
    fn write_u128(&mut self, value: u128) {
        self.current().write_u128(value);
    }
    fn write_usize(&mut self, value: usize) {
        self.current().write_usize(value);
    }
    fn write_i8(&mut self, value: i8) {
        self.current().write_i8(value);
    }
    fn write_i16(&mut self, value: i16) {
        self.current().write_i16(value);
    }
    fn write_i32(&mut self, value: i32) {
        self.current().write_i32(value);
    }
    fn write_i64(&mut self, value: i64) {
        self.current().write_i64(value);
    }
    fn write_i128(&mut self, value: i128) {
        self.current().write_i128(value);
    }
    fn write_isize(&mut self, value: isize) {
        self.current().write_isize(value);
    }
}

impl SemanticSink for ComposingSemanticSink<'_, '_> {
    const COMPOSES_KEYS: bool = true;

    fn max_key_bytes(&self) -> usize {
        self.transaction.max_key_bytes()
    }

    fn record_key_error(&mut self, error: crate::ContentKeyCacheError) {
        self.error.get_or_insert(error);
    }

    fn write_exact_key(&mut self, key: crate::ContentKey) {
        self.current().push_framed_key(key);
    }

    fn begin_node(&mut self, identity: crate::ContentKeyNodeIdentity, cacheable: bool) -> bool {
        if cacheable {
            if let Some(key) = self.transaction.get_identity(identity) {
                self.append_key(key);
                return true;
            }
        }
        self.frames
            .push(crate::SemanticKeyBuilder::with_max_bytes(self.transaction.max_key_bytes()));
        false
    }

    fn finish_node(&mut self, identity: crate::ContentKeyNodeIdentity, cacheable: bool) {
        let Some(frame) = self.frames.pop() else {
            self.error
                .get_or_insert(crate::ContentKeyCacheError::ConstructionInvariant);
            return;
        };
        let mut key = match frame.into_key() {
            Ok(key) => key,
            Err(error) => {
                self.error.get_or_insert(error);
                return;
            },
        };
        if cacheable {
            // SAFETY: generated tasks mark only nodes transitively
            // owned by the transaction's retained immutable AST root.
            match unsafe { self.transaction.stage_identity(identity, key.clone()) } {
                Ok(shared) => key = shared,
                Err(error) => {
                    self.error.get_or_insert(error);
                },
            }
        }
        self.append_key(key);
    }
}

/// Original iterative task loop; task dispatch stays with the caller's typed
/// observation. No recursive public-method re-entry is introduced.
pub fn drain<T, H>(
    stack: &mut Vec<T>,
    state: &mut H,
    mut dispatch: impl FnMut(T, &mut Vec<T>, &mut H),
) {
    while let Some(task) = stack.pop() {
        dispatch(task, stack, state);
    }
}

/// Original category-handler prelude. The identity and finish task are observed
/// only in composing mode; a cache hit skips both scheduling and the visitor.
pub fn visit_node<T, H: SemanticSink>(
    stack: &mut Vec<T>,
    state: &mut H,
    cacheable: bool,
    identity: impl FnOnce() -> crate::ContentKeyNodeIdentity,
    finish: impl FnOnce(crate::ContentKeyNodeIdentity, bool) -> T,
    visit: impl FnOnce(&mut Vec<T>, &mut H),
) {
    if H::COMPOSES_KEYS {
        let identity = identity();
        if state.begin_node(identity, cacheable) {
            return;
        }
        stack.push(finish(identity, cacheable));
    }
    visit(stack, state);
}

/// The original constructor arm writes its tag before scheduling its fields.
pub fn tagged<T, H: std::hash::Hasher, R>(
    stack: &mut Vec<T>,
    state: &mut H,
    tag: u8,
    fields: impl FnOnce(&mut Vec<T>, &mut H) -> R,
) -> R {
    state.write_u8(tag);
    fields(stack, state)
}

/// Original transparent-constructor arm: no discriminant write.
pub fn transparent<T>(stack: &mut Vec<T>, child: impl FnOnce() -> T) {
    stack.push(child());
}

/// Original ordered collection body. In particular, length is observed after
/// reverse scheduling, but its task is popped before the first element.
pub fn ordered<T, I: DoubleEndedIterator>(
    stack: &mut Vec<T>,
    elements: I,
    mut child: impl FnMut(I::Item) -> T,
    len: impl FnOnce() -> usize,
    length: impl FnOnce(usize) -> T,
) {
    for element in elements.rev() {
        stack.push(child(element));
    }
    stack.push(length(len()));
}

/// Original nonnumeric literal arm, including its Rust Hash implementation.
pub fn literal<H: std::hash::Hasher, V: std::hash::Hash + ?Sized>(
    state: &mut H,
    tag: u8,
    value: &V,
) {
    state.write_u8(tag);
    std::hash::Hash::hash(value, state);
}

/// Original numeric arm; canonical-byte computation remains at its old site.
pub fn numeric<H: std::hash::Hasher>(state: &mut H, tag: u8, canonical: impl FnOnce() -> Vec<u8>) {
    state.write_u8(tag);
    let numeric_canon: Vec<u8> = canonical();
    state.write_usize(numeric_canon.len());
    state.write(numeric_canon.as_slice());
}

/// Original uniform variable tag, before observing its Free/Bound payload.
pub fn variable<H: std::hash::Hasher>(state: &mut H, payload: impl FnOnce(&mut H)) {
    state.write_u8(0xFBu8);
    payload(state);
}

/// Original free-variable branch. Native allocation identity is not read.
pub fn free_variable<'a, H: std::hash::Hasher>(
    state: &mut H,
    name: impl FnOnce() -> Option<&'a str>,
) {
    state.write_u8(0u8);
    match name() {
        Some(name) => {
            state.write_u8(1u8);
            std::hash::Hash::hash(name, state);
        },
        None => state.write_u8(0u8),
    }
}

/// Original bound-variable branch, retaining scope-before-binder Hash calls.
pub fn bound_variable<H: std::hash::Hasher>(
    state: &mut H,
    scope: impl FnOnce(&mut H),
    binder: impl FnOnce(&mut H),
) {
    state.write_u8(1u8);
    scope(state);
    binder(state);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FramedSemanticKeyHasher;
    use std::hash::Hasher;

    #[test]
    fn shared_variable_and_literal_keep_original_framed_writes() {
        let mut actual = FramedSemanticKeyHasher::default();
        variable(&mut actual, |state| free_variable(state, || Some("a")));
        let mut original = FramedSemanticKeyHasher::default();
        original.write_u8(0xFB);
        original.write_u8(0);
        original.write_u8(1);
        std::hash::Hash::hash("a", &mut original);
        assert_eq!(actual.into_key(), original.into_key());

        let mut actual = FramedSemanticKeyHasher::default();
        literal(&mut actual, 1, &"a".to_owned());
        let mut original = FramedSemanticKeyHasher::default();
        original.write_u8(1);
        std::hash::Hash::hash(&"a".to_owned(), &mut original);
        assert_eq!(actual.into_key(), original.into_key());
    }

    #[test]
    fn ordered_worker_keeps_length_then_source_order() {
        let mut stack = Vec::new();
        let values = [11, 22, 33];
        ordered(&mut stack, values.iter(), |value| *value, || values.len(), |len| len);
        let mut popped = Vec::new();
        drain(&mut stack, &mut popped, |task, _, popped| popped.push(task));
        assert_eq!(popped, [3, 11, 22, 33]);
    }

    #[test]
    fn composing_transparent_parent_keeps_exact_child_stream() {
        use crate::{ContentKeyCache, ContentKeyNodeIdentity};
        use std::sync::Arc;
        let owner = Arc::new(("a".to_owned(),));
        let parent = ContentKeyNodeIdentity::of_ref(owner.as_ref());
        let child = ContentKeyNodeIdentity::of_ref(&owner.0);
        let mut cache = ContentKeyCache::default();
        let mut transaction = cache.transaction_for_root(owner.clone());
        // SAFETY: both identities are immutable descendants of retained owner.
        let mut sink = unsafe { ComposingSemanticSink::new(&mut transaction) };
        assert!(!sink.begin_node(parent, true));
        assert!(!sink.begin_node(child, true));
        variable(&mut sink, |state| free_variable(state, || Some(owner.0.as_str())));
        sink.finish_node(child, true);
        sink.finish_node(parent, true);
        let key = sink
            .into_result()
            .expect("balanced original visitor frames");
        transaction.commit().expect("complete transaction");
        let mut flat = FramedSemanticKeyHasher::default();
        variable(&mut flat, |state| free_variable(state, || Some("a")));
        assert_eq!(key.as_bytes(), flat.into_key());
    }
}
