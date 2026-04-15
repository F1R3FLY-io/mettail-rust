//! Channel Infrastructure for PraTTaIL Green Threads (Sprint GT-1).
//!
//! Provides the communication primitives for green-thread-based concurrent
//! parsing, modeled after the Rholang pi-calculus channel semantics:
//!
//! | Concept | Rholang | PraTTaIL |
//! |---------|---------|----------|
//! | Channel send | `ch!(@data)` | `channel.send(msg)` |
//! | Channel receive | `for (@x <- ch)` | `channel.try_recv()` / `recv_blocking()` |
//! | Join pattern | `for (@x <- a; @y <- b)` | `JoinPatternSpec { channels: [a, b] }` |
//!
//! ## Architecture
//!
//! ```text
//! ┌───────────────────────────────────────────────────────┐
//! │                    ChannelMap                          │
//! │  DashMap<ChannelId, ChannelHandle>  (lock-free)       │
//! │  DashMap<String, ChannelId>         (name→id)         │
//! │  AtomicU64                          (next_id)         │
//! │                                                       │
//! │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐   │
//! │  │ Channel<A>  │  │ Channel<B>  │  │ Channel<C>  │   │
//! │  │ crossbeam   │  │ crossbeam   │  │ crossbeam   │   │
//! │  │ sender/recv │  │ sender/recv │  │ sender/recv │   │
//! │  └─────────────┘  └─────────────┘  └─────────────┘   │
//! └───────────────────────────────────────────────────────┘
//! ```
//!
//! All runtime data structures are **non-blocking**:
//! - [`Channel`] wraps `crossbeam_channel` (lock-free MPMC).
//! - [`ChannelMap`] uses `DashMap` (lock-free concurrent hash map).
//! - Waiter counts use `AtomicU64` with `Ordering::Relaxed` (no contention).
//!
//! ## Feature Gate
//!
//! This module is gated on `feature = "green-threads"`, which transitively
//! enables `cek-runtime` and pulls in `im`, `crossbeam-channel`, `dashmap`,
//! and `num_cpus`.
//!
//! ## References
//!
//! - Milner, R. (1999). *Communicating and Mobile Systems: the Pi-Calculus*.
//!   Cambridge University Press.
//! - Fournet, C. & Gonthier, G. (1996). The reflexive CHAM and the join-calculus.
//!   *Proceedings of POPL*, pp. 372–385.

use std::any::Any;
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use crossbeam_channel::{Receiver, Sender};
use dashmap::DashMap;

// ══════════════════════════════════════════════════════════════════════════════
// Identifiers
// ══════════════════════════════════════════════════════════════════════════════

/// Unique identifier for a channel.
///
/// Channels are identified by monotonically increasing 64-bit integers,
/// allocated via [`ChannelMap::fresh_id()`]. The inner value is public
/// for serialization and debugging but should not be constructed manually
/// outside of test code.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ChannelId(pub u64);

impl fmt::Display for ChannelId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ch#{}", self.0)
    }
}

/// Unique identifier for a green thread.
///
/// Green threads are lightweight, cooperatively scheduled parse fibers.
/// Each green thread has a persistent continuation stack (via the `im` crate)
/// and communicates through channels.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GreenThreadId(pub u64);

impl fmt::Display for GreenThreadId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "gt#{}", self.0)
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// AST Specifications (compile-time grammar representation)
// ══════════════════════════════════════════════════════════════════════════════

/// Capacity configuration for a channel.
///
/// Unbounded channels use `crossbeam_channel::unbounded()`, which allocates
/// in segments and never blocks on send. Bounded channels use
/// `crossbeam_channel::bounded(cap)`, which blocks senders when full (but
/// our green-thread scheduler will yield instead of OS-blocking).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChannelCapacity {
    /// No upper bound on buffered messages.
    Unbounded,
    /// Fixed-capacity buffer; senders must wait when full.
    Bounded(usize),
}

impl Default for ChannelCapacity {
    fn default() -> Self {
        Self::Unbounded
    }
}

impl fmt::Display for ChannelCapacity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unbounded => write!(f, "unbounded"),
            Self::Bounded(cap) => write!(f, "bounded({})", cap),
        }
    }
}

/// AST representation of a channel declaration from the `channels {}` block.
///
/// ```text
/// channels {
///     tokens: Channel<Token> bounded(1024);
///     errors: Channel<ParseError>;          // unbounded (default)
///     signals: Channel;                     // untyped
/// }
/// ```
#[derive(Debug, Clone)]
pub struct ChannelSpec {
    /// Channel name (e.g., "tokens", "errors", "signals").
    pub name: String,
    /// Rust type of messages. `None` means untyped (erased to `Box<dyn Any + Send>`).
    pub element_type: Option<String>,
    /// Buffer capacity. Default: `ChannelCapacity::Unbounded`.
    pub capacity: ChannelCapacity,
}

impl ChannelSpec {
    /// Create a new channel specification with default (unbounded) capacity.
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            element_type: None,
            capacity: ChannelCapacity::default(),
        }
    }

    /// Create a typed channel specification with default (unbounded) capacity.
    pub fn typed(name: impl Into<String>, element_type: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            element_type: Some(element_type.into()),
            capacity: ChannelCapacity::default(),
        }
    }

    /// Create a bounded channel specification.
    pub fn bounded(name: impl Into<String>, capacity: usize) -> Self {
        Self {
            name: name.into(),
            element_type: None,
            capacity: ChannelCapacity::Bounded(capacity),
        }
    }
}

/// A reference to a channel within a join pattern, binding a name to received data.
///
/// In Rholang syntax: `for (@x <- ch)` becomes
/// `JoinChannelRef { channel_name: "ch", binding_name: "x" }`.
#[derive(Debug, Clone)]
pub struct JoinChannelRef {
    /// Name of the channel to receive from.
    pub channel_name: String,
    /// Name to bind the received value to in the join body.
    pub binding_name: String,
}

/// AST for a join pattern: simultaneous receive on multiple channels.
///
/// ```text
/// join recv_and_proc {
///     @token <- tokens;
///     @error <- errors;
/// }
/// ```
///
/// A join pattern fires only when ALL referenced channels have a message
/// available. This is the foundation for Rholang-style concurrent reduction:
/// `for (@x <- a; @y <- b) { P }`.
#[derive(Debug, Clone)]
pub struct JoinPatternSpec {
    /// Join pattern name (for diagnostics and debugging).
    pub name: String,
    /// Channels to simultaneously receive from.
    pub channels: Vec<JoinChannelRef>,
}

impl JoinPatternSpec {
    /// Number of channels in this join pattern.
    pub fn arity(&self) -> usize {
        self.channels.len()
    }
}

/// The full `channels {}` block specification.
///
/// Contains both individual channel declarations and join patterns.
/// Parsed from the `channels { ... }` block in the `language!` macro.
#[derive(Debug, Clone, Default)]
pub struct ChannelsBlockSpec {
    /// Individual channel declarations.
    pub channels: Vec<ChannelSpec>,
    /// Join pattern declarations.
    pub join_patterns: Vec<JoinPatternSpec>,
}

impl ChannelsBlockSpec {
    /// Create an empty channels block.
    pub fn new() -> Self {
        Self::default()
    }

    /// Whether this block has any declarations.
    pub fn is_empty(&self) -> bool {
        self.channels.is_empty() && self.join_patterns.is_empty()
    }

    /// Total number of declarations (channels + join patterns).
    pub fn len(&self) -> usize {
        self.channels.len() + self.join_patterns.len()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Runtime Channel (lock-free MPMC via crossbeam)
// ══════════════════════════════════════════════════════════════════════════════

/// A runtime lock-free MPMC channel wrapping `crossbeam_channel`.
///
/// Each `Channel<T>` maintains a waiter count for the scheduler: when a
/// green thread blocks on `recv`, it registers as a waiter so the scheduler
/// knows which threads to wake when a message arrives.
///
/// The `Sender` and `Receiver` are both `Clone + Send + Sync`, so a channel
/// can be shared across multiple green threads without additional locking.
pub struct Channel<T: Send + 'static> {
    /// This channel's unique identifier.
    id: ChannelId,
    /// Human-readable name (for diagnostics).
    name: String,
    /// The crossbeam sender half.
    sender: Sender<T>,
    /// The crossbeam receiver half.
    receiver: Receiver<T>,
    /// Number of green threads currently waiting to receive on this channel.
    /// Updated atomically; used by the scheduler for wake-up decisions.
    waiter_count: AtomicU64,
}

impl<T: Send + 'static> Channel<T> {
    /// Create a new unbounded channel.
    pub fn unbounded(id: ChannelId, name: impl Into<String>) -> Self {
        let (sender, receiver) = crossbeam_channel::unbounded();
        Self {
            id,
            name: name.into(),
            sender,
            receiver,
            waiter_count: AtomicU64::new(0),
        }
    }

    /// Create a new bounded channel with the given capacity.
    pub fn bounded(id: ChannelId, name: impl Into<String>, capacity: usize) -> Self {
        let (sender, receiver) = crossbeam_channel::bounded(capacity);
        Self {
            id,
            name: name.into(),
            sender,
            receiver,
            waiter_count: AtomicU64::new(0),
        }
    }

    /// Create a channel from a [`ChannelCapacity`] specification.
    pub fn from_capacity(
        id: ChannelId,
        name: impl Into<String>,
        capacity: &ChannelCapacity,
    ) -> Self {
        match capacity {
            ChannelCapacity::Unbounded => Self::unbounded(id, name),
            ChannelCapacity::Bounded(cap) => Self::bounded(id, name, *cap),
        }
    }

    /// This channel's unique identifier.
    pub fn id(&self) -> ChannelId {
        self.id
    }

    /// This channel's name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Send a message on this channel.
    ///
    /// For unbounded channels, this never blocks.
    /// For bounded channels, this blocks the OS thread if the buffer is full.
    /// (The green-thread scheduler should yield before calling this on bounded
    /// channels to avoid blocking the worker thread.)
    ///
    /// Returns `Err` if all receivers have been dropped.
    pub fn send(&self, msg: T) -> Result<(), crossbeam_channel::SendError<T>> {
        self.sender.send(msg)
    }

    /// Try to receive a message without blocking.
    ///
    /// Returns `Ok(msg)` if a message was available, or `Err` indicating
    /// either the channel is empty or disconnected.
    pub fn try_recv(&self) -> Result<T, crossbeam_channel::TryRecvError> {
        self.receiver.try_recv()
    }

    /// Receive a message, blocking the current OS thread until one is available.
    ///
    /// **Warning**: In green-thread contexts, prefer `try_recv()` with scheduler
    /// yield to avoid blocking the worker thread. This method is provided for
    /// testing and for use in non-green-thread contexts.
    ///
    /// Returns `Err` if all senders have been dropped and the channel is empty.
    pub fn recv_blocking(&self) -> Result<T, crossbeam_channel::RecvError> {
        self.receiver.recv()
    }

    /// Number of green threads currently waiting on this channel.
    pub fn waiter_count(&self) -> u64 {
        self.waiter_count.load(Ordering::Relaxed)
    }

    /// Register a green thread as waiting on this channel.
    ///
    /// Called by the scheduler when a green thread suspends on `recv`.
    /// The returned previous count can be used for diagnostics.
    pub fn register_waiter(&self) -> u64 {
        self.waiter_count.fetch_add(1, Ordering::Relaxed)
    }

    /// Unregister a green thread that is no longer waiting on this channel.
    ///
    /// Called by the scheduler when a green thread is woken up after
    /// receiving a message (or is cancelled).
    ///
    /// Uses saturating subtraction to avoid underflow if unregister is
    /// called without a matching register (defensive programming).
    pub fn unregister_waiter(&self) -> u64 {
        // Relaxed CAS loop for saturating decrement.
        loop {
            let current = self.waiter_count.load(Ordering::Relaxed);
            if current == 0 {
                return 0;
            }
            match self.waiter_count.compare_exchange_weak(
                current,
                current - 1,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(prev) => return prev,
                Err(_) => continue, // Spurious CAS failure, retry.
            }
        }
    }

    /// Number of messages currently buffered in the channel.
    pub fn len(&self) -> usize {
        self.receiver.len()
    }

    /// Whether the channel buffer is empty.
    pub fn is_empty(&self) -> bool {
        self.receiver.is_empty()
    }

    /// Clone the sender half (for distributing to multiple producers).
    pub fn sender(&self) -> Sender<T> {
        self.sender.clone()
    }

    /// Clone the receiver half (for distributing to multiple consumers).
    pub fn receiver(&self) -> Receiver<T> {
        self.receiver.clone()
    }
}

impl<T: Send + 'static> fmt::Debug for Channel<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Channel")
            .field("id", &self.id)
            .field("name", &self.name)
            .field("waiter_count", &self.waiter_count.load(Ordering::Relaxed))
            .field("buffered", &self.receiver.len())
            .finish()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Type-Erased Channel Handle
// ══════════════════════════════════════════════════════════════════════════════

/// A type-erased handle to a [`Channel<T>`], stored in [`ChannelMap`].
///
/// Uses `Arc<dyn Any + Send + Sync>` for type erasure. Consumers downcast
/// back to `Arc<Channel<T>>` via [`ChannelHandle::downcast()`].
///
/// The `pending_check` closure provides a type-erased way to check if
/// the channel has pending messages without knowing the concrete message type.
#[derive(Clone)]
pub struct ChannelHandle {
    /// The type-erased channel.
    inner: Arc<dyn Any + Send + Sync>,
    /// Channel name, cached for diagnostics without downcasting.
    name: String,
    /// Channel id, cached for O(1) access without downcasting.
    id: ChannelId,
    /// Type-erased check for pending messages.
    /// Captures the channel's `Receiver::is_empty()` at construction time.
    pending_check: Arc<dyn Fn() -> bool + Send + Sync>,
    /// Reference count for CESK GC lifecycle tracking.
    ///
    /// Tracks how many `StoreValue::ChannelRef` entries point to this channel.
    /// When the count reaches zero (all refs garbage collected), the channel
    /// can be removed from the `ChannelMap`.
    gc_refcount: Arc<AtomicU64>,
}

impl ChannelHandle {
    /// Wrap a `Channel<T>` into a type-erased handle.
    ///
    /// Captures a clone of the channel's `Receiver` to enable type-erased
    /// pending message checks via [`has_pending()`](Self::has_pending).
    pub fn new<T: Send + 'static>(channel: Channel<T>) -> Self {
        let id = channel.id;
        let name = channel.name.clone();
        // Clone the receiver before moving the channel into Arc.
        // The cloned receiver shares the same underlying buffer.
        let recv_clone = channel.receiver();
        let pending_check = Arc::new(move || !recv_clone.is_empty())
            as Arc<dyn Fn() -> bool + Send + Sync>;
        Self {
            inner: Arc::new(channel),
            name,
            id,
            pending_check,
            gc_refcount: Arc::new(AtomicU64::new(1)), // Initial ref from creator
        }
    }

    /// Increment the GC reference count for this channel.
    ///
    /// Called when a new `StoreValue::ChannelRef` is created pointing to this channel.
    pub fn gc_inc_ref(&self) -> u64 {
        self.gc_refcount.fetch_add(1, Ordering::Relaxed)
    }

    /// Decrement the GC reference count for this channel.
    ///
    /// Called by the GC when a `StoreValue::ChannelRef` is collected.
    /// Returns the new refcount. When it reaches zero, the channel
    /// can be removed from the `ChannelMap`.
    pub fn gc_dec_ref(&self) -> u64 {
        let prev = self.gc_refcount.fetch_sub(1, Ordering::Relaxed);
        prev.saturating_sub(1)
    }

    /// Current GC reference count.
    pub fn gc_ref_count(&self) -> u64 {
        self.gc_refcount.load(Ordering::Relaxed)
    }

    /// Attempt to downcast to a concrete `Channel<T>`.
    ///
    /// Returns `None` if the channel's message type does not match `T`.
    pub fn downcast<T: Send + 'static>(&self) -> Option<&Channel<T>> {
        self.inner.downcast_ref::<Channel<T>>()
    }

    /// Attempt to get a cloned `Arc<Channel<T>>` for shared ownership.
    ///
    /// Returns `None` if the channel's message type does not match `T`.
    pub fn downcast_arc<T: Send + 'static>(&self) -> Option<Arc<Channel<T>>> {
        // Clone the Arc, then attempt downcast.
        let cloned: Arc<dyn Any + Send + Sync> = Arc::clone(&self.inner);
        Arc::downcast::<Channel<T>>(cloned).ok()
    }

    /// The cached channel name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The cached channel id.
    pub fn id(&self) -> ChannelId {
        self.id
    }

    /// Whether this channel has pending (unread) messages.
    ///
    /// This check is type-erased: it works without knowing the concrete
    /// message type `T`. Uses a captured `Receiver::is_empty()` closure.
    pub fn has_pending(&self) -> bool {
        (self.pending_check)()
    }
}

impl fmt::Debug for ChannelHandle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ChannelHandle")
            .field("id", &self.id)
            .field("name", &self.name)
            .finish()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Channel Map (lock-free concurrent registry)
// ══════════════════════════════════════════════════════════════════════════════

/// Lock-free concurrent map of channels.
///
/// The central registry for all channels in a green-thread runtime.
/// Uses [`DashMap`] for concurrent access without global locking.
///
/// ## Thread Safety
///
/// All operations are lock-free (DashMap uses fine-grained sharding internally).
/// Multiple green threads / OS threads can create, look up, and remove channels
/// concurrently without contention.
///
/// ## ID Allocation
///
/// Channel IDs are allocated via a monotonically increasing `AtomicU64`.
/// This guarantees uniqueness without locking (assuming no overflow of u64,
/// which is infeasible in practice).
pub struct ChannelMap {
    /// Channel ID → type-erased channel handle.
    channels: DashMap<ChannelId, ChannelHandle>,
    /// Channel name → channel ID (reverse lookup).
    name_to_id: DashMap<String, ChannelId>,
    /// Monotonically increasing ID counter.
    next_id: AtomicU64,
}

impl ChannelMap {
    /// Create a new empty channel map.
    pub fn new() -> Self {
        Self {
            channels: DashMap::new(),
            name_to_id: DashMap::new(),
            next_id: AtomicU64::new(0),
        }
    }

    /// Create a new channel map with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            channels: DashMap::with_capacity(capacity),
            name_to_id: DashMap::with_capacity(capacity),
            next_id: AtomicU64::new(0),
        }
    }

    /// Allocate a fresh, globally unique [`ChannelId`].
    ///
    /// IDs are monotonically increasing and never reused within a single
    /// `ChannelMap` instance.
    pub fn fresh_id(&self) -> ChannelId {
        ChannelId(self.next_id.fetch_add(1, Ordering::Relaxed))
    }

    /// Create a new channel and register it in the map.
    ///
    /// Returns the new channel's ID. If a channel with the same name already
    /// exists, the old channel is replaced (last-writer-wins semantics).
    pub fn create_channel<T: Send + 'static>(
        &self,
        name: impl Into<String>,
        capacity: &ChannelCapacity,
    ) -> ChannelId {
        let name = name.into();
        let id = self.fresh_id();
        let channel = Channel::<T>::from_capacity(id, &name, capacity);
        let handle = ChannelHandle::new(channel);
        self.channels.insert(id, handle);
        self.name_to_id.insert(name, id);
        id
    }

    /// Look up a channel handle by ID.
    ///
    /// Returns `None` if no channel with the given ID exists.
    pub fn get_channel(&self, id: ChannelId) -> Option<ChannelHandle> {
        self.channels.get(&id).map(|entry| entry.value().clone())
    }

    /// Look up a channel ID by name.
    ///
    /// Returns `None` if no channel with the given name exists.
    pub fn get_id_by_name(&self, name: &str) -> Option<ChannelId> {
        self.name_to_id.get(name).map(|entry| *entry.value())
    }

    /// Look up a channel handle by name.
    ///
    /// Convenience method combining `get_id_by_name` + `get_channel`.
    pub fn get_channel_by_name(&self, name: &str) -> Option<ChannelHandle> {
        let id = self.get_id_by_name(name)?;
        self.get_channel(id)
    }

    /// Remove a channel from the map.
    ///
    /// Returns the removed handle, or `None` if the channel did not exist.
    /// Also removes the name→ID mapping.
    pub fn remove_channel(&self, id: ChannelId) -> Option<ChannelHandle> {
        let removed = self.channels.remove(&id);
        if let Some((_, ref handle)) = removed {
            self.name_to_id.remove(handle.name());
        }
        removed.map(|(_, handle)| handle)
    }

    /// Number of channels currently registered.
    pub fn channel_count(&self) -> usize {
        self.channels.len()
    }

    /// Whether the map is empty.
    pub fn is_empty(&self) -> bool {
        self.channels.is_empty()
    }

    /// Iterate over all channel IDs.
    ///
    /// Note: The iteration is a snapshot — channels may be added or removed
    /// concurrently. This is consistent with DashMap's iteration semantics.
    pub fn channel_ids(&self) -> Vec<ChannelId> {
        self.channels.iter().map(|entry| *entry.key()).collect()
    }

    /// Iterate over all channel names.
    pub fn channel_names(&self) -> Vec<String> {
        self.name_to_id.iter().map(|entry| entry.key().clone()).collect()
    }

    /// Decrement the GC reference count for a channel.
    ///
    /// Called by the GC when a `StoreValue::ChannelRef(ch_id)` is collected.
    /// Returns the new refcount. If the count reaches zero, the channel
    /// can be removed from the map (caller's responsibility).
    pub fn gc_dec_ref(&self, id: ChannelId) -> u64 {
        if let Some(handle) = self.channels.get(&id) {
            handle.gc_dec_ref()
        } else {
            0
        }
    }

    /// Increment the GC reference count for a channel.
    ///
    /// Called when a new `StoreValue::ChannelRef` is created.
    pub fn gc_inc_ref(&self, id: ChannelId) {
        if let Some(handle) = self.channels.get(&id) {
            handle.gc_inc_ref();
        }
    }
}

impl Default for ChannelMap {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for ChannelMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ChannelMap")
            .field("channel_count", &self.channels.len())
            .field("next_id", &self.next_id.load(Ordering::Relaxed))
            .finish()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Channel Waiter (scheduler integration)
// ══════════════════════════════════════════════════════════════════════════════

/// The pattern a green thread is waiting on.
///
/// Determines how the scheduler decides when to wake a suspended thread:
/// - [`Single`]: Wake when the specified channel has a message.
/// - [`Join`]: Wake only when ALL specified channels have messages.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WaitPattern {
    /// Waiting on a single channel: `for (@x <- ch) { ... }`.
    Single,
    /// Join pattern: waiting on multiple channels simultaneously.
    /// All channels must have a message before the thread is woken.
    ///
    /// The `Vec<ChannelId>` lists the additional channels beyond the
    /// primary channel in the [`ChannelWaiter`].
    Join(Vec<ChannelId>),
}

impl fmt::Display for WaitPattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Single => write!(f, "Single"),
            Self::Join(ids) => {
                write!(f, "Join(")?;
                for (i, id) in ids.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", id)?;
                }
                write!(f, ")")
            }
        }
    }
}

/// Registration for a green thread waiting on a channel.
///
/// Created by the scheduler when a green thread suspends on a `recv` or
/// join pattern. Used to track which threads need to be woken when
/// messages arrive.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChannelWaiter {
    /// The green thread that is waiting.
    pub thread_id: GreenThreadId,
    /// The primary channel being waited on.
    pub channel_id: ChannelId,
    /// The wait pattern (single receive or join).
    pub pattern: WaitPattern,
}

impl ChannelWaiter {
    /// Create a waiter for a single-channel receive.
    pub fn single(thread_id: GreenThreadId, channel_id: ChannelId) -> Self {
        Self {
            thread_id,
            channel_id,
            pattern: WaitPattern::Single,
        }
    }

    /// Create a waiter for a join pattern.
    pub fn join(
        thread_id: GreenThreadId,
        primary_channel: ChannelId,
        additional_channels: Vec<ChannelId>,
    ) -> Self {
        Self {
            thread_id,
            channel_id: primary_channel,
            pattern: WaitPattern::Join(additional_channels),
        }
    }

    /// All channel IDs involved in this wait (primary + join).
    pub fn all_channels(&self) -> Vec<ChannelId> {
        let mut result = vec![self.channel_id];
        if let WaitPattern::Join(ref extras) = self.pattern {
            result.extend_from_slice(extras);
        }
        result
    }

    /// Whether this is a join pattern (waiting on multiple channels).
    pub fn is_join(&self) -> bool {
        matches!(self.pattern, WaitPattern::Join(_))
    }
}

impl fmt::Display for ChannelWaiter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Waiter({} on {} pattern={})",
            self.thread_id, self.channel_id, self.pattern
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WakeRegistry — Maps channels to suspended green threads
// ══════════════════════════════════════════════════════════════════════════════

/// Registry tracking which green threads are waiting on which channels.
///
/// Used by the coordinator to wake suspended threads when channel messages
/// arrive. Thread-safe via `DashMap` for concurrent access.
///
/// ## Wake-up Protocol
///
/// 1. Worker executes thread T, which suspends on channel C.
/// 2. Worker sends `ThreadSuspended { tid: T, waiting_on: [C] }` to coordinator.
/// 3. Coordinator calls `register(C, T)` on the WakeRegistry.
/// 4. Coordinator periodically calls `check_and_wake()` with the `ChannelMap`.
/// 5. If channel C has messages, coordinator takes waiters and resumes them.
pub struct WakeRegistry {
    /// Map from channel ID to list of green threads waiting on that channel.
    waiters: DashMap<ChannelId, Vec<GreenThreadId>>,
}

impl WakeRegistry {
    /// Create a new empty wake registry.
    pub fn new() -> Self {
        Self {
            waiters: DashMap::new(),
        }
    }

    /// Register a green thread as waiting on a channel.
    ///
    /// A thread can wait on multiple channels (join pattern). Call this
    /// once per channel in the wait set.
    pub fn register(&self, channel_id: ChannelId, thread_id: GreenThreadId) {
        self.waiters
            .entry(channel_id)
            .or_default()
            .push(thread_id);
    }

    /// Unregister a green thread from a channel's waiter list.
    ///
    /// Called when a thread is woken or cancelled. Removes only the first
    /// matching entry (a thread could theoretically wait on the same channel
    /// from multiple join patterns, though this is unusual).
    pub fn unregister(&self, channel_id: ChannelId, thread_id: GreenThreadId) {
        if let Some(mut waiters) = self.waiters.get_mut(&channel_id) {
            if let Some(pos) = waiters.iter().position(|&id| id == thread_id) {
                waiters.swap_remove(pos);
            }
            if waiters.is_empty() {
                drop(waiters);
                self.waiters.remove(&channel_id);
            }
        }
    }

    /// Take all waiters for a channel, removing them from the registry.
    ///
    /// Returns the list of green thread IDs that were waiting. The caller
    /// is responsible for resuming these threads (transitioning them from
    /// Suspended to Ready and enqueuing them).
    pub fn take_waiters(&self, channel_id: ChannelId) -> Vec<GreenThreadId> {
        self.waiters
            .remove(&channel_id)
            .map(|(_, waiters)| waiters)
            .unwrap_or_default()
    }

    /// List all channel IDs that have at least one waiter.
    pub fn channels_with_waiters(&self) -> Vec<ChannelId> {
        self.waiters.iter().map(|entry| *entry.key()).collect()
    }

    /// Total number of channels with registered waiters.
    pub fn channel_count(&self) -> usize {
        self.waiters.len()
    }

    /// Total number of registered waiters across all channels.
    pub fn total_waiters(&self) -> usize {
        self.waiters
            .iter()
            .map(|entry| entry.value().len())
            .sum()
    }

    /// Register a join-pattern waiter: a thread waiting on ALL of the given channels.
    ///
    /// Equivalent to calling `register(ch_id, thread_id)` for each channel in
    /// the join set. The caller is responsible for maintaining the join-set mapping
    /// externally (e.g., in the coordinator's `join_sets` HashMap) so that
    /// `check_and_wake_join` can verify all-channel readiness.
    pub fn register_join(
        &self,
        thread_id: GreenThreadId,
        channels: &[ChannelId],
    ) {
        for &ch_id in channels {
            self.register(ch_id, thread_id);
        }
    }

    /// Check join patterns: wake threads only when ALL their channels have pending messages.
    ///
    /// Iterates waiters on channels with pending messages. For each thread found
    /// in `join_sets`, checks if ALL channels the thread is registered on also
    /// have pending messages. Only wakes threads where the full join set is satisfied.
    /// Single-channel waiters are handled by [`check_and_wake()`].
    ///
    /// Returns threads to wake with the channel that triggered the check.
    pub fn check_and_wake_join(
        &self,
        channel_map: &ChannelMap,
        join_sets: &std::collections::HashMap<GreenThreadId, Vec<ChannelId>>,
    ) -> Vec<(GreenThreadId, ChannelId)> {
        let mut to_wake = Vec::new();
        let mut already_checked = std::collections::HashSet::new();

        for entry in self.waiters.iter() {
            let channel_id = *entry.key();
            if let Some(handle) = channel_map.get_channel(channel_id) {
                if !handle.has_pending() {
                    continue;
                }

                for &tid in entry.value().iter() {
                    if already_checked.contains(&tid) {
                        continue;
                    }
                    already_checked.insert(tid);

                    // Check if this thread has a join set.
                    if let Some(join_channels) = join_sets.get(&tid) {
                        // All channels in the join set must have pending messages.
                        let all_ready = join_channels.iter().all(|ch| {
                            channel_map
                                .get_channel(*ch)
                                .map(|h| h.has_pending())
                                .unwrap_or(false)
                        });
                        if all_ready {
                            to_wake.push((tid, channel_id));
                        }
                    }
                    // Single-channel waiters are not handled here
                    // (they use check_and_wake instead).
                }
            }
        }

        // Unregister woken threads from ALL their join channels.
        for &(tid, _) in &to_wake {
            if let Some(join_channels) = join_sets.get(&tid) {
                for &ch_id in join_channels {
                    self.unregister(ch_id, tid);
                }
            }
        }

        to_wake
    }

    /// Check all channels for pending messages and return threads to wake.
    ///
    /// Iterates over all channels with registered waiters, checks if the
    /// channel has pending messages via `ChannelMap`, and returns the
    /// threads that should be woken.
    ///
    /// This is a polling-based approach. The coordinator calls this
    /// periodically. Event-driven wake-ups via `WorkerReport::ChannelActivity`
    /// handle the fast path; this method serves as a fallback.
    pub fn check_and_wake(&self, channel_map: &ChannelMap) -> Vec<(GreenThreadId, ChannelId)> {
        let mut to_wake = Vec::new();
        let channels = self.channels_with_waiters();
        for channel_id in channels {
            if let Some(handle) = channel_map.get_channel(channel_id) {
                if handle.has_pending() {
                    let waiters = self.take_waiters(channel_id);
                    for tid in waiters {
                        to_wake.push((tid, channel_id));
                    }
                }
            }
        }
        to_wake
    }
}

impl Default for WakeRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for WakeRegistry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WakeRegistry")
            .field("channels", &self.waiters.len())
            .field("total_waiters", &self.total_waiters())
            .finish()
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    // ── ChannelId ──────────────────────────────────────────────────────────

    #[test]
    fn test_channel_id_ordering_and_hashing() {
        let a = ChannelId(0);
        let b = ChannelId(1);
        let c = ChannelId(2);

        // Ordering.
        assert!(a < b);
        assert!(b < c);
        assert_eq!(a, ChannelId(0));

        // Hashing — distinct IDs produce distinct hash set entries.
        let mut set = HashSet::new();
        set.insert(a);
        set.insert(b);
        set.insert(c);
        assert_eq!(set.len(), 3);

        // Duplicate insertion.
        set.insert(ChannelId(1));
        assert_eq!(set.len(), 3);
    }

    #[test]
    fn test_channel_id_display() {
        assert_eq!(ChannelId(42).to_string(), "ch#42");
    }

    // ── GreenThreadId ──────────────────────────────────────────────────────

    #[test]
    fn test_green_thread_id_ordering() {
        let a = GreenThreadId(10);
        let b = GreenThreadId(20);
        let c = GreenThreadId(10);

        assert!(a < b);
        assert_eq!(a, c);
        assert_ne!(a, b);

        // Hash set behavior.
        let mut set = HashSet::new();
        set.insert(a);
        set.insert(b);
        set.insert(c); // duplicate of a
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn test_green_thread_id_display() {
        assert_eq!(GreenThreadId(7).to_string(), "gt#7");
    }

    // ── ChannelSpec ────────────────────────────────────────────────────────

    #[test]
    fn test_channel_spec_construction() {
        let untyped = ChannelSpec::new("signals");
        assert_eq!(untyped.name, "signals");
        assert!(untyped.element_type.is_none());
        assert_eq!(untyped.capacity, ChannelCapacity::Unbounded);

        let typed = ChannelSpec::typed("tokens", "Token");
        assert_eq!(typed.name, "tokens");
        assert_eq!(typed.element_type, Some("Token".to_string()));

        let bounded = ChannelSpec::bounded("events", 256);
        assert_eq!(bounded.capacity, ChannelCapacity::Bounded(256));
    }

    #[test]
    fn test_channel_capacity_display() {
        assert_eq!(ChannelCapacity::Unbounded.to_string(), "unbounded");
        assert_eq!(ChannelCapacity::Bounded(1024).to_string(), "bounded(1024)");
    }

    // ── JoinPatternSpec ────────────────────────────────────────────────────

    #[test]
    fn test_join_pattern_spec_multiple_channels() {
        let pattern = JoinPatternSpec {
            name: "recv_pair".to_string(),
            channels: vec![
                JoinChannelRef {
                    channel_name: "tokens".to_string(),
                    binding_name: "tok".to_string(),
                },
                JoinChannelRef {
                    channel_name: "positions".to_string(),
                    binding_name: "pos".to_string(),
                },
                JoinChannelRef {
                    channel_name: "weights".to_string(),
                    binding_name: "w".to_string(),
                },
            ],
        };

        assert_eq!(pattern.arity(), 3);
        assert_eq!(pattern.channels[0].channel_name, "tokens");
        assert_eq!(pattern.channels[1].binding_name, "pos");
        assert_eq!(pattern.channels[2].channel_name, "weights");
    }

    // ── ChannelsBlockSpec ──────────────────────────────────────────────────

    #[test]
    fn test_channels_block_spec() {
        let mut block = ChannelsBlockSpec::new();
        assert!(block.is_empty());
        assert_eq!(block.len(), 0);

        block.channels.push(ChannelSpec::new("ch1"));
        block.channels.push(ChannelSpec::typed("ch2", "i32"));
        block.join_patterns.push(JoinPatternSpec {
            name: "j1".to_string(),
            channels: vec![],
        });

        assert!(!block.is_empty());
        assert_eq!(block.len(), 3);
    }

    // ── Channel<T> send/recv ───────────────────────────────────────────────

    #[test]
    fn test_channel_send_try_recv_roundtrip() {
        let ch = Channel::<i32>::unbounded(ChannelId(0), "test");
        assert_eq!(ch.id(), ChannelId(0));
        assert_eq!(ch.name(), "test");
        assert!(ch.is_empty());

        ch.send(42).expect("send should succeed");
        ch.send(99).expect("send should succeed");
        assert_eq!(ch.len(), 2);

        assert_eq!(ch.try_recv().expect("recv should succeed"), 42);
        assert_eq!(ch.try_recv().expect("recv should succeed"), 99);
        assert!(ch.try_recv().is_err());
        assert!(ch.is_empty());
    }

    #[test]
    fn test_channel_bounded_send_recv() {
        let ch = Channel::<String>::bounded(ChannelId(1), "bounded_test", 2);

        ch.send("hello".to_string()).expect("send should succeed");
        ch.send("world".to_string()).expect("send should succeed");
        // Buffer is full at capacity 2; try_send would block on a third.

        assert_eq!(
            ch.recv_blocking().expect("recv should succeed"),
            "hello"
        );
        assert_eq!(
            ch.try_recv().expect("recv should succeed"),
            "world"
        );
    }

    #[test]
    fn test_channel_from_capacity() {
        let unbounded = Channel::<u8>::from_capacity(
            ChannelId(10),
            "ub",
            &ChannelCapacity::Unbounded,
        );
        unbounded.send(1).expect("send should succeed");
        assert_eq!(unbounded.try_recv().expect("recv should succeed"), 1);

        let bounded = Channel::<u8>::from_capacity(
            ChannelId(11),
            "bd",
            &ChannelCapacity::Bounded(8),
        );
        bounded.send(2).expect("send should succeed");
        assert_eq!(bounded.try_recv().expect("recv should succeed"), 2);
    }

    // ── Channel waiter registration ────────────────────────────────────────

    #[test]
    fn test_channel_waiter_registration() {
        let ch = Channel::<()>::unbounded(ChannelId(0), "waiter_test");
        assert_eq!(ch.waiter_count(), 0);

        let prev1 = ch.register_waiter();
        assert_eq!(prev1, 0);
        assert_eq!(ch.waiter_count(), 1);

        let prev2 = ch.register_waiter();
        assert_eq!(prev2, 1);
        assert_eq!(ch.waiter_count(), 2);

        let prev3 = ch.unregister_waiter();
        assert_eq!(prev3, 2);
        assert_eq!(ch.waiter_count(), 1);

        let prev4 = ch.unregister_waiter();
        assert_eq!(prev4, 1);
        assert_eq!(ch.waiter_count(), 0);

        // Saturating: unregister when already 0.
        let prev5 = ch.unregister_waiter();
        assert_eq!(prev5, 0);
        assert_eq!(ch.waiter_count(), 0);
    }

    // ── ChannelHandle type erasure ─────────────────────────────────────────

    #[test]
    fn test_channel_handle_downcast() {
        let ch = Channel::<i64>::unbounded(ChannelId(5), "typed_ch");
        ch.send(123).expect("send should succeed");

        let handle = ChannelHandle::new(ch);
        assert_eq!(handle.id(), ChannelId(5));
        assert_eq!(handle.name(), "typed_ch");

        // Correct downcast.
        let concrete = handle.downcast::<i64>().expect("downcast should succeed");
        assert_eq!(concrete.try_recv().expect("recv should succeed"), 123);

        // Wrong type downcast.
        assert!(handle.downcast::<String>().is_none());
    }

    #[test]
    fn test_channel_handle_downcast_arc() {
        let ch = Channel::<u32>::unbounded(ChannelId(6), "arc_ch");
        ch.send(77).expect("send should succeed");

        let handle = ChannelHandle::new(ch);

        // Correct downcast to Arc.
        let arc = handle.downcast_arc::<u32>().expect("downcast_arc should succeed");
        assert_eq!(arc.try_recv().expect("recv should succeed"), 77);

        // Wrong type.
        assert!(handle.downcast_arc::<f64>().is_none());
    }

    // ── ChannelMap ─────────────────────────────────────────────────────────

    #[test]
    fn test_channel_map_create_get_remove() {
        let map = ChannelMap::new();
        assert!(map.is_empty());
        assert_eq!(map.channel_count(), 0);

        let id1 = map.create_channel::<i32>("alpha", &ChannelCapacity::Unbounded);
        let id2 = map.create_channel::<String>("beta", &ChannelCapacity::Bounded(16));
        assert_eq!(map.channel_count(), 2);

        // Retrieve by ID.
        let h1 = map.get_channel(id1).expect("channel should exist");
        assert_eq!(h1.name(), "alpha");

        let h2 = map.get_channel(id2).expect("channel should exist");
        assert_eq!(h2.name(), "beta");

        // Non-existent ID.
        assert!(map.get_channel(ChannelId(999)).is_none());

        // Remove.
        let removed = map.remove_channel(id1).expect("remove should succeed");
        assert_eq!(removed.name(), "alpha");
        assert_eq!(map.channel_count(), 1);
        assert!(map.get_channel(id1).is_none());

        // Double remove.
        assert!(map.remove_channel(id1).is_none());
    }

    #[test]
    fn test_channel_map_name_to_id() {
        let map = ChannelMap::new();

        let id = map.create_channel::<u8>("signals", &ChannelCapacity::Unbounded);
        assert_eq!(map.get_id_by_name("signals"), Some(id));
        assert!(map.get_id_by_name("nonexistent").is_none());

        // get_channel_by_name convenience.
        let handle = map
            .get_channel_by_name("signals")
            .expect("should find by name");
        assert_eq!(handle.id(), id);
    }

    #[test]
    fn test_channel_map_fresh_id_uniqueness() {
        let map = ChannelMap::new();
        let mut ids = HashSet::new();
        for _ in 0..1000 {
            let id = map.fresh_id();
            assert!(ids.insert(id), "fresh_id should produce unique IDs");
        }
        assert_eq!(ids.len(), 1000);
    }

    #[test]
    fn test_channel_map_name_removal() {
        let map = ChannelMap::new();
        let id = map.create_channel::<bool>("flag", &ChannelCapacity::Unbounded);
        assert!(map.get_id_by_name("flag").is_some());

        map.remove_channel(id);
        // Name mapping should also be removed.
        assert!(map.get_id_by_name("flag").is_none());
    }

    #[test]
    fn test_channel_map_channel_ids_and_names() {
        let map = ChannelMap::new();
        map.create_channel::<i32>("a", &ChannelCapacity::Unbounded);
        map.create_channel::<i32>("b", &ChannelCapacity::Unbounded);
        map.create_channel::<i32>("c", &ChannelCapacity::Unbounded);

        let ids = map.channel_ids();
        assert_eq!(ids.len(), 3);

        let mut names = map.channel_names();
        names.sort();
        assert_eq!(names, vec!["a", "b", "c"]);
    }

    // ── ChannelWaiter ──────────────────────────────────────────────────────

    #[test]
    fn test_channel_waiter_single() {
        let waiter = ChannelWaiter::single(GreenThreadId(1), ChannelId(10));
        assert_eq!(waiter.thread_id, GreenThreadId(1));
        assert_eq!(waiter.channel_id, ChannelId(10));
        assert_eq!(waiter.pattern, WaitPattern::Single);
        assert!(!waiter.is_join());
        assert_eq!(waiter.all_channels(), vec![ChannelId(10)]);
    }

    #[test]
    fn test_channel_waiter_join() {
        let waiter = ChannelWaiter::join(
            GreenThreadId(2),
            ChannelId(10),
            vec![ChannelId(20), ChannelId(30)],
        );
        assert!(waiter.is_join());
        assert_eq!(
            waiter.all_channels(),
            vec![ChannelId(10), ChannelId(20), ChannelId(30)]
        );
    }

    #[test]
    fn test_channel_waiter_display() {
        let single = ChannelWaiter::single(GreenThreadId(1), ChannelId(5));
        assert_eq!(
            single.to_string(),
            "Waiter(gt#1 on ch#5 pattern=Single)"
        );

        let join = ChannelWaiter::join(
            GreenThreadId(3),
            ChannelId(10),
            vec![ChannelId(20)],
        );
        assert_eq!(
            join.to_string(),
            "Waiter(gt#3 on ch#10 pattern=Join(ch#20))"
        );
    }

    #[test]
    fn test_wait_pattern_display() {
        assert_eq!(WaitPattern::Single.to_string(), "Single");
        assert_eq!(
            WaitPattern::Join(vec![ChannelId(1), ChannelId(2)]).to_string(),
            "Join(ch#1, ch#2)"
        );
    }

    // ── Concurrent operations ──────────────────────────────────────────────

    #[test]
    fn test_concurrent_channel_send_recv() {
        let ch = Arc::new(Channel::<u64>::unbounded(ChannelId(0), "concurrent"));
        let n = 1000u64;

        // Spawn producer threads.
        let mut handles = Vec::with_capacity(4);
        for t in 0..4u64 {
            let ch_clone = Arc::clone(&ch);
            let start = t * (n / 4);
            let end = start + (n / 4);
            handles.push(std::thread::spawn(move || {
                for i in start..end {
                    ch_clone.send(i).expect("send should succeed");
                }
            }));
        }

        // Wait for all producers.
        for h in handles {
            h.join().expect("producer thread should not panic");
        }

        // All messages should be present.
        assert_eq!(ch.len(), n as usize);

        // Collect all messages (order is not guaranteed).
        let mut received = HashSet::with_capacity(n as usize);
        for _ in 0..n {
            let msg = ch.try_recv().expect("should have a message");
            received.insert(msg);
        }
        assert_eq!(received.len(), n as usize);
        for i in 0..n {
            assert!(received.contains(&i), "missing message {}", i);
        }
    }

    #[test]
    fn test_concurrent_channel_map_operations() {
        let map = Arc::new(ChannelMap::new());
        let n_threads = 8;
        let channels_per_thread = 50;

        let mut handles = Vec::with_capacity(n_threads);
        for t in 0..n_threads {
            let map_clone = Arc::clone(&map);
            handles.push(std::thread::spawn(move || {
                for i in 0..channels_per_thread {
                    let name = format!("ch_{}_{}", t, i);
                    map_clone.create_channel::<u32>(&name, &ChannelCapacity::Unbounded);
                }
            }));
        }

        for h in handles {
            h.join().expect("thread should not panic");
        }

        assert_eq!(
            map.channel_count(),
            n_threads * channels_per_thread,
        );
    }

    #[test]
    fn test_concurrent_waiter_registration() {
        let ch = Arc::new(Channel::<()>::unbounded(ChannelId(0), "waiter_stress"));
        let n_threads = 8;
        let ops_per_thread = 500;

        // Each thread registers and unregisters ops_per_thread times.
        let mut handles = Vec::with_capacity(n_threads);
        for _ in 0..n_threads {
            let ch_clone = Arc::clone(&ch);
            handles.push(std::thread::spawn(move || {
                for _ in 0..ops_per_thread {
                    ch_clone.register_waiter();
                }
                for _ in 0..ops_per_thread {
                    ch_clone.unregister_waiter();
                }
            }));
        }

        for h in handles {
            h.join().expect("thread should not panic");
        }

        // All registrations should be balanced.
        assert_eq!(ch.waiter_count(), 0);
    }

    // ── Channel Debug ──────────────────────────────────────────────────────

    #[test]
    fn test_channel_debug() {
        let ch = Channel::<i32>::unbounded(ChannelId(42), "debug_test");
        ch.send(1).expect("send should succeed");
        let debug_str = format!("{:?}", ch);
        assert!(debug_str.contains("Channel"));
        assert!(debug_str.contains("42"));
        assert!(debug_str.contains("debug_test"));
    }

    #[test]
    fn test_channel_handle_debug() {
        let ch = Channel::<u8>::unbounded(ChannelId(7), "handle_dbg");
        let handle = ChannelHandle::new(ch);
        let debug_str = format!("{:?}", handle);
        assert!(debug_str.contains("ChannelHandle"));
        assert!(debug_str.contains("handle_dbg"));
    }

    #[test]
    fn test_channel_map_debug() {
        let map = ChannelMap::new();
        map.create_channel::<i32>("x", &ChannelCapacity::Unbounded);
        let debug_str = format!("{:?}", map);
        assert!(debug_str.contains("ChannelMap"));
        assert!(debug_str.contains("channel_count"));
    }

    // ── ChannelHandle has_pending ────────────────────────────────────────

    #[test]
    fn test_channel_handle_has_pending() {
        let ch = Channel::<i32>::unbounded(ChannelId(0), "pending_test");
        let handle = ChannelHandle::new(ch);

        assert!(!handle.has_pending(), "empty channel should not have pending");

        // Send a message through the original channel (via downcast).
        let concrete = handle.downcast::<i32>().expect("downcast should succeed");
        concrete.send(42).expect("send should succeed");

        assert!(handle.has_pending(), "channel with message should have pending");

        concrete.try_recv().expect("recv should succeed");
        assert!(!handle.has_pending(), "drained channel should not have pending");
    }

    // ── WakeRegistry ────────────────────────────────────────────────────

    #[test]
    fn test_wake_registry_register_and_take() {
        let reg = WakeRegistry::new();
        assert_eq!(reg.channel_count(), 0);
        assert_eq!(reg.total_waiters(), 0);

        reg.register(ChannelId(1), GreenThreadId(10));
        reg.register(ChannelId(1), GreenThreadId(20));
        reg.register(ChannelId(2), GreenThreadId(30));

        assert_eq!(reg.channel_count(), 2);
        assert_eq!(reg.total_waiters(), 3);

        let waiters = reg.take_waiters(ChannelId(1));
        assert_eq!(waiters.len(), 2);
        assert!(waiters.contains(&GreenThreadId(10)));
        assert!(waiters.contains(&GreenThreadId(20)));

        // Channel 1 should be removed after take.
        assert_eq!(reg.channel_count(), 1);
        assert_eq!(reg.total_waiters(), 1);

        // Take from non-existent channel returns empty.
        assert!(reg.take_waiters(ChannelId(99)).is_empty());
    }

    #[test]
    fn test_wake_registry_unregister() {
        let reg = WakeRegistry::new();
        reg.register(ChannelId(1), GreenThreadId(10));
        reg.register(ChannelId(1), GreenThreadId(20));

        reg.unregister(ChannelId(1), GreenThreadId(10));
        assert_eq!(reg.total_waiters(), 1);

        reg.unregister(ChannelId(1), GreenThreadId(20));
        // Channel should be cleaned up when empty.
        assert_eq!(reg.channel_count(), 0);
    }

    #[test]
    fn test_wake_registry_unregister_nonexistent() {
        let reg = WakeRegistry::new();
        // Should not panic.
        reg.unregister(ChannelId(1), GreenThreadId(10));
        assert_eq!(reg.channel_count(), 0);
    }

    #[test]
    fn test_wake_registry_channels_with_waiters() {
        let reg = WakeRegistry::new();
        reg.register(ChannelId(5), GreenThreadId(1));
        reg.register(ChannelId(10), GreenThreadId(2));

        let mut channels = reg.channels_with_waiters();
        channels.sort();
        assert_eq!(channels, vec![ChannelId(5), ChannelId(10)]);
    }

    #[test]
    fn test_wake_registry_check_and_wake() {
        let reg = WakeRegistry::new();
        let map = ChannelMap::new();

        let ch_id = map.create_channel::<i32>("test_ch", &ChannelCapacity::Unbounded);
        reg.register(ch_id, GreenThreadId(42));

        // No messages yet — should not wake anyone.
        let to_wake = reg.check_and_wake(&map);
        assert!(to_wake.is_empty());
        assert_eq!(reg.total_waiters(), 1); // waiter still registered

        // Send a message.
        let handle = map.get_channel(ch_id).expect("channel exists");
        let ch = handle.downcast::<i32>().expect("downcast");
        ch.send(99).expect("send");

        // Re-register the waiter (it was not taken because channel was empty before).
        // Actually, the waiter is still there since check_and_wake only takes if pending.
        let to_wake = reg.check_and_wake(&map);
        assert_eq!(to_wake.len(), 1);
        assert_eq!(to_wake[0], (GreenThreadId(42), ch_id));

        // Waiter should be removed after wake.
        assert_eq!(reg.total_waiters(), 0);
    }

    #[test]
    fn test_wake_registry_debug() {
        let reg = WakeRegistry::new();
        reg.register(ChannelId(1), GreenThreadId(10));
        let debug = format!("{:?}", reg);
        assert!(debug.contains("WakeRegistry"));
        assert!(debug.contains("channels"));
    }

    // ── WakeRegistry Join Pattern Tests ─────────────────────────────────

    #[test]
    fn test_wake_registry_register_join() {
        let reg = WakeRegistry::new();
        let tid = GreenThreadId(1);
        let channels = vec![ChannelId(10), ChannelId(20), ChannelId(30)];

        reg.register_join(tid, &channels);

        // Thread should be registered on all 3 channels.
        assert_eq!(reg.channel_count(), 3);
        assert_eq!(reg.total_waiters(), 3);

        let mut ch_ids = reg.channels_with_waiters();
        ch_ids.sort();
        assert_eq!(ch_ids, vec![ChannelId(10), ChannelId(20), ChannelId(30)]);
    }

    #[test]
    fn test_wake_registry_check_and_wake_join_all_ready() {
        let reg = WakeRegistry::new();
        let map = ChannelMap::new();

        let ch_a = map.create_channel::<i32>("ch_a", &ChannelCapacity::Unbounded);
        let ch_b = map.create_channel::<i32>("ch_b", &ChannelCapacity::Unbounded);
        let tid = GreenThreadId(1);

        // Register a join pattern waiter.
        reg.register_join(tid, &[ch_a, ch_b]);

        let mut join_sets = std::collections::HashMap::new();
        join_sets.insert(tid, vec![ch_a, ch_b]);

        // Neither channel has messages — should not wake.
        let wakes = reg.check_and_wake_join(&map, &join_sets);
        assert!(wakes.is_empty());
        assert_eq!(reg.total_waiters(), 2); // still registered

        // Send on channel A only — still should not wake (B has no message).
        let ha = map.get_channel(ch_a).expect("channel A");
        ha.downcast::<i32>().expect("downcast").send(1).expect("send");
        let wakes = reg.check_and_wake_join(&map, &join_sets);
        assert!(wakes.is_empty(), "should not wake when only one join channel has data");

        // Send on channel B too — NOW should wake.
        let hb = map.get_channel(ch_b).expect("channel B");
        hb.downcast::<i32>().expect("downcast").send(2).expect("send");
        let wakes = reg.check_and_wake_join(&map, &join_sets);
        assert_eq!(wakes.len(), 1);
        assert_eq!(wakes[0].0, tid);

        // Waiters should be cleaned up from both channels.
        assert_eq!(reg.total_waiters(), 0);
    }

    #[test]
    fn test_wake_registry_check_and_wake_join_partial_ready() {
        let reg = WakeRegistry::new();
        let map = ChannelMap::new();

        let ch_a = map.create_channel::<String>("ch_a", &ChannelCapacity::Unbounded);
        let ch_b = map.create_channel::<String>("ch_b", &ChannelCapacity::Unbounded);
        let ch_c = map.create_channel::<String>("ch_c", &ChannelCapacity::Unbounded);
        let tid = GreenThreadId(5);

        reg.register_join(tid, &[ch_a, ch_b, ch_c]);

        let mut join_sets = std::collections::HashMap::new();
        join_sets.insert(tid, vec![ch_a, ch_b, ch_c]);

        // Only 2 of 3 channels have messages — should not wake.
        let ha = map.get_channel(ch_a).expect("ch_a");
        ha.downcast::<String>().expect("downcast").send("a".to_string()).expect("send");
        let hc = map.get_channel(ch_c).expect("ch_c");
        hc.downcast::<String>().expect("downcast").send("c".to_string()).expect("send");

        let wakes = reg.check_and_wake_join(&map, &join_sets);
        assert!(wakes.is_empty(), "should not wake with 2/3 channels ready");
        assert_eq!(reg.total_waiters(), 3, "waiters should remain registered");
    }

    #[test]
    fn test_wake_registry_check_and_wake_join_ignores_single_waiters() {
        let reg = WakeRegistry::new();
        let map = ChannelMap::new();

        let ch_a = map.create_channel::<i32>("ch_a", &ChannelCapacity::Unbounded);
        let single_tid = GreenThreadId(1);
        let join_tid = GreenThreadId(2);

        // Register a single waiter (not in join_sets).
        reg.register(ch_a, single_tid);
        // Register a join waiter.
        reg.register(ch_a, join_tid);

        // join_sets only has the join_tid.
        let mut join_sets = std::collections::HashMap::new();
        join_sets.insert(join_tid, vec![ch_a]);

        // Send a message.
        let ha = map.get_channel(ch_a).expect("ch_a");
        ha.downcast::<i32>().expect("downcast").send(42).expect("send");

        let wakes = reg.check_and_wake_join(&map, &join_sets);
        // Only the join waiter should be woken; the single waiter is not in join_sets.
        assert_eq!(wakes.len(), 1);
        assert_eq!(wakes[0].0, join_tid);

        // The single waiter should still be registered.
        assert_eq!(reg.total_waiters(), 1);
    }

    // ── Property-Based Tests (proptest) ──────────────────────────────────

    mod proptest_channel {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            /// FIFO roundtrip: send N items, receive N items in the same order.
            #[test]
            fn prop_fifo_roundtrip(items in proptest::collection::vec(any::<i64>(), 0..128)) {
                let ch = Channel::<i64>::unbounded(ChannelId(0), "fifo_test");
                for &item in &items {
                    ch.send(item).expect("send should succeed");
                }
                let mut received = Vec::with_capacity(items.len());
                for _ in 0..items.len() {
                    received.push(ch.try_recv().expect("recv should succeed"));
                }
                prop_assert_eq!(items, received, "FIFO order must be preserved");
                prop_assert!(ch.try_recv().is_err(), "channel should be empty after draining");
            }

            /// Waiter count is always >= 0: register/unregister never underflows.
            #[test]
            fn prop_waiter_count_non_negative(
                registers in 0u64..64,
                unregisters in 0u64..128,
            ) {
                let ch = Channel::<()>::unbounded(ChannelId(0), "waiter_prop");
                for _ in 0..registers {
                    ch.register_waiter();
                }
                for _ in 0..unregisters {
                    ch.unregister_waiter();
                }
                // Waiter count must always be non-negative (u64 saturating).
                // With saturating decrement, the count is max(0, registers - unregisters).
                let expected = registers.saturating_sub(unregisters);
                prop_assert_eq!(
                    ch.waiter_count(), expected,
                    "waiter count should be saturating difference"
                );
            }

            /// fresh_id returns unique IDs across N calls on the same ChannelMap.
            #[test]
            fn prop_fresh_id_unique(n in 1usize..256) {
                let map = ChannelMap::new();
                let mut ids = std::collections::HashSet::with_capacity(n);
                for _ in 0..n {
                    let id = map.fresh_id();
                    prop_assert!(ids.insert(id), "fresh_id must produce unique IDs, duplicate: {:?}", id);
                }
                prop_assert_eq!(ids.len(), n);
            }

            /// Downcast roundtrip: send a typed value through a ChannelHandle,
            /// downcast back to the correct type, and receive the same value.
            #[test]
            fn prop_downcast_roundtrip(value in any::<i64>()) {
                let ch = Channel::<i64>::unbounded(ChannelId(0), "downcast_prop");
                ch.send(value).expect("send should succeed");

                let handle = ChannelHandle::new(ch);

                // Correct type downcast succeeds.
                let concrete = handle.downcast::<i64>();
                prop_assert!(concrete.is_some(), "downcast to correct type must succeed");
                let received = concrete.expect("downcast should succeed").try_recv().expect("recv should succeed");
                prop_assert_eq!(value, received, "roundtrip value must match");

                // Wrong type downcast fails.
                prop_assert!(handle.downcast::<String>().is_none(), "downcast to wrong type must fail");
            }
        }
    }
}
