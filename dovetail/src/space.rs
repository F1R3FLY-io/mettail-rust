//! A tuplespace-shaped rendezvous trait + an in-memory default — the
//! substrate seam between the reduction core and a concurrent tuplespace.
//!
//! This is the **forward-compatibility seam** for a future "Reified RSpace"
//! exposure (f1r3node-reified-rspaces, blocked on the Scala→Rust PR migration):
//! the trait is generic over channel/pattern/data/continuation `(C, P, A, K)`
//! with a [`Match`] seam, exactly the shape a Reified-RSpace backend would
//! implement (inner store ≈ a per-channel queue/priority-queue; outer store ≈ a
//! map; the `Match` seam ≈ the spatial matcher). dovetail ships only the trait
//! plus an in-memory default; it takes NO dependency on any reified-rspace API.

use std::collections::HashMap;
use std::hash::Hash;

/// The spatial-match seam: decide whether pattern `P` consumes datum `A`, and
/// if so produce the captured `Bindings`.
pub trait Match<P, A> {
    /// What a successful match captures (e.g. the bound subterms).
    type Bindings;
    /// `Some(bindings)` iff `pat` matches `data`; `None` otherwise.
    fn matches(&self, pat: &P, data: &A) -> Option<Self::Bindings>;
}

/// The outcome of a COMM: the partner that fired plus the captured bindings.
/// For `produce`, `partner` is the consumer's continuation `K`; for `consume`,
/// `partner` is the matched datum `A`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fired<Partner, Bindings> {
    pub partner: Partner,
    pub bindings: Bindings,
}

/// A tuplespace-shaped rendezvous over channels `C`, with a [`Match`] seam.
///
/// `produce`/`consume` are the rendezvous: each tries to fire a COMM against a
/// waiting partner on the same channel, and otherwise parks. This is the shape a
/// Reified-RSpace backend implements; the reduction core drives reduction
/// through it without knowing the concrete store.
pub trait TupleSpace<C, P, A, K> {
    /// The spatial matcher used to fire COMMs.
    type Matcher: Match<P, A>;

    /// Offer `data` on `chan`. If a parked consumer's pattern matches, the COMM
    /// fires (the consumer is removed) and its continuation + bindings are
    /// returned; otherwise `data` is parked and `None` is returned.
    fn produce(
        &mut self,
        chan: C,
        data: A,
    ) -> Option<Fired<K, <Self::Matcher as Match<P, A>>::Bindings>>;

    /// Offer continuation `k` guarded by `pat` on `chan`. If parked data
    /// matches, the COMM fires (the datum is removed) and it + bindings are
    /// returned; otherwise `(pat, k)` is parked and `None` is returned.
    fn consume(
        &mut self,
        chan: C,
        pat: P,
        k: K,
    ) -> Option<Fired<A, <Self::Matcher as Match<P, A>>::Bindings>>;
}

/// An in-memory tuplespace: per-channel queues of parked data and parked
/// continuations, matched first-fit by a supplied [`Match`]. This is the default
/// substrate; a concurrent / Reified-RSpace backend replaces it behind the
/// [`TupleSpace`] trait.
pub struct InMemSpace<C, P, A, K, M>
where
    C: Eq + Hash,
{
    data: HashMap<C, Vec<A>>,
    conts: HashMap<C, Vec<(P, K)>>,
    matcher: M,
}

impl<C, P, A, K, M> InMemSpace<C, P, A, K, M>
where
    C: Eq + Hash,
    M: Match<P, A>,
{
    /// A new in-memory space with the given matcher.
    pub fn new(matcher: M) -> Self {
        InMemSpace { data: HashMap::new(), conts: HashMap::new(), matcher }
    }

    /// Number of parked data items on a channel.
    pub fn parked_data(&self, chan: &C) -> usize {
        self.data.get(chan).map_or(0, Vec::len)
    }

    /// Number of parked continuations on a channel.
    pub fn parked_conts(&self, chan: &C) -> usize {
        self.conts.get(chan).map_or(0, Vec::len)
    }
}

impl<C, P, A, K, M> TupleSpace<C, P, A, K> for InMemSpace<C, P, A, K, M>
where
    C: Eq + Hash + Clone,
    M: Match<P, A>,
{
    type Matcher = M;

    fn produce(&mut self, chan: C, data: A) -> Option<Fired<K, M::Bindings>> {
        // First-fit against parked continuations on this channel.
        if let Some(waiting) = self.conts.get_mut(&chan) {
            if let Some(idx) = waiting
                .iter()
                .position(|(pat, _)| self.matcher.matches(pat, &data).is_some())
            {
                let (pat, k) = waiting.remove(idx);
                let bindings = self
                    .matcher
                    .matches(&pat, &data)
                    .expect("match re-confirmed at fire");
                return Some(Fired { partner: k, bindings });
            }
        }
        // No consumer: park the datum.
        self.data.entry(chan).or_default().push(data);
        None
    }

    fn consume(&mut self, chan: C, pat: P, k: K) -> Option<Fired<A, M::Bindings>> {
        // First-fit against parked data on this channel.
        if let Some(waiting) = self.data.get_mut(&chan) {
            if let Some(idx) =
                waiting.iter().position(|d| self.matcher.matches(&pat, d).is_some())
            {
                let data = waiting.remove(idx);
                let bindings =
                    self.matcher.matches(&pat, &data).expect("match re-confirmed at fire");
                return Some(Fired { partner: data, bindings });
            }
        }
        // No datum: park the continuation.
        self.conts.entry(chan).or_default().push((pat, k));
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A test pattern: match anything (capturing the datum) or an exact value.
    #[derive(Clone, Debug)]
    enum Pat {
        Any,
        Exact(i64),
    }

    /// A matcher whose bindings are the captured datum.
    struct CaptureMatch;
    impl Match<Pat, i64> for CaptureMatch {
        type Bindings = i64;
        fn matches(&self, pat: &Pat, data: &i64) -> Option<i64> {
            match pat {
                Pat::Any => Some(*data),
                Pat::Exact(v) => (v == data).then_some(*data),
            }
        }
    }

    fn space() -> InMemSpace<String, Pat, i64, u32, CaptureMatch> {
        InMemSpace::new(CaptureMatch)
    }

    #[test]
    fn produce_then_consume_fires() {
        let mut s = space();
        assert!(s.produce("ch".into(), 5).is_none(), "no consumer yet → park");
        assert_eq!(s.parked_data(&"ch".into()), 1);
        let fired = s.consume("ch".into(), Pat::Any, 7).expect("should fire");
        assert_eq!(fired.partner, 5, "consume returns the matched datum");
        assert_eq!(fired.bindings, 5);
        assert_eq!(s.parked_data(&"ch".into()), 0, "datum consumed");
    }

    #[test]
    fn consume_then_produce_fires() {
        let mut s = space();
        assert!(s.consume("ch".into(), Pat::Exact(9), 7).is_none(), "no datum yet → park");
        assert_eq!(s.parked_conts(&"ch".into()), 1);
        let fired = s.produce("ch".into(), 9).expect("should fire");
        assert_eq!(fired.partner, 7, "produce returns the matched continuation");
        assert_eq!(fired.bindings, 9);
        assert_eq!(s.parked_conts(&"ch".into()), 0, "continuation consumed");
    }

    #[test]
    fn non_match_parks_both_sides() {
        let mut s = space();
        assert!(s.consume("ch".into(), Pat::Exact(1), 7).is_none());
        // 2 does not match Exact(1): no fire, datum parks alongside the cont.
        assert!(s.produce("ch".into(), 2).is_none());
        assert_eq!(s.parked_conts(&"ch".into()), 1);
        assert_eq!(s.parked_data(&"ch".into()), 1);
        // Now a matching datum fires the parked continuation.
        let fired = s.produce("ch".into(), 1).expect("matches Exact(1)");
        assert_eq!(fired.partner, 7);
        assert_eq!(s.parked_conts(&"ch".into()), 0);
    }

    #[test]
    fn channels_are_isolated() {
        let mut s = space();
        s.produce("a".into(), 5);
        assert!(s.consume("b".into(), Pat::Any, 1).is_none(), "different channel → no fire");
        assert_eq!(s.parked_data(&"a".into()), 1);
        assert_eq!(s.parked_conts(&"b".into()), 1);
    }
}
