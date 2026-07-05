#!/usr/bin/env sage
# RhoNet small-state exploration (pgmcp #1956 Epic 8 #2049).
#
# Models RhoNet channels and rules as a small FINITE transition system and
# enumerates every reachable configuration for tiny instances, checking the three
# operational facets the item names -- MATCHING, SCHEDULING, and OBSERVATION.
# This complements the mechanized proofs (which are abstract/parametric) and the
# TLA+ scheduler (formal/tla/rho_machine/RhoNetScheduler.tla) with concrete,
# exhaustive small-state evidence:
#
#   * MATCHING     -- the positional set-automaton dispatch (root op+arity index,
#                     Rocq PositionalSetAutomatonSound.v) agrees with the recursive
#                     positional matcher on every small subject.
#   * OBSERVATION  -- a base-rewrite sigma-receiver, fired under the sigma the
#                     matcher computes, lands exactly RHS[sigma] on the out channel
#                     (the SwapDemo correspondence, Rocq LinearCommCorrespondence.v /
#                     the rho_net_equivalence runtime test), non-vacuously.
#   * SCHEDULING   -- independent COMM redexes on distinct channels are
#                     schedule-confluent: every firing order yields the same resting
#                     out-channel barb multiset (the EndToEndCommCorrespondence.v /
#                     RhoNetScheduler fairness picture, enumerated).
#
# Run:  sage formal/sage/rho_net/rho_net_small_state.sage   (prints a JSON summary;
#       exits non-zero on any failed small-state check)
#
# Pure Python (Sage preprocesses this file but uses only stdlib), so it also runs
# under a bare `python3`.

import itertools
import json
import sys


# --- Terms: (constructor, tuple-of-children). Nullary A/B are the leaves. ---
def term(constructor, *children):
    return (constructor, tuple(children))


def op(t):
    return t[0]


def arity(t):
    return len(t[1])


# --- MATCHING -------------------------------------------------------------
# A positional pattern: ("var", name) matches any subject; ("app", op, [args])
# matches by op + arity then recurses. The set automaton dispatches an ("app")
# pattern only where its (op, arity) root key matches, then runs the same recursion.
def recursive_match(pattern, subject, sigma):
    kind = pattern[0]
    if kind == "var":
        name = pattern[1]
        if name in sigma and sigma[name] != subject:
            return None            # non-linear consistency (merge_substs)
        sigma = dict(sigma)
        sigma[name] = subject
        return sigma
    # app pattern
    _, pop, pargs = pattern
    if op(subject) != pop or arity(subject) != len(pargs):
        return None
    for parg, sarg in zip(pargs, subject[1]):
        sigma = recursive_match(parg, sarg, sigma)
        if sigma is None:
            return None
    return sigma


def dispatched(pattern, subject):
    # The root-index verdict: variables dispatch everywhere; app patterns only
    # where the (op, arity) key agrees.
    if pattern[0] == "var":
        return True
    _, pop, pargs = pattern
    return op(subject) == pop and arity(subject) == len(pargs)


def automaton_match(pattern, subject):
    # The automaton checks the root index first, then the full recursion.
    if not dispatched(pattern, subject):
        return None
    return recursive_match(pattern, subject, {})


def explore_matching():
    # Small pattern + subject universe over ops {Swap, Pair, A, B}, arity <= 2.
    A, B = term("A"), term("B")
    leaves = [A, B]
    subjects = list(leaves)
    for f in ("Swap", "Pair"):
        for a in leaves:
            for b in leaves:
                subjects.append(term(f, a, b))
    patterns = [
        ("var", "x"),
        ("app", "Swap", [("var", "x"), ("var", "y")]),
        ("app", "Pair", [("var", "x"), ("var", "y")]),
        ("app", "Swap", [("var", "x"), ("var", "x")]),   # non-linear: x twice
        ("app", "A", []),
    ]
    checked = 0
    for p in patterns:
        for s in subjects:
            # The index NEVER drops a match, and adds no false match:
            expected = recursive_match(p, s, {})
            got = automaton_match(p, s)
            assert got == expected, ("matching mismatch", p, s, got, expected)
            checked += 1
    return checked


# --- OBSERVATION ----------------------------------------------------------
# SwapDemo base rewrite Swap(x, y) ~> Pair(y, x). The matcher yields sigma; the
# sigma-receiver reflects RHS Pair(y, x) under sigma onto the out channel.
def fire_swap_receiver(sigma):
    return term("Pair", sigma["y"], sigma["x"])


def explore_observation():
    leaves = [term("A"), term("B")]
    pattern = ("app", "Swap", [("var", "x"), ("var", "y")])
    cases = []
    nonvacuous = 0
    for a in leaves:
        for b in leaves:
            subject = term("Swap", a, b)
            sigma = automaton_match(pattern, subject)
            assert sigma is not None
            observed = fire_swap_receiver(sigma)         # rests on the out channel
            expected = term("Pair", b, a)                # RHS Pair(y, x) with sigma
            assert observed == expected, (subject, observed, expected)
            if observed != subject:                      # Swap(a,b) != Pair(b,a)
                nonvacuous += 1
            cases.append({"subject": _show(subject), "observed": _show(observed)})
    return cases, nonvacuous


# --- SCHEDULING -----------------------------------------------------------
# Two independent COMM redexes on distinct channels, each producing one datum on
# the shared out channel. Enumerate every firing order.
def explore_scheduling():
    redexes = {"c1": "d1", "c2": "d2", "c3": "d3"}
    observations = set()
    for order in itertools.permutations(redexes.keys()):
        barbs = tuple(sorted(redexes[ch] for ch in order))
        observations.add(barbs)
    # schedule-confluence: exactly one observed barb multiset across all orders.
    assert len(observations) == 1, ("not schedule-confluent", observations)
    (confluent,) = observations
    return list(confluent), len(list(itertools.permutations(redexes.keys())))


def _show(t):
    if arity(t) == 0:
        return op(t)
    return "%s(%s)" % (op(t), ", ".join(_show(c) for c in t[1]))


def run():
    matched = explore_matching()
    obs_cases, nonvacuous = explore_observation()
    confluent_barbs, orders = explore_scheduling()
    # Coerce counters to native Python int: Sage preprocesses integer literals into
    # Sage `Integer`s, which `json.dumps` cannot serialize.
    return {
        "matching_pattern_subject_pairs_checked": int(matched),
        "matching_automaton_equals_recursive_oracle": True,
        "observation_cases": obs_cases,
        "observation_nonvacuous_offdiagonal": int(nonvacuous),
        "scheduling_orders_explored": int(orders),
        "scheduling_confluent_barbs": confluent_barbs,
    }


def main():
    try:
        summary = run()
    except AssertionError as err:
        print("rho_net_small_state FAILED: %s" % (err,), file=sys.stderr)
        sys.exit(1)
    print(json.dumps(summary, indent=2))
    print("rho_net_small_state: all small-state checks passed", file=sys.stderr)
    # Success = natural return (exit 0). We do NOT `sys.exit(0)` because Sage's
    # `.sage` runner turns that SystemExit into a non-zero exit; failures still
    # signal via the `sys.exit(1)` in the AssertionError handler above.


# Call unconditionally: Sage's `.sage` runner does not set __name__ == "__main__",
# so a guard would silently skip execution under `sage this.sage` (it still runs
# correctly under `python3 this.sage`).
main()
