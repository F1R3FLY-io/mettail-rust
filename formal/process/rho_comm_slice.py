#!/usr/bin/env python3
"""Generate and check the bounded Rho/Dovetail COMM process slice."""

from __future__ import annotations

import argparse
from collections import Counter
import itertools
import json
import math
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
SPEC_PATH = Path(__file__).with_name("rho_comm_slice.json")
IDENT_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_]*$")


def require_identifier(value: str, field: str) -> None:
    if not isinstance(value, str) or not IDENT_RE.fullmatch(value):
        raise ValueError(f"{field} must be an ASCII identifier, got {value!r}")


def require_distinct(values: list[str], field: str) -> None:
    duplicates = sorted(value for value, count in Counter(values).items() if count > 1)
    if duplicates:
        raise ValueError(f"{field} must be unique; duplicates: {duplicates}")


def lower(label: str) -> str:
    return label.lower()


def validate_spec(spec: dict) -> dict:
    redexes = spec["redexes"]
    if not redexes:
        raise ValueError("redexes must be nonempty")
    labels = [redex["label"] for redex in redexes]
    facts = [redex["fact"] for redex in redexes]
    for index, label in enumerate(labels):
        require_identifier(label, f"redexes[{index}].label")
    for index, fact in enumerate(facts):
        require_identifier(fact, f"redexes[{index}].fact")
    require_distinct(labels, "redex labels")
    require_distinct(
        [lower(label) for label in labels],
        "redex labels after mCRL2 field-name lowering",
    )
    require_distinct(facts, "redex facts")

    completion = spec["completion_observation"]
    require_identifier(completion, "completion_observation")
    if completion in labels:
        raise ValueError("completion observation must be distinct from redex labels")

    guard = spec["guarded_join"]
    guard_fact_fields = [
        "left_fact",
        "bad_fact",
        "good_fact",
        "open_fact",
        "rejected_fact",
        "completed_fact",
    ]
    guard_facts = [guard[field] for field in guard_fact_fields]
    for field, fact in zip(guard_fact_fields, guard_facts):
        require_identifier(fact, f"guarded_join.{field}")
    require_distinct(guard_facts, "guarded-join facts")
    if set(facts).intersection(guard_facts):
        raise ValueError("guarded-join facts must be distinct from COMM facts")

    guard_observation_fields = [
        "bad_reject_observation",
        "good_commit_observation",
    ]
    guard_observations = [guard[field] for field in guard_observation_fields]
    for field, observation in zip(guard_observation_fields, guard_observations):
        require_identifier(observation, f"guarded_join.{field}")
    require_distinct(guard_observations, "guarded-join observations")
    if set(guard_facts).intersection(guard_observations):
        raise ValueError(
            "guarded-join observations must be distinct from guarded-join facts"
        )
    return spec


def load_spec() -> dict:
    with SPEC_PATH.open(encoding="utf-8") as handle:
        spec = json.load(handle)
    return validate_spec(spec)


def state_args(fields: list[str]) -> str:
    return ", ".join(fields)


def render_mcrl2_rho(spec: dict) -> str:
    redexes = spec["redexes"]
    labels = [r["label"] for r in redexes]
    in_fields = [f"{lower(label)}In" for label in labels]
    reserved_fields = [f"{lower(label)}Reserved" for label in labels]
    out_fields = [f"{lower(label)}Out" for label in labels]
    all_fields = in_fields + reserved_fields + out_fields + ["joinReserved", "completed"]

    actions = (
        [f"reserve{label}" for label in labels]
        + ["reserveJoin"]
        + [f"fire{label}" for label in labels]
        + ["complete", "done"]
    )
    lines = [
        "% Generated from formal/process/rho_comm_slice.json.",
        "% Finite RhoNet COMM projection with internal RSpace-style reserve/commit",
        "% phases.",
        "%",
        "% Each independent redex first reserves its matching channel datum",
        "% internally and only then exposes the visible commit. Completion",
        "% likewise has an internal join reservation before the visible",
        "% `complete` observation. The matching Dovetail projection in",
        "% dovetail_fact_steps.mcrl2 performs direct visible fact steps.",
        "% The Makefile compares the two LTSs by branching bisimulation while",
        "% treating reserve actions as internal tau steps.",
        "",
        "act",
        f"  {', '.join(actions)};",
        "",
        "proc",
        "  RhoNet(",
    ]
    for field in all_fields[:-1]:
        lines.append(f"    {field}: Bool,")
    lines.append(f"    {all_fields[-1]}: Bool")
    lines.extend(["  ) =",])

    transition_lines = []
    for index, label in enumerate(labels):
        l = lower(label)
        choice = "       " if index == 0 else "     + "
        reserve_args = all_fields.copy()
        reserve_args[index] = "false"
        reserve_args[len(in_fields) + index] = "true"
        fire_args = all_fields.copy()
        fire_args[len(in_fields) + index] = "false"
        fire_args[len(in_fields) + len(reserved_fields) + index] = "true"
        transition_lines.extend(
            [
                f"{choice}({l}In && !{l}Reserved && !{l}Out && !completed)",
                f"         -> reserve{label} . RhoNet({state_args(reserve_args)})",
                f"     + ({l}Reserved && !completed)",
                f"         -> fire{label} . RhoNet({state_args(fire_args)})",
            ]
        )

    join_guard = " && ".join([f"{lower(label)}Out" for label in labels] + ["!joinReserved", "!completed"])
    join_args = all_fields.copy()
    for index in range(len(labels)):
        join_args[len(in_fields) + len(reserved_fields) + index] = "false"
    join_args[-2] = "true"
    complete_args = all_fields.copy()
    complete_args[-2] = "false"
    complete_args[-1] = "true"
    transition_lines.extend(
        [
            f"     + ({join_guard})",
            f"         -> reserveJoin . RhoNet({state_args(join_args)})",
            "     + (joinReserved && !completed)",
            f"         -> complete . RhoNet({state_args(complete_args)})",
            "     + completed",
            f"         -> done . RhoNet({state_args(all_fields[:-1] + ['true'])});",
            "",
            "init",
            f"  RhoNet({state_args(['true'] * len(labels) + ['false'] * (len(all_fields) - len(labels)))});",
            "",
        ]
    )
    lines.extend(transition_lines)
    return "\n".join(lines)


def render_mcrl2_dovetail(spec: dict) -> str:
    labels = [r["label"] for r in spec["redexes"]]
    in_fields = [f"{lower(label)}In" for label in labels]
    out_fields = [f"{lower(label)}Out" for label in labels]
    all_fields = in_fields + out_fields + ["completed"]
    lines = [
        "% Generated from formal/process/rho_comm_slice.json.",
        "% Finite Dovetail fact-step projection for the same COMM fragment as",
        "% rho_net_comm.mcrl2.",
        "%",
        "% Dovetail's abstract fact steps are direct: firing each redex consumes",
        "% the corresponding input and produces the corresponding observation.",
        "% Completion consumes all produced observations. The RhoNet model has",
        "% extra internal reserve actions; this model intentionally does not.",
        "",
        "act",
        f"  {', '.join([f'fire{label}' for label in labels] + ['complete', 'done'])};",
        "",
        "proc",
        "  Dovetail(",
    ]
    for field in all_fields[:-1]:
        lines.append(f"    {field}: Bool,")
    lines.append(f"    {all_fields[-1]}: Bool")
    lines.extend(["  ) =",])
    transitions = []
    for index, label in enumerate(labels):
        l = lower(label)
        choice = "       " if index == 0 else "     + "
        args = all_fields.copy()
        args[index] = "false"
        args[len(in_fields) + index] = "true"
        transitions.extend(
            [
                f"{choice}({l}In && !{l}Out && !completed) -> fire{label} . Dovetail({state_args(args)})",
            ]
        )
    join_guard = " && ".join([f"{lower(label)}Out" for label in labels] + ["!completed"])
    complete_args = all_fields.copy()
    for index in range(len(labels)):
        complete_args[len(in_fields) + index] = "false"
    complete_args[-1] = "true"
    transitions.append(f"     + ({join_guard}) -> complete . Dovetail({state_args(complete_args)})")
    transitions.append(f"     + completed -> done . Dovetail({state_args(all_fields[:-1] + ['true'])});")
    lines.extend(transitions)
    lines.extend(
        [
            "",
            "init",
            f"  Dovetail({state_args(['true'] * len(labels) + ['false'] * (len(all_fields) - len(labels)))});",
            "",
        ]
    )
    return "\n".join(lines)


def render_rho_formula(spec: dict) -> str:
    labels = [r["label"] for r in spec["redexes"]]
    diamonds = []
    boxes = []
    for order in itertools.permutations(labels):
        prefix = " . ".join(action for label in order for action in (f"reserve{label}", f"fire{label}"))
        diamonds.append(f"<{prefix} . reserveJoin . complete>true")
        boxes.append(f"[{prefix}]<reserveJoin . complete>true")
    return " &&\n".join(diamonds + boxes) + "\n"


def render_dovetail_formula(spec: dict) -> str:
    labels = [r["label"] for r in spec["redexes"]]
    diamonds = []
    boxes = []
    for order in itertools.permutations(labels):
        prefix = " . ".join(f"fire{label}" for label in order)
        diamonds.append(f"<{prefix} . complete>true")
        boxes.append(f"[{prefix}]<complete>true")
    return " &&\n".join(diamonds + boxes) + "\n"


def render_mcrl2_rho_guard(spec: dict) -> str:
    guard = spec["guarded_join"]
    reject = guard["bad_reject_observation"]
    commit = guard["good_commit_observation"]
    return f"""% Generated from formal/process/rho_comm_slice.json.
% Guarded RhoNet join projection with internal reservation and explicit
% failed-guard release. The bad candidate must remain available after
% `{reject}`, and the valid candidate must still be able to commit.

act
  reserveGuardBad, reserveGuardGood, {reject}, {commit}, observeBad, observeRejected, done;

proc
  RhoGuard(
    leftIn: Bool,
    badIn: Bool,
    goodIn: Bool,
    guardOpen: Bool,
    badReserved: Bool,
    goodReserved: Bool,
    rejected: Bool,
    completed: Bool
  ) =
       (leftIn && badIn && guardOpen && !badReserved && !goodReserved && !completed)
         -> reserveGuardBad . RhoGuard(false, false, goodIn, false, true, goodReserved, rejected, completed)
     + (badReserved && !completed)
         -> {reject} . RhoGuard(true, true, goodIn, false, false, goodReserved, true, completed)
     + (leftIn && goodIn && !badReserved && !goodReserved && !completed)
         -> reserveGuardGood . RhoGuard(false, badIn, false, guardOpen, badReserved, true, rejected, completed)
     + (goodReserved && !completed)
         -> {commit} . RhoGuard(leftIn, badIn, goodIn, guardOpen, badReserved, false, rejected, true)
     + (completed && badIn)
         -> observeBad . RhoGuard(leftIn, badIn, goodIn, guardOpen, badReserved, goodReserved, rejected, completed)
     + (completed && rejected)
         -> observeRejected . RhoGuard(leftIn, badIn, goodIn, guardOpen, badReserved, goodReserved, rejected, completed)
     + completed
         -> done . RhoGuard(leftIn, badIn, goodIn, guardOpen, badReserved, goodReserved, rejected, true);

init
  RhoGuard(true, true, true, true, false, false, false, false);
"""


def render_mcrl2_dovetail_guard(spec: dict) -> str:
    guard = spec["guarded_join"]
    reject = guard["bad_reject_observation"]
    commit = guard["good_commit_observation"]
    return f"""% Generated from formal/process/rho_comm_slice.json.
% Guarded Dovetail fact-step projection. Failed guards are direct visible
% facts and do not consume the candidate inputs.

act
  {reject}, {commit}, observeBad, observeRejected, done;

proc
  DovetailGuard(
    leftIn: Bool,
    badIn: Bool,
    goodIn: Bool,
    guardOpen: Bool,
    rejected: Bool,
    completed: Bool
  ) =
       (leftIn && badIn && guardOpen && !completed)
         -> {reject} . DovetailGuard(true, true, goodIn, false, true, completed)
     + (leftIn && goodIn && !completed)
         -> {commit} . DovetailGuard(false, badIn, false, guardOpen, rejected, true)
     + (completed && badIn)
         -> observeBad . DovetailGuard(leftIn, badIn, goodIn, guardOpen, rejected, completed)
     + (completed && rejected)
         -> observeRejected . DovetailGuard(leftIn, badIn, goodIn, guardOpen, rejected, completed)
     + completed
         -> done . DovetailGuard(leftIn, badIn, goodIn, guardOpen, rejected, true);

init
  DovetailGuard(true, true, true, true, false, false);
"""


def render_rho_guard_formula(spec: dict) -> str:
    guard = spec["guarded_join"]
    reject = guard["bad_reject_observation"]
    commit = guard["good_commit_observation"]
    return " &&\n".join(
        [
            f"<reserveGuardBad . {reject} . reserveGuardGood . {commit} . observeBad>true",
            f"<reserveGuardBad . {reject} . reserveGuardGood . {commit} . observeRejected>true",
            f"[reserveGuardBad . {reject}]<reserveGuardGood . {commit} . observeBad>true",
            f"<reserveGuardGood . {commit} . observeBad>true",
            f"[reserveGuardGood . {commit}]<observeBad>true",
        ]
    ) + "\n"


def render_dovetail_guard_formula(spec: dict) -> str:
    guard = spec["guarded_join"]
    reject = guard["bad_reject_observation"]
    commit = guard["good_commit_observation"]
    return " &&\n".join(
        [
            f"<{reject} . {commit} . observeBad>true",
            f"<{reject} . {commit} . observeRejected>true",
            f"[{reject}]<{commit} . observeBad>true",
            f"<{commit} . observeBad>true",
            f"[{commit}]<observeBad>true",
        ]
    ) + "\n"


def render_maude_rho(spec: dict) -> str:
    labels = [r["label"] for r in spec["redexes"]]
    facts = [r["fact"] for r in spec["redexes"]]
    ops = facts + [f"reserved{label}" for label in labels] + [f"fired{label}" for label in labels] + ["reservedJoin", "completed"]
    visible_steps = [f"fire{label}" for label in labels] + ["complete"]
    lines = [
        "--- Generated from formal/process/rho_comm_slice.json.",
        "--- Executable rewrite-logic projection for a finite RhoNet COMM",
        "--- fragment with internal RSpace-style reserve/commit phases.",
        "",
        "mod RHO-NET-COMM is",
        "  protecting BOOL .",
        "",
        "  sorts Fact State .",
        "  subsort Fact < State .",
        "",
        f"  ops {' '.join(ops)} : -> Fact [ctor] .",
        "  op empty : -> State [ctor] .",
        "  op __ : State State -> State [ctor assoc comm id: empty] .",
        "",
    ]
    for label, fact in zip(labels, facts):
        lines.append(f"  rl [reserve{label}] : {fact} => reserved{label} .")
        lines.append(f"  rl [fire{label}] : reserved{label} => fired{label} .")
    lines.append(f"  rl [reserveJoin] : {' '.join(f'fired{label}' for label in labels)} => reservedJoin .")
    lines.append("  rl [complete] : reservedJoin => completed .")
    lines.append("endm")
    lines.append("")
    lines.extend(
        [
            "mod RHO-NET-COMM-TRACED is",
            "  protecting BOOL .",
            "",
            "  sorts Fact State Trace Step Config .",
            "  subsort Fact < State .",
            "",
            f"  ops {' '.join(ops)} : -> Fact [ctor] .",
            f"  ops {' '.join(visible_steps)} : -> Step [ctor] .",
            "  op empty : -> State [ctor] .",
            "  op __ : State State -> State [ctor assoc comm id: empty] .",
            "  op nil : -> Trace [ctor] .",
            "  op _then_ : Trace Step -> Trace [ctor] .",
            "  op <_;_> : State Trace -> Config [ctor] .",
            "",
            "  var REST : State .",
            "  var T : Trace .",
            "",
        ]
    )
    for label, fact in zip(labels, facts):
        lines.append(f"  rl [reserve{label}Traced] : < {fact} REST ; T > => < reserved{label} REST ; T > .")
        lines.append(f"  rl [fire{label}Traced] : < reserved{label} REST ; T > => < fired{label} REST ; T then fire{label} > .")
    lines.append(
        f"  rl [reserveJoinTraced] : < {' '.join(f'fired{label}' for label in labels)} REST ; T > => < reservedJoin REST ; T > ."
    )
    lines.append("  rl [completeTraced] : < reservedJoin REST ; T > => < completed REST ; T then complete > .")
    lines.append("endm")
    guard = spec["guarded_join"]
    gl = guard["left_fact"]
    bad = guard["bad_fact"]
    good = guard["good_fact"]
    open_fact = guard["open_fact"]
    rejected = guard["rejected_fact"]
    completed = guard["completed_fact"]
    reject = guard["bad_reject_observation"]
    commit = guard["good_commit_observation"]
    lines.extend(
        [
            "",
            "mod RHO-GUARDED-JOIN is",
            "  protecting BOOL .",
            "",
            "  sorts Fact State .",
            "  subsort Fact < State .",
            "",
            f"  ops {gl} {bad} {good} {open_fact} {rejected} {completed} reservedGuardBad reservedGuardGood : -> Fact [ctor] .",
            "  op empty : -> State [ctor] .",
            "  op __ : State State -> State [ctor assoc comm id: empty] .",
            "",
            f"  rl [reserveGuardBad] : {gl} {bad} {open_fact} => reservedGuardBad .",
            f"  rl [{reject}] : reservedGuardBad => {gl} {bad} {rejected} .",
            f"  rl [reserveGuardGood] : {gl} {good} => reservedGuardGood .",
            f"  rl [{commit}] : reservedGuardGood => {completed} .",
            "endm",
            "",
            "mod RHO-GUARDED-JOIN-TRACED is",
            "  protecting BOOL .",
            "",
            "  sorts Fact State Trace Step Config .",
            "  subsort Fact < State .",
            "",
            f"  ops {gl} {bad} {good} {open_fact} {rejected} {completed} reservedGuardBad reservedGuardGood : -> Fact [ctor] .",
            f"  ops {reject} {commit} : -> Step [ctor] .",
            "  op empty : -> State [ctor] .",
            "  op __ : State State -> State [ctor assoc comm id: empty] .",
            "  op nil : -> Trace [ctor] .",
            "  op _then_ : Trace Step -> Trace [ctor] .",
            "  op <_;_> : State Trace -> Config [ctor] .",
            "",
            "  var REST : State .",
            "  var T : Trace .",
            "",
            f"  rl [reserveGuardBadTraced] : < {gl} {bad} {open_fact} REST ; T > => < reservedGuardBad REST ; T > .",
            f"  rl [{reject}Traced] : < reservedGuardBad REST ; T > => < {gl} {bad} {rejected} REST ; T then {reject} > .",
            f"  rl [reserveGuardGoodTraced] : < {gl} {good} REST ; T > => < reservedGuardGood REST ; T > .",
            f"  rl [{commit}Traced] : < reservedGuardGood REST ; T > => < {completed} REST ; T then {commit} > .",
            "endm",
        ]
    )
    return "\n".join(lines) + "\n"


def render_maude_dovetail(spec: dict) -> str:
    labels = [r["label"] for r in spec["redexes"]]
    facts = [r["fact"] for r in spec["redexes"]]
    ops = facts + [f"fired{label}" for label in labels] + ["completed"]
    visible_steps = [f"fire{label}" for label in labels] + ["complete"]
    lines = [
        "--- Generated from formal/process/rho_comm_slice.json.",
        "--- Executable rewrite-logic projection for the corresponding finite",
        "--- Dovetail fact-step fragment. The visible observations intentionally",
        "--- match the RhoNet projection in rho-net.maude.",
        "",
        "mod DOVETAIL-FACT-STEPS is",
        "  protecting BOOL .",
        "",
        "  sorts Fact State .",
        "  subsort Fact < State .",
        "",
        f"  ops {' '.join(ops)} : -> Fact [ctor] .",
        "  op empty : -> State [ctor] .",
        "  op __ : State State -> State [ctor assoc comm id: empty] .",
        "",
    ]
    for label, fact in zip(labels, facts):
        lines.append(f"  rl [fire{label}] : {fact} => fired{label} .")
    lines.append(f"  rl [complete] : {' '.join(f'fired{label}' for label in labels)} => completed .")
    lines.append("endm")
    lines.append("")
    lines.extend(
        [
            "mod DOVETAIL-FACT-STEPS-TRACED is",
            "  protecting BOOL .",
            "",
            "  sorts Fact State Trace Step Config .",
            "  subsort Fact < State .",
            "",
            f"  ops {' '.join(ops)} : -> Fact [ctor] .",
            f"  ops {' '.join(visible_steps)} : -> Step [ctor] .",
            "  op empty : -> State [ctor] .",
            "  op __ : State State -> State [ctor assoc comm id: empty] .",
            "  op nil : -> Trace [ctor] .",
            "  op _then_ : Trace Step -> Trace [ctor] .",
            "  op <_;_> : State Trace -> Config [ctor] .",
            "",
            "  var REST : State .",
            "  var T : Trace .",
            "",
        ]
    )
    for label, fact in zip(labels, facts):
        lines.append(f"  rl [fire{label}Traced] : < {fact} REST ; T > => < fired{label} REST ; T then fire{label} > .")
    lines.append(
        f"  rl [completeTraced] : < {' '.join(f'fired{label}' for label in labels)} REST ; T > => < completed REST ; T then complete > ."
    )
    lines.append("endm")
    guard = spec["guarded_join"]
    gl = guard["left_fact"]
    bad = guard["bad_fact"]
    good = guard["good_fact"]
    open_fact = guard["open_fact"]
    rejected = guard["rejected_fact"]
    completed = guard["completed_fact"]
    reject = guard["bad_reject_observation"]
    commit = guard["good_commit_observation"]
    lines.extend(
        [
            "",
            "mod DOVETAIL-GUARDED-JOIN is",
            "  protecting BOOL .",
            "",
            "  sorts Fact State .",
            "  subsort Fact < State .",
            "",
            f"  ops {gl} {bad} {good} {open_fact} {rejected} {completed} : -> Fact [ctor] .",
            "  op empty : -> State [ctor] .",
            "  op __ : State State -> State [ctor assoc comm id: empty] .",
            "",
            f"  rl [{reject}] : {gl} {bad} {open_fact} => {gl} {bad} {rejected} .",
            f"  rl [{commit}] : {gl} {good} => {completed} .",
            "endm",
            "",
            "mod DOVETAIL-GUARDED-JOIN-TRACED is",
            "  protecting BOOL .",
            "",
            "  sorts Fact State Trace Step Config .",
            "  subsort Fact < State .",
            "",
            f"  ops {gl} {bad} {good} {open_fact} {rejected} {completed} : -> Fact [ctor] .",
            f"  ops {reject} {commit} : -> Step [ctor] .",
            "  op empty : -> State [ctor] .",
            "  op __ : State State -> State [ctor assoc comm id: empty] .",
            "  op nil : -> Trace [ctor] .",
            "  op _then_ : Trace Step -> Trace [ctor] .",
            "  op <_;_> : State Trace -> Config [ctor] .",
            "",
            "  var REST : State .",
            "  var T : Trace .",
            "",
            f"  rl [{reject}Traced] : < {gl} {bad} {open_fact} REST ; T > => < {gl} {bad} {rejected} REST ; T then {reject} > .",
            f"  rl [{commit}Traced] : < {gl} {good} REST ; T > => < {completed} REST ; T then {commit} > .",
            "endm",
        ]
    )
    return "\n".join(lines) + "\n"


def maude_trace(actions: list[str]) -> str:
    trace = "nil"
    for action in actions:
        trace = f"({trace} then {action})"
    return trace


def maude_visible_schedule_queries(spec: dict) -> list[tuple[str, str]]:
    labels = [r["label"] for r in spec["redexes"]]
    facts = [r["fact"] for r in spec["redexes"]]
    fact_multiset = " ".join(facts)
    queries: list[tuple[str, str]] = []

    positive_orders = list(itertools.permutations(labels))
    for order in positive_orders:
        actions = [f"fire{label}" for label in order] + ["complete"]
        trace = maude_trace(actions)
        queries.append(
            (
                f"search [1] in RHO-NET-COMM-TRACED : < {fact_multiset} ; nil > =>* < completed ; {trace} > .",
                "Solution 1",
            )
        )
        queries.append(
            (
                f"search [1] in DOVETAIL-FACT-STEPS-TRACED : < {fact_multiset} ; nil > =>* < completed ; {trace} > .",
                "Solution 1",
            )
        )

    premature_prefixes: set[tuple[str, ...]] = {()}
    for length in range(1, len(labels)):
        premature_prefixes.update(itertools.permutations(labels, length))
    for prefix in sorted(premature_prefixes):
        actions = [f"fire{label}" for label in prefix] + ["complete"]
        trace = maude_trace(actions)
        queries.append(
            (
                f"search [1] in RHO-NET-COMM-TRACED : < {fact_multiset} ; nil > =>* < completed ; {trace} > .",
                "No solution.",
            )
        )
        queries.append(
            (
                f"search [1] in DOVETAIL-FACT-STEPS-TRACED : < {fact_multiset} ; nil > =>* < completed ; {trace} > .",
                "No solution.",
            )
        )
    return queries


def expected_visible_schedule_query_counts(redex_count: int) -> tuple[int, int]:
    positive = 2 * math.factorial(redex_count)
    premature_prefixes = sum(
        math.factorial(redex_count) // math.factorial(redex_count - length)
        for length in range(redex_count)
    )
    negative = 2 * premature_prefixes
    return positive, negative


def maude_guard_queries(spec: dict) -> list[tuple[str, str]]:
    guard = spec["guarded_join"]
    gl = guard["left_fact"]
    bad = guard["bad_fact"]
    good = guard["good_fact"]
    open_fact = guard["open_fact"]
    rejected = guard["rejected_fact"]
    completed = guard["completed_fact"]
    reject = guard["bad_reject_observation"]
    commit = guard["good_commit_observation"]
    initial = f"{gl} {bad} {good} {open_fact}"
    reject_trace = maude_trace([reject])
    reject_commit_trace = maude_trace([reject, commit])
    commit_trace = maude_trace([commit])
    return [
        (
            f"search [1] in RHO-GUARDED-JOIN : {initial} =>* {gl} {bad} {good} {rejected} .",
            "Solution 1",
        ),
        (
            f"search [1] in DOVETAIL-GUARDED-JOIN : {initial} =>* {gl} {bad} {good} {rejected} .",
            "Solution 1",
        ),
        (
            f"search [1] in RHO-GUARDED-JOIN : {initial} =>! {bad} {rejected} {completed} .",
            "Solution 1",
        ),
        (
            f"search [1] in DOVETAIL-GUARDED-JOIN : {initial} =>! {bad} {rejected} {completed} .",
            "Solution 1",
        ),
        (
            f"search [1] in RHO-GUARDED-JOIN : {initial} =>! {bad} {open_fact} {completed} .",
            "Solution 1",
        ),
        (
            f"search [1] in DOVETAIL-GUARDED-JOIN : {initial} =>! {bad} {open_fact} {completed} .",
            "Solution 1",
        ),
        (
            f"search [1] in RHO-GUARDED-JOIN-TRACED : < {initial} ; nil > =>* < {bad} {rejected} {completed} ; {reject_commit_trace} > .",
            "Solution 1",
        ),
        (
            f"search [1] in DOVETAIL-GUARDED-JOIN-TRACED : < {initial} ; nil > =>* < {bad} {rejected} {completed} ; {reject_commit_trace} > .",
            "Solution 1",
        ),
        (
            f"search [1] in RHO-GUARDED-JOIN-TRACED : < {initial} ; nil > =>* < {bad} {open_fact} {completed} ; {commit_trace} > .",
            "Solution 1",
        ),
        (
            f"search [1] in DOVETAIL-GUARDED-JOIN-TRACED : < {initial} ; nil > =>* < {bad} {open_fact} {completed} ; {commit_trace} > .",
            "Solution 1",
        ),
        (
            f"search [1] in RHO-GUARDED-JOIN-TRACED : < {initial} ; nil > =>* < {bad} {rejected} {completed} ; {reject_trace} > .",
            "No solution.",
        ),
        (
            f"search [1] in DOVETAIL-GUARDED-JOIN-TRACED : < {initial} ; nil > =>* < {bad} {rejected} {completed} ; {reject_trace} > .",
            "No solution.",
        ),
    ]


def render_maude_checks(spec: dict) -> str:
    labels = [r["label"] for r in spec["redexes"]]
    facts = [r["fact"] for r in spec["redexes"]]
    fact_multiset = " ".join(facts)
    lines = [
        "--- Generated from formal/process/rho_comm_slice.json.",
        "load ../rho-net.maude",
        "load ../dovetail-rules.maude",
        "",
        f"search [2] in RHO-NET-COMM : {fact_multiset} =>! S:State .",
        f"search [2] in DOVETAIL-FACT-STEPS : {fact_multiset} =>! S:State .",
        "",
    ]
    for index, (label, fact) in enumerate(zip(labels, facts)):
        rest = facts.copy()
        rest[index] = f"reserved{label}"
        lines.append(f"search [1] in RHO-NET-COMM : {fact_multiset} =>* {' '.join(rest)} .")
        rest[index] = f"fired{label}"
        lines.append(f"search [1] in RHO-NET-COMM : {fact_multiset} =>* {' '.join(rest)} .")
    lines.append(f"search [1] in RHO-NET-COMM : {fact_multiset} =>* reservedJoin .")
    for index, label in enumerate(labels):
        rest = facts.copy()
        rest[index] = f"fired{label}"
        lines.append(f"search [1] in DOVETAIL-FACT-STEPS : {fact_multiset} =>* {' '.join(rest)} .")
    lines.append("")
    lines.append("--- Visible schedule equivalence checks.")
    lines.append("--- Rho internal reserve steps are intentionally not recorded in the trace.")
    for query, _ in maude_visible_schedule_queries(spec):
        lines.append(query)
    lines.append("")
    lines.append("--- Guarded join checks.")
    lines.append("--- Failed guards release their data; valid joins can still commit later.")
    for query, _ in maude_guard_queries(spec):
        lines.append(query)
    lines.extend(["", "quit", ""])
    return "\n".join(lines)


def normalize_maude_query(query: str) -> str:
    return " ".join(query.replace("(", " ").replace(")", " ").split())


def maude_ac_query_parts(query: str) -> tuple[str, Counter[str]] | None:
    normalized = normalize_maude_query(query)
    if "<" in normalized or "=>*" not in normalized:
        return None
    prefix, target = normalized.split("=>*", 1)
    target = target.strip()
    if target.endswith("."):
        target = target[:-1].strip()
    return prefix.strip(), Counter(target.split())


def find_maude_block(blocks: dict[str, str], query: str) -> str | None:
    normalized = normalize_maude_query(query)
    block = blocks.get(normalized)
    if block is not None:
        return block
    ac_parts = maude_ac_query_parts(query)
    if ac_parts is None:
        return None
    for candidate, candidate_block in blocks.items():
        if maude_ac_query_parts(candidate) == ac_parts:
            return candidate_block
    return None


def maude_log_blocks(log_text: str) -> dict[str, str]:
    blocks: dict[str, str] = {}
    for raw_block in log_text.split("=========================================="):
        lines = raw_block.splitlines()
        while lines and not lines[0].strip():
            lines.pop(0)
        if not lines or not lines[0].startswith("search "):
            continue
        query_lines = []
        for line in lines:
            if not line.strip():
                break
            query_lines.append(line.strip())
        blocks[normalize_maude_query(" ".join(query_lines))] = "\n".join(lines)
    return blocks


def check_maude_log(spec: dict, log_path: Path) -> int:
    log_text = log_path.read_text(encoding="utf-8")
    blocks = maude_log_blocks(log_text)
    labels = [r["label"] for r in spec["redexes"]]
    facts = [r["fact"] for r in spec["redexes"]]
    fact_multiset = " ".join(facts)

    expectations: list[tuple[str, str, str]] = [
        (
            f"search [2] in RHO-NET-COMM : {fact_multiset} =>! S:State .",
            "S:State --> completed",
            "rho terminal state is completed",
        ),
        (
            f"search [2] in RHO-NET-COMM : {fact_multiset} =>! S:State .",
            "No more solutions.",
            "rho terminal state is unique",
        ),
        (
            f"search [2] in DOVETAIL-FACT-STEPS : {fact_multiset} =>! S:State .",
            "S:State --> completed",
            "dovetail terminal state is completed",
        ),
        (
            f"search [2] in DOVETAIL-FACT-STEPS : {fact_multiset} =>! S:State .",
            "No more solutions.",
            "dovetail terminal state is unique",
        ),
    ]
    for index, (label, fact) in enumerate(zip(labels, facts)):
        rest = facts.copy()
        rest[index] = f"reserved{label}"
        expectations.append(
            (
                f"search [1] in RHO-NET-COMM : {fact_multiset} =>* {' '.join(rest)} .",
                "Solution 1",
                f"rho can reserve {label}",
            )
        )
        rest[index] = f"fired{label}"
        expectations.append(
            (
                f"search [1] in RHO-NET-COMM : {fact_multiset} =>* {' '.join(rest)} .",
                "Solution 1",
                f"rho can visibly fire {label}",
            )
        )
    expectations.append(
        (
            f"search [1] in RHO-NET-COMM : {fact_multiset} =>* reservedJoin .",
            "Solution 1",
            "rho can reserve final join",
        )
    )
    for index, label in enumerate(labels):
        rest = facts.copy()
        rest[index] = f"fired{label}"
        expectations.append(
            (
                f"search [1] in DOVETAIL-FACT-STEPS : {fact_multiset} =>* {' '.join(rest)} .",
                "Solution 1",
                f"dovetail can visibly fire {label}",
            )
        )
    for query, expected in maude_visible_schedule_queries(spec):
        expectations.append((query, expected, query))
    for query, expected in maude_guard_queries(spec):
        expectations.append((query, expected, query))

    failures = []
    for query, expected, label in expectations:
        block = find_maude_block(blocks, query)
        if block is None:
            failures.append(f"missing Maude query for {label}: {query}")
        elif expected not in block:
            failures.append(f"Maude query failed {label}: expected {expected!r} in block:\n{block}")
    if failures:
        print("Maude Rho COMM slice verification failed:")
        for failure in failures:
            print(f"  {failure}")
        return 1
    return 0


def tla_set(items: list[str], indent: str = "  ") -> list[str]:
    if not items:
        return [indent + "{}"]
    quoted = [f'"{item}"' for item in items]
    lines = [indent + "{" + quoted[0] + ("," if len(quoted) > 1 else "}")]
    for item in quoted[1:-1]:
        lines.append(indent + " " + item + ",")
    if len(quoted) > 1:
        lines.append(indent + " " + quoted[-1] + "}")
    return lines


def tla_membership(variable: str, items: list[str], indent: str = "  ") -> list[str]:
    set_lines = tla_set(items, "")
    lines = [f"{indent}{variable} \\in {set_lines[0]}"]
    lines.extend(indent + line for line in set_lines[1:])
    return lines


def render_tla(spec: dict) -> str:
    labels = [r["label"] for r in spec["redexes"]]
    q = spec["completion_observation"]
    prefixes = ["Empty"]
    for length in range(1, len(labels) + 1):
        prefixes.extend("".join(order) for order in itertools.permutations(labels, length))
    full = ["".join(order) for order in itertools.permutations(labels)]
    completed = [trace + q for trace in full]
    valid = prefixes + completed

    lines = [
        "---- MODULE RhoNetScheduler ----",
        "EXTENDS Naturals, Sequences, TLC",
        "",
        "\\* Generated from formal/process/rho_comm_slice.json.",
        "\\* Bounded scheduler model for a finite RhoNet COMM fragment.",
        "\\*",
        "\\* The COMM redexes are independent. A fair scheduler may fire them",
        "\\* in any order; once all are fired, the complete observation must",
        "\\* become enabled and, under weak fairness, eventually occur.",
        "",
        "VARIABLES",
    ]
    for label in labels:
        lines.extend([f"  \\* @type: Bool;", f"  fired{label},"])
    lines.extend(["  \\* @type: Bool;", "  completed,", "  \\* @type: Str;", "  trace", ""])
    lines.append(f"vars == <<{', '.join([f'fired{label}' for label in labels] + ['completed', 'trace'])}>>")
    lines.extend(["", "ValidTraces =="])
    lines.extend(tla_set(valid))
    lines.append("")
    for label in labels:
        has_items = [trace for trace in valid if label in trace]
        lines.append(f"TraceHas{label}(t) ==")
        lines.extend(tla_membership("t", has_items))
        lines.append("")
    lines.append(f"TraceHas{q}(t) ==")
    lines.extend(tla_membership("t", completed))
    lines.append("")

    for label in labels:
        mappings = []
        for trace in prefixes:
            current = "" if trace == "Empty" else trace
            if label not in current and len(current) < len(labels):
                next_trace = current + label
                mappings.append((trace, next_trace))
        lines.append(f"Append{label}(t) ==")
        for index, (source, target) in enumerate(mappings):
            prefix = "  IF" if index == 0 else "  ELSE IF"
            lines.append(f'{prefix} t = "{source}" THEN "{target}"')
        lines.append(f'  ELSE "{mappings[-1][1]}"')
        lines.append("")

    lines.append(f"Append{q}(t) ==")
    for index, trace in enumerate(full):
        prefix = "  IF" if index == 0 else "  ELSE IF"
        lines.append(f'{prefix} t = "{trace}" THEN "{trace}{q}"')
    lines.append(f'  ELSE "{full[-1]}{q}"')
    lines.append("")
    lines.append("Init ==")
    for label in labels:
        lines.append(f"  /\\ fired{label} = FALSE")
    lines.extend(["  /\\ completed = FALSE", '  /\\ trace = "Empty"', ""])

    for label in labels:
        lines.append(f"Fire{label} ==")
        lines.append(f"  /\\ ~fired{label}")
        lines.append("  /\\ ~completed")
        for other in labels:
            value = "TRUE" if other == label else f"fired{other}"
            lines.append(f"  /\\ fired{other}' = {value}")
        lines.append("  /\\ completed' = FALSE")
        lines.append(f"  /\\ trace' = Append{label}(trace)")
        lines.append("")

    lines.append("Complete ==")
    for label in labels:
        lines.append(f"  /\\ fired{label}")
    lines.append("  /\\ ~completed")
    for label in labels:
        lines.append(f"  /\\ fired{label}' = fired{label}")
    lines.append("  /\\ completed' = TRUE")
    lines.append(f"  /\\ trace' = Append{q}(trace)")
    lines.append("")
    lines.extend(["Done ==", "  /\\ completed", "  /\\ UNCHANGED vars", ""])
    lines.append(f"Next == {' \\/ '.join([f'Fire{label}' for label in labels] + ['Complete', 'Done'])}")
    lines.append("")
    lines.extend(["Spec ==", "  /\\ Init", "  /\\ [][Next]_vars"])
    for label in labels:
        lines.append(f"  /\\ WF_vars(Fire{label})")
    lines.append("  /\\ WF_vars(Complete)")
    lines.append("")
    lines.append("TypeOK ==")
    for label in labels:
        lines.append(f"  /\\ fired{label} \\in BOOLEAN")
    lines.extend(["  /\\ completed \\in BOOLEAN", "  /\\ trace \\in ValidTraces", ""])
    lines.extend(["CompleteOnlyAfterInputs ==", "  completed => " + " /\\ ".join(f"fired{label}" for label in labels), ""])
    lines.append("TraceMatchesState ==")
    for label in labels:
        lines.append(f"  /\\ fired{label} <=> TraceHas{label}(trace)")
    lines.append(f"  /\\ completed <=> TraceHas{q}(trace)")
    lines.append("")
    lines.extend(["NoPrematureCompletion ==", "  completed => trace \\in " + "{" + ", ".join(f'"{item}"' for item in completed) + "}", ""])
    lines.extend(
        [
            "AllInputsEnableCompletion ==",
            "  " + " /\\ ".join(f"fired{label}" for label in labels) + " /\\ ~completed => ENABLED Complete",
            "",
            "EventuallyComplete == <>completed",
            "",
            "====",
            "",
        ]
    )
    return "\n".join(lines)


def generated_files(spec: dict) -> dict[Path, str]:
    return {
        ROOT / "formal/mcrl2/rho_machine/rho_net_comm.mcrl2": render_mcrl2_rho(spec),
        ROOT / "formal/mcrl2/rho_machine/dovetail_fact_steps.mcrl2": render_mcrl2_dovetail(spec),
        ROOT / "formal/mcrl2/rho_machine/rho_guarded_join.mcrl2": render_mcrl2_rho_guard(spec),
        ROOT / "formal/mcrl2/rho_machine/dovetail_guarded_join.mcrl2": render_mcrl2_dovetail_guard(spec),
        ROOT / "formal/mcrl2/rho_machine/formulas/rho_internal_schedules_complete.mcf": render_rho_formula(spec),
        ROOT / "formal/mcrl2/rho_machine/formulas/dovetail_direct_schedules_complete.mcf": render_dovetail_formula(spec),
        ROOT / "formal/mcrl2/rho_machine/formulas/rho_guard_nonconsuming.mcf": render_rho_guard_formula(spec),
        ROOT / "formal/mcrl2/rho_machine/formulas/dovetail_guard_nonconsuming.mcf": render_dovetail_guard_formula(spec),
        ROOT / "formal/maude/rho_machine/rho-net.maude": render_maude_rho(spec),
        ROOT / "formal/maude/rho_machine/dovetail-rules.maude": render_maude_dovetail(spec),
        ROOT / "formal/maude/rho_machine/checks/comm-schedule.maude": render_maude_checks(spec),
        ROOT / "formal/tla/rho_machine/RhoNetScheduler.tla": render_tla(spec),
    }


def render_mcrl2_tau(spec: dict) -> str:
    labels = [r["label"] for r in spec["redexes"]]
    return ",".join([f"reserve{label}" for label in labels] + ["reserveJoin"])


def check_files(files: dict[Path, str]) -> int:
    mismatches = []
    for path, expected in files.items():
        actual = path.read_text(encoding="utf-8") if path.exists() else None
        if actual != expected:
            mismatches.append(path)
    if mismatches:
        print("Generated Rho COMM slice files are stale:")
        for path in mismatches:
            print(f"  {path.relative_to(ROOT)}")
        print("Run: python3 formal/process/rho_comm_slice.py --write")
        return 1
    return 0


def sample_spec(redex_count: int = 4) -> dict:
    labels = [chr(ord("A") + index) for index in range(redex_count)]
    return {
        "name": f"rho_comm_{redex_count}_redex",
        "completion_observation": "Q",
        "redexes": [
            {
                "label": label,
                "fact": f"fact{label}",
            }
            for label in labels
        ],
        "guarded_join": {
            "left_fact": "gl",
            "bad_fact": "gbad",
            "good_fact": "gok",
            "open_fact": "guardOpen",
            "rejected_fact": "rejectedGuard",
            "completed_fact": "completedGuard",
            "bad_reject_observation": "guardReject",
            "good_commit_observation": "guardCommit",
        },
    }


def expect_invalid(spec: dict, expected: str) -> None:
    try:
        validate_spec(spec)
    except ValueError as err:
        if expected not in str(err):
            raise AssertionError(f"expected validation error containing {expected!r}, got {err!r}") from err
        return
    raise AssertionError(f"expected validation error containing {expected!r}")


def run_self_test() -> int:
    for redex_count in range(1, 6):
        spec = validate_spec(sample_spec(redex_count))
        labels = [redex["label"] for redex in spec["redexes"]]
        positive_count, negative_count = expected_visible_schedule_query_counts(redex_count)
        visible_queries = maude_visible_schedule_queries(spec)
        expected_total = positive_count + negative_count
        if len(visible_queries) != expected_total:
            raise AssertionError(
                f"{redex_count} redexes produced {len(visible_queries)} "
                f"visible Maude schedule queries, expected {expected_total}"
            )
        if sum(expected == "Solution 1" for _, expected in visible_queries) != positive_count:
            raise AssertionError(
                f"{redex_count} redexes produced the wrong number of positive visible schedules"
            )
        if sum(expected == "No solution." for _, expected in visible_queries) != negative_count:
            raise AssertionError(
                f"{redex_count} redexes produced the wrong number of premature-completion negatives"
            )
        normalized_queries = [normalize_maude_query(query) for query, _ in visible_queries]
        if len(normalized_queries) != len(set(normalized_queries)):
            raise AssertionError(
                f"{redex_count} redexes produced duplicate visible Maude schedule queries"
            )
        rho_clauses = [line for line in render_rho_formula(spec).split("&&") if line.strip()]
        dovetail_clauses = [line for line in render_dovetail_formula(spec).split("&&") if line.strip()]
        if len(rho_clauses) != math.factorial(redex_count) * 2:
            raise AssertionError(
                f"{redex_count} redexes produced the wrong number of Rho mCRL2 schedule clauses"
            )
        if len(dovetail_clauses) != math.factorial(redex_count) * 2:
            raise AssertionError(
                f"{redex_count} redexes produced the wrong number of Dovetail mCRL2 schedule clauses"
            )
        tau_actions = render_mcrl2_tau(spec).split(",")
        if tau_actions != [f"reserve{label}" for label in labels] + ["reserveJoin"]:
            raise AssertionError(
                f"{redex_count} redexes produced the wrong mCRL2 tau action set"
            )
        render_tla(spec)

    duplicate_label = sample_spec()
    duplicate_label["redexes"][1]["label"] = duplicate_label["redexes"][0]["label"]
    expect_invalid(duplicate_label, "redex labels")

    duplicate_lowered_label = sample_spec()
    duplicate_lowered_label["redexes"][1]["label"] = duplicate_lowered_label[
        "redexes"
    ][0]["label"].lower()
    expect_invalid(duplicate_lowered_label, "field-name lowering")

    duplicate_fact = sample_spec()
    duplicate_fact["redexes"][1]["fact"] = duplicate_fact["redexes"][0]["fact"]
    expect_invalid(duplicate_fact, "redex facts")

    empty_redexes = sample_spec()
    empty_redexes["redexes"] = []
    expect_invalid(empty_redexes, "redexes must be nonempty")

    invalid_label = sample_spec()
    invalid_label["redexes"][0]["label"] = "bad-label"
    expect_invalid(invalid_label, "ASCII identifier")

    duplicate_completion = sample_spec()
    duplicate_completion["completion_observation"] = duplicate_completion["redexes"][0][
        "label"
    ]
    expect_invalid(duplicate_completion, "completion observation")

    duplicate_guard_fact = sample_spec()
    duplicate_guard_fact["guarded_join"]["good_fact"] = duplicate_guard_fact[
        "guarded_join"
    ]["bad_fact"]
    expect_invalid(duplicate_guard_fact, "guarded-join facts")

    overlapping_guard_fact = sample_spec()
    overlapping_guard_fact["guarded_join"]["bad_fact"] = overlapping_guard_fact[
        "redexes"
    ][0]["fact"]
    expect_invalid(overlapping_guard_fact, "distinct from COMM facts")

    overlapping_guard_observation = sample_spec()
    overlapping_guard_observation["guarded_join"][
        "good_commit_observation"
    ] = overlapping_guard_observation["guarded_join"]["completed_fact"]
    expect_invalid(overlapping_guard_observation, "distinct from guarded-join facts")

    return 0


def write_files(files: dict[Path, str]) -> int:
    for path, content in files.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="check generated files without writing")
    parser.add_argument("--write", action="store_true", help="rewrite generated files")
    parser.add_argument("--check-maude-log", type=Path, help="check a Maude comm-schedule log")
    parser.add_argument(
        "--mcrl2-tau",
        action="store_true",
        help="print reserve actions to hide for mCRL2 branching-bisim checks",
    )
    parser.add_argument("--self-test", action="store_true", help="run generator invariant tests")
    args = parser.parse_args()
    selected = sum(
        bool(flag)
        for flag in (
            args.check,
            args.write,
            args.check_maude_log,
            args.mcrl2_tau,
            args.self_test,
        )
    )
    if selected != 1:
        parser.error(
            "choose exactly one of --check, --write, --check-maude-log, "
            "--mcrl2-tau, or --self-test"
        )
    if args.self_test:
        return run_self_test()
    spec = load_spec()
    files = generated_files(spec)
    if args.check:
        return check_files(files)
    if args.write:
        return write_files(files)
    if args.mcrl2_tau:
        print(render_mcrl2_tau(spec))
        return 0
    return check_maude_log(spec, args.check_maude_log)


if __name__ == "__main__":
    raise SystemExit(main())
