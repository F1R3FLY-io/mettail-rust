#!/usr/bin/env python3
"""Generate and check the bounded Rho/Dovetail COMM process slice."""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC_PATH = Path(__file__).with_name("rho_comm_slice.json")


def load_spec() -> dict:
    with SPEC_PATH.open(encoding="utf-8") as handle:
        spec = json.load(handle)
    redexes = spec["redexes"]
    labels = [redex["label"] for redex in redexes]
    facts = [redex["fact"] for redex in redexes]
    if len(labels) != len(set(labels)):
        raise ValueError("redex labels must be unique")
    if len(facts) != len(set(facts)):
        raise ValueError("redex facts must be unique")
    if spec["completion_observation"] in labels:
        raise ValueError("completion observation must be distinct from redex labels")
    return spec


def lower(label: str) -> str:
    return label.lower()


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


def render_maude_rho(spec: dict) -> str:
    labels = [r["label"] for r in spec["redexes"]]
    facts = [r["fact"] for r in spec["redexes"]]
    ops = facts + [f"reserved{label}" for label in labels] + [f"fired{label}" for label in labels] + ["reservedJoin", "completed"]
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
    return "\n".join(lines) + "\n"


def render_maude_dovetail(spec: dict) -> str:
    labels = [r["label"] for r in spec["redexes"]]
    facts = [r["fact"] for r in spec["redexes"]]
    ops = facts + [f"fired{label}" for label in labels] + ["completed"]
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
    return "\n".join(lines) + "\n"


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
    lines.extend(["", "quit", ""])
    return "\n".join(lines)


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
        ROOT / "formal/mcrl2/rho_machine/formulas/rho_internal_schedules_complete.mcf": render_rho_formula(spec),
        ROOT / "formal/mcrl2/rho_machine/formulas/dovetail_direct_schedules_complete.mcf": render_dovetail_formula(spec),
        ROOT / "formal/maude/rho_machine/rho-net.maude": render_maude_rho(spec),
        ROOT / "formal/maude/rho_machine/dovetail-rules.maude": render_maude_dovetail(spec),
        ROOT / "formal/maude/rho_machine/checks/comm-schedule.maude": render_maude_checks(spec),
        ROOT / "formal/tla/rho_machine/RhoNetScheduler.tla": render_tla(spec),
    }


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


def write_files(files: dict[Path, str]) -> int:
    for path, content in files.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="check generated files without writing")
    parser.add_argument("--write", action="store_true", help="rewrite generated files")
    args = parser.parse_args()
    if args.check == args.write:
        parser.error("choose exactly one of --check or --write")
    files = generated_files(load_spec())
    return check_files(files) if args.check else write_files(files)


if __name__ == "__main__":
    raise SystemExit(main())
