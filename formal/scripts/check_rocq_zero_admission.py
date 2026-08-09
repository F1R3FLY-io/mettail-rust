#!/usr/bin/env python3
"""Check critical Rocq suites for proof admissions after stripping comments."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_ROOTS = [
    "dovetail/formal/rocq/theories",
    "formal/rocq/rho_bridge/theories",
    "formal/rocq/symbolic_algebra/theories",
    "formal/rocq/sft/theories",
    "formal/rocq/advanced_automata/theories",
    "formal/rocq/trampoline/theories",
]
DEFAULT_COQ_PROJECTS = [
    "formal/rocq/prattail_wpda_runtime/_CoqProject",
]
BANNED_COMMAND = re.compile(
    r"^\s*(?:Local\s+|Global\s+|Polymorphic\s+|Monomorphic\s+)*"
    r"(?:Axiom|Conjecture|Parameter|Parameters)\b|"
    r"^\s*Admitted\s*\.|"
    r"(?<![A-Za-z0-9_])admit\s*\."
)


def strip_rocq_comments(text: str, path: Path) -> str:
    """Remove nested Rocq comments while preserving line numbers."""

    depth = 0
    output: list[str] = []
    index = 0
    while index < len(text):
        if text.startswith("(*", index):
            depth += 1
            output.append(" ")
            output.append(" ")
            index += 2
            continue
        if depth > 0 and text.startswith("*)", index):
            depth -= 1
            output.append(" ")
            output.append(" ")
            index += 2
            continue
        char = text[index]
        if depth > 0:
            output.append("\n" if char == "\n" else " ")
        else:
            output.append(char)
        index += 1

    if depth != 0:
        raise ValueError(f"{path}: unterminated Rocq comment")
    return "".join(output)


def coq_project_entries(project: Path, text: str) -> list[Path]:
    """Resolve the Rocq sources registered by one ``_CoqProject`` manifest."""

    files: list[Path] = []
    for line_number, raw_line in enumerate(text.splitlines(), start=1):
        line = raw_line.partition("#")[0].strip()
        if not line or line.startswith("-"):
            continue
        tokens = line.split()
        sources = [token for token in tokens if token.endswith(".v")]
        if len(sources) > 1:
            raise ValueError(
                f"{project}:{line_number}: multiple Rocq sources on one manifest line"
            )
        if sources:
            files.append(project.parent / sources[0])
    return files


def rocq_files(roots: list[Path], coq_projects: list[Path]) -> list[Path]:
    files: list[Path] = []
    for root in roots:
        if root.is_file() and root.suffix == ".v":
            files.append(root)
        elif root.is_dir():
            files.extend(sorted(root.rglob("*.v")))
        else:
            raise FileNotFoundError(root)
    for project in coq_projects:
        if not project.is_file():
            raise FileNotFoundError(project)
        for path in coq_project_entries(project, project.read_text(encoding="utf-8")):
            if not path.is_file():
                raise FileNotFoundError(
                    f"{project}: registered Rocq source does not exist: {path}"
                )
            files.append(path)
    return sorted(set(files))


def display_path(path: Path) -> Path:
    try:
        return path.relative_to(REPO_ROOT)
    except ValueError:
        return path


def check_text(path: Path, text: str) -> list[str]:
    uncommented = strip_rocq_comments(text, path)
    failures = []
    for line_number, line in enumerate(uncommented.splitlines(), start=1):
        if BANNED_COMMAND.search(line):
            failures.append(f"{display_path(path)}:{line_number}: {line.strip()}")
    return failures


def check_file(path: Path) -> list[str]:
    return check_text(path, path.read_text(encoding="utf-8"))


def run_self_test() -> int:
    clean = """
(* Axiom hidden_in_comment : False. *)
(* nested (* Admitted. *) comment *)
Definition admit_force := 0.
Theorem ok : True.
Proof. exact I. Qed.
"""
    if check_text(Path("clean_self_test.v"), clean):
        raise AssertionError(
            "comment stripping or identifier handling produced a false positive"
        )

    cases = {
        "axiom_self_test.v": "Axiom bad : False.\n",
        "conjecture_self_test.v": "Conjecture bad : False.\n",
        "parameter_self_test.v": "Parameter bad : False.\n",
        "admitted_self_test.v": "Theorem bad : False.\nAdmitted.\n",
        "admit_tactic_self_test.v": "Theorem bad : False.\nProof. admit. Qed.\n",
    }
    for filename, text in cases.items():
        if not check_text(Path(filename), text):
            raise AssertionError(
                f"{filename} did not trigger the zero-admission scanner"
            )

    project = Path("formal/rocq/example/_CoqProject")
    entries = coq_project_entries(
        project,
        """
-Q theories Example
theories/First.v
theories/Second.v # an inline explanation
""",
    )
    expected = [
        project.parent / "theories/First.v",
        project.parent / "theories/Second.v",
    ]
    if entries != expected:
        raise AssertionError(
            f"_CoqProject source discovery drifted: expected {expected}, got {entries}"
        )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run scanner self-tests instead of scanning repository files",
    )
    parser.add_argument(
        "--coq-project",
        action="append",
        default=[],
        help="scan the .v sources registered by this _CoqProject manifest",
    )
    parser.add_argument(
        "roots",
        nargs="*",
        help="Rocq files or directories to scan; defaults to critical Dovetail/Rho suites",
    )
    args = parser.parse_args()

    if args.self_test:
        return run_self_test()

    roots = [REPO_ROOT / root for root in (args.roots or DEFAULT_ROOTS)]
    project_names = args.coq_project or ([] if args.roots else DEFAULT_COQ_PROJECTS)
    coq_projects = [REPO_ROOT / project for project in project_names]
    failures = []
    files = rocq_files(roots, coq_projects)
    for path in files:
        failures.extend(check_file(path))

    if failures:
        print("Rocq zero-admission check failed:", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1
    print(f"Rocq zero-admission check passed: {len(files)} registered/critical sources")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
