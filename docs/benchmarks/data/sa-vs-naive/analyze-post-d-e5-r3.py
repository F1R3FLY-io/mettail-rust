#!/usr/bin/env python3
"""Analyze a frozen pgmcp experiment-174 capture without changing its data.

The primary metric is deterministic ``matching_tau`` (lower is better).  Wall
time is secondary: this script reports one-sided Welch tests with
Benjamini-Hochberg correction and a one-sided 95% upper confidence bound for
the treatment/control geometric-mean ratio.  The ratio interval is computed
on ``log(inj_ns)`` with Welch-Satterthwaite degrees of freedom.  That method is
fixed here before the one-shot capture is made.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import statistics
from collections import defaultdict
from pathlib import Path

from scipy import stats

ALPHA = 0.05
NONINFERIORITY_RATIO = 1.05
EXPECTED_REPS = 51
SIZES = (2, 4, 8, 16, 32, 64)


def bh_adjust(values: list[float]) -> list[float]:
    """Return Benjamini-Hochberg step-up q-values in input order."""
    ranked = sorted(enumerate(values), key=lambda pair: pair[1])
    adjusted = [1.0] * len(values)
    running = 1.0
    for rank in range(len(ranked), 0, -1):
        index, value = ranked[rank - 1]
        running = min(running, value * len(ranked) / rank)
        adjusted[index] = running
    return adjusted


def welch_df(left: list[float], right: list[float]) -> tuple[float, float]:
    """Return the standard error and Welch-Satterthwaite degrees of freedom."""
    left_var = statistics.variance(left)
    right_var = statistics.variance(right)
    left_term = left_var / len(left)
    right_term = right_var / len(right)
    standard_error = math.sqrt(left_term + right_term)
    if standard_error == 0.0:
        return 0.0, math.inf
    numerator = (left_term + right_term) ** 2
    denominator = left_term**2 / (len(left) - 1) + right_term**2 / (len(right) - 1)
    return standard_error, numerator / denominator


def wall_statistics(control: list[int], treatment: list[int]) -> dict[str, float]:
    """Compute frozen superiority and 5% non-inferiority wall statistics."""
    control_float = [float(value) for value in control]
    treatment_float = [float(value) for value in treatment]
    superiority = stats.ttest_ind(
        treatment_float, control_float, equal_var=False, alternative="less"
    )

    control_log = [math.log(value) for value in control_float]
    treatment_log = [math.log(value) for value in treatment_float]
    delta = statistics.mean(treatment_log) - statistics.mean(control_log)
    standard_error, degrees = welch_df(treatment_log, control_log)
    if standard_error == 0.0:
        ratio_upper = math.exp(delta)
        noninferiority_p = 0.0 if delta < math.log(NONINFERIORITY_RATIO) else 1.0
    else:
        critical = stats.t.ppf(1.0 - ALPHA, degrees)
        ratio_upper = math.exp(delta + critical * standard_error)
        statistic = (delta - math.log(NONINFERIORITY_RATIO)) / standard_error
        noninferiority_p = float(stats.t.cdf(statistic, degrees))
    return {
        "control_inj_ns_median": statistics.median(control_float),
        "treatment_inj_ns_median": statistics.median(treatment_float),
        "geomean_ratio": math.exp(delta),
        "ratio_upper_95": ratio_upper,
        "p_superiority": float(superiority.pvalue),
        "p_noninferiority_1_05": noninferiority_p,
    }


def constant(rows: list[dict[str, str]], field: str) -> int:
    values = {int(row[field]) for row in rows}
    if len(values) != 1:
        raise ValueError(f"{field} is not deterministic: {sorted(values)}")
    return values.pop()


def load(run_directory: Path) -> dict[tuple[int, str], list[dict[str, str]]]:
    samples = run_directory / "samples.tsv"
    grouped: dict[tuple[int, str], list[dict[str, str]]] = defaultdict(list)
    with samples.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle, delimiter="\t"):
            grouped[(int(row["n"]), row["matcher"])].append(row)
    expected = {(size, arm) for size in SIZES for arm in ("sa", "naive-r3")}
    if set(grouped) != expected:
        raise ValueError(
            f"cell set differs: got {sorted(grouped)}, expected {sorted(expected)}"
        )
    for cell, rows in grouped.items():
        if len(rows) != EXPECTED_REPS:
            raise ValueError(
                f"{cell} has {len(rows)} measured reps, expected {EXPECTED_REPS}"
            )
    return grouped


def analyze(run_directory: Path) -> tuple[list[dict[str, object]], str]:
    grouped = load(run_directory)
    results: list[dict[str, object]] = []
    for size in SIZES:
        control = grouped[(size, "sa")]
        treatment = grouped[(size, "naive-r3")]
        row: dict[str, object] = {"n": size}
        for prefix, arm in (("control", control), ("treatment", treatment)):
            for metric in (
                "program_encoded_len",
                "program_receiver_count",
                "observed_count",
                "consumed_cost_units",
                "matching_tau",
                "firing_visible",
                "subst_tau",
                "respread_tau",
                "other",
                "join_arity_gt1",
                "attempts",
                "successes",
            ):
                row[f"{prefix}_{metric}"] = constant(arm, metric)
        row.update(
            wall_statistics(
                [int(sample["inj_ns"]) for sample in control],
                [int(sample["inj_ns"]) for sample in treatment],
            )
        )
        row["semantic_pass"] = (
            row["control_observed_count"] == size
            and row["treatment_observed_count"] == size
            and row["control_firing_visible"] == size
            and row["treatment_firing_visible"] == size
        )
        row["r3_route_pass"] = (
            row["treatment_matching_tau"] == 4 * size
            and row["treatment_subst_tau"] == 3 * size
            and row["treatment_respread_tau"] == 3 * size
            and row["treatment_other"] == size
            and row["treatment_join_arity_gt1"] == 0
        )
        row["primary_pass"] = (
            row["treatment_matching_tau"] < row["control_matching_tau"]
        )
        row["resource_pass"] = (
            row["treatment_consumed_cost_units"] <= row["control_consumed_cost_units"]
            and row["treatment_program_encoded_len"]
            <= row["control_program_encoded_len"]
        )
        results.append(row)

    superiority_q = bh_adjust([float(row["p_superiority"]) for row in results])
    noninferiority_q = bh_adjust(
        [float(row["p_noninferiority_1_05"]) for row in results]
    )
    for row, sup_q, noninf_q in zip(results, superiority_q, noninferiority_q):
        row["q_bh_superiority"] = sup_q
        row["q_bh_noninferiority_1_05"] = noninf_q
        row["wall_pass"] = (
            float(row["ratio_upper_95"]) <= NONINFERIORITY_RATIO and noninf_q < ALPHA
        )

    retarget = all(
        bool(row[key])
        for row in results
        for key in (
            "semantic_pass",
            "r3_route_pass",
            "primary_pass",
            "resource_pass",
            "wall_pass",
        )
    )
    decision = (
        "retarget-generated-driver-to-r3" if retarget else "keep-both-production-routes"
    )
    return results, decision


def write_outputs(
    run_directory: Path, results: list[dict[str, object]], decision: str
) -> None:
    payload = {
        "experiment_id": 174,
        "alpha": ALPHA,
        "bh_family": list(SIZES),
        "wall_ratio_method": "Welch log-scale one-sided 95% upper confidence bound",
        "noninferiority_ratio": NONINFERIORITY_RATIO,
        "decision": decision,
        "cells": results,
    }
    (run_directory / "analysis.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    lines = [
        "# Post-D-E5 production-SA versus persistent-R3 comparison",
        "",
        f"Decision: **{decision}**.",
        "",
        "The primary is exact deterministic `matching_tau`. Wall time uses a one-sided ",
        "Welch test, Benjamini-Hochberg correction over the six sizes, and a log-scale ",
        "one-sided 95% upper confidence bound for the treatment/control geometric-mean ratio.",
        "",
        "| n | SA match | R3 match | cost SA/R3 | bytes SA/R3 | wall ratio | upper 95% | q noninf | gates |",
        "|---:|---:|---:|---:|---:|---:|---:|---:|:---|",
    ]
    for row in results:
        gates = (
            "PASS"
            if all(
                bool(row[key])
                for key in (
                    "semantic_pass",
                    "r3_route_pass",
                    "primary_pass",
                    "resource_pass",
                    "wall_pass",
                )
            )
            else "KEEP BOTH"
        )
        lines.append(
            f"| {row['n']} | {row['control_matching_tau']} | {row['treatment_matching_tau']} "
            f"| {row['control_consumed_cost_units']}/{row['treatment_consumed_cost_units']} "
            f"| {row['control_program_encoded_len']}/{row['treatment_program_encoded_len']} "
            f"| {float(row['geomean_ratio']):.4f} | {float(row['ratio_upper_95']):.4f} "
            f"| {float(row['q_bh_noninferiority_1_05']):.6g} | {gates} |"
        )
    lines.extend(["", "Machine-readable detail: `analysis.json`.", ""])
    (run_directory / "comparison.md").write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("run_directory", type=Path)
    args = parser.parse_args()
    results, decision = analyze(args.run_directory)
    write_outputs(args.run_directory, results, decision)
    print(decision)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
