#!/usr/bin/env python3
"""E-6a (pgmcp experiment 145) analysis: per-cell control-vs-treatment on the
pre-registered PRIMARY metric `spread_plus_matching_comms_per_normalization`
(lower better), Welch t-test at alpha = 0.05 with Benjamini-Hochberg correction
across the cell family (the LOCKED criterion), plus the honest secondaries
(inj wall, consumed cost units, encoded len, attempts).

The primary metric is COUNTER-DETERMINISTIC (fixed seeds, fresh runtime per
rep), so within-arm variance is expected to be exactly 0; Welch degenerates to
the exact comparison (p = 0 when the constants differ, p = 1 when equal) —
handled explicitly below and reported as such.

Reads driver/*.jsonl; writes summary.csv (one row per cell x arm), the
per-cell test table cells.csv, and comparison.md.
"""

import csv
import glob
import json
import math
import os
import statistics
import sys

from scipy import stats

HERE = os.path.dirname(os.path.abspath(__file__))
DRIVER_DIR = os.path.join(HERE, "driver")
ALPHA = 0.05

PRIMARY = "spread_plus_matching_comms_per_normalization"
SECONDARIES = ["inj_ns", "consumed_cost_units", "program_encoded_len", "attempts"]


def load_cells():
    cells = {}
    for path in sorted(glob.glob(os.path.join(DRIVER_DIR, "*.jsonl"))):
        header = None
        reps = []
        dnfs = []
        with open(path, encoding="utf-8") as handle:
            for line in handle:
                line = line.strip()
                if not line:
                    continue
                record = json.loads(line)
                if "e6a_header" in record:
                    header = record["e6a_header"]
                elif "e6a_rep" in record:
                    reps.append(record["e6a_rep"])
                elif record.get("dnf"):
                    dnfs.append(record)
        if header is None:
            print(f"WARN: no header in {path}", file=sys.stderr)
            continue
        key = (header["workload"], int(header["n"]))
        arm = header["arm"]
        cells.setdefault(key, {})[arm] = {
            "header": header,
            "reps": [r for r in reps if not r["is_warmup"]],
            "warmups": [r for r in reps if r["is_warmup"]],
            "dnfs": dnfs,
            "path": os.path.relpath(path, HERE),
        }
    return cells


def series(reps, metric):
    return [float(r[metric]) for r in reps]


def welch(control, treatment):
    """Welch p-value, degenerate-variance-aware (deterministic counters)."""
    if len(control) < 2 or len(treatment) < 2:
        return None
    vc = statistics.pvariance(control)
    vt = statistics.pvariance(treatment)
    if vc == 0.0 and vt == 0.0:
        return 0.0 if control[0] != treatment[0] else 1.0
    result = stats.ttest_ind(control, treatment, equal_var=False)
    return float(result.pvalue)


def benjamini_hochberg(pvalues):
    """BH-adjusted q-values (step-up), preserving input order; None passthrough."""
    indexed = [(i, p) for i, p in enumerate(pvalues) if p is not None]
    m = len(indexed)
    adjusted = [None] * len(pvalues)
    if m == 0:
        return adjusted
    indexed.sort(key=lambda item: item[1])
    running = 1.0
    for rank in range(m, 0, -1):
        index, p = indexed[rank - 1]
        q = min(running, p * m / rank)
        running = q
        adjusted[index] = q
    return adjusted


def median(values):
    return statistics.median(values) if values else float("nan")


def main():
    cells = load_cells()
    if not cells:
        print("no driver data found", file=sys.stderr)
        return 1

    summary_rows = []
    test_rows = []
    for (workload, n), arms in sorted(cells.items()):
        for arm in ("control", "treatment"):
            if arm not in arms:
                continue
            data = arms[arm]
            reps = data["reps"]
            row = {
                "workload": workload,
                "n": n,
                "arm": arm,
                "measured_reps": len(reps),
                "warmup_reps": len(data["warmups"]),
                "dnf_count": len(data["dnfs"]),
                "dnf_reason_first": (data["dnfs"][0]["reason"] if data["dnfs"] else ""),
                "source": data["path"],
            }
            for metric in [PRIMARY, "spread_sends", "matching_comms"] + SECONDARIES:
                values = series(reps, metric) if reps else []
                row[f"{metric}_median"] = median(values)
                row[f"{metric}_min"] = min(values) if values else float("nan")
                row[f"{metric}_max"] = max(values) if values else float("nan")
            if reps:
                row["firing_visible_median"] = median(series(reps, "comm.firing_visible")
                    if False else [float(r["comm"]["firing_visible"]) for r in reps])
                row["observed_count_median"] = median(series(reps, "observed_count"))
            summary_rows.append(row)

        control = arms.get("control", {}).get("reps", [])
        treatment = arms.get("treatment", {}).get("reps", [])
        cell_row = {"workload": workload, "n": n,
                    "control_reps": len(control), "treatment_reps": len(treatment)}
        if control and treatment:
            c = series(control, PRIMARY)
            t = series(treatment, PRIMARY)
            cell_row["control_primary_median"] = median(c)
            cell_row["treatment_primary_median"] = median(t)
            cell_row["effect"] = median(t) - median(c)
            cell_row["effect_sign"] = (
                "treatment_lower" if median(t) < median(c)
                else ("equal" if median(t) == median(c) else "treatment_higher")
            )
            cell_row["p_welch_primary"] = welch(c, t)
            ci = series(control, "inj_ns")
            ti = series(treatment, "inj_ns")
            cell_row["control_inj_ns_median"] = median(ci)
            cell_row["treatment_inj_ns_median"] = median(ti)
            cell_row["p_welch_inj_ns"] = welch(ci, ti)
        else:
            cell_row["control_primary_median"] = median(series(control, PRIMARY)) if control else None
            cell_row["treatment_primary_median"] = median(series(treatment, PRIMARY)) if treatment else None
            cell_row["effect"] = None
            missing = "treatment" if not treatment else "control"
            arm_data = arms.get("treatment" if not treatment else "control", {})
            reason = arm_data.get("dnfs", [{}])[0].get("reason", "no data") if arm_data else "no data"
            cell_row["effect_sign"] = f"{missing}_dnf: {reason[:120]}"
            cell_row["p_welch_primary"] = None
            cell_row["p_welch_inj_ns"] = None
        test_rows.append(cell_row)

    qs = benjamini_hochberg([row["p_welch_primary"] for row in test_rows])
    qi = benjamini_hochberg([row["p_welch_inj_ns"] for row in test_rows])
    for row, q_primary, q_inj in zip(test_rows, qs, qi):
        row["q_bh_primary"] = q_primary
        row["q_bh_inj_ns"] = q_inj
        row["significant_primary"] = (q_primary is not None and q_primary < ALPHA)
        row["significant_inj_ns"] = (q_inj is not None and q_inj < ALPHA)

    with open(os.path.join(HERE, "summary.csv"), "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(summary_rows[0].keys()))
        writer.writeheader()
        writer.writerows(summary_rows)
    with open(os.path.join(HERE, "cells.csv"), "w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(test_rows[0].keys()))
        writer.writeheader()
        writer.writerows(test_rows)

    with open(os.path.join(HERE, "comparison.md"), "w", encoding="utf-8") as handle:
        handle.write("# E-6a comparison — PathMap-index treatment vs spread+drive control\n\n")
        handle.write(
            "Primary (LOCKED): `spread_plus_matching_comms_per_normalization`, lower better; "
            "Welch α=0.05, BH across cells. The primary is counter-deterministic "
            "(within-arm variance 0 on every completed cell), so Welch degenerates to the "
            "exact comparison (p=0 iff the constants differ). Secondary (exploratory): "
            "inj wall ns.\n\n")
        handle.write(
            "| workload | n | control primary (median) | treatment primary (median) | "
            "effect (t−c) | sign | q_BH primary | sig | control inj ms | treatment inj ms | "
            "q_BH inj | sig |\n")
        handle.write("|---|---|---|---|---|---|---|---|---|---|---|---|\n")
        for row in test_rows:
            def fmt(value, scale=1.0, digits=3):
                if value is None or (isinstance(value, float) and math.isnan(value)):
                    return "—"
                return f"{value / scale:.{digits}f}".rstrip("0").rstrip(".")
            handle.write(
                f"| {row['workload']} | {row['n']} "
                f"| {fmt(row.get('control_primary_median'))} "
                f"| {fmt(row.get('treatment_primary_median'))} "
                f"| {fmt(row.get('effect'))} | {row.get('effect_sign')} "
                f"| {fmt(row.get('q_bh_primary'), 1.0, 6)} "
                f"| {'YES' if row.get('significant_primary') else '—'} "
                f"| {fmt(row.get('control_inj_ns_median'), 1e6)} "
                f"| {fmt(row.get('treatment_inj_ns_median'), 1e6)} "
                f"| {fmt(row.get('q_bh_inj_ns'), 1.0, 6)} "
                f"| {'YES' if row.get('significant_inj_ns') else '—'} |\n")
        handle.write("\nSee summary.csv (per-arm medians/min/max of every recorded metric) "
                     "and cells.csv (the test table).\n")

    print(f"wrote {os.path.join(HERE, 'summary.csv')}")
    print(f"wrote {os.path.join(HERE, 'cells.csv')}")
    print(f"wrote {os.path.join(HERE, 'comparison.md')}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
