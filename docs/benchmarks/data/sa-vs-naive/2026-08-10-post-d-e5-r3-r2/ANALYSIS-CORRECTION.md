# Experiment 174 analysis correction record

The raw samples in this directory are complete and immutable. All twelve cells
contain three warmups and 51 measured repetitions, zero DNF results, and one
deterministic counter/resource vector per cell. `sha256sums.txt` authenticates
the driver, JSON-lines samples, tabular projections, and initial derived output.

The initial committed analyzer produced `keep-both-production-routes` because
its semantic predicate incorrectly required both arms to emit `n` observations.
That is not the frozen contract. The two implementations deliberately expose
different observation shapes:

* production SA emits `n` individual observations;
* persistent R3 emits one combined normal-form observation;
* both must record `n` visible firings;
* the driver must validate each arm's exact expected observed content.

Every R3 cell correctly reported one observation, so the faulty predicate—and
only that predicate—failed. Pgmcp bug
`use-arm-specific-observation-cardinalities-in-the-post-d-e5-decision-gate-98c6aa`
tracks the correction. The raw run will not be repeated or altered. The repair
will recompute only derived analysis from these same authenticated samples, and
git history will retain this initial result for auditability.

The corrected analyzer's three arm-shape regression tests pass. Re-analysis of
the unchanged samples produces `retarget-generated-driver-to-r3`: all five
gates pass at all six sizes. R3 uses fewer matching COMMs, consumed cost units,
and encoded program bytes at every size; its wall-time geometric-mean ratio
falls from 0.7354 at `n = 2` to 0.1866 at `n = 64`, and every one-sided 95%
upper ratio bound is below the frozen 1.05 threshold after the associated
six-cell Benjamini-Hochberg non-inferiority gate.
