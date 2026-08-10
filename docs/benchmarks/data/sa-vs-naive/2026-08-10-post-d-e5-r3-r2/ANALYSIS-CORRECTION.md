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
