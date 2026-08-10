# Post-D-E5 production-SA versus persistent-R3 comparison

Decision: **retarget-generated-driver-to-r3**.

The primary is exact deterministic `matching_tau`. Wall time uses a one-sided
Welch test, Benjamini-Hochberg correction over the six sizes, and a log-scale
one-sided 95% upper confidence bound for the treatment/control geometric-mean ratio.

| n | SA match | R3 match | cost SA/R3 | bytes SA/R3 | wall ratio | upper 95% | q noninf | gates |
|---:|---:|---:|---:|---:|---:|---:|---:|:---|
| 2 | 17 | 8 | 85/42 | 31540/14045 | 0.7354 | 0.7461 | 9.81942e-54 | PASS |
| 4 | 46 | 16 | 230/74 | 74880/15005 | 0.5874 | 0.5970 | 1.88492e-79 | PASS |
| 8 | 140 | 32 | 700/138 | 196960/16925 | 0.4766 | 0.4815 | 8.1902e-110 | PASS |
| 16 | 472 | 64 | 2360/266 | 582720/20765 | 0.3899 | 0.3944 | 6.452e-100 | PASS |
| 32 | 1712 | 128 | 8560/522 | 1920640/28445 | 0.2908 | 0.2919 | 5.04236e-162 | PASS |
| 64 | 6496 | 256 | 32480/1034 | 6862080/43899 | 0.1866 | 0.1872 | 7.54835e-114 | PASS |

Machine-readable detail: `analysis.json`.
