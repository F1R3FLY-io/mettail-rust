# E-6a comparison — PathMap-index treatment vs spread+drive control

Primary (LOCKED): `spread_plus_matching_comms_per_normalization`, lower better; Welch α=0.05, BH across cells. The primary is counter-deterministic (within-arm variance 0 on every completed cell), so Welch degenerates to the exact comparison (p=0 iff the constants differ). Secondary (exploratory): inj wall ns.

| workload | n | control primary (median) | treatment primary (median) | effect (t−c) | sign | q_BH primary | sig | control inj ms | treatment inj ms | q_BH inj | sig |
|---|---|---|---|---|---|---|---|---|---|---|---|
| lambda_chain | 4 | 178 | 16 | -162 | treatment_lower | 0 | YES | 20.473 | 24.614 | 0 | YES |
| lambda_chain | 8 | 596 | 32 | -564 | treatment_lower | 0 | YES | 69.985 | 83.289 | 0 | YES |
| multi_rule_shared | 402 | 88 | 13 | -75 | treatment_lower | 0 | YES | 6.92 | 16.295 | 0 | YES |
| multi_rule_shared | 803 | 220 | 25 | -195 | treatment_lower | 0 | YES | 26.467 | 109.207 | 0 | YES |
| nested_spine | 2 | 32 | 5 | -27 | treatment_lower | 0 | YES | 1.902 | 3.19 | 0 | YES |
| nested_spine | 8 | 140 | 11 | -129 | treatment_lower | 0 | YES | 12.448 | 44.674 | 0 | YES |
| nested_spine | 16 | 284 | 19 | -265 | treatment_lower | 0 | YES | 44.257 | 246.227 | 0 | YES |
| swap_comb | 4 | 64 | 7 | -57 | treatment_lower | 0 | YES | 3.935 | 10.319 | 0 | YES |
| swap_comb | 16 | 268 | 19 | -249 | treatment_lower | 0 | YES | 39.481 | 250.735 | 0 | YES |
| swap_comb | 64 | 1084 | — | — | treatment_dnf: E-6a index «s» entry exceeds the machine trie-key caps at location `site0/Pair.1/Pair.1/Pair.1/Pair.1/Pair.1/Pair.1/Pair | — | — | — | — | — | — |

See summary.csv (per-arm medians/min/max of every recorded metric) and cells.csv (the test table).
