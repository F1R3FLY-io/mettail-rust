# E-6a comparison — PathMap-index treatment vs spread+drive control

Primary (LOCKED): `spread_plus_matching_comms_per_normalization`, lower better; Welch α=0.05, BH across cells. The primary is counter-deterministic (within-arm variance 0 on every completed cell), so Welch degenerates to the exact comparison (p=0 iff the constants differ). Secondary (exploratory): inj wall ns.

| workload | n | control primary (median) | treatment primary (median) | effect (t−c) | sign | q_BH primary | sig | control inj ms | treatment inj ms | q_BH inj | sig |
|---|---|---|---|---|---|---|---|---|---|---|---|
| lambda_chain | 4 | 178 | 16 | -162 | treatment_lower | 0 | YES | 21.847 | 53.389 | 0 | YES |
| lambda_chain | 8 | 596 | 32 | -564 | treatment_lower | 0 | YES | 74.211 | 217.392 | 0 | YES |
| multi_rule_shared | 402 | 88 | 13 | -75 | treatment_lower | 0 | YES | 7.165 | 65.246 | 0 | YES |
| multi_rule_shared | 803 | 220 | 25 | -195 | treatment_lower | 0 | YES | 26.858 | 567.204 | 0 | YES |
| nested_spine | 2 | 32 | 5 | -27 | treatment_lower | 0 | YES | 1.987 | 7.832 | 0 | YES |
| nested_spine | 8 | 140 | 11 | -129 | treatment_lower | 0 | YES | 13.246 | 195.893 | 0 | YES |
| nested_spine | 16 | 284 | 19 | -265 | treatment_lower | 0 | YES | 46.445 | 1315.088 | 0 | YES |
| swap_comb | 4 | 64 | 7 | -57 | treatment_lower | 0 | YES | 4.182 | 38.333 | 0 | YES |
| swap_comb | 16 | 268 | 19 | -249 | treatment_lower | 0 | YES | 41.294 | 1541.572 | 0 | YES |
| swap_comb | 64 | 1084 | — | — | treatment_dnf: E-6a index «s» entry exceeds the machine trie-key caps at location `site0/Pair.1/Pair.1/Pair.1/Pair.1/Pair.1/Pair.1/Pair | — | — | — | — | — | — |

See summary.csv (per-arm medians/min/max of every recorded metric) and cells.csv (the test table).
