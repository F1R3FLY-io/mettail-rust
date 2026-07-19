# E-6a comparison — PathMap-index treatment vs spread+drive control

Primary (LOCKED): `spread_plus_matching_comms_per_normalization`, lower better; Welch α=0.05, BH across cells. The primary is counter-deterministic (within-arm variance 0 on every completed cell), so Welch degenerates to the exact comparison (p=0 iff the constants differ). Secondary (exploratory): inj wall ns.

| workload | n | control primary (median) | treatment primary (median) | effect (t−c) | sign | q_BH primary | sig | control inj ms | treatment inj ms | q_BH inj | sig |
|---|---|---|---|---|---|---|---|---|---|---|---|
| lambda_chain | 4 | 178 | 16 | -162 | treatment_lower | 0 | YES | 22.396 | 56.797 | 0 | YES |
| lambda_chain | 8 | 596 | 32 | -564 | treatment_lower | 0 | YES | 75.2 | 232.249 | 0 | YES |
| multi_rule_shared | 402 | 88 | 13 | -75 | treatment_lower | 0 | YES | 7.537 | 75.254 | 0 | YES |
| multi_rule_shared | 803 | 220 | 25 | -195 | treatment_lower | 0 | YES | 28.088 | 623.416 | 0 | YES |
| nested_spine | 2 | 32 | 5 | -27 | treatment_lower | 0 | YES | 1.992 | 8.543 | 0 | YES |
| nested_spine | 8 | 140 | 11 | -129 | treatment_lower | 0 | YES | 13.508 | 211.945 | 0 | YES |
| nested_spine | 16 | 284 | 19 | -265 | treatment_lower | 0 | YES | 47.929 | 1382.703 | 0 | YES |
| swap_comb | 4 | 64 | 7 | -57 | treatment_lower | 0 | YES | 4.165 | 41.999 | 0 | YES |
| swap_comb | 16 | 268 | 19 | -249 | treatment_lower | 0 | YES | 41.826 | 1660.51 | 0 | YES |
| swap_comb | 64 | 1084 | — | — | treatment_dnf: E-6a index «s» entry exceeds the machine trie-key caps at location `site0/Pair.1/Pair.1/Pair.1/Pair.1/Pair.1/Pair.1/Pair | — | — | — | — | — | — |

See summary.csv (per-arm medians/min/max of every recorded metric) and cells.csv (the test table).
