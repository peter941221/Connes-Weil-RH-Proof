# 2109 - Known-prefix owner margin ledger

Date: 2026-09-28.

Status: `KNOWN-PREFIX-MARGIN-LEDGER-CANDIDATE`.

For the weakest tested known-prefix owner at
`gamma=39.2524485855`, `delta=0.445`, and `scale=0.80`, the sampled finite
window margin is `1.675397327895099e12`. Owner-matched charges are:

```text
finite-window EM forward       5.720420308066749e7
true a_mat transfer             5.9268334716796875e4
true Gram H1 diagnostic         1.733805888696289e7
40..infinity tail               2.2087121764650203e-138
known error sum                 7.460153030234718e7
known error / margin            4.452766460841471e-5
```

The direct square solve is used because the interpolation matrix is square and
nonsingular; it is the unique feasible coefficient vector and therefore also
the minimum-H1 feasible vector for this same family. The Gram movement is kept
as a separate diagnostic and is not charged twice into the direct path.

This ledger is not a producer theorem. The first-30 numerical zero prefix is
not the complete abstract `sourceNontrivialZeroSet` closed-ball owner, and
outward promotion, owner-uniform conditioning, and Lean certificate assembly
remain open.

Artifact: `results/2109_known_prefix_margin_ledger.json`.
Script: `scripts/routea_known_prefix_margin_ledger_2109.py`.
