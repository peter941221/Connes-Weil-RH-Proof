# 3267: Route A formal weighted-original full-window blocks

Status
------

Diagnostic only. This record does not provide a Lean certificate,
`producer_go`, `SourceRH`, or RH.

Method
------

The 3238 weighted-original Taylor-6 evaluator is replayed over the complete
40960-cell finite window. The 30 owner families are split into contiguous
blocks, and each block receives its own value, second-derivative,
fourth-derivative, and sixth-derivative enclosure before its cell integrals
are summed.

This measures the cost of separating family blocks. The sixth-derivative
envelope is not cancellation-preserving across blocks, so a positive sum of
block uppers is a decomposition loss, not a mathematical no-go for the
aggregate evaluator.

Reproduction
------------

    python scripts/routea_concrete_owner_weighted_original_blocks_3267.py

Output
------

    results/3267_routea_original_blocks_40960_5.json
