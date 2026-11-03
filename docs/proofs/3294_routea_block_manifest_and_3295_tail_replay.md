# 3294/3295 Route A block manifest and tail replay

Record 3294 converts the audited 3273 weighted-original 40960-cell JSONL into
160 contiguous blocks of 256 cells.  The generator replays the grid, Taylor-6
cell formula, upward rounding, and exact aggregate before writing the block
sums.  The result is external evidence only.

Record 3295 adds the correction-owner contour tail from the 2353 supplier to
the 3294 finite upper.  The combined rational upper is negative, but neither
the block values nor the tail supplier is imported into Lean.

The Lean side adds `sum_range_mul_block_decomp3294` and a consumer theorem
that accepts three explicit premises: endpoint dominance over
`ratCellValueUpper3289`, block upper bounds, and a strictly negative sum of
those block bounds.  This is the proof shape needed to avoid expanding all
40960 rational rectangles in one `native_decide` call.

```text
3273 JSONL replay
        |
        v
3294 block sums (external)
        |
        +--> Lean endpoint dominance (open)
        +--> Lean block-sum sign (open)
        |
        v
3295 finite + 2353 tail (external negative)
        |
        v
signed full-kernel / C3' import (open)
```

The fail-closed status is intentional.  A sidecar number is not a Lean
certificate merely because it is rational or exactly replayable.

Validation used the project gate in WSL2 ext4:

```text
cat lean-toolchain
# leanprover/lean4:v4.30.0
lean --version
# Lean (version 4.30.0)
LEAN_NUM_THREADS=1 lake build ConnesWeilRH.Dev.C1RouteARationalBlockManifest3294
```

The focused build completed with `3968/3968` jobs. The independent audit
reported exactly `[propext, Classical.choice, Quot.sound]` for both the range
decomposition and the block-manifest consumer theorem.
