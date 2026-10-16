# Complete-owner dependency and storage audit

This source-only round adds no producer and runs no aggregate build.

## Mathematical dependency

`CC20YoshidaConvolution.lean:323` constructs a correction through
`fixed_window_finite_mellin_surjective`, then obtains a quadratic decay
constant. The fixed-correction assembly at line 1099 retains this correction
and constant for every convolution count n. Its explicit bound is
`(6*pi)^2 * (1/2)^(n+1) * C`.

The important quantifier order is:

```text
choose finite radius R
  -> choose correction(R) and C(R)
  -> choose convolution count n
  -> evaluate the gate for this same owner and its actual prime domain
```

Thus increasing n can make this tail estimate small for a fixed correction,
but does not prove the same-owner gate survives. Increasing R changes the
correction and C; it is not a free prefix extension. The displayed theorem is
quadratic decay, not by itself the twelfth-order raw product premise used by
2711. Neither a numerical cardinal interpolant nor its sampled constants can
be identified with the existential correction without a separate equality or
a construction satisfying the same consumer premises.

The next bounded target is to expose a quantitative norm bound from the
finite interpolation construction and track its dependence on node separation,
then compare it with the actual same-owner gate. Completion requires a proved
inequality or a scoped obstruction; another interface or n scan is insufficient.
Budget: one source-only review, 30 minutes, no generated entry modules.

## WSL inventory and targeted cleanup

Old build: `.lake/build`, 220 GiB.
Active build: `.lake/build`, 50 GiB.
File sizes below are logical bytes, not filesystem allocation:

```text
type       old build bytes    active build bytes
.json      150192552428       33972812388
.olean      59092609608       15922468888
.c          21449659446        1569914253
.ilean       3002649171        1205152306
```

Largest observed JSON files are generated `ir/.../*.setup.json`, including
`C1RouteAAnalyticContainmentBridge2646.setup.json` (5365371 bytes). This is
evidence about the largest examples, not a classification of every JSON file.
No JSON was deleted under the existing extension-limited cleanup authorization.

After verifying no exact-name lake/lean process was running, removed only
68885 regular `.c` files from the resolved old build root: 21449659446 bytes.
All sources, proof objects, certificates, current build and unrelated caches
were retained. WSL free bytes increased from 138600759296 to 160193921024.
The machine-readable receipt is in the active WSL copy at
`results/2712_old_c_cleanup.json`.

This frees space inside WSL. It does not establish that the Windows VHDX
container shrank. No compaction or WSL shutdown was performed.
