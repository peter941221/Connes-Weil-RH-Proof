# G8 P1 — literal metric survivor/boundary Gram

Date: 2026-09-10

Consumer: the healthy-`CompactLog`, selected-detector, same-owner B5/P2
readback `G8SameOwnerReadbackData`.

The literal finite-cutoff metric sandwich in the positive physical endpoint
is now formally rewritten through the exact finite Euler decomposition

```text
metricCoframe = upperFactor • (survivor + boundarySum).
```

The equality remains inside the same `C_n† (·)† W_g (·) C_n` Gram, with the
original selected owner, cutoff, scale, and finite family retained.  It is an
operator identity before trace; no uncut projection-response replacement is
made.

This isolates the next mathematical P1 obligation: identify the trace
contribution of the actual finite `boundarySum` against the selected finite
visible-prime scalar, with the survivor and internal terms explicitly left as
the canonical residual.  No such identification or `qw` conclusion is made
here.

Evidence: `ConnesWeilRH.Dev.C1G8P1MetricBoundary` and paired Audit completed
in `build-logs/1275_g8_p1_metric_boundary_retry4.log` (3924 jobs, zero
`error:` and `sorryAx`; only `[propext, Classical.choice, Quot.sound]`).
