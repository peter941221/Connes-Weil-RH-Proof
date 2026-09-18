# 1643 — Source-compressed root norm bridge

Date: 2026-09-18.

## Result

The direct S3 operator is

```text
J† C J : sourceSoninCarrier -> sourceSoninCarrier,
```

where `J` is the source inclusion and `C` is the selected root convolution.
The new Lean theorems prove, pointwise,

```text
||J† C J u|| = ||P C J u||,
```

with `P = J J†` the actual Sonin projection. Consequently, for every named
source Hilbert basis, square-summability of the columns of `J† C J` is exactly
square-summability of the projected-root columns `P C J`.

## Significance

This is a norm/readback bridge, not an energy estimate. It removes an
artificial distinction between the direct-kernel S3 target and the existing
Hardy/Sonin-corner target. The remaining mathematical obligation is therefore
the square-sum for the projected root itself. The prolate remainder terms in
the Hardy-corner decomposition are already covered by existing Hilbert--
Schmidt interfaces; the central Hardy corner remains open.

No RH conclusion is claimed. The paired audit builds with only
`[propext, Classical.choice, Quot.sound]`.

## Evidence

- `ConnesWeilRH/Dev/C1G8R3SourceCompressedRootKernel.lean`
- `ConnesWeilRH/Dev/C1G8R3SourceCompressedRootKernelAudit.lean`
- Build log: `build-logs/1643_source_kernel_bridge_retry.log`
