# Proof 574: raw physical old-carrier reduction

## Result

`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction.lean` makes the
first concrete reduction for the remaining physical producer.

Let `F` be the actual old suffix frame.  The packed physical analysis is
written as

```text
physicalAnalysis = W * F
```

where `W` is the genuine finite-S old-carrier map with the two coordinates

```text
adjoint(ambientLossFactor)
adjoint(boundary) = (I - newFrame * newFrame†) * transport†
```

The second equality is obtained from the actual rectangular adjoint field.
It is not an oblique similarity or a guessed projection formula.

The raw four-term row is also written as

```text
rawRow = R0 * F
R0 = rawRow * oldFrame†.
```

This uses only `oldFrame† * oldFrame = I` and preserves the signed raw row.

## New Lean interfaces

The source module defines:

```text
suffixEulerFrameAmbientBoundaryOldCarrierAnalysis
suffixActualBandRawPhysicalReducedRow
SuffixRawOldCarrierDomination
```

It proves the exact analysis and raw-row factorizations, and proves that a full
all-vector Douglas estimate for `R0` through `W` constructs the original
packed physical readout with the same bound.

This is a sufficient lower-level producer interface.  The estimate itself is
not proved.  In particular, boundedness of `rawRow` or injectivity of the
ambient loss column does not imply `SuffixRawOldCarrierDomination`.

## Boundary

The remaining source theorem is now an old-carrier, same-object inequality:

```text
||R0 y||^2 <= C^2 ||W y||^2
```

for every old-carrier vector `y`, with `C` uniform in `p` and `S`.
The existing Proof 573 residual energy estimate does not supply this
lower-bound/Douglas estimate.

No Gate 3U, finite-S sign, Burnol identity, or RH theorem is claimed.

## Verification

Verification was run in an Ubuntu-24.04 WSL2 ext4 mirror after copying from
the Windows source of truth:

```text
CCM25Concrete aggregate: 3843 jobs, PASS
574 axiom audit: PASS
  [propext, Classical.choice, Quot.sound]
```

The target module was rebuilt as part of the aggregate.  The audit reports
only

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, or user axiom was added.  The WSL localhost-proxy warning
and existing repository linter warnings are environmental or pre-existing.
