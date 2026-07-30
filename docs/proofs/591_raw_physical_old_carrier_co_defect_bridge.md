# Proof 591: raw physical old-carrier co-defect bridge

## Result

The new bridge transfers a source-side right-factor contract through the
actual adjacent Julia left co-defect to the old-carrier analysis used by Bone
1.  For one visible-prime/suffix pair, the premise is

```text
rawDefect = leftCoDefect * rightFactor
||rightFactor|| <= C
```

and the conclusion is

```text
||R0 y||^2 <= C^2 ||W y||^2.
```

The proof keeps the signed raw row intact.  It uses the old-frame/complement
orthogonal split, the old-frame isometry, and the exact packed energy identity.
The complement contribution of the reduced row is zero, while the old-frame
part is the four-term row.  The factorization then bounds that row by the
actual left co-defect, and the packed energy bounds the co-defect by `W`.

```text
 +-------------------------------+
 | source right-factor contract  |
 | rawDefect = leftCoDefect F    |
 | ||F|| <= C                    |
 +---------------+---------------+
                 |
                 v
 +-------------------------------+
 | old-frame split                |
 | y = oldProjection y            |
 |   + oldComplement y            |
 | reduced row vanishes on        |
 | oldComplement y               |
 +---------------+---------------+
                 |
                 v
 +-------------------------------+
 | ||R0 y||^2 <= C^2 ||leftCoDefect
 | (oldFrame^dagger y)||^2       |
 +---------------+---------------+
                 |
                 v
 +-------------------------------+
 | ||leftCoDefect(...)||^2       |
 | <= ||W y||^2                  |
 +---------------+---------------+
                 |
                 v
 +-------------------------------+
 | ||R0 y||^2 <= C^2 ||W y||^2   |
 +-------------------------------+
```

## Boundary

This closes only the transfer from the explicit right-factor contract to the
old-carrier domination contract.  It does not construct the source-specific
factor, prove a uniform bound, prove Gate 3U, prove the finite-S sign, prove
Burnol's identity, or prove RH.  The factor contract remains the active Bone 1
producer obligation.

No spectral gap is used.  This matters because the existing approximate-kernel
results rule out a positive family-uniform spectral gap for the actual `W`.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoDefectBridge.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoDefectBridgeAudit.lean
```

The audited declarations use only
`[propext, Classical.choice, Quot.sound]`.

## Verification

Verification is run in the Ubuntu-24.04 WSL2 ext4 mirror after synchronizing
the Windows source of truth.  The module-level build passed before the
aggregate and full builds; the counts are recorded in the project build log.

The WSL localhost-proxy notice and existing repository linter warnings are
environmental or pre-existing.  No `sorry`, `admit`, or user axiom is added.
