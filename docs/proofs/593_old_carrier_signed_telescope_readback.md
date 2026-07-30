# Proof 593: old-carrier signed telescope readback

## Result

The reduced old-carrier row is now named as one signed operator:

```text
R0(p,S)
  = Z_S * T(p,S)^dagger * oldFrame(p,S)^dagger
    - T(p,S)^dagger * Z_(p::S) * oldFrame(p,S)^dagger,
```

where `Z_S` is the complete boundary moment.  The same operator has the
response-level readback

```text
R0(p,S)
  = R_S^dagger * T(p,S)^dagger * oldFrame(p,S)^dagger
    - T(p,S)^dagger * R_(p::S)^dagger * oldFrame(p,S)^dagger.
```

The row also annihilates the orthogonal complement of the old-frame range:

```text
R0(p,S) * (I - oldFrame * oldFrame^dagger) = 0.
```

This is an exact carrier readback.  It keeps the adjacent moments in one
signed telescope and does not estimate the two terms separately.

```text
 +-------------------------------+
 | old-carrier input y           |
 +---------------+---------------+
                 |
                 v
 +-------------------------------+
 | oldFrame(p,S)^dagger y        |
 +---------------+---------------+
                 |
                 v
 +-------------------------------+
 | Z_S T^dagger - T^dagger Z_pS |
 | one signed synchronized gap   |
 +---------------+---------------+
                 |
                 v
 +-------------------------------+
 | reduced raw row R0(p,S)y     |
 +-------------------------------+
```

## Boundary

The readback does not provide the missing uniform quotient through the old
carrier analysis `W`.  The remaining source theorem must still show that this
single synchronized difference is bounded by the two-channel energy of `W`,
or equivalently by the adjacent Julia left co-defect.  In particular, the
readback does not license separate norm estimates for `Z_S` and `Z_(p::S)`.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescope.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSignedTelescopeAudit.lean
```

The audit is expected to use only
`[propext, Classical.choice, Quot.sound]`.
