# Proof 582: one-prime boundary-moment norm bound

## Result

The exact signed boundary moment is

```text
M(F,E) = E† (I - R_0) D J + J† D F,
```

where `F` is the forward coframe, `E` is the endpoint coframe, `D` is the
selected detector, and `J` is the source inclusion.  The new generic norm
ledger keeps this sum intact and bounds it only after the two coframes have
been scaled together.

For every finite prime-power family, with

```text
rho_S = product_{p in S} (1 - a_p)/(1 + a_p),
```

the existing forward contraction and mixed metric contraction give

```text
||rho_S M(F_S,E_S)|| <= 3 ||D||.
```

For a family whose visible-prime list is exactly `[p]`, the elementary bound
`rho_p >= 1/8` gives the concrete unscaled estimate

```text
||M(F_p,E_p)|| <= 24 ||D||.
```

The Lean owners are:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentNorm.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentNormAudit.lean
```

## What this closes

This is the first actual operator-norm estimate for the one-prime moment on
the source-side coframe.  It uses the exact mixed normalization already
proved for the metric coframe, rather than treating the raw metric coframe as
contractive.

```text
forward norm <= 1
        |
        +-- rho_S * metric norm <= 1
        |
        v
rho_S * endpoint norm <= 2
        |
        +-- moment telescope: endpoint branch + forward branch
        v
rho_S * moment norm <= 3 * detector norm
        |
        +-- one-prime rho_p >= 1/8
        v
moment norm <= 24 * detector norm
```

## Remaining boundary

This is not the old-carrier Douglas estimate.  It does not prove a bounded
operator `Q` satisfying

```text
Q * W = suffixActualBandRawPhysicalReducedRow.
```

It also does not identify the moment with `Z * (W† W)`.  The old-carrier
quotient, any Douglas residual, Gate 3U, the finite-S sign, Burnol's identity,
and RH remain open.  The transition skew, right co-defect, endpoint residual,
and raw physical residual remain separate objects.

## Verification target

The source and audit must be built in the Ubuntu-24.04 WSL2 ext4 mirror, then
the `CCM25Concrete` aggregate and full repository must be rebuilt.  The audit
must report only

```text
[propext, Classical.choice, Quot.sound]
```

for all four new declarations.
