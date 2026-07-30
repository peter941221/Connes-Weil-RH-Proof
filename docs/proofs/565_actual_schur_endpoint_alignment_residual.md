# Proof 565: Actual Schur Endpoint Alignment Residual

## Result

Proof 553 and Proof 564 use two endpoint layers with different carriers:

```text
Proof 553: literal suffix-list coframes
Proof 564: FinitePrimePowerFamily endpoint coframes
```

For a family `family`, the new module proves the visible-prime bridges:

```text
suffix coframe family.visiblePrimes = family coframe
suffix metric coframe family.visiblePrimes = family metric coframe
suffix named Schur endpoint family.visiblePrimes
  = family source-forward Schur endpoint
```

The physical endpoint therefore has the exact source/suffix readback

```text
physical endpoint
  = suffix named Schur endpoint
    + transport residual.
```

The actual Schur endpoint is then written against the same named suffix
endpoint by defining the signed alignment residual

```text
alignment residual
  = transport residual - physical/actual-Schur endpoint residual.
```

and proving

```text
actual Schur endpoint
  = suffix named Schur endpoint + alignment residual.
```

## What This Closes

This removes an endpoint naming/carrier mismatch between the Proof 553
raw-row ledger and the Proof 564 actual-Schur endpoint ledger. The theorem is
an exact continuous-linear-map identity, proved by visible-prime expansion and
additive-group algebra.

## What This Does Not Close

The alignment residual is not proved to vanish, to have a sign, or to admit a
bound uniform in the visible-prime family. It is not a Douglas factor and it
does not provide Gate 3U:

```text
||gap(p,S)† x||² <= C² ||leftCoDefect(p,S) x||².
```

Approximate kernels, the uniform non-polar gap estimate, the finite-S sign,
Burnol's identity, and `_root_.RiemannHypothesis` remain open.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurEndpointAlignmentResidual.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurEndpointAlignmentResidualAudit.lean
ConnesWeilRH/Source/CCM25Concrete.lean
```

The audit is intended to report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

for each declaration. No residual-zero or Gate 3U claim is introduced.
