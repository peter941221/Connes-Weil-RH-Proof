# Proof 490: Raw completed lower-factor gauge owner

Date: 2026-07-22

## Result

The result is structurally good, but it does not close Gate 3U.  The raw
actual-band remainder now has an exact paired lower-factor gauge owner with no
external inverse lower-factor square in the operator identity.

```text
lowerFactorGaugedCompletedResponse(S)
  =sourceActualBandFiniteEulerRemainderResponse(S)
  =actualBandCompletedRelativeResponse(S).
```

For the family selected by the compact Weil square,

```text
canonicalLowerFactorGaugedCompletedResponse
  =canonicalActualBandCompletedRelativeResponse.
```

The source and audit are:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSRawCompletedGaugeOwner.lean

ConnesWeilRH/Dev/
  CCM24FiniteSRawCompletedGaugeOwnerAudit.lean
```

## What the gauge is

Let

```text
c_S=finiteEulerLowerFactor(S)>0.
```

The completed numerator and inverse Gram covariance are changed together:

```text
N_S        ->(conj(c_S)c_S) N_S,
Gamma_S^-1 ->(conj(c_S)c_S)^-1 Gamma_S^-1.
```

Their product is therefore unchanged.  Lean specializes the generic scalar
gauge from Proof 443 and proves

```text
gaugedNumerator(S)=conj(c_S)c_S * completedNumerator(S),

gaugedNumerator(S) * gaugedGammaInv(S)
  =actualBandQuadraticCycledResponse(S).
```

Proof 441 then identifies that quadratic cycle with the actual source
remainder.  The equality is on the genuine source Sonin carrier; it is not a
finite-dimensional trace cycle.

## Why this differs from Proof 489

Proof 489 starts from the separately normalized endpoint:

```text
normalized endpoint=c_S^2 * raw endpoint.
```

Reading the raw endpoint back from that equation exposes `c_S^-2`.  Proof 490
does not divide this normalized estimate.  It puts `c_S^2` in the completed
numerator and the matching inverse in the same owner, where they cancel before
any norm or trace is taken.

This changes the correct object to estimate, but it does not itself provide an
estimate.  Bounding the gauged numerator and gauged inverse separately would
recreate the same condition-number loss and is forbidden.

## Trace legality and axioms

The fixed-family trace-class theorem for the actual source remainder transfers
to the gauged owner by exact equality.  No new trace premise is introduced.

All ten audited declarations use exactly

```text
[propext, Classical.choice, Quot.sound].
```

The final verification batch is:

```text
+--------------------------------------+-------+--------+
| target                               | jobs  | result |
+--------------------------------------+-------+--------+
| Proof 490/491 focused audits         |  3275 | PASS   |
| CCM25Concrete aggregate              |  3765 | PASS   |
| full repository                      |  3846 | PASS   |
+--------------------------------------+-------+--------+
```

## Boundary

The inverse lower-factor square has been removed from the exact owner, not from
a proved uniform inequality.  The next analytic producer must estimate the
ordinary trace of this complete paired owner while retaining compact root
support before the first absolute value.  Gate 3U, the finite-S sign,
negative-owner integration, Burnol's identity, and RH remain open.
