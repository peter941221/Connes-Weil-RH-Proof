# 3080 - Route A same-owner joint-symbol data

Date: 2026-10-20

Status: `POINTWISE SYMBOL AND FINITE NEGATIVE BAND PROVED; WEIL INTEGRAL READBACK AND SIGN BALANCE OPEN`.

## Formalized owner data

`C1RouteAJointSymbolData3080.lean` defines the joint symbol from one actual
`OrbitG8Geometry`. Its prime set is the prime part of that geometry's
support-derived visible-prime range; its transform starts from the exact raw
orbit factor; and the archimedean term uses the existing `c3Sigma` owner.

The new Lean results establish:

- the raw orbit transform at `1/2 + i*xi` equals the selected half-density
  source transform at `i*xi`, so the frequency coordinate shift is explicit;
- each prime Poisson multiplier is bounded in absolute value by
  `2*r/(1-r)`, where `r = 1/sqrt(p)`;
- summing those bounds gives an owner-specific bound for the whole prime
  symbol, without changing that geometry's prime set;
- the frequency energy density equals its pointwise positive credit minus
  negative deficit;
- `c3Sigma` eventually falls below any fixed finite prime allowance, so the
  joint symbol is nonnegative outside an owner-specific bounded interval;
- therefore the negative-sign band of that joint symbol is bounded.

These are pointwise and coordinate results. They do not prove that `qw` equals
the integral of this density. They also do not prove that integrated positive
credit dominates negative deficit. The current prime allowance uses an
absolute sum, so it is useful for locating the negative band but cannot serve
as the cancellation-sensitive sign supplier.

## Next mathematical gate

Prove the exact full-line identity between the selected owner's Weil value
and the integral of the joint frequency density, with the Fourier
normalization, archimedean multiplier, complete prime-power owner, and
integrability all checked in Lean. Then prove the finite-band credit lower
bound needed to dominate the complete deficit using both the actual
interpolation values and `OrbitG8Geometry.raw_square_tail`. The far-tail
pointwise symbol result is only a band-location input; it is not positive
credit.

Route B remains dormant because this Route A mechanism has not reached a
scoped no-go. No RH theorem, `SourceRH`, or producer closure follows from
record 3080.

## Verification

Linux ext4 Lean 4.30 build passed for the module and its audit. The audited
declarations use exactly `[propext, Classical.choice, Quot.sound]`. No
`sorry`, `admit`, or `sorryAx` was introduced.
