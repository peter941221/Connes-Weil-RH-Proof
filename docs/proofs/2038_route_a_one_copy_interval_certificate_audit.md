# 2038 — Route A one-copy interval-certificate audit

Date: 2026-09-27.

Status: scoped no-go for the current one-copy certificate attempt. Route A as
an entire mathematical idea remains open, but this selector does not pass the
producer gate. RH is not claimed.

## Target

The one-copy G8-H basis from record 2037 removes the two-copy affine-fibre
ambiguity. The remaining target is still stronger than a sampled negative
number:

```text
strict interval upper bound for the full-line grouped ICgate(g.square)
quadratic form < 0.
```

The bound must cover the actual support-derived visible-prime owner and the
whole xi line. A finite-grid value is not sufficient.

## Evidence

Record 2037 gives the following refinement pair on xi in [-40, 40]:

```text
one-copy, dxi = 0.008:  Q = -1.111095866723678e20
one-copy, dxi = 0.004:  Q = -1.1111917908404727e20
relative spread:          8.632083923682255e-5
raw H1 condition:         1.318248416390374e6
interpolation rank/nullity: 17 / 0
visible prime-power count: 1647
```

This is a stable floating-point candidate. It is not an interval enclosure.

## Certificate audit

The required chain has four unresolved links:

1. The source transform and H1-solved coefficients have no directed-rounding
   enclosure tied to the actual basis.
2. The signed prime-plus-archimedean kernel has no certified enclosure over
   every xi panel.
3. The finite-window quadrature error has no registered rigorous bound.
4. No full-line tail bound is registered for |xi| > 40.

Consequently the full-line value has no finite certified upper interval in the
current artifact set. The negative sampled integral therefore cannot imply the
strict producer premise.

## Decision

```text
A-DEAD-CURRENT-CERTIFICATE
```

Stop this selector. Do not add a Lean consumer, do not assemble a producer,
and do not expand gamma/rank/height. A new Route-A selector may reopen the lane
only after it supplies a named interval mechanism and a complete-owner,
parameter-uniform bound.

This is scoped to the current one-copy certificate attempt. It does not prove
that every future Route-A construction is impossible.

Evidence files:

- `results/2037_route_a_g8h_basis_comparison.json`
- `results/2038_route_a_one_copy_interval_certificate_audit.json`
- `scripts/routea_g8h_basis_comparison_2037.py`