# 2371 - Coordinate and panel remainder price

日期：2026-10-02。

The existing 2348 Lean theorem has the explicit remainder shape
`step² * (2*radius) * weightedCurvature / 12`. Record 2371 prices that term
alongside the symmetric coordinate charge from the outer-pin bridge, using the
stored owner coefficients, the 240001-node step, the 2366 displacement, and
the binding `sigma=-0.5`.

This is a decision-oriented price only. It uses stored floating operands via
high-precision mpmath and does not certify the pointwise interval bounds,
directed accumulation, or the producer import. The output is used to decide
whether the remaining panel/coordinate terms are numerically viable before
spending effort on their formal enclosure.

Status: `COORDINATE_AND_PANEL_REMAINDER_PRICE_NOT_CERTIFICATE`; producer GO:
`false`.
