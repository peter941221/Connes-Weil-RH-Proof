# 2293 — Grouped centered derivative and flat-endpoint preflight

Date: 2026-09-30.

Status: repaired derivative-method preflight on the captured stored owner. This
is not a directed-MPFR integral certificate or an `hgap` supplier. The previous
2292 no-go is withdrawn because its support handling, derivative numerators, and
complex modulus extraction were wrong.

The owner has 30 families with physical radius `R = width^2`. Inside support,
`q = 1 - x^2/R^2` and the amplitude is
`exp(-30/q + (0.5 + i theta) x)`; outside support it is exactly zero.
The program uses grouped complex Taylor jets through order six. It bounds the
fifth derivative at the cell centre with a sixth-derivative variation term and
uses a separate flat-extension envelope for cells crossing support endpoints.

The five Lobatto nodes are `-1, -1/sqrt(2), 0, 1/sqrt(2), 1`. Their monic node
product has exact reference integral `1/8` after splitting at its roots. The
artifact therefore reports an interpolation-only proxy with panel length and
node-product factors. It does not include rounded node values, moment errors,
functional propagation, or the infinite xi tail.

```text
+----------+----------------+-------------------+---------------------+
| subcells | base centered  | correction direct | correction centered |
+----------+----------------+-------------------+---------------------+
| 8        | 4.19007136e4   | 2.21059430e7      | 2.21059430e7        |
| 16       | 3.08858208e4   | 1.22115871e7      | 9.01468749e6        |
| 32       | 2.02183024e4   | 6.49384066e6      | 2.39897951e6        |
+----------+----------------+-------------------+---------------------+
```

The 32-subcell correction center/variation price is 2.71x tighter than the
same-run direct interval price. These values are transform-interpolation
prices, not charges for the kernel-weighted hgap functional; comparing them
directly with the `1e7` hgap budget would mix different objects.

The run command is:

`python3 scripts/routea_grouped_centered_derivative_preflight_2293.py --ladder 8,16,32`

The run artifact keeps all ladder readings. The canonical top-level result is
the 32-subcell reading. The selftest command is:

`python3 scripts/routea_grouped_centered_derivative_selftest_2293.py`

It passes 19 tests, including independent 100-digit fifth/sixth differentiation,
both signs, grouped stored coefficients, support endpoints, centred variation,
complex modulus, and the exact Lobatto integral. These controls validate the
implementation but do not replace a directed-rounding theorem.

```text
stored owner -> grouped derivative enclosure -> interpolation proxy
                                                |
                         actual functional propagation + node/moment error
                                                |
                              finite-window quadrature certificate
                                                |
                              independent infinite-xi tail bound
                                                |
                              same-owner hgap supplier: OPEN
```

The next mathematical step is to propagate this transform error through
`K(xi) |P(xi)|^2 |base(xi)|^2 |corr(xi)|^2`, preserve signed cancellation, and
then separately certify the finite window and the infinite tail. The 41136
support-derived prime-power readback is still required. No producer GO, SourceRH,
or RH conclusion follows.

Evidence: `scripts/routea_grouped_centered_derivative_preflight_2293.py`,
`scripts/routea_grouped_centered_derivative_selftest_2293.py`, and
`results/2293_grouped_centered_derivative_preflight.json`.