# 2443 — Route A q bounds

Date: 2026-10-02.

Lean proves the analytic bounds for `q = 1-u²`: `q ≥ 0` when `|u| ≤ 1`,
`q > 0` when `|u| < 1`, and `q ≤ 1` globally.  These are the sign and range
facts needed before applying the profile exponential interval propagation.

The interval enclosure of a whole `u` box and its directed MPFR endpoint
values remain separate obligations.
