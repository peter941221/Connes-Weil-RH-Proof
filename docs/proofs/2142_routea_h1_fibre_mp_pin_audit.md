# 2142 - High-precision pin audit of the null-fibre candidate

Date: 2026-09-28.

Status: PIN-STABILITY-PASS, signed producer gate still OPEN.

The audit reconstructs trial 162 from the committed 2141 seed and evaluates
its same double-precision coefficients with 80-digit arithmetic and
Gauss-Legendre windows. At 160 points per panel, one pin still has error
`6.56e-2`, but at 320 points per panel the maximum base pin error is
`2.43e-10` and the maximum correction pin error is `1.21e-10`. The 160-point
failure is therefore a quadrature-resolution failure, not evidence by itself
that the null-fibre coefficients violate the target constraints.

This does not certify the coefficient solve: the H1 Gram condition number is
`9.62e16`, the coefficients were generated in double precision, and no
interval error budget has been propagated. It also does not certify the
full-line signed integral or the complete closed-ball owner.

Decision: retain 2141 as a numerical candidate and proceed to high-precision
coefficient reconstruction plus interval gate pricing. Do not call this a
producer Go.

Evidence: `scripts/routea_overcomplete_h1_fibre_mp_pin_audit_2142.py` and
`results/2142_routea_h1_fibre_mp_pin_audit.json`.
