# 1779 — Differentiated half-anchor reciprocal series

Date: 2026-09-21

## Result

The new declaration
`ConnesWeilRH.Dev.hasDerivAt_halfAnchorReciprocalSeries_of_re_ge_quarter`
proves that the half-anchor reciprocal series can be differentiated term by
term on the open half-plane `Re z > 1/4`.  Its derivative is the reciprocal
square series, and the derivative norms are dominated uniformly by
`(n + 1/4)^(-2)`, which is summable.

The proof uses Mathlib's preconnected-domain smooth-series theorem.  The
base-point summability comes from the existing half-anchor Gauss reciprocal
series theorem; the majorant is proved by comparison with the shifted p-series.

## Verification

Build log: `/home/peter/rh/build-logs/digamma-derivative-audit-v1.log`.

The owning module and paired audit both built successfully (3539 jobs).  The
audit reports exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx`
was reported.

## Boundary of the result

This closes only the differentiated reciprocal-series interface.  It does not
yet identify that series with `Complex.digamma`'s derivative, prove the sharp
numeric bound `ψ' ≤ 20`, assemble the `W^{2,1}` kernel certificate, or prove
S3 positivity/RH.  Those remain the live downstream obligations.
