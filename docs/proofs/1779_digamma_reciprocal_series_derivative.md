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

## Formal extension 1780

The same module now also proves the local-equality derivative transfer
`hasDerivAt_digamma_of_re_ge_quarter`, and the explicit telescoping estimate
`quarter_series_tsum_le_twenty`.  Together they give
`norm_digamma_deriv_le_twenty` on `Re z > 1/4`.

The tail comparison is exact: the first reciprocal-square term contributes
16, and every shifted tail term is bounded by the adjacent reciprocal
difference; that difference series telescopes to 4.

The owning module and paired audit both built successfully (3539 jobs) in
`/home/peter/rh/build-logs/digamma-bound-audit-v2.log`.  The audit remains
axiom-clean with no `sorryAx`.

## Boundary of the result

This closes Lemma C, but does not yet assemble the `W^{2,1}` kernel
certificate, prove the translation-tail identities, or prove S3
positivity/RH.  Those remain the live downstream obligations.
