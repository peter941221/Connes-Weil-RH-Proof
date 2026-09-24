# Record 1942: four-point n=2 physical quadratic

The span physical expansion is now specialized to the two-vector owner
`spanObj ![A, B] ![1, -lambda]`. For every prime-power index, and therefore
for `n = 2`, the signed profile term is the exact quadratic in `lambda` whose
four coefficients are the real parts of the four pair physical integrals
`AA`, `AB`, `BA`, and `BB`.

The formal declaration is
`signedProfileTerm_twoSpan_eq_four_pair_physical_integrals` in
`C1P2SpanProfileMatrix.lean`. It is an exact identity only; no coefficient
sign is assumed.

Verification: `20260924_span_physical5.log`, 3789 jobs, zero errors; the
paired audit reports only `[propext, Classical.choice, Quot.sound]` and no
`sorryAx`.

The next quantitative target is now the strict signed inequality for this
four-channel quadratic at the vertex coefficient already supplied by the
four-point gate certificate.
