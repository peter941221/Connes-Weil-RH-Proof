# 1812 — C3' negative diagonal certificate

Date: 2026-09-22

## Result

The theorem
`tripleVanishingRoot_ICgate_neg_of_narrow_base_of_laplaceAt_two_ne_zero`
proves a strict negative complete gate for the D3 triple-vanishing root of a
narrowly supported `CompactLogTest` whose Laplace value at `2` is nonzero.

The proof combines the strict negative Archimedean term from `C1LaneRStrictness`
with the public `C1LaneRD3Root` support theorem, which places the convolution
square inside the open log-2 window, so the finite visible-prime sum vanishes.

This is a negative diagonal candidate only. It does not prove a mixed
cross-gate estimate, or compatibility with the selected healthy orbit
detector's detection data. Round 2 therefore remains open.

## Verification

Focused build: `ConnesWeilRH.Dev.C1P2NegativeDiagonalCertificate` and its
paired `...Audit` module. Evidence:
`/home/peter/rh/build-logs/1812_negative_diagonal_final.log`.
The log reports `Build completed successfully (3650 jobs)`, no `error:` or
`sorryAx`, and the audit prints exactly `propext`, `Classical.choice`, and
`Quot.sound`.
