# 1813 — C3' parity-compatible odd negative diagonal

Date: 2026-09-22

The theorem `odd_ICgate_neg_of_narrow_budget` proves
`ICgate g.convolutionSquare < 0` from oddness, a square support interval
`(-R,R)` with `R < log 2`, the strict narrow Archimedean budget, and positive
square mass. The Archimedean term is strictly negative and the visible-prime
sum vanishes on the same owner.

The oddness field makes this certificate directly usable as the negative
diagonal input of the even/odd gate consumer. It does not establish the three
node equations, detector detection, or the selected orbit owner's support and
signed budget. Round 2 therefore remains open.

Verification: `/home/peter/rh/build-logs/1813_odd_negative.log`; focused build
completed successfully in 3810 jobs, with no `error:` or `sorryAx`. The audit
uses only `propext`, `Classical.choice`, and `Quot.sound`.
