# 1745 - Orbit signed credit-deficit budget

Date: 2026-09-20.

Status: FORMAL interface reduction; no positivity claim.

The selected healthy detector's finite visible-prime aggregate is now split
exactly into positive profile credit and negative profile deficit. For the
same `OrbitG8Geometry` owner, the semi-local gate is equivalent to
`archimedeanTerm + signedProfileCredit <= signedProfileDeficit`.

The decomposition uses `max 0 term - max 0 (-term)` term by term, so it does
not assume a pointwise sign and does not alter the detector or visible-prime
set. The remaining mathematical work is an actual lower bound on credit
relative to the archimedean term and deficit, with all three quantities on
the same finite range.

Evidence:

- `ConnesWeilRH/Dev/C1P2SignedBudget.lean`
- paired `C1P2SignedBudgetAudit.lean`
- `build-logs/shortest_route_20260920_signed_budget_v7.log`

The focused build completed successfully (3783 jobs), with zero `error:`
lines and zero `sorryAx`; the audited declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.

This is a formal reduction, not a sign supplier and not an RH proof. The
next shortest live attack is a same-owner estimate for this balance from the
selected orbit interpolation data. The pointwise profile route is closed by
record 1744, and the paper screen in 1738 shows that tail-only or frozen
prime shortcuts cannot supply this balance.
