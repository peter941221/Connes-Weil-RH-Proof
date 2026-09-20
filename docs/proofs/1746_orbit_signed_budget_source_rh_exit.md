# 1746 - Orbit signed budget to SourceRH exit

Date: 2026-09-20.

Status: FORMAL consumer closure; the producer inequality remains open.

The exact B5 quantifier is now wired in Lean. If, for every hypothetical
right-hand off-line zero `rho`, there exist a test `g`, an
`OrbitG8Geometry rho g`, healthy detector data for the same `g`, and

`archimedeanTerm + signedProfileCredit <= signedProfileDeficit`

on that geometry's actual finite visible-prime range, then the existing
healthy-owner contradiction yields `SourceRH`.

This theorem does not prove the signed budget. It removes the remaining
consumer ambiguity: future work must supply that one same-owner inequality,
not a universal positivity theorem, a normalized carrier, or a separate
detector. The theorem is
`sourceRH_of_right_orbitGeometry_signedBudget` in
`C1P2SignedBudget.lean`.

Evidence: paired Audit and
`build-logs/shortest_route_20260920_signed_budget_exit_v2.log`, which reports
3783 successful jobs, zero `error:` lines, zero `sorryAx`, and only
`propext`, `Classical.choice`, and `Quot.sound`.
