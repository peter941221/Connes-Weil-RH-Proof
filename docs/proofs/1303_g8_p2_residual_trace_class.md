# G8 P2 residual trace-class specialization

The import-facing leaf `C1G8P2CanonicalResidual` now proves
`g8VisibleEulerResidual_isTraceClassAlong`. The theorem keeps the same
healthy `CompactLog` owner, support interval, named Hilbert basis, and
per-prime-power `GlobalPrimePowerTraceBasisData`; its only analytic input is
the already explicit trace-class witness for the fixed G8 projection response.
It is a direct specialization of `sameObjectResidual_isTraceClassAlong`, so
no scalar counterterm or owner change is introduced.

This is FORMAL P2 interface evidence: green build
`1419_g8_p2_residual_trace_class.log`, 3301 jobs, zero `error:`/`sorryAx`, and
only `[propext, Classical.choice, Quot.sound]` in the paired audit. It does
not prove residual convergence, the P2 sign, or the P1 metric-to-radial
transport needed to construct the required readback witness.
