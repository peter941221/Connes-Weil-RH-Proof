# G8 P2 completed-residual prefix limit

The import-facing leaf `C1G8P2CanonicalResidual` specializes the existing
endpoint arithmetic-prefix limit to
`g8CanonicalFamily owner`.  The theorem
`tendsto_g8CompletedResidualPrefix_eq_routeTrace_sub_selectedSupport` proves
that the completed residual prefix converges, along the same named global
basis, to

`ordinaryTraceAlong routeTrace - selected owner finitePrimeTerm sum`.

The support sum is the exact canonical nonzero prime-power support, obtained
by the P1 family readback; no unrelated family or scalar counterterm is
introduced.

This is FORMAL same-owner P2 endpoint-limit evidence.  Owning and paired
audit build `1444_g8_p2_residual_prefix_limit.log` completed successfully
with 3827 jobs, zero `error:`/`sorryAx`, and only
`[propext, Classical.choice, Quot.sound]` in the audit.  The theorem is a
prefix trace limit, not yet the analytic assertion that the G8 remainder
itself tends to zero or has the required sign; metric-to-radial transport and
the P3 producer remain open.
