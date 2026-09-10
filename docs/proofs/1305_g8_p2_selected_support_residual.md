# G8 P2 selected-support residual readback

The import-facing leaf `C1G8P2CanonicalResidual` now combines the canonical
same-owner family from P1 with the existing residual decomposition.  Its
theorem
`ordinaryTraceAlong_projectionResponse_eq_selectedSupport_sum_add_g8Residual`
states that the named-basis trace of the G8 projection response is exactly
the selected owner's finite-prime-term sum plus the same-owner
`ordinaryTraceAlong g8VisibleEulerResidual`.

The first summand is the exact canonical nonzero prime-power support of the
selected owner.  The residual is the same-owner trace-class object already
used by the P2 interface theorem.

This is FORMAL same-owner P2 identity/readback evidence.  Owning and paired
audit build `1438_g8_p2_selected_support_residual.log` completed successfully
with 3827 jobs, zero `error:`/`sorryAx`, and only
`[propext, Classical.choice, Quot.sound]` in the audit.  It does not prove
the residual limit or sign, the metric-to-radial transport/finite metric trace
identity, or the P3 contradiction producer.
