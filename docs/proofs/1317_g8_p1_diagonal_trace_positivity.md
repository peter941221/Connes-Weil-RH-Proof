# G8 P1 diagonal metric-channel trace positivity

Date: 2026-09-11.

The diagonal-channel positivity leaf now pushes operator positivity through
the named source-basis ordinary trace. For every literal cutoff and either
metric coframe leg, the self-channel trace has nonnegative real part. The
proof uses the existing same-owner Hilbert--Schmidt trace-class owner and the
adjoint-conjugation positivity; it does not alter the mixed-channel ledger.

Evidence: `1518_g8_p1_diagonal_trace_positive.log`, owning and audit targets
green (3926 jobs), zero `error:`/`sorryAx`; audited declarations use exactly
`[propext, Classical.choice, Quot.sound]`.

Mixed-channel signs, projection-defect control, metric-to-radial transport,
endpoint production, P2 remainder/sign, and P3 positivity remain open. RH is
not claimed.
