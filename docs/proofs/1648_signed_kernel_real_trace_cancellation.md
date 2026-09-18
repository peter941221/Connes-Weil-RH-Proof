# 1648 — The signed compact-root trace has zero real part

The signed compact-root operator is formally skew-adjoint:
`sourceCompactRootSignedKernelOperator_adjoint_eq_neg`.  Combining this with
the named-basis identity
`ordinaryTraceAlong_adjoint` gives the exact theorem
`sourceCompactRootSignedKernelOperator_trace_re_eq_zero`.

More explicitly, if `T` is the signed compact-root operator, then its trace
identity reads `-re(trace T) = re(trace T)`, hence `re(trace T) = 0`.
The paired Audit leaf reports only the standard axioms
`[propext, Classical.choice, Quot.sound]`; the focused build completed with
zero `error:` lines and zero `sorryAx`.

This is a genuine cancellation result, not the required positivity theorem.
It removes the skew compact-root contribution from the real part of the
aggregate.  The coupled second-support/prolate remainder and its renewal
weights still require a same-owner nonnegative-sign producer before the G8
consumer can yield `SourceRH`.

No RH conclusion is claimed.
