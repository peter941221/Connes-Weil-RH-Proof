# 1649 — The bare coupled remainder has zero real trace

The existing source facts give the coupled second-support/prolate remainder
both of the required structural properties:

- `sourceSecondSupportProlateRemainder_adjoint_eq_neg`;
- `sourceSecondSupportProlateRemainder_isTraceClassAlong` when the concrete
  boundary factor data are supplied.

The new theorem
`sourceSecondSupportProlateRemainder_trace_re_eq_zero` combines only the
skew-adjoint identity with the general named-basis trace-adjoint identity. It
therefore needs no hidden trace-class premise: the diagonal `tsum` identity
already implies `-re(trace) = re(trace)`, hence the real part is zero.

This sharpens the live target. The unresolved real contribution is not the
bare coupled remainder; it is the remainder after the noncommuting renewal
translation and source-band/prefix sandwich. That Hermitian response still
needs a same-owner estimate or positivity producer. The focused build
completed with zero `error:` lines and zero `sorryAx`; the Audit leaf reports
only `[propext, Classical.choice, Quot.sound]`.

No RH conclusion is claimed.
