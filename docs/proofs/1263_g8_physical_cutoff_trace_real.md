# G8 physical cutoff trace is real

Date: 2026-09-10

For every finite cutoff, the physical-endpoint source trace product is
self-adjoint.  Using the ordinary-trace adjoint identity and taking imaginary
parts, Lean proves

`(ordinaryTraceAlong sourceBasis traceProduct).im = 0`.

Formal declaration: `g8PhysicalEndpointSourceCutoffPairData_trace_im_eq_zero`
in `ConnesWeilRH.Dev.C1G8AdjointShearGram`.

Evidence: `1263_physical_cutoff_trace_real_main.log` and
`1263_physical_cutoff_trace_real_audit.log`; both builds completed
successfully, with zero `error:` and zero `sorryAx` lines.  The focused audit
reports exactly `[propext, Classical.choice, Quot.sound]`.

This removes the need to take an ad hoc real part at the finite-cutoff stage.
It still does not identify the limit with the finite visible-prime ledger or
prove `0 ≤ qw`.
