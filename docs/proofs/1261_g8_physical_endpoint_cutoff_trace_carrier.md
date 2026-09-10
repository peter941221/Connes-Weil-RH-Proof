# G8 physical endpoint finite-cutoff trace carrier

Date: 2026-09-10

The positive physical endpoint Gram from records 1259–1260 is now inserted
into a source-level finite-window pair.  Its left leg is the adjoint source
inclusion applied to the existing G8 window leg, and its middle operator is
`g8PhysicalEndpointGram`.  Lean proves the exact trace-product expansion,
trace-classness, positivity, and nonnegative real ordinary trace for every
finite cutoff.

Formal declarations: `g8PhysicalEndpointSourceCutoffPairData`,
`g8PhysicalEndpointSourceCutoffPairData_traceProduct_eq`,
`g8PhysicalEndpointSourceCutoffPairData_traceProduct_isTraceClassAlong`,
`g8PhysicalEndpointSourceCutoffPairData_traceProduct_isPositive`, and
`g8PhysicalEndpointSourceCutoffPairData_trace_re_nonnegative` in
`ConnesWeilRH.Dev.C1G8AdjointShearGram`.

Evidence: `1261_physical_endpoint_cutoff_main.log` and
`1261_physical_endpoint_cutoff_audit.log`; the builds completed successfully
(3921/3922 jobs), with zero `error:` and zero `sorryAx` lines.  The focused
audit reports exactly `[propext, Classical.choice, Quot.sound]`.

This closes only the finite-cutoff operator carrier.  No cutoff convergence,
finite-visible-prime identity, `qw` readback, or RH conclusion follows yet.
