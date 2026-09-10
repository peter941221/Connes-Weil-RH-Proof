# G8 P1 ordinary trace projection-defect ledger

Date: 2026-09-11.

The import-facing leaf `C1G8P1MetricProjectionDefectTraceLedger` transports
the exact operator ledger to the named source-basis ordinary trace. Using the
explicit trace-class owners for the metric term and all three projection-defect
channels, it proves that the raw G8 cutoff trace equals the metric trace plus
the three defect traces. This is a legal finite-cutoff trace identity on one
owner; it supplies neither a defect sign nor a cutoff limit.

Evidence: `1514_g8_p1_projection_defect_trace_ledger.log`, owning and audit
targets green (3929 jobs), zero `error:`/`sorryAx`; the audited declaration
uses exactly `[propext, Classical.choice, Quot.sound]`.

No metric-to-radial transport, endpoint production, P2 remainder/sign, or P3
positivity conclusion is asserted. RH is not claimed.
