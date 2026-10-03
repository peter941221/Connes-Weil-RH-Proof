# Record 2518: production exponential table bridge

`C1RouteAExpProductionTableBridge2518.lean` exports the 2516 production
remainder through an abstract 640-cell table.  Its only analytic premise is
the explicit per-cell inequality from the 2516 remainder term to the table
entry; the proof uses the nonnegative factor `step^3 / 12` and finite-sum
monotonicity.  The table is intentionally not populated from the external
2517 floating-point price.

The Lean audit passed with the standard axiom trio only.  This is a producer-
facing interface, not a completed margin or RH result.
