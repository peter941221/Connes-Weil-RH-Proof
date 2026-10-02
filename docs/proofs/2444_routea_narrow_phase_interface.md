# Record 2444: Route A narrow phase rectangle interface

## Scope

The Route A phase evaluator already produces endpoint bounds for `cos t` and
`sin t`. This record adds the Lean interface that turns those four inequalities
into membership of the corresponding complex rectangle for
`exp (t * I)`.

The earlier `phaseRect2441` result remains the broad analytic fallback
`[-1,1] + i[-1,1]`. Record 2444 does not certify the evaluator's endpoint
numbers; it consumes those endpoint inequalities as explicit hypotheses.

## Verified surface

- `phaseRectOfBounds2444` packages `(cLo,cHi,sLo,sHi)` as a rectangle.
- `phase_mem_of_sin_cos_bounds2444` proves phase membership from the four
  endpoint inequalities.
- The audit prints the theorem axioms; no numeric data or new axiom is added.

## Remaining bridge

The MPFR evaluator must still export certified endpoint inequalities in the
owner's exact convention, and those inequalities must be imported or replayed
without replacing them by sampled or float-only evidence.
