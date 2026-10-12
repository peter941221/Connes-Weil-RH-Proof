# Record 2681: repaired-owner base-D2 family-0 bridge

The cell-4096 base-D2 bridge now compiles for repaired binary64 family 0.
The proof derives the second-factor rectangle from the explicit log-derivative
formulas, then composes it with the already proved midpoint rectangle and the
repaired coefficient point.

The generator in `scripts/routea_cell4096_containment_2676.py` now mirrors the
Lean proof order: the D2 factor rectangle is rounded outward to the 160-bit
dyadic grid before the complex rectangle product is formed. The previous
screen multiplied by the unrounded factor and therefore omitted the staged
rounding allowance. The regenerated 2676 screen returned
`CELL4096_CONTAINMENT_SCREEN_PASS`.

Lean evidence:

- `C1RouteARepairedOwnerBaseD22681.lean` compiles with Lean 4.30.
- `C1RouteACellContainment2676Aggregates.lean` was regenerated and compiles.
- `C1RouteARepairedOwnerBaseD22681Audit.lean` audits the four bridge lemmas.
- The audited leaves contain no `sorryAx`; the expected foundational axioms are
  `propext`, `Classical.choice`, and `Quot.sound`.

Scope remains local. This closes one family bridge in cell 4096 for the base-D2
channel. The other 29 base-D2 family bridges, the other 8191 cells, the finite
sum consumer, `chargeRest`, the signed infinite tail, Producer GO, `SourceRH`,
and RH remain open.
