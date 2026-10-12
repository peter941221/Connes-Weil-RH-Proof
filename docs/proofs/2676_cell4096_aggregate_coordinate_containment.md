# Record 2676 - cell 4096 aggregate-coordinate containment

Verdict: SCREEN PASS AND LEAN FINITE-SUM BRIDGE GREEN; familywise continuum containment remains open.

The record-2676 screen recomputes the four channel aggregates for cell 4096 of
the 8192-cell repaired-owner partition using the committed owner inputs. Each
aggregate coordinate is rounded outward to an exact rational with denominator
2^160. The screen then checks that these four dyadic aggregate rectangles lie
inside the corresponding record-2675 exported rectangles. The closest margin
is the upper imaginary coordinate of `correction_M0`, at approximately 4.0716
binary64 ulps. The complete exact inputs and margins are recorded in
`results/2676_cell4096_containment_screen.json`.

`C1RouteACellContainment2676Aggregates.lean` now also defines all 120
per-family rectangles, proves each of the four finite rectangle sums equals
the corresponding aggregate rectangle, and supplies four whole-cell
conditional consumers. The family rectangles are rounded outward to exact
160-bit dyadics before summation. `C1RouteACellContainment2676AggregatesAudit.lean`
audits the coordinate, finite-sum, and consumer theorems; all use exactly
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. Both modules
compile with Lean/Mathlib v4.30 in the Linux build workspace.

The new consumers still take per-family containment as an explicit premise:
for every position in `Icc 0 record2675CellRight`, each generated rectangle
must contain the corresponding continuous family value. The Lean bridge does
not yet prove those 120 premises, and it does not connect the generated
binary64 midpoint coefficients to the live owner. Consequently it does not
yet discharge record 2675's load-bearing continuum-containment premise or its
conditional integral bound.
The 8192-cell Lean sum, live-owner `chargeRest` identity, signed infinite-xi
tail, Producer GO, SourceRH, and RH remain open.
