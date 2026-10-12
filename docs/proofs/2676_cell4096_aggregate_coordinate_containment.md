# Record 2676 - cell 4096 aggregate-coordinate containment

Verdict: SCREEN PASS AND LEAN COORDINATE BRIDGE GREEN; familywise continuum containment remains open.

The record-2676 screen recomputes the four channel aggregates for cell 4096 of
the 8192-cell repaired-owner partition using the committed owner inputs. Each
aggregate coordinate is rounded outward to an exact rational with denominator
2^160. The screen then checks that these four dyadic aggregate rectangles lie
inside the corresponding record-2675 exported rectangles. The closest margin
is the upper imaginary coordinate of `correction_M0`, at approximately 4.0716
binary64 ulps. The complete exact inputs and margins are recorded in
`results/2676_cell4096_containment_screen.json`.

`C1RouteACellContainment2676Aggregates.lean` defines the rational dyadic
coordinates and proves the four coordinate-subset statements by `norm_num`.
`C1RouteACellContainment2676AggregatesAudit.lean` audits each statement; all
four use exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
Both modules compile with Lean/Mathlib v4.30 in the Linux build workspace.

The Lean theorems establish only arithmetic facts about the four stored
aggregate rectangles. They do not prove that the rectangles enclose the sum
of all 30 family rectangles, nor that any per-family rectangle contains the
actual continuous function. Consequently they do not discharge record 2675's
load-bearing continuum-containment premise or its conditional integral bound.
The 8192-cell Lean sum, live-owner `chargeRest` identity, signed infinite-xi
tail, Producer GO, SourceRH, and RH remain open.
