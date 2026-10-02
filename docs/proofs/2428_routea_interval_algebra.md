# 2428 — Route A interval algebra interface

Date: 2026-10-02.

`ConnesWeilRH/Dev/C1RouteAIntervalAlgebra.lean` introduces an axis-aligned
complex rectangle and proves two purely algebraic facts:

* rectangles containing two complex terms contain the rectangle sum;
* pointwise rectangle containment for a finite family implies containment of
  the corresponding finite complex sum.

The file was compiled independently with Lean 4.30 and the current Mathlib
build.  Its hypotheses do not contain stored numerical conclusions.  The
companion audit file prints the theorem axioms.

This is an interface reduction, not a numeric import.  The remaining Route A
obligation is to prove, for the actual `correctedPhysical` summands, that the
directed `Kernel.eval_box` construction supplies the rectangle hypotheses.
The 2422/2423/2426 artifacts therefore remain interface controls only;
`lean_numeric_imported`, `producer_go`, and `rh_claim` remain false.
