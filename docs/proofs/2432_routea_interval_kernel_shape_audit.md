# 2432 — Route A interval-kernel shape audit

Date: 2026-10-02.

The source audit checks that the current evaluator still has the exact shape
formalized by the Lean interval layer: `iprod` computes four lower-directed
and four upper-directed corner products, then takes three lower and three
upper hull steps; `ciprod` composes four real products with two directed
subtractions and two directed additions.

This is a structural source guard, not a proof of MPFR rounding containment or
of the mathematical owner formula.  The audit leaves numeric import,
pointwise mathematical dominance, producer GO, and RH claim false.
