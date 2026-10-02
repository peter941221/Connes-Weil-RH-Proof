# 2429 — Route A interval arithmetic primitives

Date: 2026-10-02.

The interval interface now also proves the directed primitives needed before
the numerical evaluator can be connected to the owner formula:

* rectangle subtraction;
* multiplication of a rectangle by a nonnegative real scalar;
* containment preservation for both operations.

These are exact real-order lemmas, compiled independently with Lean 4.30 and
the current Mathlib build.  They do not assert that the Python MPFR endpoints
are valid, and they do not import any stored number.  General signed interval
products (the `iprod`/`ciprod` step) and the actual `correctedPhysical`
identification remain open.
