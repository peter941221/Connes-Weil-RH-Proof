# 2435 — Current MPFR rounding-contract audit

Date: 2026-10-02.

The current evaluator source is checked structurally: every direct arithmetic
operation in `Kernel.eval_box` uses RNDD or RNDU, transcendental calls use a
directed rounding argument, the four MPFR accumulator conversions use the
matching lower/upper directions, and the public binary64 hull has explicit
outward `nextafter` steps.

This is the prerequisite rounding contract for the directed endpoint
interface.  It is not a proof that the mathematical `correctedPhysical`
summand is enclosed, and it does not import a numerical artifact into Lean.
