3182 Route-A Signed Finite-Window Enclosure
============================================

Status
------

SIGNED_FINITE_WINDOW_INTERVAL_STYLE_ENCLOSURE

This record targets the correction coefficient endpoint identified by 3181 at
sigma -1/2. It uses the existing Arb interval jets and derivative envelope from
record 2561, but changes the node quantity from an absolute-value majorant to
the signed real-part upper bound.

For each cell, the calculation is:

    signed trapezoid upper + h^3 / 12 * upper bound for abs(second derivative)

The derivative envelope supplies a cellwise bound for the curvature remainder.
The result is still an external artifact: it is not yet a Lean theorem and it
does not include the full-line tail.

Reproduction
------------

    python scripts/routea_signed_correction_enclosure_3182.py

Machine-readable output:

    results/3182_signed_finite_window_enclosure.json

Observed result
---------------

At 2560 cells and 192-bit Arb precision, the signed node upper is about
-3.5379181104e-9. The curvature remainder upper is about 65011.5525, so the
total finite-window upper is positive, about 65011.5525. The candidate is
therefore not closed by this first interval-style budget.

The failure mechanism is informative: the signed node cancellation survives,
but the uniform cellwise derivative envelope is far too conservative near the
support boundaries. The next refinement should split boundary cells or use a
local envelope, while preserving the same correction endpoint and owner.