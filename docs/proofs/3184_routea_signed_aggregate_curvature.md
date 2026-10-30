3184 Route-A Signed Aggregate Curvature
=======================================

Status
------

SIGNED_AGGREGATE_CURVATURE_DIAGNOSTIC

Record 3182 priced the third derivative family-by-family before summing. This
record instead sums the signed complex third derivatives first, then adds the
coefficient uncertainty and fourth-derivative charges. The change preserves
more cancellation in the trapezoid remainder estimate.

Reproduction
------------

    python scripts/routea_signed_aggregate_curvature_3184.py

Output:

    results/3184_signed_aggregate_curvature.json

This is a diagnostic comparison, not a Lean certificate or RH claim.

Observed result
---------------

At 2560 cells and 192-bit precision, the signed node upper remains about
-3.5379181104e-9. Aggregating the signed third derivative before adding its
coefficient and fourth-derivative charges reduces the curvature remainder from
about 65011.55 in record 3182 to about 9157.13. The total upper is still
positive, about 9157.13.

This confirms that family-by-family absolute third-derivative pricing was a
real source of overestimation, but the remaining fourth-derivative envelope is
still too conservative for the 1e-8-scale candidate margin.