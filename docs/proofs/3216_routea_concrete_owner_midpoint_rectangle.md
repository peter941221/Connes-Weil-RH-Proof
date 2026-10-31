3216 Route-A Concrete-Owner Midpoint Rectangle
==============================================

Status
------

PASS_EXTERNAL_MIDPOINT_RECTANGLE_IMPORT_PREMISE_OPEN

Purpose
-------

This record evaluates the actual record2680 owner at the actual 3212
 diagnostic midpoint for cell 0. It does not use the legacy normalized cell
 coordinate.

Reproduction
------------

    python scripts/routea_concrete_owner_midpoint_rectangle_3216.py

Output
------

    results/3216_routea_concrete_owner_midpoint_rectangle.json

Observed result
---------------

At midpoint

    -2684289064959 / 409600000000

with sigma `-1/2`, the 30-family Arb evaluation has exactly one nonzero family
rectangle after rounding to the `10^-80` rational grid. The aggregate real
rectangle is

    reLo = -1 / 10^80
    reHi = 0

and it matches the 3204 `value_upper = 0` row. This is a strong numerical
coordinate-identity check, not a Lean certificate.

Remaining boundary
-------------------

Lean still needs a proof that the concrete family-4 expression at this exact
midpoint lies in the generated rectangle. The old `record2680CorrectionM0CellContained`
certificate cannot be reused because it covers a different normalized cell
coordinate. No producer or RH claim follows.
