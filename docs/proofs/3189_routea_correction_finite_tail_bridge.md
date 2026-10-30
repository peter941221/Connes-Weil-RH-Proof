3189 Route-A Correction Finite/Tail Bridge
===========================================

Status
------

NUMERIC_FINITE_TAIL_MARGIN_PROMISING_OWNER_TRANSFER_OPEN

This record compares the 40960-cell correction finite-window upper from 3187
with the external contour tail upper from 2353. The comparison is exact
rational arithmetic, but it is deliberately fail-closed: record 2353 is not
declared to be the same correction owner, and the tail is not imported into
Lean.

Reproduction
------------

    python scripts/routea_correction_finite_tail_bridge_3189.py

Output:

    results/3189_correction_finite_tail_bridge.json

Observed result
---------------

The external 2353 contour tail upper is approximately 1.7182037663e-16.
Adding it to the 3187 40960-cell finite-window upper gives approximately
-3.5110506604e-9. Thus the numerical scale leaves margin. This does not close
the route because 2353 has not been proved to price the same correction owner,
and the tail is not imported into Lean.