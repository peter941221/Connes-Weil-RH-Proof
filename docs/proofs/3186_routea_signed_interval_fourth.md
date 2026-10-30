3186 Route-A Signed Interval Fourth Derivative
==============================================

Status
------

SIGNED_INTERVAL_FOURTH_DIAGNOSTIC

This record computes a cell-local Arb interval for the aggregate fourth
derivative. Families fully inside a cell are summed before taking the modulus;
cells crossing a support boundary use the existing conservative fallback.

Reproduction
------------

    python scripts/routea_signed_interval_fourth_3186.py

Output:

    results/3186_signed_interval_fourth.json

The result remains diagnostic and does not provide a Lean or RH certificate.

Observed result
---------------

At 2560 cells and 192-bit precision, the total upper is about 22.9240733360,
with a fourth-order remainder upper about 22.9240733395. This improves on the
3185 total upper of about 214.76 by preserving cancellation inside each cell.
The result remains positive and is still diagnostic only.