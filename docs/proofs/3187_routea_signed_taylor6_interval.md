3187 Route-A Signed Taylor-6 Interval
=====================================

Status
------

SIGNED_TAYLOR6_INTERVAL_DIAGNOSTIC

This record extends the local aggregate interval method to a sixth-order
midpoint Taylor formula. Interior cells use aggregate sixth-derivative Arb
intervals; support-crossing cells retain a conservative fallback.

The symmetric-cell formula is:

    h*f + h^3*f2/24 + h^5*f4/1920 + h^7*sup_abs_f6/322560

Reproduction:

    python scripts/routea_signed_taylor6_interval_3187.py

Output:

    results/3187_signed_taylor6_interval.json

Refined result
--------------

At 40960 cells and 192-bit precision, the total upper is approximately
-3.51105083224e-9. The sixth-order remainder upper is approximately
2.68672781838e-11. This is the first interval-style finite-window run in this
sequence whose total upper is negative. It remains external evidence: the
full-line tail and Lean import are still open.