# 2384 — shared geometry alignment guard

Date: 2026-10-02.

The shared geometry cache is now guarded by a runtime equality check on the
four channel `Kernel.recs` signatures `(a, theta)`.  The current owner has
30 records in every channel with identical order and values, so index-based
reuse is justified for this owner.  A future coefficient path that drops or
reorders a family now fails closed instead of silently misapplying a cached
interval.
