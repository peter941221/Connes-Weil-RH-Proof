# 2378 — full-grid span-control failure and expression mismatch

Date: 2026-10-02.

The delayed 776611-node, 12-worker replay completed and produced the same
directed integrals as record 2374.  The newly added span-level comparison is
`False` for `base_M0` and `corr_D2`, although the final global comparison is
`True` for all four channels.

This is not a certificate.  The failed comparison is between two different
expressions: the exact sum of nearest-binary64 terms built from
`math.hypot(...) * math.exp(...)`, and the MPFR round-up path that recomputes
norm, exponential, weight, and accumulation directionally.  Global
dominance cannot repair a local under-bound, especially when the two paths
are not the same object.  The next correction is to gate each directed term
against its own directed construction allowance, or to remove this
cross-expression dominance test from the certificate path.

The producer and RH claim remain false.
