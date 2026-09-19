# 1712 — Exact L2 energy readback of the source-root annulus

Date: 2026-09-20

Status: formal brick, not an RH result.

The theorem
`sourceRootAnnularOutputWindow_normSq_eq_annulus_integral` combines the
committed L2 norm identity with record 1711.  For every source-carrier input,
the squared norm of the source-root annular output is exactly the ordinary
integral of the squared norm of the root-convolution output restricted to
the symmetric annulus `Icc (-n) n \ Icc (-N) N`.

This is the precise function-level/kernel-diagonal form requested by the S3
consumer.  It adds no estimate, summability, positivity, carrier witness, or
RH premise.  The remaining producer obligation is to obtain a bound uniform
in the expanding annulus after summing over the selected source basis; record
1708 identifies that obligation with the Hardy-corner square-sum.

Verification: the theorem and paired Audit leaf built successfully in 3967
jobs, with zero `error:` lines and zero `sorryAx`.  The Audit declaration
reports only `propext`, `Classical.choice`, and `Quot.sound`.
