# 1711 — Exact pointwise readback of the source-root annulus

Date: 2026-09-20

Status: formal brick, not an RH result.

The new theorem
`sourceRootAnnularOutputWindow_coeFn_eq_annulus_indicator` proves that the
source-root annular output window is, almost everywhere, the set difference of
the two symmetric interval indicators applied to one and the same
`rootConvolution` output:

```text
(P_n - P_N) rootConvolution =
  indicator (Icc (-n) n \ Icc (-N) N) * rootConvolution.
```

The proof expands the committed interval-projection readback and the Lp
subtraction representative, then handles the nested intervals directly.  It
adds no positivity, trace estimate, summability, or carrier witness.  Its
consumer is the S3 source-root annular estimate: the remaining analytic task
is now a kernel-diagonal or local-energy bound for this explicit annular
restriction, equivalently the Hardy-corner square-sum identified in record
1708.

Verification: focused build of the theorem and paired Audit leaf completed
successfully in 3963 jobs, with zero `error:` lines and zero `sorryAx`; the
Audit declaration reports only `propext`, `Classical.choice`, and `Quot.sound`.
