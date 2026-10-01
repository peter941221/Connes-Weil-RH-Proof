# 2368 - Exact binary64 accumulation audit

日期：2026-10-02。

The 2359 full-grid replay was rerun with the same 240001 nodes, 20001-node
spans, and ordered parent reduction. Each generated binary64 term is now also
converted with `Fraction.from_float` and accumulated exactly in node/span
order. The largest difference between the existing NumPy accumulation and the
exact sum of those binary64 terms is approximately `3.058588208835539e-10`,
on the fourth channel; the other channel gaps are approximately
`6.23e-15`, `9.89e-12`, and `3.89e-13`.

This closes an accounting sub-obligation for the already-generated float
terms, but it is not a directed MPFR accumulation theorem: the pointwise
`interval_abs_upper` conversion and the trapezoid remainder remain outside
this audit. The result is conditional diagnostic evidence, not a producer
certificate or GO.

Status: `EXACT_BINARY64_TERM_SUM_ONLY`; producer GO: `false`.
