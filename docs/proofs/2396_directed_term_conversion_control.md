# 2396 — directed term conversion control

Date: 2026-10-02.

Without modifying the 2385 source, a 1001-node sequential replay captured all
4004 point/channel MPFR term conversions performed by the worker. Every
conversion was finite and nonnegative, and its RNDU binary64 result was at
least its RNDD result.

This validates the conversion operation used by the directed path on the
control run. It does not prove the underlying interval enclosure theorem,
the full-grid termwise bound, or Lean numeric import.
