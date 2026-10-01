# 2421 — geometry-cache outward repair

Date: 2026-10-02.

The 20001-node mpmath control exposed a genuine enclosure escape that was
not repaired by increasing the public binary64 hull from 4 to 8, 16, or 32
ULPs.  The failure localized to the shared `geometry_cache`: a fresh
`eval_box(x,x,None)` contained the exact-rational-operand, 90-digit mpmath
value, while a cached second evaluation did not.  The cached MPFR endpoints
had been reduced to binary64 without an independent outward margin, and the
loss was amplified by cancellation in `base_D2`.

The evaluator now applies a separately named four-ULP outward margin to every
nonzero cached lower/upper geometry endpoint, while leaving the public hull
margin at four ULPs.  The current-source 20001-node control then checked all
80004 point/channel values with zero failures.

This is still a sampled control.  The full-domain enclosure, Lean numeric
import, producer gate, and RH claim remain false.  A fresh full-grid replay is
required because the previous 2414 artifact predates this evaluator change.
