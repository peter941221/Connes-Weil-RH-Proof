# 2218 — Relative-error to complex-radius interface

Date: 2026-09-29

Consumer: the healthy `CompactLog` B5 selected detector on the actual
source-zero owner; the downstream target remains same-owner `qw >= 0`.

The new audited theorem
`C1RouteAFloatRelativeError.norm_real_relative_error_le` proves the exact
machine-interface implication

```text
|e| ≤ u,  0 ≤ u
  -> ‖((1 : ℂ) + e) * x - x‖ ≤ u * ‖x‖.
```

Thus a future binary64 proof only needs to supply a relative operation error
`e` and its concrete `ulp` bound; the complex norm radius consumed by the
2216 final AMP aggregation is then kernel-checked.

Verification:

- module: `results/20260929_2218_float_relative_module_pass3.log`;
- paired audit: `results/20260929_2218_float_relative_audit.log`;
- audited axioms: `[propext, Classical.choice, Quot.sound]` only;
- no `sorryAx`.

## Scoped Mathlib finding

The repository's Mathlib `Data/FP/Basic.lean` exposes `ofRat`, `add`, `mul`,
and `div` as `unsafe` definitions and supplies no theorem connecting their
results to a real-number rounding interval. Therefore the direct route
“call Mathlib `Float`, then invoke its soundness theorem” is unavailable. This
is a scoped interface gap, not a claim that IEEE soundness is impossible; a
separate exact binary64 model or externally generated rational certificate is
required.

Status: `RELATIVE-ERROR-RADIUS-CLOSED /
MACHINE-SEMANTICS-OR-RATIONAL-ULP-CERTIFICATE-OPEN`.
No RH claim follows.
