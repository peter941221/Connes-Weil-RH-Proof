# 3238: weighted-original-function Taylor-6 diagnostic

Status: aligned external feasibility evidence; not a Lean certificate.

The formal Route-A aggregate target is the real function

```text
weightedExternal3201 (-1/2) coefficients modulations x
= Re(exp((-1/2) * x) * externalPhysical2344 coefficients modulations x)
```

The 3238 evaluator uses the concrete binary64 owner coefficients, the stored
owner squared radii, the captured modulation coordinates, and the 40960-cell
grid. Its jet generator starts with `raw[j]`, so its zero-th jet is the
weighted original function value. This is the object required by the Lean
`hvalue` premise in records 3225 and 3230.

The numerical result is:

```text
cells                                      40960
sigma                                      -1/2
Taylor-6 window upper                      -1.4151657848627206e-8
sixth-order remainder upper                 1.4593071872206805e-14
minimum cell index                         16923
minimum cell upper                         -2.6747156900538511e-2
producer_go                                false
```

For comparison, the same evaluator at 2560 cells gives a positive upper of
approximately `3.563796884971633e-6`. This shows that the fine partition is
part of the numerical margin, not merely a presentation choice.

The result does not prove the finite aggregate because the evaluator and its
JSON output remain outside Lean. The next formal artifact must reproduce the
same object with exact owner data, interval bounds, and no look-ahead from the
JSON sidecar. The first local target is a weighted version of the correlated
taxi-ball enclosure at midpoint index `17168`.
