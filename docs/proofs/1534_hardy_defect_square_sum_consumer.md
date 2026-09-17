# 1534 — Hardy defect square-sum consumer

Date: 2026-09-17

Record 1533 gave the exact decomposition
`((E Q E) M - M) J = -(I-E) M J - E (I-Q) E M J`.

The new owning theorem
`sourceSoninHardySubId_sourceBasis_normSq_summable_of_radial_fourierDefects`
proves that square-summability of the two defect columns, after arbitrary
bounded ambient postcomposition and source-side precomposition, implies
square-summability of the Hardy-sub-identity column.  It preserves the signs
and keeps `M` inside both defects.

Together with records 1532 and 1531, the B4 producer is now reduced to two
explicit physical estimates:

```text
sum ||D (I-E) M J N e_i||^2 < infinity
sum ||D E (I-Q) E M J N e_i||^2 < infinity
```

No estimate or positivity theorem is supplied here.  The existing radial
finite-window result does not cover arbitrary actual `M`, and the Fourier-gap
estimate is still open.

Owning declaration: `ConnesWeilRH.Dev.C1G8R3BoundaryOutputFactorizationBridge`.
Audit: `...BoundaryOutputFactorizationBridgeAudit`.
