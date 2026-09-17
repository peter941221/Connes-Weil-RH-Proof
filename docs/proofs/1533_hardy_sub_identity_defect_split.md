# 1533 — Hardy-sub-identity radial/Fourier defect split

Date: 2026-09-17

The remaining B4 producer column from records 1531–1532 is
`((E Q E) M - M) J`.  The new exact bridge theorem expands it as

```text
((E Q E) M - M) J
  = -(I-E) M J - E (I-Q) E M J.
```

The factor `M` remains inside both terms, so this is an object-level identity
for the actual boundary factorization rather than a post hoc estimate.  The
first term is the radial boundary defect; the second is the Fourier-gap
defect.  No commutation of `M` with either projection is assumed.

This split does not supply either estimate.  In particular, the existing
finite-window radial theorem matches only the special root factor without an
arbitrary physical `M`, while the Fourier-gap term remains the genuine
healthy-carrier obstruction.  The theorem therefore sharpens the producer
target without changing WO-B's OPEN status.

Owning declaration: `ConnesWeilRH.Dev.C1G8R3BoundaryOutputFactorizationBridge`.
Audit: `...BoundaryOutputFactorizationBridgeAudit`.
