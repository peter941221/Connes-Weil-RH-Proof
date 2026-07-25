# Proof 559: physical analysis isometric factor

The existing ambient-defect ledger proves the exact pointwise identity

```text
||AmbientBoundaryAnalysis(p,S) x||^2
  = ||leftCoDefect(p,S) x||^2.
```

Proof 559 applies the repository's all-vector Douglas construction to the
packed physical carrier and obtains an actual operator `V_(p,S)` such that

```text
V_(p,S) * leftCoDefect(p,S) = AmbientBoundaryAnalysis(p,S)
||V_(p,S)|| <= 1.
```

It also proves that `V_(p,S)` preserves the norm of every vector presented by
`leftCoDefect(p,S)`. This is an isometric lifting of the Julia co-defect into
the genuine two-channel physical carrier. The proof keeps the ambient and
moving-boundary coordinates packed until after the norm identity.

This closes a real carrier/factorization gap. It does not factor the raw or
route/polar mismatch row through the co-defect. The non-polar gap, Gate 3U,
the finite-S sign, Burnol's identity, and RH remain open.
