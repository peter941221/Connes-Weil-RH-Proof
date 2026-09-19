# 1702 — Hilbert–Schmidt factor compression closes the trace-level obligation

Date: 2026-09-19.

## Result

`Dev/StripDensityTraceLedger.lean` now proves
`stripDensity_compression_of_positiveComposition`.  If `A : H ->L G` has a
square-summable column family on a named Hilbert basis and `P : H ->L H` is
self-adjoint with operator norm at most one, then

```text
Re Tr(P (A† A) P) <= Re Tr(A† A).
```

The proof factors the compressed operator as `(A P)† (A P)` and applies the
existing Hilbert–Schmidt precomposition estimate.  It therefore avoids the
operator-square-root layer that was previously named as the missing
`StripDensityCompressionObligation`.

## Route meaning

This closes the compression obligation whenever the positive operator already
has a Hilbert–Schmidt factor.  It does not prove that every positive operator
has such a factor in the current tree, and it does not itself prove the G8
source-projection energy estimate.  Its healthy-`CompactLog` B5 consumer is
the trace/annular route: any future factorization of the selected finite-window
positive operator can now discharge the compression step without adding a
new analytic assumption.

## Acceptance

The paired Audit module built with
`Build completed successfully (2664 jobs)`, zero `error:` lines, zero
`sorryAx`, and standard axioms only:
`[propext, Classical.choice, Quot.sound]`.

RH is not claimed.
