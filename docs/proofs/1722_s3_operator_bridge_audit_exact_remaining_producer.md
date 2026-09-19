# 1722 — S3 operator bridge audit: exact remaining producer

Date: 2026-09-20

Consumer: the healthy `CompactLog` B5 route, specifically the S3
`sourceCompressedRoot` square-summability consumer.

## Finding

The committed physical trace-class results do not yet produce S3. In
particular, `sourceActualBandFiniteEulerPairedResponse_isTraceClassAlong`
controls a paired response containing the source band projection, the Sonin
projection, a finite-Euler inverse, and the selected detector. Its input
energy is supplied by the physical boundary pair. S3 instead asks for the
square-sum of the columns of
`sourceCompressedRoot = sourceInclusion† * rootConvolution * sourceInclusion`.
No theorem in the audited modules identifies these operators or bounds the
latter by the former.

## Exact surviving interface

The committed chain is now:

1. `sourceCompressedRoot_squareSum_iff_projectedRoot_squareSum` reduces S3 to
   the source-Sonin projected root.
2. `sourceCompressedRoot_squareSum_of_eventual_annular_tsum_energy` reduces
   the limit to a uniform bound on the annular output column energy.
3. `sourceRootAnnularOutputWindow_normSq_eq_annulus_integral` and
   `sourceRootAnnularOutputWindow_lintegral_tsum_eq_tsum_lintegral` reduce
   that bound to the diagonal of the annular root kernel after Tonelli.

Thus the remaining producer is a genuine operator-level estimate of the form

`integral (sum_i ||1_[N,n] (rootConvolution (sourceInclusion e_i))(t)||^2) <= B`

uniformly in the outer cutoff `n`, with `B` independent of the source basis.
The quadratic Fourier-decay and square-summability theorems in record 1721
are sufficient once this actual kernel diagonal is placed in their hypotheses,
but they do not supply that placement for an arbitrary source-Sonin basis.

## Route ruling

This is a formal/interface audit, not a numerical conclusion. The next
mathematical brick must therefore construct the annular kernel diagonal (or a
genuine operator factorization through an already controlled Hilbert-Schmidt
leg). Reusing detector-response trace class as an S3 proof is rejected.
