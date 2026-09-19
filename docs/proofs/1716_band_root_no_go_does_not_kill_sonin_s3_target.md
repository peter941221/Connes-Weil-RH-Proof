# 1716 — The ambient band-root Hilbert–Schmidt no-go does not kill S3

Date: 2026-09-20

Status: formal route clarification; no RH claim.

## Formal fact

`sourceRootCompletedBandRoot_not_hilbertSchmidt` proves that, when the
selected source Laplace value is nonzero, the ambient operator

`rootConvolution owner ∘L sourceBandProjection unitSoninScale`

cannot have square-summable columns on a Hilbert basis of `finiteSCarrier`.
The proof uses the separated translated source orbit and the already
square-summable range leg, so the leakage leg cannot be cancelled at infinity.

## Exact scope

This is not the S3 target. The live S3 energy is the source-carrier
compression

`sourceSoninProjection lambda ∘L rootConvolution owner ∘L sourceInclusion lambda`,

equivalently `sourceCompressedRoot owner lambda`. The formal source/band
geometry treats `sourceBandProjection` as the complementary Fourier-defect
channel, and the existing S3 normal form removes the prolate correction before
leaving the Hardy corner. Therefore the ambient band-root no-go cannot be
used to infer failure of the source-projection square-sum.

## Route consequence

The full ambient-Hilbert–Schmidt shortcut is closed, while S3 remains a live
finite-tail/annular kernel-diagonal estimate. The exact current consumer is
`sourceCompressedRoot_squareSum_of_eventual_ambient_annular_trace_bound`:
it needs a uniform upper bound for the ambient annular Gram trace, not an
ambient Hilbert–Schmidt theorem.

Evidence: `ConnesWeilRH/Dev/C1G8R3HilbertSchmidtOrthonormalObstruction.lean`,
`ConnesWeilRH/Dev/C1G8R3GateAmbientNormalForm.lean`, and
`ConnesWeilRH/Dev/C1G8R3AnnularTraceConsumer.lean`.
