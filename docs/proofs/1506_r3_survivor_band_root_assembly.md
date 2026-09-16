# 1506 — S3 survivor band-root assembly

Date: 2026-09-16.

Status: FORMAL structural reduction; no sign and no RH claim.

`C1G8R3SurvivorBandRootAssembly.lean` proves that the completed range leg,
whose same-basis square-sum is already available at every Sonin scale, and
the Fourier-leakage commutator leg assemble exactly to
`rootConvolution owner ∘L sourceBandProjection lambda`. The proof uses the
committed identity
`sourceRootCompletedLeftLegs_add_eq_root_band` and the Hilbert--Schmidt
sum-of-two-legs estimate.

Thus S3 is reduced to one genuine estimate: square-summability of
`sourceRootCompletedRightCommutatorLeftLeg`. This record does not assert that
estimate. B3, B4, the Euler-content identification in ρ5, and RH remain open.

Acceptance: `0916_s3_band_assembly_try3.log`, 3288 jobs, zero `error:` lines,
zero `sorryAx`, and the paired Audit leaf prints only
`[propext, Classical.choice, Quot.sound]`.
