# 1326 — G8 P1 Schur boundary antiresonant factorization

Date: 2026-09-11.

Status: FORMAL Lean brick. It puts the one-step rectangular Schur boundary
dagger of the finite-S Euler cascade into the antiresonant language already
used on the radial side of P1, with an exact scalar identity and a closed
two-channel ledger. It proves no summability of the antiresonant column
energy, no vanishing, no metric-to-radial cutoff identification, and no RH
statement.

## Statement

The one-step boundary dagger of the Euler Schur cascade is definitionally

```text
boundaryDagger(p,S) = (I - newFrame newFrame†) ∘L transport† ∘L oldFrame.
```

Lean now proves the antiresonant factorization of this channel:

1. exact scalar identity
   `transport† = I - √q_p • (primeEulerAmbientLossFactor p)†`
   — the Euler factor `(1 - q_p p^{-s})` and the antiresonant factor
   `(1 + p^{-s})` differ by the visible square-root coefficient and the
   identity channel;
2. exact split, for every source vector `x`, after cutting `oldFrame x`
   through the suffix range projection `P_S`:
   ```text
   boundaryDagger x
     = (I - P_S)(transport†((I - P_S)(oldFrame x)))
       - √q_p • (I - P_S)(antiresonantColumn(newFrame†(oldFrame x)));
   ```
3. pointwise two-channel ledger
   `‖boundaryDagger x‖ ≤ ‖x‖ + √q_p ‖antiresonantColumn(newFrame†(oldFrame x))‖`,
   using that the range complement `I - P_S` is itself a star projection
   (contractive), `transport†` is contractive, and `oldFrame` is
   contractive;
4. operator-norm corollary
   `‖boundaryDagger‖ ≤ 1 + √q_p ‖antiresonantColumn ∘L newFrame† ∘L oldFrame‖`.

Consequence for P1: the metric-side coframe boundary map at the first step
now carries the SAME visible antiresonant column as the radial crossing
channel of the record 1325 ledger (`32‖q_p⁻¹‖ ‖antiCol(frame† u)‖`), with
prefix `newFrame† ∘L oldFrame` in place of `frame†`. Both sides of P1 are
now fed by one named antiresonant column family; the remaining transport is
the comparison of the two pullback prefixes at the same cutoff.

## Lean owner

`C1G8P1SchurBoundaryAntiresonantFactorization.lean`, paired audit
declarations:

```text
norm_id_sub_newSuffixRangeProjection_apply_le
id_sub_newSuffixRangeProjection_apply_newSuffixFrame
normalizedPrimeEulerFrameTransport_adjoint_eq_id_sub_sqrtCoeff_smul_lossFactorAdjoint
normalizedPrimeEulerFrameTransport_adjoint_apply
norm_normalizedPrimeEulerFrameTransport_adjoint_le_one
norm_oldSuffixFrame_le_one
suffixEulerFrameSchurStep_boundaryDagger_apply_eq_interior_add_antiresonant
norm_suffixEulerFrameSchurStep_boundaryDagger_apply_le_twoChannel
norm_suffixEulerFrameSchurStep_boundaryDagger_le
```

## Verification

Batch `1539_g8_p1_schur_boundary_antiresonant_batch.log` (3460 jobs): zero
`error:` and `sorryAx`; every audit declaration prints only
`[propext, Classical.choice, Quot.sound]`.

RH is not claimed.
