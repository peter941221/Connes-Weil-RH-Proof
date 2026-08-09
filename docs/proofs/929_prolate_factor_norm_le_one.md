# 929 — Sharp prolate-factor ceiling: ||factor|| ≤ 1 (verified axiom-clean)

Date: 2026-08-10. Type: analytic record sharpening on the Piece-1 front. No `sorry`,
no new `axiom`. RH NOT claimed.

## 0. What this sharpens

`CCM24SourceProlateTrace:35` defines the source prolate Hilbert-Schmidt factor

```text
sourceProlateHilbertSchmidtFactor lambda = sourceFourierSupportProjection lambda
    o (radialSupportProjection lambda - sourceSoninProjection lambda)
```

The second factor is the source orthogonal Sonin band `B0 = radial - sourceSonin`.
`CCM24FiniteSFixedQuotientCarrier:46` proves `B0` is itself an orthogonal
(star) projection, so `||B0|| <= 1` (via `IsStarProjection.norm_le`).  The
first factor is also a star-projection, `||Q_fourier|| <= 1`.  Composition gives

    ||factor|| <= ||Q_fourier|| * ||B0|| <= 1 * 1 = 1.

This sharpens the coarse triangle-inequality ceiling `||B0|| <= 2` (equivalently
`||factor|| <= 2`) that `ELambdaProjectorNormBoundProbe` (2026-08-06) recorded
as the strict-contraction obstruction.

## 2. Status (WSL-verified)

`ConnesWeilRH/Dev/EBandFactorSharpProbe.lean`, theorem
`prolateLemmaFactor.prolateFactor_norm_le_one`, compiles axiom-clean with
`#print axioms = [propext, Classical.choice, Quot.sound]`, 0 sorry, 0 project
axioms.  Verified against the warm cached oleans of the current-base mirror
`cwr-main` (Windows HEAD sync).

## 3. Does it close the Gate? - No (spectral still open)

The strict contraction `||factor|| < 1` required by
`summable_normSq_of_strictContraction_of_defect` is STILL not furnished (the
bound is `<= 1`, equality possible). Hence `Summable ||factor||^2` along the
generic-`lambda` wall still requires the spectral/eigenvalue route, exactly as
`ELambdaProjectorNormBoundProbe` concluded. The improvement here is that the
correct operator-norm ceiling of the factor is **1**, not 2, so any future
operator-norm-based estimate uses the constant `1` rather than `4` for
`||factor||^2`.

The infinite-carrier Gate remains OPEN: it reduces to the single analytic
identity `L_S = sourceActualBandCombinedCoframeLeakage = F + (D - J) = 0` on
non-empty prime families (docs/925-928), and this bound does not touch `D`.
RH NOT claimed.

## 4. Files

- `ConnesWeilRH/Dev/EBandFactorSharpProbe.lean` (new, verified).
- `docs/proofs/929_*` (this record).
- MEMORY change-log entry 2026-08-10.

