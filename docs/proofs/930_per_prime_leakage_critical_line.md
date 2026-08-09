# 930 - Per-prime physical leakage is critical-line divergent: only cancellation can close the infinite Gate

Date: 2026-08-10. Type: analytic route record (source-grounded). No `sorry`, no new `axiom`. RH NOT claimed.

## 0. The single-prime bound (already in the library)

`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMomentDecay.lean:879` proves

    norm_normalizedPhysicalLeakage_singlePrime_le_twelve_mul_coefficient :
        || normalizedSourcePhysicalCoframeLeakage lambda (singlePrimeFamily p hp) || <= 12 * ccm24PrimeEulerCoefficient p

with `ccm24PrimeEulerCoefficient p = 1 / Real.sqrt p` (CCM24EulerTransport.lean:33)
the critical-line coefficient.  So every single non-empty visible prime `p` contributes a
leakage norm bounded by `12 / Real.sqrt p`, i.e. **O(p^{-1/2})**.

## 1. Consequence: absolute-value per-prime summability fails at exactly the critical line

The series of prime bounds is

    Sum_{p prime} 1 / Real.sqrt p ~ 2 sqrt(x) / ln x      (diverges, as x -> infinity)

so the **absolute-value per-prime total diverges**.  It is not a soft tail (`sum 1/p^s`
with `Re s > 1`); it sits exactly at the RH critical exponent `1/2`. Hence the infinite
-carrier Gate CANNOT be closed by summing the per-prime operator-norm bounds in absolute
value. Any closing must come from the **signed cancellation** inside the complete physical
owner, i.e. the Piece-1 identity

    L_S = sourceActualBandCombinedCoframeLeakage = F + (D - J) = 0

The `(I-P)F = -(I-P)D` cancellation is therefore not a cosmetic option: it is the only
mechanism, because the absolute route provably diverges.

## 2. Relation to the earlier divergence (docs/927)

- docs/927 pointed to `(card B) * ||Support(B)||` diverging as the band extends, a
  band-cardinality effect.
- This memo adds the **complementary** per-prime fact: even summing prime-by-prime,
  the leakage coefficient `p^{-1/2}` is critical-line and diverges absolutely. Both
  point the same way: no absolute-summability route closes the Gate; cancellation is
  required. This is RH-scale coherence, not a Lean-assembly leaf.

## 3. Not a closure

The `O(p^{-1/2})` bound gives no lower bound on any one term, does not give `L_S = 0`, and
does not give `Summable ||... ||`. It merely pins WHY the open step must be the signed
identity (Piece 1). The finite-band Gate remains the closed deliverable (byte-verified
2026-08-10); the infinite-carrier Gate remains open. RH not claimed.

## 4. Files

- `ConnesWeilRH/Source/CC20Concrete/CCM24EulerTransport.lean:33` (coeff `1/sqrt p`)
- `ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMomentDecay.lean:879` (12*coeff bound)
- `docs/proofs/930_*` (this memo), MEMORY entry 2026-08-10.
