/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurMarkovUniformBound

/-!
# Physical lower/upper normalization alignment

The normalized physical owner and the Schur--Markov owner use different
scalar gauges.  This module records their exact relation on the same
coframe and response carriers:

```text
normalized = (lower * upper) * schurMarkovScaled.
```

The product `lower * upper` is at most one.  This is a carrier and scaling
alignment only.  It does not remove the Schur--Markov factor
`lower / upper` from the raw response and therefore does not close Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSPhysicalSchurMarkovAlignment

open CC20Concrete
open CCM24FiniteSGramResponse
open CCM24FiniteSNormalizedCoframe
open CCM24FiniteSNormalizedPhysicalResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSSchurMarkovPairing
open CCM24FiniteSSchurMarkovUniformBound
open CCM24FiniteSTransportBounds

private theorem lowerUpper_mul_schurMarkovScalar_eq_lower_sq
    (S : List CCM24VisiblePrime) :
    ((finiteEulerLowerFactor S * finiteEulerUpperFactor S : ℝ) : ℂ) *
        (suffixEulerSchurMarkovScalar S : ℂ) =
      (finiteEulerLowerFactor S : ℂ) ^ 2 := by
  rw [suffixEulerSchurMarkovScalar_eq_lower_div_upper]
  have hupper : finiteEulerUpperFactor S ≠ 0 :=
    ne_of_gt (finiteEulerUpperFactor_pos S)
  have hreal :
      finiteEulerLowerFactor S * finiteEulerUpperFactor S *
          (finiteEulerLowerFactor S / finiteEulerUpperFactor S) =
        finiteEulerLowerFactor S ^ 2 := by
    field_simp [hupper]
  exact_mod_cast hreal

theorem normalizedFiniteEulerMetricCoframe_eq_lowerUpper_smul_schurMarkovMixed
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    normalizedFiniteEulerMetricCoframe lambda family =
      ((finiteEulerLowerFactor family.visiblePrimes *
          finiteEulerUpperFactor family.visiblePrimes : ℝ) : ℂ) •
        schurMarkovMixedMetricCoframe lambda family := by
  unfold normalizedFiniteEulerMetricCoframe
    CCM24FiniteSSchurMarkovUniformBound.schurMarkovMixedMetricCoframe
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.smul_apply, smul_smul]
  rw [lowerUpper_mul_schurMarkovScalar_eq_lower_sq]

theorem normalizedSourceBandGramResponse_eq_lowerUpper_smul_schurMarkovScaled
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    normalizedSourceBandGramResponse owner lambda family =
      ((finiteEulerLowerFactor family.visiblePrimes *
          finiteEulerUpperFactor family.visiblePrimes : ℝ) : ℂ) •
        schurMarkovScaledSourceBandGramResponse owner lambda family := by
  unfold normalizedSourceBandGramResponse
    CCM24FiniteSSchurMarkovUniformBound.schurMarkovScaledSourceBandGramResponse
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.smul_apply, smul_smul]
  rw [lowerUpper_mul_schurMarkovScalar_eq_lower_sq]

theorem lowerUpperFactor_nonneg
    (family : FinitePrimePowerFamily) :
    0 ≤ finiteEulerLowerFactor family.visiblePrimes *
      finiteEulerUpperFactor family.visiblePrimes := by
  exact mul_nonneg
    (le_of_lt (finiteEulerLowerFactor_pos family.visiblePrimes))
    (le_of_lt (finiteEulerUpperFactor_pos family.visiblePrimes))

theorem lowerUpperFactor_le_one
    (family : FinitePrimePowerFamily) :
    finiteEulerLowerFactor family.visiblePrimes *
        finiteEulerUpperFactor family.visiblePrimes ≤ 1 :=
  finiteEulerLower_mul_upper_le_one family.visiblePrimes

theorem norm_normalizedFiniteEulerMetricCoframe_le_norm_schurMarkovMixed
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖normalizedFiniteEulerMetricCoframe lambda family‖ ≤
      ‖schurMarkovMixedMetricCoframe lambda family‖ := by
  rw [normalizedFiniteEulerMetricCoframe_eq_lowerUpper_smul_schurMarkovMixed
    lambda family]
  calc
    ‖((finiteEulerLowerFactor family.visiblePrimes *
        finiteEulerUpperFactor family.visiblePrimes : ℝ) : ℂ) •
        schurMarkovMixedMetricCoframe lambda family‖ ≤
      ‖((finiteEulerLowerFactor family.visiblePrimes *
        finiteEulerUpperFactor family.visiblePrimes : ℝ) : ℂ)‖ *
        ‖schurMarkovMixedMetricCoframe lambda family‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ 1 * ‖schurMarkovMixedMetricCoframe lambda family‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (lowerUpperFactor_nonneg family)]
      exact mul_le_mul_of_nonneg_right (lowerUpperFactor_le_one family)
        (norm_nonneg (schurMarkovMixedMetricCoframe lambda family))
    _ = ‖schurMarkovMixedMetricCoframe lambda family‖ := one_mul _

theorem norm_normalizedSourceBandGramResponse_le_norm_schurMarkovScaled
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖normalizedSourceBandGramResponse owner lambda family‖ ≤
      ‖schurMarkovScaledSourceBandGramResponse owner lambda family‖ := by
  rw [normalizedSourceBandGramResponse_eq_lowerUpper_smul_schurMarkovScaled
    owner lambda family]
  calc
    ‖((finiteEulerLowerFactor family.visiblePrimes *
        finiteEulerUpperFactor family.visiblePrimes : ℝ) : ℂ) •
        schurMarkovScaledSourceBandGramResponse owner lambda family‖ ≤
      ‖((finiteEulerLowerFactor family.visiblePrimes *
        finiteEulerUpperFactor family.visiblePrimes : ℝ) : ℂ)‖ *
        ‖schurMarkovScaledSourceBandGramResponse owner lambda family‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ 1 * ‖schurMarkovScaledSourceBandGramResponse owner lambda family‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (lowerUpperFactor_nonneg family)]
      exact mul_le_mul_of_nonneg_right (lowerUpperFactor_le_one family)
        (norm_nonneg
          (schurMarkovScaledSourceBandGramResponse owner lambda family))
    _ = ‖schurMarkovScaledSourceBandGramResponse owner lambda family‖ :=
      one_mul _

end CCM24FiniteSPhysicalSchurMarkovAlignment
end CCM25Concrete
end Source
end ConnesWeilRH
