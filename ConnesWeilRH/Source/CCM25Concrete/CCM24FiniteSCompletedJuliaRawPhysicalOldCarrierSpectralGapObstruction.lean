/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMovingMomentColumnSelector
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap

/-!
# Source-specific obstruction to a uniform old-carrier spectral gap

Proof 590 closes the spectral-gap branch of Bone 1 whenever the actual source
Sonin carrier has a nonzero vector.  Proof 584 supplies a genuine sequence of
old-carrier columns

```text
  y_p = newSuffixFrame lambda [] x
  ||W_p y_p|| -> 0
```

while the polar frame isometry keeps `||y_p|| = ||x|| > 0`.  A family-uniform
lower bound for `W_p` is therefore impossible.  This is stronger than the
generic quotient guard, but it is still only a branch obstruction: it does not
rule out a direct signed quotient `R0 = F * W` whose numerator decays on the
same columns.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGapObstruction

open scoped InnerProduct InnerProductSpace
open scoped Topology

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMovingMomentColumnSelector
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSFrameGramCalculus

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The actual spectral-gap obstruction -/

theorem noExistsUniformOldCarrierSpectralGap_of_nonzero_source_column
    {lambda : CCM24SoninScale}
    (prime : ℕ → CCM24VisiblePrime)
    (hcoeff : Filter.Tendsto
      (fun n => ccm24PrimeEulerCoefficient (prime n))
      Filter.atTop (𝓝 0))
    (x : sourceSoninCarrier lambda) (hx : x ≠ 0) :
    ¬ ∃ gap : ℝ,
      Nonempty (SuffixRawOldCarrierUniformSpectralGapData lambda gap) := by
  rintro ⟨gap, ⟨data⟩⟩
  have hgap : 0 < gap := data.gap_pos
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hcolumn :=
    tendsto_suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_norm_on_newSuffixFrame_of_tendsto_coefficient
      lambda x prime hcoeff
  let energy : ℝ := gap * ‖x‖ ^ 2
  have henergy : 0 < energy := by
    dsimp [energy]
    exact mul_pos hgap (sq_pos_of_pos hxnorm)
  have hsqrt : 0 < Real.sqrt energy := Real.sqrt_pos.2 henergy
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 hcolumn) (Real.sqrt energy) hsqrt
  have hframe : ∀ n : ℕ,
      ‖newSuffixFrame lambda [] x‖ = ‖x‖ := by
    intro n
    exact parameterizedSoninPolarFrame_isometry lambda 1 []
      (by norm_num) x
  obtain ⟨n, hn⟩ := (Filter.eventually_ge_atTop N).exists
  have hsmallDist := hN n hn
  have hsmall :
      ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda (prime n) []
          (newSuffixFrame lambda [] x)‖ < Real.sqrt energy := by
    simpa [Real.dist_eq,
      abs_of_nonneg (norm_nonneg _)] using hsmallDist
  have hsmallSq :
      ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda (prime n) []
          (newSuffixFrame lambda [] x)‖ ^ 2 < energy := by
    have hsum : 0 < Real.sqrt energy +
        ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda (prime n) []
          (newSuffixFrame lambda [] x)‖ := by
      positivity
    have hdiff : 0 < Real.sqrt energy -
        ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda (prime n) []
          (newSuffixFrame lambda [] x)‖ := by
      exact sub_pos.mpr hsmall
    have hprod : 0 <
        (Real.sqrt energy -
          ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda (prime n) []
            (newSuffixFrame lambda [] x)‖) *
        (Real.sqrt energy +
          ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda (prime n) []
            (newSuffixFrame lambda [] x)‖) :=
      mul_pos hdiff hsum
    rw [← Real.sq_sqrt henergy.le]
    nlinarith
  have hgapLower := data.lower_bound (prime n) []
    (newSuffixFrame lambda [] x)
  have hgapLower' : energy ≤
      ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda (prime n) []
        (newSuffixFrame lambda [] x)‖ ^ 2 := by
    simpa only [energy, hframe n] using hgapLower
  exact (not_lt_of_ge hgapLower') hsmallSq

/-! ## Arithmetic-prime specialization -/

theorem noExistsUniformOldCarrierSpectralGap_of_nonzero_source_column_arithmeticPrimes
    {lambda : CCM24SoninScale}
    (x : sourceSoninCarrier lambda) (hx : x ≠ 0) :
    ¬ ∃ gap : ℝ,
      Nonempty (SuffixRawOldCarrierUniformSpectralGapData lambda gap) := by
  exact noExistsUniformOldCarrierSpectralGap_of_nonzero_source_column
    arithmeticVisiblePrimeSequence
    tendsto_ccm24PrimeEulerCoefficient_arithmeticVisiblePrimeSequence
    x hx

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGapObstruction
end CCM25Concrete
end Source
end ConnesWeilRH
