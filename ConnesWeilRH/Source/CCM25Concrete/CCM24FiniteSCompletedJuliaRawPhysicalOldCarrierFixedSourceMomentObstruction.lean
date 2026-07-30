/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction

/-!
# Fixed-source one-prime moment obstruction

Proof 584 supplies an actual approximate kernel for the old-carrier analysis
on the fixed source column `newSuffixFrame lambda [] x` whenever the Euler
coefficient tends to zero.  This module closes the logical handoff to the
actual one-prime moment:

```text
uniform old-carrier quotient
  -> moment is bounded by the old-carrier analysis
  -> moment tends to zero on every fixed source column
```

The result is deliberately one-sided.  It does not assert that the moment
has a positive lower bound, because that would require a source theorem about
the signed physical response rather than an operator-norm estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceMomentObstruction

open scoped InnerProduct InnerProductSpace
open scoped Topology

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard
open CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierSpectralGap

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## The forced moment limit under a uniform quotient -/

set_option maxHeartbeats 4000000 in
-- The old-carrier quotient and filter composition require a larger local budget.
set_option maxRecDepth 10000 in
theorem tendsto_onePrimeBoundaryMoment_norm_on_newSuffixFrame_of_uniformOldCarrierDomination
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (prime : ℕ → CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hcoeff : Filter.Tendsto
      (fun n => ccm24PrimeEulerCoefficient (prime n))
      Filter.atTop (𝓝 0))
    {bound : ℝ}
    (hdata : Nonempty
      (SuffixRawOldCarrierUniformDominationData owner lambda bound)) :
    Filter.Tendsto
      (fun n =>
        ‖onePrimeBoundaryMoment owner lambda (prime n)
            ((ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda (prime n) []).oldFrame)
              (newSuffixFrame lambda [] x))‖)
      Filter.atTop (𝓝 0) := by
  obtain ⟨data⟩ := hdata
  have hanalysis : Filter.Tendsto
      (fun n =>
        ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda
            (prime n) [] (newSuffixFrame lambda [] x)‖)
      Filter.atTop (𝓝 0) :=
    tendsto_suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_norm_on_newSuffixFrame_of_tendsto_coefficient
      lambda x prime hcoeff
  have hupper : ∀ n,
      ‖onePrimeBoundaryMoment owner lambda (prime n)
          ((ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda (prime n) []).oldFrame)
            (newSuffixFrame lambda [] x))‖ ≤
        (8 * bound) *
          ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda
              (prime n) [] (newSuffixFrame lambda [] x)‖ := by
    intro n
    have hpoint := onePrimeBoundaryMoment_oldCarrier_norm_le owner lambda
      (prime n) bound (data.domination (prime n) [])
      (newSuffixFrame lambda [] x)
    simpa only [mul_assoc] using hpoint
  have hlimit : Filter.Tendsto
      (fun n =>
        (8 * bound) *
          ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda
              (prime n) [] (newSuffixFrame lambda [] x)‖)
      Filter.atTop (𝓝 0) := by
    simpa using hanalysis.const_mul (8 * bound)
  apply squeeze_zero (fun n => norm_nonneg _) hupper hlimit

/-! ## Direct obstruction entry point -/

set_option maxHeartbeats 4000000 in
-- The contradiction unfolds the uniform data through the previous filter theorem.
set_option maxRecDepth 10000 in
theorem noExistsUniformOldCarrierDomination_of_fixedSourceMoment_not_tendsto_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (prime : ℕ → CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hcoeff : Filter.Tendsto
      (fun n => ccm24PrimeEulerCoefficient (prime n))
      Filter.atTop (𝓝 0))
    (hmoment : ¬ Filter.Tendsto
      (fun n =>
        ‖onePrimeBoundaryMoment owner lambda (prime n)
            ((ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda (prime n) []).oldFrame)
              (newSuffixFrame lambda [] x))‖)
      Filter.atTop (𝓝 0)) :
    ¬ ∃ bound : ℝ,
      Nonempty
        (SuffixRawOldCarrierUniformDominationData owner lambda bound) := by
  rintro ⟨bound, hdata⟩
  exact hmoment
    (tendsto_onePrimeBoundaryMoment_norm_on_newSuffixFrame_of_uniformOldCarrierDomination
      prime x hcoeff hdata)

set_option maxHeartbeats 4000000 in
-- The lower-bound specialization keeps the exact old-carrier column unchanged.
set_option maxRecDepth 10000 in
theorem noExistsUniformOldCarrierDomination_of_fixedSourceMoment_lowerBound
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (prime : ℕ → CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hcoeff : Filter.Tendsto
      (fun n => ccm24PrimeEulerCoefficient (prime n))
      Filter.atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hmoment : ∀ᶠ n in Filter.atTop,
      epsilon ≤
        ‖onePrimeBoundaryMoment owner lambda (prime n)
            ((ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda (prime n) []).oldFrame)
              (newSuffixFrame lambda [] x))‖) :
    ¬ ∃ bound : ℝ,
      Nonempty
        (SuffixRawOldCarrierUniformDominationData owner lambda bound) := by
  apply noExistsUniformOldCarrierDomination_of_onePrimeMomentApproximateKernel
    (prime := prime)
    (y := fun _ => newSuffixFrame lambda [] x)
    (epsilon := epsilon) hepsilon
  · simpa only using hmoment
  · exact
      tendsto_suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_norm_on_newSuffixFrame_of_tendsto_coefficient
        lambda x prime hcoeff

/-! ## Moving-source obstruction entry point

The actual approximate-kernel witness is allowed to follow the prime.  The
only uniformity needed by the old-carrier estimate is a bound on the source
norm; this keeps translated/scattering candidates in the original carrier
without replacing the signed moment by its operator norm.
-/

set_option maxHeartbeats 4000000 in
-- The moving source, Douglas readout, and filter contradiction elaborate together.
set_option maxRecDepth 10000 in
theorem noExistsUniformOldCarrierDomination_of_movingSourceMoment_lowerBound
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (prime : ℕ → CCM24VisiblePrime)
    (x : ℕ → sourceSoninCarrier lambda)
    (hcoeff : Filter.Tendsto
      (fun n => ccm24PrimeEulerCoefficient (prime n))
      Filter.atTop (𝓝 0))
    {sourceBound : ℝ} (hsourceBound : 0 ≤ sourceBound)
    (hx : ∀ n, ‖x n‖ ≤ sourceBound)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hmoment : ∀ᶠ n in Filter.atTop,
      epsilon ≤
        ‖onePrimeBoundaryMoment owner lambda (prime n)
            ((ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda (prime n) []).oldFrame)
              (newSuffixFrame lambda [] (x n)))‖) :
    ¬ ∃ bound : ℝ,
      Nonempty
        (SuffixRawOldCarrierUniformDominationData owner lambda bound) := by
  apply noExistsUniformOldCarrierDomination_of_onePrimeMomentApproximateKernel
    (prime := prime)
    (y := fun n => newSuffixFrame lambda [] (x n))
    (epsilon := epsilon) hepsilon
  · simpa only using hmoment
  · exact
      tendsto_suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_norm_on_newSuffixFrame_of_tendsto_coefficient_of_uniformly_bounded_source
        lambda x prime hcoeff hsourceBound hx

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceMomentObstruction
end CCM25Concrete
end Source
end ConnesWeilRH
