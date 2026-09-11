/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundaryColumnFullCarrierExtension
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundaryCauchyPairProducer

/-!
# G8 P1 radial crossing energy transport

The full-carrier extension supplies the pointwise comparison

```text
‖radial boundary crossing u‖ ≤ 32 ‖q_p⁻¹‖ ‖antiresonant column (frame† u)‖
```

for every `u : finiteSCarrier`, and the Cauchy pair producer turns basis
summability of the crossing energy into an explicitly owned trace-class
positive defect.  This leaf connects the two: summability of the
antiresonant-column pullback energy over any Hilbert basis of `finiteSCarrier`
transported through the canonical `(32 ‖q_p⁻¹‖)` factor gives the crossing
energy, and with it the owning pair for `C†C`.

This is a conditional transport only.  No vanishing, no summability theorem
for the antiresonant-column energy itself, and no RH-facing sign is claimed.
The remaining analytic input is now one named series, of the same kind as the
single cutoff-leg energy left open on the metric side of P1.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1RadialCrossingEnergyTransport

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryColumnBridge
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryColumnFullCarrierExtension
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryCauchyPairProducer
open CCM25Concrete.AntiresonantFrameLossRadialBoundaryCauchyDefect
open CCM25Concrete.AntiresonantFrameLossRadialBoundarySplit
open CCM25Concrete.AntiresonantFrameLossCommutator
open CCM25Concrete.CCM24FiniteSActualSchurCascade
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialSplit
open CCM25Concrete.CCM24FiniteSFrameGramCalculus
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Termwise column comparison -/

/-- The canonical pointwise square-norm comparison: the radial boundary
crossing costs at most `(32 ‖q_p⁻¹‖)²` times the pulled-back antiresonant
column energy.  The inverse Euler coefficient is kept visible, so the
comparison is not a uniform bound in `p`. -/
theorem normSq_radialSoninBoundaryCrossing_apply_le_canonical_antiresonantColumn
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) (u : finiteSCarrier) :
    ‖radialSoninBoundaryCrossing p S u‖ ^ 2 ≤
      (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) ^ 2 *
        ‖newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S) u)‖ ^ 2 := by
  have hnorm := norm_fullCarrierBoundaryChannelReadout_apply_le
    (canonicalRadialBoundarySourceColumnFactorizationData p S) u
  rw [fullCarrierBoundaryChannelReadout_eq_radialSoninBoundaryCrossing
    (canonicalRadialBoundarySourceColumnFactorizationData p S)] at hnorm
  have hconst : 0 ≤ (32 : ℝ) * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖ :=
    mul_nonneg (by norm_num) (norm_nonneg _)
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hconst (norm_nonneg _))).2 hnorm

/-! ## Conditional energy transport -/

/-- Summability of the pulled-back antiresonant-column basis energy implies
summability of the radial crossing basis energy, with the visible canonical
`(32 ‖q_p⁻¹‖)²` cost per term. -/
theorem summable_radialSoninBoundaryCrossing_normSq_of_antiresonantColumnEnergy
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcolumn : Summable fun i =>
      ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (sourceBasis i))‖ ^ 2) :
    Summable fun i =>
      ‖radialSoninBoundaryCrossing p S (sourceBasis i)‖ ^ 2 := by
  have hscaled := Summable.const_smul
    ((32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) ^ 2) hcolumn
  have hscaled' : Summable fun i =>
      (32 * ‖(ccm24PrimeEulerCoefficient p : ℂ)⁻¹‖) ^ 2 *
        ‖newFrameAntiresonantColumn unitSoninScale p S
          (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
            (sourceBasis i))‖ ^ 2 := by
    simpa only [smul_eq_mul] using hscaled
  refine Summable.of_nonneg_of_le (hf := hscaled') ?_ ?_
  · intro i
    exact sq_nonneg _
  · intro i
    exact normSq_radialSoninBoundaryCrossing_apply_le_canonical_antiresonantColumn
      p S (sourceBasis i)

/-- Under the same column-energy premise the positive Cauchy defect `C†C` is
trace-class along the chosen basis. -/
theorem isTraceClassAlong_radialSoninBoundaryCauchyDefect_of_antiresonantColumnEnergy
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcolumn : Summable fun i =>
      ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (sourceBasis i))‖ ^ 2) :
    IsTraceClassAlong sourceBasis (radialSoninBoundaryCauchyDefect p S) :=
  radialSoninBoundaryCauchyPairData_isTraceClassAlong sourceBasis p S
    (summable_radialSoninBoundaryCrossing_normSq_of_antiresonantColumnEnergy
      sourceBasis p S hcolumn)

/-! ## The explicitly owned pair -/

/-- The Hilbert--Schmidt pair produced by the column-energy transport.  Its
two legs are the crossing itself, so the positive defect is owned, not merely
dominated. -/
noncomputable def radialCauchyPairDataOfAntiresonantColumnEnergy
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcolumn : Summable fun i =>
      ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (sourceBasis i))‖ ^ 2) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) sourceBasis :=
  radialSoninBoundaryCauchyPairData sourceBasis p S
    (summable_radialSoninBoundaryCrossing_normSq_of_antiresonantColumnEnergy
      sourceBasis p S hcolumn)

/-- The transported pair owns the exact positive Cauchy defect. -/
theorem radialCauchyPairDataOfAntiresonantColumnEnergy_traceProduct_eq_defect
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcolumn : Summable fun i =>
      ‖newFrameAntiresonantColumn unitSoninScale p S
        (ContinuousLinearMap.adjoint (newSuffixFrame unitSoninScale S)
          (sourceBasis i))‖ ^ 2) :
    (radialCauchyPairDataOfAntiresonantColumnEnergy sourceBasis p S
      hcolumn).traceProduct =
      radialSoninBoundaryCauchyDefect p S :=
  radialSoninBoundaryCauchyPairData_traceProduct_eq_defect sourceBasis p S _

end C1G8P1RadialCrossingEnergyTransport
end Source
end ConnesWeilRH
