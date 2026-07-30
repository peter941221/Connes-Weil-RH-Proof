/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialBoundaryCauchyEnergy

/-!
# Conditional pair producer for the radial Cauchy defect

Proof 693 keeps the positive defect as its own source object.  The operator
`C† C` is supported on the suffix Sonin range on both sides.  If a source
theorem supplies the named-basis energy `sum_i ‖C e_i‖² < ∞`, the two equal
Hilbert--Schmidt legs `C` form a genuine pair whose trace product is exactly
the positive defect.

This producer is intentionally for `C† C`, not for `C` itself.  It therefore
does not manufacture the missing `A† B = C` boundary pair and does not close
Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace AntiresonantFrameLossRadialBoundaryCauchyPairProducer

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open AntiresonantFrameLossRadialBoundarySplit
open AntiresonantFrameLossRadialBoundaryAdjointSupport
open AntiresonantFrameLossRadialBoundaryColumnFullCarrierExtension
open AntiresonantFrameLossRadialBoundaryCauchyDefect
open AntiresonantFrameLossRadialBoundaryCauchyEnergy
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorAdjacentProjectionGap
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

/-! ## Two-sided suffix support -/

/-- The positive Cauchy defect is fixed by the suffix range projection on the
right. -/
theorem radialSoninBoundaryCauchyDefect_comp_newSuffixRangeProjection_eq_self
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    radialSoninBoundaryCauchyDefect p S ∘L
        newSuffixRangeProjection unitSoninScale S =
      radialSoninBoundaryCauchyDefect p S := by
  unfold radialSoninBoundaryCauchyDefect
  apply ContinuousLinearMap.ext
  intro u
  have h := DFunLike.congr_fun
    (radialSoninBoundaryCrossing_comp_newSuffixRangeProjection_eq_self p S) u
  simp only [ContinuousLinearMap.comp_apply] at h ⊢
  rw [h]

/-- The positive Cauchy defect is fixed by the suffix range projection on the
left. -/
theorem newSuffixRangeProjection_comp_radialSoninBoundaryCauchyDefect_eq_self
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    newSuffixRangeProjection unitSoninScale S ∘L
        radialSoninBoundaryCauchyDefect p S =
      radialSoninBoundaryCauchyDefect p S := by
  unfold radialSoninBoundaryCauchyDefect
  apply ContinuousLinearMap.ext
  intro u
  have h := DFunLike.congr_fun
    (newSuffixRangeProjection_comp_radialSoninBoundaryCrossing_adjoint_eq_self
      p S)
    (radialSoninBoundaryCrossing p S u)
  simp only [ContinuousLinearMap.comp_apply] at h ⊢
  exact h

/-! ## Direct positive-energy pair -/

/-- Two equal crossing legs produce a Hilbert--Schmidt pair for the positive
Cauchy defect once the crossing energy is supplied. -/
noncomputable def radialSoninBoundaryCauchyPairData
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcross : Summable fun i =>
      ‖radialSoninBoundaryCrossing p S (sourceBasis i)‖ ^ 2) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) sourceBasis :=
  { left := radialSoninBoundaryCrossing p S
    right := radialSoninBoundaryCrossing p S
    left_summable_normSq := hcross
    right_summable_normSq := hcross }

/-- The direct positive-energy pair owns the exact Cauchy defect. -/
theorem radialSoninBoundaryCauchyPairData_traceProduct_eq_defect
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcross : Summable fun i =>
      ‖radialSoninBoundaryCrossing p S (sourceBasis i)‖ ^ 2) :
    (radialSoninBoundaryCauchyPairData sourceBasis p S hcross).traceProduct =
      radialSoninBoundaryCauchyDefect p S := by
  rfl

theorem radialSoninBoundaryCauchyPairData_isTraceClassAlong
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hcross : Summable fun i =>
      ‖radialSoninBoundaryCrossing p S (sourceBasis i)‖ ^ 2) :
    IsTraceClassAlong sourceBasis
      (radialSoninBoundaryCauchyDefect p S) := by
  rw [← radialSoninBoundaryCauchyPairData_traceProduct_eq_defect
    sourceBasis p S hcross]
  exact (radialSoninBoundaryCauchyPairData sourceBasis p S hcross).traceProduct_isTraceClassAlong

/-! ## Pair construction from a positive-defect trace premise -/

/-- A positive-defect trace premise is enough to instantiate the direct pair;
the crossing energy is recovered by the exact criterion from Proof 692. -/
noncomputable def radialSoninBoundaryCauchyPairDataOfTraceClass
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hdefect : IsTraceClassAlong sourceBasis
      (radialSoninBoundaryCauchyDefect p S)) :
    BasisHilbertSchmidtPairData (G := finiteSCarrier) sourceBasis :=
  radialSoninBoundaryCauchyPairData sourceBasis p S
    (radialSoninBoundaryCrossing_summable_of_cauchyDefect_isTraceClassAlong
      sourceBasis p S hdefect)

theorem radialSoninBoundaryCauchyPairDataOfTraceClass_traceProduct_eq_defect
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ finiteSCarrier)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hdefect : IsTraceClassAlong sourceBasis
      (radialSoninBoundaryCauchyDefect p S)) :
    (radialSoninBoundaryCauchyPairDataOfTraceClass sourceBasis p S hdefect).traceProduct =
      radialSoninBoundaryCauchyDefect p S := by
  exact radialSoninBoundaryCauchyPairData_traceProduct_eq_defect sourceBasis p S _

end AntiresonantFrameLossRadialBoundaryCauchyPairProducer
end CCM25Concrete
end Source
end ConnesWeilRH
