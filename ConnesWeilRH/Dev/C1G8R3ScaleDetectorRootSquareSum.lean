/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ScaleProlateStrictAngle
import ConnesWeilRH.Dev.C1G8R3DetectorRootSquareSum

/-!
# Moving-scale completed detector-root range leg

The relative prolate factor has an all-scale Hilbert--Schmidt square-sum.
This leaf transports that result back to the actual source prolate factor and
then inserts the selected detector root.  It closes the completed range leg
at every Sonin scale and supplies its no-gap weighted-energy limit on the same
global basis.  The leakage and common-right legs remain separate obligations.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.CC20Concrete.PositiveTrace

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier

/-- The source prolate factor is square-summable at every selected scale,
by conjugating the all-scale relative-factor result back to the source
coordinate. -/
theorem sourceProlateHilbertSchmidtFactor_summable_all_scales
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier)
    (lambda : CCM24SoninScale) :
    Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (basis i)‖ ^ 2 := by
  exact sourceProlateHilbertSchmidtFactor_summable_of_relativeFactor
    basis lambda
    (doubledShiftProlateHilbertSchmidtFactor_summable basis (Real.log lambda))

/-- The selected convolution root applied to the completed prolate-range leg
has a same-basis Hilbert--Schmidt square-sum at every Sonin scale. -/
theorem sourceRootCompletedRangeLeftLeg_summable_all_scales
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier)
    (lambda : CCM24SoninScale) :
    Summable fun i =>
      ‖sourceRootCompletedRangeLeftLeg owner lambda (basis i)‖ ^ 2 := by
  exact sourceRootCompletedRangeLeftLeg_summable_of_prolateFactor
    owner lambda basis
    (sourceProlateHilbertSchmidtFactor_summable_all_scales basis lambda)

/-- The actual-scale range-leg energy is bounded by the root norm times the
relative prolate energy, with both column sums taken on the same basis. -/
theorem sourceRootCompletedRangeLeftLeg_basisEnergy_le_all_scales
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier)
    (lambda : CCM24SoninScale) :
    (∑' i, ‖sourceRootCompletedRangeLeftLeg owner lambda (basis i)‖ ^ 2) ≤
      ‖sourceCompressedDetectorRightRoot owner lambda‖ ^ 2 *
        ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda (basis i)‖ ^ 2 := by
  exact sourceRootCompletedRangeLeftLeg_basisEnergy_le owner lambda basis
    (sourceProlateHilbertSchmidtFactor_summable_all_scales basis lambda)

/-- No-gap alternating powers converge in weighted Hilbert--Schmidt energy
on the actual moving-scale completed range leg. -/
theorem sourceRootCompletedRangeLeftLeg_weighted_hs_energy_tendsto_zero_all_scales
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier)
    (lambda : CCM24SoninScale) :
    Filter.Tendsto
      (fun n : ℕ => ∑' i,
        ‖(((doubledShiftAlternatingProduct (Real.log lambda)) ^ n -
            doubledShiftSoninIntersectionProjection (Real.log lambda))
          (sourceRootCompletedRangeLeftLeg owner lambda (basis i)))‖ ^ 2)
      Filter.atTop (nhds 0) := by
  exact doubledShiftAlternatingProduct_weighted_hs_energy_tendsto_zero_of_strong_limit
    (Real.log lambda) basis (sourceRootCompletedRangeLeftLeg owner lambda)
    (sourceRootCompletedRangeLeftLeg_summable_all_scales owner basis lambda)

/-- The positive composition of the completed moving-scale range leg is
trace-class along the same named global basis. -/
theorem sourceRootCompletedRangeLeftLeg_positiveComposition_isTraceClassAlong_all_scales
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier)
    (lambda : CCM24SoninScale) :
    IsTraceClassAlong basis
      ((sourceRootCompletedRangeLeftLeg owner lambda).adjoint ∘L
        sourceRootCompletedRangeLeftLeg owner lambda) := by
  let data : BasisHilbertSchmidtData basis :=
    { operator := sourceRootCompletedRangeLeftLeg owner lambda
      summable_normSq :=
        sourceRootCompletedRangeLeftLeg_summable_all_scales owner basis lambda }
  exact data.positiveComposition_isTraceClassAlong

end Dev
end ConnesWeilRH
