/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3PowerProjectionBridge
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleStrictAngle

/-!
# R3 detector-root square-sum bridge

The no-gap power limit is now available on the actual finite-S carrier.  This
leaf connects it to the first exact source-owned root leg whose Hilbert--
Schmidt energy is already supplied at unit scale by the fixed-source prolate
theorem.

The raw convolution root is deliberately not used as an HS factor: it is a
whole-line Fourier multiplier.  The legal factor here is the completed range
leg `sourceRootCompletedRangeLeftLeg`, namely the selected root applied to the
prolate factor.  The remaining leakage leg is not hidden by this theorem.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open Source.CCM25Concrete.CCM24UnitScaleProlateTraceReduction

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier

theorem sourceRootCompletedRangeLeftLeg_unit_summable
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier) :
    Summable fun i =>
      ‖sourceRootCompletedRangeLeftLeg owner unitSoninScale
        (basis i)‖ ^ 2 := by
  exact sourceRootCompletedRangeLeftLeg_summable_of_prolateFactor
    owner unitSoninScale basis
    (sourceProlateHilbertSchmidtFactor_unit_summable basis)

theorem sourceRootCompletedRangeLeftLeg_unit_basisEnergy_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier) :
    (∑' i, ‖sourceRootCompletedRangeLeftLeg owner unitSoninScale
        (basis i)‖ ^ 2) ≤
      ‖sourceCompressedDetectorRightRoot owner unitSoninScale‖ ^ 2 *
        ∑' i, ‖sourceProlateHilbertSchmidtFactor unitSoninScale
          (basis i)‖ ^ 2 := by
  exact sourceRootCompletedRangeLeftLeg_basisEnergy_le owner unitSoninScale
    basis (sourceProlateHilbertSchmidtFactor_unit_summable basis)

/-- Strong convergence alone is enough once the actual factor square-sum is
available; no columnwise defect-series premise is needed any more. -/
theorem doubledShiftAlternatingProduct_weighted_hs_energy_tendsto_zero_of_strong_limit
    {ι : Type*}
    (b : ℝ) (basis : HilbertBasis ι ℂ Carrier)
    (factor : Carrier →L[ℂ] Carrier)
    (hfactor : Summable (fun i => ‖factor (basis i)‖ ^ 2)) :
    Filter.Tendsto
      (fun n : ℕ => ∑' i,
        ‖(((doubledShiftAlternatingProduct b) ^ n -
            doubledShiftSoninIntersectionProjection b)
          (factor (basis i)))‖ ^ 2)
      Filter.atTop (nhds 0) := by
  let operators : ℕ → Carrier →L[ℂ] Carrier := fun n =>
    (doubledShiftAlternatingProduct b) ^ n
  let limit : Carrier →L[ℂ] Carrier :=
    doubledShiftSoninIntersectionProjection b
  have hpoint : ∀ i,
      Filter.Tendsto
        (fun n => (operators n - limit) (factor (basis i)))
        Filter.atTop (nhds 0) := by
    intro i
    have hstrong := doubledShiftAlternatingProduct_tendsto_intersectionProjection_no_gap
      b (factor (basis i))
    have hdiff : Filter.Tendsto
        (fun n : ℕ =>
          ((doubledShiftAlternatingProduct b) ^ n) (factor (basis i)) -
            doubledShiftSoninIntersectionProjection b (factor (basis i)))
        Filter.atTop (nhds 0) :=
      tendsto_sub_nhds_zero_iff.mpr hstrong
    simpa only [operators, limit, ContinuousLinearMap.sub_apply] using hdiff
  have hoperators : ∀ᶠ n : ℕ in Filter.atTop, ‖operators n‖ ≤ 1 := by
    filter_upwards [] with n
    dsimp [operators]
    exact norm_pow_le_one_of_norm_le_one
      (doubledShiftAlternatingProduct_norm_le_one b) n
  have hlimit : ‖limit‖ ≤ 1 := by
    dsimp [limit]
    exact IsStarProjection.norm_le _
      (doubledShiftSoninIntersectionProjection_isStarProjection b)
  simpa only [operators, limit, ContinuousLinearMap.sub_apply] using
    tendsto_hilbertSchmidt_energy_of_strong_convergence
      basis factor operators limit Filter.atTop hfactor hpoint hoperators hlimit

theorem sourceRootCompletedRangeLeftLeg_unit_weighted_hs_energy_tendsto_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    {ι : Type*} (b : ℝ) (basis : HilbertBasis ι ℂ Carrier) :
    Filter.Tendsto
      (fun n : ℕ => ∑' i,
        ‖(((doubledShiftAlternatingProduct b) ^ n -
            doubledShiftSoninIntersectionProjection b)
          (sourceRootCompletedRangeLeftLeg owner unitSoninScale
            (basis i)))‖ ^ 2)
      Filter.atTop (nhds 0) := by
  exact doubledShiftAlternatingProduct_weighted_hs_energy_tendsto_zero_of_strong_limit
    b basis (sourceRootCompletedRangeLeftLeg owner unitSoninScale)
    (sourceRootCompletedRangeLeftLeg_unit_summable owner basis)

end Dev
end ConnesWeilRH
