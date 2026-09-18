/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3HardyOffDiagonalFactor
import ConnesWeilRH.Dev.C1G8R3HardyDefectLeakageConsumer

/-!
# Off-diagonal Hardy-column consumer for S3

The positive-square identity turns a square-summable column family for the
off-diagonal Hankel factor into the required defect-column family by bounded
postcomposition with its adjoint.  The latter is then consumed by the exact
finite-S leakage bridge.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier

theorem sourceRootCompletedRightCommutatorLeftLeg_sourceBasis_normSq_summable_of_hardyOffDiagonal
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ Carrier)
    (hfactor : Summable fun i : ι =>
      ‖((ContinuousLinearMap.id ℂ Carrier -
          cc20PositiveHalfLineProjection) ∘L
        doubledShiftHardy (Real.log lambda) ∘L
        cc20PositiveHalfLineProjection) (basis i)‖ ^ 2) :
    Summable fun i : ι =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2 := by
  let P := cc20PositiveHalfLineProjection
  let K := doubledShiftHardy (Real.log lambda)
  let A := (ContinuousLinearMap.id ℂ Carrier - P) ∘L K ∘L P
  have hA : Summable fun i : ι => ‖A (basis i)‖ ^ 2 := by
    simpa only [A, P, K] using hfactor
  have hdefect : Summable fun i : ι =>
      ‖(P - P ∘L K ∘L P ∘L K ∘L P) (basis i)‖ ^ 2 := by
    have hpost := PositiveTrace.summable_normSq_postcomp basis A A.adjoint hA
    have heq : P - P ∘L K ∘L P ∘L K ∘L P = A.adjoint ∘L A := by
      simpa only [A, P, K, ContinuousLinearMap.comp_assoc] using
        (doubledShiftHardyDefect_eq_offDiagonal_adjoint_comp_self
          (Real.log lambda))
    rw [heq]
    exact hpost
  exact sourceRootCompletedRightCommutatorLeftLeg_sourceBasis_normSq_summable_of_hardyDefect
    owner lambda basis hdefect

end Dev
end ConnesWeilRH
