/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3HardyOffDiagonalColumnConsumer
import ConnesWeilRH.Dev.C1G8R3HilbertSchmidtOrthonormalObstruction

/-!
# No-go for the full-basis off-diagonal Hardy estimate

The off-diagonal consumer is a valid conditional bridge, but its premise
cannot hold at unit scale when the selected source Laplace value is nonzero.
This prevents replacing the detector-specific compressed energy estimate by a
global Hilbert--Schmidt estimate on the whole source carrier.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CC20YoshidaConvolution
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier

theorem not_hardyOffDiagonal_at_unitScale_of_nonzero_sourceLaplace
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (rho : ℂ)
    (hvalue : CompactLogTest.laplaceAt owner.sourceTest rho ≠ 0)
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier) :
    ¬ Summable (fun i : ι =>
      ‖((ContinuousLinearMap.id ℂ Carrier -
          cc20PositiveHalfLineProjection) ∘L
        doubledShiftHardy (Real.log unitSoninScale) ∘L
        cc20PositiveHalfLineProjection) (basis i)‖ ^ 2) := by
  intro hfactor
  have hleak :=
    sourceRootCompletedRightCommutatorLeftLeg_sourceBasis_normSq_summable_of_hardyOffDiagonal
      owner unitSoninScale basis hfactor
  exact sourceRootCompletedRightCommutatorLeftLeg_not_hilbertSchmidt
    owner rho hvalue basis hleak

end Dev
end ConnesWeilRH
