/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ScaleDetectorRootSquareSum
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet

/-!
# S3 survivor band-root assembly

The completed range leg is already Hilbert--Schmidt at every Sonin scale.
This leaf performs the exact algebraic assembly with the Fourier-leakage
commutator leg.  It isolates the remaining S3 input: square-summability of
that one leakage leg.  No leakage estimate, sign, or RH conclusion is hidden
in the statement.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.SelectedCrossingOperatorBridge

local notation "Carrier" => finiteSCarrier

theorem sourceRootCompletedBandRoot_summable_of_fourierLeakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {ι : Type*}
    (basis : HilbertBasis ι ℂ Carrier)
    (hleak : Summable fun i =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner lambda
        (basis i)‖ ^ 2) :
    Summable fun i =>
      ‖(rootConvolution owner ∘L sourceBandProjection lambda)
        (basis i)‖ ^ 2 := by
  rw [← sourceRootCompletedLeftLegs_add_eq_root_band]
  exact summable_normSq_add basis
    (sourceRootCompletedRangeLeftLeg owner lambda)
    (sourceRootCompletedRightCommutatorLeftLeg owner lambda)
    (sourceRootCompletedRangeLeftLeg_summable_all_scales owner basis lambda)
    hleak

end Dev
end ConnesWeilRH
