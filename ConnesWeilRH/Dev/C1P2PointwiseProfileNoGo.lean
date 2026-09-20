/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 License.
-/

import ConnesWeilRH.Dev.C1P2BilateralProfileExit

/-!
# Pointwise bilateral-profile sign is not the B5 producer

The pointwise profile witness is a sufficient sign certificate, but it cannot
hold for a healthy detector: the same detector data already gives strict
negative `qw`, while the witness gives nonnegative `qw`.  This formally
closes the pointwise shortcut and leaves the signed aggregate profile as the
live producer target.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2PointwiseProfileNoGo

open C1HealthyYoshidaDetector
open C1P2BilateralProfileExit
open C1SpectralWeil
open C1CenterTwoCriterionBridge
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution

theorem not_pointwiseProfileSignWitness_of_healthyDetectorData
    {rho : Complex} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g)
    (p : P2BilateralProfileSignWitness g) : False := by
  have hnonneg : 0 ≤ C1SameOwnerWeil.qw g :=
    qw_nonneg_of_p2BilateralProfileSignWitness g hdata.vanishesOnF p
  have hspectral : C1SpectralWeil.spectralWeilValue g.convolutionSquare < 0 :=
    (weilSquareSumPositive_iff_spectralWeilValue_neg g).mp
      hdata.weilSquareSumPositive
  have hnegative : C1SameOwnerWeil.qw g < 0 := by
    rw [C1CenterTwoCriterionBridge.qw_eq_spectralWeilValue_centerTwo]
    exact hspectral
  exact (not_lt_of_ge hnonneg) hnegative

end C1P2PointwiseProfileNoGo
end Source
end ConnesWeilRH
