/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3LeakageDefectTelescoping
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovFirstDifference

/-!
# R3 common-right leg: finite visible-prime coboundary telescope

The normalized finite Euler inverse is a finite causal product.  Its centered
part therefore has an exact finite telescoping expansion into prefixed
one-prime translation coboundaries.  This leaf reconnects that expansion to
the source-root-completed common-right leg on the same carrier.

The result is structural: it supplies no Hilbert--Schmidt, trace, sign, or RH
conclusion.  It exposes the finite visible-prime terms that a later
anti-resonance or boundary estimate must control.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSInverseMetric
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24FiniteSCausalMarkov
open Source.CCM25Concrete.CCM24FiniteSCausalMarkovFirstDifference

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

noncomputable def normalizedFiniteEulerInverseList_coboundaryTelescope :
    List CCM24VisiblePrime → Op
  | [] => 0
  | p :: S =>
      normalizedFiniteEulerInverseList S ∘L
          normalizedPrimeEulerInverseTranslationCoboundary p +
        normalizedFiniteEulerInverseList_coboundaryTelescope S

theorem normalizedFiniteEulerInverseList_nil_eq_id :
    normalizedFiniteEulerInverseList [] =
      ContinuousLinearMap.id ℂ Carrier := by
  apply ContinuousLinearMap.ext
  intro u
  simp [normalizedFiniteEulerInverseList, finiteEulerLowerFactor]

theorem normalizedFiniteEulerInverseList_sub_id_eq_coboundaryTelescope
    (S : List CCM24VisiblePrime) :
    normalizedFiniteEulerInverseList S - ContinuousLinearMap.id ℂ Carrier =
      normalizedFiniteEulerInverseList_coboundaryTelescope S := by
  induction S with
  | nil =>
      rw [normalizedFiniteEulerInverseList_nil_eq_id]
      simp [normalizedFiniteEulerInverseList_coboundaryTelescope]
  | cons p S ih =>
      calc
        normalizedFiniteEulerInverseList (p :: S) -
            ContinuousLinearMap.id ℂ Carrier =
          (normalizedFiniteEulerInverseList (p :: S) -
              normalizedFiniteEulerInverseList S) +
            (normalizedFiniteEulerInverseList S -
              ContinuousLinearMap.id ℂ Carrier) := by
                abel
        _ = normalizedFiniteEulerInverseList S ∘L
              normalizedPrimeEulerInverseTranslationCoboundary p +
            normalizedFiniteEulerInverseList_coboundaryTelescope S := by
              rw [normalizedFiniteEulerInverseList_cons_sub_eq_prefixedTranslationCoboundary,
                ih]
        _ = normalizedFiniteEulerInverseList_coboundaryTelescope (p :: S) := by
          rfl

theorem sourceRootCompletedFiniteEulerCommonRightLeg_eq_coboundaryTelescope
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceRootCompletedCommonRightLeg owner lambda
        (radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda) =
      rootConvolution owner ∘L sourceSoninProjection lambda ∘L
        normalizedFiniteEulerInverseList_coboundaryTelescope
          family.visiblePrimes ∘L sourceBandProjection lambda := by
  have hfamily : normalizedFiniteEulerInverse family =
      normalizedFiniteEulerInverseList family.visiblePrimes := by
    rw [normalizedFiniteEulerInverse_eq_causalAverage,
      finiteEulerCausalAverage_eq_normalizedInverse]
  rw [sourceRootCompletedFiniteEulerCommonRightLeg_eq_centeredCausalCrossing,
    hfamily, normalizedFiniteEulerInverseList_sub_id_eq_coboundaryTelescope]

end Dev
end ConnesWeilRH
