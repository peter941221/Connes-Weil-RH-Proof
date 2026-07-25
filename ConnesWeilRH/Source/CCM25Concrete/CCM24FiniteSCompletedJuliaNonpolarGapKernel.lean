/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaNonpolarGapObstruction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawCoDefectFactor

/-!
# Kernel sanity for the non-polar gap

Proof 543 records the necessary zero-mode test for a proposed non-polar gap
factor. This module identifies that test with the existing same-object
polar/raw mismatch and raw-row kernel tests.

The result is deliberately a kernel diagnostic, not a uniform estimate:
to close Gate 3U one still has to prove the non-polar gap Douglas bound
from Proof 547.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaNonpolarGapKernel

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaNonpolarGapFactorBridge
open CCM24FiniteSCompletedJuliaNonpolarGapObstruction
open CCM24FiniteSCompletedJuliaNonpolarMismatchNormalForm
open CCM24FiniteSCompletedJuliaPolarSlotBound
open CCM24FiniteSCompletedJuliaRawCoDefectFactor
open CCM24FiniteSCompletedJuliaSignedLocalization
open CCM24FiniteSCompletedJuliaUniformRawReadout
open CCM24FiniteSFrameGramCalculus

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Non-polar gap versus the same-object mismatch -/

/-- The non-polar gap adjoint is the adjoint of the already named
polar/raw mismatch defect. -/
theorem suffixActualBandLocalNonpolarLocalizationGap_adjoint_eq_mismatch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)† =
      (suffixActualBandLocalRoutePolarRawMismatchDefect owner lambda p S)† := by
  rw [suffixActualBandLocalNonpolarLocalizationGap_eq_routePolarRawMismatchDefect]

/-- The kernel test for the non-polar gap is exactly the local mismatch
kernel test. -/
theorem suffixActualBandLocalNonpolarLocalizationGap_adjoint_eq_zero_iff_mismatch
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ((suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)†) x = 0 ↔
      ((suffixActualBandLocalRoutePolarRawMismatchDefect owner lambda p S)†) x = 0 := by
  rw [suffixActualBandLocalNonpolarLocalizationGap_adjoint_eq_mismatch]

/-- The same kernel test can also be read on the one-sided intertwining
defect. -/
theorem suffixActualBandLocalNonpolarLocalizationGap_adjoint_eq_zero_iff_intertwining
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ((suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)†) x = 0 ↔
      ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
        owner lambda p S)†) x = 0 := by
  exact
    (suffixActualBandLocalNonpolarLocalizationGap_adjoint_eq_zero_iff_mismatch
      owner lambda p S x).trans
      (suffixActualBandLocalRoutePolarRawMismatchDefect_adjoint_eq_zero_iff
        owner lambda p S x)

/-! ## Co-defect kernel comparison with the raw row -/

/-- On an adjacent Julia co-defect zero mode, the non-polar gap zero test is
equivalent to the recombined raw four-term zero test. -/
theorem suffixActualBandLocalNonpolarLocalizationGap_adjoint_eq_zero_iff_raw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0) :
    ((suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)†) x = 0 ↔
      ((suffixActualBandRawQuadraticIntertwiningDefect owner lambda p S)†) x = 0 := by
  have hbridge :=
    suffixActualBandLocalNonpolarLocalizationGap_adjoint_eq_zero_iff_intertwining
      owner lambda p S x
  have hinter :=
    suffixMismatchIntertwining_adjoint_on_leftCoDefectKernel
      owner lambda p S x hx
  constructor
  · intro hgap
    have hinterZero := hbridge.mp hgap
    rw [hinter] at hinterZero
    simpa only [neg_eq_zero] using hinterZero
  · intro hraw
    apply hbridge.mpr
    rw [hinter, hraw, neg_zero]

/-- A raw-row zero-mode obstruction rules out every non-polar gap factor
family, because on the co-defect kernel it is equivalent to a non-polar gap
obstruction. -/
theorem noExistsUniformNonpolarGapFactor_of_rawAdjoint_ne_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hraw : ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ ∃ bound : ℝ,
      Nonempty (SuffixLocalNonpolarGapCoDefectUniformFactorData
        owner lambda bound) := by
  have hgap :
      ((suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)†) x ≠ 0 := by
    intro hzero
    exact hraw
      ((suffixActualBandLocalNonpolarLocalizationGap_adjoint_eq_zero_iff_raw
        owner lambda p S x hx).mp hzero)
  exact noExistsUniformNonpolarGapFactor_of_adjoint_ne_zero p S x hx hgap

/-- The same raw-row zero-mode obstruction rules out the family-uniform
physical domination contract through the Proof 542 bridge. -/
theorem noExistsUniformPhysicalDomination_of_rawAdjoint_ne_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hraw : ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ ∃ bound : ℝ,
      Nonempty (SuffixMismatchAmbientBoundaryUniformDominationData
        owner lambda bound) := by
  intro hdom
  have hfactor :
      ∃ bound : ℝ,
        Nonempty (SuffixLocalNonpolarGapCoDefectUniformFactorData
          owner lambda bound) :=
    (exists_uniformNonpolarGapFactor_iff_exists_uniformPhysicalDomination
      owner lambda).mpr hdom
  exact noExistsUniformNonpolarGapFactor_of_rawAdjoint_ne_zero
    p S x hx hraw hfactor

end CCM24FiniteSCompletedJuliaNonpolarGapKernel
end CCM25Concrete
end Source
end ConnesWeilRH
