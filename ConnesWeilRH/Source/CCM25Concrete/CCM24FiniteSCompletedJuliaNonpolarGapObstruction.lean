/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaNonpolarGapFactorBridge

/-!
# Non-polar gap zero-mode obstruction

Proof 542 identifies the remaining non-polar gap factor with the existing
polar/raw mismatch factor.  This module records the direct kernel consequence
for that exact active target.

It does not assert that the adjacent left co-defect has a nonzero kernel
vector, nor that the gap is nonzero on such a vector.  Those are source
questions.  If such a witness is supplied, however, every finite gap-factor
bound and every uniform physical producer is ruled out.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaNonpolarGapObstruction

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaNonpolarGapFactorBridge
open CCM24FiniteSCompletedJuliaPolarSlotBound
open CCM24FiniteSCompletedJuliaSignedLocalization
open CCM24FiniteSCompletedJuliaUniformRawReadout
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCoDefect

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Single-suffix kernel guard -/

/-- A successful non-polar gap factor kills the gap adjoint on the actual
adjacent left-co-defect kernel. -/
theorem SuffixLocalNonpolarGapCoDefectFactorData.adjoint_eq_zero_of_leftCoDefect_eq_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (data : SuffixLocalNonpolarGapCoDefectFactorData
      owner lambda p S bound)
    {x : sourceSoninCarrier lambda}
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0) :
    ((suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)†) x = 0 := by
  have hadjoint := congrArg ContinuousLinearMap.adjoint data.factorization
  have hself : IsSelfAdjoint
      (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
    simpa only [RectangularSchurCoDefectStepData.leftCoDefect] using
      (canonicalJuliaDefect_isSelfAdjoint
        (ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).transition)
        (suffixEulerFrameSchurStep lambda p S).transitionAdjointContract)
  have hmap :
      (suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)† =
        (data.completion)† ∘L
          (suffixEulerFrameSchurStep lambda p S).leftCoDefect := by
    simpa only [ContinuousLinearMap.adjoint_comp, hself.adjoint_eq] using hadjoint
  rw [hmap]
  simp only [ContinuousLinearMap.comp_apply, hx, map_zero]

/-- A nonzero non-polar gap adjoint on a left-co-defect zero mode rules out a
single-suffix non-polar factor at every numerical bound. -/
theorem noLocalNonpolarGapFactor_of_adjoint_ne_zero_on_leftCoDefectKernel
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hgap : ((suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)†) x ≠ 0) :
    ∀ bound : ℝ,
      ¬ Nonempty (SuffixLocalNonpolarGapCoDefectFactorData
        owner lambda p S bound) := by
  intro bound hdata
  rcases hdata with ⟨data⟩
  exact hgap
    (SuffixLocalNonpolarGapCoDefectFactorData.adjoint_eq_zero_of_leftCoDefect_eq_zero
      data hx)

/-! ## Uniform-family obstruction -/

/-- The same witness rules out a uniform non-polar gap family, independently
of its shared bound. -/
theorem noUniformNonpolarGapFactor_of_adjoint_ne_zero_on_leftCoDefectKernel
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hgap : ((suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)†) x ≠ 0) :
    ∀ bound : ℝ,
      ¬ Nonempty (SuffixLocalNonpolarGapCoDefectUniformFactorData
        owner lambda bound) := by
  intro bound hdata
  rcases hdata with ⟨data⟩
  exact hgap
    (SuffixLocalNonpolarGapCoDefectFactorData.adjoint_eq_zero_of_leftCoDefect_eq_zero
      (data.factor p S) hx)

/-- A nonzero gap adjoint on one actual zero mode rules out the existence of
any finite uniform non-polar gap factor bound. -/
theorem noExistsUniformNonpolarGapFactor_of_adjoint_ne_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hgap : ((suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)†) x ≠ 0) :
    ¬ ∃ bound : ℝ,
      Nonempty (SuffixLocalNonpolarGapCoDefectUniformFactorData
        owner lambda bound) := by
  rintro ⟨bound, hdata⟩
  exact
    (noUniformNonpolarGapFactor_of_adjoint_ne_zero_on_leftCoDefectKernel
      p S x hx hgap bound) hdata

/-! ## Handoff to the physical owner -/

/-- The same source witness rules out the family-uniform physical domination
contract through the exact Proof 542 bridge. -/
theorem noExistsUniformPhysicalDomination_of_nonpolarGapAdjoint_ne_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hgap : ((suffixActualBandLocalNonpolarLocalizationGap owner lambda p S)†) x ≠ 0) :
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
  exact noExistsUniformNonpolarGapFactor_of_adjoint_ne_zero p S x hx hgap hfactor

end CCM24FiniteSCompletedJuliaNonpolarGapObstruction
end CCM25Concrete
end Source
end ConnesWeilRH
