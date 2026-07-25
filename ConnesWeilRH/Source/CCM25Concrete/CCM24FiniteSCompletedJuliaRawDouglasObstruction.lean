/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawDouglasReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaComponentKernel

/-!
# Kernel obstruction for raw Douglas domination

Proof 538 gives the direct raw Douglas formulation of the remaining producer.
This module records the kernel consequence of that formulation itself.

A raw Douglas producer must annihilate the adjacent left-co-defect kernel.
After converting its raw readout to component rows, it also annihilates the
complete polar/raw mismatch there.  Hence any nonzero raw or mismatch adjoint
on that kernel rules out the direct raw Douglas producer.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawDouglasObstruction

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaComponentKernel
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaRawDouglasReadout
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawPhysicalReadout
open CCM24FiniteSFrameGramCalculus

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

/-! ## Single-suffix kernel consequences -/

/-- A raw Douglas producer kills the raw four-term adjoint on the actual
physical-analysis kernel. -/
theorem rawDomination_rawAdjoint_eq_zero_of_analysis_eq_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (hdom : SuffixRawAmbientBoundaryDomination
      owner lambda p S bound)
    (x : sourceSoninCarrier lambda)
    (hx : suffixEulerFrameAmbientBoundaryAnalysis lambda p S x = 0) :
    ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x = 0 := by
  let data :=
    suffixRawAmbientBoundaryReadoutDataOfDomination
      owner lambda p S bound hdom
  have hfactor := congrArg (fun operator : SourceOp lambda => operator x)
    data.factorization
  simpa only [ContinuousLinearMap.comp_apply, hx, map_zero] using hfactor.symm

/-- A raw Douglas producer kills the raw four-term adjoint on the adjacent
left-co-defect kernel. -/
theorem rawDomination_rawAdjoint_eq_zero_of_leftCoDefect_eq_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (hdom : SuffixRawAmbientBoundaryDomination
      owner lambda p S bound)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0) :
    ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x = 0 := by
  apply rawDomination_rawAdjoint_eq_zero_of_analysis_eq_zero hdom x
  exact
    (suffixEulerFrameAmbientBoundaryAnalysis_eq_zero_iff_leftCoDefect_eq_zero
      lambda p S x).mpr hx

/-- A raw Douglas producer also kills the complete polar/raw mismatch adjoint
on the adjacent left-co-defect kernel. -/
theorem rawDomination_mismatchAdjoint_eq_zero_of_leftCoDefect_eq_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (hdom : SuffixRawAmbientBoundaryDomination
      owner lambda p S bound)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0) :
    ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)†) x = 0 := by
  let rawData :=
    suffixRawAmbientBoundaryReadoutDataOfDomination
      owner lambda p S bound hdom
  let componentData :=
    SuffixRawAmbientBoundaryReadoutData.toComponentReadoutWithBound rawData
  exact
    componentReadout_mismatchAdjoint_eq_zero_of_leftCoDefect_eq_zero
      componentData x hx

/-! ## Single-suffix no-go forms -/

/-- A nonzero raw four-term adjoint on the left-co-defect kernel rules out
raw Douglas domination for this suffix. -/
theorem noRawDomination_of_rawAdjoint_ne_zero_on_leftCoDefectKernel
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hraw : ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ SuffixRawAmbientBoundaryDomination owner lambda p S bound := by
  intro hdom
  exact hraw
    (rawDomination_rawAdjoint_eq_zero_of_leftCoDefect_eq_zero
      hdom x hx)

/-- A nonzero complete polar/raw mismatch adjoint on the left-co-defect
kernel rules out raw Douglas domination for this suffix. -/
theorem noRawDomination_of_mismatchAdjoint_ne_zero_on_leftCoDefectKernel
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {p : CCM24VisiblePrime}
    {S : List CCM24VisiblePrime} {bound : ℝ}
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hmismatch : ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ SuffixRawAmbientBoundaryDomination owner lambda p S bound := by
  intro hdom
  exact hmismatch
    (rawDomination_mismatchAdjoint_eq_zero_of_leftCoDefect_eq_zero
      hdom x hx)

/-! ## Uniform-family no-go forms -/

/-- A raw zero-mode obstruction rules out any uniform raw Douglas package
with the specified bound. -/
theorem noUniformRawDomination_of_rawAdjoint_ne_zero_on_leftCoDefectKernel
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hraw : ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ Nonempty
      (SuffixRawAmbientBoundaryUniformDominationData
        owner lambda bound) := by
  rintro ⟨data⟩
  exact
    (noRawDomination_of_rawAdjoint_ne_zero_on_leftCoDefectKernel
      (bound := bound) x hx hraw) (data.domination p S)

/-- A mismatch zero-mode obstruction rules out any uniform raw Douglas
package with the specified bound. -/
theorem noUniformRawDomination_of_mismatchAdjoint_ne_zero_on_leftCoDefectKernel
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale} {bound : ℝ}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hmismatch : ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ Nonempty
      (SuffixRawAmbientBoundaryUniformDominationData
        owner lambda bound) := by
  rintro ⟨data⟩
  exact
    (noRawDomination_of_mismatchAdjoint_ne_zero_on_leftCoDefectKernel
      (bound := bound) x hx hmismatch) (data.domination p S)

/-- A raw zero-mode obstruction rules out existence of any finite uniform raw
Douglas bound. -/
theorem noExistsUniformRawDomination_of_rawAdjoint_ne_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hraw : ((suffixActualBandRawQuadraticIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ ∃ bound : ℝ,
      Nonempty
        (SuffixRawAmbientBoundaryUniformDominationData
          owner lambda bound) := by
  rintro ⟨bound, hdata⟩
  exact
    (noUniformRawDomination_of_rawAdjoint_ne_zero_on_leftCoDefectKernel
      (bound := bound) p S x hx hraw) hdata

/-- A mismatch zero-mode obstruction rules out existence of any finite
uniform raw Douglas bound. -/
theorem noExistsUniformRawDomination_of_mismatchAdjoint_ne_zero
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda)
    (hx : (suffixEulerFrameSchurStep lambda p S).leftCoDefect x = 0)
    (hmismatch : ((suffixActualBandRoutePolarRawMismatchIntertwiningDefect
      owner lambda p S)†) x ≠ 0) :
    ¬ ∃ bound : ℝ,
      Nonempty
        (SuffixRawAmbientBoundaryUniformDominationData
          owner lambda bound) := by
  rintro ⟨bound, hdata⟩
  exact
    (noUniformRawDomination_of_mismatchAdjoint_ne_zero_on_leftCoDefectKernel
      (bound := bound) p S x hx hmismatch) hdata

end CCM24FiniteSCompletedJuliaRawDouglasObstruction
end CCM25Concrete
end Source
end ConnesWeilRH
